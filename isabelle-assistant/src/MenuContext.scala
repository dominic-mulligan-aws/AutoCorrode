/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer
import scala.jdk.CollectionConverters._
import java.io.File

/** Analyzes cursor context to determine which context menu items to show. */
object MenuContext {

  /** Common view state extracted once for reuse across actions. */
  case class ViewContext(
    buffer: JEditBuffer,
    offset: Int,
    hasCommand: Boolean,
    selection: Option[String]
  ) {
    def hasIQ: Boolean = IQAvailable.isAvailable && hasCommand
  }

  object ViewContext {
    def apply(view: View): ViewContext = {
      val buffer = view.getBuffer
      val offset = view.getTextArea.getCaretPosition
      val hasCommand = CommandExtractor.getCommandAtOffset(buffer, offset).isDefined
      val selection = Option(view.getTextArea.getSelectedText).filter(_.trim.nonEmpty)
      ViewContext(buffer, offset, hasCommand, selection)
    }
  }

  /** Find an open theory buffer by name (with or without .thy suffix). 
    * Uses proper path matching to avoid matching substring theory names. */
  def findTheoryBuffer(theoryName: String): Option[JEditBuffer] = {
    val normalized = if (theoryName.endsWith(".thy")) theoryName else s"$theoryName.thy"
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
      .filter(b => b.getPath != null && b.getPath.endsWith(".thy"))

    val byExactPath = buffers.filter(_.getPath == normalized)
    if (byExactPath.size == 1) return byExactPath.headOption

    val byPathSuffix = buffers.filter { b =>
      val path = b.getPath
      path.endsWith(File.separator + normalized) ||
      path.endsWith("/" + normalized) ||
      path.endsWith("\\" + normalized)
    }
    if (byPathSuffix.size == 1) return byPathSuffix.headOption

    val byFilename = buffers.filter(b => new File(b.getPath).getName == normalized)
    if (byFilename.size == 1) byFilename.headOption
    else None
  }

  /** Best-effort absolute path lookup for a jEdit buffer. */
  def bufferPath(buffer: JEditBuffer): Option[String] =
    buffer match {
      case b: org.gjt.sp.jedit.Buffer =>
        Option(b.getPath).map(_.trim).filter(_.nonEmpty)
      case _ =>
        org.gjt.sp.jedit.jEdit
          .getBufferManager()
          .getBuffers()
          .asScala
          .find(_ eq buffer)
          .flatMap(b => Option(b.getPath).map(_.trim).filter(_.nonEmpty))
    }

  case class Context(
    inProof: Boolean,
    hasGoal: Boolean,
    onError: Boolean,
    onWarning: Boolean,
    hasSelection: Boolean,
    hasCommand: Boolean,
    hasTypeInfo: Boolean,
    hasApplyProof: Boolean,
    onDefinition: Boolean,
    iqAvailable: Boolean
  )

  /** Extract Isabelle keywords from buffer lines up to offset (local, no MCP).
    * Walks backward through buffer lines, extracting first token of each line.
    */
  private def extractKeywordsUpTo(buffer: JEditBuffer, offset: Int, maxLinesBack: Int = 200): Seq[String] = {
    val line = buffer.getLineOfOffset(offset)
    val startLine = math.max(0, line - maxLinesBack)
    val keywords = scala.collection.mutable.ArrayBuffer[String]()
    
    for (lineNum <- line to startLine by -1) {
      val lineText = buffer.getLineText(lineNum)
      if (lineText != null) {
        val trimmed = lineText.trim
        if (trimmed.nonEmpty) {
          // Extract first token
          val firstToken = trimmed.takeWhile(c => !c.isWhitespace && c != '(' && c != '"')
          if (IsabelleKeywords.allKeywords.contains(firstToken)) {
            keywords += firstToken
          }
        }
      }
    }
    keywords.toSeq
  }

  /** Get the first keyword on the line containing offset (local, no MCP). */
  private def firstKeywordAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    val line = buffer.getLineOfOffset(offset)
    val lineText = buffer.getLineText(line)
    if (lineText == null) return None
    
    val trimmed = lineText.trim
    if (trimmed.isEmpty) return None
    
    val firstToken = trimmed.takeWhile(c => !c.isWhitespace && c != '(' && c != '"')
    if (IsabelleKeywords.allKeywords.contains(firstToken)) Some(firstToken)
    else None
  }

  /** Check if any visible lines around offset contain "apply" keyword (local, no MCP). */
  private def hasApplyInContext(buffer: JEditBuffer, offset: Int, contextLines: Int = 50): Boolean = {
    val centerLine = buffer.getLineOfOffset(offset)
    val startLine = math.max(0, centerLine - contextLines)
    val endLine = math.min(buffer.getLineCount - 1, centerLine + contextLines)
    
    for (lineNum <- startLine to endLine) {
      val lineText = buffer.getLineText(lineNum)
      if (lineText != null && CommandMatcher.startsWithKeyword(lineText.trim, "apply")) {
        return true
      }
    }
    false
  }

  /** Analyze cursor context using only local buffer text (no blocking MCP calls).
    * Safe for use on the EDT (e.g., in menu construction). May be slightly over-inclusive.
    */
  def analyzeLocal(view: View, buffer: JEditBuffer, offset: Int, selection: Option[String]): Context = {
    val hasSelection = selection.exists(_.trim.nonEmpty)
    
    // Check if line at offset has non-whitespace text
    val line = buffer.getLineOfOffset(offset)
    val lineText = buffer.getLineText(line)
    val hasCommand = lineText != null && lineText.trim.nonEmpty
    
    // Extract keywords and detect proof context
    val keywords = extractKeywordsUpTo(buffer, offset)
    val inProof = GoalExtractor.isInProofContextFromKeywords(keywords)
    
    // Assume goal exists if in proof (action will handle if missing)
    val hasGoal = inProof
    
    // Check if first keyword at offset is a definition/entity keyword
    val onDefinition = firstKeywordAtOffset(buffer, offset)
      .exists(IsabelleKeywords.entityKeywords.contains)
    
    // Check for apply-style proof in visible context
    val hasApplyProof = hasApplyInContext(buffer, offset)
    
    // Always show error/type items - actions handle "not found" case
    val onError = true
    val hasTypeInfo = hasCommand
    
    Context(
      inProof = inProof,
      hasGoal = hasGoal,
      onError = onError,
      onWarning = false,  // Not used by any menu items
      hasSelection = hasSelection,
      hasCommand = hasCommand,
      hasTypeInfo = hasTypeInfo,
      hasApplyProof = hasApplyProof,
      onDefinition = onDefinition,
      iqAvailable = IQAvailable.isAvailableCached
    )
  }

  /** Analyze cursor context using MCP introspection (may block, use off EDT). */
  def analyze(view: View, buffer: JEditBuffer, offset: Int, selection: Option[String]): Context = {
    val inProof = GoalExtractor.isInProofContext(buffer, offset)
    val hasGoal = inProof && GoalExtractor.getGoalState(buffer, offset).isDefined
    val onError = ExplainErrorAction.hasErrorAtOffset(buffer, offset)
    val onWarning = hasWarningAtOffset(buffer, offset)
    val hasSelection = selection.exists(_.trim.nonEmpty)
    val command = CommandExtractor.getCommandAtOffset(buffer, offset)
    val hasCommand = command.isDefined
    val hasTypeInfo = ShowTypeAction.hasTypeAtOffset(buffer, offset)
    val hasApplyProof = {
      val block = if (hasSelection) selection else ProofExtractor.getProofBlockAtOffset(buffer, offset)
      block.exists(ProofExtractor.isApplyStyleProof)
    }
    // Use PIDE span name to detect definition keywords — no string splitting
    val onDefinition = {
      val defKeywords = IsabelleKeywords.entityKeywords
      CommandExtractor.getCommandKeyword(buffer, offset).exists(defKeywords.contains)
    }

    Context(
      inProof = inProof,
      hasGoal = hasGoal,
      onError = onError,
      onWarning = onWarning,
      hasSelection = hasSelection,
      hasCommand = hasCommand,
      hasTypeInfo = hasTypeInfo,
      hasApplyProof = hasApplyProof,
      onDefinition = onDefinition,
      iqAvailable = IQAvailable.isAvailable
    )
  }

  private def hasWarningAtOffset(buffer: JEditBuffer, offset: Int): Boolean = {
    if (!IQAvailable.isAvailable) false
    else {
      val clamped = math.max(0, math.min(offset, buffer.getLength))
      val selectionArgs = bufferPath(buffer) match {
        case Some(path) =>
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> clamped
          )
        case None =>
          Map("command_selection" -> "current")
      }
      IQMcpClient
        .callGetDiagnostics(
          severity = IQMcpClient.DiagnosticSeverity.Warning,
          scope = IQMcpClient.DiagnosticScope.Selection,
          timeoutMs = 1000L,
          selectionArgs = selectionArgs
        )
        .toOption
        .exists(_.diagnostics.nonEmpty)
    }
  }
}
