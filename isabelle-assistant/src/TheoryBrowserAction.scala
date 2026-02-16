/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View
import scala.jdk.CollectionConverters._

/** Theory browsing commands: list, read, search, and dependency inspection. */
object TheoryBrowserAction {

  def theories(): Unit = {
    try {
      val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
      val theories = buffers.filter(_.getPath != null)
        .filter(_.getPath.endsWith(".thy"))
        .map(b => java.io.File(b.getPath).getName.replace(".thy", ""))
        .sorted
      if (theories.nonEmpty) ChatAction.addResponse(s"**Open Theories (${theories.length}):**\n\n- ${theories.mkString("\n- ")}")
      else ChatAction.addResponse("No theory files currently open.")
    } catch { case ex: Exception => ChatAction.addResponse(s"Error listing theories: ${ex.getMessage}") }
  }

  def read(view: View, args: String): Unit = {
    if (args.trim.isEmpty) { ChatAction.addResponse("Usage: `:read <theory> [lines]`  (default: 100 lines)"); return }
    val parts = args.trim.split("\\s+", 2)
    val theoryName = parts(0)
    val maxLines = if (parts.length > 1) try { parts(1).toInt } catch { case _: NumberFormatException => 100 } else 100
    try {
      findBuffer(theoryName) match {
        case Some(buffer) =>
          val content = buffer.getText(0, buffer.getLength)
          val allLines = content.split("\n")
          val lines = allLines.take(maxLines)
          val preview = if (allLines.length > maxLines)
            lines.mkString("\n") + s"\n\n... (showing $maxLines of ${allLines.length} lines, use `:read $theoryName ${maxLines + 100}` for more)"
          else content
          ChatAction.addResponse(s"**Theory: $theoryName**\n\n```isabelle\n$preview\n```")
        case None => ChatAction.addResponse(s"Theory '$theoryName' not found in open buffers. Use :theories to list available theories.")
      }
    } catch { case ex: Exception => ChatAction.addResponse(s"Error reading theory: ${ex.getMessage}") }
  }

  def deps(view: View, theoryName: String): Unit = {
    if (theoryName.trim.isEmpty) { ChatAction.addResponse("Usage: `:deps <theory>`"); return }
    try {
      findBuffer(theoryName) match {
        case Some(buffer) =>
          val content = buffer.getText(0, buffer.getLength)
          val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
          importPattern.findFirstMatchIn(content) match {
            case Some(m) =>
              val tokenPattern = """"[^"]+"|[^\s"]+""".r
              val imports = tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
              if (imports.nonEmpty) ChatAction.addResponse(s"**Dependencies of $theoryName:**\n\n- ${imports.mkString("\n- ")}")
              else ChatAction.addResponse(s"Theory '$theoryName' has no explicit imports.")
            case None => ChatAction.addResponse(s"No imports found in theory '$theoryName'.")
          }
        case None => ChatAction.addResponse(s"Theory '$theoryName' not found in open buffers. Use :theories to list available theories.")
      }
    } catch { case ex: Exception => ChatAction.addResponse(s"Error getting dependencies: ${ex.getMessage}") }
  }

  def search(view: View, args: String): Unit = {
    val parts = args.split("\\s+", 2)
    if (parts.length < 2) { ChatAction.addResponse("Usage: `:search <theory> <pattern>`"); return }
    val theoryName = parts(0)
    val pattern = parts(1)
    val maxResults = 20
    try {
      findBuffer(theoryName) match {
        case Some(buffer) =>
          val lines = buffer.getText(0, buffer.getLength).split("\n")
          val allMatches = lines.zipWithIndex.filter(_._1.toLowerCase.contains(pattern.toLowerCase))
          val shown = allMatches.take(maxResults)
          if (shown.nonEmpty) {
            val matchList = shown.map { case (line, idx) => s"Line ${idx + 1}: ${line.trim}" }.mkString("\n")
            val truncated = if (allMatches.length > maxResults) s"\n\n... (showing $maxResults of ${allMatches.length} matches)" else ""
            ChatAction.addResponse(s"**Found matches in $theoryName:**\n\n$matchList$truncated")
          } else ChatAction.addResponse(s"No matches found for '$pattern' in theory '$theoryName'.")
        case None => ChatAction.addResponse(s"Theory '$theoryName' not found in open buffers. Use :theories to list available theories.")
      }
    } catch { case ex: Exception => ChatAction.addResponse(s"Error searching theory: ${ex.getMessage}") }
  }

  private def findBuffer(theoryName: String): Option[org.gjt.sp.jedit.buffer.JEditBuffer] =
    MenuContext.findTheoryBuffer(theoryName)
}
