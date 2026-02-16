/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import scala.jdk.CollectionConverters._
import java.util.concurrent.{CountDownLatch, TimeUnit}
import software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator

/**
 * Tool definitions and execution for LLM tool use (Anthropic function calling).
 * Tools give the LLM autonomous access to theory files, goal state, and Isabelle queries.
 */
object AssistantTools {

  case class ToolParam(name: String, typ: String, description: String, required: Boolean = false)
  case class ToolDef(name: String, description: String, params: List[ToolParam])

  val tools: List[ToolDef] = List(
    ToolDef("read_theory",
      "Read lines from an open Isabelle theory file. Returns the file content. Use start_line/end_line to read a specific range.",
      List(
        ToolParam("theory", "string", "Theory name (e.g. 'Foo' or 'Foo.thy')", required = true),
        ToolParam("start_line", "integer", "First line to read (1-based, default: 1)"),
        ToolParam("end_line", "integer", "Last line to read (default: end of file)")
      )),
    ToolDef("list_theories",
      "List all currently open Isabelle theory files.",
      Nil),
    ToolDef("search_in_theory",
      "Search for a text pattern in an open theory file. Returns matching lines with line numbers.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam("pattern", "string", "Text pattern to search for (case-insensitive)", required = true),
        ToolParam("max_results", "integer", "Maximum results to return (default: 20)")
      )),
    ToolDef("get_goal_state",
      "Get the current proof goal state at the cursor position. Returns the goal or empty if not in a proof.",
      Nil),
    ToolDef("get_proof_context",
      "Get local facts and assumptions in scope at the cursor position.",
      Nil),
    ToolDef("find_theorems",
      "Search for Isabelle theorems matching a pattern. Requires I/Q plugin.",
      List(
        ToolParam("pattern", "string", "Search pattern for find_theorems", required = true),
        ToolParam("max_results", "integer", "Maximum results (default: 20)")
      )),
    ToolDef("verify_proof",
      "Verify a proof method against the current goal using Isabelle. Returns success/failure. Requires I/Q plugin.",
      List(
        ToolParam("proof", "string", "Proof method to verify (e.g. 'by simp', 'by auto')", required = true)
      )),
    ToolDef("run_sledgehammer",
      "Run Sledgehammer to find proofs using external ATP provers. Returns found proof methods. Requires I/Q plugin.",
      Nil)
  )

  /** Write tool definitions into a JsonGenerator as the Anthropic tools array. */
  def writeToolsJson(g: JsonGenerator): Unit = {
    g.writeArrayFieldStart("tools")
    for (tool <- tools) {
      g.writeStartObject()
      g.writeStringField("name", tool.name)
      g.writeStringField("description", tool.description)
      g.writeObjectFieldStart("input_schema")
      g.writeStringField("type", "object")
      g.writeObjectFieldStart("properties")
      for (p <- tool.params) {
        g.writeObjectFieldStart(p.name)
        g.writeStringField("type", p.typ)
        g.writeStringField("description", p.description)
        g.writeEndObject()
      }
      g.writeEndObject() // properties
      val req = tool.params.filter(_.required).map(_.name)
      if (req.nonEmpty) {
        g.writeArrayFieldStart("required")
        req.foreach(g.writeString)
        g.writeEndArray()
      }
      g.writeEndObject() // input_schema
      g.writeEndObject() // tool
    }
    g.writeEndArray()
  }

  /** Maximum length for string arguments from LLM tool calls. */
  private val MAX_STRING_ARG_LENGTH = 10000
  /** Maximum length for proof text arguments. */
  private val MAX_PROOF_ARG_LENGTH = 5000
  /** Maximum length for search pattern arguments. */
  private val MAX_PATTERN_ARG_LENGTH = 500
  /** Valid theory name pattern. */
  private val THEORY_NAME_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters. */
  private def safeStringArg(args: Map[String, Any], key: String, maxLen: Int = MAX_STRING_ARG_LENGTH): String = {
    val raw = args.getOrElse(key, "").toString
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    cleaned.take(maxLen).trim
  }

  /** Validate a theory name argument. */
  private def safeTheoryArg(args: Map[String, Any]): Either[String, String] = {
    val name = safeStringArg(args, "theory", 200)
    if (name.isEmpty) Left("Error: theory name required")
    else if (THEORY_NAME_PATTERN.findFirstIn(name).isEmpty) Left(s"Error: invalid theory name '$name'")
    else Right(name)
  }

  /**
   * Execute a tool by name. Returns the result as a string.
   * Called from the agentic loop on a background thread.
   * All arguments are sanitized before use to prevent injection or resource exhaustion.
   */
  def executeTool(name: String, args: Map[String, Any], view: View): String = {
    Output.writeln(s"[Assistant] Tool call: $name(${args.map { case (k, v) => s"$k=${v.toString.take(100)}" }.mkString(", ")})")
    AssistantDockable.setStatus(s"[tool] $name...")
    try {
      name match {
        case "read_theory" => execReadTheory(args, view)
        case "list_theories" => execListTheories()
        case "search_in_theory" => execSearchInTheory(args, view)
        case "get_goal_state" => execGetGoalState(view)
        case "get_proof_context" => execGetProofContext(view)
        case "find_theorems" => execFindTheorems(args, view)
        case "verify_proof" => execVerifyProof(args, view)
        case "run_sledgehammer" => execRunSledgehammer(view)
        case _ => s"Unknown tool: $name"
      }
    } catch {
      case ex: Exception => s"Tool error: ${ex.getMessage}"
    }
  }

  private def execReadTheory(args: Map[String, Any], view: View): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
      val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
      findBuffer(normalized) match {
        case None => s"Theory '$theory' not found in open buffers."
        case Some(buffer) =>
          val content = buffer.getText(0, buffer.getLength)
          val allLines = content.split("\n")
          val start = math.max(0, intArg(args, "start_line", 1) - 1)
          val end = math.min(allLines.length, intArg(args, "end_line", allLines.length))
          val lines = allLines.slice(start, end)
          val header = s"Theory $theory (lines ${start + 1}-$end of ${allLines.length}):\n"
          header + lines.zipWithIndex.map { case (l, i) => s"${start + i + 1}: $l" }.mkString("\n")
      }
    }
  }

  private def execListTheories(): String = {
    val buffers = org.gjt.sp.jedit.jEdit.getBufferManager().getBuffers().asScala
    val theories = buffers.filter(b => b.getPath != null && b.getPath.endsWith(".thy"))
      .map(b => java.io.File(b.getPath).getName).sorted
    if (theories.nonEmpty) theories.mkString("\n") else "No theory files open."
  }

  private def execSearchInTheory(args: Map[String, Any], view: View): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
      if (pattern.isEmpty) "Error: pattern required"
      else {
      val normalized = if (theory.endsWith(".thy")) theory else s"$theory.thy"
      findBuffer(normalized) match {
        case None => s"Theory '$theory' not found."
        case Some(buffer) =>
          val max = math.min(AssistantConstants.MAX_SEARCH_RESULTS, math.max(1, intArg(args, "max_results", 20)))
          val lines = buffer.getText(0, buffer.getLength).split("\n")
          val matches = lines.zipWithIndex
            .filter(_._1.toLowerCase.contains(pattern.toLowerCase))
            .take(max)
          if (matches.isEmpty) s"No matches for '$pattern' in $theory."
          else matches.map { case (l, i) => s"${i + 1}: ${l.trim}" }.mkString("\n")
      }
      }
    }
  }

  private def execGetGoalState(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var result = "No goal at cursor position."
    GUI_Thread.later {
      try {
        val buffer = view.getBuffer
        val offset = view.getTextArea.getCaretPosition
        GoalExtractor.getGoalState(buffer, offset).foreach(g => result = g)
      } catch { case _: Exception => }
      latch.countDown()
    }
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    result
  }

  private def execGetProofContext(view: View): String = {
    // getContextString must be called from a background thread (it dispatches to GUI internally)
    PrintContextAction.getContextString(view).getOrElse("No local facts in scope.")
  }

  private def execFindTheorems(args: Map[String, Any], view: View): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      // Read buffer/offset on GUI thread
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          val buffer = view.getBuffer
          val offset = view.getTextArea.getCaretPosition
          commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val max = math.min(AssistantConstants.MAX_FIND_THEOREMS_RESULTS, math.max(1, intArg(args, "max_results", 20)))
          val timeout = AssistantOptions.getFindTheoremsTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          val quoted = if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

          GUI_Thread.later {
            IQIntegration.runFindTheoremsAsync(view, command, quoted, max, timeout, {
              case Right(results) =>
                result = if (results.nonEmpty) results.mkString("\n") else s"No theorems found for: $pattern"
                latch.countDown()
              case Left(err) =>
                result = s"Error: $err"
                latch.countDown()
            })
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "find_theorems timed out." else result
      }
    }
  }

  private def execVerifyProof(args: Map[String, Any], view: View): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getVerificationTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.verifyProofAsync(view, command, proof, timeout, {
              case IQIntegration.ProofSuccess(ms, _) => result = s"[ok] Proof verified (${ms}ms)"; latch.countDown()
              case IQIntegration.ProofFailure(err) => result = s"[FAIL] Failed: $err"; latch.countDown()
              case IQIntegration.ProofTimeout => result = "[FAIL] Timed out"; latch.countDown()
              case _ => result = "[FAIL] Unavailable"; latch.countDown()
            })
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Verification timed out." else result
      }
    }
  }

  private def execRunSledgehammer(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val cmdLatch = new CountDownLatch(1)
      @volatile var commandOpt: Option[Command] = None
      GUI_Thread.later {
        try {
          commandOpt = IQIntegration.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition)
        } catch { case _: Exception => }
        cmdLatch.countDown()
      }
      cmdLatch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)

      commandOpt match {
        case None => "No Isabelle command at cursor position."
        case Some(command) =>
          val timeout = AssistantOptions.getSledgehammerTimeout
          val latch = new CountDownLatch(1)
          @volatile var result = ""
          GUI_Thread.later {
            IQIntegration.runSledgehammerAsync(view, command, timeout, {
              case Right(results) if results.nonEmpty =>
                result = results.map(r => s"${r.proofMethod} (${r.timeMs}ms)").mkString("\n")
                latch.countDown()
              case Right(_) => result = "No proofs found."; latch.countDown()
              case Left(err) => result = s"Error: $err"; latch.countDown()
            })
          }
          latch.await(timeout + 2000, TimeUnit.MILLISECONDS)
          if (result.isEmpty) "Sledgehammer timed out." else result
      }
    }
  }

  private def findBuffer(normalized: String): Option[org.gjt.sp.jedit.buffer.JEditBuffer] =
    MenuContext.findTheoryBuffer(normalized)

  private def intArg(args: Map[String, Any], key: String, default: Int): Int = {
    args.get(key) match {
      case Some(n: Number) => n.intValue()
      case Some(s: String) => try { s.toInt } catch { case _: NumberFormatException => default }
      case _ => default
    }
  }
}
