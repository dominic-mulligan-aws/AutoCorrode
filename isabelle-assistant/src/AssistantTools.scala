/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}
import java.util.Locale
import scala.annotation.unused
import scala.util.control.NonFatal
import scala.jdk.CollectionConverters._
import software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator

/** Tool definitions and execution for LLM tool use (Anthropic function
  * calling). Tools give the LLM autonomous access to theory files, goal state,
  * and Isabelle queries.
  */
object AssistantTools {

  case class ToolParam(
      name: String,
      typ: String,
      description: String,
      required: Boolean = false
  )
  case class ToolDef private (
      id: ToolId,
      description: String,
      params: List[ToolParam]
  ) {
    val name: String = id.wireName
  }
  object ToolDef {
    def apply(id: ToolId, description: String, params: List[ToolParam]): ToolDef =
      new ToolDef(id, description, params)

    def apply(name: String, description: String, params: List[ToolParam]): ToolDef =
      ToolId
        .fromWire(name)
        .map(id => new ToolDef(id, description, params))
        .getOrElse(
          throw new IllegalArgumentException(s"Unknown tool name in definition: $name")
        )
  }

  val tools: List[ToolDef] = List(
    ToolDef(
      "read_theory",
      "Read lines from an open Isabelle theory file. Returns the file content. Use start_line/end_line to read a specific range. Large files are automatically truncated; use start_line/end_line for precise ranges.",
      List(
        ToolParam(
          "theory",
          "string",
          "Theory name (e.g. 'Foo' or 'Foo.thy')",
          required = true
        ),
        ToolParam(
          "start_line",
          "integer",
          "First line to read (1-based, default: 1)"
        ),
        ToolParam(
          "end_line",
          "integer",
          "Last line to read (default: end of file)"
        ),
        ToolParam(
          "max_lines",
          "integer",
          "Maximum lines to return (default: 300). Use start_line/end_line for precise ranges instead."
        )
      )
    ),
    ToolDef(
      "list_theories",
      "List all currently open Isabelle theory files.",
      Nil
    ),
    ToolDef(
      "search_in_theory",
      "Search for a text pattern in an open theory file. Returns matching lines with line numbers.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum results to return (default: 20)"
        )
      )
    ),
    ToolDef(
      "search_theories",
      "Search for a text pattern in theory files. Unified tool replacing search_in_theory and search_all_theories. Returns matching lines with theory names and line numbers.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "scope",
          "string",
          "Scope: 'current' (current buffer), 'all' (all open theories), or a theory name",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum results to return (default: 20)"
        )
      )
    ),
    ToolDef(
      "get_goal_state",
      "Get the current proof goal state at the cursor position. Returns the goal or empty if not in a proof.",
      Nil
    ),
    ToolDef(
      "get_subgoal",
      "Extract a single subgoal by index from the current proof state. More efficient than get_goal_state for multi-subgoal proofs when you only need to focus on one subgoal.",
      List(
        ToolParam(
          "index",
          "integer",
          "Subgoal index (1-based). Use 1 for the first subgoal.",
          required = true
        )
      )
    ),
    ToolDef(
      "get_proof_context",
      "Get local facts and assumptions in scope at the cursor position.",
      Nil
    ),
    ToolDef(
      "find_theorems",
      "Search for Isabelle theorems matching a pattern. Requires I/Q plugin.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Search pattern for find_theorems",
          required = true
        ),
        ToolParam("max_results", "integer", "Maximum results (default: 20)")
      )
    ),
    ToolDef(
      "verify_proof",
      "Verify a proof method against the current goal using Isabelle. Returns success/failure. Requires I/Q plugin.",
      List(
        ToolParam(
          "proof",
          "string",
          "Proof method to verify (e.g. 'by simp', 'by auto')",
          required = true
        )
      )
    ),
    ToolDef(
      "run_sledgehammer",
      "Run Sledgehammer to find proofs using external ATP provers. Returns found proof methods. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "run_nitpick",
      "Run Nitpick model finder to search for counterexamples to the current goal. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "run_quickcheck",
      "Run QuickCheck to test the current goal with random examples. Returns counterexample if found. Requires I/Q plugin.",
      Nil
    ),
    ToolDef(
      "find_counterexample",
      "Search for counterexamples to the current goal using Nitpick or QuickCheck. Returns counterexample if found. Requires I/Q plugin.",
      List(
        ToolParam(
          "method",
          "string",
          "Method: 'nitpick', 'quickcheck', or 'both' (default: 'quickcheck')"
        )
      )
    ),
    ToolDef(
      "get_type",
      "Get type information for the term at the cursor position. Returns the term and its type.",
      Nil
    ),
    ToolDef(
      "get_command_text",
      "Get the source text of the Isabelle command at the cursor position.",
      Nil
    ),
    ToolDef(
      "get_errors",
      "Get error messages from PIDE's processed region. IMPORTANT: Only returns errors from the already-processed portion of the theory. To check if a file is completely error-free, first use set_cursor_position to move to the end of the file, then call get_errors. By default returns all errors in the current buffer with line numbers. Use scope='cursor' to get only errors at cursor position.",
      List(
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all errors in current buffer), 'cursor' (only at cursor position), or a theory name"
        )
      )
    ),
    ToolDef(
      "get_diagnostics",
      "Get error or warning messages from PIDE's processed region. IMPORTANT: Only returns diagnostics from the already-processed portion of the theory. To check if a file is completely error/warning-free, first use set_cursor_position to move to the end of the file, then call get_diagnostics.",
      List(
        ToolParam(
          "severity",
          "string",
          "Severity level: 'error', 'warning', or 'all'",
          required = true
        ),
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all diagnostics in current buffer), 'cursor' (only at cursor position), or a theory name"
        ),
        ToolParam(
          "count_only",
          "boolean",
          "Return only counts instead of full diagnostic messages (default: false)"
        )
      )
    ),
    ToolDef(
      "get_definitions",
      "Get definitions for specified constant or type names. Returns the definition text for each name. Requires I/Q plugin.",
      List(
        ToolParam(
          "names",
          "string",
          "Space-separated list of constant/type names to look up",
          required = true
        )
      )
    ),
    ToolDef(
      "get_file_stats",
      "Get file statistics (line count, entity count, processing status) without reading full content. Efficient alternative to read_theory + get_entities for overview. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "get_processing_status",
      "Get PIDE processing status (unprocessed/running/finished/failed command counts). Use this to check if a theory has been fully processed before querying for errors. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "get_sorry_positions",
      "Find all sorry/oops commands in a theory file with their line numbers and enclosing proof names. Useful for identifying incomplete proofs. Requires I/Q plugin.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "execute_step",
      "Execute a proof step and return the resulting proof state. Use this to explore what happens when you apply a proof method. Returns the new goal state and whether the proof is complete. Requires I/Q plugin.",
      List(
        ToolParam(
          "proof",
          "string",
          "Proof text to execute (e.g., 'by simp', 'apply auto')",
          required = true
        )
      )
    ),
    ToolDef(
      "trace_simplifier",
      "Trace the simplifier to understand rewriting steps. Returns detailed trace of simp/auto operations. Output is automatically truncated to prevent context overflow. Requires I/Q plugin.",
      List(
        ToolParam(
          "method",
          "string",
          "Method to trace: 'simp' or 'auto' (default: 'simp')"
        ),
        ToolParam(
          "max_lines",
          "integer",
          "Maximum lines to return (default: 100). Traces can be very long."
        )
      )
    ),
    ToolDef(
      "get_proof_block",
      "Get the full proof block (lemma/theorem...qed/done) at the cursor position. Returns the complete proof text including the statement.",
      Nil
    ),
    ToolDef(
      "get_proof_outline",
      "Get a structural outline of the proof block at the cursor position. Returns only the proof skeleton (keyword lines) with line numbers, filtering out proof details. Useful for understanding proof structure without full content.",
      Nil
    ),
    ToolDef(
      "get_context_info",
      "Get structured context information at cursor: whether in a proof, whether there's a goal, whether on an error, etc. Returns a summary of the cursor context.",
      List(
        ToolParam(
          "quick",
          "boolean",
          "Quick mode: skip diagnostic and type checks for faster response (default: false)"
        )
      )
    ),
    ToolDef(
      "search_all_theories",
      "Search for a text pattern across all open theory files. Returns matching lines with theory names and line numbers.",
      List(
        ToolParam(
          "pattern",
          "string",
          "Text pattern to search for (case-insensitive)",
          required = true
        ),
        ToolParam(
          "max_results",
          "integer",
          "Maximum total results across all theories (default: 20)"
        )
      )
    ),
    ToolDef(
      "get_dependencies",
      "Get the import dependencies for a specific theory file. Returns the list of imported theories.",
      List(
        ToolParam("theory", "string", "Theory name", required = true)
      )
    ),
    ToolDef(
      "get_warnings",
      "Get warning messages from PIDE's processed region. IMPORTANT: Only returns warnings from the already-processed portion of the theory. To check if a file is completely warning-free, first use set_cursor_position to move to the end of the file, then call get_warnings. By default returns all warnings in the current buffer with line numbers. Use scope='cursor' to get only warnings at cursor position.",
      List(
        ToolParam(
          "scope",
          "string",
          "Scope: 'all' (default, all warnings in current buffer), 'cursor' (only at cursor position), or a theory name"
        )
      )
    ),
    ToolDef(
      "set_cursor_position",
      "Move the cursor to a specific line number in the current theory. This allows inspection of goals and context at different positions. Returns confirmation or error.",
      List(
        ToolParam(
          "line",
          "integer",
          "Line number to move cursor to (1-based)",
          required = true
        )
      )
    ),
    ToolDef(
      "edit_theory",
      "Edit a theory file by inserting, replacing, or deleting text at specified line ranges. Use read_theory first to see current content. For multi-line inserts/replacements, include literal \\n characters in the text parameter. All edits are wrapped in compound edits for proper undo support.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam(
          "operation",
          "string",
          "Operation: 'insert', 'replace', or 'delete'",
          required = true
        ),
        ToolParam(
          "start_line",
          "integer",
          "Starting line number (1-based)",
          required = true
        ),
        ToolParam(
          "end_line",
          "integer",
          "Ending line number for replace/delete operations (1-based, inclusive)"
        ),
        ToolParam(
          "text",
          "string",
          "Text to insert or use as replacement (required for insert/replace)"
        )
      )
    ),
    ToolDef(
      "try_methods",
      "Try multiple proof methods at once and return which ones succeed. More efficient than calling verify_proof repeatedly. Returns results for all methods. Requires I/Q plugin.",
      List(
        ToolParam(
          "methods",
          "string",
          "Comma-separated list of proof methods to try (e.g., 'by simp, by auto, by blast')",
          required = true
        )
      )
    ),
    ToolDef(
      "get_entities",
      "List all named entities (lemmas, definitions, datatypes, etc.) in a theory file with their line numbers. Returns a structured listing of the theory's contents.",
      List(
        ToolParam("theory", "string", "Theory name", required = true),
        ToolParam(
          "max_results",
          "integer",
          "Maximum entities to return (default: 50)"
        )
      )
    ),
    ToolDef(
      "create_theory",
      "Create a new Isabelle theory file in the same directory as the current buffer. The file will be opened in jEdit after creation.",
      List(
        ToolParam(
          "name",
          "string",
          "Theory name (without .thy extension)",
          required = true
        ),
        ToolParam(
          "imports",
          "string",
          "Space-separated list of theories to import (default: 'Main')"
        ),
        ToolParam(
          "content",
          "string",
          "Initial content to add after 'begin' (optional)"
        )
      )
    ),
    ToolDef(
      "open_theory",
      "Open an existing theory file that is not currently open. Makes it available for inspection and editing with other tools.",
      List(
        ToolParam(
          "path",
          "string",
          "Path to theory file (relative or absolute)",
          required = true
        )
      )
    ),
    ToolDef(
      "ask_user",
      "Ask the user a multiple-choice question when you are uncertain about something, need clarification on their intent, or want their perspective on a decision. The user will see the question and options in the chat panel and click their choice. Use this sparingly — only when the answer genuinely affects your approach.",
      List(
        ToolParam(
          "question",
          "string",
          "The question to present to the user. Be clear and concise.",
          required = true
        ),
        ToolParam(
          "options",
          "string",
          "Comma-separated list of short option labels (minimum 2). Keep options brief and clear for best UX.",
          required = true
        ),
        ToolParam(
          "context",
          "string",
          "Optional brief context explaining why you're asking (shown as a subtitle)"
        )
      )
    ),
    ToolDef(
      "task_list_add",
      "Add a new task to the session task list. Each task should have a clear title, detailed description of what needs to be done, and specific acceptance criteria for completion.",
      List(
        ToolParam(
          "title",
          "string",
          "Brief task title (e.g., 'Implement authentication')",
          required = true
        ),
        ToolParam(
          "description",
          "string",
          "Detailed description of what needs to be done",
          required = true
        ),
        ToolParam(
          "acceptance_criteria",
          "string",
          "Clear criteria for when the task is considered complete",
          required = true
        )
      )
    ),
    ToolDef(
      "task_list_done",
      "Mark a task as completed. Use this when a task has been successfully finished and all acceptance criteria have been met.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to mark as done",
          required = true
        )
      )
    ),
    ToolDef(
      "task_list_irrelevant",
      "Mark a task as irrelevant or no longer needed. Use this when a task is obsolete, out of scope, or superseded by other work.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to mark as irrelevant",
          required = true
        )
      )
    ),
    ToolDef(
      "task_list_next",
      "Get the next pending task to work on. Returns the first task in the list that has not been completed or marked irrelevant.",
      Nil
    ),
    ToolDef(
      "task_list_show",
      "Show all tasks in the task list with their current statuses. Displays a visual overview of progress.",
      Nil
    ),
    ToolDef(
      "task_list_get",
      "Get detailed information about a specific task, including its full description and acceptance criteria.",
      List(
        ToolParam(
          "task_id",
          "integer",
          "The ID of the task to retrieve details for",
          required = true
        )
      )
    )
  )

  private val toolsById: Map[ToolId, ToolDef] = tools.map(t => t.id -> t).toMap
  require(
    toolsById.size == tools.size,
    "Tool definitions must have unique tool IDs."
  )
  require(
    toolsById.keySet == ToolId.values.toSet,
    "Tool definitions must cover all ToolId values exactly."
  )
  private[assistant] def toolDefinition(toolId: ToolId): Option[ToolDef] =
    toolsById.get(toolId)

  /** Write a single tool definition to a JsonGenerator. Shared helper for writeToolsJson and writeFilteredToolsJson. */
  private def writeToolJson(g: JsonGenerator, tool: ToolDef): Unit = {
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
      // Add enum constraints for specific parameters
      if (tool.id == ToolId.EditTheory && p.name == "operation") {
        g.writeArrayFieldStart("enum")
        g.writeString("insert")
        g.writeString("replace")
        g.writeString("delete")
        g.writeEndArray()
      } else if (
        (tool.id == ToolId.GetErrors || tool.id == ToolId.GetWarnings) && p.name == "scope"
      ) {
        g.writeArrayFieldStart("enum")
        g.writeString("all")
        g.writeString("cursor")
        g.writeEndArray()
      }
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

  /** Write tool definitions into a JsonGenerator as the Anthropic tools array.
    */
  def writeToolsJson(g: JsonGenerator): Unit = {
    g.writeArrayFieldStart("tools")
    for (tool <- tools) writeToolJson(g, tool)
    g.writeEndArray()
  }

  /**
   * Write filtered tool definitions (excludes Deny-level tools).
   * Used when sending tools to the LLM to prevent it from seeing/using denied tools.
   */
  def writeFilteredToolsJson(g: JsonGenerator): Unit = {
    val visibleTools = ToolPermissions.getVisibleTools
    g.writeArrayFieldStart("tools")
    for (tool <- visibleTools) writeToolJson(g, tool)
    g.writeEndArray()
  }

  /**
   * Execute a tool with permission checking.
   * Wraps executeTool with capability-based authorization.
   * Returns tool result or permission denial message.
   */
  sealed trait ToolExecResult {
    def toUserMessage: String
  }
  object ToolExecResult {
    case class Success(output: String) extends ToolExecResult {
      def toUserMessage: String = output
    }
    case class UnknownTool(name: String) extends ToolExecResult {
      def toUserMessage: String = s"Unknown tool: $name"
    }
    case class PermissionDenied(message: String) extends ToolExecResult {
      def toUserMessage: String = message
    }
    case class ExecutionFailure(toolId: ToolId, message: String)
        extends ToolExecResult {
      def toUserMessage: String = s"Tool error: $message"
    }
  }
  import ToolExecResult._

  private val toolHandlers: Map[ToolId, (ResponseParser.ToolArgs, View) => String] =
    Map(
      ToolId.ReadTheory -> ((a, v) => execReadTheory(a, v)),
      ToolId.ListTheories -> ((_, _) => execListTheories()),
      ToolId.SearchInTheory -> ((a, v) => execSearchInTheory(a, v)),
      ToolId.SearchTheories -> ((a, v) => execSearchTheories(a, v)),
      ToolId.GetGoalState -> ((_, v) => execGetGoalState(v)),
      ToolId.GetSubgoal -> ((a, v) => execGetSubgoal(a, v)),
      ToolId.GetProofContext -> ((_, v) => execGetProofContext(v)),
      ToolId.FindTheorems -> ((a, v) => execFindTheorems(a, v)),
      ToolId.VerifyProof -> ((a, v) => execVerifyProof(a, v)),
      ToolId.RunSledgehammer -> ((_, v) => execRunSledgehammer(v)),
      ToolId.RunNitpick -> ((_, v) => execRunNitpick(v)),
      ToolId.RunQuickcheck -> ((_, v) => execRunQuickcheck(v)),
      ToolId.FindCounterexample -> ((a, v) => execFindCounterexample(a, v)),
      ToolId.GetType -> ((_, v) => execGetType(v)),
      ToolId.GetCommandText -> ((_, v) => execGetCommandText(v)),
      ToolId.GetErrors -> ((a, v) => execGetErrors(a, v)),
      ToolId.GetDiagnostics -> ((a, v) => execGetDiagnosticsUnified(a, v)),
      ToolId.GetDefinitions -> ((a, v) => execGetDefinitions(a, v)),
      ToolId.GetFileStats -> ((a, v) => execGetFileStats(a, v)),
      ToolId.GetProcessingStatus -> ((a, v) => execGetProcessingStatus(a, v)),
      ToolId.GetSorryPositions -> ((a, v) => execGetSorryPositions(a, v)),
      ToolId.ExecuteStep -> ((a, v) => execExecuteStep(a, v)),
      ToolId.TraceSimplifier -> ((a, v) => execTraceSimplifier(a, v)),
      ToolId.GetProofBlock -> ((_, v) => execGetProofBlock(v)),
      ToolId.GetProofOutline -> ((_, v) => execGetProofOutline(v)),
      ToolId.GetContextInfo -> ((a, v) => execGetContextInfo(a, v)),
      ToolId.SearchAllTheories -> ((a, v) => execSearchAllTheories(a, v)),
      ToolId.GetDependencies -> ((a, v) => execGetDependencies(a, v)),
      ToolId.GetWarnings -> ((a, v) => execGetWarnings(a, v)),
      ToolId.SetCursorPosition -> ((a, v) => execSetCursorPosition(a, v)),
      ToolId.EditTheory -> ((a, v) => execEditTheory(a, v)),
      ToolId.TryMethods -> ((a, v) => execTryMethods(a, v)),
      ToolId.GetEntities -> ((a, v) => execGetEntities(a, v)),
      ToolId.CreateTheory -> ((a, v) => execCreateTheory(a, v)),
      ToolId.OpenTheory -> ((a, v) => execOpenTheory(a, v)),
      ToolId.AskUser -> ((a, v) => execAskUser(a, v)),
      ToolId.TaskListAdd -> ((a, v) => execTaskListAdd(a, v)),
      ToolId.TaskListDone -> ((a, v) => execTaskListDone(a, v)),
      ToolId.TaskListIrrelevant -> ((a, v) => execTaskListIrrelevant(a, v)),
      ToolId.TaskListNext -> ((_, v) => execTaskListNext(v)),
      ToolId.TaskListShow -> ((_, v) => execTaskListShow(v)),
      ToolId.TaskListGet -> ((a, v) => execTaskListGet(a, v))
    )

  def executeToolWithPermission(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    executeToolWithPermissionResult(name, args, view).toUserMessage

  def executeToolWithPermissionResult(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult =
    ToolId.fromWire(name) match {
      case Some(toolId) => executeToolWithPermissionResult(toolId, args, view)
      case None         => UnknownTool(name)
    }

  private def executeToolWithPermissionResult(
      toolId: ToolId,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult = {
    ToolPermissions.checkPermission(toolId, args) match {
      case ToolPermissions.Allowed =>
        executeToolResult(toolId, args, view)
      case ToolPermissions.Denied =>
        val name = toolId.wireName
        safeLog(s"[Permissions] Tool '$name' denied by policy")
        PermissionDenied(s"Permission denied: tool '$name' is not allowed.")
      case ToolPermissions.NeedPrompt(promptToolId, resource, details) =>
        val toolName = promptToolId.wireName
        ToolPermissions.promptUser(promptToolId, resource, details, view) match {
          case ToolPermissions.Allowed =>
            executeToolResult(toolId, args, view)
          case ToolPermissions.Denied =>
            safeLog(s"[Permissions] User denied tool '$toolName'")
            PermissionDenied(
              s"Permission denied: user declined tool '$toolName'."
            )
          case _ =>
            safeLog(s"[Permissions] Unexpected decision for tool '$toolName'")
            PermissionDenied(s"Permission denied: tool '$toolName'.")
        }
    }
  }

  /** Maximum length for string arguments from LLM tool calls. */
  private val MAX_STRING_ARG_LENGTH = 10000

  /** Maximum length for proof text arguments. */
  private val MAX_PROOF_ARG_LENGTH = 5000

  /** Maximum length for search pattern arguments. */
  private val MAX_PATTERN_ARG_LENGTH = 500

  /** Valid theory reference pattern (for referring to already-open theories). */
  private val THEORY_REFERENCE_PATTERN = """^[A-Za-z0-9_.\-/]+$""".r

  /** Valid new theory file name (single file name, no path separators). */
  private val CREATE_THEORY_NAME_PATTERN = """^[A-Za-z][A-Za-z0-9_']*$""".r

  /** Sanitize a string argument: trim, limit length, reject control characters.
    */
  private def safeStringArg(
      args: ResponseParser.ToolArgs,
      key: String,
      maxLen: Int = MAX_STRING_ARG_LENGTH,
      trim: Boolean = true
  ): String = {
    val raw = args.get(key).map(ResponseParser.toolValueToString).getOrElse("")
    val cleaned = raw.filter(c => !c.isControl || c == '\n' || c == '\t')
    val limited = cleaned.take(maxLen)
    if (trim) limited.trim else limited
  }

  /** Validate a theory name argument. */
  private def safeTheoryArg(
      args: ResponseParser.ToolArgs
  ): Either[String, String] = {
    val name = safeStringArg(args, "theory", 200)
    if (name.isEmpty) Left("Error: theory name required")
    else if (THEORY_REFERENCE_PATTERN.findFirstIn(name).isEmpty)
      Left(s"Error: invalid theory name '$name'")
    else Right(name)
  }

  private[assistant] def isValidCreateTheoryName(name: String): Boolean =
    CREATE_THEORY_NAME_PATTERN.findFirstIn(name).isDefined

  private[assistant] def normalizeReadRange(
      totalLines: Int,
      requestedStart: Int,
      requestedEnd: Int
  ): (Int, Int) = {
    if (totalLines <= 0) (1, 0)
    else {
      val start = math.max(1, math.min(totalLines, requestedStart))
      val rawEnd = if (requestedEnd <= 0) totalLines else requestedEnd
      val end = math.max(start, math.min(totalLines, rawEnd))
      (start, end)
    }
  }

  private[assistant] def clampOffset(offset: Int, bufferLength: Int): Int =
    math.max(0, math.min(offset, bufferLength))

  private val readToolsTimeoutMs: Long =
    AssistantConstants.CONTEXT_FETCH_TIMEOUT + AssistantConstants.TIMEOUT_BUFFER_MS

  private val numberedLinePattern = """^\s*(?:→\s*)?(\d+):(.*)$""".r
  private final case class ViewStateSnapshot(
      path: Option[String],
      caretOffset: Int,
      bufferLength: Int
  )

  private def normalizeTheoryFileName(raw: String): String = {
    val trimmed = raw.trim
    if (trimmed.endsWith(".thy")) trimmed else s"$trimmed.thy"
  }

  private def baseName(path: String): String =
    java.nio.file.Paths.get(path).getFileName.toString

  private def optionalIntArg(args: ResponseParser.ToolArgs, key: String): Option[Int] =
    args.get(key).map {
      case ResponseParser.DecimalValue(d) if !d.isWhole =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer, got decimal value: $d"
        )
      case ResponseParser.DecimalValue(d) => d.toInt
      case ResponseParser.IntValue(i)     => i
      case ResponseParser.StringValue(s) =>
        scala.util.Try(s.toInt).getOrElse(
          throw new IllegalArgumentException(
            s"Parameter '$key' must be an integer, got: '$s'"
          )
        )
      case ResponseParser.BooleanValue(_) | ResponseParser.JsonValue(_) =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
      case ResponseParser.NullValue =>
        throw new IllegalArgumentException(
          s"Parameter '$key' must be an integer"
        )
    }

  private def boolArg(args: ResponseParser.ToolArgs, key: String, default: Boolean): Boolean =
    args.get(key) match {
      case Some(ResponseParser.BooleanValue(b)) => b
      case Some(ResponseParser.StringValue(s)) => 
        s.trim.toLowerCase match {
          case "true" => true
          case "false" => false
          case _ => default
        }
      case _ => default
    }

  private def snapshotViewState(view: View): Option[ViewStateSnapshot] =
    Option(view).flatMap { v =>
      try {
        Some(
          GUI_Thread.now {
            val bufferOpt = Option(v.getBuffer)
            val path =
              bufferOpt.flatMap(b => Option(b.getPath)).map(_.trim).filter(_.nonEmpty)
            val bufferLength = bufferOpt.map(_.getLength).getOrElse(0)
            val caretOffset = Option(v.getTextArea).map(_.getCaretPosition).getOrElse(0)
            ViewStateSnapshot(path, caretOffset, bufferLength)
          }
        )
      } catch {
        case _: Exception => None
      }
    }

  private def selectionArgsForCurrentView(view: View): Map[String, Any] =
    snapshotViewState(view)
      .flatMap(snapshot =>
        snapshot.path.map(path =>
          Map(
            "command_selection" -> "file_offset",
            "path" -> path,
            "offset" -> clampOffset(snapshot.caretOffset, snapshot.bufferLength)
          )
        )
      )
      .getOrElse(Map("command_selection" -> "current"))

  private def currentBufferPath(view: View): Either[String, String] =
    snapshotViewState(view)
      .flatMap(_.path)
      .toRight("Error: current buffer has no path")

  private def resolveTheoryPath(
      theory: String,
      openOnly: Boolean = true
  ): Either[String, String] = {
    val normalized = normalizeTheoryFileName(theory)
    IQMcpClient
      .callListFiles(
        filterOpen = if (openOnly) Some(true) else None,
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = readToolsTimeoutMs
      )
      .flatMap { result =>
        val matches = result.files.filter(f => baseName(f.path) == normalized)
        matches match {
          case one :: Nil => Right(one.path)
          case Nil =>
            val scopeHint =
              if (openOnly) "open or tracked theory files" else "tracked theory files"
            Left(s"Theory '$theory' not found in $scopeHint.")
          case many =>
            Left(
              s"Theory '$theory' is ambiguous; matching paths: ${
                  many.map(_.path).mkString(", ")
                }"
            )
        }
      }
  }

  private def lineCountFromNumberedContent(content: String): Int =
    content.linesIterator.count {
      case numberedLinePattern(_, _) => true
      case _                         => false
    }

  private def stripNumberPrefix(line: String): String = line match {
    case numberedLinePattern(_, rest) => rest
    case _                            => line
  }

  private def stripNumberPrefixes(content: String): String =
    content.linesIterator.map(stripNumberPrefix).mkString("\n")

  private def firstHighlightedOrFirstLine(context: String): String = {
    val nonEmpty = context.linesIterator.map(_.trim).filter(_.nonEmpty).toList
    val picked = nonEmpty.find(_.startsWith("→")).orElse(nonEmpty.headOption).getOrElse("")
    stripNumberPrefix(picked).trim
  }

  private def formatDiagnosticsMessages(
      diagnostics: IQMcpClient.DiagnosticsResult,
      emptyMessage: String
  ): String = {
    if (diagnostics.diagnostics.isEmpty) emptyMessage
    else
      diagnostics.diagnostics
        .map { d =>
          if (d.line > 0) s"Line ${d.line}: ${d.message}" else d.message
        }
        .distinct
        .mkString("\n")
  }

  private def isSensitiveArgName(argName: String): Boolean = {
    val lowered = argName.toLowerCase(Locale.ROOT)
    AssistantConstants.SENSITIVE_ARG_TOKENS.exists(token => lowered.contains(token))
  }

  private def summarizeToolArgsForLog(args: ResponseParser.ToolArgs): String =
    args.map { case (k, v) =>
      val rendered =
        if (isSensitiveArgName(k)) "***"
        else ResponseParser.toolValueToDisplay(v).replace('\n', ' ').take(100)
      s"$k=$rendered"
    }.mkString(", ")

  private def safeLog(message: String): Unit = {
    try Output.writeln(message)
    catch {
      case NonFatal(_) | _: LinkageError => ()
    }
  }

  private def firstNonEmpty(parts: List[String]): Option[String] =
    parts.map(_.trim).find(_.nonEmpty)

  private def exploreFailureMessage(
      result: IQMcpClient.ExploreResult,
      fallback: String
  ): String =
    firstNonEmpty(List(result.error.getOrElse(""), result.message, result.results))
      .getOrElse(fallback)

  /** Execute an I/Q explore query and return formatted result string.
    * Encapsulates the common pattern: check IQ availability → call explore → format success/timeout/error.
    * 
    * @param query The query type (Proof, Sledgehammer, or FindTheorems)
    * @param arguments Query arguments (e.g., proof text, search pattern)
    * @param timeoutMs Timeout in milliseconds
    * @param toolLabel Human-readable label for error messages (e.g., "sledgehammer")
    * @param successMapper Transform successful result text (default: identity)
    * @param emptyMessage Message to return when result is empty (default: "<toolLabel> returned no output")
    * @param extraParams Additional parameters for the explore query (e.g., max_results)
    * @return Formatted result string
    */
  private def execExplore(
      query: IQMcpClient.ExploreQueryType,
      arguments: String,
      timeoutMs: Long,
      toolLabel: String,
      successMapper: String => String = identity,
      emptyMessage: String = "",
      extraParams: Map[String, Any] = Map.empty
  ): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      IQMcpClient
        .callExplore(
          query = query,
          arguments = arguments,
          timeoutMs = timeoutMs,
          extraParams = extraParams
        )
        .fold(
          mcpErr => s"Error: $toolLabel failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              val effectiveEmpty = if (emptyMessage.nonEmpty) emptyMessage 
                                   else s"$toolLabel returned no output."
              if (text.nonEmpty && text != "No results") successMapper(text)
              else effectiveEmpty
            } else if (explore.timedOut) s"$toolLabel timed out."
            else s"Error: ${exploreFailureMessage(explore, s"$toolLabel failed")}"
          }
        )
    }
  }

  /** Execute a tool by name. Returns the result as a string. Called from the
    * agentic loop on a background thread. All arguments are sanitized before
    * use to prevent injection or resource exhaustion.
    */
  def executeTool(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    executeToolResult(name, args, view).toUserMessage

  def executeToolResult(
      name: String,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult =
    ToolId.fromWire(name) match {
      case Some(toolId) => executeToolResult(toolId, args, view)
      case None         => UnknownTool(name)
    }

  private def executeToolResult(
      toolId: ToolId,
      args: ResponseParser.ToolArgs,
      view: View
  ): ToolExecResult = {
    val toolName = toolId.wireName
    safeLog(s"[Assistant] Tool call: $toolName(${summarizeToolArgsForLog(args)})")
    AssistantDockable.setStatus(s"[tool] $toolName...")
    try {
      toolHandlers.get(toolId) match {
        case Some(handler) => Success(handler(args, view))
        case None =>
          ExecutionFailure(
            toolId,
            s"No execution handler registered for tool '$toolName'"
          )
      }
    } catch {
      case ex: Exception => ExecutionFailure(toolId, ex.getMessage)
    }
  }

  /** Read lines from a theory file via I/Q MCP. Returns file content or error message. */
  private def execReadTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val start = optionalIntArg(args, "start_line")
        val end = optionalIntArg(args, "end_line")
        val maxLines = optionalIntArg(args, "max_lines")
          .map(n => math.max(1, math.min(n, 10000)))
          .getOrElse(AssistantConstants.DEFAULT_READ_THEORY_MAX_LINES)
        
        resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = start.orElse(Some(1)),
                endLine = end,
                timeoutMs = readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                numberedContent => {
                  if (numberedContent.trim.isEmpty) s"Theory $theory is empty."
                  else {
                    val totalLines = lineCountFromNumberedContent(numberedContent)
                    val lines = numberedContent.linesIterator.toList
                    
                    // Apply truncation if needed and not using explicit range
                    val (displayLines, wasTruncated) = if (start.isEmpty && end.isEmpty && lines.length > maxLines) {
                      (lines.take(maxLines), true)
                    } else {
                      (lines, false)
                    }
                    
                    val content = displayLines.mkString("\n")
                    val header = s"Theory $theory ($totalLines lines)"
                    val rangeInfo = if (start.isDefined || end.isDefined) {
                      val actualStart = start.getOrElse(1)
                      val actualEnd = end.getOrElse(totalLines)
                      s", showing lines $actualStart-$actualEnd"
                    } else if (wasTruncated) {
                      s", showing lines 1-$maxLines"
                    } else {
                      ""
                    }
                    
                    val truncationNote = if (wasTruncated) {
                      val remaining = totalLines - maxLines
                      s"\n\n... [truncated, $remaining more lines. Use start_line/end_line to read specific ranges]"
                    } else ""
                    
                    s"$header$rangeInfo:\n$content$truncationNote"
                  }
                }
              )
        )
    }
  }

  /** List all open theory files via I/Q MCP. Returns newline-separated theory names. */
  private def execListTheories(): String = {
    IQMcpClient
      .callListFiles(
        filterOpen = Some(true),
        filterTheory = Some(true),
        sortBy = Some("path"),
        timeoutMs = readToolsTimeoutMs
      )
      .fold(
        err => s"Error: $err",
        listed => {
          val theories = listed.files.map(f => baseName(f.path)).distinct.sorted
          if (theories.nonEmpty) theories.mkString("\n") else "No theory files open."
        }
      )
  }

  /** Search for text patterns in a theory file. Returns matching lines with line numbers. */
  private def execSearchInTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (pattern.isEmpty) "Error: pattern required"
        else {
          val max = math.min(
            AssistantConstants.MAX_SEARCH_RESULTS,
            math.max(1, intArg(args, "max_results", 20))
          )
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileSearch(
                  path = path,
                  pattern = pattern,
                  contextLines = 0,
                  timeoutMs = readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  matches => {
                    val shown = matches.take(max)
                    if (shown.isEmpty) s"No matches for '$pattern' in $theory."
                    else
                      shown
                        .map(m =>
                          s"${m.lineNumber}: ${firstHighlightedOrFirstLine(m.context)}"
                        )
                        .mkString("\n")
                  }
                )
          )
        }
    }
  }

  /** Unified search tool with flexible scope (current buffer, all theories, or specific theory). */
  private def execSearchTheories(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    val scope = safeStringArg(args, "scope", 200)
    if (pattern.isEmpty) "Error: pattern required"
    else if (scope.isEmpty) "Error: scope required"
    else {
      scope.toLowerCase match {
        case "current" =>
          currentBufferPath(view).fold(
            err => err,
            path => {
              val max = math.min(AssistantConstants.MAX_SEARCH_RESULTS, math.max(1, intArg(args, "max_results", 20)))
              IQMcpClient.callReadFileSearch(path, pattern, 0, readToolsTimeoutMs).fold(
                err => s"Error: $err",
                matches => {
                  val shown = matches.take(max)
                  if (shown.isEmpty) s"No matches for '$pattern' in current buffer."
                  else shown.map(m => s"${m.lineNumber}: ${firstHighlightedOrFirstLine(m.context)}").mkString("\n")
                }
              )
            }
          )
        case "all" =>
          val argsForAll = Map("pattern" -> ResponseParser.StringValue(pattern), "max_results" -> ResponseParser.IntValue(intArg(args, "max_results", 20)))
          execSearchAllTheories(argsForAll, view)
        case _ =>
          val argsForSingle = Map("theory" -> ResponseParser.StringValue(scope), "pattern" -> ResponseParser.StringValue(pattern), "max_results" -> ResponseParser.IntValue(intArg(args, "max_results", 20)))
          execSearchInTheory(argsForSingle, view)
      }
    }
  }

  /** Get current proof goal state at cursor via I/Q MCP. Returns goal text or error. */
  private def execGetGoalState(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx =>
            if (ctx.goal.hasGoal && ctx.goal.goalText.trim.nonEmpty)
              ctx.goal.goalText.trim
            else "No goal at cursor position."
        )
  }

  /** Extract a single subgoal by index from proof state. Parses PIDE goal format. */
  private def execGetSubgoal(args: ResponseParser.ToolArgs, view: View): String = {
    val index = intArg(args, "index", -1)
    if (index <= 0) "Error: index must be a positive integer"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx => {
            if (!ctx.goal.hasGoal || ctx.goal.goalText.trim.isEmpty)
              "No goal at cursor position."
            else {
              // Parse PIDE goal format: "goal (N subgoals):\n 1. ...\n 2. ..."
              val goalText = ctx.goal.goalText
              val lines = goalText.linesIterator.toList
              
              // Find the header line
              val headerPattern = """^goal \((\d+) subgoals?\):$""".r
              val subgoalCount = lines.headOption.flatMap {
                case headerPattern(n) => scala.util.Try(n.toInt).toOption
                case _ => None
              }.getOrElse(ctx.goal.numSubgoals)
              
              if (subgoalCount == 0) {
                "No subgoals (proof complete)."
              } else if (index > subgoalCount) {
                s"Error: subgoal $index out of range (only $subgoalCount subgoal${if (subgoalCount == 1) "" else "s"})"
              } else {
                // Find subgoal N - they're numbered as " 1. ", " 2. ", etc
                val subgoalPattern = (s"""^\\s*$index\\.\\s+(.*)""").r
                val subgoalLines = scala.collection.mutable.ListBuffer[String]()
                var inTargetSubgoal = false
                var foundStart = false
                
                for (line <- lines.drop(1)) { // Skip header
                  line match {
                    case subgoalPattern(rest) =>
                      inTargetSubgoal = true
                      foundStart = true
                      subgoalLines += rest
                    case l if inTargetSubgoal && l.trim.nonEmpty && l.matches("""^\s*\d+\.\s+.*""") =>
                      // Hit next subgoal, stop
                      inTargetSubgoal = false
                    case l if inTargetSubgoal =>
                      subgoalLines += l
                    case _ => // skip
                  }
                }
                
                if (!foundStart) {
                  s"Error: could not find subgoal $index in goal state"
                } else if (subgoalLines.isEmpty) {
                  s"Subgoal $index (empty)"
                } else {
                  s"Subgoal $index of $subgoalCount:\n${subgoalLines.mkString("\n")}"
                }
              }
            }
          }
        )
    }
  }

  /** Get local facts and assumptions in scope at cursor. Returns context text or error. */
  private def execGetProofContext(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetProofContext(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx => {
            if (ctx.success && ctx.hasContext && ctx.context.trim.nonEmpty)
              ctx.context.trim
            else if (ctx.timedOut) "Proof context lookup timed out."
            else if (ctx.message.trim.nonEmpty) ctx.message.trim
            else "No local facts in scope."
          }
        )
  }

  /** Search for theorems via I/Q find_theorems. Returns matching theorems or error. */
  private def execFindTheorems(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val max = math.min(
        AssistantConstants.MAX_FIND_THEOREMS_RESULTS,
        math.max(1, intArg(args, "max_results", 20))
      )
      val timeout = AssistantOptions.getFindTheoremsTimeout
      val quoted =
        if (pattern.startsWith("\"")) pattern else s"\"$pattern\""

      execExplore(
        query = IQMcpClient.ExploreQueryType.FindTheorems,
        arguments = quoted,
        timeoutMs = timeout,
        toolLabel = "find_theorems",
        emptyMessage = s"No theorems found for: $pattern",
        extraParams = Map("max_results" -> max)
      )
    }
  }

  /** Verify a proof method via I/Q MCP. Returns [ok]/[FAIL] with timing or error. */
  private def execVerifyProof(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"[FAIL] I/Q MCP verification failed: $mcpErr",
          explore => {
            if (explore.success) "[ok] Proof verified"
            else if (explore.timedOut) "[FAIL] Timed out"
            else
              s"[FAIL] Failed: ${exploreFailureMessage(explore, "proof verification failed")}"
          }
        )
    }
  }

  /** Run sledgehammer via I/Q explore. Returns found proof methods or error. */
  private def execRunSledgehammer(@unused view: View): String =
    execExplore(
      query = IQMcpClient.ExploreQueryType.Sledgehammer,
      arguments = "",
      timeoutMs = AssistantOptions.getSledgehammerTimeout,
      toolLabel = "sledgehammer",
      emptyMessage = "No proofs found."
    )

  /** Run nitpick counterexample finder via I/Q explore. Returns counterexample or error. */
  private def execRunNitpick(@unused view: View): String =
    execExplore(
      query = IQMcpClient.ExploreQueryType.Proof,
      arguments = "nitpick",
      timeoutMs = AssistantOptions.getNitpickTimeout,
      toolLabel = "nitpick"
    )

  /** Run quickcheck random testing via I/Q explore. Returns counterexample or error. */
  private def execRunQuickcheck(@unused view: View): String =
    execExplore(
      query = IQMcpClient.ExploreQueryType.Proof,
      arguments = "quickcheck",
      timeoutMs = AssistantOptions.getQuickcheckTimeout,
      toolLabel = "quickcheck"
    )

  /** Unified counterexample finder supporting nitpick, quickcheck, or both. */
  private def execFindCounterexample(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val method = safeStringArg(args, "method", 50).toLowerCase
    val effectiveMethod = if (method.isEmpty || method == "quickcheck") "quickcheck" else method
    
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      effectiveMethod match {
        case "quickcheck" => execRunQuickcheck(view)
        case "nitpick" => execRunNitpick(view)
        case "both" =>
          // Try quickcheck first (fast), then nitpick if no counterexample
          val quickResult = execRunQuickcheck(view)
          if (quickResult.contains("Counterexample") || quickResult.contains("counterexample")) {
            s"[quickcheck]\n$quickResult"
          } else {
            val nitResult = execRunNitpick(view)
            if (nitResult.contains("Counterexample") || nitResult.contains("counterexample")) {
              s"[nitpick]\n$nitResult"
            } else {
              s"[quickcheck] $quickResult\n[nitpick] $nitResult"
            }
          }
        case _ => s"Error: method must be 'nitpick', 'quickcheck', or 'both', got '$method'"
      }
    }
  }

  /** Get type information for term at cursor via I/Q MCP. Returns type text or error. */
  private def execGetType(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetTypeAtSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          t =>
            if (t.hasType && t.typeText.trim.nonEmpty) t.typeText.trim
            else t.message.filter(_.trim.nonEmpty).getOrElse(
              "No type information at cursor position."
            )
        )
  }

  /** Get source text of Isabelle command at cursor via I/Q MCP. Returns command text or error. */
  private def execGetCommandText(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callResolveCommandTarget(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          resolved =>
            Option(resolved.command.source)
              .map(_.trim)
              .filter(_.nonEmpty)
              .getOrElse("No command at cursor position.")
        )
  }

  /** Get error or warning diagnostics from PIDE. Handles 'cursor', 'all', or specific theory scope. */
  private def execGetDiagnostics(
      args: ResponseParser.ToolArgs,
      view: View,
      severity: IQMcpClient.DiagnosticSeverity,
      emptyMsgPrefix: String
  ): String = {
    val timeoutMs = readToolsTimeoutMs
    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        IQMcpClient
          .callGetDiagnostics(
            severity = severity,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgsForCurrentView(view)
          )
          .fold(
            err => s"Error: $err",
            diagnostics =>
              formatDiagnosticsMessages(diagnostics, s"$emptyMsgPrefix at cursor position.")
          )

      case "all" =>
        currentBufferPath(view).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = severity,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    s"$emptyMsgPrefix in current buffer."
                  )
              )
        )

      case _ =>
        resolveTheoryPath(effectiveScope).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = severity,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics =>
                  formatDiagnosticsMessages(
                    diagnostics,
                    s"$emptyMsgPrefix in theory '$effectiveScope'."
                  )
              )
        )
    }
  }

  private def execGetErrors(
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    execGetDiagnostics(args, view, IQMcpClient.DiagnosticSeverity.Error, "No errors")

  /** Look up definitions for constants/types via I/Q MCP. Returns definitions or error. */
  private def execGetDefinitions(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val names = safeStringArg(args, "names", MAX_STRING_ARG_LENGTH)
    if (names.isEmpty) "Error: names required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val nameList = names.split("\\s+").toList.filter(_.nonEmpty)
      if (nameList.isEmpty) "Error: no valid names provided"
      else {
        IQMcpClient
          .callGetDefinitions(
            names = nameList,
            selectionArgs = selectionArgsForCurrentView(view),
            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
          )
          .fold(
            mcpErr => s"Error: $mcpErr",
            defs => {
              if (defs.success && defs.hasDefinitions && defs.definitions.trim.nonEmpty)
                defs.definitions.trim
              else if (defs.timedOut)
                "Definition lookup timed out."
              else {
                val msg = defs.error.getOrElse(defs.message).trim
                if (msg.nonEmpty) s"Error: $msg"
                else s"No definitions found for: ${nameList.mkString(", ")}"
              }
            }
          )
      }
    }
  }

  /** Get file statistics (line count, entity count, processing status) without reading full content. */
  private def execGetFileStats(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) "I/Q plugin not available."
        else {
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callGetFileStats(path, readToolsTimeoutMs)
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  stats => {
                    val processedStatus = if (stats.fullyProcessed) "fully processed" else "processing"
                    val errorStatus = if (stats.hasErrors) s", ${stats.errorCount} errors" else ", no errors"
                    val warningStatus = if (stats.warningCount > 0) s", ${stats.warningCount} warnings" else ""
                    s"$theory: ${stats.lineCount} lines, ${stats.entityCount} entities, $processedStatus$errorStatus$warningStatus"
                  }
                )
          )
        }
    }
  }

  /** Get PIDE processing status (unprocessed/running/finished/failed command counts). */
  private def execGetProcessingStatus(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) "I/Q plugin not available."
        else {
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callGetProcessingStatus(path, readToolsTimeoutMs)
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  status => {
                    val processedLabel = if (status.fullyProcessed) "Fully processed" else "Processing"
                    val parts = List(
                      s"$processedLabel",
                      s"unprocessed: ${status.unprocessed}",
                      s"running: ${status.running}",
                      s"finished: ${status.finished}",
                      s"failed: ${status.failed}",
                      s"consolidated: ${status.consolidated}"
                    )
                    parts.mkString("\n")
                  }
                )
          )
        }
    }
  }

  /** Find all sorry/oops commands in a theory file with line numbers and enclosing proof names. */
  private def execGetSorryPositions(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err) => err
      case Right(theory) =>
        if (!IQAvailable.isAvailable) "I/Q plugin not available."
        else {
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callGetSorryPositions(path, readToolsTimeoutMs)
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  result => {
                    if (result.count == 0) s"No sorry/oops commands in $theory."
                    else {
                      val lines = result.positions.map { pos =>
                        s"Line ${pos.line}: ${pos.keyword} in ${pos.inProof}"
                      }
                      s"Found ${result.count} sorry/oops command${if (result.count == 1) "" else "s"} in $theory:\n${lines.mkString("\n")}"
                    }
                  }
                )
          )
        }
    }
  }

  /** Execute a proof step and return resulting state via I/Q MCP. Returns [COMPLETE] or subgoal count + state. */
  private def execExecuteStep(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val proof = safeStringArg(args, "proof", MAX_PROOF_ARG_LENGTH)
    if (proof.isEmpty) "Error: proof required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getVerificationTimeout
      val mcpStart = System.currentTimeMillis()
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = proof,
          timeoutMs = timeout
        )
        .fold(
          mcpErr => s"[FAIL] step execution failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.isEmpty) "Error: step execution completed without a result."
              else {
                val stepResult = IQIntegration.parseStepResult(
                  text,
                  System.currentTimeMillis() - mcpStart
                )
                val status =
                  if (stepResult.complete) "[COMPLETE]"
                  else
                    stepResult.numSubgoals match {
                      case Some(n) => s"[$n subgoals]"
                      case None    => "[subgoal count unknown]"
                    }
                s"$status\n${stepResult.stateText}"
              }
            } else if (explore.timedOut) "Step execution timed out."
            else s"[FAIL] ${exploreFailureMessage(explore, "step execution failed")}"
          }
        )
    }
  }

  /** Trace simplifier rewriting via I/Q MCP. Returns detailed trace output or error. */
  private def execTraceSimplifier(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val method = safeStringArg(args, "method", 50)
    val effectiveMethod =
      if (method.isEmpty || method == "simp") "simp" else method
    val maxLines = optionalIntArg(args, "max_lines")
      .map(n => math.max(1, math.min(n, 1000)))
      .getOrElse(AssistantConstants.DEFAULT_TRACE_MAX_LINES)
    
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val timeout = AssistantOptions.getTraceTimeout
      val depth = AssistantOptions.getTraceDepth
      val queryTimeoutMs =
        timeout * 1000L + AssistantConstants.TIMEOUT_BUFFER_MS
      val queryArg = s"simp_trace $effectiveMethod $timeout $depth"
      IQMcpClient
        .callExplore(
          query = IQMcpClient.ExploreQueryType.Proof,
          arguments = queryArg,
          timeoutMs = queryTimeoutMs
        )
        .fold(
          mcpErr => s"Error: simplifier trace failed via I/Q MCP: $mcpErr",
          explore => {
            if (explore.success) {
              val text = explore.results.trim
              if (text.isEmpty) "Error: simplifier trace completed without a result."
              else {
                val lines = text.linesIterator.toList
                if (lines.length > maxLines) {
                  val truncated = lines.take(maxLines).mkString("\n")
                  val remaining = lines.length - maxLines
                  s"$truncated\n\n... [trace truncated at $maxLines lines; $remaining more lines omitted. Increase max_lines for full trace]"
                } else {
                  text
                }
              }
            } else if (explore.timedOut) "Simplifier trace timed out."
            else
              s"Error: ${exploreFailureMessage(explore, "simplifier trace failed")}"
          }
        )
    }
  }

  /** Get full proof block (lemma...qed) at cursor via I/Q MCP. Returns proof text or error. */
  private def execGetProofBlock(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetProofBlocksForSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          blocks =>
            blocks.proofBlocks.headOption
              .map(_.proofText.trim)
              .filter(_.nonEmpty)
              .getOrElse(
                blocks.message.getOrElse("No proof block at cursor position.")
              )
        )
  }

  /** Get proof outline (skeleton of structural keywords only). Filters proof block to show structure. */
  private def execGetProofOutline(view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else
      IQMcpClient
        .callGetProofBlocksForSelection(
          selectionArgs = selectionArgsForCurrentView(view),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          blocks =>
            blocks.proofBlocks.headOption match {
              case Some(block) =>
                val startLine = block.startLine
                val proofText = block.proofText
                // Keywords that define proof structure (not proof content)
                val structuralKeywords = Set(
                  "lemma", "theorem", "corollary", "proposition",
                  "proof", "qed", "done",
                  "case", "next",
                  "show", "have", "obtain",
                  "apply", "by", "using", "unfolding"
                )
                
                val outline = proofText.linesIterator.zipWithIndex.flatMap { case (line, idx) =>
                  val trimmed = line.trim
                  val actualLine = startLine + idx
                  // Extract first word (keyword)
                  val firstWord = trimmed.takeWhile(c => c.isLetter || c == '_')
                  if (structuralKeywords.contains(firstWord)) {
                    // Include the line with its line number
                    Some(s"L$actualLine: ${trimmed.take(80)}")
                  } else {
                    None
                  }
                }.mkString("\n")
                
                if (outline.trim.isEmpty) "Proof block has no structural keywords."
                else s"Proof outline:\n$outline"
              case None =>
                blocks.message.getOrElse("No proof block at cursor position.")
            }
        )
  }

  /** Get structured context info (in_proof, has_goal, on_error, etc.) via I/Q MCP. Returns key-value summary. */
  private def execGetContextInfo(args: ResponseParser.ToolArgs, view: View): String = {
    if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val quickMode = boolArg(args, "quick", default = false)
      val selectionArgs = selectionArgsForCurrentView(view)
      IQMcpClient
        .callGetContextInfo(
          selectionArgs = selectionArgs,
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          ctx => {
            val commandKeyword = Option(ctx.command.keyword).getOrElse("").trim
            val definitionKeywords = Set(
              "definition",
              "abbreviation",
              "fun",
              "function",
              "primrec",
              "datatype",
              "codatatype",
              "type_synonym",
              "record",
              "typedef"
            )
            val hasSelection =
              Option(view)
                .flatMap(v => Option(v.getTextArea))
                .flatMap(ta => Option(ta.getSelectedText))
                .exists(_.trim.nonEmpty)
            
            // Check if command is an apply-style proof
            val hasApplyProof = commandKeyword.startsWith("apply") || commandKeyword == "by"
            
            // In quick mode, skip the 3 additional parallel checks
            val (onError, onWarning, hasTypeInfo) = if (quickMode) {
              (false, false, false)
            } else {
              // Run the 3 additional context checks in parallel for 3x speedup
              val latch = new CountDownLatch(3)
              @volatile var errorCheck = false
              @volatile var warningCheck = false
              @volatile var typeCheck = false
              
              // Fork error diagnostics check
              val _ = Isabelle_Thread.fork(name = "context-info-errors") {
                errorCheck = IQMcpClient
                  .callGetDiagnostics(
                    severity = IQMcpClient.DiagnosticSeverity.Error,
                    scope = IQMcpClient.DiagnosticScope.Selection,
                    timeoutMs = readToolsTimeoutMs,
                    selectionArgs = selectionArgs
                  )
                  .toOption
                  .exists(_.diagnostics.nonEmpty)
                latch.countDown()
              }
              
              // Fork warning diagnostics check
              val _ = Isabelle_Thread.fork(name = "context-info-warnings") {
                warningCheck = IQMcpClient
                  .callGetDiagnostics(
                    severity = IQMcpClient.DiagnosticSeverity.Warning,
                    scope = IQMcpClient.DiagnosticScope.Selection,
                    timeoutMs = readToolsTimeoutMs,
                    selectionArgs = selectionArgs
                  )
                  .toOption
                  .exists(_.diagnostics.nonEmpty)
                latch.countDown()
              }
              
              // Fork type info check
              val _ = Isabelle_Thread.fork(name = "context-info-type") {
                typeCheck = IQMcpClient
                  .callGetTypeAtSelection(
                    selectionArgs = selectionArgs,
                    timeoutMs = readToolsTimeoutMs
                  )
                  .toOption
                  .exists(_.hasType)
                latch.countDown()
              }
              
              // Wait for all 3 checks to complete (with timeout buffer)
              val _ = latch.await(readToolsTimeoutMs * 3 + 1000, TimeUnit.MILLISECONDS)
              
              (errorCheck, warningCheck, typeCheck)
            }
            
            val parts = List(
              s"in_proof: ${ctx.inProofContext}",
              s"has_goal: ${ctx.hasGoal || ctx.goal.hasGoal}",
              s"on_error: $onError",
              s"on_warning: $onWarning",
              s"has_selection: $hasSelection",
              s"has_command: ${ctx.command.source.trim.nonEmpty}",
              s"has_type_info: $hasTypeInfo",
              s"has_apply_proof: $hasApplyProof",
              s"on_definition: ${definitionKeywords.contains(commandKeyword)}",
              "iq_available: true"
            )
            parts.mkString("\n")
          }
        )
    }
  }

  /** Search for text pattern across all open theories. Returns matches with theory:line prefixes. */
  private def execSearchAllTheories(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val pattern = safeStringArg(args, "pattern", MAX_PATTERN_ARG_LENGTH)
    if (pattern.isEmpty) "Error: pattern required"
    else {
      val maxTotal = math.min(200, math.max(1, intArg(args, "max_results", AssistantConstants.DEFAULT_SEARCH_ALL_THEORIES_MAX_RESULTS)))
      IQMcpClient
        .callListFiles(
          filterOpen = Some(true),
          filterTheory = Some(true),
          sortBy = Some("path"),
          timeoutMs = readToolsTimeoutMs
        )
        .fold(
          err => s"Error: $err",
          listed => {
            // Search theories in parallel (up to 8 concurrent threads)
            val allMatches = new java.util.concurrent.ConcurrentLinkedQueue[String]()
            val maxConcurrent = 8
            val theories = listed.files.toList
            val chunks = theories.grouped(math.max(1, theories.length / maxConcurrent + 1)).toList
            val latch = new CountDownLatch(chunks.length)
            
            for (chunk <- chunks) {
              val _ = Isabelle_Thread.fork(name = "search-theories-parallel") {
                try {
                  for (file <- chunk if allMatches.size < maxTotal && !AssistantDockable.isCancelled) {
                    val remaining = maxTotal - allMatches.size
                    if (remaining > 0) {
                      val matches = IQMcpClient
                        .callReadFileSearch(
                          path = file.path,
                          pattern = pattern,
                          contextLines = 0,
                          timeoutMs = readToolsTimeoutMs
                        )
                        .getOrElse(Nil)
                        .take(remaining)
                      matches.foreach { m =>
                        if (allMatches.size < maxTotal) {
                          val matchText = firstHighlightedOrFirstLine(m.context)
                          val truncatedText = if (matchText.length > 80) matchText.take(77) + "..." else matchText
                          val _ = allMatches.add(s"${baseName(file.path)}:${m.lineNumber}: $truncatedText")
                        }
                      }
                    }
                  }
                } finally {
                  latch.countDown()
                }
              }
            }
            
            // Wait for all search threads to complete
            val _ = latch.await(readToolsTimeoutMs * chunks.length + 2000, TimeUnit.MILLISECONDS)
            
            val matchList = allMatches.asScala.toList.take(maxTotal)
            if (matchList.nonEmpty) {
              val truncated =
                if (matchList.length >= maxTotal) s" (showing first $maxTotal)"
                else ""
              s"Found ${matchList.length} matches$truncated:\n${matchList.mkString("\n")}"
            } else s"No matches for '$pattern' in any open theory."
          }
        )
    }
  }

  /** Parse theory imports from file content. Returns dependency list or error. */
  private def execGetDependencies(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callReadFileLine(
                path = path,
                startLine = Some(1),
                endLine = Some(-1),
                timeoutMs = readToolsTimeoutMs
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                numberedContent => {
                  val content = stripNumberPrefixes(numberedContent)
                  val importPattern = """(?s)imports\s+(.*?)(?:\bbegin\b|\z)""".r
                  importPattern.findFirstMatchIn(content) match {
                    case Some(m) =>
                      val tokenPattern = """"[^"]+"|[^\s"]+""".r
                      val imports =
                        tokenPattern.findAllIn(m.group(1)).toList.filter(_.nonEmpty)
                      if (imports.nonEmpty)
                        s"Dependencies of $theory:\n${imports.mkString("\n")}"
                      else s"Theory '$theory' has no explicit imports."
                    case None => s"No imports found in theory '$theory'."
                  }
                }
              )
        )
    }
  }

  /** Get warning messages from PIDE. Delegates to execGetDiagnostics with Warning severity. */
  private def execGetWarnings(
      args: ResponseParser.ToolArgs,
      view: View
  ): String =
    execGetDiagnostics(args, view, IQMcpClient.DiagnosticSeverity.Warning, "No warnings")

  /** Unified diagnostics tool supporting errors, warnings, or all diagnostics with optional count-only mode. */
  private def execGetDiagnosticsUnified(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val severityStr = safeStringArg(args, "severity", 50).toLowerCase
    val countOnly = boolArg(args, "count_only", default = false)
    
    val severity = severityStr match {
      case "warning" => IQMcpClient.DiagnosticSeverity.Warning
      case "error" => IQMcpClient.DiagnosticSeverity.Error
      case "all" => 
        // For "all", we need to query both and combine
        return execGetDiagnosticsAll(args, view, countOnly)
      case _ => 
        return s"Error: severity must be 'error', 'warning', or 'all', got '$severityStr'"
    }
    
    if (countOnly) {
      execGetDiagnosticsCount(args, view, severity)
    } else {
      val emptyMsg = if (severity == IQMcpClient.DiagnosticSeverity.Error) "No errors" else "No warnings"
      execGetDiagnostics(args, view, severity, emptyMsg)
    }
  }

  /** Get diagnostics count only (for count_only mode). */
  private def execGetDiagnosticsCount(
      args: ResponseParser.ToolArgs,
      view: View,
      severity: IQMcpClient.DiagnosticSeverity
  ): String = {
    val timeoutMs = readToolsTimeoutMs
    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope
    val severityLabel = if (severity == IQMcpClient.DiagnosticSeverity.Error) "errors" else "warnings"

    effectiveScope.toLowerCase match {
      case "cursor" =>
        IQMcpClient
          .callGetDiagnostics(
            severity = severity,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgsForCurrentView(view)
          )
          .fold(
            err => s"Error: $err",
            diagnostics => s"${diagnostics.count} $severityLabel at cursor"
          )

      case "all" =>
        currentBufferPath(view).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = severity,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics => s"${diagnostics.count} $severityLabel in current buffer"
              )
        )

      case _ =>
        resolveTheoryPath(effectiveScope).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetDiagnostics(
                severity = severity,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                diagnostics => s"${diagnostics.count} $severityLabel in theory '$effectiveScope'"
              )
        )
    }
  }

  /** Get all diagnostics (both errors and warnings) for "all" severity mode. */
  private def execGetDiagnosticsAll(
      args: ResponseParser.ToolArgs,
      view: View,
      countOnly: Boolean
  ): String = {
    val timeoutMs = readToolsTimeoutMs
    val rawScope = safeStringArg(args, "scope", 200)
    val effectiveScope = if (rawScope.isEmpty) "all" else rawScope

    effectiveScope.toLowerCase match {
      case "cursor" =>
        val latch = new CountDownLatch(2)
        @volatile var errorResult: Option[IQMcpClient.DiagnosticsResult] = None
        @volatile var warningResult: Option[IQMcpClient.DiagnosticsResult] = None
        val selectionArgs = selectionArgsForCurrentView(view)
        
        val _ = Isabelle_Thread.fork(name = "get-errors") {
          errorResult = IQMcpClient.callGetDiagnostics(
            severity = IQMcpClient.DiagnosticSeverity.Error,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgs
          ).toOption
          latch.countDown()
        }
        
        val _ = Isabelle_Thread.fork(name = "get-warnings") {
          warningResult = IQMcpClient.callGetDiagnostics(
            severity = IQMcpClient.DiagnosticSeverity.Warning,
            scope = IQMcpClient.DiagnosticScope.Selection,
            timeoutMs = timeoutMs,
            selectionArgs = selectionArgs
          ).toOption
          latch.countDown()
        }
        
        val _ = latch.await(timeoutMs * 2 + 1000, TimeUnit.MILLISECONDS)
        
        val errorCount = errorResult.map(_.count).getOrElse(0)
        val warningCount = warningResult.map(_.count).getOrElse(0)
        
        if (countOnly) {
          s"$errorCount errors, $warningCount warnings at cursor"
        } else {
          val errors = errorResult.toList.flatMap(_.diagnostics)
          val warnings = warningResult.toList.flatMap(_.diagnostics)
          val combined = (errors ++ warnings).sortBy(_.line)
          if (combined.isEmpty) "No errors or warnings at cursor position."
          else combined.map(d => s"Line ${d.line}: ${d.message}").mkString("\n")
        }

      case "all" =>
        currentBufferPath(view).fold(
          err => err,
          path => {
            val latch = new CountDownLatch(2)
            @volatile var errorResult: Option[IQMcpClient.DiagnosticsResult] = None
            @volatile var warningResult: Option[IQMcpClient.DiagnosticsResult] = None
            
            val _ = Isabelle_Thread.fork(name = "get-errors") {
              errorResult = IQMcpClient.callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Error,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              ).toOption
              latch.countDown()
            }
            
            val _ = Isabelle_Thread.fork(name = "get-warnings") {
              warningResult = IQMcpClient.callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Warning,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              ).toOption
              latch.countDown()
            }
            
            val _ = latch.await(timeoutMs * 2 + 1000, TimeUnit.MILLISECONDS)
            
            val errorCount = errorResult.map(_.count).getOrElse(0)
            val warningCount = warningResult.map(_.count).getOrElse(0)
            
            if (countOnly) {
              s"$errorCount errors, $warningCount warnings in current buffer"
            } else {
              val errors = errorResult.toList.flatMap(_.diagnostics)
              val warnings = warningResult.toList.flatMap(_.diagnostics)
              val combined = (errors ++ warnings).sortBy(_.line)
              if (combined.isEmpty) "No errors or warnings in current buffer."
              else combined.map(d => s"Line ${d.line}: ${d.message}").mkString("\n")
            }
          }
        )

      case _ =>
        resolveTheoryPath(effectiveScope).fold(
          err => err,
          path => {
            val latch = new CountDownLatch(2)
            @volatile var errorResult: Option[IQMcpClient.DiagnosticsResult] = None
            @volatile var warningResult: Option[IQMcpClient.DiagnosticsResult] = None
            
            val _ = Isabelle_Thread.fork(name = "get-errors") {
              errorResult = IQMcpClient.callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Error,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              ).toOption
              latch.countDown()
            }
            
            val _ = Isabelle_Thread.fork(name = "get-warnings") {
              warningResult = IQMcpClient.callGetDiagnostics(
                severity = IQMcpClient.DiagnosticSeverity.Warning,
                scope = IQMcpClient.DiagnosticScope.File,
                timeoutMs = timeoutMs,
                path = Some(path)
              ).toOption
              latch.countDown()
            }
            
            val _ = latch.await(timeoutMs * 2 + 1000, TimeUnit.MILLISECONDS)
            
            val errorCount = errorResult.map(_.count).getOrElse(0)
            val warningCount = warningResult.map(_.count).getOrElse(0)
            
            if (countOnly) {
              s"$errorCount errors, $warningCount warnings in theory '$effectiveScope'"
            } else {
              val errors = errorResult.toList.flatMap(_.diagnostics)
              val warnings = warningResult.toList.flatMap(_.diagnostics)
              val combined = (errors ++ warnings).sortBy(_.line)
              if (combined.isEmpty) s"No errors or warnings in theory '$effectiveScope'."
              else combined.map(d => s"Line ${d.line}: ${d.message}").mkString("\n")
            }
          }
        )
    }
  }

  /** Move cursor to specified line in current theory via GUI thread. Returns confirmation or error. */
  private def execSetCursorPosition(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val line = intArg(args, "line", -1)
    if (line <= 0) "Error: line must be a positive integer"
    else {
      val latch = new CountDownLatch(1)
      @volatile var result = ""
      GUI_Thread.later {
        try {
          val buffer = view.getBuffer
          val lineCount = buffer.getLineCount
          if (line > lineCount) {
            result =
              s"Error: line $line out of range (theory has $lineCount lines)"
          } else {
            val offset = buffer.getLineStartOffset(line - 1)
            view.getTextArea.setCaretPosition(offset)
            result = s"Cursor moved to line $line"
          }
        } catch { 
          case ex: Exception => result = s"Error: ${ex.getMessage}" 
        } finally {
          latch.countDown()
        }
      }
      if (!latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)) {
        "Error: Operation timed out (GUI thread busy)"
      } else if (result.isEmpty) {
        "Error: Operation completed but returned no result"
      } else {
        result
      }
    }
  }

  /** Edit theory file via I/Q MCP write_file (insert/replace/delete operations). Returns context or error. */
  private def execEditTheory(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val operation = safeStringArg(args, "operation", 50).toLowerCase
    val text =
      safeStringArg(args, "text", MAX_STRING_ARG_LENGTH, trim = false).replace(
        "\\n",
        "\n"
      )
    val startLine = intArg(args, "start_line", -1)
    val endLine = intArg(args, "end_line", startLine)

    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        if (startLine <= 0) "Error: start_line must be a positive integer"
        else if (operation == "replace" && endLine < startLine)
          s"Error: end_line ($endLine) must be >= start_line ($startLine)"
        else if (operation == "delete" && endLine < startLine)
          s"Error: end_line ($endLine) must be >= start_line ($startLine)"
        else if (!Set("insert", "replace", "delete").contains(operation))
          s"Error: operation must be 'insert', 'replace', or 'delete', got '$operation'"
        else if (
          (operation == "insert" || operation == "replace") && text.isEmpty
        )
          s"Error: text required for $operation operation"
        else {
          resolveTheoryPath(theory).fold(
            err => err,
            path =>
              IQMcpClient
                .callReadFileLine(
                  path = path,
                  startLine = Some(1),
                  endLine = Some(-1),
                  timeoutMs = readToolsTimeoutMs
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  numberedContent => {
                    val lineCount = lineCountFromNumberedContent(numberedContent)
                    val canAppendAtEnd = operation == "insert" && startLine == lineCount + 1
                    if (startLine > lineCount && !canAppendAtEnd)
                      s"Error: start_line $startLine out of range (theory has $lineCount lines)"
                    else if (
                      (operation == "replace" || operation == "delete") && endLine > lineCount
                    )
                      s"Error: end_line $endLine out of range (theory has $lineCount lines)"
                    else {
                      val writeResult = operation match {
                        case "insert" =>
                          val normalizedText =
                            if (text.endsWith("\n")) text else text + "\n"
                          IQMcpClient.callWriteFileInsert(
                            path = path,
                            insertAfterLine = math.max(0, startLine - 1),
                            newText = normalizedText,
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                        case "replace" =>
                          IQMcpClient.callWriteFileLine(
                            path = path,
                            startLine = startLine,
                            endLine = endLine,
                            newText = text,
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                        case "delete" =>
                          IQMcpClient.callWriteFileLine(
                            path = path,
                            startLine = startLine,
                            endLine = endLine,
                            newText = "",
                            timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
                          )
                      }

                      writeResult.fold(
                        err => s"Error: $err",
                        result => {
                          // Get line count from write_file response summary (Phase 3.5 enhancement)
                          val newLineCount = result.summary
                            .get("new_line_count")
                            .flatMap {
                              case i: Int => Some(i)
                              case l: Long if l.isValidInt => Some(l.toInt)
                              case d: Double if d.isWhole && d.isValidInt => Some(d.toInt)
                              case _ => None
                            }
                            .getOrElse(-1)
                          
                          val action = operation match {
                            case "insert"  => 
                              val linesInserted = text.linesIterator.size
                              s"Inserted $linesInserted line${if (linesInserted == 1) "" else "s"} before line $startLine"
                            case "replace" => 
                              s"Replaced lines $startLine-$endLine"
                            case "delete"  => 
                              s"Deleted lines $startLine-$endLine"
                          }
                          
                          if (newLineCount > 0) s"$action. Theory now has $newLineCount lines."
                          else action
                        }
                      )
                    }
                  }
                )
          )
        }
    }
  }

  /** Try multiple proof methods in parallel via I/Q verification. Returns [ok]/[FAIL] for each method. */
  private def execTryMethods(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val methodsStr = safeStringArg(args, "methods", MAX_STRING_ARG_LENGTH)
    if (methodsStr.isEmpty) "Error: methods required"
    else if (!IQAvailable.isAvailable) "I/Q plugin not available."
    else {
      val methods = methodsStr.split(",").map(_.trim).filter(_.nonEmpty).toList
      if (methods.isEmpty) "Error: no valid methods provided"
      else {
        val timeout = AssistantOptions.getVerificationTimeout
        val latch = new CountDownLatch(methods.length)
        val results = new java.util.concurrent.ConcurrentHashMap[String, String]()

        // Launch all verification tasks in parallel
        for (method <- methods) {
          GUI_Thread.later {
            if (AssistantDockable.isCancelled) {
              results.put(method, s"[CANCELLED] $method")
              latch.countDown()
            } else {
              IQIntegration.verifyProofAsync(
                view,
                method,
                timeout,
                {
                  case IQIntegration.ProofSuccess(ms, _) =>
                    results.put(method, s"[ok] $method (${ms}ms)")
                    latch.countDown()
                  case IQIntegration.ProofFailure(err) =>
                    results.put(method, s"[FAIL] $method: ${err.take(50)}")
                    latch.countDown()
                  case IQIntegration.ProofTimeout =>
                    results.put(method, s"[TIMEOUT] $method")
                    latch.countDown()
                  case _ =>
                    results.put(method, s"[UNAVAILABLE] $method")
                    latch.countDown()
                }
              )
            }
          }
        }

        // Wait for all methods to complete (or timeout)
        // Methods run in parallel, so timeout is bounded by the slowest single verification
        val totalTimeout = timeout + 5000L
        if (!latch.await(totalTimeout, TimeUnit.MILLISECONDS)) {
          // Some methods didn't complete — mark them as timeout
          methods.foreach { method =>
            results.putIfAbsent(method, s"[TIMEOUT] $method")
          }
        }

        // Return results in the original order
        val orderedResults = methods.map(m =>
          results.getOrDefault(m, s"[ERROR] $m returned no result")
        )
        s"Tried ${methods.length} methods:\n${orderedResults.mkString("\n")}"
      }
    }
  }

  /** List named entities (lemmas, definitions) in theory via I/Q MCP. Returns line:keyword name list. */
  private def execGetEntities(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    safeTheoryArg(args) match {
      case Left(err)     => err
      case Right(theory) =>
        val maxResultsRaw = intArg(args, "max_results", AssistantConstants.DEFAULT_GET_ENTITIES_MAX_RESULTS)
        val maxResults = math.max(1, math.min(1000, maxResultsRaw))
        resolveTheoryPath(theory).fold(
          err => err,
          path =>
            IQMcpClient
              .callGetEntities(
                path = path,
                maxResults = Some(maxResults),
                timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
              )
              .fold(
                mcpErr => s"Error: $mcpErr",
                entitiesResult => {
                  if (entitiesResult.entities.isEmpty)
                    "No entities found in theory."
                  else {
                    val lines = entitiesResult.entities.map { entity =>
                      s"Line ${entity.line}: ${entity.keyword} ${entity.name}"
                    }
                    val suffix =
                      if (entitiesResult.truncated)
                        s"\n\nResults truncated to ${entitiesResult.returnedEntities} of ${entitiesResult.totalEntities} entities."
                      else ""
                    lines.mkString("\n") + suffix
                  }
                }
              )
        )
    }
  }

  /** Create new theory file in current directory via I/Q MCP open_file. Returns confirmation or error. */
  private def execCreateTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val name = safeStringArg(args, "name", 200)
    val imports = safeStringArg(args, "imports", 500)
    val content =
      safeStringArg(args, "content", MAX_STRING_ARG_LENGTH, trim = false)
        .replace("\\n", "\n")

    if (name.isEmpty) "Error: name required"
    else if (!isValidCreateTheoryName(name))
      s"Error: invalid theory name '$name'"
    else {
      currentBufferPath(view).fold(
        err => err,
        currentPath => {
          val currentDir = java.nio.file.Paths.get(currentPath).getParent
          if (currentDir == null) "Error: could not determine current theory directory"
          else {
            val normalizedDir = currentDir.toAbsolutePath.normalize()
            val targetPath = normalizedDir.resolve(s"$name.thy").normalize()

            val effectiveImports = if (imports.isEmpty) "Main" else imports
            val theoryContent =
              s"theory $name\n  imports $effectiveImports\nbegin\n\n${
                  if (content.nonEmpty) content + "\n\n" else ""
                }end\n"

            if (targetPath.getParent != normalizedDir)
              s"Error: invalid theory name '$name'"
            else
              IQMcpClient
                .callOpenFile(
                  path = targetPath.toString,
                  createIfMissing = true,
                  inView = true,
                  content = Some(theoryContent),
                  overwriteIfExists = false,
                  timeoutMs = AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC * 1000L
                )
                .fold(
                  mcpErr => s"Error: $mcpErr",
                  _ => s"Created and opened $name.thy"
                )
          }
        }
      )
    }
  }

  /** Open existing theory file via I/Q MCP. Resolves relative paths from current buffer. Returns confirmation or error. */
  private def execOpenTheory(
      args: ResponseParser.ToolArgs,
      view: View
  ): String = {
    val path = safeStringArg(args, "path", 1000)
    if (path.isEmpty) "Error: path required"
    else {
      if (!path.endsWith(".thy")) {
        s"Error: not a theory file (must end with .thy): $path"
      } else {
        val resolvedPath = {
          val file = java.io.File(path)
          if (file.isAbsolute) file.getPath
          else
            currentBufferPath(view).fold(_ => path, current =>
              java.nio.file.Paths
                .get(current)
                .getParent
                .resolve(path)
                .normalize()
                .toString
            )
        }
        IQMcpClient
          .callOpenFile(
            path = resolvedPath,
            createIfMissing = false,
            inView = true,
            timeoutMs = AssistantConstants.BUFFER_OPERATION_TIMEOUT_SEC * 1000L
          )
          .fold(
            err => s"Error: $err",
            opened => s"Opened ${baseName(opened.path)}"
          )
      }
    }
  }

  /**
   * Shared method to prompt the user with multiple choice options.
   * Returns Some(selectedOption) or None if cancelled/timeout.
   * Used by both execAskUser and ToolPermissions.promptUser.
   */
  private[assistant] def promptUserWithChoices(
    question: String, options: List[String], context: String, view: View
  ): Option[String] = {
    if (options.length < 2) return None
    
    val latch = new CountDownLatch(1)
    @volatile var selectedOption = ""
    @volatile var widgetShown = false
    
    GUI_Thread.later {
      try {
        val html = buildAskUserHtml(question, context, options, { choice =>
          selectedOption = choice
          latch.countDown()
        })
        ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html, 
          java.time.LocalDateTime.now(), rawHtml = true, transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
        widgetShown = true
      } catch {
        case ex: Exception =>
          ErrorHandler.logSilentError("promptUserWithChoices", ex)
          latch.countDown()
      }
    }
    
    AssistantDockable.setStatus("Waiting for your input...")
    
    val timeout = AssistantConstants.ASK_USER_TIMEOUT_SEC
    var responded = false
    val endTime = System.currentTimeMillis() + timeout * 1000
    while (!responded && !AssistantDockable.isCancelled && System.currentTimeMillis() < endTime) {
      responded = latch.await(500, TimeUnit.MILLISECONDS)
    }
    
    if (AssistantDockable.isCancelled || !responded) {
      None
    } else {
      AssistantDockable.setStatus("Processing your choice...")
      GUI_Thread.later {
        ChatAction.addMessage(ChatAction.Message(ChatAction.User, s"Selected: $selectedOption", 
          java.time.LocalDateTime.now(), transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
      Some(selectedOption)
    }
  }

  /** Present multiple-choice question to user via widget. Blocks until response or timeout. Returns selected option or error. */
  private def execAskUser(args: ResponseParser.ToolArgs, view: View): String = {
    val question = safeStringArg(args, "question", 500)
    val optionsStr = safeStringArg(args, "options", 1000)
    val context = safeStringArg(args, "context", 500)
    
    if (question.isEmpty) return "Error: question required"
    
    val options = optionsStr.split(",").map(_.trim).filter(_.nonEmpty).toList
    if (options.length < 2) return "Error: at least 2 options required"
    
    promptUserWithChoices(question, options, context, view) match {
      case Some(choice) => choice
      case None if AssistantDockable.isCancelled => "User cancelled the operation."
      case None => "User did not respond within the time limit."
    }
  }

  /** Add task to session task list and inject widget. Returns confirmation. */
  private def execTaskListAdd(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val title = safeStringArg(args, "title", 500)
    val description = safeStringArg(args, "description", 2000)
    val criteria = safeStringArg(args, "acceptance_criteria", 2000)
    
    val result = TaskList.addTask(title, description, criteria)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = WidgetRenderer.taskAdded(title, description, criteria)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  /** Mark task as completed and inject status widget. Returns confirmation or error. */
  private def execTaskListDone(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markDone(taskId)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = WidgetRenderer.taskStatus(taskId, "done", result)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  /** Mark task as irrelevant and inject status widget. Returns confirmation or error. */
  private def execTaskListIrrelevant(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.markIrrelevant(taskId)
    
    // Inject rich HTML widget
    GUI_Thread.later {
      val html = WidgetRenderer.taskStatus(taskId, "irrelevant", result)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  /** Get next pending task and inject full task list widget. Returns next task details or "no pending tasks". */
  private def execTaskListNext(@unused view: View): String = {
    val result = TaskList.getNextTask()
    
    // Inject rich HTML widget showing full checklist with next task highlighted
    GUI_Thread.later {
      val html = WidgetRenderer.taskList(highlightNext = true)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  /** Show all tasks with current statuses via widget injection. Returns summary text. */
  private def execTaskListShow(@unused view: View): String = {
    val result = TaskList.listTasks()
    
    // Inject rich HTML widget showing full checklist
    GUI_Thread.later {
      val html = WidgetRenderer.taskList(highlightNext = false)
      ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
        java.time.LocalDateTime.now(), rawHtml = true, transient = true))
      AssistantDockable.showConversation(ChatAction.getHistory)
    }
    
    result
  }

  /** Get detailed information for specific task and inject detail widget. Returns task info or error. */
  private def execTaskListGet(
      args: ResponseParser.ToolArgs,
      @unused view: View
  ): String = {
    val taskId = intArg(args, "task_id", -1)
    val result = TaskList.getTask(taskId)
    
    // Inject rich HTML widget showing detailed task card
    GUI_Thread.later {
      TaskList.getTasks.find(_.id == taskId).foreach { task =>
        val html = WidgetRenderer.taskDetail(task)
        ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, html,
          java.time.LocalDateTime.now(), rawHtml = true, transient = true))
        AssistantDockable.showConversation(ChatAction.getHistory)
      }
    }
    
    result
  }

  private def buildAskUserHtml(
      question: String,
      context: String,
      options: List[String],
      onChoice: String => Unit
  ): String = WidgetRenderer.askUser(question, context, options, onChoice)

  private def intArg(
      args: ResponseParser.ToolArgs,
      key: String,
      default: Int
  ): Int = optionalIntArg(args, key).getOrElse(default)
}
