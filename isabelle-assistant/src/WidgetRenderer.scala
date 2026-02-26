/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * Renders HTML widgets for interactive chat elements (task lists, user prompts, tool results).
 * Extracted from AssistantTools to separate rendering concerns from tool execution.
 */
object WidgetRenderer {

  /** Convert snake_case tool name to PascalCase for display.
    * Example: "read_theory" → "ReadTheory"
    */
  private def toolNameToDisplay(wireName: String): String =
    wireName.split("_").map(_.capitalize).mkString

  /** Render HTML widget for a tool result with smart truncation.
    * 
    * Creates a styled card showing the tool name and a summary of the result.
    * For short results (≤3 lines), displays inline. For longer results, shows
    * first 3 lines plus a "Show full output ▸" clickable action link.
    * 
    * @param toolName Tool's wire name (e.g., "read_theory")
    * @param result Tool execution result text
    * @param registerAction Function to register expand action and return its ID
    * @return HTML string for injection into chat
    */
  def toolResult(
      toolName: String,
      result: String,
      registerAction: (() => Unit) => String
  ): String = {
    val border = UIColors.ToolMessage.border
    val bg = "white"
    val headerText = UIColors.ToolMessage.timestamp
    val resultText = UIColors.TaskList.taskText
    val linkColor = UIColors.linkColor
    
    val displayName = toolNameToDisplay(toolName)
    val lines = result.linesIterator.toList
    val lineCount = lines.length
    
    // Smart truncation: show full if ≤3 lines, otherwise truncate with expand link
    val displayContent = if (lineCount <= 3) {
      HtmlUtil.escapeHtml(result)
    } else {
      val preview = lines.take(3).mkString("\n")
      val expandId = registerAction(() => {
        // When user clicks "Show full output", replace the widget with full content
        GUI_Thread.later {
          val fullHtml = toolResultFull(toolName, result)
          ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, fullHtml,
            java.time.LocalDateTime.now(), rawHtml = true, transient = true))
          AssistantDockable.showConversation(ChatAction.getHistory)
        }
      })
      val previewHtml = HtmlUtil.escapeHtml(preview)
      val expandLink = s"""<div style='margin-top:6px;font-size:10pt;'>
        |<a href='action:insert:$expandId' style='color:$linkColor;text-decoration:none;'>
        |▸ Show full output ($lineCount lines)</a></div>""".stripMargin
      previewHtml + expandLink
    }
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;'>
       |<b>→ Tool Result:</b> <span style='font-family:${MarkdownRenderer.codeFont};'>$displayName</span></div>
       |<div style='font-family:${MarkdownRenderer.codeFont};font-size:10pt;color:$resultText;white-space:pre-wrap;'>
       |$displayContent</div>
       |</div>""".stripMargin
  }

  /** Render full (non-truncated) tool result widget.
    * Used when user clicks "Show full output" on a truncated result.
    */
  private def toolResultFull(toolName: String, result: String): String = {
    val border = UIColors.ToolMessage.border
    val bg = "white"
    val headerText = UIColors.ToolMessage.timestamp
    val resultText = UIColors.TaskList.taskText
    
    val displayName = toolNameToDisplay(toolName)
    val lineCount = result.linesIterator.size
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;'>
       |<b>→ Tool Result:</b> <span style='font-family:${MarkdownRenderer.codeFont};'>$displayName</span> <span style='color:#888;font-weight:normal;'>($lineCount lines)</span></div>
       |<div style='font-family:${MarkdownRenderer.codeFont};font-size:10pt;color:$resultText;white-space:pre-wrap;'>
       |${HtmlUtil.escapeHtml(result)}</div>
       |</div>""".stripMargin
  }

  /** Render HTML widget for a newly added task notification.
    * 
    * Displays a compact card showing the task title with truncated description
    * and acceptance criteria. Used when the LLM calls task_list_add.
    * 
    * @param title Task title (max displayed: full)
    * @param description Task description (truncated to 100 chars for display)
    * @param criteria Acceptance criteria (truncated to 100 chars for display)
    * @return HTML string for injection into chat as a Widget message
    */
  def taskAdded(
      title: String,
      description: String,
      criteria: String
  ): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText
    
    val truncDesc = if (description.length > 100) description.take(100) + "..." else description
    val truncCrit = if (criteria.length > 100) criteria.take(100) + "..." else criteria
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;font-weight:bold;'>
       |+ Task Added</div>
       |<div style='font-size:11pt;color:$taskText;margin-bottom:2px;'>
       |"${HtmlUtil.escapeHtml(title)}"</div>
       |<div style='font-size:9pt;color:$labelColor;margin-top:4px;'>
       |Description: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncDesc)}</span></div>
       |<div style='font-size:9pt;color:$labelColor;'>
       |Criteria: <span style='color:$taskText;'>${HtmlUtil.escapeHtml(truncCrit)}</span></div>
       |</div>""".stripMargin
  }

  /** Render HTML widget for a task status change (done/irrelevant).
    * 
    * Shows a status update card with the task title, new status icon, and
    * overall progress summary. Used when the LLM calls task_list_done or
    * task_list_irrelevant.
    * 
    * @param taskId ID of the task that changed status
    * @param status New status: "done" or "irrelevant"
    * @param result Status message returned by TaskList operation
    * @return HTML string for injection into chat as a Widget message
    */
  def taskStatus(taskId: Int, status: String, result: String): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val icon = if (status == "done") UIColors.TaskList.doneIcon else UIColors.TaskList.irrelevantIcon
    val symbol = if (status == "done") "✓" else "✗"
    val action = if (status == "done") "marked as done" else "marked as irrelevant"
    
    TaskList.getTasks.find(_.id == taskId) match {
      case Some(task) =>
        val (doneCount, todoCount, _) = TaskList.getStatusCounts
        val progress = s"$doneCount/${TaskList.getTaskCount} done, $todoCount pending"
        
        s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
           |border-left:4px solid $border;border-radius:3px;
           |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
           |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;font-weight:bold;'>
           |<span style='color:$icon;'>$symbol</span> Task #$taskId $action</div>
           |<div style='font-size:11pt;margin-bottom:2px;'>
           |"${HtmlUtil.escapeHtml(task.title)}"</div>
           |<div style='font-size:9pt;color:${UIColors.TaskList.progressText};'>
           |Progress: $progress</div>
           |</div>""".stripMargin
      case None =>
        s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
           |border-left:4px solid $border;border-radius:3px;
           |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
           |<div style='font-size:10pt;color:$headerText;'>
           |${HtmlUtil.escapeHtml(result)}</div>
           |</div>""".stripMargin
    }
  }

  /** Render HTML widget showing the full task list as a checklist.
    * 
    * Displays all tasks with status icons (✓ done, ○ pending, ✗ irrelevant, ● next).
    * Used when the LLM calls task_list_show or task_list_next.
    * 
    * @param highlightNext If true, visually emphasizes the next pending task with
    *                      a filled circle (●) and "← next" marker
    * @return HTML string for injection into chat as a Widget message
    */
  def taskList(highlightNext: Boolean): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val progressText = UIColors.TaskList.progressText
    val doneIcon = UIColors.TaskList.doneIcon
    val pendingIcon = UIColors.TaskList.pendingIcon
    val nextIcon = UIColors.TaskList.nextIcon
    val irrelevantIcon = UIColors.TaskList.irrelevantIcon
    val irrelevantText = UIColors.TaskList.irrelevantText
    val taskText = UIColors.TaskList.taskText
    
    val tasks = TaskList.getTasks
    if (tasks.isEmpty) {
      s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
         |border-left:4px solid $border;border-radius:3px;
         |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
         |<div style='font-size:10pt;color:$headerText;font-weight:bold;'>Task List</div>
         |<div style='font-size:10pt;color:$progressText;margin-top:4px;'>
         |Task list is empty. Add tasks to get started.</div>
         |</div>""".stripMargin
    } else {
      val (doneCount, todoCount, _) = TaskList.getStatusCounts
      val progress = s"$doneCount/${tasks.length} done, $todoCount pending"
      
      val nextTaskId = tasks.find(_.status == TaskList.Todo).map(_.id)
      
      val taskItems = tasks.map { task =>
        val isNext = highlightNext && nextTaskId.contains(task.id)
        val (icon, iconColor) = task.status match {
          case TaskList.Done => ("✓", doneIcon)
          case TaskList.Irrelevant => ("✗", irrelevantIcon)
          case TaskList.Todo if isNext => ("●", nextIcon)
          case TaskList.Todo => ("○", pendingIcon)
        }
        
        val titleStyle = task.status match {
          case TaskList.Irrelevant => s"color:$irrelevantText;text-decoration:line-through;"
          case _ => s"color:$taskText;"
        }
        
        val nextMarker = if (isNext) s" <span style='color:$nextIcon;font-size:9pt;'>← next</span>" else ""
        
        s"""<div style='margin:2px 0;'>
           |<span style='color:$iconColor;font-weight:bold;margin-right:6px;'>$icon</span>
           |<span style='$titleStyle;font-size:10pt;'>#${task.id}. ${HtmlUtil.escapeHtml(task.title)}</span>$nextMarker
           |</div>""".stripMargin
      }.mkString("\n")
      
      s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
         |border-left:4px solid $border;border-radius:3px;
         |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
         |<div style='font-size:10pt;color:$headerText;margin-bottom:2px;font-weight:bold;'>
         |Task List <span style='font-weight:normal;color:$progressText;'>($progress)</span></div>
         |<div style='margin-top:6px;'>
         |$taskItems
         |</div>
         |</div>""".stripMargin
    }
  }

  /** Render HTML widget showing detailed information for a specific task.
    * 
    * Displays full task title, description, acceptance criteria, and status icon.
    * Used when the LLM calls task_list_get.
    * 
    * @param task The task to display details for
    * @return HTML string for injection into chat as a Widget message
    */
  def taskDetail(task: TaskList.Task): String = {
    val border = UIColors.TaskList.border
    val bg = UIColors.TaskList.background
    val headerText = UIColors.TaskList.headerText
    val labelColor = UIColors.TaskList.labelColor
    val taskText = UIColors.TaskList.taskText
    val (icon, iconColor) = task.status match {
      case TaskList.Done => ("✓", UIColors.TaskList.doneIcon)
      case TaskList.Irrelevant => ("✗", UIColors.TaskList.irrelevantIcon)
      case TaskList.Todo => ("○", UIColors.TaskList.pendingIcon)
    }
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:4px;font-weight:bold;'>
       |Task #${task.id}: ${HtmlUtil.escapeHtml(task.title)}
       |<span style='color:$iconColor;margin-left:8px;'>[$icon]</span></div>
       |<div style='font-size:9pt;color:$labelColor;margin-top:6px;margin-bottom:2px;'>Description:</div>
       |<div style='font-size:10pt;color:$taskText;margin-bottom:6px;'>
       |${HtmlUtil.escapeHtml(task.description)}</div>
       |<div style='font-size:9pt;color:$labelColor;margin-bottom:2px;'>Acceptance Criteria:</div>
       |<div style='font-size:10pt;color:$taskText;'>
       |${HtmlUtil.escapeHtml(task.acceptanceCriteria)}</div>
       |</div>""".stripMargin
  }

  /** Render HTML for a user prompt with multiple choice options.
    * @param question the question to present
    * @param context optional context/explanation
    * @param options list of option strings
    * @param onChoice callback to register actions for each option
    * @return HTML for the prompt widget
    * 
    * NOTE: Option selection is click-only. Keyboard-accessible selection
    * would require JS-like focus management which JEditorPane doesn't support.
    * Consider migrating to JPanel-based widgets for full keyboard support.
    */
  def askUser(
      question: String,
      context: String,
      options: List[String],
      onChoice: String => Unit
  ): String = {
    // Register an action for each option button
    val optionButtons = options.zipWithIndex
      .map { case (opt, idx) =>
        val actionId = AssistantDockable.registerAction(() => onChoice(opt))
        // Use letters A-Z for first 26 options, then numbers 27+ for any beyond
        val label =
          if (idx < 26) ('A' + idx).toChar.toString else (idx + 1).toString
        // Each option as a clickable list item
        s"""<div style='margin:2px 0 2px 12px;'>
         |<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionLetter};font-weight:bold;'>$label.</a>
         |<a href='action:insert:$actionId' style='text-decoration:none;color:${UIColors.AskUser.optionText};margin-left:8px;'>
         |${HtmlUtil.escapeHtml(opt)}</a>
         |</div>""".stripMargin
      }
      .mkString("\n")

    val contextHtml = if (context.nonEmpty) {
      s"<div style='font-size:10pt;color:${UIColors.AskUser.contextText};margin:4px 0 8px;font-style:italic;'>${HtmlUtil.escapeHtml(context)}</div>"
    } else ""

    // Match the message bubble pattern: white background + colored left border only
    s"""<div style='margin:6px 0;padding:8px 10px;background:${UIColors.AskUser.background};
       |border-left:4px solid ${UIColors.AskUser.border};border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:${UIColors.AskUser.title};margin-bottom:3px;'>
       |<b>Assistant needs your input</b></div>
       |<div style='font-size:12pt;color:#333333;margin-bottom:6px;'>
       |${HtmlUtil.escapeHtml(question)}</div>
       |$contextHtml
       |$optionButtons
       |</div>""".stripMargin
  }

  /** Render HTML widget for planning in progress.
    * Shows the current phase of the adaptive tree-of-thought planning process.
    * 
    * @param problem Brief description of the problem being planned
    * @param phase Current phase: "brainstorm", "elaborate", or "select"
    * @param approachTitles Titles of the 3 approaches (for elaborate/select phases)
    * @return HTML string for injection into chat as a Widget message
    */
  def planningInProgress(
      problem: String,
      phase: String,
      approachTitles: List[String] = List.empty
  ): String = {
    val border = UIColors.ToolMessage.border
    val bg = "white"
    val headerText = UIColors.ToolMessage.timestamp
    val progressText = UIColors.TaskList.progressText
    
    val truncProblem = if (problem.length > 80) problem.take(77) + "..." else problem
    
    val phaseDisplay = phase match {
      case "brainstorm" => "Phase 1: Brainstorming approaches..."
      case "elaborate" => "Phase 2: Elaborating approaches in parallel..."
      case "select" => "Phase 3: Selecting best approach..."
      case _ => "Planning..."
    }
    
    val approachesHtml = if (approachTitles.nonEmpty) {
      val items = approachTitles.zipWithIndex.map { case (title, idx) =>
        s"<div style='margin-left:12px;font-size:10pt;color:$progressText;'>→ Approach ${idx + 1}: ${HtmlUtil.escapeHtml(title)}</div>"
      }.mkString("\n")
      s"\n$items"
    } else ""
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:3px;'>
       |<b>→ Planning:</b> "${HtmlUtil.escapeHtml(truncProblem)}"</div>
       |<div style='font-size:10pt;color:$progressText;margin-top:4px;'>
       |$phaseDisplay</div>$approachesHtml
       |</div>""".stripMargin
  }

  /** Render HTML widget showing the planning result.
    * Shows all 3 approaches, which was selected, why, and the final plan.
    * 
    * @param problem The problem that was planned
    * @param approaches List of approach titles
    * @param selectedApproach Index of selected approach (1-based)
    * @param reasoning Why this approach was selected
    * @param plan The final detailed plan text
    * @param registerAction Function to register collapse/expand action
    * @return HTML string for injection into chat as a Widget message
    */
  def planningResult(
      problem: String,
      approaches: List[String],
      selectedApproach: Int,
      reasoning: String,
      plan: String,
      registerAction: (() => Unit) => String
  ): String = {
    val border = UIColors.ToolMessage.border
    val bg = "white"
    val headerText = UIColors.ToolMessage.timestamp
    val progressText = UIColors.TaskList.progressText
    val selectedIcon = UIColors.TaskList.doneIcon
    val taskText = UIColors.TaskList.taskText
    val linkColor = UIColors.linkColor
    
    val truncProblem = if (problem.length > 80) problem.take(77) + "..." else problem
    
    // List all approaches with selection indicator
    val approachesHtml = approaches.zipWithIndex.map { case (title, idx) =>
      val isSelected = (idx + 1) == selectedApproach
      val marker = if (isSelected) s"<span style='color:$selectedIcon;font-weight:bold;'>✓</span> " else "  "
      val style = if (isSelected) s"font-weight:bold;color:$headerText;" else s"color:$progressText;"
      s"<div style='margin:2px 0 2px 12px;font-size:10pt;$style;'>$marker${idx + 1}. ${HtmlUtil.escapeHtml(title)}</div>"
    }.mkString("\n")
    
    // Show reasoning for selection
    val reasoningHtml = s"""<div style='margin:8px 0 8px 12px;font-size:10pt;color:$taskText;font-style:italic;'>
       |"${HtmlUtil.escapeHtml(reasoning)}"</div>""".stripMargin
    
    // Plan content with collapse/expand
    val planLines = plan.linesIterator.toList
    val planHtml = if (planLines.length <= 15) {
      s"<pre style='font-family:${MarkdownRenderer.codeFont};font-size:10pt;color:$taskText;white-space:pre-wrap;margin:8px 0 0 12px;'>${HtmlUtil.escapeHtml(plan)}</pre>"
    } else {
      val preview = planLines.take(5).mkString("\n")
      val expandId = registerAction(() => {
        GUI_Thread.later {
          val fullHtml = planningResultExpanded(problem, approaches, selectedApproach, reasoning, plan)
          ChatAction.addMessage(ChatAction.Message(ChatAction.Widget, fullHtml,
            java.time.LocalDateTime.now(), rawHtml = true, transient = true))
          AssistantDockable.showConversation(ChatAction.getHistory)
        }
      })
      val previewHtml = HtmlUtil.escapeHtml(preview)
      s"""<pre style='font-family:${MarkdownRenderer.codeFont};font-size:10pt;color:$taskText;white-space:pre-wrap;margin:8px 0 0 12px;'>$previewHtml</pre>
         |<div style='margin:6px 0 0 12px;font-size:10pt;'>
         |<a href='action:insert:$expandId' style='color:$linkColor;text-decoration:none;'>
         |▸ Show full plan (${planLines.length} lines)</a></div>""".stripMargin
    }
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:4px;font-weight:bold;'>
       |✅ Planning Complete: "${HtmlUtil.escapeHtml(truncProblem)}"</div>
       |<div style='font-size:9pt;color:$progressText;margin:4px 0 4px 12px;'>Approaches Considered:</div>
       |$approachesHtml
       |<div style='font-size:9pt;color:$progressText;margin:8px 0 2px 12px;'>Selection Reasoning:</div>
       |$reasoningHtml
       |<div style='font-size:9pt;color:$progressText;margin:8px 0 2px 12px;'>Final Plan:</div>
       |$planHtml
       |</div>""".stripMargin
  }

  /** Render expanded planning result (full plan, no truncation). */
  private def planningResultExpanded(
      problem: String,
      approaches: List[String],
      selectedApproach: Int,
      reasoning: String,
      plan: String
  ): String = {
    val border = UIColors.ToolMessage.border
    val bg = "white"
    val headerText = UIColors.ToolMessage.timestamp
    val progressText = UIColors.TaskList.progressText
    val selectedIcon = UIColors.TaskList.doneIcon
    val taskText = UIColors.TaskList.taskText
    
    val truncProblem = if (problem.length > 80) problem.take(77) + "..." else problem
    
    val approachesHtml = approaches.zipWithIndex.map { case (title, idx) =>
      val isSelected = (idx + 1) == selectedApproach
      val marker = if (isSelected) s"<span style='color:$selectedIcon;font-weight:bold;'>✓</span> " else "  "
      val style = if (isSelected) s"font-weight:bold;color:$headerText;" else s"color:$progressText;"
      s"<div style='margin:2px 0 2px 12px;font-size:10pt;$style;'>$marker${idx + 1}. ${HtmlUtil.escapeHtml(title)}</div>"
    }.mkString("\n")
    
    val reasoningHtml = s"""<div style='margin:8px 0 8px 12px;font-size:10pt;color:$taskText;font-style:italic;'>
       |"${HtmlUtil.escapeHtml(reasoning)}"</div>""".stripMargin
    
    s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
       |border-left:4px solid $border;border-radius:3px;
       |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
       |<div style='font-size:10pt;color:$headerText;margin-bottom:4px;font-weight:bold;'>
       |✅ Planning Complete: "${HtmlUtil.escapeHtml(truncProblem)}"</div>
       |<div style='font-size:9pt;color:$progressText;margin:4px 0 4px 12px;'>Approaches Considered:</div>
       |$approachesHtml
       |<div style='font-size:9pt;color:$progressText;margin:8px 0 2px 12px;'>Selection Reasoning:</div>
       |$reasoningHtml
       |<div style='font-size:9pt;color:$progressText;margin:8px 0 2px 12px;'>Full Plan:</div>
       |<pre style='font-family:${MarkdownRenderer.codeFont};font-size:10pt;color:$taskText;white-space:pre-wrap;margin:8px 0 0 12px;'>${HtmlUtil.escapeHtml(plan)}</pre>
       |</div>""".stripMargin
  }
}
