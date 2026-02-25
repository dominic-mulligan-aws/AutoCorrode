/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Renders HTML widgets for interactive chat elements (task lists, user prompts).
 * Extracted from AssistantTools to separate rendering concerns from tool execution.
 */
object WidgetRenderer {

  /** Render HTML for a newly added task notification. */
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

  /** Render HTML for a task status change (done/irrelevant). */
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

  /** Render HTML for the full task list display. */
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
      return s"""<div style='margin:6px 0;padding:8px 10px;background:$bg;
         |border-left:4px solid $border;border-radius:3px;
         |overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);'>
         |<div style='font-size:10pt;color:$headerText;font-weight:bold;'>Task List</div>
         |<div style='font-size:10pt;color:$progressText;margin-top:4px;'>
         |Task list is empty. Add tasks to get started.</div>
         |</div>""".stripMargin
    }
    
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

  /** Render HTML for detailed task information. */
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
}