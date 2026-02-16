/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Runs Quickcheck via I/Q and offers LLM explanation of counterexamples. */
object QuickcheckAction {
  def run(view: View): Unit = {
    ChatAction.addMessage("user", ":quickcheck")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    if (commandOpt.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Copilot", "No command at cursor")
    } else {
      val goal = GoalExtractor.getGoalState(buffer, offset).getOrElse("")
      CopilotDockable.setStatus("Running quickcheck...")
      val timeout = CopilotOptions.getQuickcheckTimeout

      GUI_Thread.later {
        runQuickcheckAsync(view, commandOpt.get, timeout, { result =>
          GUI_Thread.later {
            displayResult(view, result, goal)
            CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
          }
        })
      }
    }
  }

  private def runQuickcheckAsync(
    view: View, command: Command, timeoutMs: Long,
    callback: Either[String, String] => Unit
  ): Unit = {
    IQIntegration.runQueryAsync(view, command, List("quickcheck"), timeoutMs, callback)
  }

  private def displayResult(view: View, result: Either[String, String], goal: String): Unit = {
    result match {
      case Right(output) if output.toLowerCase.contains("counterexample") =>
        val id = CopilotDockable.registerAction(() =>
          ExplainCounterexampleAction.explain(view, goal, output.trim))
        ChatAction.addMessage("assistant",
          s"Quickcheck found counterexample:\n\n```\n${output.trim}\n```\n\n{{ACTION:$id:Explain counterexample}}")
        CopilotDockable.showConversation(ChatAction.getHistory)
      case Right(output) if output.toLowerCase.contains("no counterexample") =>
        CopilotDockable.respondInChat("Quickcheck: No counterexample found.")
      case Right(output) =>
        val text = if (output.trim.isEmpty) "(no output)" else output.trim
        CopilotDockable.respondInChat(s"Quickcheck result:\n\n$text")
      case Left(error) =>
        CopilotDockable.respondInChat(s"Quickcheck error: $error")
    }
  }
}
