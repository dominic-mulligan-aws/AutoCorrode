/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Runs Nitpick model finder via I/Q and offers LLM explanation of counterexamples. */
object NitpickAction {
  def run(view: View): Unit = {
    ChatAction.addMessage("user", ":nitpick")
    AssistantDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    if (commandOpt.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Assistant", "No command at cursor")
    } else {
      val goal = GoalExtractor.getGoalState(buffer, offset).getOrElse("")
      AssistantDockable.setStatus("Running nitpick...")
      val timeout = AssistantOptions.getNitpickTimeout

      GUI_Thread.later {
        runNitpickAsync(view, commandOpt.get, timeout, { result =>
          GUI_Thread.later {
            displayResult(view, result, goal)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        })
      }
    }
  }

  private def runNitpickAsync(
    view: View, command: Command, timeoutMs: Long,
    callback: Either[String, String] => Unit
  ): Unit = {
    IQIntegration.runQueryAsync(view, command, List("nitpick"), timeoutMs, callback)
  }

  private def displayResult(view: View, result: Either[String, String], goal: String): Unit = {
    result match {
      case Right(output) if output.toLowerCase.contains("counterexample") =>
        val header = if (output.toLowerCase.contains("potential"))
          "Nitpick found potential counterexample:" else "Nitpick found counterexample:"
        val id = AssistantDockable.registerAction(() =>
          ExplainCounterexampleAction.explain(view, goal, output.trim))
        ChatAction.addMessage("assistant",
          s"$header\n\n```\n${output.trim}\n```\n\n{{ACTION:$id:Explain counterexample}}")
        AssistantDockable.showConversation(ChatAction.getHistory)
      case Right(output) if output.toLowerCase.contains("no counterexample") =>
        AssistantDockable.respondInChat("Nitpick: No counterexample found.")
      case Right(_) =>
        AssistantDockable.respondInChat("Nitpick executed. Check the Output panel for results.")
      case Left(error) =>
        AssistantDockable.respondInChat(s"Nitpick error: $error")
    }
  }
}
