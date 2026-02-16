/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Runs Sledgehammer via I/Q and displays found proof methods with insert links. */
object SledgehammerAction {
  def run(view: View): Unit = {
    ChatAction.addMessage("user", ":sledgehammer")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)

    if (commandOpt.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Copilot", "No command at cursor")
    } else {
      CopilotDockable.setStatus("Running sledgehammer...")
      val timeout = CopilotOptions.getSledgehammerTimeout

      GUI_Thread.later {
        IQIntegration.runSledgehammerAsync(view, commandOpt.get, timeout, {
          case Right(results) if results.nonEmpty =>
            displayResults(view, results)
            CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
          case Right(_) =>
            CopilotDockable.respondInChat("Sledgehammer found no proofs.")
            CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
          case Left(error) =>
            CopilotDockable.respondInChat(s"Sledgehammer error: $error")
            CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
        })
      }
    }
  }

  private def displayResults(view: View, results: List[IQIntegration.SledgehammerResult]): Unit = {
    val sb = new StringBuilder(s"Sledgehammer found ${results.length} proofs:\n\n")
    for (r <- results) {
      val id = CopilotDockable.registerAction(() => {
        val offset = view.getTextArea.getCaretPosition
        view.getBuffer.insert(offset, r.proofMethod)
      })
      sb.append(s"[sledgehammer] `${r.proofMethod}` (${r.timeMs}ms) {{INSERT:$id}}\n")
    }
    ChatAction.addMessage("assistant", sb.toString)
    CopilotDockable.showConversation(ChatAction.getHistory)
  }
}
