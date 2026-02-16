/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View

/** Cleans up Isabelle code via LLM (cartouches, formatting) with optional I/Q verification and retry. */
object TidyAction {
  def tidy(view: View): Unit = {
    ChatAction.addMessage("user", ":tidy")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val textArea = view.getTextArea
    val selection = textArea.getSelectedText

    val code = if (selection != null && selection.trim.nonEmpty) selection
    else CommandExtractor.getCommandAtOffset(buffer, textArea.getCaretPosition).getOrElse("")

    if (code.isEmpty) {
      ChatAction.addResponse("No code to tidy. Select text or place cursor on a command.")
    } else {
      val commandOpt = IQIntegration.getCommandAtOffset(buffer, textArea.getCaretPosition)
      val canVerify = IQAvailable.isAvailable && commandOpt.isDefined

      CopilotDockable.setBadge(VerificationBadge.Verifying)

      Isabelle_Thread.fork(name = "copilot-tidy") {
        try {
          val prompt = PromptLoader.load("tidy.md", Map("code" -> code))
          val response = BedrockClient.invokeInContext(prompt)

          if (!canVerify) {
            showResult(view, response, VerificationBadge.Unverified)
          } else {
            GUI_Thread.later {
              VerifyWithRetry.verify(view, commandOpt.get,
                extractCode(response), response, 1,
                retryPrompt = (failed, error) => PromptLoader.load("tidy_retry.md",
                  Map("code" -> code, "failed_attempt" -> failed, "error" -> error)),
                extractCode = extractCode,
                showResult = (resp, badge) => showResult(view, resp, badge))
            }
          }
        } catch {
          case ex: Exception =>
            GUI_Thread.later {
              CopilotDockable.setStatus("Error: " + ex.getMessage)
              GUI.error_dialog(view, "Tidy Error", ex.getMessage)
            }
        }
      }
    }
  }

  private def showResult(view: View, response: String, badge: VerificationBadge.BadgeType): Unit = {
    val code = extractCode(response)
    CopilotDockable.setBadge(badge)
    CopilotDockable.respondInChat("Tidied code:", 
      Some((code, InsertHelper.createInsertAction(view, code))))
    CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
  }

  private def extractCode(response: String): String = {
    val blocks = SendbackHelper.extractCodeBlocks(response)
    if (blocks.nonEmpty) blocks.mkString("\n") else response
  }
}
