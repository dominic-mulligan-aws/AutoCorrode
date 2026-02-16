/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View

/** Converts apply-style proofs to structured Isar via LLM, with optional I/Q verification and retry. */
object RefactorAction {
  /** Chat command handler: refactor selected proof text. */
  def chatRefactor(view: View): Unit = {
    val selectedText = view.getTextArea.getSelectedText
    if (selectedText != null && selectedText.trim.nonEmpty) refactor(view, selectedText)
    else ChatAction.addResponse("Please select proof text to refactor.")
  }

  def refactor(view: View, proofText: String): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
    val canVerify = IQAvailable.isAvailable && commandOpt.isDefined

    CopilotDockable.setBadge(VerificationBadge.Verifying)

    Isabelle_Thread.fork(name = "copilot-refactor") {
      try {
        // Fetch context information (definitions and relevant lemmas)
        val context = if (IQAvailable.isAvailable && commandOpt.isDefined) {
          fetchContext(view, commandOpt.get)
        } else ""
        
        val subs = scala.collection.mutable.Map("proof" -> proofText)
        if (context.nonEmpty) subs("context") = context
        
        val prompt = PromptLoader.load("refactor_to_isar.md", subs.toMap)
        val response = BedrockClient.invokeInContext(prompt)

        if (!canVerify) {
          showResult(view, response, VerificationBadge.Unverified)
        } else {
          GUI_Thread.later {
            VerifyWithRetry.verify(view, commandOpt.get,
              extractCode(response), response, 1,
              retryPrompt = (failed, error) => PromptLoader.load("refactor_to_isar_retry.md",
                Map("proof" -> proofText, "failed_attempt" -> failed, "error" -> error)),
              extractCode = extractCode,
              showResult = (resp, badge) => showResult(view, resp, badge))
          }
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            CopilotDockable.setStatus("Error: " + ex.getMessage)
            GUI.error_dialog(view, "Refactor Error", ex.getMessage)
          }
      }
    }
  }

  private def showResult(view: View, response: String, badge: VerificationBadge.BadgeType): Unit = {
    val code = SendbackHelper.extractCodeBlocks(response).mkString("\n")
    val insertable = if (code.nonEmpty) code else response
    CopilotDockable.setBadge(badge)
    CopilotDockable.respondInChat("Refactored to Isar:", Some((insertable, () => {
      view.getBuffer.insert(view.getTextArea.getCaretPosition, insertable)
    })))
    CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
  }

  private def extractCode(response: String): String = {
    val blocks = SendbackHelper.extractCodeBlocks(response)
    if (blocks.nonEmpty) blocks.mkString("\n") else response
  }

  private def fetchContext(view: View, command: Command): String = {
    import java.util.concurrent.{CountDownLatch, TimeUnit}
    
    // Fetch context facts and relevant theorems in parallel
    val factsLatch = new CountDownLatch(1)
    @volatile var contextFacts = ""
    
    Isabelle_Thread.fork(name = "refactor-context") {
      ErrorHandler.withErrorHandling("context facts retrieval", Some(CopilotConstants.CONTEXT_FETCH_TIMEOUT)) {
        GUI_Thread.later {
          PrintContextAction.runPrintContextAsync(view, command, CopilotConstants.CONTEXT_FETCH_TIMEOUT, { result =>
            result match {
              case Right(output) if output.trim.nonEmpty && !output.contains("No local facts") =>
                contextFacts = "Context:\n" + output.trim
              case _ =>
            }
            factsLatch.countDown()
          })
        }
      }.recover { case _ => factsLatch.countDown() }
    }
    
    factsLatch.await(CopilotConstants.CONTEXT_FETCH_TIMEOUT + CopilotConstants.TIMEOUT_BUFFER_MS, TimeUnit.MILLISECONDS)
    contextFacts
  }
}
