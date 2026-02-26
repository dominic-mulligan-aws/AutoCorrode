/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View

/**
 * Shared helper for the common action pattern: fork a background thread,
 * run an LLM call, and dispatch the result back to the GUI thread.
 * Uses ErrorHandler for consistent error handling across all actions.
 */
object ActionHelper {

  /**
   * Run an LLM-backed action in the standard fork/try/catch/GUI_Thread.later pattern.
   *
   * @param name   Thread name for debugging
   * @param status Status text shown while running
   * @param body   Background work returning the response string
   * @param onSuccess Called on GUI thread with the response
   * @param onError   Called on GUI thread with the exception message
   */
  def runAsync(
    name: String,
    status: String = AssistantConstants.STATUS_THINKING
  )(body: => String)(
    onSuccess: String => Unit,
    onError: String => Unit = msg => {
      ChatAction.addMessage(ChatAction.Assistant, s"Error: $msg")
      AssistantDockable.showConversation(ChatAction.getHistory)
      AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
    }
  ): Unit = {
    AssistantDockable.setStatus(status)
    val _ = Isabelle_Thread.fork(name = name) {
      ErrorHandler.withErrorHandling(name) {
        body
      } match {
        case scala.util.Success(response) =>
          GUI_Thread.later { onSuccess(response) }
        case scala.util.Failure(ex) =>
          GUI_Thread.later { onError(ErrorHandler.makeUserFriendly(ex.getMessage, name)) }
      }
    }
  }

  /** Convenience: run async, post response as chat message, set status Ready. */
  def runAndRespond(name: String, status: String = AssistantConstants.STATUS_THINKING)(body: => String): Unit =
    runAsync(name, status)(body)(
      response => {
        ChatAction.addMessage(ChatAction.Assistant, response)
        AssistantDockable.showConversation(ChatAction.getHistory)
        AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      }
    )

  /**
   * Run an I/Q-backed command action: fork background thread, check command at cursor, execute body.
   * Handles the common pattern of verifying cursor position before dispatching I/Q work.
   * The body receives the view and is executed on a background thread, allowing it to safely
   * call IQIntegration.*Async methods which handle their own threading and GUI callbacks.
   * 
   * @param name Thread name for debugging
   * @param status Status text to display while running
   * @param body Work to execute after verifying command exists (receives View)
   * @param view The current jEdit view
   */
  def runIQCommand(
      name: String,
      status: String
  )(body: View => Unit)(view: org.gjt.sp.jedit.View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    AssistantDockable.setStatus(status)
    
    val _ = Isabelle_Thread.fork(name = name) {
      // Verify command exists at cursor (this may call I/Q MCP so must be on background thread)
      CommandExtractor.getCommandAtOffset(buffer, offset) match {
        case None =>
          GUI_Thread.later {
            ChatAction.addResponse("No Isabelle command at cursor position.")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
        case Some(_) => 
          // Command exists — execute the body
          // Body will typically call IQIntegration.*Async which handles its own threading
          body(view)
      }
    }
  }
}
