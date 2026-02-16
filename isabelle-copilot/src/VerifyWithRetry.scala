/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View

/**
 * Shared verification-with-retry protocol for actions that generate code via LLM
 * and optionally verify it via I/Q. Used by RefactorAction, TidyAction, ExtractLemmaAction.
 *
 * Protocol:
 * 1. Fork background thread → call LLM to generate code
 * 2. If I/Q available: dispatch to GUI thread → verifyProofAsync
 * 3. On ProofSuccess: display with [ok] badge
 * 4. On ProofFailure/Timeout and attempt < maxRetries: fork → LLM retry → goto 2
 * 5. On final failure: display with [FAIL] badge
 */
object VerifyWithRetry {

  /**
   * Start verification of generated code, retrying on failure.
   * MUST be called from the GUI thread.
   *
   * @param view       jEdit view
   * @param command    Isabelle command to verify against
   * @param codeToVerify  The generated code to verify
   * @param fullResponse  The full LLM response (for display)
   * @param attempt    Current attempt number (1-based)
   * @param retryPrompt   Function that takes (failedCode, error) and returns a retry prompt string
   * @param extractCode   Function to extract verifiable code from an LLM response
   * @param showResult    Function to display the final result with a badge
   */
  def verify(
    view: View,
    command: Command,
    codeToVerify: String,
    fullResponse: String,
    attempt: Int,
    retryPrompt: (String, String) => String,
    extractCode: String => String,
    showResult: (String, VerificationBadge.BadgeType) => Unit
  ): Unit = {
    val maxRetries = CopilotOptions.getMaxVerificationRetries
    val timeout = CopilotOptions.getVerificationTimeout

    CopilotDockable.setBadge(VerificationBadge.Verifying)

    IQIntegration.verifyProofAsync(view, command, codeToVerify, timeout, {
      case IQIntegration.ProofSuccess(timeMs, _) =>
        showResult(fullResponse, VerificationBadge.Verified(Some(timeMs)))

      case IQIntegration.MissingImport(_) =>
        showResult(fullResponse, VerificationBadge.Failed("Missing Isar_Explore import"))

      case IQIntegration.IQUnavailable =>
        showResult(fullResponse, VerificationBadge.Unverified)

      case IQIntegration.ProofTimeout if attempt < maxRetries =>
        retryInBackground(view, command, codeToVerify, "Verification timed out",
          attempt, maxRetries, retryPrompt, extractCode, showResult)

      case IQIntegration.ProofTimeout =>
        showResult(fullResponse, VerificationBadge.Failed("Timed out"))

      case IQIntegration.ProofFailure(error) if attempt < maxRetries =>
        retryInBackground(view, command, codeToVerify, error,
          attempt, maxRetries, retryPrompt, extractCode, showResult)

      case IQIntegration.ProofFailure(_) =>
        showResult(fullResponse, VerificationBadge.Failed(s"Failed after $maxRetries attempts"))
    })
  }

  private def retryInBackground(
    view: View, command: Command,
    failedCode: String, error: String,
    attempt: Int, maxRetries: Int,
    retryPrompt: (String, String) => String,
    extractCode: String => String,
    showResult: (String, VerificationBadge.BadgeType) => Unit
  ): Unit = {
    CopilotDockable.setStatus(s"Retrying (${attempt + 1}/$maxRetries)...")

    Isabelle_Thread.fork(name = "copilot-verify-retry") {
      try {
        val prompt = retryPrompt(failedCode, error)
        val response = BedrockClient.invokeNoCache(prompt)
        val code = extractCode(response)
        GUI_Thread.later {
          verify(view, command, code, response, attempt + 1,
            retryPrompt, extractCode, showResult)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            showResult(failedCode, VerificationBadge.Failed("Retry failed: " + ex.getMessage))
          }
      }
    }
  }
}
