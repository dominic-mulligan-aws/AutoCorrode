/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View

/** Generates test cases and examples for Isabelle definitions via LLM. */
object GenerateTestsAction {
  
  /** Chat command handler: generate tests for definition at cursor. */
  def chatGenerate(view: View): Unit = {
    CommandExtractor.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition) match {
      case Some(text) => generate(view, text)
      case None => ChatAction.addResponse("No definition found at cursor position.")
    }
  }

  def generate(view: View, definitionText: String): Unit = {
    ChatAction.addMessage("user", ":generate-tests selection")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    ActionHelper.runAsync("copilot-generate-tests", "Generating test cases...") {
      val context = ContextFetcher.getContext(view, 3000)
      val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
      val prompt = PromptLoader.load("generate_tests.md", subs)
      SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
    }(
      cleaned => {
        CopilotDockable.respondInChat("Generated test cases:", Some((cleaned, () =>
          view.getBuffer.insert(view.getTextArea.getCaretPosition, cleaned))))
        CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
      }
    )
  }
}
