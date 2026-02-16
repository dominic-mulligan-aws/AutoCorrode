/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View

/** Generates introduction and elimination rules for datatypes/definitions via LLM. */
object GenerateRulesAction {
  
  /** Chat command handler: generate intro rule for definition at cursor. */
  def chatGenerateIntro(view: View): Unit = {
    CommandExtractor.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition) match {
      case Some(text) => generateIntro(view, text)
      case None => ChatAction.addResponse("No definition found at cursor position.")
    }
  }

  /** Chat command handler: generate elim rule for definition at cursor. */
  def chatGenerateElim(view: View): Unit = {
    CommandExtractor.getCommandAtOffset(view.getBuffer, view.getTextArea.getCaretPosition) match {
      case Some(text) => generateElim(view, text)
      case None => ChatAction.addResponse("No definition found at cursor position.")
    }
  }

  def generateIntro(view: View, definitionText: String): Unit =
    generate(view, definitionText, "generate_intro_rule.md", "intro")
  
  def generateElim(view: View, definitionText: String): Unit =
    generate(view, definitionText, "generate_elim_rule.md", "elim")
  
  private def generate(view: View, definitionText: String, promptFile: String, kind: String): Unit = {
    ChatAction.addMessage("user", s":generate-$kind selection")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    ActionHelper.runAsync(s"copilot-generate-$kind", s"Generating $kind rule...") {
      val context = ContextFetcher.getContext(view, 3000)
      val subs = Map("definition" -> definitionText) ++ context.map("context" -> _)
      val prompt = PromptLoader.load(promptFile, subs)
      SendbackHelper.stripCodeFences(BedrockClient.invokeInContext(prompt).trim)
    }(
      cleaned => {
        CopilotDockable.respondInChat(s"Generated $kind rule:", Some((cleaned, () =>
          view.getBuffer.insert(view.getTextArea.getCaretPosition, cleaned))))
        CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
      }
    )
  }
}
