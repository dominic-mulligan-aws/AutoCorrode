/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/** Tests for ConversationRenderer HTML output. */
class ConversationRendererTest extends AnyFunSuite with Matchers {

  test("createUserMessageHtml should include username and timestamp") {
    val html = ConversationRenderer.createUserMessageHtml("Hello", "12:34")
    html should include("<b>You</b>")
    html should include("12:34")
    html should include("Hello")
  }

  test("createUserMessageHtml should have blue border") {
    val html = ConversationRenderer.createUserMessageHtml("Test", "12:00")
    html should include(UIColors.ChatBubble.userBorder)
  }

  test("createUserMessageHtml should include copy link") {
    val html = ConversationRenderer.createUserMessageHtml("Copy me", "12:00")
    html should include("action:copy:")
  }

  test("createAssistantMessageHtml should include assistant label") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "Hello from assistant",
      "12:34",
      rawHtml = false,
      registerAction
    )
    html should include("<b>Assistant</b>")
    html should include("12:34")
    html should include("Hello from assistant")
  }

  test("createAssistantMessageHtml should use purple border for normal messages") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "Normal message",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include(UIColors.ChatBubble.assistantBorder)
  }

  test("createAssistantMessageHtml should use red border for errors") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "Error: something went wrong",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include(UIColors.ChatBubble.errorBorder)
  }

  test("createAssistantMessageHtml should use red border for FAIL messages") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "[FAIL] Verification failed",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include(UIColors.ChatBubble.errorBorder)
  }

  test("createAssistantMessageHtml should process Markdown when rawHtml=false") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "This is **bold** text",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include("<b>")
    html should include("bold")
  }

  test("createAssistantMessageHtml should not process Markdown when rawHtml=true") {
    val registerAction = (_: String) => "test-id"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "<div>Raw HTML</div>",
      "12:00",
      rawHtml = true,
      registerAction
    )
    html should include("<div>Raw HTML</div>")
    html should not include("&lt;div&gt;")
  }

  test("createAssistantMessageHtml should convert INSERT placeholders") {
    val registerAction = (_: String) => "test-id-123"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "Try this: {{INSERT:abc123}}",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include("action:insert:abc123")
    html should include("[Insert]")
  }

  test("createAssistantMessageHtml should convert ACTION placeholders") {
    val registerAction = (_: String) => "test-id-123"
    val html = ConversationRenderer.createAssistantMessageHtml(
      "Click here: {{ACTION:abc123:Retry}}",
      "12:00",
      rawHtml = false,
      registerAction
    )
    html should include("action:insert:abc123")
    html should include("Run Retry")
  }

  test("createToolMessageHtml should include tool name") {
    val params = Map(
      "theory" -> ResponseParser.StringValue("Foo.thy"),
      "start_line" -> ResponseParser.IntValue(1)
    )
    val html = ConversationRenderer.createToolMessageHtml(
      "read_theory",
      params,
      "12:34"
    )
    html should include("<b>Tool</b>")
    html should include("12:34")
    html should include("ReadTheory")
  }

  test("createToolMessageHtml should convert snake_case to PascalCase") {
    val html = ConversationRenderer.createToolMessageHtml(
      "get_proof_context",
      Map.empty,
      "12:00"
    )
    html should include("GetProofContext")
  }

  test("createToolMessageHtml should show parameters inline") {
    val params = Map(
      "theory" -> ResponseParser.StringValue("Foo"),
      "pattern" -> ResponseParser.StringValue("lemma")
    )
    val html = ConversationRenderer.createToolMessageHtml(
      "search_in_theory",
      params,
      "12:00"
    )
    html should include("theory: Foo")
    html should include("pattern: lemma")
  }

  test("createToolMessageHtml should handle empty params") {
    val html = ConversationRenderer.createToolMessageHtml(
      "list_theories",
      Map.empty,
      "12:00"
    )
    html should include("ListTheories")
    html should include("()")
  }

  test("createWelcomeHtml should include title and description") {
    val registerHelp = () => "help-id"
    val html = ConversationRenderer.createWelcomeHtml(registerHelp)
    html should include("Isabelle Assistant")
    html should include("AWS Bedrock")
  }

  test("createWelcomeHtml should include help link") {
    val registerHelp = () => "help-id-123"
    val html = ConversationRenderer.createWelcomeHtml(registerHelp)
    html should include("action:insert:help-id-123")
    html should include(":help")
  }

  test("createWelcomeHtml should show warning when model not configured") {
    val originalModel = AssistantOptions.getModelId
    try {
      AssistantOptions.setSetting("model", "")
      val registerHelp = () => "help-id"
      val html = ConversationRenderer.createWelcomeHtml(registerHelp)
      html should include("No model configured")
      html should include(":models")
    } finally {
      if (originalModel.nonEmpty)
        AssistantOptions.setSetting("model", originalModel)
    }
  }

  test("createWelcomeHtml should not show warning when model is configured") {
    val originalModel = AssistantOptions.getModelId
    try {
      AssistantOptions.setSetting("model", "us.anthropic.claude-3-5-sonnet-20241022-v2:0")
      val registerHelp = () => "help-id"
      val html = ConversationRenderer.createWelcomeHtml(registerHelp)
      html should not include "No model configured"
    } finally {
      if (originalModel.nonEmpty)
        AssistantOptions.setSetting("model", originalModel)
      else
        AssistantOptions.setSetting("model", "")
    }
  }

  test("messageBubbleHtml should include provided border color") {
    val html = ConversationRenderer.messageBubbleHtml(
      border = "#ff0000",
      headerHtml = "<div>Header</div>",
      bodyHtml = "<div>Body</div>",
      copyContent = None
    )
    html should include("border-left:4px solid #ff0000")
  }

  test("messageBubbleHtml should include copy link when copyContent provided") {
    val html = ConversationRenderer.messageBubbleHtml(
      border = "#000000",
      headerHtml = "<div>Header</div>",
      bodyHtml = "<div>Body</div>",
      copyContent = Some("Raw content")
    )
    html should include("action:copy:")
    html should include("Copy")
  }

  test("messageBubbleHtml should not include copy link when copyContent is None") {
    val html = ConversationRenderer.messageBubbleHtml(
      border = "#000000",
      headerHtml = "<div>Header</div>",
      bodyHtml = "<div>Body</div>",
      copyContent = None
    )
    html should not include "action:copy:"
  }
}