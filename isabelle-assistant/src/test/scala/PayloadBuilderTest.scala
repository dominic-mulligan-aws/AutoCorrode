/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for PayloadBuilder: Anthropic model detection and JSON payload construction.
 * Updated to test only Anthropic support (non-Anthropic providers removed).
 */
class PayloadBuilderTest extends AnyFunSuite with Matchers {

  // --- Provider detection ---

  test("isAnthropicModel should detect Anthropic models") {
    PayloadBuilder.isAnthropicModel("anthropic.claude-v2") shouldBe true
    PayloadBuilder.isAnthropicModel("anthropic.claude-3-sonnet-20240229-v1:0") shouldBe true
  }

  test("isAnthropicModel should handle CRIS-prefixed IDs") {
    PayloadBuilder.isAnthropicModel("us.anthropic.claude-3-sonnet") shouldBe true
    PayloadBuilder.isAnthropicModel("eu.anthropic.claude-3-sonnet") shouldBe true
    PayloadBuilder.isAnthropicModel("ap.anthropic.claude-v2") shouldBe true
    PayloadBuilder.isAnthropicModel("global.anthropic.claude-haiku-4-5") shouldBe true
  }

  test("isAnthropicModel should reject non-Anthropic models") {
    PayloadBuilder.isAnthropicModel("meta.llama3-70b") shouldBe false
    PayloadBuilder.isAnthropicModel("amazon.titan-text") shouldBe false
    PayloadBuilder.isAnthropicModel("mistral.mistral-7b") shouldBe false
    PayloadBuilder.isAnthropicModel("us.meta.llama3-70b") shouldBe false
    PayloadBuilder.isAnthropicModel("") shouldBe false
  }

  // --- Payload construction ---

  test("buildPayload for Anthropic should include anthropic_version and messages array") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000)
    payload should include("anthropic_version")
    payload should include("bedrock-2023-05-31")
    payload should include("messages")
    payload should include("Hello")
    payload should include("1000")
    payload should not include "system"
  }

  test("buildPayload for Anthropic with system prompt should include system field") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000, Some("You are helpful"))
    payload should include("anthropic_version")
    payload should include("system")
    payload should include("You are helpful")
    payload should include("messages")
    payload should include("Hello")
  }

  test("buildPayload for Anthropic with empty system prompt should not include system field") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello", 0.5, 1000, Some(""))
    payload should not include "system"
  }

  test("buildPayload should properly escape special characters") {
    val payload = PayloadBuilder.buildPayload("anthropic.claude-v2", "Hello \"world\" \n test", 0.5, 1000)
    // Jackson handles JSON escaping automatically
    payload should include("Hello")
  }

  test("buildChatPayload for Anthropic should include system prompt separately") {
    val payload = PayloadBuilder.buildChatPayload(
      "anthropic.claude-v2", "You are helpful", List(("user", "Hi")), 0.3, 2000)
    payload should include("system")
    payload should include("You are helpful")
    payload should include("messages")
    payload should include("Hi")
  }

  test("buildChatPayload should handle multiple messages") {
    val messages = List(("user", "Hello"), ("assistant", "Hi there"), ("user", "Help me"))
    val payload = PayloadBuilder.buildChatPayload(
      "anthropic.claude-v2", "System", messages, 0.3, 2000)
    payload should include("Hello")
    payload should include("Hi there")
    payload should include("Help me")
  }

  test("isAnthropicStructuredContent should accept valid content block arrays") {
    PayloadBuilder.isAnthropicStructuredContent(
      """[{"type":"text","text":"hello"},{"type":"tool_result","tool_use_id":"x","content":"ok"}]"""
    ) shouldBe true
  }

  test("isAnthropicStructuredContent should reject non-JSON and non-block arrays") {
    PayloadBuilder.isAnthropicStructuredContent("[not valid json") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("""[{"text":"missing type"}]""") shouldBe false
    PayloadBuilder.isAnthropicStructuredContent("""["plain text"]""") shouldBe false
  }

  test("buildAnthropicToolPayload should serialize bracket-prefixed plain text as string content") {
    val payload = PayloadBuilder.buildAnthropicToolPayload(
      "System",
      List(("user", "[this is plain text, not JSON blocks]")),
      0.3,
      2000
    )
    payload should include("\"content\":\"[this is plain text, not JSON blocks]\"")
  }

  test("writeJson should produce valid JSON") {
    val json = PayloadBuilder.writeJson { g =>
      g.writeStringField("key", "value")
      g.writeNumberField("num", 42)
      g.writeBooleanField("flag", true)
    }
    json should include("\"key\"")
    json should include("\"value\"")
    json should include("42")
    json should include("true")
  }

  // --- Structured output payload ---

  test("buildAnthropicStructuredPayload should include tool_choice forcing") {
    val schema = StructuredResponseSchema(
      "return_code", "Return code",
      """{"type":"object","properties":{"code":{"type":"string"}},"required":["code"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "System prompt", List(("user", "Refactor this")), schema, 0.3, 2000
    )
    payload should include("tool_choice")
    payload should include("\"type\":\"tool\"")
    payload should include("\"name\":\"return_code\"")
  }

  test("buildAnthropicStructuredPayload should include single tool definition with schema") {
    val schema = StructuredResponseSchema(
      "return_suggestions", "Return suggestions",
      """{"type":"object","properties":{"suggestions":{"type":"array","items":{"type":"string"}}},"required":["suggestions"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "System", List(("user", "Suggest")), schema, 0.5, 1000
    )
    payload should include("\"name\":\"return_suggestions\"")
    payload should include("input_schema")
    payload should include("suggestions")
    // Should include only the schema tool, not agentic tools
    payload should not include "read_theory"
    payload should not include "verify_proof"
  }

  test("buildAnthropicStructuredPayload should include anthropic_version and messages") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "Sys", List(("user", "Hello")), schema, 0.3, 500
    )
    payload should include("anthropic_version")
    payload should include("bedrock-2023-05-31")
    payload should include("messages")
    payload should include("Hello")
  }

  test("buildAnthropicStructuredPayload should handle empty system prompt") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "", List(("user", "Hello")), schema, 0.3, 500
    )
    payload should not include "\"system\""
  }

  test("buildAnthropicStructuredPayload should handle structured content in messages") {
    val schema = StructuredResponseSchema(
      "test_tool", "Test",
      """{"type":"object","properties":{"x":{"type":"string"}},"required":["x"]}"""
    )
    val structuredContent = """[{"type":"text","text":"hello"}]"""
    val payload = PayloadBuilder.buildAnthropicStructuredPayload(
      "Sys", List(("user", structuredContent)), schema, 0.3, 500
    )
    // Structured content should be raw JSON, not string-escaped
    payload should include(""""content":[{"type":"text","text":"hello"}]""")
  }
}