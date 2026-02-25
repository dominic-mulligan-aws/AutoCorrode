/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonGenerator, JsonToken}
import java.io.StringWriter

/**
 * Builds JSON request payloads for Anthropic models on AWS Bedrock.
 * Extracted from BedrockClient for testability and separation of concerns.
 *
 * Supports only Anthropic Claude models. The Assistant enforces this requirement
 * via BedrockClient.requireAnthropicModel() which rejects non-Anthropic models
 * before payload construction.
 */
object PayloadBuilder {
  private val jsonFactory = new JsonFactory()

  // --- Provider detection ---

  /** Check if a model ID belongs to the Anthropic provider.
   *  Handles CRIS-prefixed IDs like "us.anthropic.claude-..." and global inference profiles. */
  def isAnthropicModel(modelId: String): Boolean = {
    val stripped = if (modelId.matches("^(us|eu|ap|global)\\..*")) modelId.dropWhile(_ != '.').drop(1) else modelId
    stripped.startsWith("anthropic.")
  }

  // --- Chat payloads ---

  /**
   * Build request payload for chat-style interactions (Anthropic only).
   *
   * @param modelId The Bedrock model identifier (must be Anthropic)
   * @param systemPrompt The system prompt
   * @param messages The conversation history as (role, content) pairs
   * @param temperature The sampling temperature (0.0-1.0)
   * @param maxTokens Maximum tokens to generate
   * @return JSON payload string
   */
  def buildChatPayload(modelId: String, systemPrompt: String, messages: List[(String, String)], temperature: Double, maxTokens: Int): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
      g.writeStringField("system", systemPrompt)
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        g.writeStringField("content", content)
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  // --- Single prompt payloads ---

  /**
   * Build request payload for single prompt interactions (Anthropic only).
   *
   * @param modelId The Bedrock model identifier (must be Anthropic)
   * @param prompt The complete prompt text
   * @param temperature The sampling temperature (0.0-1.0)
   * @param maxTokens Maximum tokens to generate
   * @param systemPrompt Optional system prompt
   * @return JSON payload string
   */
  def buildPayload(modelId: String, prompt: String, temperature: Double, maxTokens: Int, systemPrompt: Option[String] = None): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
      systemPrompt.filter(_.nonEmpty).foreach(s => g.writeStringField("system", s))
      g.writeArrayFieldStart("messages")
      g.writeStartObject()
      g.writeStringField("role", "user")
      g.writeStringField("content", prompt)
      g.writeEndObject()
      g.writeEndArray()
    }
  }

  // --- Anthropic tool-use payloads ---

  /** Build Anthropic payload with tools. Messages may contain structured content (JSON arrays). */
  def buildAnthropicToolPayload(
    systemPrompt: String, messages: List[(String, String)],
    temperature: Double, maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
      g.writeStringField("system", systemPrompt)
      AssistantTools.writeFilteredToolsJson(g)
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        if (isAnthropicStructuredContent(content)) {
          g.writeFieldName("content")
          g.writeRawValue(content)
        } else {
          g.writeStringField("content", content)
        }
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  /** Only treat content as raw JSON when it is a valid Anthropic content-block array. */
  private[assistant] def isAnthropicStructuredContent(content: String): Boolean = {
    val trimmed = content.trim
    if (!trimmed.startsWith("[")) return false
    val parser = jsonFactory.createParser(trimmed)
    try {
      if (parser.nextToken() != JsonToken.START_ARRAY) return false
      var token = parser.nextToken()
      while (token != null && token != JsonToken.END_ARRAY) {
        if (token != JsonToken.START_OBJECT) return false
        var hasValidType = false
        while (parser.nextToken() != JsonToken.END_OBJECT) {
          if (parser.currentToken() == JsonToken.FIELD_NAME) {
            val fieldName = parser.currentName()
            val valueToken = parser.nextToken()
            if (
              fieldName == "type" &&
              valueToken == JsonToken.VALUE_STRING &&
              parser.getValueAsString("").trim.nonEmpty
            ) {
              hasValidType = true
            } else {
              val _ = parser.skipChildren()
            }
          }
        }
        if (!hasValidType) return false
        token = parser.nextToken()
      }
      token == JsonToken.END_ARRAY
    } catch {
      case _: Exception => false
    } finally {
      parser.close()
    }
  }

  /** Build Anthropic payload with a single forced tool for structured output.
    * Uses tool_choice to guarantee the response is a tool_use block matching the schema.
    * Does NOT include agentic tools — only the synthetic schema tool. */
  def buildAnthropicStructuredPayload(
    systemPrompt: String, messages: List[(String, String)],
    schema: StructuredResponseSchema,
    temperature: Double, maxTokens: Int
  ): String = {
    writeJson { g =>
      g.writeStringField("anthropic_version", "bedrock-2023-05-31")
      g.writeNumberField("max_tokens", maxTokens)
      g.writeNumberField("temperature", temperature)
      if (systemPrompt.nonEmpty) g.writeStringField("system", systemPrompt)
      // Single synthetic tool from schema
      g.writeArrayFieldStart("tools")
      g.writeStartObject()
      g.writeStringField("name", schema.name)
      g.writeStringField("description", schema.description)
      g.writeFieldName("input_schema")
      g.writeRawValue(schema.jsonSchema)
      g.writeEndObject()
      g.writeEndArray()
      // Force the model to call this tool
      g.writeObjectFieldStart("tool_choice")
      g.writeStringField("type", "tool")
      g.writeStringField("name", schema.name)
      g.writeEndObject()
      // Messages
      g.writeArrayFieldStart("messages")
      for ((role, content) <- messages) {
        g.writeStartObject()
        g.writeStringField("role", role)
        if (isAnthropicStructuredContent(content)) {
          g.writeFieldName("content")
          g.writeRawValue(content)
        } else {
          g.writeStringField("content", content)
        }
        g.writeEndObject()
      }
      g.writeEndArray()
    }
  }

  /** Write a JSON object using Jackson's JsonGenerator, which handles all escaping. */
  def writeJson(body: JsonGenerator => Unit): String = {
    val sw = new StringWriter()
    val gen = jsonFactory.createGenerator(sw)
    gen.writeStartObject()
    body(gen)
    gen.writeEndObject()
    gen.close()
    sw.toString
  }
}
