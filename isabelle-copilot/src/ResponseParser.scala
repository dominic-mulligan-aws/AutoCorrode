/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import software.amazon.awssdk.thirdparty.jackson.core.{JsonFactory, JsonToken}

/**
 * Parses JSON responses from different Bedrock model providers.
 * Extracted from BedrockClient for testability and separation of concerns.
 *
 * Handles response formats for: Anthropic (Claude), Meta (Llama), Amazon (Titan),
 * Mistral, and generic models.
 */
object ResponseParser {
  private val jsonFactory = new JsonFactory()

  /**
   * Parse response from Bedrock model using Jackson JSON parser.
   * Throws on empty/unparseable responses so callers don't treat errors as valid text.
   *
   * @param modelId The model identifier (determines which fields to extract)
   * @param json The raw JSON response string
   * @return Extracted text content
   * @throws RuntimeException on empty/unparseable responses
   */
  def parseResponse(modelId: String, json: String): String = {
    if (json == null || json.trim.isEmpty)
      throw new RuntimeException("Empty response from model")

    val parser = jsonFactory.createParser(json)
    try {
      val result = extractTextField(parser, modelId)
      result.getOrElse(throw new RuntimeException(s"Could not parse model response (no text field found)"))
    } catch {
      case e: RuntimeException => throw e
      case ex: Exception =>
        throw new RuntimeException(s"Failed to parse model response: ${ex.getMessage}", ex)
    } finally {
      parser.close()
    }
  }

  /** Extract text content fields from a Bedrock JSON response, collecting all matching blocks. */
  private[copilot] def extractTextField(parser: software.amazon.awssdk.thirdparty.jackson.core.JsonParser, modelId: String): Option[String] = {
    val targetFields = if (PayloadBuilder.isProvider(modelId, "anthropic")) Set("text")
      else if (PayloadBuilder.isProvider(modelId, "meta")) Set("generation")
      else if (PayloadBuilder.isProvider(modelId, "amazon")) Set("outputText")
      else Set("text", "content", "output", "response", "generation")

    val results = scala.collection.mutable.ListBuffer[String]()
    while (parser.nextToken() != null) {
      if (parser.currentToken() == JsonToken.FIELD_NAME && targetFields.contains(parser.currentName())) {
        parser.nextToken()
        if (parser.currentToken() == JsonToken.VALUE_STRING) {
          val value = parser.getValueAsString
          if (value != null && value.nonEmpty) results += value
        }
      }
    }
    if (results.nonEmpty) Some(results.mkString("\n")) else None
  }

  /** Represents a content block in an Anthropic response. */
  enum ContentBlock {
    case TextBlock(text: String)
    case ToolUseBlock(id: String, name: String, input: Map[String, Any])
  }
  export ContentBlock._

  /** Parse Anthropic response content blocks and stop_reason.
   *  Uses a cleaner streaming parser with explicit state tracking.
   *  
   *  State machine:
   *  - Parse top-level fields until we find "content" array or "stop_reason"
   *  - Inside content array, parse each block object
   *  - For tool_use blocks, parse the input object recursively
   */
  def parseAnthropicContentBlocks(json: String): (List[ContentBlock], String) = {
    val parser = jsonFactory.createParser(json)
    val blocks = scala.collection.mutable.ListBuffer[ContentBlock]()
    var stopReason = ""
    
    try {
      // State: toplevel | in_content | in_block | in_input | in_nested
      enum State { case TopLevel, InContent, InBlock, InInput, InNested }
      import State._
      
      var state = TopLevel
      var depth = 0  // Track nesting depth for skipping
      
      // Current block being parsed
      var blockType = ""
      var textVal = ""
      var toolId = ""
      var toolName = ""
      var inputMap = Map.empty[String, Any]
      var nestedJson: java.io.StringWriter = null
      var nestedGen: software.amazon.awssdk.thirdparty.jackson.core.JsonGenerator = null
      var nestedKey = ""
      
      while (parser.nextToken() != null) {
        val token = parser.currentToken()
        
        (state, token) match {
          // Top level: look for "content" and "stop_reason"
          case (TopLevel, JsonToken.FIELD_NAME) =>
            parser.currentName() match {
              case "content" =>
                if (parser.nextToken() == JsonToken.START_ARRAY) state = InContent
              case "stop_reason" =>
                parser.nextToken()
                stopReason = parser.getValueAsString("")
              case _ => // skip
            }
          
          // Inside content array: parse block objects
          case (InContent, JsonToken.START_OBJECT) =>
            state = InBlock
            blockType = ""; textVal = ""; toolId = ""; toolName = ""; inputMap = Map.empty
          
          case (InContent, JsonToken.END_ARRAY) =>
            state = TopLevel
          
          // Inside a content block: extract fields
          case (InBlock, JsonToken.FIELD_NAME) =>
            parser.currentName() match {
              case "type" => parser.nextToken(); blockType = parser.getValueAsString("")
              case "text" => parser.nextToken(); textVal = parser.getValueAsString("")
              case "id" => parser.nextToken(); toolId = parser.getValueAsString("")
              case "name" => parser.nextToken(); toolName = parser.getValueAsString("")
              case "input" =>
                if (parser.nextToken() == JsonToken.START_OBJECT) state = InInput
              case _ => // skip
            }
          
          case (InBlock, JsonToken.END_OBJECT) =>
            // Emit the completed block
            blockType match {
              case "text" if textVal.nonEmpty => blocks += TextBlock(textVal)
              case "tool_use" if toolId.nonEmpty => blocks += ToolUseBlock(toolId, toolName, inputMap)
              case _ => // incomplete block, skip
            }
            state = InContent
          
          // Inside input object: parse key-value pairs
          case (InInput, JsonToken.FIELD_NAME) =>
            val key = parser.currentName()
            val valueToken = parser.nextToken()
            valueToken match {
              case JsonToken.VALUE_STRING => inputMap += (key -> parser.getValueAsString(""))
              case JsonToken.VALUE_NUMBER_INT => inputMap += (key -> parser.getIntValue)
              case JsonToken.VALUE_NUMBER_FLOAT => inputMap += (key -> parser.getDoubleValue)
              case JsonToken.VALUE_TRUE => inputMap += (key -> true)
              case JsonToken.VALUE_FALSE => inputMap += (key -> false)
              case JsonToken.START_OBJECT | JsonToken.START_ARRAY =>
                // Serialize nested structure to JSON string
                nestedKey = key
                nestedJson = new java.io.StringWriter()
                nestedGen = jsonFactory.createGenerator(nestedJson)
                state = InNested
                depth = 1
                if (valueToken == JsonToken.START_OBJECT) nestedGen.writeStartObject()
                else nestedGen.writeStartArray()
              case _ => // null or other, skip
            }
          
          case (InInput, JsonToken.END_OBJECT) =>
            state = InBlock
          
          // Inside nested structure: copy tokens verbatim
          case (InNested, JsonToken.START_OBJECT) =>
            nestedGen.writeStartObject(); depth += 1
          case (InNested, JsonToken.END_OBJECT) =>
            depth -= 1
            nestedGen.writeEndObject()
            if (depth == 0) {
              nestedGen.close()
              inputMap += (nestedKey -> nestedJson.toString)
              state = InInput
            }
          case (InNested, JsonToken.START_ARRAY) =>
            nestedGen.writeStartArray(); depth += 1
          case (InNested, JsonToken.END_ARRAY) =>
            depth -= 1
            nestedGen.writeEndArray()
            if (depth == 0) {
              nestedGen.close()
              inputMap += (nestedKey -> nestedJson.toString)
              state = InInput
            }
          case (InNested, JsonToken.FIELD_NAME) =>
            nestedGen.writeFieldName(parser.currentName())
          case (InNested, JsonToken.VALUE_STRING) =>
            nestedGen.writeString(parser.getValueAsString(""))
          case (InNested, JsonToken.VALUE_NUMBER_INT) =>
            nestedGen.writeNumber(parser.getLongValue)
          case (InNested, JsonToken.VALUE_NUMBER_FLOAT) =>
            nestedGen.writeNumber(parser.getDoubleValue)
          case (InNested, JsonToken.VALUE_TRUE) =>
            nestedGen.writeBoolean(true)
          case (InNested, JsonToken.VALUE_FALSE) =>
            nestedGen.writeBoolean(false)
          case (InNested, JsonToken.VALUE_NULL) =>
            nestedGen.writeNull()
          
          case _ => // Other states/tokens - skip
        }
      }
    } finally {
      parser.close()
    }
    
    (blocks.toList, stopReason)
  }
}
