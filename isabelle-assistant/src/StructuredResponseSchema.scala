/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** Schema for structured output via Anthropic tool_choice forcing.
  * 
  * When sent to the Bedrock API with tool_choice set to force this tool,
  * the model is required to respond with a tool_use block matching this schema.
  * The response is then parsed to extract structured data (e.g., a list of
  * proof suggestions) rather than relying on free-form text parsing.
  * 
  * @param name The synthetic tool name used in the tool_choice directive
  * @param description Tool description sent to the model
  * @param jsonSchema JSON Schema (as a string) defining the input_schema
  */
case class StructuredResponseSchema(
    name: String,
    description: String,
    jsonSchema: String
)