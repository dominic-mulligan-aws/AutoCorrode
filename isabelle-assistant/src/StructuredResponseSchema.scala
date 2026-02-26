/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Structured response schemas for forced tool_choice.
 * Used with BedrockClient.invokeStructured to guarantee parseable JSON responses.
 */
case class StructuredResponseSchema(
  name: String,
  description: String,
  jsonSchema: String
)

object StructuredResponseSchema {
  /** Schema for planning agent brainstorm phase: generates 3 distinct approaches. */
  val PlanningBrainstorm: StructuredResponseSchema = StructuredResponseSchema(
    name = "brainstorm_approaches",
    description = "Generate three distinct approaches to solve the given problem.",
    jsonSchema = """{
      "type": "object",
      "properties": {
        "approaches": {
          "type": "array",
          "description": "Three distinct approaches to the problem",
          "items": {
            "type": "object",
            "properties": {
              "id": {
                "type": "integer",
                "description": "Approach ID (1, 2, or 3)"
              },
              "title": {
                "type": "string",
                "description": "Short descriptive title for this approach"
              },
              "summary": {
                "type": "string",
                "description": "2-3 sentence summary of the approach"
              },
              "key_idea": {
                "type": "string",
                "description": "The core insight or strategy that makes this approach work"
              },
              "exploration_hints": {
                "type": "array",
                "description": "Hints for what to explore when elaborating this approach",
                "items": { "type": "string" }
              }
            },
            "required": ["id", "title", "summary", "key_idea", "exploration_hints"]
          },
          "minItems": 3,
          "maxItems": 3
        }
      },
      "required": ["approaches"]
    }"""
  )

  /** Schema for planning agent selection phase: picks best approach and produces final plan. */
  val PlanningSelect: StructuredResponseSchema = StructuredResponseSchema(
    name = "select_best_plan",
    description = "Select the best approach from the elaborated plans and produce a final refined plan.",
    jsonSchema = """{
      "type": "object",
      "properties": {
        "selected_approach": {
          "type": "integer",
          "description": "The ID of the selected approach (1, 2, or 3)"
        },
        "reasoning": {
          "type": "string",
          "description": "Explanation of why this approach was selected over the others"
        },
        "plan": {
          "type": "string",
          "description": "The final detailed plan, potentially refined or combining elements from multiple approaches"
        }
      },
      "required": ["selected_approach", "reasoning", "plan"]
    }"""
  )
}