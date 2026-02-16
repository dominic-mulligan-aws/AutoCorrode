/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

/**
 * Type aliases for stringly-typed values throughout Isabelle Copilot.
 * 
 * These aliases improve type safety by distinguishing between different
 * string "roles" in the type system. While Scala doesn't enforce newtype
 * semantics, these aliases serve as documentation and enable future
 * migration to opaque types or value classes if needed.
 * 
 * Usage guidelines:
 * - Use these aliases in public API signatures
 * - Internal functions may use String for brevity
 * - Consider using opaque types in Scala 3 for stronger guarantees
 */
object CopilotTypes {
  /** AWS Bedrock model identifier (e.g., "anthropic.claude-3-sonnet-20240229-v1:0"). */
  type ModelId = String
  
  /** AWS region identifier (e.g., "us-east-1"). */
  type Region = String
  
  /** Complete prompt text sent to LLM. */
  type PromptText = String
  
  /** Isabelle proof text (e.g., "by simp", "proof ... qed"). */
  type ProofText = String
  
  /** Isabelle command source text (e.g., "lemma foo: P"). */
  type CommandText = String
  
  /** Goal state text from PIDE output panel. */
  type GoalState = String
  
  /** Error message text. */
  type ErrorMessage = String
  
  /** LLM response text. */
  type ResponseText = String
  
  /** Theory file name (e.g., "Foo.thy"). */
  type TheoryName = String
  
  /** Lemma or theorem name identifier. */
  type LemmaName = String
  
  /** JSON payload string for API requests. */
  type JsonPayload = String
  
  /** Markdown-formatted text for chat display. */
  type MarkdownText = String
  
  /** HTML-formatted text for rendering. */
  type HtmlText = String
}