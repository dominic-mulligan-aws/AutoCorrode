/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Utilities for extracting code blocks from Markdown-formatted LLM responses.
 * Used by actions that need to separate Isabelle code from explanatory text
 * in LLM output (e.g., RefactorAction, TidyAction, ExtractLemmaAction).
 */
object SendbackHelper {
  private val codeBlockPattern = """```(?:isabelle)?\s*\n([\s\S]*?)\n```""".r

  /** Extract all code blocks from markdown-formatted response */
  def extractCodeBlocks(response: String): List[String] =
    codeBlockPattern.findAllMatchIn(response).map(_.group(1).trim).toList

  /** Extract the first code block, stripping fences, or return the original text */
  def stripCodeFences(text: String): String =
    codeBlockPattern.findFirstMatchIn(text).map(_.group(1).trim).getOrElse(text)
}
