/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for SuggestAction.parseLLMSuggestions and rankCandidates.
 * These are pure functions that don't require jEdit runtime.
 */
class SuggestActionParserTest extends AnyFunSuite with Matchers {

  // --- parseLLMSuggestions ---

  test("parseLLMSuggestions should parse SUGGESTION: format") {
    val response = """Here are some suggestions:
      |SUGGESTION: by simp
      |SUGGESTION: by auto
      |SUGGESTION: by blast""".stripMargin
    val result = SuggestAction.parseLLMSuggestions(response)
    result should contain("by simp")
    result should contain("by auto")
    result should contain("by blast")
    result should have length 3
  }

  test("parseLLMSuggestions should handle extra whitespace in SUGGESTION: lines") {
    val response = "SUGGESTION:   by (simp add: foo_def)  "
    val result = SuggestAction.parseLLMSuggestions(response)
    result should contain("by (simp add: foo_def)")
  }

  test("parseLLMSuggestions should fall back to numbered list") {
    val response = """Here are some options:
      |1. by simp
      |2. by auto
      |3. by blast""".stripMargin
    val result = SuggestAction.parseLLMSuggestions(response)
    result should contain("by simp")
    result should contain("by auto")
    result should contain("by blast")
  }

  test("parseLLMSuggestions should fall back to markdown code blocks") {
    val response = "Try this:\n```isabelle\nby simp\n```"
    val result = SuggestAction.parseLLMSuggestions(response)
    result should contain("by simp")
  }

  test("parseLLMSuggestions should deduplicate suggestions") {
    val response = """SUGGESTION: by simp
      |SUGGESTION: by simp
      |SUGGESTION: by auto""".stripMargin
    val result = SuggestAction.parseLLMSuggestions(response)
    result.count(_ == "by simp") shouldBe 1
    result should have length 2
  }

  test("parseLLMSuggestions should return empty for no recognizable suggestions") {
    val response = "I'm not sure how to proceed with this goal."
    SuggestAction.parseLLMSuggestions(response) shouldBe empty
  }

  test("parseLLMSuggestions should filter non-proof items from numbered lists") {
    val response = """1. by simp
      |2. This is not a proof method
      |3. by auto""".stripMargin
    val result = SuggestAction.parseLLMSuggestions(response)
    result should contain("by simp")
    result should contain("by auto")
    result should not contain "This is not a proof method"
  }

  // --- rankCandidates ---

  test("rankCandidates should sort Verified before Unverified") {
    val candidates = List(
      SuggestAction.Candidate("by auto", SuggestAction.LLM, VerificationBadge.Unverified),
      SuggestAction.Candidate("by simp", SuggestAction.LLM, VerificationBadge.Verified(Some(100)))
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by simp"
  }

  test("rankCandidates should sort Sledgehammer before Unverified but after Verified") {
    val candidates = List(
      SuggestAction.Candidate("by auto", SuggestAction.LLM, VerificationBadge.Unverified),
      SuggestAction.Candidate("by smt", SuggestAction.Sledgehammer, VerificationBadge.Sledgehammer(Some(500))),
      SuggestAction.Candidate("by simp", SuggestAction.LLM, VerificationBadge.Verified(Some(100)))
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked(0).proof shouldBe "by simp"
    ranked(1).proof shouldBe "by smt"
    ranked(2).proof shouldBe "by auto"
  }

  test("rankCandidates should sort Failed last") {
    val candidates = List(
      SuggestAction.Candidate("by fail", SuggestAction.LLM, VerificationBadge.Failed("type error")),
      SuggestAction.Candidate("by auto", SuggestAction.LLM, VerificationBadge.Unverified)
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by auto"
    ranked.last.proof shouldBe "by fail"
  }

  test("rankCandidates should sort by time within same badge type") {
    val candidates = List(
      SuggestAction.Candidate("by auto", SuggestAction.LLM, VerificationBadge.Verified(Some(500)), timeMs = Some(500)),
      SuggestAction.Candidate("by simp", SuggestAction.LLM, VerificationBadge.Verified(Some(100)), timeMs = Some(100))
    )
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "by simp" // faster
  }
}