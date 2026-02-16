/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class SuggestActionTest extends AnyFunSuite with Matchers {
  
  test("parseLLMSuggestions should extract suggestions correctly") {
    val response = """
      Some text before
      SUGGESTION: by simp
      More text
      SUGGESTION: by auto
      SUGGESTION: by (simp add: foo_def)
      Final text
    """
    
    val suggestions = SuggestAction.parseLLMSuggestions(response)
    suggestions should contain theSameElementsAs List(
      "by simp",
      "by auto", 
      "by (simp add: foo_def)"
    )
  }
  
  test("parseLLMSuggestions should handle empty response") {
    val suggestions = SuggestAction.parseLLMSuggestions("")
    suggestions shouldBe empty
  }
  
  test("parseLLMSuggestions should handle malformed suggestions") {
    val response = """
      SUGGESTION:
      SUGGESTION: 
      SUGGESTION: by simp
      Not a suggestion line
    """
    
    val suggestions = SuggestAction.parseLLMSuggestions(response)
    suggestions should contain only "by simp"
  }
  
  test("parseLLMSuggestions should respect max candidates limit") {
    val response = (1 to 10).map(i => s"SUGGESTION: method$i").mkString("\n")
    val suggestions = SuggestAction.parseLLMSuggestions(response)
    suggestions.length should be <= CopilotOptions.getMaxVerifyCandidates
  }
  
  test("rankCandidates should prioritize verified candidates") {
    val candidates = List(
      SuggestAction.Candidate("failed", SuggestAction.LLM, VerificationBadge.Failed("error")),
      SuggestAction.Candidate("verified", SuggestAction.LLM, VerificationBadge.Verified(Some(100L))),
      SuggestAction.Candidate("unverified", SuggestAction.LLM, VerificationBadge.Unverified)
    )
    
    val ranked = SuggestAction.rankCandidates(candidates)
    ranked.head.proof shouldBe "verified"
    ranked.last.proof shouldBe "failed"
  }
}
