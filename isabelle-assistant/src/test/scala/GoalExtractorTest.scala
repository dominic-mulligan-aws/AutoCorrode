/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class GoalExtractorTest extends AnyFunSuite with Matchers {

  test("GoalAnalysis should store structured goal information") {
    val analysis = GoalExtractor.GoalAnalysis(
      text = "⊢ P ⟹ Q",
      freeVars = List("x", "y"),
      constants = List("P", "Q"),
      numSubgoals = 1
    )
    
    analysis.text shouldBe "⊢ P ⟹ Q"
    analysis.freeVars should contain theSameElementsAs List("x", "y")
    analysis.constants should contain theSameElementsAs List("P", "Q")
    analysis.numSubgoals shouldBe 1
  }

  test("isInProofContext should detect proof nesting") {
    // Note: This test requires actual PIDE buffer/command structure
    // which isn't available in unit tests. The method is integration-tested
    // via the plugin runtime. We document expected behavior:
    // - Should return true when offset is between proof...qed
    // - Should return false outside proof blocks
    // - Should track nested proof...qed depth correctly
    pending
  }
}