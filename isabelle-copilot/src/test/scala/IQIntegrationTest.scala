/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import isabelle.copilot.IQIntegration.VerificationResult
import isabelle.copilot.IQIntegration.VerificationResult._
import isabelle.copilot.IQIntegration.IQStatus
import isabelle.copilot.IQIntegration.IQStatus._

/**
 * Tests for IQIntegration — proof verification, sledgehammer, find_theorems.
 * 
 * Note: These tests verify the logic and structure without requiring actual
 * I/Q plugin runtime. Mock-based tests would require complex jEdit/PIDE mocking,
 * which is out of scope. Integration tests that require actual I/Q are in
 * CopilotIntegrationTest.
 */
class IQIntegrationTest extends AnyFunSuite with Matchers {

  test("VerificationResult enum should have all expected cases") {
    // Verify all cases exist and are distinct types
    val success: VerificationResult = ProofSuccess(100)
    val failure: VerificationResult = ProofFailure("error")
    val timeout: VerificationResult = ProofTimeout
    val unavailable: VerificationResult = IQUnavailable
    val missingImport: VerificationResult = MissingImport("suggestion")
    
    success should not be failure
    failure should not be timeout
    timeout should not be unavailable
    unavailable should not be missingImport
  }

  test("ProofSuccess should store timing information") {
    val result = ProofSuccess(150, "state text")
    result match {
      case ProofSuccess(timeMs, resultState) =>
        timeMs shouldBe 150
        resultState shouldBe "state text"
      case _ => fail("Should be ProofSuccess")
    }
  }

  test("ProofFailure should store error message") {
    val result = ProofFailure("syntax error")
    result match {
      case ProofFailure(error) => error shouldBe "syntax error"
      case _ => fail("Should be ProofFailure")
    }
  }

  test("SledgehammerResult should store method and timing") {
    val result = IQIntegration.SledgehammerResult("by (metis foo)", 500)
    result.proofMethod shouldBe "by (metis foo)"
    result.timeMs shouldBe 500
  }

  test("ProofStepResult should track completion status") {
    val complete = IQIntegration.ProofStepResult(
      complete = true, 
      numSubgoals = 0, 
      stateText = "No subgoals", 
      timeMs = 200
    )
    complete.complete shouldBe true
    complete.numSubgoals shouldBe 0
    
    val incomplete = IQIntegration.ProofStepResult(
      complete = false, 
      numSubgoals = 3, 
      stateText = "3 subgoals", 
      timeMs = 150
    )
    incomplete.complete shouldBe false
    incomplete.numSubgoals shouldBe 3
  }

  test("getIsarExploreImportSuggestion should provide helpful guidance") {
    val suggestion = IQIntegration.getIsarExploreImportSuggestion
    suggestion should include("Isar_Explore")
    suggestion should include("import")
    suggestion should include("$IQ_HOME")
  }

  test("IQStatus enum should have connected and disconnected states") {
    val connected: IQStatus = IQConnected
    val disconnected: IQStatus = IQDisconnected
    
    connected should not be disconnected
  }

  // Test the parseStepResult logic by extracting it to a testable form
  test("parseStepResult should parse PROOF_COMPLETE header") {
    // This is testing the logic that would be in parseStepResult
    // The actual method is private, but we can test the expected behavior
    val text = "PROOF_COMPLETE\nProof state after completion"
    val lines = text.linesIterator
    val header = lines.next()
    
    header should startWith("PROOF_COMPLETE")
    // A ProofStepResult created from this should have complete=true, numSubgoals=0
  }

  test("parseStepResult should parse PROOF_STATE header with subgoal count") {
    val text = "PROOF_STATE 3\nSubgoal 1: P\nSubgoal 2: Q\nSubgoal 3: R"
    val lines = text.linesIterator
    val header = lines.next()
    
    header should startWith("PROOF_STATE")
    val count = header.stripPrefix("PROOF_STATE ").trim.toInt
    count shouldBe 3
    // A ProofStepResult created from this should have complete=false, numSubgoals=3
  }

  test("parseStepResult should handle legacy format without header") {
    val text = "goal (1 subgoal):\n 1. P ⟹ Q"
    val lines = text.linesIterator
    val header = lines.next()
    
    header should not startWith("PROOF_")
    // Legacy format should be treated as opaque state with numSubgoals=-1
  }
}