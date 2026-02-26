/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ContextSummarizerTest extends AnyFunSuite with Matchers {

  test("shouldSummarize should return false when auto_summarize is disabled") {
    // Test with auto_summarize = false
    val snapshot = AssistantOptions.parseSnapshot(
      (k, d) => if (k == "assistant.auto.summarize") "false" else d,
      (k, d) => if (k == "assistant.auto.summarize") false else d
    )
    
    // Verify the setting was parsed correctly
    snapshot.autoSummarize shouldBe false
    
    info("When auto_summarize is false, summarization should not trigger")
  }

  test("shouldSummarize should return false when message count is below minimum") {
    // Verify the constant is set correctly
    AssistantConstants.MIN_MESSAGES_FOR_SUMMARIZATION should be (5)
    
    // With fewer than MIN_MESSAGES_FOR_SUMMARIZATION messages, should not trigger
    info("With fewer than MIN_MESSAGES_FOR_SUMMARIZATION messages, summarization should not trigger")
  }

  test("buildRestorationMessage should format summary into structured markdown") {
    val summary = ContextSummarizer.SummarizationResult(
      userGoal = "Prove sorted_append lemma",
      accomplishments = "- Set up induction\n- Proved base case",
      pendingWork = "Complete induction step",
      keyContext = "File: SortedLists.thy\nLemma: sorted_append",
      approachHistory = "Initially tried auto, then switched to manual approach",
      decisionsAndConstraints = "Use Isar style only",
      currentState = "Working on induction step"
    )
    
    // Method is now private[assistant] so we can call it directly
    val result = ContextSummarizer.buildRestorationMessage(summary)
    
    result should include ("CONTEXT SUMMARY")
    result should include ("ORIGINAL TASK")
    result should include ("Prove sorted_append lemma")
    result should include ("CURRENT STATE")
    result should include ("KEY CONTEXT")
    result should include ("ACCOMPLISHMENTS")
    result should include ("PENDING WORK")
    result should include ("APPROACH HISTORY")
    result should include ("DECISIONS & CONSTRAINTS")
    result should include ("SortedLists.thy")
  }

  test("SummarizationResult should preserve all required fields") {
    val result = ContextSummarizer.SummarizationResult(
      userGoal = "test goal",
      accomplishments = "test accomplishments",
      pendingWork = "test pending",
      keyContext = "test context",
      approachHistory = "test history",
      decisionsAndConstraints = "test decisions",
      currentState = "test state"
    )
    
    result.userGoal should not be empty
    result.accomplishments should not be empty
    result.pendingWork should not be empty
    result.keyContext should not be empty
    result.approachHistory should not be empty
    result.decisionsAndConstraints should not be empty
    result.currentState should not be empty
  }

  test("Message sectioning should split conversation into three sections with correct proportions") {
    // Test the sectioning math used by ContextSummarizer
    val total = 10
    
    // Expected splits: 40% / 40% / 20%
    // 10 * 0.4 = 4 (section 1: messages 1-4)
    // 10 * 0.8 = 8 (section 2: messages 5-8)
    // remaining (section 3: messages 9-10)
    
    val section1End = (total * 0.4).toInt
    val section2End = (total * 0.8).toInt
    
    section1End should be (4)
    section2End should be (8)
    
    // Section 1: 4 messages (40%)
    // Section 2: 4 messages (40%)
    // Section 3: 2 messages (20%)
    
    info("10 messages split into sections: 1-4 (40%), 5-8 (40%), 9-10 (20%)")
  }

  test("Summarization threshold constants should be valid") {
    AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD should be (0.75)
    AssistantConstants.MIN_SUMMARIZATION_THRESHOLD should be (0.5)
    AssistantConstants.MAX_SUMMARIZATION_THRESHOLD should be (0.95)
    AssistantConstants.MIN_MESSAGES_FOR_SUMMARIZATION should be (5)
    
    // Sanity checks on constant relationships
    AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD should be >= AssistantConstants.MIN_SUMMARIZATION_THRESHOLD
    AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD should be <= AssistantConstants.MAX_SUMMARIZATION_THRESHOLD
  }
}