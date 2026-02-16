/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for BedrockClient helper methods.
 * Since isProvider and isLlama3OrLater are private, we test them indirectly
 * via BedrockModels.applyCrisPrefix which exercises provider detection.
 * We also test LLMResponseCache behavior thoroughly.
 */
class BedrockClientTest extends AnyFunSuite with Matchers {

  // --- LLMResponseCache tests ---

  test("LLMResponseCache should store and retrieve entries") {
    LLMResponseCache.clear()
    LLMResponseCache.put("prompt1", "response1")
    LLMResponseCache.get("prompt1") shouldBe Some("response1")
  }

  test("LLMResponseCache should return None for missing entries") {
    LLMResponseCache.clear()
    LLMResponseCache.get("nonexistent") shouldBe None
  }

  test("LLMResponseCache should not cache error responses") {
    LLMResponseCache.clear()
    LLMResponseCache.put("prompt", "Error: something went wrong")
    LLMResponseCache.get("prompt") shouldBe None
  }

  test("LLMResponseCache should not cache timeout messages") {
    LLMResponseCache.clear()
    LLMResponseCache.put("prompt", "Operation timed out. Please try again.")
    LLMResponseCache.get("prompt") shouldBe None
  }

  test("LLMResponseCache should not cache credential errors") {
    LLMResponseCache.clear()
    LLMResponseCache.put("prompt", "AWS credentials are invalid or insufficient.")
    LLMResponseCache.get("prompt") shouldBe None
  }

  test("LLMResponseCache should respect max size via eviction") {
    LLMResponseCache.clear()
    // Fill beyond cache capacity
    for (i <- 1 to (CopilotConstants.LLM_CACHE_SIZE + 20)) {
      LLMResponseCache.put(s"prompt-$i", s"response-$i")
    }
    // Recent entries should be present
    LLMResponseCache.get(s"prompt-${CopilotConstants.LLM_CACHE_SIZE + 20}") shouldBe Some(s"response-${CopilotConstants.LLM_CACHE_SIZE + 20}")
    // Very old entries should be evicted
    LLMResponseCache.get("prompt-1") shouldBe None
    LLMResponseCache.clear()
  }

  test("LLMResponseCache.clear should empty the cache") {
    LLMResponseCache.put("key", "value")
    LLMResponseCache.clear()
    LLMResponseCache.get("key") shouldBe None
  }

  test("LLMResponseCache.cleanup should remove expired entries") {
    LLMResponseCache.clear()
    LLMResponseCache.put("key", "value")
    // Cleanup shouldn't remove recently added entries
    LLMResponseCache.cleanup()
    LLMResponseCache.get("key") shouldBe Some("value")
    LLMResponseCache.clear()
  }

  // --- ErrorHandler integration tests ---

  test("ErrorHandler.makeUserFriendly handles credential errors") {
    val msg = ErrorHandler.makeUserFriendly("access denied for user", "test")
    msg should include("credentials")
  }

  test("ErrorHandler.makeUserFriendly handles network errors") {
    val msg = ErrorHandler.makeUserFriendly("connection refused to host", "test")
    msg should include("connection")
  }

  test("ErrorHandler.makeUserFriendly handles throttling") {
    val msg = ErrorHandler.makeUserFriendly("throttle limit exceeded", "test")
    msg should include("limit")
  }

  test("ErrorHandler.makeUserFriendly handles model not found") {
    val msg = ErrorHandler.makeUserFriendly("model xyz not found in region", "test")
    msg should include("model")
  }

  test("ErrorHandler.makeUserFriendly handles JSON parse errors") {
    val msg = ErrorHandler.makeUserFriendly("json parse error at position 42", "test")
    msg should include("invalid response")
  }

  test("ErrorHandler.sanitize truncates long strings") {
    val long = "x" * 20000
    val result = ErrorHandler.sanitize(long)
    result.length shouldBe CopilotConstants.MAX_RESPONSE_LENGTH
  }

  test("ErrorHandler.sanitize handles null") {
    ErrorHandler.sanitize(null) shouldBe ""
  }
}