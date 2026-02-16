/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.BeforeAndAfterAll

/**
 * Tests for LLMResponseCache functionality.
 * Note: True integration tests requiring Isabelle runtime are not included
 * in the automated test suite.
 */
class LLMResponseCacheTest extends AnyFunSuite with Matchers with BeforeAndAfterAll {
  
  test("LLMResponseCache basic operations") {
    LLMResponseCache.clear()
    LLMResponseCache.get("nonexistent") shouldBe None
    LLMResponseCache.put("key", "value")
    LLMResponseCache.get("key") shouldBe Some("value")
    LLMResponseCache.clear()
    LLMResponseCache.get("key") shouldBe None
  }

  test("LLMResponseCache stats") {
    LLMResponseCache.clear()
    val stats = LLMResponseCache.stats
    stats should include("0 entries")
  }
}
