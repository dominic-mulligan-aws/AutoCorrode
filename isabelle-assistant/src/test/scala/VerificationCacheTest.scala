/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class VerificationCacheTest extends AnyFunSuite with Matchers {
  
  test("cache clear should reset size to zero") {
    VerificationCache.clear()
    VerificationCache.size shouldBe 0
  }
  
  test("cache should provide stats") {
    VerificationCache.clear()
    val stats = VerificationCache.stats
    stats should include("0")
    stats should include("entries")
  }
}
