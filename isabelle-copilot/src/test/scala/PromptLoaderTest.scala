/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class PromptLoaderTest extends AnyFunSuite with Matchers {
  
  test("clearCache should not throw") {
    noException should be thrownBy PromptLoader.clearCache()
  }
}
