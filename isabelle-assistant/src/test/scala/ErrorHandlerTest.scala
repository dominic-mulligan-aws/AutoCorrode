/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ErrorHandlerTest extends AnyFunSuite with Matchers {
  
  test("validateInput should reject null input") {
    ErrorHandler.validateInput(null).isFailure shouldBe true
  }
  
  test("validateInput should reject empty input") {
    ErrorHandler.validateInput("").isFailure shouldBe true
  }
  
  test("validateInput should accept valid input") {
    ErrorHandler.validateInput("valid input").isSuccess shouldBe true
  }
  
  test("makeUserFriendly should convert timeout errors") {
    val result = ErrorHandler.makeUserFriendly("operation timed out", "test")
    result should include("timed out")
  }

  test("makeUserFriendly should handle null message") {
    val result = ErrorHandler.makeUserFriendly(null, "test")
    result should include("Unknown error")
  }

  test("truncateError should handle long messages") {
    val long = "x" * 1000
    val result = ErrorHandler.truncateError(long)
    result.length should be <= (AssistantConstants.MAX_ERROR_MESSAGE_LENGTH + 3)
  }
}
