/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class BedrockModelsTest extends AnyFunSuite with Matchers {

  test("applyCrisPrefix adds us. for anthropic") {
    BedrockModels.applyCrisPrefix("anthropic.claude-v2", "us-east-1") shouldBe "us.anthropic.claude-v2"
  }

  test("applyCrisPrefix adds eu. for eu regions") {
    BedrockModels.applyCrisPrefix("anthropic.claude-v2", "eu-west-1") shouldBe "eu.anthropic.claude-v2"
  }

  test("applyCrisPrefix does not double-prefix") {
    BedrockModels.applyCrisPrefix("us.anthropic.claude-v2", "us-east-1") shouldBe "us.anthropic.claude-v2"
    BedrockModels.applyCrisPrefix("global.anthropic.claude-haiku-4-5", "us-east-1") shouldBe "global.anthropic.claude-haiku-4-5"
  }

  test("applyCrisPrefix skips non-CRIS providers") {
    BedrockModels.applyCrisPrefix("amazon.titan-text-express-v1", "us-east-1") shouldBe "amazon.titan-text-express-v1"
  }

  test("applyCrisPrefix handles meta provider") {
    BedrockModels.applyCrisPrefix("meta.llama3-8b-instruct-v1:0", "us-west-2") shouldBe "us.meta.llama3-8b-instruct-v1:0"
  }

  test("applyCrisPrefix handles mistral provider") {
    BedrockModels.applyCrisPrefix("mistral.mistral-large-2402-v1:0", "us-east-1") shouldBe "us.mistral.mistral-large-2402-v1:0"
  }

  test("getModels returns empty when no cache") {
    // This test just verifies the method doesn't throw when cache file doesn't exist
    val models = BedrockModels.getModels
    models should not be null
  }
}
