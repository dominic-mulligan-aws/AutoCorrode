/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers


/**
 * Tests for AssistantOptions pure parsing and key resolution helpers.
 */
class AssistantOptionsTest extends AnyFunSuite with Matchers {

  private def parse(
    props: Map[String, String] = Map.empty,
    bools: Map[String, Boolean] = Map.empty
  ): AssistantOptions.SettingsSnapshot =
    AssistantOptions.parseSnapshot(
      (k, d) => props.getOrElse(k, d),
      (k, d) => bools.getOrElse(k, d)
    )

  test("normalizeKey should lowercase and convert hyphens to underscores") {
    AssistantOptions.normalizeKeyForTest("VERIFY-TIMEOUT") shouldBe "verify_timeout"
    AssistantOptions.normalizeKeyForTest("Max_Tokens") shouldBe "max_tokens"
  }

  test("known settings and aliases should resolve") {
    AssistantOptions.hasSettingKey("region") shouldBe true
    AssistantOptions.hasSettingKey("verify-timeout") shouldBe true
    AssistantOptions.hasSettingKey("use_cris") shouldBe true
    AssistantOptions.hasSettingKey("sledgehammer") shouldBe true
    AssistantOptions.hasSettingKey("does_not_exist") shouldBe false
  }

  test("parseSnapshot should sanitize invalid region/model values") {
    val snapshot = parse(Map(
      "assistant.aws.region" -> "!!!",
      "assistant.model.id" -> "bad model id with spaces"
    ))
    snapshot.region shouldBe "us-east-1"
    snapshot.baseModelId shouldBe ""
  }

  test("parseSnapshot should reject non-Anthropic model IDs") {
    val snapshot = parse(Map("assistant.model.id" -> "meta.llama3-70b-instruct-v1:0"))
    snapshot.baseModelId shouldBe ""
  }

  test("parseSnapshot should accept valid Anthropic model IDs") {
    val snapshot = parse(Map("assistant.model.id" -> "anthropic.claude-3-7-sonnet-20250219-v1:0"))
    snapshot.baseModelId shouldBe "anthropic.claude-3-7-sonnet-20250219-v1:0"
  }

  test("parseSnapshot should clamp numeric values to configured bounds") {
    val snapshot = parse(Map(
      "assistant.temperature" -> "-1.0",
      "assistant.max.tokens" -> "99999999",
      "assistant.trace.depth" -> "0",
      "assistant.verify.timeout" -> "1"
    ))
    snapshot.temperature shouldBe AssistantConstants.MIN_TEMPERATURE
    snapshot.maxTokens shouldBe 99999999 // No upper clamp - supports large token counts
    snapshot.traceDepth shouldBe 1
    snapshot.verifyTimeout shouldBe 5000L
  }

  test("parseSnapshot should fall back to defaults for non-numeric values") {
    val snapshot = parse(Map(
      "assistant.temperature" -> "not-a-number",
      "assistant.max.tokens" -> "nan",
      "assistant.trace.timeout" -> "oops"
    ))
    snapshot.temperature shouldBe AssistantConstants.DEFAULT_TEMPERATURE
    snapshot.maxTokens shouldBe AssistantConstants.DEFAULT_MAX_TOKENS
    snapshot.traceTimeout shouldBe AssistantConstants.DEFAULT_TRACE_TIMEOUT
  }

  test("parseSnapshot should honor boolean flags and defaults") {
    val defaults = parse()
    defaults.useCris shouldBe true
    defaults.verifySuggestions shouldBe true
    defaults.useSledgehammer shouldBe false

    val overridden = parse(
      bools = Map(
        "assistant.use.cris" -> false,
        "assistant.verify.suggestions" -> false,
        "assistant.use.sledgehammer" -> true
      )
    )
    overridden.useCris shouldBe false
    overridden.verifySuggestions shouldBe false
    overridden.useSledgehammer shouldBe true
  }

  test("parseSnapshot should default maxToolIterations to configured default") {
    val defaults = parse()
    defaults.maxToolIterations shouldBe Some(AssistantConstants.DEFAULT_MAX_TOOL_ITERATIONS)
  }

  test("parseSnapshot should parse valid maxToolIterations values") {
    val withLimit = parse(Map("assistant.max.tool.iterations" -> "25"))
    withLimit.maxToolIterations shouldBe Some(25)
  }

  test("parseSnapshot should treat empty/0/none/unlimited as unlimited") {
    parse(Map("assistant.max.tool.iterations" -> "")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "0")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "none")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "unlimited")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "UNLIMITED")).maxToolIterations shouldBe None
  }

  test("parseSnapshot should clamp maxToolIterations to valid range") {
    parse(Map("assistant.max.tool.iterations" -> "100")).maxToolIterations shouldBe None
    parse(Map("assistant.max.tool.iterations" -> "-5")).maxToolIterations shouldBe None
  }

  test("parseSnapshot should accept valid planning model ID") {
    val snapshot = parse(Map("assistant.planning.model.id" -> "anthropic.claude-3-haiku-20240307-v1:0"))
    snapshot.planningBaseModelId shouldBe "anthropic.claude-3-haiku-20240307-v1:0"
  }

  test("parseSnapshot should reject invalid planning model ID") {
    val snapshot = parse(Map("assistant.planning.model.id" -> "meta.llama3-8b-instruct-v1:0"))
    snapshot.planningBaseModelId shouldBe ""
  }

  test("parseSnapshot should allow empty planning model ID (use main model)") {
    val snapshot = parse(Map("assistant.planning.model.id" -> ""))
    snapshot.planningBaseModelId shouldBe ""
  }

  test("parseSnapshot should parse valid planning temperature") {
    val snapshot = parse(Map("assistant.planning.temperature" -> "0.5"))
    snapshot.planningTemperature shouldBe Some(0.5)
  }

  test("parseSnapshot should treat empty planning temperature as None") {
    val snapshot = parse(Map("assistant.planning.temperature" -> ""))
    snapshot.planningTemperature shouldBe None
  }

  test("parseSnapshot should reject out-of-range planning temperature") {
    val snapshot1 = parse(Map("assistant.planning.temperature" -> "1.5"))
    snapshot1.planningTemperature shouldBe None
    
    val snapshot2 = parse(Map("assistant.planning.temperature" -> "-0.5"))
    snapshot2.planningTemperature shouldBe None
  }

  test("parseSnapshot should reject invalid planning temperature string") {
    val snapshot = parse(Map("assistant.planning.temperature" -> "not-a-number"))
    snapshot.planningTemperature shouldBe None
  }

  test("planning_model and planning_temperature should be in settingDefs") {
    AssistantOptions.hasSettingKey("planning_model") shouldBe true
    AssistantOptions.hasSettingKey("planning_temperature") shouldBe true
  }

  test("parseSnapshot should accept valid summarization model ID") {
    val snapshot = parse(Map("assistant.summarization.model.id" -> "anthropic.claude-3-5-haiku-20241022-v1:0"))
    snapshot.summarizationBaseModelId shouldBe "anthropic.claude-3-5-haiku-20241022-v1:0"
  }

  test("parseSnapshot should reject invalid summarization model ID") {
    val snapshot = parse(Map("assistant.summarization.model.id" -> "meta.llama3-8b-instruct-v1:0"))
    snapshot.summarizationBaseModelId shouldBe ""
  }

  test("parseSnapshot should allow empty summarization model ID (use main model)") {
    val snapshot = parse(Map("assistant.summarization.model.id" -> ""))
    snapshot.summarizationBaseModelId shouldBe ""
  }

  test("parseSnapshot should parse valid summarization temperature") {
    val snapshot = parse(Map("assistant.summarization.temperature" -> "0.0"))
    snapshot.summarizationTemperature shouldBe Some(0.0)
  }

  test("parseSnapshot should treat empty summarization temperature as None") {
    val snapshot = parse(Map("assistant.summarization.temperature" -> ""))
    snapshot.summarizationTemperature shouldBe None
  }

  test("parseSnapshot should reject out-of-range summarization temperature") {
    val snapshot1 = parse(Map("assistant.summarization.temperature" -> "1.5"))
    snapshot1.summarizationTemperature shouldBe None
    
    val snapshot2 = parse(Map("assistant.summarization.temperature" -> "-0.5"))
    snapshot2.summarizationTemperature shouldBe None
  }

  test("parseSnapshot should parse autoSummarize boolean") {
    val defaults = parse()
    defaults.autoSummarize shouldBe true

    val disabled = parse(bools = Map("assistant.auto.summarize" -> false))
    disabled.autoSummarize shouldBe false
  }

  test("parseSnapshot should parse and clamp summarization threshold") {
    val defaults = parse()
    defaults.summarizationThreshold shouldBe AssistantConstants.DEFAULT_SUMMARIZATION_THRESHOLD

    val valid = parse(Map("assistant.summarization.threshold" -> "0.8"))
    valid.summarizationThreshold shouldBe 0.8

    val tooHigh = parse(Map("assistant.summarization.threshold" -> "1.5"))
    tooHigh.summarizationThreshold shouldBe AssistantConstants.MAX_SUMMARIZATION_THRESHOLD

    val tooLow = parse(Map("assistant.summarization.threshold" -> "0.3"))
    tooLow.summarizationThreshold shouldBe AssistantConstants.MIN_SUMMARIZATION_THRESHOLD
  }

  test("summarization settings should be in settingDefs") {
    AssistantOptions.hasSettingKey("auto_summarize") shouldBe true
    AssistantOptions.hasSettingKey("summarization_threshold") shouldBe true
    AssistantOptions.hasSettingKey("summarization_model") shouldBe true
    AssistantOptions.hasSettingKey("summarization_temperature") shouldBe true
  }
}
