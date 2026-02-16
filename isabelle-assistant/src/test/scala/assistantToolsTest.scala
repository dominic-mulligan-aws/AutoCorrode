/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for AssistantTools input sanitization and tool definitions.
 * Tests the tool definition structure without requiring jEdit runtime.
 */
class AssistantToolsTest extends AnyFunSuite with Matchers {

  test("tool definitions should have unique names") {
    val names = AssistantTools.tools.map(_.name)
    names.distinct.length shouldBe names.length
  }

  test("all tools should have non-empty descriptions") {
    for (tool <- AssistantTools.tools) {
      tool.description should not be empty
    }
  }

  test("required params should have descriptions") {
    for (tool <- AssistantTools.tools; param <- tool.params if param.required) {
      param.description should not be empty
    }
  }

  test("tool param types should be valid JSON schema types") {
    val validTypes = Set("string", "integer", "number", "boolean", "array", "object")
    for (tool <- AssistantTools.tools; param <- tool.params) {
      validTypes should contain(param.typ)
    }
  }

  test("expected tools should be defined") {
    val toolNames = AssistantTools.tools.map(_.name).toSet
    toolNames should contain("read_theory")
    toolNames should contain("list_theories")
    toolNames should contain("search_in_theory")
    toolNames should contain("get_goal_state")
    toolNames should contain("get_proof_context")
    toolNames should contain("find_theorems")
    toolNames should contain("verify_proof")
    toolNames should contain("run_sledgehammer")
  }

  test("read_theory should require theory param") {
    val tool = AssistantTools.tools.find(_.name == "read_theory").get
    val required = tool.params.filter(_.required).map(_.name)
    required should contain("theory")
  }

  test("verify_proof should require proof param") {
    val tool = AssistantTools.tools.find(_.name == "verify_proof").get
    val required = tool.params.filter(_.required).map(_.name)
    required should contain("proof")
  }
}