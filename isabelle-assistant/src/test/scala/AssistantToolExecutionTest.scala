/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.BeforeAndAfterEach
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.util.concurrent.atomic.AtomicInteger

class AssistantToolExecutionTest
    extends AnyFunSuite
    with Matchers
    with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    super.beforeEach()
    ToolPermissions.clearSession()
    ToolPermissions.resetToDefaults()
  }

  test("executeTool should return clear error for unknown tool") {
    AssistantTools.executeTool("definitely_unknown_tool", Map.empty, null) shouldBe
      "Unknown tool: definitely_unknown_tool"
  }

  test("executeTool should validate edit_theory arguments before any file operations") {
    AssistantTools.executeTool("edit_theory", Map.empty, null) shouldBe
      "Error: theory name required"
  }

  test("executeTool should validate set_cursor_position arguments before touching view state") {
    AssistantTools.executeTool(
      "set_cursor_position",
      Map("line" -> ResponseParser.IntValue(-1)),
      null
    ) shouldBe "Error: line must be a positive integer"
  }

  test("executeToolWithPermission should deny tools configured as Deny") {
    ToolPermissions.setConfiguredLevel("edit_theory", ToolPermissions.Deny)
    AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
      "Permission denied: tool 'edit_theory' is not allowed."
  }

  test("executeToolWithPermission should respect user denial from prompt") {
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => Some("Deny (for this session)")) {
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Permission denied: user declined tool 'edit_theory'."
    }
  }

  test("AskAlways tools should prompt on every invocation") {
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Allow Once")
    }) {
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Error: theory name required"
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Error: theory name required"
    }
    prompts.get shouldBe 2
  }

  test("AskAtFirstUse tools should prompt once when session-allowed") {
    ToolPermissions.setConfiguredLevel("edit_theory", ToolPermissions.AskAtFirstUse)
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Allow (for this session)")
    }) {
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Error: theory name required"
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Error: theory name required"
    }
    prompts.get shouldBe 1
  }

  test("AskAtFirstUse tools denied for session should not re-prompt") {
    ToolPermissions.setConfiguredLevel("edit_theory", ToolPermissions.AskAtFirstUse)
    val prompts = new AtomicInteger(0)
    ToolPermissions.withPromptChoicesForTest((_, _, _, _) => {
      prompts.incrementAndGet()
      Some("Deny (for this session)")
    }) {
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Permission denied: user declined tool 'edit_theory'."
      AssistantTools.executeToolWithPermission("edit_theory", Map.empty, null) shouldBe
        "Permission denied: tool 'edit_theory' is not allowed."
    }
    prompts.get shouldBe 1
  }
}

