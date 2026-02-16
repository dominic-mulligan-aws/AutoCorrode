/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class SendbackHelperTest extends AnyFunSuite with Matchers {

  test("extractCodeBlocks from markdown") {
    val md = "text\n```isabelle\nby simp\n```\nmore\n```\nby auto\n```"
    val blocks = SendbackHelper.extractCodeBlocks(md)
    blocks should have length 2
    blocks(0) shouldBe "by simp"
    blocks(1) shouldBe "by auto"
  }

  test("extractCodeBlocks empty on no fences") {
    SendbackHelper.extractCodeBlocks("no code here") shouldBe empty
  }

  test("stripCodeFences extracts first block") {
    val md = "```isabelle\nby simp\n```"
    SendbackHelper.stripCodeFences(md) shouldBe "by simp"
  }

  test("stripCodeFences returns original when no fences") {
    SendbackHelper.stripCodeFences("plain text") shouldBe "plain text"
  }
}
