/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class TargetParserTest extends AnyFunSuite with Matchers {

  test("parse cursor keywords") {
    TargetParser.parseTarget("cursor", null) shouldBe Some(TargetParser.CurrentCursor)
    TargetParser.parseTarget("current", null) shouldBe Some(TargetParser.CurrentCursor)
  }

  test("parse selection keyword") {
    TargetParser.parseTarget("selection", null) shouldBe Some(TargetParser.CurrentSelection)
  }

  test("parse file:line") {
    TargetParser.parseTarget("Foo.thy:42", null) shouldBe Some(TargetParser.FileLine("Foo.thy", 42))
  }

  test("parse file:range") {
    TargetParser.parseTarget("Foo.thy:10-20", null) shouldBe Some(TargetParser.FileRange("Foo.thy", 10, 20))
  }

  test("parse named element") {
    TargetParser.parseTarget("Foo.thy:my_lemma", null) shouldBe Some(TargetParser.NamedElement("Foo.thy", "my_lemma"))
  }

  test("parse relative position") {
    TargetParser.parseTarget("cursor+5", null) shouldBe Some(TargetParser.RelativePosition(TargetParser.CurrentCursor, 5))
    TargetParser.parseTarget("cursor-3", null) shouldBe Some(TargetParser.RelativePosition(TargetParser.CurrentCursor, -3))
  }

  test("reject invalid target") {
    TargetParser.parseTarget("nonsense", null) shouldBe None
  }

  test("formatTarget round-trips") {
    val targets = List(
      TargetParser.CurrentCursor,
      TargetParser.CurrentSelection,
      TargetParser.FileLine("T.thy", 5),
      TargetParser.FileRange("T.thy", 1, 10)
    )
    for (t <- targets) {
      TargetParser.formatTarget(t) should not be empty
    }
  }
}
