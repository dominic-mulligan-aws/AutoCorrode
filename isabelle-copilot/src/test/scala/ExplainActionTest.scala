/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class ExplainActionTest extends AnyFunSuite with Matchers {

  test("extractName from definition") {
    ExplainAction.extractName("definition foo where") shouldBe Some("foo")
  }

  test("extractName from fun") {
    ExplainAction.extractName("fun bar :: \"nat \\<Rightarrow> nat\" where") shouldBe Some("bar")
  }

  test("extractName from lemma") {
    ExplainAction.extractName("lemma my_lemma:") shouldBe Some("my_lemma")
  }

  test("extractName from theorem") {
    ExplainAction.extractName("theorem important_thm[simp]:") shouldBe Some("important_thm")
  }

  test("extractName from corollary") {
    ExplainAction.extractName("corollary foo_cor:") shouldBe Some("foo_cor")
  }

  test("extractName from datatype") {
    ExplainAction.extractName("datatype 'a tree = Leaf | Node (left: \"'a tree\") (val: 'a) (right: \"'a tree\")") shouldBe Some("tree")
  }

  test("extractName from abbreviation") {
    ExplainAction.extractName("abbreviation my_abbrev where") shouldBe Some("my_abbrev")
  }

  test("extractName from primrec") {
    ExplainAction.extractName("primrec count :: \"nat list \\<Rightarrow> nat\" where") shouldBe Some("count")
  }

  test("extractName with locale qualifier") {
    ExplainAction.extractName("lemma (in my_locale) local_lemma:") shouldBe Some("local_lemma")
  }

  test("extractName with primed identifier") {
    ExplainAction.extractName("definition foo' where") shouldBe Some("foo'")
  }

  test("extractName returns None for non-definition") {
    ExplainAction.extractName("apply auto") shouldBe None
    ExplainAction.extractName("by simp") shouldBe None
    ExplainAction.extractName("") shouldBe None
  }
}