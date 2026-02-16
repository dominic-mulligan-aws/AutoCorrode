/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

/**
 * Tests for ProofLoop and ProofTextUtil helper methods.
 * After refactoring, most functionality is in ProofTextUtil, so tests reference that.
 */
class ProofLoopTest extends AnyFunSuite with Matchers {

  // Tests now reference ProofTextUtil since ProofLoop delegates to it

  test("extractCode should extract from markdown fences") {
    val response = "Here is the proof:\n```isabelle\nproof (induct x)\n  case 0\n  then show ?case by simp\nnext\n  case (Suc n)\n  then show ?case by simp\nqed\n```"
    val code = ProofTextUtil.extractCode(response)
    code should include("proof (induct x)")
    code should include("qed")
  }

  test("extractCode should find bare proof keywords") {
    val response = "Try this:\nby simp"
    ProofTextUtil.extractCode(response) shouldBe "by simp"
  }

  test("extractCode should return empty for no code") {
    ProofTextUtil.extractCode("No code here at all") shouldBe ""
  }

  test("countSorries should count unfilled sorries") {
    ProofTextUtil.countSorries("sorry") shouldBe 1
    ProofTextUtil.countSorries("sorry sorry sorry") shouldBe 3
    ProofTextUtil.countSorries("proof\n  sorry\nnext\n  sorry\nqed") shouldBe 2
  }

  test("countSorries should not count marked sorries") {
    ProofTextUtil.countSorries("sorry (* unfilled *)") shouldBe 0
    ProofTextUtil.countSorries("sorry (* unfilled *) sorry") shouldBe 1
  }

  test("countSorries should not match sorry inside words") {
    ProofTextUtil.countSorries("notsorry") shouldBe 0
    ProofTextUtil.countSorries("sorrynothing") shouldBe 0
  }

  test("countUnfilled should count unfilled markers") {
    ProofTextUtil.countUnfilled("sorry (* unfilled *)") shouldBe 1
    ProofTextUtil.countUnfilled("sorry (* unfilled *) sorry (* unfilled *)") shouldBe 2
  }

  test("countUnfilled should not count regular sorries") {
    ProofTextUtil.countUnfilled("sorry") shouldBe 0
  }

  test("sorryify should replace by-clauses with sorry") {
    ProofTextUtil.sorryify("by simp") shouldBe "sorry"
    ProofTextUtil.sorryify("by auto") shouldBe "sorry"
  }

  test("sorryify should handle by with parenthesized args") {
    ProofTextUtil.sorryify("by (simp add: foo_def)") shouldBe "sorry"
    ProofTextUtil.sorryify("by (auto intro!: conjI)") shouldBe "sorry"
  }

  test("sorryify should handle multiple by-clauses") {
    val proof = "proof\n  case 0\n  then show ?case by simp\nnext\n  case (Suc n)\n  then show ?case by auto\nqed"
    val result = ProofTextUtil.sorryify(proof)
    result should include("sorry")
    result should not include "by simp"
    result should not include "by auto"
    ProofTextUtil.countSorries(result) shouldBe 2
  }

  test("sorryify should skip by inside cartouches") {
    val proof = """text ‹by example› by simp"""
    val result = ProofTextUtil.sorryify(proof)
    result should include("‹by example›")
  }

  test("sorryify should skip by inside quotes") {
    val proof = """"by example" by auto"""
    ProofTextUtil.sorryify(proof) shouldBe """"by example" sorry"""
  }

  test("isStructurallyComplete should detect qed") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry\nqed") shouldBe true
  }

  test("isStructurallyComplete should detect done") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry\ndone") shouldBe true
  }

  test("isStructurallyComplete should detect by") {
    ProofTextUtil.isStructurallyComplete("by simp") shouldBe true
  }

  test("isStructurallyComplete should reject incomplete") {
    ProofTextUtil.isStructurallyComplete("proof\n  sorry") shouldBe false
    ProofTextUtil.isStructurallyComplete("apply auto") shouldBe false
  }

  test("cleanProofText should strip trailing metadata") {
    ProofTextUtil.cleanProofText("proof\n  sorry\nqed,0,95)") shouldBe "proof\n  sorry\nqed"
  }

  test("cleanProofText should strip leading parens") {
    ProofTextUtil.cleanProofText("(by simp") shouldBe "by simp"
  }

  test("stripGoalRestatement should strip goal line before proof") {
    val code = "mult m (add n p) = add (mult m n) (mult m p)\nproof -\n  sorry\nqed"
    val result = ProofTextUtil.stripGoalRestatement(code)
    result should startWith("proof -")
    result should not include "mult m (add n p)"
  }

  test("stripGoalRestatement should preserve code without goal prefix") {
    val code = "proof -\n  show Q by simp\nqed"
    ProofTextUtil.stripGoalRestatement(code) shouldBe code
  }

  test("extractLemmaStatement should extract statement without proof") {
    val response = """```isabelle
lemma foo: ‹P ⟹ Q›
proof -
  show Q by simp
qed
```"""
    val stmt = ProofTextUtil.extractLemmaStatement(response)
    stmt should include("lemma foo:")
    stmt should not contain "proof"
  }

  test("extractLemmaName should parse lemma name") {
    ProofTextUtil.extractLemmaName("lemma my_lemma: P") shouldBe "my_lemma"
    ProofTextUtil.extractLemmaName("theorem foo_bar [simp]: Q") shouldBe "foo_bar"
  }
}