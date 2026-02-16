/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{ConcurrentLinkedQueue, CountDownLatch, TimeUnit}
import scala.jdk.CollectionConverters._

/**
 * Generates proof skeletons via parallel LLM calls.
 * Skeletons are maximally-sorry proofs with correct structure but unfilled leaves.
 */
object SketchGenerator {

  private def chat(msg: String): Unit =
    GUI_Thread.later { ChatAction.addTransient(msg) }

  /**
   * Generate N proof skeletons in parallel and return the first structurally valid one.
   * 
   * @param view jEdit view
   * @param command Isabelle command for verification
   * @param commandText The lemma statement
   * @param goalState The initial goal state
   * @param context Available definitions and theorems
   * @param plan Informal proof plan (optional)
   * @param deadline Wall-clock deadline for generation
   * @return Some(skeleton) with all by-clauses replaced by sorry, or None
   */
  def generateSkeleton(
    view: View,
    command: Command,
    commandText: String,
    goalState: String,
    context: String,
    plan: String,
    deadline: Long
  ): Option[String] = {
    val numBranches = AssistantOptions.getProveBranches
    chat(s"## Phase 1: Skeleton\nGenerating $numBranches proof skeletons...")

    val sketches = new ConcurrentLinkedQueue[String]()
    val latch = new CountDownLatch(numBranches)
    
    for (i <- 1 to numBranches) {
      Isabelle_Thread.fork(name = s"prove-sketch-$i") {
        try {
          val subs = scala.collection.mutable.Map(
            "goal_state" -> goalState, 
            "command" -> commandText
          )
          if (context.nonEmpty) subs("relevant_theorems") = context
          if (plan.nonEmpty) subs("proof_plan") = plan
          
          val latch = new CountDownLatch(1)
          @volatile var response: Option[String] = None
          
          Isabelle_Thread.fork(name = s"sketch-llm-$i") {
            try {
              response = Some(BedrockClient.invokeNoCache(
                PromptLoader.load("prove_sketch.md", subs.toMap)))
            } catch { 
              case _: Exception => 
            } finally {
              latch.countDown()
            }
          }
          
          latch.await(AssistantConstants.PROVE_LLM_CALL_TIMEOUT, TimeUnit.MILLISECONDS)
          response.foreach { r =>
            val code = ProofTextUtil.extractCode(r)
            Output.writeln(s"[Assistant] sketch-$i extractCode result (${code.length} chars): <<<$code>>>")
            if (code.nonEmpty) sketches.add(code)
          }
        } catch { 
          case _: Exception => 
        } finally {
          latch.countDown()
        }
      }
    }
    
    latch.await(90, TimeUnit.SECONDS)
    val all = sketches.asScala.toList

    if (all.isEmpty) {
      chat("No skeletons generated")
      return None
    }

    for ((s, i) <- all.zipWithIndex)
      chat(s"**Skeleton ${i + 1}** (${s.linesIterator.size} lines, ${ProofTextUtil.countSorries(s)} sorries):\n```isabelle\n$s\n```")

    chat(s"Checking ${all.length} skeleton structures via I/Q...")
    
    all.find { sketch =>
      if (!ProofTextUtil.isStructurallyComplete(sketch)) {
        chat(s"  [FAIL] Skeleton not structurally complete (no qed/done)")
        false
      } else {
        val sorried = ProofTextUtil.sorryify(sketch)
        val sorryCount = ProofTextUtil.countSorries(sorried)
        if (sorryCount == 0) {
          chat(s"  [FAIL] Skeleton has no sorry placeholders to fill")
          false
        } else {
          // Verify skeleton via I/Q
          val iqResult = IQExecutor.executeStep(view, command, sorried)
          iqResult match {
            case Right(_) =>
              chat(s"  [ok] I/Q verified, $sorryCount sorries to fill")
              true
            case Left(err) =>
              chat(s"  [FAIL] I/Q rejected skeleton: $err")
              false
          }
        }
      }
    }.map { sketch =>
      val sorried = ProofTextUtil.sorryify(sketch)
      chat(s"**Skeleton accepted** (${ProofTextUtil.countSorries(sorried)} sorries to fill)")
      sorried
    }
  }
}