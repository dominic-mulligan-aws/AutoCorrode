/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}

/**
 * Proof planning module for the autonomous prover.
 * Analyzes goals, fetches relevant context, and generates informal proof plans
 * that guide subsequent skeleton generation and filling phases.
 */
object ProofPlanner {

  /**
   * Create an informal proof plan by analyzing the goal, definitions, and available lemmas.
   * The plan is fed into all subsequent phases to guide skeleton generation, fill, and refinement.
   */
  def createProofPlan(commandText: String, goalState: String, context: String): String = {
    if (commandText.isEmpty && goalState.isEmpty) return ""
    
    val chat = (msg: String) => GUI_Thread.later { ChatAction.addTransient(msg) }
    chat("## Proof Planning\nAnalyzing goal and available context...")
    
    try {
      val subs = scala.collection.mutable.Map(
        "goal_state" -> goalState,
        "command" -> commandText
      )
      if (context.nonEmpty) subs("relevant_theorems") = context
      
      val latch = new CountDownLatch(1)
      @volatile var planResult: Either[Exception, String] = Left(new RuntimeException("timeout"))
      
      Isabelle_Thread.fork(name = "proof-plan") {
        try {
          val plan = BedrockClient.invokeNoCache(PromptLoader.load("prove_plan.md", subs.toMap))
          planResult = Right(plan)
        } catch { 
          case ex: Exception => planResult = Left(ex) 
        } finally { 
          latch.countDown() 
        }
      }
      
      latch.await(CopilotConstants.PROVE_LLM_CALL_TIMEOUT, TimeUnit.MILLISECONDS)
      
      planResult match {
        case Right(plan) =>
          Output.writeln(s"[Copilot] Proof plan:\n$plan")
          plan
        case Left(ex) =>
          Output.writeln(s"[Copilot] Proof planning failed: ${ex.getMessage}")
          chat("Planning failed, proceeding without plan")
          ""
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"[Copilot] Proof planning failed: ${ex.getMessage}")
        chat("Planning failed, proceeding without plan")
        ""
    }
  }

  /**
   * Fetch rich context for the auto-prover including:
   * 1. Local proof facts (from print_context)
   * 2. PIDE entity definitions (from ContextFetcher)
   * 3. Relevant theorems via find_theorems for goal constants
   * 4. Datatype and function definitions from the current theory
   *
   * This ensures the LLM sees the actual constructor names, function equations,
   * and available lemmas — preventing it from guessing wrong names.
   */
  def fetchRichContext(
    view: View, 
    command: Command, 
    goalState: String,
    goalAnalysis: Option[GoalExtractor.GoalAnalysis]
  ): String = {
    val timeout = CopilotConstants.CONTEXT_FETCH_TIMEOUT
    val parts = scala.collection.mutable.ListBuffer[String]()

    // 1. Local proof facts
    val factsLatch = new CountDownLatch(1)
    @volatile var factsResult = ""
    GUI_Thread.later {
      PrintContextAction.runPrintContextAsync(view, command, timeout, { r =>
        r match {
          case Right(o) if o.trim.nonEmpty && !o.contains("No local facts") && !o.contains("No facts") =>
            factsResult = o.trim
          case _ =>
        }
        factsLatch.countDown()
      })
    }

    // 2. PIDE entity definitions
    val defsLatch = new CountDownLatch(1)
    @volatile var defsResult = ""
    Isabelle_Thread.fork(name = "prove-defs") {
      ContextFetcher.getContext(view, timeout).foreach(c => defsResult = c)
      defsLatch.countDown()
    }

    // 3. Find relevant theorems for constants in the goal
    val theoremsLatch = new CountDownLatch(1)
    @volatile var theoremsResult = ""
    val constants = goalAnalysis.map(_.constants).getOrElse(Nil)
    if (constants.nonEmpty && IQAvailable.isAvailable) {
      val criteria = constants.take(5).map(c => {
        val shortName = c.split('.').last
        s"""name: "$shortName""""
      }).mkString(" ")
      Output.writeln(s"[Copilot] Searching theorems for: $criteria")
      GUI_Thread.later {
        IQIntegration.runFindTheoremsAsync(view, command, criteria,
          CopilotOptions.getFindTheoremsLimit, CopilotOptions.getFindTheoremsTimeout, {
          case Right(results) if results.nonEmpty =>
            theoremsResult = "Relevant theorems:\n" + results.mkString("\n")
            theoremsLatch.countDown()
          case _ =>
            theoremsLatch.countDown()
        })
      }
    } else {
      theoremsLatch.countDown()
    }

    // 4. Fetch datatype and function definitions via PIDE/I/Q
    val theoryDefsLatch = new CountDownLatch(1)
    @volatile var theoryDefsResult = ""
    if (constants.nonEmpty && IQAvailable.isAvailable) {
      Isabelle_Thread.fork(name = "prove-theory-defs") {
        theoryDefsResult = fetchDefinitionsViaIQ(view, command, goalAnalysis, timeout)
        theoryDefsLatch.countDown()
      }
    } else {
      theoryDefsLatch.countDown()
    }

    // Wait for async results
    val waitMs = timeout + CopilotConstants.TIMEOUT_BUFFER_MS
    factsLatch.await(waitMs, TimeUnit.MILLISECONDS)
    defsLatch.await(waitMs, TimeUnit.MILLISECONDS)
    theoremsLatch.await(waitMs, TimeUnit.MILLISECONDS)
    theoryDefsLatch.await(waitMs, TimeUnit.MILLISECONDS)

    if (factsResult.nonEmpty) parts += s"Local facts:\n$factsResult"
    if (defsResult.nonEmpty) parts += s"Definitions:\n$defsResult"
    if (theoryDefsResult.nonEmpty) parts += theoryDefsResult
    if (theoremsResult.nonEmpty) parts += theoremsResult

    parts.filter(_.nonEmpty).mkString("\n\n")
  }

  /**
   * Fetch definitions for constants mentioned in the goal using PIDE/I/Q.
   */
  private def fetchDefinitionsViaIQ(
    view: View, 
    command: Command,
    goalAnalysis: Option[GoalExtractor.GoalAnalysis],
    timeoutMs: Long
  ): String = {
    val constants = goalAnalysis.map(_.constants).getOrElse(Nil)
    if (constants.isEmpty) return ""

    val shortNames = constants.map(c => c.split('.').last).distinct

    try {
      ContextFetcher.fetchDefinitionsForNames(view, command, shortNames, timeoutMs) match {
        case Some(defs) if defs.nonEmpty =>
          s"Definitions from current theory:\n$defs"
        case _ => ""
      }
    } catch {
      case ex: Exception =>
        Output.writeln(s"[Copilot] fetchDefinitionsViaIQ failed: ${ex.getMessage}")
        ""
    }
  }
}