/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import java.util.concurrent.{CountDownLatch, TimeUnit}

/**
 * Centralized I/Q operation execution utilities.
 * Provides synchronous wrappers around IQIntegration's async operations
 * for use in proof loop contexts where blocking is acceptable.
 */
object IQExecutor {

  /**
   * Execute a proof step synchronously and return the resulting proof state.
   * Blocks until completion or timeout.
   * 
   * @param view jEdit view
   * @param command Isabelle command context
   * @param proofText Proof text to execute
   * @return Right(result) on success, Left(error) on failure
   */
  def executeStep(
    view: View, 
    command: Command, 
    proofText: String
  ): Either[String, IQIntegration.ProofStepResult] = {
    val timeoutMs = AssistantOptions.getProveStepTimeout
    Output.writeln(s"[Assistant] executeStep sending:\n$proofText")
    
    val latch = new CountDownLatch(1)
    @volatile var result: Either[String, IQIntegration.ProofStepResult] = Left("no response")
    
    GUI_Thread.later {
      IQIntegration.executeStepAsync(view, command, proofText, timeoutMs, { r =>
        Output.writeln(s"[Assistant] executeStep result: $r")
        result = r
        latch.countDown()
      })
    }
    
    latch.await(timeoutMs + 5000, TimeUnit.MILLISECONDS)
    result
  }

  /**
   * Get the goal state text at the given view position.
   * Blocks until completion or timeout.
   */
  def getGoalState(view: View): String = {
    val latch = new CountDownLatch(1)
    @volatile var goal = ""
    
    GUI_Thread.later {
      goal = GoalExtractor.getGoalState(
        view.getBuffer, 
        view.getTextArea.getCaretPosition
      ).getOrElse("")
      latch.countDown()
    }
    
    latch.await(AssistantConstants.GUI_DISPATCH_TIMEOUT_SEC, TimeUnit.SECONDS)
    goal
  }

  /**
   * Get structured goal analysis from PIDE markup at cursor.
   * Blocks until completion or timeout.
   */
  def analyzeGoalAtCursor(view: View): Option[GoalExtractor.GoalAnalysis] = {
    GUIThreadUtil.awaitOnGUIThread(AssistantConstants.GUI_DISPATCH_TIMEOUT) {
      GoalExtractor.analyzeGoal(
        view.getBuffer, 
        view.getTextArea.getCaretPosition
      )
    }.flatten
  }

  /**
   * Get structured goal analysis at a specific offset.
   */
  def analyzeGoalAtOffset(view: View, offset: Int): Option[GoalExtractor.GoalAnalysis] = {
    GUIThreadUtil.awaitOnGUIThread(AssistantConstants.GUI_DISPATCH_TIMEOUT) {
      GoalExtractor.analyzeGoal(view.getBuffer, offset)
    }.flatten
  }

  /**
   * Get the PIDE Command object at the current cursor position.
   */
  def getCommandAtCursor(view: View): Option[Command] = {
    GUIThreadUtil.awaitOnGUIThread(AssistantConstants.GUI_DISPATCH_TIMEOUT) {
      IQIntegration.getCommandAtOffset(
        view.getBuffer,
        view.getTextArea.getCaretPosition
      )
    }.flatten
  }

  /**
   * Find the buffer offset of a PIDE Command.
   */
  def findCommandOffset(view: View, cmd: Command): Option[Int] = {
    GUIThreadUtil.awaitOnGUIThread(AssistantConstants.GUI_DISPATCH_TIMEOUT) {
      Document_Model.get_model(view.getBuffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val node = snapshot.get_node(model.node_name)
        node.command_iterator().toList.find(_._1.id == cmd.id).map(_._2)
      }
    }.flatten
  }

  /**
   * Try a list of proof methods via I/Q, returning the first that succeeds.
   */
  def tryMethods(
    view: View, 
    command: Command, 
    methods: List[String], 
    label: String
  ): Option[String] = {
    val chat = (msg: String) => GUI_Thread.later { ChatAction.addTransient(msg) }
    chat(s"Trying ${methods.length} $label methods...")
    
    import scala.util.boundary, boundary.break
    boundary {
      for (method <- methods) {
        if (AssistantDockable.isCancelled) break(None)
        
        val latch = new CountDownLatch(1)
        @volatile var result: Option[IQIntegration.VerificationResult] = None
        
        GUI_Thread.later {
          IQIntegration.verifyProofAsync(
            view, command, method, 
            AssistantOptions.getProveStepTimeout, 
            { r =>
              result = Some(r)
              latch.countDown()
            }
          )
        }
        
        latch.await(AssistantOptions.getProveStepTimeout + 2000, TimeUnit.MILLISECONDS)
        
        result match {
          case Some(IQIntegration.ProofSuccess(ms, _)) =>
            chat(s"  [ok] `$method` verified (${ms}ms)")
            break(Some(method))
          case _ => // try next
        }
      }
      None
    }
  }
}