/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Traces simplifier (simp/auto) via I/Q and explains the trace output using LLM. */
object TraceSimplifierAction {
  
  def trace(view: View, method: String = "simp"): Unit = {
    // Emit command to chat
    ChatAction.addMessage("user", ":trace")
    CopilotDockable.showConversation(ChatAction.getHistory)
    
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    
    val goalState = GoalExtractor.getGoalState(buffer, offset)
    if (goalState.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Copilot", "No goal at cursor")
    } else {
      val commandOpt = IQIntegration.getCommandAtOffset(buffer, offset)
      if (commandOpt.isEmpty || !IQAvailable.isAvailable) {
        GUI.warning_dialog(view, "Isabelle Copilot", "I/Q required for tracing")
      } else {
        CopilotDockable.setStatus(s"Running $method with trace...")
    
        GUI_Thread.later {
          runSimpTrace(view, commandOpt.get, goalState.get, method)
        }
      }
    }
  }
  
  private def runSimpTrace(view: View, command: Command, goal: String, method: String): Unit = {
    val timeout = CopilotOptions.getTraceTimeout
    val depth = CopilotOptions.getTraceDepth
    val queryTimeoutMs = timeout * 1000L + CopilotConstants.TIMEOUT_BUFFER_MS

    IQIntegration.runQueryAsync(view, command, List(s"simp_trace $method $timeout $depth"), queryTimeoutMs, {
      case Right(output) => processTrace(view, goal, output, method)
      case Left(error) => processTrace(view, goal, s"Error: $error", method)
    })
  }
  
  private def processTrace(view: View, goal: String, traceOutput: String, method: String): Unit = {
    if (traceOutput.trim.isEmpty) {
      ChatAction.addMessage("assistant", "No output captured."); CopilotDockable.showConversation(ChatAction.getHistory)
      CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
    } else {
    
    // Check if it timed out
    val timedOut = traceOutput.contains("TIMED_OUT")
    
    CopilotDockable.setStatus("Explaining trace...")
    
    Isabelle_Thread.fork(name = "explain-trace") {
      try {
        val subs = scala.collection.mutable.Map(
          "goal" -> goal,
          "trace" -> traceOutput,
          "method" -> method
        )
        if (timedOut) subs("timed_out") = "true"
        
        val prompt = PromptLoader.load("trace_simplifier.md", subs.toMap)
        val response = BedrockClient.invokeInContext(prompt)
        
        GUI_Thread.later {
          ChatAction.addMessage("assistant", response); CopilotDockable.showConversation(ChatAction.getHistory)
          CopilotDockable.setStatus(CopilotConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            // Show raw trace if LLM fails
            ChatAction.addMessage("assistant", s"Trace output:\n\n$traceOutput"); CopilotDockable.showConversation(ChatAction.getHistory)
            CopilotDockable.setStatus("Error: " + ex.getMessage)
          }
      }
    }
    }
  }
}
