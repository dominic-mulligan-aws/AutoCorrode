/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.buffer.JEditBuffer

/**
 * Detects Copilot feature support level based on theory imports.
 * Reports FullSupport (Copilot_Support imported), PartialSupport (I/Q or Eisbach),
 * or NoSupport (LLM-only). Used by the status bar and help dialog.
 */
object CopilotSupport {
  
  sealed trait Status
  case object FullSupport extends Status      // Copilot_Support imported
  case object PartialSupport extends Status   // I/Q available or Eisbach imported  
  case object NoSupport extends Status        // No special support
  
  /** Check if a theory is in the loaded dependencies */
  private def hasTheoryImport(buffer: JEditBuffer, theoryName: String): Boolean = {
    Document_Model.get_model(buffer).exists { model =>
      val snapshot = Document_Model.snapshot(model)
      val nodes = snapshot.version.nodes
      nodes.domain.exists { name =>
        val str = name.theory
        str == theoryName || str.endsWith("." + theoryName)
      }
    }
  }
  
  private def hasCopilotSupport(buffer: JEditBuffer): Boolean =
    hasTheoryImport(buffer, "Copilot_Support")
  
  private def hasEisbachImport(buffer: JEditBuffer): Boolean =
    // Copilot_Support imports Eisbach, so if we have Copilot_Support we have Eisbach
    hasCopilotSupport(buffer) || hasTheoryImport(buffer, "Eisbach")
  
  def getStatus(buffer: JEditBuffer): Status = {
    val hasCopilot = hasCopilotSupport(buffer)
    val hasEisbach = hasEisbachImport(buffer)
    val hasIQ = IQAvailable.isAvailable
    
    // Full support requires Copilot_Support (which includes Eisbach)
    if (hasCopilot) FullSupport
    // Partial if we have I/Q or Eisbach but not Copilot_Support
    else if (hasIQ || hasEisbach) PartialSupport
    else NoSupport
  }
  
  def hasEisbach(buffer: JEditBuffer): Boolean = 
    hasCopilotSupport(buffer) || hasEisbachImport(buffer)
  
  def hasIQ: Boolean = IQAvailable.isAvailable
  
  def importSuggestion: String = 
    """imports "Isabelle_Copilot.Copilot_Support" (* or: imports "$ISABELLE_COPILOT_HOME/Copilot_Support" *)"""
  
  def statusText(status: Status): String = status match {
    case FullSupport => "Copilot [ok]"
    case PartialSupport =>
      if (!IQAvailable.isAvailable) "Copilot (no I/Q)"
      else "Copilot: Partial"
    case NoSupport => "Copilot (LLM only)"
  }
  
  def statusColor(status: Status): java.awt.Color = status match {
    case FullSupport => ThemeUtils.successColor
    case PartialSupport => ThemeUtils.warningColor
    case NoSupport => ThemeUtils.neutralColor
  }
  
  def helpText(buffer: JEditBuffer): String = {
    val hasCopilot = hasCopilotSupport(buffer)
    val hasEisbach = hasEisbachImport(buffer)
    val hasIQ = IQAvailable.isAvailable
    
    val features = List(
      if (hasIQ) "[ok] Proof verification (I/Q)" else "[n/a] Proof verification (I/Q not installed)",
      if (hasIQ) "[ok] Sledgehammer integration" else "[n/a] Sledgehammer (I/Q not installed)",
      if (hasEisbach || hasCopilot) "[ok] Custom tactic generation (Eisbach)" else "[n/a] Custom tactics (import Eisbach)",
      if (hasIQ) "[ok] Simplifier tracing" else "[n/a] Simplifier tracing (I/Q not installed)"
    ).mkString("\n")
    
    if (hasCopilot && hasIQ) {
      s"""Copilot has full support enabled.
         |
         |$features""".stripMargin
    } else {
      s"""Copilot feature status:
         |
         |$features
         |
         |For full features, import:
         |$importSuggestion""".stripMargin
    }
  }
}
