/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/**
 * Analyzes proof patterns across a theory file and suggests improvements.
 * Extracts all proof blocks using PIDE command structure and sends them
 * to the LLM for pattern analysis.
 */
object AnalyzePatternsAction {
  
  def analyze(view: View): Unit = {
    val buffer = view.getBuffer
    val proofs = extractProofBlocks(buffer)
    
    if (proofs.isEmpty) {
      GUI.warning_dialog(view, "Isabelle Assistant", "No proof blocks found in theory")
    } else {
      ActionHelper.runAndRespond("assistant-analyze-patterns", "Analyzing proof patterns...") {
        val subs = Map("proofs" -> proofs.mkString("\n\n---\n\n"), "proof_count" -> proofs.length.toString)
        val prompt = PromptLoader.load("analyze_patterns.md", subs)
        BedrockClient.invokeInContext(prompt)
      }
    }
  }
  
  /** Extract proof blocks using PIDE command structure for reliable parsing. */
  private def extractProofBlocks(buffer: org.gjt.sp.jedit.buffer.JEditBuffer): List[String] = {
    val proofStarters = IsabelleKeywords.proofStarters
    // Enders that close a proof...qed block (decrement depth)
    val structuralEnders = Set("qed", "done", "sorry", "oops")

    Document_Model.get_model(buffer).map { model =>
      val snapshot = Document_Model.snapshot(model)
      val node = snapshot.get_node(model.node_name)
      if (node.commands.isEmpty) Nil
      else {
        val commands = node.command_iterator().toList
        val blocks = scala.collection.mutable.ListBuffer[String]()
        var i = 0
        while (i < commands.length) {
          val (cmd, _) = commands(i)
          // Use PIDE span name — the parsed command keyword
          val kw = cmd.span.name
          if (proofStarters.contains(kw)) {
            var depth = 0
            val block = scala.collection.mutable.ListBuffer[String]()
            var j = i
            var found = false
            while (j < commands.length && !found) {
              val (c, _) = commands(j)
              val k = c.span.name
              block += c.source
              if (k == "proof") depth += 1
              if (k == "by" && depth == 0) {
                // Top-level one-liner proof: lemma ... by method
                found = true
              } else if (structuralEnders.contains(k)) {
                if (depth <= 1) found = true
                else depth -= 1
              }
              j += 1
            }
            if (found) blocks += block.mkString("\n")
            i = j
          } else {
            i += 1
          }
        }
        blocks.toList.filter(_.length > 8).take(30)
      }
    }.getOrElse(Nil)
  }
}
