/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.buffer.JEditBuffer

/**
 * Extracts the Isabelle command source text at a given buffer offset using PIDE markup.
 * Looks up the PIDE document model for the buffer, finds the command spanning the offset,
 * and returns its source text. Returns None if no model or command is available.
 */
object CommandExtractor {
  /** Get the source text of the Isabelle command at the given buffer offset.
   *  Requires the buffer to have an active PIDE document model. */
  def getCommandAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    Document_Model.get_model(buffer).flatMap { model =>
      val snapshot = Document_Model.snapshot(model)
      val node = snapshot.get_node(model.node_name)

      if (node.commands.nonEmpty) {
        // Clamp range to avoid exceeding buffer length when cursor is at end
        val safeEnd = math.min(offset + 1, buffer.getLength)
        val targetRange = Text.Range(offset, safeEnd)
        node.command_iterator(targetRange).toList.headOption.map {
          case (command, _) => command.source
        }
      } else None
    }
  }

  /** Get the PIDE span name (parsed command keyword) at the given buffer offset.
   *  Uses PIDE's command parser — no string splitting or regex. */
  def getCommandKeyword(buffer: JEditBuffer, offset: Int): Option[String] = {
    Document_Model.get_model(buffer).flatMap { model =>
      val snapshot = Document_Model.snapshot(model)
      val node = snapshot.get_node(model.node_name)

      if (node.commands.nonEmpty) {
        // Clamp range to avoid exceeding buffer length when cursor is at end
        val safeEnd = math.min(offset + 1, buffer.getLength)
        val targetRange = Text.Range(offset, safeEnd)
        node.command_iterator(targetRange).toList.headOption.map {
          case (command, _) => command.span.name
        }
      } else None
    }
  }
}
