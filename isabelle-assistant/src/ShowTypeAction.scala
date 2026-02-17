/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View
import org.gjt.sp.jedit.buffer.JEditBuffer

/** Displays type information at cursor from PIDE typing markup. */
object ShowTypeAction {
  def showType(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition

    getTypeAtOffset(buffer, offset) match {
      case Some(typ) =>
        AssistantDockable.respondInChat(s"Type: `$typ`")
      case None =>
        AssistantDockable.respondInChat("No type information available at cursor position.")
    }
  }

  def getTypeAtOffset(buffer: JEditBuffer, offset: Int): Option[String] = {
    try {
      Document_Model.get_model(buffer).flatMap { model =>
        val snapshot = Document_Model.snapshot(model)
        val searchStart = math.max(0, offset - 50)
        val searchEnd = math.min(buffer.getLength, offset + 50)
        val range = Text.Range(searchStart, searchEnd)

        val types = snapshot.cumulate(range, List.empty[(Text.Range, String)],
          Markup.Elements(Markup.TYPING), _ => {
            case (acc, Text.Info(r, XML.Elem(Markup(Markup.TYPING, _), body))) =>
              Some(acc :+ (r, XML.content(body)))
            case _ => None
          })

        types.flatMap(_._2)
          .filter { case (r, _) => r.contains(offset) }
          .sortBy { case (r, _) => r.length }
          .headOption
          .map { case (r, typ) =>
            val term = buffer.getText(r.start, math.min(r.length, 80))
            s"$term :: $typ"
          }
      }
    } catch {
      case _: Exception => None
    }
  }

  def hasTypeAtOffset(buffer: JEditBuffer, offset: Int): Boolean =
    getTypeAtOffset(buffer, offset).isDefined
}
