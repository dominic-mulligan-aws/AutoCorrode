/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/**
 * Checks I/Q plugin availability via class loading, with periodic re-checking.
 * I/Q (Isabelle/Q) provides proof verification, sledgehammer, find_theorems,
 * and other Isabelle query capabilities. When unavailable, Assistant runs in
 * LLM-only mode with reduced functionality.
 *
 * The availability status is cached but can be refreshed via `recheck()`,
 * for example if I/Q is installed after Assistant starts.
 */
object IQAvailable {
  @volatile private var _cached: Option[Boolean] = None

  private def check(): Boolean = {
    try {
      Class.forName("isabelle.Extended_Query_Operation")
      true
    } catch {
      case _: ClassNotFoundException => false
      case _: NoClassDefFoundError => false
    }
  }

  def isAvailable: Boolean = _cached match {
    case Some(v) => v
    case None =>
      val result = check()
      _cached = Some(result)
      result
  }

  /** Force a re-check of I/Q availability. Call after installing I/Q at runtime. */
  def recheck(): Boolean = {
    val result = check()
    val changed = _cached.exists(_ != result)
    _cached = Some(result)
    if (changed) {
      logStatus()
      AssistantDockable.refreshIQStatus()
    }
    result
  }

  def logStatus(): Unit = {
    if (isAvailable)
      Output.writeln("[Assistant] I/Q plugin detected - proof verification features enabled")
    else
      Output.writeln("[Assistant] I/Q plugin not found - running in LLM-only mode. Restart Isabelle/jEdit after installing I/Q to enable verification.")
  }
}