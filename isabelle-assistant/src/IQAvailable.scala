/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._

/** Checks I/Q availability via MCP reachability probes, with periodic heartbeat.
  *
  * I/Q (Isabelle/Q) provides proof verification, sledgehammer, find_theorems,
  * and other Isabelle query capabilities. When unavailable, Assistant runs in
  * LLM-only mode with reduced functionality.
  *
  * The availability status is periodically refreshed via a background heartbeat
  * that uses a lightweight `ping` method to minimize overhead.
  */
object IQAvailable {
  @volatile private var _cached: Option[Boolean] = None
  private val HeartbeatProbeTimeoutMs = 500L      // Fast probe for heartbeat
  private val InitialProbeTimeoutMs = 1000L       // Longer timeout for initial check
  private val HeartbeatIntervalMs = 15000L        // Check every 15 seconds
  @volatile private var heartbeatScheduled = false
  
  private val scheduler = java.util.concurrent.Executors.newSingleThreadScheduledExecutor(
    new java.util.concurrent.ThreadFactory {
      def newThread(r: Runnable): Thread = {
        val t = new Thread(r, "iq-heartbeat")
        t.setDaemon(true)
        t
      }
    }
  )

  private def probe(timeoutMs: Long = HeartbeatProbeTimeoutMs): Boolean = {
    // Use lightweight ping instead of list_files
    IQMcpClient.ping(timeoutMs)
  }

  /** Start periodic heartbeat to monitor I/Q availability.
    * Called from AssistantPlugin.start().
    */
  def startHeartbeat(): Unit = synchronized {
    if (!heartbeatScheduled) {
      heartbeatScheduled = true
      // Initial probe with longer timeout
      val initial = probe(InitialProbeTimeoutMs)
      _cached = Some(initial)
      logStatus()
      
      // Schedule periodic probes with shorter timeout
      val _ = scheduler.scheduleWithFixedDelay(
        () => {
          val wasAvailable = _cached.getOrElse(false)
          val nowAvailable = probe(HeartbeatProbeTimeoutMs)
          _cached = Some(nowAvailable)
          if (wasAvailable != nowAvailable) {
            logStatus()
            AssistantDockable.refreshIQStatus()
          }
        },
        HeartbeatIntervalMs,
        HeartbeatIntervalMs,
        java.util.concurrent.TimeUnit.MILLISECONDS
      )
    }
  }

  /** Stop the heartbeat scheduler. Called from AssistantPlugin.stop(). */
  def stopHeartbeat(): Unit = synchronized {
    if (heartbeatScheduled) {
      heartbeatScheduled = false
      val _ = scheduler.shutdownNow()
    }
  }

  def isAvailable: Boolean = _cached match {
    case Some(v) => v
    case None =>
      // First access - do immediate probe and start heartbeat
      val result = probe(InitialProbeTimeoutMs)
      _cached = Some(result)
      startHeartbeat()
      result
  }

  /** Get cached I/Q availability status without making any network call.
    * Returns false if no probe has been performed yet. Safe for EDT use.
    */
  def isAvailableCached: Boolean = _cached.getOrElse(false)

  /** Force a re-check of I/Q availability. Call after installing I/Q at runtime. */
  def recheck(): Boolean = {
    val result = probe(InitialProbeTimeoutMs)
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
      Output.writeln("[Assistant] I/Q MCP endpoint unavailable - running in LLM-only mode.")
  }
}
