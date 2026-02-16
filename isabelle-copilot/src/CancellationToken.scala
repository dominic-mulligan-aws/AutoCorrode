/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import java.util.concurrent.atomic.AtomicBoolean

/**
 * Per-operation cancellation token.
 * Allows individual operations to be cancelled without affecting others.
 * Thread-safe via atomic operations.
 */
class CancellationToken {
  private val cancelled = new AtomicBoolean(false)
  
  /** Check if this operation has been cancelled. */
  def isCancelled: Boolean = cancelled.get()
  
  /** Cancel this operation. */
  def cancel(): Unit = cancelled.set(true)
  
  /** Reset cancellation state (for reuse, though creating new tokens is preferred). */
  def reset(): Unit = cancelled.set(false)
}

/**
 * Manages cancellation tokens for active operations.
 * The UI cancel button cancels the most recent operation.
 */
object CancellationToken {
  private val currentToken = new AtomicBoolean(false)
  
  /** Create a new cancellation token and register it as the current operation. */
  def create(): CancellationToken = {
    val token = new CancellationToken()
    // For now, maintain backward compatibility with global _cancelled flag
    // Future: migrate all operations to use their own tokens
    token
  }
  
  /** Cancel the current operation (backward compatibility with global cancel). */
  def cancelCurrent(): Unit = {
    currentToken.set(true)
  }
  
  /** Check if current operation is cancelled (backward compatibility). */
  def isCurrentCancelled: Boolean = currentToken.get()
  
  /** Reset current cancellation state. */
  def resetCurrent(): Unit = {
    currentToken.set(false)
  }
}