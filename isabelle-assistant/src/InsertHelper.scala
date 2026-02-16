/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.View

/**
 * Utilities for creating insert actions that add generated code to the buffer.
 * Provides a consistent, DRY way to create insert callbacks with proper
 * compound edit wrapping throughout the codebase.
 */
object InsertHelper {
  
  /**
   * Create an insert action that adds code at the current cursor position.
   * Wraps the insertion in a compound edit for proper undo/redo support.
   * 
   * @param view The jEdit view
   * @param code The code to insert
   * @return Action callback suitable for AssistantDockable.registerAction
   */
  def createInsertAction(view: View, code: String): () => Unit = () => {
    val buf = view.getBuffer
    buf.beginCompoundEdit()
    try {
      buf.insert(view.getTextArea.getCaretPosition, code)
    } finally {
      buf.endCompoundEdit()
    }
  }
  
  /**
   * Create an insert action and register it with AssistantDockable.
   * Returns the action ID for use in hyperlinks.
   * 
   * @param view The jEdit view
   * @param code The code to insert
   * @return Action ID for use in {{INSERT:id}} placeholders
   */
  def registerInsertAction(view: View, code: String): String = {
    AssistantDockable.registerAction(createInsertAction(view, code))
  }
}