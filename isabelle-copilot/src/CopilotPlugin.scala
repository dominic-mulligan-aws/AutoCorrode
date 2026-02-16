/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

import isabelle._
import org.gjt.sp.jedit.{EBMessage, EBPlugin}

/** jEdit plugin lifecycle: starts/stops Copilot services and cleans up resources. */
class CopilotPlugin extends EBPlugin {
  override def start(): Unit = {
    Output.writeln("Isabelle Copilot starting...")
    IQAvailable.logStatus()
  }

  override def stop(): Unit = {
    Output.writeln("Isabelle Copilot stopping...")
    BedrockClient.cleanup()
    ErrorHandler.cleanupAll()
    VerificationCache.clear()
    PromptLoader.clearCache()
    LLMResponseCache.clear()
  }

  override def handleMessage(message: EBMessage): Unit = {}
}
