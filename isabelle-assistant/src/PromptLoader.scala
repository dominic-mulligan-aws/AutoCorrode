/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import com.samskivert.mustache.Mustache
import scala.jdk.CollectionConverters._

/**
 * Loads Mustache prompt templates from the prompts/ directory.
 * Caches auto-discovered system prompts from prompts/system/ for reuse.
 */
object PromptLoader {
  @volatile private var cachedSystemPrompt: Option[String] = None
  private val cacheLock = new Object()

  /** Resolve ISABELLE_ASSISTANT_HOME, returning None with a warning if unset. */
  private def assistantHome: Option[String] = {
    val home = Isabelle_System.getenv("ISABELLE_ASSISTANT_HOME")
    if (home.isEmpty) {
      Output.warning("[Assistant] ISABELLE_ASSISTANT_HOME not set. Install the plugin via 'make install' or set the variable manually.")
      None
    } else Some(home)
  }

  def load(name: String, substitutions: Map[String, String]): String = {
    val home = assistantHome.getOrElse(
      error("ISABELLE_ASSISTANT_HOME not set — install the plugin via 'make install' or add init_component to settings"))

    val path = Path.explode(home) + Path.explode("prompts") + Path.explode(name)
    if (!path.is_file)
      error("Prompt file not found: " + path)

    val template = Mustache.compiler().compile(File.read(path))
    template.execute(substitutions.asJava)
  }

  /** Load and cache all system prompts from prompts/system/ directory */
  def getSystemPrompt: String = cacheLock.synchronized {
    cachedSystemPrompt.getOrElse {
      val prompt = assistantHome match {
        case None => ""
        case Some(home) =>
          val systemDir = Path.explode(home) + Path.explode("prompts") + Path.explode("system")
          if (systemDir.is_dir) {
            val files = File.read_dir(systemDir).filter(_.endsWith(".md")).sorted
            files.map(name => File.read(systemDir + Path.explode(name))).mkString("\n\n")
          } else ""
      }
      cachedSystemPrompt = Some(prompt)
      prompt
    }
  }

  /** Clear cached system prompt (for development/testing) */
  def clearCache(): Unit = cacheLock.synchronized { cachedSystemPrompt = None }
}
