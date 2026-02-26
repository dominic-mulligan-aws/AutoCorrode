/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/** HTML escaping utility for the Assistant plugin.
  *
  * Provides canonical HTML entity escaping used throughout all HTML generation
  * in chat messages, widgets, and code blocks. This ensures XSS-safe output when
  * displaying user-provided or LLM-generated content.
  */
object HtmlUtil {

  /** Escape HTML special characters for safe embedding in HTML documents.
    *
    * Converts & → &amp;, < → &lt;, > → &gt;, " → &quot;, ' → &#39; to prevent 
    * HTML injection and ensure special characters display correctly both in text 
    * content and attribute values.
    *
    * @param s The string to escape (may contain any characters)
    * @return HTML-safe string with special characters converted to entities
    */
  def escapeHtml(s: String): String =
    s.replace("&", "&amp;")
      .replace("<", "&lt;")
      .replace(">", "&gt;")
      .replace("\"", "&quot;")
      .replace("'", "&#39;")
}
