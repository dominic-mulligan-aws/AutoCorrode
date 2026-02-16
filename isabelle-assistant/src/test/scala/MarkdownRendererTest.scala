/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class MarkdownRendererTest extends AnyFunSuite with Matchers {

  test("bold rendering") {
    val html = MarkdownRenderer.toBodyHtml("**bold**")
    html should include("<b>bold</b>")
  }

  test("italic rendering") {
    val html = MarkdownRenderer.toBodyHtml("*italic*")
    html should include("<i>italic</i>")
  }

  test("inline code rendering") {
    val html = MarkdownRenderer.toBodyHtml("`code`")
    html should include("<code")
    html should include("code</code>")
  }

  test("nested bold and italic") {
    val html = MarkdownRenderer.toBodyHtml("**bold *italic* text**")
    html should include("<b>bold <i>italic</i> text</b>")
  }

  test("code fence rendering") {
    val md = "```\nsome code\n```"
    val html = MarkdownRenderer.toBodyHtml(md)
    html should include("<pre")
    html should include("some code")
  }

  test("heading rendering") {
    MarkdownRenderer.toBodyHtml("# H1") should include("<h1")
    MarkdownRenderer.toBodyHtml("## H2") should include("<h2")
    MarkdownRenderer.toBodyHtml("### H3") should include("<h3")
  }

  test("bullet list rendering") {
    val html = MarkdownRenderer.toBodyHtml("- item")
    html should include("•")
    html should include("item")
  }

  test("HTML escaping") {
    val html = MarkdownRenderer.toBodyHtml("<script>alert('xss')</script>")
    html should not include "<script>"
    html should include("&lt;script&gt;")
  }

  test("action code block") {
    val md = "```action:abc123\nby simp\n```"
    val html = MarkdownRenderer.toBodyHtml(md)
    html should include("action:insert:abc123")
    html should include("by simp")
  }
}
