/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Renders HTML for conversation message bubbles in the chat panel.
 * Extracted from AssistantDockable to separate rendering concerns from UI lifecycle.
 */
object ConversationRenderer {

  /** Shared chat bubble wrapper used by user, assistant, and tool message renderers. */
  def messageBubbleHtml(
      border: String,
      headerHtml: String,
      bodyHtml: String,
      copyContent: Option[String] = None
  ): String = {
    val copyLink = copyContent match {
      case Some(raw) =>
        val encoded = java.net.URLEncoder.encode(raw, "UTF-8")
        val copyColor = UIColors.CopyButton.color
        s"""<a href='action:copy:$encoded' style='position:absolute;top:6px;right:8px;text-decoration:none;color:$copyColor;opacity:0.6;font-size:10pt;font-weight:normal;' onmouseover='this.style.opacity="1.0"' onmouseout='this.style.opacity="0.6"' title='Copy message'>Copy</a>"""
      case None => ""
    }
    val posStyle = if (copyContent.isDefined) "position:relative;" else ""
    s"""<div style='margin:6px 0;padding:8px 10px;background:white;border-left:4px solid $border;border-radius:3px;overflow-x:hidden;word-wrap:break-word;box-shadow:0 1px 2px rgba(0,0,0,0.1);$posStyle'>
       |$copyLink
       |$headerHtml
       |<div>$bodyHtml</div>
       |</div>""".stripMargin
  }

  def createUserMessageHtml(
      content: String,
      timestamp: String
  ): String = {
    val tsColor = UIColors.ChatBubble.userTimestamp
    messageBubbleHtml(
      border = UIColors.ChatBubble.userBorder,
      headerHtml =
        s"<div style='font-size:10pt;color:$tsColor;margin-bottom:3px;'><b>You</b> · $timestamp</div>",
      bodyHtml = MarkdownRenderer.toBodyHtml(content),
      copyContent = Some(content)
    )
  }

  def createAssistantMessageHtml(
      content: String,
      timestamp: String,
      rawHtml: Boolean = false,
      registerAction: String => String
  ): String = {
    val isError = content.startsWith("Error:") || content.startsWith("[FAIL]")
    val body =
      if (rawHtml) content
      else {
        val rendered =
          MarkdownRenderer.toBodyHtmlWithActions(content, registerAction)
        val withLinks = "\\{\\{INSERT:([a-f0-9]+)\\}\\}".r.replaceAllIn(
          rendered,
          m => s"<a href='action:insert:${m.group(1)}'>[Insert]</a>"
        )
        "\\{\\{ACTION:([a-f0-9]+):([^}]+)\\}\\}".r.replaceAllIn(
          withLinks,
          m => s"<a href='action:insert:${m.group(1)}'>Run ${m.group(2)}</a>"
        )
      }
    val (border, tsColor) = if (isError) {
      (UIColors.ChatBubble.errorBorder, UIColors.ChatBubble.errorTimestamp)
    } else {
      (
        UIColors.ChatBubble.assistantBorder,
        UIColors.ChatBubble.assistantTimestamp
      )
    }
    messageBubbleHtml(
      border = border,
      headerHtml =
        s"<div style='font-size:10pt;color:$tsColor;margin-bottom:3px;'><b>Assistant</b> · $timestamp</div>",
      bodyHtml = body,
      copyContent = Some(content)
    )
  }

  /** Create HTML for a tool-use message. Parameters shown inline only. */
  def createToolMessageHtml(
      toolName: String,
      params: ResponseParser.ToolArgs,
      timestamp: String
  ): String = {
    val border = UIColors.ToolMessage.border
    val tsColor = UIColors.ToolMessage.timestamp

    // Convert snake_case to PascalCase for display
    val displayName = toolName.split("_").map(_.capitalize).mkString

    // Format parameters for summary line
    val paramSummary =
      if (params.isEmpty) "()"
      else {
        val formatted = params
          .map { case (k, v) =>
            s"$k: ${HtmlUtil.escapeHtml(ResponseParser.toolValueToDisplay(v))}"
          }
          .mkString(", ")
        s"($formatted)"
      }

    val bodyHtml =
      s"<div style='font-family:${MarkdownRenderer.codeFont};font-size:11pt;'><b>$displayName</b><span style='color:#888;font-weight:normal;'>$paramSummary</span></div>"
    messageBubbleHtml(
      border = border,
      headerHtml =
        s"<div style='font-size:10pt;color:$tsColor;margin-bottom:3px;'><b>Tool</b> · $timestamp</div>",
      bodyHtml = bodyHtml
    )
  }

  def createWelcomeHtml(registerHelpAction: () => String): String = {
    val helpId = registerHelpAction()
    val wBg = UIColors.Welcome.background
    val wBorder = UIColors.Welcome.border
    val wTitle = UIColors.Welcome.title
    val wText = UIColors.Welcome.text
    val wMuted = UIColors.Welcome.muted
    val codeBg = UIColors.Welcome.codeBackground
    val linkColor = UIColors.Welcome.linkColor

    val modelWarning = if (AssistantOptions.getModelId.isEmpty) {
      val eBg = UIColors.ErrorBox.background
      val eBorder = UIColors.ErrorBox.border
      val eText = UIColors.ErrorBox.text
      s"""<div style='margin-top:6px;padding:6px 8px;background:$eBg;border:1px solid $eBorder;border-radius:3px;font-size:11pt;color:$eText;'>
         |No model configured. Use <code style='background:$codeBg;padding:1px 4px;border-radius:2px;'>:set model &lt;model-id&gt;</code> or
         |<b>Plugins → Plugin Options → Isabelle Assistant</b> to set one.
         |Run <code style='background:$codeBg;padding:1px 4px;border-radius:2px;'>:models</code> to see available models.</div>""".stripMargin
    } else ""
    s"""<div style='margin:8px 0;padding:10px 12px;background:$wBg;border:1px solid $wBorder;border-radius:4px;'>
       |<div style='font-weight:bold;color:$wTitle;margin-bottom:4px;'>Isabelle Assistant</div>
       |<div style='color:$wText;font-size:11pt;'>AI assistant for Isabelle/HOL proofs, powered by AWS Bedrock.<br/>
       |Type a message or click <a href='action:insert:$helpId' style='color:$linkColor;text-decoration:none;font-weight:bold;'>:help</a> to see all available commands.
       |<span style='font-size:10pt;color:$wMuted;'>(Enter sends, Shift+Enter for newline)</span></div>
       |$modelWarning
       |</div>""".stripMargin
  }
}