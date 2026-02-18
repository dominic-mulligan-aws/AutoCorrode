/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt._
import javax.swing._

/** Verification status badges (Verified, Failed, Unverified, etc.) with colored Swing panels.
 *  Each badge type represents a verification outcome and maps to a display color and label. */
object VerificationBadge {
  /** Verification outcome for display in the dockable badge area and chat messages. */
  enum BadgeType {
    case Verified(timeMs: Option[Long] = None)
    case Failed(reason: String = "")
    case Unverified
    case Verifying
    case Sledgehammer(timeMs: Option[Long] = None)
    case EisbachMissing
  }
  export BadgeType._

  def toStatus(badge: BadgeType): String = badge match {
    case Verified(_) => AssistantConstants.STATUS_READY
    case Failed(_) => AssistantConstants.STATUS_READY
    case Unverified => AssistantConstants.STATUS_READY
    case Verifying => AssistantConstants.STATUS_VERIFYING
    case Sledgehammer(_) => AssistantConstants.STATUS_READY
    case EisbachMissing => AssistantConstants.STATUS_READY
  }

  private def badgeInfo(badge: BadgeType): (String, String, String, String) = badge match {
    case Verified(t) => (UIColors.Badge.successBackground, UIColors.Badge.successText, UIColors.Badge.successBorder, "Verified" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case Failed(r) => (UIColors.Badge.errorBackground, UIColors.Badge.errorText, UIColors.Badge.errorBorder, "Failed" + (if (r.nonEmpty) s": ${r.take(40)}" else ""))
    case Unverified => (UIColors.Badge.warningBackground, UIColors.Badge.warningText, UIColors.Badge.warningBorder, "Unverified")
    case Verifying => (UIColors.Badge.neutralBackground, UIColors.Badge.neutralText, UIColors.Badge.neutralBorder, "Verifying...")
    case Sledgehammer(t) => (UIColors.Badge.infoBackground, UIColors.Badge.infoText, UIColors.Badge.infoBorder, "Sledgehammer" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case EisbachMissing => (UIColors.Badge.accentBackground, UIColors.Badge.accentText, UIColors.Badge.accentBorder, "Eisbach not imported")
  }

  def createBadgePanel(badge: BadgeType): JPanel = {
    val (bgColor, textColor, borderColor, text) = badgeInfo(badge)

    // Create rounded panel with light-tinted modern styling
    val roundedPanel = new JPanel() {
      override def paintComponent(g: java.awt.Graphics): Unit = {
        val g2 = g.asInstanceOf[java.awt.Graphics2D]
        g2.setRenderingHint(java.awt.RenderingHints.KEY_ANTIALIASING, java.awt.RenderingHints.VALUE_ANTIALIAS_ON)
        // Fill background
        g2.setColor(Color.decode(bgColor))
        g2.fillRoundRect(0, 0, getWidth - 1, getHeight - 1, 4, 4)
        // Draw border
        g2.setColor(Color.decode(borderColor))
        g2.drawRoundRect(0, 0, getWidth - 1, getHeight - 1, 4, 4)
      }
    }
    roundedPanel.setLayout(new FlowLayout(FlowLayout.CENTER, 0, 0))
    roundedPanel.setOpaque(false)

    val label = new JLabel(text)
    label.setFont(UIManager.getFont("Label.font").deriveFont(Font.PLAIN, 11f))
    label.setForeground(Color.decode(textColor))
    label.setBorder(BorderFactory.createEmptyBorder(4, 10, 4, 10))
    label.setOpaque(false)

    roundedPanel.add(label)

    val containerPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 10, 6))
    containerPanel.add(roundedPanel)
    containerPanel
  }
}
