/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.copilot

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
    case Verified(_) => CopilotConstants.STATUS_READY
    case Failed(_) => CopilotConstants.STATUS_READY
    case Unverified => CopilotConstants.STATUS_READY
    case Verifying => CopilotConstants.STATUS_VERIFYING
    case Sledgehammer(_) => CopilotConstants.STATUS_READY
    case EisbachMissing => CopilotConstants.STATUS_READY
  }

  private def badgeInfo(badge: BadgeType): (Color, String) = badge match {
    case Verified(t) => (ThemeUtils.successColor, "[ok] Verified" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case Failed(r) => (ThemeUtils.errorColor, "[FAIL] Failed" + (if (r.nonEmpty) s": ${r.take(40)}" else ""))
    case Unverified => (ThemeUtils.warningColor, "[?] Unverified")
    case Verifying => (ThemeUtils.neutralColor, "[...] Verifying...")
    case Sledgehammer(t) => (ThemeUtils.infoColor, "[sledgehammer] Sledgehammer" + t.map(ms => s" (${ms}ms)").getOrElse(""))
    case EisbachMissing => (ThemeUtils.accentColor, "[!] Eisbach not imported")
  }

  def createBadgePanel(badge: BadgeType): JPanel = {
    val (color, text) = badgeInfo(badge)

    val panel = new JPanel()
    panel.setLayout(new FlowLayout(FlowLayout.LEFT, 8, 6))

    val label = new JLabel(" " + text + " ")
    label.setFont(UIManager.getFont("Label.font").deriveFont(Font.BOLD, 12f))
    label.setForeground(Color.WHITE)
    label.setBackground(color)
    label.setOpaque(true)
    label.setBorder(BorderFactory.createEmptyBorder(6, 12, 6, 12))

    panel.add(label)
    panel
  }
}
