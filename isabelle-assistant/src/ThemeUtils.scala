/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt.Color

/**
 * Shared theme detection and color utilities.
 * Centralizes dark/light theme detection that was previously duplicated
 * across AssistantDockable, VerificationBadge, ChatAction, AssistantSupport,
 * and MarkdownRenderer.
 */
object ThemeUtils {
  /** Brightness threshold below which we consider the theme "dark". */
  private val DARK_THEME_THRESHOLD = 384

  /** Detect whether the current Look-and-Feel uses a dark theme.
   *  Based on the Panel.background RGB sum. */
  def isDark: Boolean = {
    val uiBase = javax.swing.UIManager.getColor("Panel.background")
    uiBase != null && uiBase.getRed + uiBase.getGreen + uiBase.getBlue < DARK_THEME_THRESHOLD
  }

  /** Pick a color based on the current theme. */
  def themed(dark: Color, light: Color): Color =
    if (isDark) dark else light

  /** Pick a hex color string based on the current theme. */
  def themedHex(dark: String, light: String): String =
    if (isDark) dark else light

  // --- Common color constants ---

  /** Verified / success green. */
  def successColor: Color = themed(new Color(129, 199, 132), new Color(76, 175, 80))

  /** Failed / error red. */
  def errorColor: Color = themed(new Color(239, 120, 120), new Color(244, 67, 54))

  /** Unverified / warning orange. */
  def warningColor: Color = themed(new Color(255, 183, 77), new Color(255, 152, 0))

  /** Neutral / disabled gray. */
  def neutralColor: Color = themed(new Color(189, 189, 189), new Color(158, 158, 158))

  /** Sledgehammer / info blue. */
  def infoColor: Color = themed(new Color(100, 181, 246), new Color(33, 150, 243))

  /** Eisbach missing / accent orange. */
  def accentColor: Color = themed(new Color(255, 138, 101), new Color(255, 87, 34))
}