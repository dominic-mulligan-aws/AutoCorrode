/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Centralized theme-aware color constants for UI components.
 * All colors are defined as (dark theme, light theme) pairs and resolved
 * via ThemeUtils at runtime.
 * 
 * Color schemes are designed to:
 * - Provide sufficient contrast in both light and dark themes
 * - Use semantic colors (green=success, red=error, etc.)
 * - Maintain visual consistency across the plugin UI
 * - Support accessibility requirements (WCAG 2.1 AA minimum)
 */
object UIColors {

  /** Chat bubble colors for message display in the dockable panel. */
  object ChatBubble {
    def userBackground: String = ThemeUtils.themedHex("#2a3a4a", "#e8f0fe")
    def userBorder: String = ThemeUtils.themedHex("#5b9bd5", "#4285f4")
    def userTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
    
    def assistantBackground: String = ThemeUtils.themedHex("#302040", "#f3e8fd")
    def assistantBorder: String = ThemeUtils.themedHex("#8060b0", "#9c27b0")
    def assistantTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
    
    def errorBackground: String = ThemeUtils.themedHex("#4a2020", "#ffebee")
    def errorBorder: String = ThemeUtils.themedHex("#e06060", "#ef5350")
    def errorTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
  }
  
  // Welcome message colors
  object Welcome {
    def background: String = ThemeUtils.themedHex("#3a3520", "#fff8e1")
    def border: String = ThemeUtils.themedHex("#6a6030", "#ffe082")
    def title: String = ThemeUtils.themedHex("#d4b830", "#f57f17")
    def text: String = ThemeUtils.themedHex("#c0b890", "#555555")
    def muted: String = ThemeUtils.themedHex("#888070", "#888888")
    def codeBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
    def linkColor: String = ThemeUtils.themedHex("#b090d0", "#7b1fa2")
  }
  
  // Error/warning box colors
  object ErrorBox {
    def background: String = ThemeUtils.themedHex("#4a2020", "#ffebee")
    def border: String = ThemeUtils.themedHex("#804040", "#ef9a9a")
    def text: String = ThemeUtils.themedHex("#e09090", "#c62828")
  }
  
  // Help table colors
  object HelpTable {
    def headerBackground: String = if (ThemeUtils.isDark) "#3a3a3a" else "#f0f0f0"
    def borderColor: String = if (ThemeUtils.isDark) "#555" else "#ccc"
    def rowBorder: String = if (ThemeUtils.isDark) "#444" else "#eee"
    def accentColor: String = if (ThemeUtils.isDark) "#b090d0" else "#7b1fa2"
  }
  
  // Info box colors (for help sections)
  object InfoBox {
    def background: String = if (ThemeUtils.isDark) "#2a3040" else "#f5f5f5"
    def border: String = if (ThemeUtils.isDark) "#4a4a5a" else "#e0e0e0"
  }
  
  // General link color
  def linkColor: String = "#7b1fa2"
  
  // Code block colors for syntax highlighting
  object CodeBlock {
    def background: String = ThemeUtils.themedHex("#2a2a2a", "#f8f8f8")
    def border: String = ThemeUtils.themedHex("#444", "#e0e0e0")
    def actionBackground: String = ThemeUtils.themedHex("#353535", "#f0f0f0")
    def actionBorder: String = ThemeUtils.themedHex("#444", "#e0e0e0")
    def actionLinkBackground: String = ThemeUtils.themedHex("#4a3a5a", "#e8e0f0")
  }
  
  // Inline code background
  def inlineCodeBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
  
  // Table colors
  object Table {
    def border: String = ThemeUtils.themedHex("#555", "#d0d0d0")
    def headerBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
  }
}
