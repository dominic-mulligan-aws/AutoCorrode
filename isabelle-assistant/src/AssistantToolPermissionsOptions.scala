/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import org.gjt.sp.jedit.AbstractOptionPane
import javax.swing.{JComboBox, JButton}

/** Dedicated options pane for configuring assistant tool permissions. */
class AssistantToolPermissionsOptions
    extends AbstractOptionPane("assistant-tool-permissions-options") {

  private val permissionCombos =
    scala.collection.mutable.Map.empty[String, JComboBox[String]]

  override def _init(): Unit = {
    addSeparator("Tool Permissions")

    permissionCombos.clear()

    for (tool <- AssistantTools.tools.sortBy(_.name)) {
      val combo = new JComboBox(ToolPermissions.PermissionLevel.displayOptions)
      val configured =
        ToolPermissions.getConfiguredLevel(tool.name).toDisplayString
      combo.setSelectedItem(configured)

      val displayName = tool.name.split("_").map(_.capitalize).mkString(" ")
      val description = ToolPermissions.getToolDescription(tool.id)
      val tooltipBase = if (tool.name == "ask_user") {
        "This tool allows the assistant to ask you questions. Must always be allowed (locked)."
      } else {
        s"Allows the assistant to $description"
      }
      val tooltip = s"$tooltipBase\nTool ID: ${tool.name}"

      combo.setEnabled(tool.name != "ask_user")
      combo.setToolTipText(tooltip)
      permissionCombos(tool.name) = combo
      addComponent(displayName + ":", combo)
    }

    val resetButton = new JButton("Reset to Defaults")
    resetButton.addActionListener(_ => {
      // Only update UI - don't write to properties until _save() is called
      for (tool <- AssistantTools.tools) {
        permissionCombos.get(tool.name).foreach { combo =>
          val defaultLevel = ToolPermissions.getDefaultLevel(tool.id)
          combo.setSelectedItem(defaultLevel.toDisplayString)
        }
      }
    })
    addComponent("", resetButton)
  }

  override def _save(): Unit = {
    // Iterate over tools in canonical order, not map order
    for (tool <- AssistantTools.tools) {
      permissionCombos.get(tool.name).foreach { combo =>
        val displayLabel =
          Option(combo.getSelectedItem).map(_.toString).getOrElse("Ask at First Use")
        ToolPermissions.PermissionLevel.fromDisplayString(displayLabel).foreach {
          permLevel => ToolPermissions.setConfiguredLevel(tool.name, permLevel)
        }
      }
    }
  }
}
