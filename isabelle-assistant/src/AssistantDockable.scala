/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import java.awt.{BorderLayout, CardLayout, Color, FlowLayout}
import javax.swing.{
  BorderFactory,
  JButton,
  JEditorPane,
  JLabel,
  JOptionPane,
  JPanel,
  JScrollPane,
  JTextArea,
  JWindow
}
import javax.swing.event.{HyperlinkEvent, HyperlinkListener}

import isabelle._
import isabelle.jedit._
import org.gjt.sp.jedit.View

/** Singleton companion for the Assistant dockable panel. Manages the single
  * instance, insert-action registry, cancellation state, and provides
  * thread-safe methods for updating the UI from background threads.
  */
object AssistantDockable {
  private val insertActions =
    new java.util.concurrent.ConcurrentHashMap[String, () => Unit]()
  private val insertActionOrder =
    new java.util.concurrent.ConcurrentLinkedDeque[String]()
  private val insertActionsLock = new Object()
  private val maxInsertActions = AssistantConstants.MAX_INSERT_ACTIONS
  @volatile private var _cancelled = false
  @volatile private var _busy = false
  @volatile private var _busyStartTime = 0L

  def isCancelled: Boolean = _cancelled

  def cancel(): Unit = {
    _cancelled = true
    _busy = false
    setStatus(AssistantConstants.STATUS_CANCELLED)
  }

  def resetCancel(): Unit = { _cancelled = false }

  /** Clear all registered insert actions. Thread-safe with atomic clear. */
  def clearInsertActions(): Unit = insertActionsLock.synchronized {
    insertActions.clear()
    insertActionOrder.clear()
  }

  /** Register an insert action and return its ID for use in hyperlinks.
    * Synchronized to ensure HashMap and Deque operations are atomic.
    */
  def registerAction(action: () => Unit): String =
    insertActionsLock.synchronized {
      val id = java.util.UUID.randomUUID().toString.take(8)
      insertActions.put(id, action)
      insertActionOrder.addLast(id)
      // Evict oldest entries if we exceed the limit
      while (insertActions.size > maxInsertActions) {
        val oldest = insertActionOrder.pollFirst()
        if (oldest != null) {
          val _ = insertActions.remove(oldest)
        }
      }
      id
    }

  /** Add a chat response with optional clickable insert link */
  def respondInChat(
      text: String,
      insertCode: Option[(String, () => Unit)] = None
  ): Unit = {
    val content = insertCode match {
      case Some((code, action)) =>
        val id = registerAction(action)
        s"$text\n\n```action:$id\n$code\n```"
      case None => text
    }
    ChatAction.addMessage(ChatAction.Assistant, content)
    showConversation(ChatAction.getHistory)
  }

  def showConversation(history: List[ChatAction.Message]): Unit =
    AssistantEventBus.publish(AssistantEvent.ShowConversation(history))

  def setStatus(status: String): Unit =
    setStatus(AssistantStatus.fromText(status))

  def setStatus(status: AssistantStatus): Unit = {
    val statusText = status.text
    val wasBusy = _busy
    _busy =
      statusText != AssistantConstants.STATUS_READY && statusText != AssistantConstants.STATUS_CANCELLED && !statusText
        .startsWith("Error")
    if (_busy && !wasBusy) _busyStartTime = System.currentTimeMillis()
    AssistantEventBus.publish(AssistantEvent.StatusUpdate(status))
  }

  def setBadge(badge: VerificationBadge.BadgeType): Unit =
    AssistantEventBus.publish(AssistantEvent.BadgeUpdate(badge))

  def refreshIQStatus(): Unit =
    AssistantEventBus.publish(AssistantEvent.IQStatusRefresh())

  def refreshModelLabel(): Unit =
    AssistantEventBus.publish(AssistantEvent.ModelLabelRefresh())

  /** Global teardown hook used from plugin stop to avoid leaked dockable
    * state/subscriptions.
    */
  def shutdown(): Unit = {
    // Notify bus that dockable is effectively dead by pushing cancelled status?
    // In event-bus architecture, instances clean themselves up. We just clear
    // the static state actions.
    synchronized {
      clearInsertActions()
      _cancelled = false
      _busy = false
      _busyStartTime = 0L
    }
  }
}

/** Chat UI panel docked in Isabelle/jEdit. Renders conversation history as
  * styled HTML, provides chat input with keyboard shortcuts, status indicators
  * for I/Q and model, and clickable insert links for generated code.
  */
class AssistantDockable(view: View, position: String)
    extends Dockable(view, position) {

  private val eventBusListener: AssistantEvent => Unit = {
    case AssistantEvent.StatusUpdate(status) =>
      GUI_Thread.later { updateStatus(status.text) }
    case AssistantEvent.BadgeUpdate(badge) =>
      GUI_Thread.later { updateBadge(badge) }
    case AssistantEvent.ShowConversation(history) =>
      GUI_Thread.later { displayConversation(history) }
    case AssistantEvent.IQStatusRefresh() =>
      GUI_Thread.later { updateAssistantStatus() }
    case AssistantEvent.ModelLabelRefresh() =>
      GUI_Thread.later { updateModelLabel() }
    case _ => // Optional Catch-all
  }
  AssistantEventBus.subscribe(eventBusListener)

  private[this] val statusSubscription =
    AssistantStatusSubscription.create(
      PIDE.session,
      s"assistant-status-${System.identityHashCode(this)}",
      _ => GUI_Thread.later { updateAssistantStatus() }
    )
  @volatile private[this] var disposed = false

  MarkdownRenderer.setSyntheticImageReadyCallback(() => {
    if (!disposed) AssistantDockable.showConversation(ChatAction.getHistory)
  })

  // Display state — MUST be declared before initializeUI() runs
  private val displayLock = new Object()
  @volatile private var renderedMessageCount = 0
  @volatile private var welcomeShown = false

  // Input history navigation
  private var inputHistory: List[String] = Nil       // Oldest → newest
  private var inputHistoryIndex: Int = -1             // -1 = not browsing
  private var savedDraft: String = ""                 // Draft saved when user starts browsing
  @volatile private var lastEscapeTime: Long = 0L     // For double-tap Escape

  // UI Components
  private val badgeContainer = createBadgeContainer()
  private val htmlPane = createHtmlPane()
  private val cardLayout = new CardLayout()
  private val contentPanel = createContentPanel()
  private val mainPanel = createMainPanel()
  private val (iqStatusLabel, modelLabel) = createStatusLabels()
  private val contextBar = new ContextBarPanel()
  private val (statusLabel, cancelButton, clearButton) = createControlElements()
  private val topPanel = createTopPanel()
  private val (chatInput, sendButton, inputPanel) = createInputPanel()

  // Completion popup state
  private var completionWindow: Option[JWindow] = None
  private var completionList: Option[javax.swing.JList[String]] = None
  private var filteredCompletions: Array[String] = Array.empty

  // Initialize UI
  initializeUI()
  initializeEventHandlers()

  private def createBadgeContainer(): JPanel = {
    val container = new JPanel(new BorderLayout())
    container.setVisible(false)
    container.setBorder(
      BorderFactory.createMatteBorder(
        0,
        0,
        1,
        0,
        javax.swing.UIManager.getColor("Separator.foreground")
      )
    )
    container
  }

  private def createHtmlPane(): JEditorPane = {
    val pane = new JEditorPane()
    pane.setEditorKit(new SyntheticImageAwareEditorKit())
    pane.setEditable(false)
    pane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, true)
    pane.addHyperlinkListener(new HyperlinkListener {
      def hyperlinkUpdate(e: HyperlinkEvent): Unit = {
        if (e.getEventType == HyperlinkEvent.EventType.ACTIVATED) {
          val desc = e.getDescription
          if (desc != null && desc.startsWith("action:insert:")) {
            val id = desc.stripPrefix("action:insert:")
            val action = AssistantDockable.insertActions.get(id)
            if (action != null) action()
          } else if (desc != null && desc.startsWith("action:copy:")) {
            val encoded = desc.stripPrefix("action:copy:")
            val text = java.net.URLDecoder.decode(encoded, "UTF-8")
            val clipboard =
              java.awt.Toolkit.getDefaultToolkit.getSystemClipboard
            clipboard.setContents(
              new java.awt.datatransfer.StringSelection(text),
              null
            )
          }
        }
      }
    })
    pane
  }

  private def createContentPanel(): JPanel = {
    val panel = new JPanel(cardLayout)
    panel.add(new JScrollPane(htmlPane), "html")
    panel
  }

  private def createMainPanel(): JPanel = {
    val panel = new JPanel(new BorderLayout())
    panel.add(badgeContainer, BorderLayout.NORTH)
    panel.add(contentPanel, BorderLayout.CENTER)
    panel
  }

  private def createStatusLabels(): (JLabel, JLabel) = {
    val iqStatus = new JLabel("I/Q: Unknown")
    iqStatus.setOpaque(true)
    iqStatus.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))

    val model = new JLabel("Model: Loading...")
    model.setBorder(BorderFactory.createEmptyBorder(2, 4, 2, 4))

    (iqStatus, model)
  }


  /** Apply consistent top-bar button styling (font, border, background, hover).
    */
  private def styleTopButton(btn: JButton): Unit = {
    btn.setFocusPainted(true)
    btn.setFont(btn.getFont.deriveFont(11f))
    btn.setBorder(
      BorderFactory.createCompoundBorder(
        BorderFactory.createLineBorder(
          java.awt.Color.decode(UIColors.TopButton.border),
          1,
          true
        ),
        BorderFactory.createEmptyBorder(2, 8, 2, 8)
      )
    )
    btn.setBackground(java.awt.Color.decode(UIColors.TopButton.background))
    btn.setForeground(javax.swing.UIManager.getColor("Button.foreground"))
    btn.setCursor(
      java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR)
    )
    btn.addMouseListener(new java.awt.event.MouseAdapter {
      override def mouseEntered(e: java.awt.event.MouseEvent): Unit =
        btn.setBackground(
          java.awt.Color.decode(UIColors.TopButton.hoverBackground)
        )
      override def mouseExited(e: java.awt.event.MouseEvent): Unit =
        btn.setBackground(java.awt.Color.decode(UIColors.TopButton.background))
    })
  }

  private def createControlElements(): (JLabel, JButton, JButton) = {
    val status = new JLabel(AssistantConstants.STATUS_READY)

    val cancel = new JButton("Cancel")
    cancel.setVisible(false)
    styleTopButton(cancel)

    val clear = new JButton("Clear")
    styleTopButton(clear)

    (status, cancel, clear)
  }

  private def createTopPanel(): JPanel = {
    val panel = new JPanel(new BorderLayout())
    val leftPanel = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 2))
    leftPanel.add(iqStatusLabel)
    leftPanel.add(modelLabel)
    leftPanel.add(contextBar)

    val rightPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT))
    rightPanel.add(statusLabel)
    rightPanel.add(cancelButton)
    rightPanel.add(clearButton)

    panel.add(leftPanel, BorderLayout.WEST)
    panel.add(rightPanel, BorderLayout.EAST)
    panel
  }

  private def createInputPanel(): (JTextArea, JButton, JPanel) = {
    val input = new JTextArea(
      AssistantConstants.CHAT_INPUT_ROWS,
      AssistantConstants.CHAT_INPUT_COLUMNS
    )
    input.setLineWrap(true)
    input.setWrapStyleWord(true)
    input.setFont(javax.swing.UIManager.getFont("TextField.font"))
    input.setBorder(BorderFactory.createEmptyBorder(8, 12, 8, 40)) // Right padding for send button
    input.setBackground(Color.decode(UIColors.ChatInput.background))

    // Placeholder label overlay (shows "Ask a question..." when empty)
    val placeholder = new JLabel(AssistantConstants.CHAT_INPUT_PLACEHOLDER)
    placeholder.setFont(input.getFont)
    placeholder.setForeground(Color.decode(UIColors.ChatInput.placeholder))
    placeholder.setVisible(input.getText.isEmpty)

    // Update placeholder visibility based on text content
    input.getDocument.addDocumentListener(
      new javax.swing.event.DocumentListener {
        def insertUpdate(e: javax.swing.event.DocumentEvent): Unit =
          placeholder.setVisible(input.getText.isEmpty)
        def removeUpdate(e: javax.swing.event.DocumentEvent): Unit =
          placeholder.setVisible(input.getText.isEmpty)
        def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {}
      }
    )
    input.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusGained(e: java.awt.event.FocusEvent): Unit =
        placeholder.setVisible(false)
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        placeholder.setVisible(input.getText.isEmpty)
    })

    // Modern circular send button with Unicode arrow (➤)
    val send = new JButton("➤")
    send.setToolTipText("Send message (Enter)")
    send.setFont(send.getFont.deriveFont(java.awt.Font.BOLD, 16f))
    send.setPreferredSize(new java.awt.Dimension(32, 32))
    send.setMinimumSize(new java.awt.Dimension(32, 32))
    send.setMaximumSize(new java.awt.Dimension(32, 32))
    send.setMargin(new java.awt.Insets(0, 0, 0, 0))
    send.setFocusable(true)
    send.setContentAreaFilled(false)
    send.setForeground(Color.decode(UIColors.ChatInput.sendButton))
    send.setBorder(BorderFactory.createEmptyBorder())
    send.setCursor(
      java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR)
    )
    
    // Hover effect for send button
    send.addMouseListener(new java.awt.event.MouseAdapter {
      override def mouseEntered(e: java.awt.event.MouseEvent): Unit = {
        send.setOpaque(true)
        send.setBackground(Color.decode(UIColors.ChatInput.sendButtonHoverBackground))
        send.setForeground(Color.decode(UIColors.ChatInput.sendButtonHover))
      }
      override def mouseExited(e: java.awt.event.MouseEvent): Unit = {
        send.setOpaque(false)
        send.setForeground(Color.decode(UIColors.ChatInput.sendButton))
      }
    })

    // Rounded border with focus ring support
    val normalBorder = BorderFactory.createLineBorder(
      Color.decode(UIColors.ChatInput.border),
      1,
      true
    )
    val focusBorder = BorderFactory.createLineBorder(
      Color.decode(UIColors.ChatInput.focusBorder),
      2,
      true
    )

    val scrollPane = new JScrollPane(input)
    scrollPane.setBorder(normalBorder)
    scrollPane.setVerticalScrollBarPolicy(
      javax.swing.ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED
    )

    // Focus ring - swap border on focus/blur
    input.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusGained(e: java.awt.event.FocusEvent): Unit =
        scrollPane.setBorder(focusBorder)
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        scrollPane.setBorder(normalBorder)
    })

    // Layered panel with overlapping children (placeholder, send button over scroll pane)
    val layered = new JPanel(null) {
      override def isOptimizedDrawingEnabled: Boolean = false // Fix for overlapping repaints
      override def getPreferredSize: java.awt.Dimension =
        scrollPane.getPreferredSize
      override def doLayout(): Unit = {
        val w = getWidth
        val h = getHeight
        scrollPane.setBounds(0, 0, w, h)
        
        // Position placeholder label at top-left with padding matching input
        placeholder.setBounds(12, 8, w - 50, 20)
        
        // Position send button in bottom-right corner
        val bw = send.getPreferredSize.width
        val bh = send.getPreferredSize.height
        send.setBounds(w - bw - 8, h - bh - 8, bw, bh)
      }
    }
    layered.add(placeholder) // overlay on top
    layered.add(send) // overlay on top
    layered.add(scrollPane) // behind

    val panel = new JPanel(new BorderLayout())
    panel.setBorder(BorderFactory.createEmptyBorder(3, 0, 0, 0))
    panel.add(layered, BorderLayout.CENTER)
    (input, send, panel)
  }

  private def initializeUI(): Unit = {
    setupInitialState()
    layoutComponents()
    showWelcomeMessage()
  }

  private def setupInitialState(): Unit = {
    updateAssistantStatus()
    updateModelLabel()
  }

  private def layoutComponents(): Unit = {
    add(topPanel, BorderLayout.NORTH)
    set_content(mainPanel)
    add(inputPanel, BorderLayout.SOUTH)
  }

  private def showWelcomeMessage(): Unit = {
    displayConversation(ChatAction.getHistory)
  }

  private def initializeEventHandlers(): Unit = {
    setupButtonHandlers()
    setupChatInputHandlers()
    setupAccessibilityHandlers()
    setupStatusHandlers()
  }

  private def setupButtonHandlers(): Unit = {
    clearButton.addActionListener(_ => clearChat())
    sendButton.addActionListener(_ => sendChat())
    cancelButton.addActionListener(_ => AssistantDockable.cancel())
  }

  private def setupChatInputHandlers(): Unit = {
    // Non-focus-stealing auto-completion using JWindow
    initializeCompletionPopup()
    
    // Document listener to update completion popup as user types
    chatInput.getDocument.addDocumentListener(
      new javax.swing.event.DocumentListener {
        def insertUpdate(e: javax.swing.event.DocumentEvent): Unit =
          updateCompletionPopup()
        def removeUpdate(e: javax.swing.event.DocumentEvent): Unit =
          updateCompletionPopup()
        def changedUpdate(e: javax.swing.event.DocumentEvent): Unit = {}
      }
    )
    
    // Focus listener to hide popup when input loses focus
    chatInput.addFocusListener(new java.awt.event.FocusAdapter {
      override def focusLost(e: java.awt.event.FocusEvent): Unit =
        hideCompletionPopup()
    })

    val inputMap = chatInput.getInputMap(javax.swing.JComponent.WHEN_FOCUSED)
    val actionMap = chatInput.getActionMap()

    // Use key bindings (instead of KeyListener) for reliable cross-platform handling.
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ENTER"), "send-or-complete")
    // Explicitly map Shift+Enter to insert-break for cross-platform consistency
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("shift ENTER"), "insert-break")

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("ctrl ENTER"), "send")
    inputMap.put(javax.swing.KeyStroke.getKeyStroke("TAB"), "accept-completion")
    
    actionMap.put(
      "send-or-complete",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (isCompletionPopupVisible) acceptSelectedCompletion()
          else sendChat()
        }
      }
    )
    
    actionMap.put(
      "send",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = sendChat()
      }
    )
    
    actionMap.put(
      "accept-completion",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (isCompletionPopupVisible) acceptSelectedCompletion()
        }
      }
    )

    inputMap.put(
      javax.swing.KeyStroke.getKeyStroke("ESCAPE"),
      "cancel-or-clear"
    )
    actionMap.put(
      "cancel-or-clear",
      new javax.swing.AbstractAction() {
        def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
          if (isCompletionPopupVisible) {
            hideCompletionPopup()
          } else {
            val now = System.currentTimeMillis()
            if (AssistantDockable._busy) {
              AssistantDockable.cancel()
            } else if (chatInput.getText.trim.nonEmpty) {
              chatInput.setText("")
              inputHistoryIndex = -1
              savedDraft = ""
              lastEscapeTime = now
            } else if (now - lastEscapeTime < 400) {
              clearChat()
              lastEscapeTime = 0L
            } else {
              // Input already empty, single Esc — still clear conversation for backward compat
              clearChat()
            }
          }
        }
      }
    )

    // Save original caret-up / caret-down actions for delegation
    val originalUp = actionMap.get("caret-up")
    val originalDown = actionMap.get("caret-down")

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("UP"), "completion-or-history-up")
    actionMap.put("completion-or-history-up", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
        if (isCompletionPopupVisible) navigateCompletionUp()
        else if (isCaretOnFirstLine) navigateHistoryBack()
        else if (originalUp != null) originalUp.actionPerformed(e)
      }
    })

    inputMap.put(javax.swing.KeyStroke.getKeyStroke("DOWN"), "completion-or-history-down")
    actionMap.put("completion-or-history-down", new javax.swing.AbstractAction() {
      def actionPerformed(e: java.awt.event.ActionEvent): Unit = {
        if (isCompletionPopupVisible) navigateCompletionDown()
        else if (isCaretOnLastLine) navigateHistoryForward()
        else if (originalDown != null) originalDown.actionPerformed(e)
      }
    })
  }

  /** Initialize the non-focus-stealing completion popup window */
  private def initializeCompletionPopup(): Unit = {
    val window = new javax.swing.JWindow(javax.swing.SwingUtilities.getWindowAncestor(this))
    window.setFocusableWindowState(false)  // Critical: prevents focus stealing
    window.setAlwaysOnTop(true)
    
    val list = new javax.swing.JList[String]()
    list.setSelectionMode(javax.swing.ListSelectionModel.SINGLE_SELECTION)
    list.setVisibleRowCount(8)
    list.setFont(chatInput.getFont)
    
    val scrollPane = new JScrollPane(list)
    scrollPane.setBorder(BorderFactory.createLineBorder(Color.GRAY, 1))
    window.add(scrollPane)
    
    completionWindow = Some(window)
    completionList = Some(list)
  }

  /** Update completion popup based on current input text */
  private def updateCompletionPopup(): Unit = {
    javax.swing.SwingUtilities.invokeLater { () =>
      val text = chatInput.getText
      
      // Only show completions for command prefixes (starts with : and no space yet)
      if (text.startsWith(":") && text.length >= 2 && !text.contains(" ")) {
        val prefix = text.drop(1).toLowerCase
        val commands = ChatAction.commandNames
          .filter(_.startsWith(prefix))
          .sorted
          .take(8)
        
        if (commands.nonEmpty) {
          filteredCompletions = commands.map(":" + _).toArray
          showCompletionPopup(filteredCompletions)
        } else {
          hideCompletionPopup()
        }
      } else {
        hideCompletionPopup()
      }
    }
  }

  /** Show the completion popup with the given completions */
  private def showCompletionPopup(completions: Array[String]): Unit = {
    // Get the position early, fail fast if component not on screen
    val locationOpt = try {
      Some((inputPanel.getLocationOnScreen, inputPanel.getHeight))
    } catch {
      case _: java.awt.IllegalComponentStateException => None
    }
    
    locationOpt.foreach { case (inputLocation, inputHeight) =>
      for {
        window <- completionWindow
        list <- completionList
      } {
        list.setListData(completions)
        list.setSelectedIndex(0)
        
        // Position popup below the input panel
        window.setLocation(inputLocation.x, inputLocation.y + inputHeight)
        
        // Size to fit content
        window.pack()
        val preferredWidth = Math.max(200, inputPanel.getWidth / 2)
        window.setSize(preferredWidth, window.getHeight)
        
        if (!window.isVisible) window.setVisible(true)
      }
    }
  }

  /** Hide the completion popup */
  private def hideCompletionPopup(): Unit = {
    completionWindow.foreach(_.setVisible(false))
  }

  /** Check if completion popup is currently visible */
  private def isCompletionPopupVisible: Boolean = {
    completionWindow.exists(_.isVisible)
  }

  /** Navigate up in the completion list */
  private def navigateCompletionUp(): Unit = {
    completionList.foreach { list =>
      val currentIndex = list.getSelectedIndex
      if (currentIndex > 0) {
        list.setSelectedIndex(currentIndex - 1)
        list.ensureIndexIsVisible(currentIndex - 1)
      }
    }
  }

  /** Navigate down in the completion list */
  private def navigateCompletionDown(): Unit = {
    completionList.foreach { list =>
      val currentIndex = list.getSelectedIndex
      if (currentIndex < list.getModel.getSize - 1) {
        list.setSelectedIndex(currentIndex + 1)
        list.ensureIndexIsVisible(currentIndex + 1)
      }
    }
  }

  /** Accept the currently selected completion */
  private def acceptSelectedCompletion(): Unit = {
    completionList.foreach { list =>
      val selected = list.getSelectedValue
      if (selected != null) {
        chatInput.setText(selected + " ")
        chatInput.setCaretPosition(chatInput.getText.length)
        hideCompletionPopup()
      }
    }
  }

  private def setupAccessibilityHandlers(): Unit = {
    chatInput.getAccessibleContext.setAccessibleName("Chat input")
    chatInput.getAccessibleContext.setAccessibleDescription(
      "Type your message to the Isabelle Assistant. Enter sends, Shift+Enter for newline."
    )

    sendButton.getAccessibleContext.setAccessibleName("Send message")
    sendButton.getAccessibleContext.setAccessibleDescription(
      "Send your message to the AI assistant"
    )

    clearButton.getAccessibleContext.setAccessibleName("Clear conversation")
    clearButton.getAccessibleContext.setAccessibleDescription(
      "Clear the chat history and start fresh"
    )

    cancelButton.getAccessibleContext.setAccessibleName("Cancel operation")
    cancelButton.getAccessibleContext.setAccessibleDescription(
      "Cancel the current in-progress operation"
    )

    htmlPane.getAccessibleContext.setAccessibleName("Conversation display")
    htmlPane.getAccessibleContext.setAccessibleDescription(
      "Shows the conversation history and AI responses"
    )

    statusLabel.getAccessibleContext.setAccessibleName("Status")
    statusLabel.getAccessibleContext.setAccessibleDescription(
      "Current status of the Isabelle Assistant"
    )

    modelLabel.getAccessibleContext.setAccessibleName("Model information")
    modelLabel.getAccessibleContext.setAccessibleDescription(
      "Currently selected AI model"
    )

    iqStatusLabel.getAccessibleContext.setAccessibleName("I/Q status")
    iqStatusLabel.getAccessibleContext.setAccessibleDescription(
      "Status of the I/Q integration"
    )

    setFocusTraversalPolicy(new java.awt.DefaultFocusTraversalPolicy())
    setFocusCycleRoot(true)

    sendButton.setMnemonic('S')
    clearButton.setMnemonic('C')
  }

  private def setupStatusHandlers(): Unit = {
    iqStatusLabel.addMouseListener(new java.awt.event.MouseAdapter() {
      override def mouseClicked(e: java.awt.event.MouseEvent): Unit =
        showAssistantHelp()
    })

    statusSubscription.start()
  }

  private[assistant] def disposeDockable(): Unit = synchronized {
    if (!disposed) {
      disposed = true
      statusSubscription.stop()
      AssistantEventBus.unsubscribe(eventBusListener)
      MarkdownRenderer.setSyntheticImageReadyCallback(() => ())
    }
  }

  override def exit(): Unit = {
    disposeDockable()
    super.exit()
  }

  private def clearChat(): Unit = {
    ChatAction.clearHistory()
    AssistantDockable.clearInsertActions()
    ToolPermissions.clearSession()
    TaskList.clear()
    htmlPane.setText("")
    badgeContainer.setVisible(false)
    welcomeShown = false
    renderedMessageCount = 0
    inputHistory = Nil
    inputHistoryIndex = -1
    savedDraft = ""
    contextBar.reset()
    cardLayout.show(contentPanel, "html")
    chatInput.requestFocus()
  }

  private def isCaretOnFirstLine: Boolean = {
    try {
      val caretPos = chatInput.getCaretPosition
      chatInput.getLineOfOffset(caretPos) == 0
    } catch { case _: Exception => true }
  }

  private def isCaretOnLastLine: Boolean = {
    try {
      val caretPos = chatInput.getCaretPosition
      chatInput.getLineOfOffset(caretPos) == chatInput.getLineCount - 1
    } catch { case _: Exception => true }
  }

  private def navigateHistoryBack(): Unit = {
    if (inputHistory.isEmpty) return
    
    // If we're not currently browsing, save the current draft
    if (inputHistoryIndex == -1) {
      savedDraft = chatInput.getText
      inputHistoryIndex = 0
    } else if (inputHistoryIndex < inputHistory.length - 1) {
      inputHistoryIndex += 1
    } else {
      return // Already at oldest entry
    }
    
    // Index 0 = most recent, so reverse-index into the list
    val entry = inputHistory(inputHistory.length - 1 - inputHistoryIndex)
    chatInput.setText(entry)
    chatInput.setCaretPosition(entry.length)
  }

  private def navigateHistoryForward(): Unit = {
    if (inputHistoryIndex == -1) return // Not browsing
    
    if (inputHistoryIndex > 0) {
      inputHistoryIndex -= 1
      val entry = inputHistory(inputHistory.length - 1 - inputHistoryIndex)
      chatInput.setText(entry)
      chatInput.setCaretPosition(entry.length)
    } else {
      // Back to draft
      inputHistoryIndex = -1
      chatInput.setText(savedDraft)
      chatInput.setCaretPosition(savedDraft.length)
    }
  }

  private val maxInputLength =
    AssistantConstants.MAX_CHAT_CONTEXT_CHARS / 2 // 50K chars max per message

  private def sendChat(): Unit = {
    val message = chatInput.getText.trim
    if (message.nonEmpty) {
      if (message.length > maxInputLength) {
        javax.swing.JOptionPane.showMessageDialog(
          this,
          s"Message too long (${"%,d".format(message.length)} chars, max ${"%,d".format(maxInputLength)}). Please shorten your message.",
          "Isabelle Assistant",
          javax.swing.JOptionPane.WARNING_MESSAGE
        )
      } else {
        chatInput.setText("")
        // Add to input history (avoid consecutive duplicates)
        if (inputHistory.isEmpty || inputHistory.last != message)
          inputHistory = inputHistory :+ message
        inputHistoryIndex = -1
        savedDraft = ""
        AssistantDockable.resetCancel()
        ChatAction.chat(view, message)
      }
    }
  }

  def updateBadge(badge: VerificationBadge.BadgeType): Unit = {
    badgeContainer.removeAll()
    badgeContainer.add(
      VerificationBadge.createBadgePanel(badge),
      BorderLayout.CENTER
    )
    badgeContainer.setVisible(true)
    badgeContainer.revalidate()
    badgeContainer.repaint()
    statusLabel.setText(VerificationBadge.toStatus(badge))
  }

  /** Render a single chat message to HTML. Shared by incremental and full render. */
  private def renderSingleMessage(
      msg: ChatAction.Message,
      registerAction: String => String
  ): String = {
    msg.role match {
      case ChatAction.User =>
        ConversationRenderer.createUserMessageHtml(
          msg.content,
          ChatAction.formatTime(msg.timestamp)
        )
      case ChatAction.Widget =>
        msg.content // Widget role: raw HTML, no wrapper
      case ChatAction.Tool =>
        // Parse tool message content: "toolName|||{json params}"
        val parts = msg.content.split("\\|\\|\\|", 2)
        if (parts.length == 2) {
          try {
            val toolName = parts(0)
            val paramsJson = parts(1)
            val params =
              ResponseParser.parseToolArgsJsonObject(paramsJson)
            ConversationRenderer.createToolMessageHtml(
              toolName,
              params,
              ChatAction.formatTime(msg.timestamp)
            )
          } catch {
            case _: Exception =>
              ConversationRenderer.createAssistantMessageHtml(
                msg.content,
                ChatAction.formatTime(msg.timestamp),
                msg.rawHtml,
                registerAction
              )
          }
        } else
          ConversationRenderer.createAssistantMessageHtml(
            msg.content,
            ChatAction.formatTime(msg.timestamp),
            msg.rawHtml,
            registerAction
          )
      case _ =>
        ConversationRenderer.createAssistantMessageHtml(
          msg.content,
          ChatAction.formatTime(msg.timestamp),
          msg.rawHtml,
          registerAction
        )
    }
  }

  def displayConversation(history: List[ChatAction.Message]): Unit =
    displayLock.synchronized {
      badgeContainer.setVisible(false)

      val welcome = if (history.isEmpty && !welcomeShown) {
        welcomeShown = true
        ConversationRenderer.createWelcomeHtml(() => 
          AssistantDockable.registerAction(() => ChatAction.chat(view, ":help"))
        )
      } else ""

      // Incremental append: if we have a prefix match, append only new messages
      // Synchronized to prevent concurrent updates from desynchronizing count vs. DOM
      val canIncrement =
        renderedMessageCount > 0 && history.length > renderedMessageCount

      if (canIncrement) {
        val registerAction = (code: String) =>
          AssistantDockable.registerAction(
            InsertHelper.createInsertAction(view, code)
          )
        val newMessages = history.drop(renderedMessageCount)
        val newHtml = newMessages.map(renderSingleMessage(_, registerAction)).mkString

        val doc =
          htmlPane.getDocument.asInstanceOf[javax.swing.text.html.HTMLDocument]
        try {
          val root = doc.getDefaultRootElement
          var body: javax.swing.text.Element = null
          for (i <- 0 until root.getElementCount if body == null) {
            val child = root.getElement(i)
            if (child.getName == "body") body = child
          }
          if (body != null) {
            doc.insertBeforeEnd(body, newHtml)
            renderedMessageCount = history.length
          } else {
            fullRender(history, welcome)
          }
        } catch {
          case _: Exception => fullRender(history, welcome)
        }
      } else {
        fullRender(history, welcome)
      }

      // Update context bar
      updateContextBar(history)

      javax.swing.SwingUtilities.invokeLater(() =>
        htmlPane.setCaretPosition(htmlPane.getDocument.getLength)
      )
      cardLayout.show(contentPanel, "html")
    }

  private def fullRender(
      history: List[ChatAction.Message],
      welcome: String
  ): Unit = {
    val registerAction = (code: String) =>
      AssistantDockable.registerAction(
        InsertHelper.createInsertAction(view, code)
      )
    val htmlContent = history.map(renderSingleMessage(_, registerAction)).mkString

    val fullHtml = s"""<html><head><style>
      |body { font-family: 'Segoe UI', 'Helvetica Neue', sans-serif; font-size: 12pt;
      |       margin: 0; padding: 8px; overflow-x: hidden; }
      |a { color: ${UIColors.linkColor}; text-decoration: none; }
      |a:hover { text-decoration: underline; }
      |img { max-width: 100%; }
      |table { max-width: 100%; }
      |pre { max-width: 100%; overflow-x: auto; }
      |</style></head><body>$welcome$htmlContent</body></html>""".stripMargin

    htmlPane.setText(fullHtml)
    renderedMessageCount = history.length
  }

  def updateStatus(status: String): Unit = {
    val displayStatus =
      if (AssistantDockable._busy && AssistantDockable._busyStartTime > 0) {
        val elapsed =
          (System.currentTimeMillis() - AssistantDockable._busyStartTime) / 1000
        if (elapsed >= 2) s"$status (${elapsed}s)" else status
      } else status

    // Add colored dot indicator based on status
    val (dot, color) =
      if (status.startsWith("Error") || status.startsWith("[FAIL]")) {
        ("●", UIColors.StatusDot.error)
      } else if (
        status == AssistantConstants.STATUS_READY || status == AssistantConstants.STATUS_CANCELLED
      ) {
        ("●", UIColors.StatusDot.ready)
      } else {
        ("●", UIColors.StatusDot.busy)
      }

    // Create HTML with colored dot
    val htmlStatus =
      s"<html><span style='color:$color;'>$dot</span> $displayStatus</html>"
    statusLabel.setText(htmlStatus)
    cancelButton.setVisible(AssistantDockable._busy)
  }

  def updateAssistantStatus(): Unit = {
    val buffer = view.getBuffer
    val status = AssistantSupport.getStatus(buffer)
    // Use modern light-tinted badge style instead of solid color blocks
    val (bgColor, textColor, borderColor) = status match {
      case AssistantSupport.FullSupport =>
        (
          UIColors.Badge.successBackground,
          UIColors.Badge.successText,
          UIColors.Badge.successBorder
        )
      case AssistantSupport.PartialSupport =>
        (
          UIColors.Badge.warningBackground,
          UIColors.Badge.warningText,
          UIColors.Badge.warningBorder
        )
      case AssistantSupport.NoSupport =>
        (
          UIColors.Badge.neutralBackground,
          UIColors.Badge.neutralText,
          UIColors.Badge.neutralBorder
        )
    }
    iqStatusLabel.setBackground(Color.decode(bgColor))
    iqStatusLabel.setForeground(Color.decode(textColor))
    iqStatusLabel.setBorder(
      BorderFactory.createCompoundBorder(
        BorderFactory.createLineBorder(Color.decode(borderColor), 1, true),
        BorderFactory.createEmptyBorder(3, 8, 3, 8)
      )
    )
    iqStatusLabel.setText(AssistantSupport.statusText(status))
  }

  private def showAssistantHelp(): Unit = {
    val buffer = view.getBuffer
    JOptionPane.showMessageDialog(
      this,
      AssistantSupport.helpText(buffer),
      "Isabelle Assistant Help",
      JOptionPane.INFORMATION_MESSAGE
    )
  }

  def updateModelLabel(): Unit = {
    val modelId = AssistantOptions.getModelId
    val (display, tooltip) = if (modelId.nonEmpty) {
      // Strip CRIS prefix (us./eu./ap.) and provider prefix, show the model name portion
      val stripped =
        if (modelId.matches("^(us|eu|ap)\\..*"))
          modelId.dropWhile(_ != '.').drop(1)
        else modelId
      val afterProvider =
        if (stripped.contains("."))
          stripped.substring(stripped.indexOf('.') + 1)
        else stripped
      val shortName = HtmlUtil.escapeHtml(afterProvider.take(30))
      val escapedModelId = HtmlUtil.escapeHtml(modelId)
      val mutedColor = UIColors.ModelLabel.muted
      (
        s"<html><span style='color:$mutedColor;font-size:10pt;'>Model:</span> <b style='font-size:10pt;'>$shortName</b></html>",
        s"Model: $escapedModelId"
      )
    } else {
      val mutedColor = UIColors.ModelLabel.muted
      val unconfiguredColor = UIColors.ModelLabel.unconfigured
      (
        s"<html><span style='color:$mutedColor;font-size:10pt;'>Model:</span> <b style='font-size:10pt;color:$unconfiguredColor;'>Not configured</b></html>",
        "No model configured — use :set model <id>"
      )
    }
    modelLabel.setText(display)
    modelLabel.setToolTipText(tooltip)
  }

  override def focusOnDefaultComponent(): Unit = chatInput.requestFocus()

  /** Update the context bar with current conversation usage. */
  private def updateContextBar(history: List[ChatAction.Message]): Unit = {
    try {
      val modelId = AssistantOptions.getModelId
      val usage = ContextTracker.calculate(history, modelId)
      contextBar.updateUsage(usage)
    } catch {
      case ex: Exception =>
        Output.warning(s"[Assistant] Failed to update context bar: ${ex.getMessage}")
    }
  }
}

/** Custom panel for displaying context usage as a progress bar.
  * 
  * Shows token usage with semantic color coding (green → amber → red).
  * Displays both percentage and fraction (e.g., "68% ~14K/200K").
  * Click to show detailed breakdown in chat.
  */
class ContextBarPanel extends JPanel {
  private var usage: Option[ContextTracker.ContextUsage] = None
  
  setPreferredSize(new java.awt.Dimension(160, 20))
  setMinimumSize(new java.awt.Dimension(140, 20))
  setMaximumSize(new java.awt.Dimension(180, 20))
  setOpaque(false)
  setCursor(java.awt.Cursor.getPredefinedCursor(java.awt.Cursor.HAND_CURSOR))
  
  // Click to show detailed stats in chat
  addMouseListener(new java.awt.event.MouseAdapter {
    override def mouseClicked(e: java.awt.event.MouseEvent): Unit = {
      usage.foreach { u =>
        val details = s"""**Context Usage Details**
          |
          |* Used: ~${ContextTracker.formatThousands(u.usedTokens)} tokens
          |* Model limit: ~${ContextTracker.formatThousands(u.maxTokens)} tokens
          |* Budget limit: ~${ContextTracker.formatThousands(u.budgetTokens)} tokens (internal)
          |* Messages: ${u.messageCount} total${if (u.truncatedCount > 0) s", ${u.truncatedCount} truncated" else ""}
          |* System prompt: ~${ContextTracker.formatThousands(u.systemPromptTokens)} tokens
          |* Percentage: ${(u.percentage * 100).toInt}%
          |
          |**Note:** Token estimates use a ~3.5 chars/token heuristic. Actual usage may vary slightly.
          |Context management will be improved in future updates with auto-compaction.""".stripMargin
        ChatAction.addResponse(details)
      }
    }
  })
  
  override def paintComponent(g: java.awt.Graphics): Unit = {
    super.paintComponent(g)
    val g2 = g.asInstanceOf[java.awt.Graphics2D]
    g2.setRenderingHint(
      java.awt.RenderingHints.KEY_ANTIALIASING,
      java.awt.RenderingHints.VALUE_ANTIALIAS_ON
    )
    
    val w = getWidth
    val h = getHeight
    val radius = 4
    
    // Background track
    g2.setColor(java.awt.Color.decode(UIColors.ContextBar.background))
    g2.fillRoundRect(0, 0, w, h, radius, radius)
    
    // Border
    g2.setColor(java.awt.Color.decode(UIColors.ContextBar.border))
    g2.drawRoundRect(0, 0, w - 1, h - 1, radius, radius)
    
    usage.foreach { u =>
      val pct = u.percentage
      if (pct > 0) {
        // Determine fill color based on percentage
        val fillColor = if (pct < 0.60) {
          UIColors.ContextBar.fillHealthy
        } else if (pct < 0.85) {
          UIColors.ContextBar.fillWarning
        } else {
          UIColors.ContextBar.fillDanger
        }
        
        g2.setColor(java.awt.Color.decode(fillColor))
        val fillWidth = math.min(w - 2, ((w - 2) * pct).toInt)
        g2.fillRoundRect(1, 1, fillWidth, h - 2, radius - 1, radius - 1)
      }
      
      // Text overlay: "68% ~14K/200K"
      val text = s"${u.formatPercentage} ~${ContextTracker.formatThousands(u.usedTokens)}/${ContextTracker.formatThousands(u.maxTokens)}"
      g2.setColor(java.awt.Color.decode(UIColors.ContextBar.text))
      g2.setFont(g2.getFont.deriveFont(9f))
      val fm = g2.getFontMetrics
      val textWidth = fm.stringWidth(text)
      val textHeight = fm.getHeight
      val x = (w - textWidth) / 2
      val y = (h + textHeight) / 2 - fm.getDescent
      g2.drawString(text, x, y)
    }
  }
  
  /** Update the context bar with new usage data */
  def updateUsage(newUsage: ContextTracker.ContextUsage): Unit = {
    usage = Some(newUsage)
    setToolTipText(newUsage.formatTooltip)
    repaint()
  }
  
  /** Reset the context bar to empty state */
  def reset(): Unit = {
    usage = None
    setToolTipText(null)
    repaint()
  }
}

/** HTMLEditorKit that resolves synthetic image URLs (latex://, mermaid://)
  * from MarkdownRenderer's
  * cache.
  */
class SyntheticImageAwareEditorKit extends javax.swing.text.html.HTMLEditorKit {
  override def getViewFactory: javax.swing.text.ViewFactory =
    new SyntheticImageViewFactory(super.getViewFactory)
}

class SyntheticImageViewFactory(delegate: javax.swing.text.ViewFactory)
    extends javax.swing.text.ViewFactory {
  def create(elem: javax.swing.text.Element): javax.swing.text.View = {
    val kind = elem.getName
    if (kind != null && kind.equalsIgnoreCase("img")) {
      val src = elem.getAttributes.getAttribute(
        javax.swing.text.html.HTML.Attribute.SRC
      )
      if (src != null && MarkdownRenderer.isSyntheticImageUrl(src.toString)) {
        new SyntheticImageView(elem)
      } else delegate.create(elem)
    } else delegate.create(elem)
  }
}

class SyntheticImageView(elem: javax.swing.text.Element)
    extends javax.swing.text.View(elem) {
  private val src = elem.getAttributes
    .getAttribute(javax.swing.text.html.HTML.Attribute.SRC)
    .toString

  private def currentImage: java.awt.Image =
    MarkdownRenderer.getCachedImage(src).orNull

  override def getPreferredSpan(axis: Int): Float = {
    val img = currentImage
    if (img == null) 0f
    else if (axis == javax.swing.text.View.X_AXIS) img.getWidth(null).toFloat
    else img.getHeight(null).toFloat
  }

  override def getMinimumSpan(axis: Int): Float = getPreferredSpan(axis)
  override def getMaximumSpan(axis: Int): Float = getPreferredSpan(axis)

  override def paint(g: java.awt.Graphics, allocation: java.awt.Shape): Unit = {
    val img = currentImage
    if (img != null) {
      val rect = allocation.getBounds
      val _ = g.drawImage(img, rect.x, rect.y, null)
    }
  }

  override def modelToView(
      pos: Int,
      a: java.awt.Shape,
      bias: javax.swing.text.Position.Bias
  ): java.awt.Shape = {
    val rect = a.getBounds
    if (pos <= getStartOffset)
      new java.awt.Rectangle(rect.x, rect.y, 0, rect.height)
    else new java.awt.Rectangle(rect.x + rect.width, rect.y, 0, rect.height)
  }

  override def viewToModel(
      x: Float,
      y: Float,
      a: java.awt.Shape,
      biasReturn: Array[javax.swing.text.Position.Bias]
  ): Int = {
    val rect = a.getBounds
    biasReturn(0) = javax.swing.text.Position.Bias.Forward
    if (x < rect.x + rect.width / 2) getStartOffset else getEndOffset
  }
}
