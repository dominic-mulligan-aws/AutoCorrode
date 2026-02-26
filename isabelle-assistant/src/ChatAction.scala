/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

import isabelle._
import org.gjt.sp.jedit.View
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import scala.jdk.CollectionConverters._

/** Central command dispatcher and chat history manager for the Assistant
  * dockable. Handles 30+ colon-prefixed commands (`:help`, `:suggest`, etc.)
  * and free-form LLM chat. Maintains conversation history with size limits.
  *
  * The dispatch table is the single source of truth for both command execution
  * and help text, preventing drift between the two.
  */
object ChatAction {
  private final case class ChatContextSeed(
      selectedText: Option[String],
      path: Option[String],
      caretOffset: Int
  )

  enum ChatRole(val wireValue: String) {
    case User extends ChatRole("user")
    case Assistant extends ChatRole("assistant")
    case Tool extends ChatRole("tool")
    case Widget extends ChatRole("widget")
  }
  object ChatRole {
    def fromWire(value: String): Option[ChatRole] = value match {
      case "user"      => Some(User)
      case "assistant" => Some(Assistant)
      case "tool"      => Some(Tool)
      case "widget"    => Some(Widget)
      case _           => None
    }
  }
  export ChatRole._

  case class Message(
      role: ChatRole,
      content: String,
      timestamp: LocalDateTime,
      rawHtml: Boolean = false,
      transient: Boolean = false
  )

  // Bounded history using immutable List with lock for thread-safety
  private val maxHistory = AssistantConstants.MAX_ACCUMULATED_MESSAGES
  private val historyLock = new Object()
  @volatile private var history: List[Message] = Nil
  private val timeFmt = DateTimeFormatter.ofPattern("HH:mm")

  /** Command dispatch entry: description for help, handler function, whether
    * I/Q is required.
    */
  private case class CommandEntry(
      description: String,
      handler: (View, String) => Unit,
      needsIQ: Boolean = false
  )

  enum CommandId(val wireName: String) {
    case Analyze extends CommandId("analyze")
    case Deps extends CommandId("deps")
    case Explain extends CommandId("explain")
    case ExplainCounterexample extends CommandId("explain-counterexample")
    case ExplainError extends CommandId("explain-error")
    case Extract extends CommandId("extract")
    case Find extends CommandId("find")
    case GenerateDoc extends CommandId("generate-doc")
    case GenerateElim extends CommandId("generate-elim")
    case GenerateIntro extends CommandId("generate-intro")
    case GenerateTests extends CommandId("generate-tests")
    case Help extends CommandId("help")
    case Models extends CommandId("models")
    case Nitpick extends CommandId("nitpick")
    case PrintContext extends CommandId("print-context")
    case Quickcheck extends CommandId("quickcheck")
    case Read extends CommandId("read")
    case Refactor extends CommandId("refactor")
    case Search extends CommandId("search")
    case Set extends CommandId("set")
    case ShowType extends CommandId("show-type")
    case Sledgehammer extends CommandId("sledgehammer")
    case Suggest extends CommandId("suggest")
    case SuggestName extends CommandId("suggest-name")
    case SuggestStrategy extends CommandId("suggest-strategy")
    case SuggestTactic extends CommandId("suggest-tactic")
    case Summarize extends CommandId("summarize")
    case Theories extends CommandId("theories")
    case Tidy extends CommandId("tidy")
    case Trace extends CommandId("trace")
    case TryMethods extends CommandId("try-methods")
    case Verify extends CommandId("verify")
  }

  object CommandId {
    private val byWire: Map[String, CommandId] =
      values.iterator.map(id => id.wireName -> id).toMap

    def fromWire(wireName: String): Option[CommandId] =
      byWire.get(wireName.trim.toLowerCase)
  }

  /** Expose command names for auto-completion. */
  def commandNames: List[String] =
    dispatch.keysIterator.map(_.wireName).toList.sorted

  /** Single dispatch table — source of truth for both execution and help. */
  private lazy val dispatch: Map[CommandId, CommandEntry] = Map(
    CommandId.Analyze -> CommandEntry(
      "Analyze proof patterns and suggest improvements for proof structure",
      (v, _) => AnalyzePatternsAction.analyze(v)
    ),
    CommandId.Deps -> CommandEntry(
      "Display theory dependencies and imports for a specified theory file",
      (v, a) => TheoryBrowserAction.deps(v, a)
    ),
    CommandId.Explain -> CommandEntry(
      "Provide detailed explanation of Isabelle code at specified location",
      (v, a) => runExplain(v, a)
    ),
    CommandId.ExplainCounterexample -> CommandEntry(
      "Explain why a counterexample was generated and what it means",
      (v, _) => ExplainCounterexampleAction.chatCommand(v)
    ),
    CommandId.ExplainError -> CommandEntry(
      "Analyze and explain error messages at the current cursor position",
      (v, _) => runExplainError(v)
    ),
    CommandId.Extract -> CommandEntry(
      "Extract selected proof text into a separate reusable lemma",
      (v, _) => ExtractLemmaAction.chatExtract(v)
    ),
    CommandId.Find -> CommandEntry(
      "Search for theorems matching a given pattern or keyword",
      (v, a) => runFind(v, a),
      needsIQ = true
    ),
    CommandId.GenerateDoc -> CommandEntry(
      "Generate documentation for definitions and theorems",
      (v, _) => GenerateDocAction.chatGenerate(v)
    ),
    CommandId.GenerateElim -> CommandEntry(
      "Generate elimination rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateElim(v)
    ),
    CommandId.GenerateIntro -> CommandEntry(
      "Generate introduction rules for datatypes and definitions",
      (v, _) => GenerateRulesAction.chatGenerateIntro(v)
    ),
    CommandId.GenerateTests -> CommandEntry(
      "Generate test cases and examples for definitions",
      (v, _) => GenerateTestsAction.chatGenerate(v)
    ),
    CommandId.Help -> CommandEntry(
      "Display this table of available commands and their descriptions",
      (_, _) => showHelp()
    ),
    CommandId.Models -> CommandEntry(
      "Refresh the list of available Anthropic models from AWS Bedrock",
      (_, _) => runModels()
    ),
    CommandId.Nitpick -> CommandEntry(
      "Run Nitpick model finder to search for counterexamples",
      (v, _) =>
        CounterexampleFinderAction.run(v, CounterexampleFinderAction.Nitpick),
      needsIQ = true
    ),
    CommandId.PrintContext -> CommandEntry(
      "Display current proof context including assumptions and goals",
      (v, _) => PrintContextAction.run(v),
      needsIQ = true
    ),
    CommandId.Quickcheck -> CommandEntry(
      "Run QuickCheck to test conjectures with random examples",
      (v, _) =>
        CounterexampleFinderAction
          .run(v, CounterexampleFinderAction.Quickcheck),
      needsIQ = true
    ),
    CommandId.Read -> CommandEntry(
      "Display the content of a specified theory file (optional: line count)",
      (v, a) => TheoryBrowserAction.read(v, a)
    ),
    CommandId.Refactor -> CommandEntry(
      "Convert proof text to structured Isar proof style",
      (v, _) => RefactorAction.chatRefactor(v)
    ),
    CommandId.Search -> CommandEntry(
      "Search for specific text patterns within a theory file",
      (v, a) => TheoryBrowserAction.search(v, a)
    ),
    CommandId.Set -> CommandEntry(
      "View or modify Assistant configuration settings",
      (_, a) => runSet(a)
    ),
    CommandId.ShowType -> CommandEntry(
      "Display type information for the symbol at cursor position",
      (v, _) => ShowTypeAction.showType(v)
    ),
    CommandId.Sledgehammer -> CommandEntry(
      "Run Sledgehammer to find automatic proofs using external provers",
      (v, _) => runSledgehammer(v),
      needsIQ = true
    ),
    CommandId.Suggest -> CommandEntry(
      "Generate proof step suggestions for the current proof state",
      (v, a) => runSuggest(v, a)
    ),
    CommandId.SuggestName -> CommandEntry(
      "Suggest a descriptive name for the lemma, theorem, or definition at cursor",
      (v, _) => SuggestNameAction.chatSuggestName(v)
    ),
    CommandId.SuggestStrategy -> CommandEntry(
      "Recommend high-level proof strategies for the current goal",
      (v, _) => SuggestStrategyAction.suggest(v)
    ),
    CommandId.SuggestTactic -> CommandEntry(
      "Suggest specific tactics to apply at the current proof step",
      (v, _) => SuggestTacticAction.chatSuggest(v)
    ),
    CommandId.Summarize -> CommandEntry(
      "Generate a summary of theory content including key definitions",
      (v, _) => SummarizeTheoryAction.summarize(v)
    ),
    CommandId.Theories -> CommandEntry(
      "List all currently loaded theory files in the session",
      (_, _) => TheoryBrowserAction.theories()
    ),
    CommandId.Tidy -> CommandEntry(
      "Clean up and format proof text for better readability",
      (v, _) => TidyAction.tidy(v)
    ),
    CommandId.Trace -> CommandEntry(
      "Trace simplifier operations to understand rewriting steps",
      (v, _) => TraceSimplifierAction.trace(v),
      needsIQ = true
    ),
    CommandId.TryMethods -> CommandEntry(
      "Attempt various proof methods automatically on current goal",
      (v, _) => TryMethodsAction.run(v),
      needsIQ = true
    ),
    CommandId.Verify -> CommandEntry(
      "Verify that a given proof text is correct and complete",
      (v, a) => runVerify(v, a),
      needsIQ = true
    )
  )
  require(
    dispatch.keySet == CommandId.values.toSet,
    "ChatAction dispatch must cover all CommandId values."
  )

  def addMessage(message: Message): Unit = historyLock.synchronized {
    history = (history :+ message).takeRight(maxHistory)
  }

  def addMessage(role: ChatRole, content: String): Unit =
    addMessage(Message(role, content, LocalDateTime.now()))

  def clearHistory(): Unit = historyLock.synchronized {
    history = Nil
  }

  /** Get the current history as an immutable snapshot. Thread-safe because
    * @volatile ensures visibility and the List reference is immutable once
    * published. Writers are serialized by historyLock.
    */
  def getHistory: List[Message] = history

  def formatTime(ts: LocalDateTime): String = ts.format(timeFmt)

  /** Start a chat conversation with the LLM.
    *
    * @param view
    *   The current jEdit view
    * @param userMessage
    *   The user's message
    */
  def chat(view: View, userMessage: String): Unit = {
    AssistantDockable.resetCancel()
    if (userMessage.startsWith(":")) {
      handleCommand(view, userMessage)
    } else {
      val contextSeed = captureContextSeed(view)
      addMessage(Message(User, userMessage, LocalDateTime.now()))
      AssistantDockable.showConversation(getHistory)
      AssistantDockable.setStatus(AssistantConstants.STATUS_THINKING)

      val messagesForApi = getHistory
        .filterNot(_.transient)
        .map(m => (m.role.wireValue, m.content))

      val _ = Isabelle_Thread.fork(name = "assistant-chat") {
        val context = getContext(contextSeed)
        val systemPromptEither =
          try {
            Right(
              PromptLoader.load(
                "chat_system.md",
                if (context.nonEmpty) Map("context" -> context) else Map.empty
              )
            )
          } catch {
            case ex: Exception => Left(ex)
          }

        systemPromptEither match {
          case Left(ex) =>
            GUI_Thread.later {
              val errorMsg =
                ErrorHandler.makeUserFriendly(
                  s"Failed to load prompt: ${ex.getMessage}",
                  "chat"
                )
              AssistantDockable.setStatus(s"Error: $errorMsg")
              addResponse(s"Error: $errorMsg")
            }
          case Right(systemPrompt) =>
            try {
              BedrockClient.setCurrentView(view)
              val response =
                BedrockClient.invokeChat(systemPrompt, messagesForApi)
              GUI_Thread.later {
                addMessage(Message(Assistant, response, LocalDateTime.now()))
                AssistantDockable.showConversation(getHistory)
                AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
              }
            } catch {
              case ex: Exception =>
                GUI_Thread.later {
                  val errorMsg =
                    ErrorHandler.makeUserFriendly(ex.getMessage, "chat")
                  AssistantDockable.setStatus(s"Error: $errorMsg")

                  val retryAction = () => {
                    AssistantDockable.setStatus("Retrying...")
                    retryChatInternal(view, systemPrompt, messagesForApi)
                  }
                  val retryId = AssistantDockable.registerAction(retryAction)
                  ChatAction.addMessage(
                    Assistant,
                    s"Error: $errorMsg\n\n{{ACTION:$retryId:Retry}}"
                  )
                  AssistantDockable.showConversation(ChatAction.getHistory)
                }
            }
        }
      }
    }
  }

  /** Retry a chat without re-adding the user message to history. */
  private def retryChatInternal(
      view: View,
      systemPrompt: String,
      messagesForApi: List[(String, String)]
  ): Unit = {
    val _ = Isabelle_Thread.fork(name = "assistant-chat-retry") {
      try {
        BedrockClient.setCurrentView(view)
        val response = BedrockClient.invokeChat(systemPrompt, messagesForApi)
        GUI_Thread.later {
          addMessage(Message(Assistant, response, LocalDateTime.now()))
          AssistantDockable.showConversation(getHistory)
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            val errorMsg = ErrorHandler.makeUserFriendly(ex.getMessage, "chat")
            AssistantDockable.setStatus(s"Error: $errorMsg")
            addResponse(s"Error: $errorMsg")
          }
      }
    }
  }

  private def handleCommand(view: View, input: String): Unit = {
    val parts = input.drop(1).split("\\s+", 2)
    val rawCmd = parts(0).toLowerCase
    val arg = if (parts.length > 1) parts(1) else ""

    addMessage(Message(User, input, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)

    CommandId.fromWire(rawCmd) match {
      case Some(commandId) =>
        dispatch(commandId) match {
          case entry if entry.needsIQ && !IQAvailable.isAvailable =>
            addResponse(
              "I/Q plugin not available. Install I/Q to use this command."
            )
          case entry => entry.handler(view, arg)
        }
      case None =>
        addResponse(
          s"Unknown command `:$rawCmd`. Type `:help` for available commands."
        )
    }
  }

  private def showHelp(): Unit = {
    val headerBg = UIColors.HelpTable.headerBackground
    val borderColor = UIColors.HelpTable.borderColor
    val rowBorder = UIColors.HelpTable.rowBorder
    val accentColor = UIColors.HelpTable.accentColor
    val infoBg = UIColors.InfoBox.background
    val infoBorder = UIColors.InfoBox.border

    val sortedCommands = dispatch.toList.sortBy(_._1.wireName)
    val header =
      s"<tr><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:left;font-size:11pt;background:$headerBg;'>Command</th><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:left;font-size:11pt;background:$headerBg;'>Description</th><th style='padding:4px 8px;border-bottom:2px solid $borderColor;text-align:center;font-size:11pt;background:$headerBg;'>I/Q</th></tr>"
    val rows = sortedCommands.map { case (commandId, entry) =>
      val iq = if (entry.needsIQ) "yes" else ""
      s"<tr><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-family:${MarkdownRenderer.codeFont};font-size:11pt;white-space:nowrap;color:$accentColor;'>:${commandId.wireName}</td><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-size:11pt;'>${entry.description}</td><td style='padding:4px 8px;border-bottom:1px solid $rowBorder;font-size:11pt;text-align:center;'>$iq</td></tr>"
    }.mkString
    val table =
      s"<table style='width:100%;border-collapse:collapse;'>$header$rows</table>"
    val targetHelp =
      s"""<div style='margin-top:10px;padding:8px 10px;background:$infoBg;border:1px solid $infoBorder;border-radius:3px;'>
      |<div style='font-weight:bold;margin-bottom:4px;'>Target Syntax</div>
      |<div style='font-size:11pt;'>Commands like <code>:explain</code> and <code>:suggest</code> accept optional targets:</div>
      |<div style='font-size:11pt;padding-left:12px;margin-top:4px;'>
      |• <code>cursor</code> — current cursor position (default)<br/>
      |• <code>selection</code> — current text selection<br/>
      |• <code>Theory.thy:42</code> — specific line<br/>
      |• <code>Theory.thy:10-20</code> — line range<br/>
      |• <code>Theory.thy:lemma_name</code> — named element<br/>
      |• <code>cursor+5</code>, <code>cursor-3</code> — relative offset
      |</div></div>""".stripMargin
    addMessage(
      Message(
        Assistant,
        table + targetHelp,
        LocalDateTime.now(),
        rawHtml = true
      )
    )
    AssistantDockable.showConversation(getHistory)
  }

  /** Refresh available Bedrock models and display in chat.
    * 
    * Queries AWS Bedrock for available Anthropic models in the configured region.
    * Updates the model cache and displays the list in chat. Runs asynchronously on
    * background thread to avoid blocking the UI.
    */
  private def runModels(): Unit = {
    AssistantDockable.setStatus("Refreshing models...")

    val _ = Isabelle_Thread.fork(name = "chat-models") {
      try {
        val region = AssistantOptions.getRegion
        val models = BedrockModels.refreshModels(region)
        GUI_Thread.later {
          val modelList = models.map(m => s"* `$m`").mkString("\n")
          addResponse(
            s"**Available Anthropic Models** (${models.length} total)\n\n$modelList"
          )
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        }
      } catch {
        case ex: Exception =>
          GUI_Thread.later {
            addResponse(s"Error refreshing models: ${ex.getMessage}")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          }
      }
    }
  }

  /** View or modify Assistant configuration settings.
    * 
    * Handles three forms:
    * - `:set` - List all settings with their current values
    * - `:set key` - Show value of specific setting
    * - `:set key value` - Update setting to new value
    * 
    * Settings changes take effect immediately and persist across sessions.
    * 
    * @param arg Arguments after `:set` command (empty, key only, or key + value)
    */
  private def runSet(arg: String): Unit = {
    val parts = arg.trim.split("\\s+", 2)

    if (arg.trim.isEmpty) {
      addResponse(s"**Current Settings**\n\n${AssistantOptions.listSettings}")
    } else if (parts.length == 1) {
      AssistantOptions.getSetting(parts(0)) match {
        case Some(value) => addResponse(s"`${parts(0)}` = `$value`")
        case None        =>
          addResponse(
            s"Unknown setting: `${parts(0)}`. Type `:set` to see all settings."
          )
      }
    } else {
      AssistantOptions.setSetting(parts(0), parts(1)) match {
        case Some(msg) =>
          if (parts(0).toLowerCase == "model")
            AssistantDockable.refreshModelLabel()
          addResponse(msg)
        case None =>
          addResponse(
            s"Unknown setting: `${parts(0)}`. Type `:set` to see all settings."
          )
      }
    }
  }

  /** Explain Isabelle code at specified target location.
    * 
    * Resolves the target (cursor, selection, or explicit location), fetches surrounding context,
    * and invokes the LLM with the explain_with_context prompt template. Displays result in chat.
    * 
    * @param view The current jEdit view
    * @param targetSpec Target specification (empty for cursor, or TargetParser syntax)
    */
  private def runExplain(view: View, targetSpec: String): Unit = {
    val targetOpt =
      if (targetSpec.trim.isEmpty) Some(TargetParser.CurrentCursor)
      else {
        TargetParser.parseTarget(targetSpec, view) match {
          case Some(target) => Some(target)
          case None         =>
            addResponse(
              s"Invalid target: $targetSpec. Use 'cursor', 'selection', or 'Theory.thy:line'"
            )
            None
        }
      }

    targetOpt.foreach { target =>
      TargetParser.resolveTarget(target, view) match {
        case Some((buffer, start, end)) =>
          val textOpt = if (start == end) {
            CommandExtractor.getCommandAtOffset(buffer, start) match {
              case Some(text) => Some(text)
              case None       =>
                addResponse("No command found at target location")
                None
            }
          } else {
            Some(buffer.getText(start, end - start))
          }

          textOpt.foreach { text =>
            ActionHelper.runAndRespond("chat-explain", "Explaining code...") {
              val context = ContextFetcher.getContext(view, 3000)
              val subs = Map("theorem" -> text) ++
                context.map(c => Map("context" -> c)).getOrElse(Map.empty)
              val prompt = PromptLoader.load("explain_with_context.md", subs)
              BedrockClient.invokeInContext(prompt)
            }
          }
        case None =>
          addResponse(
            s"Could not resolve target: ${TargetParser.formatTarget(target)}"
          )
      }
    }
  }

  /** Generate proof step suggestions for target location.
    * 
    * Delegates to SuggestAction which combines LLM suggestions with optional Sledgehammer results,
    * verifies candidates in parallel when I/Q is available, and displays ranked results with badges.
    * 
    * @param view The current jEdit view
    * @param targetSpec Target specification (empty for cursor, or TargetParser syntax)
    */
  private def runSuggest(view: View, targetSpec: String): Unit = {
    val targetOpt =
      if (targetSpec.trim.isEmpty) Some(TargetParser.CurrentCursor)
      else {
        TargetParser.parseTarget(targetSpec, view) match {
          case Some(target) => Some(target)
          case None         =>
            addResponse(
              s"Invalid target: $targetSpec. Use 'cursor', 'selection', or 'Theory.thy:line'"
            )
            None
        }
      }

    targetOpt.foreach { target =>
      TargetParser.resolveTarget(target, view) match {
        case Some((buffer, offset, _)) =>
          AssistantDockable.setStatus("Generating suggestions...")
          val _ = Isabelle_Thread.fork(name = "chat-suggest") {
            try {
              SuggestAction.suggestFromChat(view, buffer, offset)
              GUI_Thread.later {
                AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
              }
            } catch {
              case ex: Exception =>
                GUI_Thread.later {
                  addResponse(s"Error: ${ex.getMessage}")
                  AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
                }
            }
          }
        case None =>
          addResponse(
            s"Could not resolve target: ${TargetParser.formatTarget(target)}"
          )
      }
    }
  }

  /** Explain error message at cursor position.
    * 
    * Extracts the error message from PIDE at the current cursor position, gathers surrounding
    * command text and goal state as context, then invokes the LLM with the explain_error prompt.
    * 
    * @param view The current jEdit view
    */
  private def runExplainError(view: View): Unit = {
    val buffer = view.getBuffer
    val offset = view.getTextArea.getCaretPosition
    
    // Extract error first (this is local to PIDE, not I/Q MCP)
    ExplainErrorAction.extractErrorAtOffset(buffer, offset) match {
      case None =>
        addResponse("No error at cursor position.")
      case Some(error) =>
        // Fork immediately to avoid blocking EDT on I/Q MCP calls
        ActionHelper.runAndRespond(
          "chat-explain-error",
          "Explaining error..."
        ) {
          // These I/Q MCP calls are now on background thread
          val context =
            CommandExtractor.getCommandAtOffset(buffer, offset).getOrElse("")
          val goalState = GoalExtractor.getGoalState(buffer, offset)

          val subs = Map(
            "error" -> error,
            "context" -> context
          ) ++ goalState.map(g => Map("goal_state" -> g)).getOrElse(Map.empty)

          val prompt = PromptLoader.load("explain_error.md", subs)
          BedrockClient.invokeInContext(prompt)
        }
    }
  }

  /** Verify proof method via I/Q and optionally diagnose failures with LLM.
    * 
    * Runs I/Q proof verification on the provided proof text. On success, displays timing.
    * On failure, automatically diagnoses the error using the LLM with the diagnose_verification
    * prompt template.
    * 
    * @param view The current jEdit view
    * @param proof The proof text to verify (e.g., "by simp", "by (induction xs) auto")
    */
  private def runVerify(view: View, proof: String): Unit = {
    if (proof.trim.isEmpty)
      addResponse("Usage: `:verify <proof>`\n\nExample: `:verify by simp`")
    else {
      ActionHelper.runIQCommand("chat-verify", AssistantConstants.STATUS_VERIFYING) { v =>
        val buffer = v.getBuffer
        val offset = v.getTextArea.getCaretPosition
        val timeout = AssistantOptions.getVerificationTimeout
        
        IQIntegration.verifyProofAsync(v, proof, timeout, {
          case IQIntegration.ProofSuccess(timeMs, _) =>
            addResponse(s"[ok] Proof verified successfully (${timeMs}ms)")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case IQIntegration.ProofFailure(error) =>
            val result = s"[FAIL] Verification failed: $error"
            addResponse(result)
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
            // Diagnose failure using LLM on background thread
            val _ = Isabelle_Thread.fork(name = "chat-verify-diagnose") {
              val goalState = GoalExtractor.getGoalState(buffer, offset)
              val context = CommandExtractor.getCommandAtOffset(buffer, offset)
              try {
                val subs = Map("proof" -> proof, "error" -> error) ++
                  goalState.map(g => Map("goal_state" -> g)).getOrElse(Map.empty) ++
                  context.map(c => Map("context" -> c)).getOrElse(Map.empty)
                val diagPrompt = PromptLoader.load("diagnose_verification.md", subs)
                val diagnosis = BedrockClient.invokeNoCache(diagPrompt)
                GUI_Thread.later { addResponse(diagnosis) }
              } catch {
                case ex: Exception =>
                  Output.writeln(s"[Assistant] Post-verification diagnosis failed: ${ex.getMessage}")
              }
            }
          case IQIntegration.ProofTimeout =>
            addResponse("[FAIL] Verification timed out")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case _ =>
            addResponse("[FAIL] Verification unavailable")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        })
      }(view)
    }
  }

  private def runSledgehammer(view: View): Unit = {
    ActionHelper.runIQCommand("chat-sledgehammer", "Running sledgehammer...") { v =>
      val timeout = AssistantOptions.getSledgehammerTimeout
      IQIntegration.runSledgehammerAsync(v, timeout, {
        case Right(results) if results.nonEmpty =>
          val lines = results
            .map(r => s"[sledgehammer] `${r.proofMethod}` (${r.timeMs}ms)")
            .mkString("\n\n")
          addResponse(s"**Sledgehammer found ${results.length} proofs:**\n\n$lines")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        case Right(_) =>
          addResponse("Sledgehammer found no proofs.")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        case Left(error) =>
          addResponse(s"Sledgehammer error: $error")
          AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
      })
    }(view)
  }

  private def runFind(view: View, pattern: String): Unit = {
    if (pattern.trim.isEmpty)
      addResponse(
        "Usage: `:find <pattern>`\n\nExample: `:find \"_ + _ = _ + _\"`"
      )
    else {
      ActionHelper.runIQCommand("chat-find", "Searching theorems...") { v =>
        val limit = AssistantOptions.getFindTheoremsLimit
        val timeout = AssistantOptions.getFindTheoremsTimeout
        val quotedPattern =
          if (pattern.startsWith("\"")) pattern else s"\"$pattern\""
        
        IQIntegration.runFindTheoremsAsync(v, quotedPattern, limit, timeout, {
          case Right(results) if results.nonEmpty =>
            val lines = results.map(r => s"* $r").mkString("\n\n")
            addResponse(s"**Found ${results.length} theorems:**\n\n$lines")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case Right(_) =>
            addResponse(s"No theorems found matching: $pattern")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
          case Left(error) =>
            addResponse(s"Find theorems error: $error")
            AssistantDockable.setStatus(AssistantConstants.STATUS_READY)
        })
      }(view)
    }
  }

  def addResponse(content: String): Unit = {
    addMessage(Message(Assistant, content, LocalDateTime.now()))
    AssistantDockable.showConversation(getHistory)
  }

  /** Add a display-only message that appears in chat but is NOT sent to the
    * LLM.
    */
  def addTransient(content: String): Unit = {
    addMessage(
      Message(Assistant, content, LocalDateTime.now(), transient = true)
    )
    AssistantDockable.showConversation(getHistory)
  }

  /** Add a tool-use message showing which tool is being called with what
    * parameters. Format: "toolName|||{json params}" - transient so it doesn't
    * get sent to LLM.
    */
  def addToolMessage(
      toolName: String,
      params: ResponseParser.ToolArgs
  ): Unit = {
    val jsonParams = ResponseParser.toolArgsToJson(params)
    val content = s"$toolName|||$jsonParams"
    addMessage(Message(Tool, content, LocalDateTime.now(), transient = true))
    AssistantDockable.showConversation(getHistory)
  }

  private def captureContextSeed(view: View): ChatContextSeed =
    try {
      GUI_Thread.now {
        val textArea = view.getTextArea
        val selected =
          Option(textArea.getSelectedText).map(_.trim).filter(_.nonEmpty)
        val buffer = view.getBuffer
        val path = MenuContext.bufferPath(buffer)
        val caret =
          Option(textArea).map(_.getCaretPosition).getOrElse(0)
        ChatContextSeed(
          selectedText = selected,
          path = path,
          caretOffset = math.max(0, caret)
        )
      }
    } catch {
      case _: Exception =>
        ChatContextSeed(selectedText = None, path = None, caretOffset = 0)
    }

  private def getContext(seed: ChatContextSeed): String =
    seed.selectedText.getOrElse {
      seed.path
        .flatMap { path =>
          IQMcpClient
            .callResolveCommandTarget(
              selectionArgs = Map(
                "command_selection" -> "file_offset",
                "path" -> path,
                "offset" -> seed.caretOffset
              ),
              timeoutMs = AssistantConstants.CONTEXT_FETCH_TIMEOUT
            )
            .toOption
            .map(_.command.source)
            .map(_.trim)
            .filter(_.nonEmpty)
        }
        .getOrElse("")
    }
}
