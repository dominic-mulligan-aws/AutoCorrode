<!-- Variables: command (required), command_type (required) -->
Generate a documentation comment for this Isabelle {{command_type}}.

```isabelle
{{command}}
```

Use Isabelle's `text \<open>...\<close>` format. Available markup symbols:
- `\<^verbatim>\<open>name\<close>` — for the name being defined (renders as monospace)
- `\<^const>\<open>name\<close>` — for referencing existing constants (creates hyperlink)
- `\<^term>\<open>expr\<close>` — for inline terms (typeset as math)
- `\<^typ>\<open>type\<close>` — for type expressions
- `\<^emph>\<open>text\<close>` — for emphasis (italic)

These are Isabelle's formal document markup (not LaTeX or Markdown). They render in Isabelle's HTML and PDF output.

Keep it concise (3-8 lines). Output ONLY the text block, no markdown fences:

text \<open>
  ...
\<close>
