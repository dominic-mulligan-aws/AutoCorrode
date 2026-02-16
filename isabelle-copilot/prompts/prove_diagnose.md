<!-- Variables: command (required), proof (required), num_sorries (required), subgoals (optional), context (optional) -->
The following Isabelle proof has {{num_sorries}} unfilled sorry placeholder{{#plural}}s{{/plural}}.

## Lemma
```isabelle
{{command}}
```

## Proof (with sorry placeholders)
```isabelle
{{proof}}
```

{{#subgoals}}
## Unfilled Subgoals
These are the actual proof obligations at the sorry positions, as reported by Isabelle:
```
{{subgoals}}
```
{{/subgoals}}

{{#context}}
## Available Context
The following definitions, theorems, and type information are available in scope:
```
{{context}}
```
{{/context}}

## Instructions
For each unfilled sorry, analyze:

1. **The exact obligation** — what goal needs to be proved at this position (use the subgoal information above if available)
2. **Why simple methods failed** — consider whether `simp`, `auto`, `blast` lack needed rewrite rules or lemmas
3. **What auxiliary lemma is missing** — identify the specific intermediate fact that would make the proof go through
4. **A concrete lemma statement** the user should prove first

Format each suggested lemma as:
```isabelle
lemma suggested_name:
  shows ‹exact_statement›
```

Be specific — use the actual function names, constructor names, and types from the context. Do not guess names; use only identifiers that appear in the proof, subgoals, or context above.