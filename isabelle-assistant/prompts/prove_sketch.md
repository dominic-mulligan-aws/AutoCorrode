<!-- Variables: goal_state (required), command (required), relevant_theorems (optional), proof_plan (optional) -->
You are an expert Isabelle/HOL theorem prover (Isabelle2025-2). Write a proof SKELETON for this goal.

## Lemma
```isabelle
{{command}}
```

## Current Goal State
```
{{goal_state}}
```
{{#relevant_theorems}}

## Available Context
```
{{relevant_theorems}}
```
{{/relevant_theorems}}
{{#proof_plan}}

## Proof Plan
The following informal proof plan was produced by analyzing the goal and available context. Use this to guide your skeleton structure:
{{proof_plan}}
{{/proof_plan}}

## Instructions
Write a structured Isar proof skeleton from `proof` to `qed`. Use `sorry` for EVERY leaf proof step — do not attempt to close any goals yourself. Your job is ONLY to decompose the proof into the right structure.

**CRITICAL**: Use the EXACT constructor names, function names, and variable names from the context and goal state above. Do NOT guess or invent names — if the datatype has constructors `Z` and `S`, use `Z` and `S` (not `Zero`/`Succ`/`Suc`). The skeleton will be verified by Isabelle and rejected if names are wrong.

Example output for an induction proof (use the actual constructor names from the context — these are just placeholders):
```isabelle
proof (induct x)
  case Base_Constructor
  then show ?case sorry
next
  case (Recursive_Constructor n)
  then show ?case sorry
qed
```

Example output for a proof needing intermediate facts:
```isabelle
proof -
  obtain k where ‹n = mult m k› using assms(1) sorry
  have ‹mult n p = mult m (mult k p)› sorry
  then show ?thesis sorry
qed
```

Guidelines:
- Use `sorry` for EVERY `show`, `have`, and `obtain` — no `by`, `simp`, `auto`, etc.
- Focus on decomposing the goal: what intermediate facts are needed? what case splits?
- Use `obtain` to introduce witnesses from existential assumptions
- Use `have` for intermediate facts that bridge assumptions to the conclusion
- For induction: `proof (induct var)` with `case` blocks, each ending in `sorry`
- For case analysis: `proof (cases var)` with `case` blocks
- For elimination: `proof (elim rule)` or `obtain ... where ... sorry`

Output ONLY the proof skeleton (from `proof` to `qed`), wrapped in ```isabelle fences. Do NOT include any explanation, commentary, or surrounding text. Do NOT wrap the code in parentheses or add any metadata. The content inside the fences must be valid Isabelle/Isar that can be pasted directly into a .thy file.
