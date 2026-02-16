<!-- Variables: goal_state (required), command (required), proof_context (required), failed_methods (required), relevant_theorems (optional), proof_plan (optional) -->
You are an expert Isabelle/HOL theorem prover. A proof step cannot be closed by a single method. Decompose it into smaller steps.

## Lemma
```isabelle
{{command}}
```

## Proof so far (the sorry you need to refine is marked with <<< sorry >>>)
```isabelle
{{proof_context}}
```

## Goal at the sorry position
```
{{goal_state}}
```

## Methods that were tried and failed
{{failed_methods}}

{{#relevant_theorems}}
## Available Context
```
{{relevant_theorems}}
```
{{/relevant_theorems}}
{{#proof_plan}}

## Proof Plan
{{proof_plan}}
{{/proof_plan}}

## Instructions
The sorry above could not be closed by any single method. Replace it with a **multi-step sub-proof** that decomposes the goal into smaller, simpler intermediate steps. Each intermediate step should end with `sorry` — the fill phase will close them later.

Strategies (in order of preference):
1. **Missing auxiliary lemmas**: If the goal needs a fact that isn't available, introduce it as `have ‹fact› sorry` then use it. For example, if you need associativity/commutativity lemmas, introduce them as local `have` steps. These can later be extracted as standalone lemmas.
2. **Equational reasoning**: Use `have "LHS = step1" sorry` / `also have "... = step2" sorry` / `finally show ?thesis .` for algebraic simplification chains. Each step should be a single rewrite that `simp` or `auto` can handle.
3. **Intermediate facts**: Use `have ‹intermediate_fact› sorry` to establish stepping stones that bridge the gap between assumptions and conclusion.
4. **Rewriting then closing**: Use `have "rewritten_form" sorry` then `then show ?case sorry`
5. **Using specific lemmas from context**: If the context mentions relevant lemmas, reference them with `using lemma_name` or `by (simp add: lemma_name)`

The key idea: break one hard sorry into multiple easier sorries. Each new sorry should be closable by a simple method like `simp`, `auto`, or `simp add: specific_lemma`.

Use the EXACT function, constructor, and variable names from the goal and context. Do NOT guess names.

Output ONLY the replacement text that goes where `sorry` currently is, wrapped in ```isabelle fences. 

**CRITICAL FORMATTING RULES — VIOLATION CAUSES SYNTAX ERRORS**:
- Do NOT restate the goal. Do NOT write the goal statement (e.g., `mult m (add n p) = ...`) before your proof. The goal is already in the proof context. Writing it will cause "Outer syntax error: keyword 'is' expected".
- The FIRST line of your output MUST be `proof -` or `by (...)` — nothing before it.
- Do NOT include `show ?case` or `show ?thesis` — those are already in the proof.
- Do NOT include the surrounding case/show — only the proof fragment itself.
- If using a sub-proof, start with `proof -` and end with `qed`.
- Every leaf step must end in `sorry`.

Example: if the proof has `then show ?case sorry` and the sorry needs decomposition, output:
```isabelle
proof -
  have ‹intermediate_fact_1› sorry
  have ‹intermediate_fact_2› using ‹intermediate_fact_1› sorry
  then show ?thesis sorry
qed
