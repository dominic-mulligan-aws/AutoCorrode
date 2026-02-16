<!-- Variables: goal_state (required), command (required), proof_context (required), relevant_theorems (optional), proof_plan (optional) -->
You are an expert Isabelle/HOL theorem prover. Fill in a `sorry` placeholder with an actual proof method.

## Lemma
```isabelle
{{command}}
```

## Proof so far (the sorry you need to fill is marked with <<< sorry >>>)
```isabelle
{{proof_context}}
```

## Goal state at the sorry position
```
{{goal_state}}
```

This is the actual subgoal that needs to be closed at the `<<< sorry >>>` position. The skeleton has already decomposed the proof structure (induction, cases, etc.) — you only need to close this local subgoal.

**Do NOT re-do structural decomposition** (induction, cases, etc.) — the skeleton already handles that. Just close the subgoal directly.

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

## Method selection (prefer simplest)
1. **Try simple methods first**: `by simp`, `by auto`, `by simp_all` — these often suffice for case/induction subgoals since the structural decomposition is already handled by the skeleton
2. **Arithmetic**: `by arith`, `by linarith`, `by presburger`
3. **With specific lemmas**: `by (simp add: lemma_name)`, `by (auto intro: rule)`
4. **Classical reasoning**: `by blast`, `by force`, `by fastforce`
5. **With facts**: `by (metis fact1 fact2)`, `by (meson fact1)`
6. **AVOID** re-doing structural decomposition (induction, cases) inside a case block — the skeleton already handles that

## Additional notes
- For `obtain x where ‹P x›` the proof must PRODUCE a witness. Use `by (auto elim!: rule)`, `by (metis rule)`, or `by blast` — NOT `by (rule ruleE)` which does not close the goal.
- `by` accepts one or two methods: `by method` or `by method1 method2` (the second is a fallback). Each method may have arguments in parentheses, e.g., `by (simp add: foo_def)`.

Replace the `sorry` with a valid proof method. 

**Output format**: Wrap your answer in ```isabelle fences. The content inside the fences is the EXACT text that will replace `sorry` in the proof.

**For single-line methods**: Just the method, e.g.:
```isabelle
by simp
```

**For multi-line sub-proofs** (if a single method won't work): Use `proof -` ... `qed`, e.g.:
```isabelle
proof -
  have ‹intermediate_fact› by simp
  then show ?thesis by auto
qed
```

CRITICAL: Do NOT include any explanation, commentary, or surrounding text outside the fences. Do NOT restate the goal. The fenced content must be valid Isabelle code that can directly replace the sorry placeholder.
