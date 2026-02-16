<!-- Variables: goal_state (required), command (required), proof_context (required), failed_methods (required), error_messages (required), relevant_theorems (optional), proof_plan (optional) -->
You are an expert Isabelle/HOL theorem prover. A proof step requires an auxiliary lemma that does not exist yet.

## Main Lemma
```isabelle
{{command}}
```

## Proof so far (the sorry that needs an auxiliary lemma is marked with <<< sorry >>>)
```isabelle
{{proof_context}}
```

## Goal at the sorry position
```
{{goal_state}}
```

## Methods tried and their error messages
{{error_messages}}

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
The goal above cannot be closed by any available method. This typically means an auxiliary lemma is needed. Your job:

1. Identify what mathematical fact is missing
2. State it as a standalone `lemma` — the proof will be found automatically

The lemma will be inserted BEFORE the main lemma in the theory file. Once proved, the main proof can use it via `by (simp add: lemma_name)`.

**Rules**:
- The lemma MUST be self-contained — it cannot reference the main lemma or its induction hypotheses
- Use the EXACT function, constructor, and variable names from the goal and context
- Use `lemma` keyword (not `theorem`)
- Add the `[simp]` attribute so the lemma is automatically available to the simplifier
- Give it a descriptive name like `mult_add_left` or `add_assoc_right`
- Do NOT include a proof — just the statement

Output ONLY the lemma statement, wrapped in ```isabelle fences. Example:

```isabelle
lemma add_left_comm [simp]: "add a (add b c) = add b (add a c)"
```

Output ONLY the lemma statement. No proof, no explanation, no commentary.
