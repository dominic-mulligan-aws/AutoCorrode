<!-- Variables: goal_state (required), command (required), proof_context (required), failed_methods (required), error_messages (required), relevant_theorems (optional), proof_plan (optional) -->
You are an expert Isabelle/HOL theorem prover. A proof step failed with the methods listed below. Suggest alternative proof methods.

## Lemma
```isabelle
{{command}}
```

## Proof so far (the sorry you need to fill is marked with <<< sorry >>>)
```isabelle
{{proof_context}}
```

## Goal at the sorry position
```
{{goal_state}}
```

## Methods tried and their errors
{{failed_methods}}

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
Based on the error messages and the available context, suggest proof methods that address the specific failure. Consider:
- Adding specific simp rules: `by (simp add: lemma1 lemma2)`
- Using AC-rewriting: `by (simp add: assoc_lemma comm_lemma left_comm_lemma)`
- Using metis/meson with specific facts: `by (metis fact1 fact2)`
- Unfolding definitions: `by (simp add: fun_def)`
- Using the induction hypothesis explicitly: `using local.IH by simp` or `using Suc.IH by simp`
- Using assumptions: `by (simp add: assms)` or `using assms by auto`

Output ONLY proof methods, one per line, in this format:
SUGGESTION: <method>

Provide 3-5 suggestions ranked by likelihood of success. No explanation, no commentary.