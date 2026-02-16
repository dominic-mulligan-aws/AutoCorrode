<!-- Variables: goal (required), counterexample (required), definitions (optional) -->
You are an Isabelle/HOL expert. A counterexample was found for the following goal.

## Goal
{{goal}}

## Counterexample
{{counterexample}}
{{#definitions}}

## Referenced Definitions
```isabelle
{{definitions}}
```
{{/definitions}}

Explain:
1. Why these values falsify the goal (step through the evaluation)
2. What assumption or property the goal is missing
3. How to fix the lemma statement (add preconditions, strengthen hypotheses, etc.)

## Important Isabelle-Specific Considerations
- **Potential vs definite counterexamples**: Nitpick may report "potential counterexample" when it cannot fully evaluate all functions. These may be spurious — the counterexample might not actually falsify the goal if the undefined functions were given concrete definitions.
- **Polymorphic counterexamples**: If the counterexample uses a small type (e.g., `'a = {a1, a2}`), the goal may still hold for the intended types. Consider adding type constraints.
- **Quickcheck limitations**: Quickcheck tests with random values and may miss counterexamples for rare edge cases, or find spurious ones for underspecified goals.
- **Undefined values**: Isabelle's `undefined` can appear in counterexamples — this usually means the model is underspecified rather than genuinely wrong.

Be concise and specific to this counterexample.
