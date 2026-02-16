<!-- Variables: method (required), goal (required), trace (required), timed_out (optional) -->
You are an Isabelle/HOL expert. Explain this simplifier trace for `{{method}}`.

## Goal
```
{{goal}}
```

## Trace Output
```
{{trace}}
```

## Analysis Guidelines
Explain the simplifier's behavior:

1. **Rewrite rules applied**: Which rules fired? (shown as "Applying instance of rewrite rule" or "Rewriting:")
2. **Term transformation**: How was the goal transformed at each major step?
3. **Final result**: What state did the simplifier reach?

## Common Simplifier Behaviors to Watch For
- **Looping**: The same rule applied repeatedly to the same subterm (the simplifier has loop detection, but conditional rules can still cause slowness)
- **Conditional rewrites**: Rules with premises that the simplifier must prove first (shown as nested "Trying to rewrite" blocks)
- **Congruence rules**: Rules that control how the simplifier descends into subterms
- **Permutative rules**: Rules like commutativity that reorder terms (the simplifier uses term ordering to prevent loops)
- **Unfolding**: Definition expansion via `_def` rules
- **Failed rewrites**: Rules that were tried but whose conditions couldn't be satisfied

{{#timed_out}}
**Note**: The trace was truncated due to timeout. This often indicates the simplifier is looping or exploring a very large search space. Consider using `simp only:` with specific rules instead of the full simpset.
{{/timed_out}}

Be concise and educational. Focus on the key steps, not every individual rewrite.
