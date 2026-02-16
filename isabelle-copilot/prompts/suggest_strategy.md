<!-- Variables: goal_state (required), command (required), relevant_lemmas (optional), context (optional) -->
You are an Isabelle/HOL expert. Analyze this proof goal and suggest the best high-level strategy.

## Goal State
```
{{goal_state}}
```

## Command Context
```isabelle
{{command}}
```
{{#relevant_lemmas}}

## Relevant Lemmas (local proof context)
```
{{relevant_lemmas}}
```
{{/relevant_lemmas}}
{{#context}}

## Referenced Definitions
```isabelle
{{context}}
```
{{/context}}

Analyze the goal and the relevant lemmas. Suggest ONE primary proof strategy from:
- **Induction**: For goals involving recursive datatypes/naturals. Look for `.induct` rules.
- **Case analysis**: For disjunctions or datatypes. Look for `.cases` or `.exhaust` rules.
- **Contradiction**: When assuming negation leads to False
- **Direct proof**: When definitions/simplification suffice. Look for `.simps` or `_def` lemmas.
- **Rule application**: When a specific intro/elim/dest rule directly applies
- **Coinduction**: For coinductive predicates

Provide:
1. **Strategy**: The recommended approach
2. **Why**: Why this strategy fits (reference specific relevant lemmas if applicable)
3. **First step**: The Isabelle command to begin (e.g., `proof (induct x)`)
4. **Key lemmas**: Specific lemmas from the relevant list to use

Be concise.
