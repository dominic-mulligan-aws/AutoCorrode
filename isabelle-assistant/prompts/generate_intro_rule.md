<!-- Variables: definition (required), context (optional) -->
You are an Isabelle/HOL expert. Generate ONLY an introduction rule for this definition.

## Definition
```isabelle
{{definition}}
```
{{#context}}

## Referenced Definitions
```isabelle
{{context}}
```
{{/context}}

An introduction rule (naming convention: `<name>I`) allows proving the defined predicate from its expansion. It should be suitable for use with `intro` or `rule` tactics.

Output ONLY a single lemma with:
- Name ending in `I` (e.g., `fooI`)
- Uses `assumes`/`shows` style (NOT bare implications)
- Uses cartouches ‹...› (NOT quotation marks "...")
- A simple proof using the definition

Example format:
```
lemma fooI:
  assumes ‹precondition›
  shows ‹foo x›
  using assms unfolding foo_def by auto
```

Output ONLY the lemma. No explanation, no other rules.
