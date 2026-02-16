<!-- Variables: definition (required), context (optional) -->
You are an Isabelle/HOL expert. Generate ONLY an elimination rule for this definition.

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

An elimination rule (naming convention: `<name>E`) allows deriving consequences from the defined predicate. It should be suitable for use with `elim` or `erule` tactics.

Output ONLY a single lemma with:
- Name ending in `E` (e.g., `fooE`)
- Uses `assumes`/`obtains` or `assumes`/`shows` style
- Uses cartouches ‹...› (NOT quotation marks "...")
- A simple proof using the definition

Example format:
```
lemma fooE:
  assumes ‹foo x›
  obtains y where ‹precondition y x›
  using assms unfolding foo_def by auto
```

Output ONLY the lemma. No explanation, no other rules.
