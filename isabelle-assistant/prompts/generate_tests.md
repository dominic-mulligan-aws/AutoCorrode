<!-- Variables: definition (required), context (optional) -->
You are an Isabelle/HOL expert. Generate test cases for this definition.

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

Generate 5-10 `value` commands that test the definition with:
- Typical/common inputs
- Edge cases (empty, zero, boundary values)
- Corner cases specific to the definition's logic

Format each test as:
```
value ‹expr›
```

For each test, add a brief Isar comment (\<comment> \<open>...\<close>) explaining what it tests.
Output ONLY valid Isabelle code. Use cartouches ‹...› not quotation marks.
