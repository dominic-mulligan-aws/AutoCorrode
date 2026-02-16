<!-- Variables: error (required), context (required), goal_state (optional), definitions (optional) -->
You are an expert Isabelle/HOL theorem prover. Analyze this error systematically and provide actionable solutions.

## Error Message
```
{{error}}
```

## Code Context
```isabelle
{{context}}
```
{{#goal_state}}

## Current Goal State
```
{{goal_state}}
```
{{/goal_state}}
{{#definitions}}

## Referenced Definitions
```isabelle
{{definitions}}
```
{{/definitions}}

## Error Analysis Framework
1. **Error Classification**: What type of error is this?
   - Syntax error (malformed code)
   - Type error (type mismatch)
   - Proof error (method failed)
   - Undefined reference (missing import/definition)

2. **Root Cause**: Why did this specific error occur?

3. **Immediate Fixes**: 2-3 concrete solutions to try:
   - Fix A: [specific change]
   - Fix B: [alternative approach]
   - Fix C: [fallback option]

4. **Prevention**: How to avoid this error in future

## Common Patterns
- `No such constant "X"` → Import theory or add definition
- `Type unification failed` → Add type annotations or check variable types
- `Failed to apply initial proof method` → Try simpler method or add intermediate steps

Provide systematic analysis and specific, actionable fixes.
