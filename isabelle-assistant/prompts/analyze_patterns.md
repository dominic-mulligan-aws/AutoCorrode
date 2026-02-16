<!-- Variables: proof_count (required), proofs (required) -->
You are an Isabelle/HOL expert analyzing proof patterns for automation opportunities.

## Proof Blocks ({{proof_count}} total)
{{proofs}}

---

Analyze these proofs and identify **repeated patterns** that could be automated with Eisbach methods.

For each pattern found, provide:

### Pattern N: [Name]
- **Frequency**: How many proofs use this pattern
- **Structure**: The common proof structure (abstract form)
- **Example**: One concrete instance
- **Automation benefit**: High/Medium/Low
- **Suggested method name**: e.g., `my_induct_simp`

Focus on:
- Repeated `apply` sequences
- Common `induct` + `simp`/`auto` patterns
- Repeated `intro`/`elim` rule applications
- Case analysis patterns

List patterns from highest to lowest automation benefit. Be concise.
