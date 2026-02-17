<!-- Variables: command (required), command_type (required), current_name (optional), existing_names (optional), theory_name (optional), context (optional) -->
Suggest a descriptive name for this Isabelle {{command_type}}.

**Command:**
```isabelle
{{command}}
```

{{#current_name}}
**Current name:** `{{current_name}}`
{{/current_name}}

{{#theory_name}}
**Theory:** {{theory_name}}
{{/theory_name}}

{{#existing_names}}
**Names already in scope (avoid these):**
{{existing_names}}

{{/existing_names}}
{{#context}}
**Surrounding context:**
```isabelle
{{context}}
```

{{/context}}
**Naming guidelines:**
- Use lowercase with underscores (snake_case): `my_lemma_name`
- Be descriptive but concise (2-4 words typically)
- Reflect the main property or purpose
- Follow Isabelle conventions:
  - Theorems/lemmas: describe the property (e.g., `map_append`, `length_rev`)
  - Functions: verb or noun describing the operation (e.g., `insert_sorted`, `merge_lists`)
  - Definitions: noun describing what is defined (e.g., `is_sorted`, `list_sum`)
- Avoid generic names like `lemma1`, `helper`, `aux`
- Do NOT use names already in scope (listed above)

Provide 3-5 suggested names in this format:
NAME: suggested_name
NAME: alternative_name
NAME: another_name

Do not include explanations, just the NAME: lines.