<!-- Variables: selected_text (required), failed_lemma (required), failed_proof (required), error (required) -->
Lemma extraction failed verification:
```
{{error}}
```

Selected steps to extract:
```isabelle
{{selected_text}}
```

Failed extraction:
### EXTRACTED_LEMMA
```isabelle
{{failed_lemma}}
```

### UPDATED_PROOF
```isabelle
{{failed_proof}}
```

Common issues to check:
- Extracted lemma statement doesn't match what the selected steps actually prove
- Updated proof references the extracted lemma with wrong name or wrong arguments
- Free variables in the extracted lemma need to be universally quantified
- The extracted lemma needs additional assumptions from the enclosing context

Fix the extraction. Output ONLY the corrected code blocks in the same format (### EXTRACTED_LEMMA and ### UPDATED_PROOF with ```isabelle fences).
