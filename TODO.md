- Remove excessive imports.
- Clean up instances to take advantage of Lean 4.
- Fix variable letters.
- Add documentation.
- Clarify that `@[simp]` lemmas normalise casts between permutation types to be visible to help with applying lemmas. (Change them to coercions, and then we won't need this maybe?)
- Remove instance names.
- Rename all of the `Allowable`/`BasePerm`/`StructPerm` objects?
- Remove double line breaks.
- Reformat lines containing only `by`.
- Change `refine'` to new variants.
- Remove unnecessary instances of `*_eta` lemmas.
- Turn `Allowable.comp *` into `*.comp`.
- Make `Constrains` use `InflexibleBot` etc.
- Fix the imports of the main lean files (e.g. `Counting.lean`).
- Try to remove typed atoms.
- Add `noncomputable section` everywhere.
