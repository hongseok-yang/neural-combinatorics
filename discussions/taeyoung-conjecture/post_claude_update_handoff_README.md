# Post-Claude update handoff package

This package summarizes work done after Claude's latest comments on the Turan-Sidorenko / smoothed-Goodman project.

Main documents:

- `turan_sidorenko_post_claude_update.pdf` and `.tex`: detailed self-contained status note.
- `feedback_request_memo.pdf` and `.tex`: short memo asking Claude targeted questions.

Scripts:

- `scripts/verify_post_claude_identities.py`: unified exact SymPy checker for the directed-transitivity identity, the four-block pointwise obstruction, and the five-vertex cloning obstruction.
- `scripts/check_cloning_potentials.py`: exact small-graph checks for corrected cloning potentials.
- `scripts/symmetrization_obstruction.py`: exact check for naive symmetrization obstruction.
- `scripts/verify_directed_transitivity.py`: exact directed-transitivity identity checker from the intermediate investigation.

To run the main checker:

```bash
cd scripts
python verify_post_claude_identities.py
```

The output should match `verify_post_claude_identities_output.txt`.
