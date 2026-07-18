# claude_jul17 — companion files for `paper_new_region2_claude_v1.tex`

Produced by Claude on 2026-07-16/17.  The consolidated note
`../paper_new_region2_claude_v1.tex` inlines the proof notes below (and cites
the `m=9,11,13` note in `sm3/` rather than inlining it); this directory holds
those notes plus the machine-validation and independent-verification scripts
referenced by the note's "How to audit" section.  All scripts are python3
(numpy / sympy / mpmath / fractions); each exits 0 iff every check passes.

**§4 update (2026-07-17, later):** the small-cycle section was restructured.
`m=3,5,7` are now closed by elementary density-free identities (Goodman's
triangle theorem; the `C_5` completed square; the `C_7` sum of squares) —
`elem_357.tex`, symbolically verified. `m=9,11,13` are closed by extending the
verified Zone-B/Zone-C proofs (§5/§6) to the fixed length — `sm3/m91113_final.tex`,
whole-domain validation passes (worst ratio `R_m/(C_m ψ)` = 0.710/0.763/0.799),
independent verifier pass, adversarial review "within tolerance". This removes
both computational residues of the superseded first draft
`smallm_regionII_proof_v2.tex` (its Bernstein tables and box subdivision). The
`m=9,11,13` certificates are fixed displayed covers (no adaptive subdivision) but
inherit §6's bracket lemmas via the `m→n=m−2` substitution and are tightest at
`m=9` (~6% majorant slack, largest cover); see Remark "Honest status" in §4.

## Section → files map

| Section of the consolidated note | standalone note | author validation | independent verification |
|---|---|---|---|
| §4 small-m, `m=3,5,7` (elementary) | `elem_357.tex` | `validate_elem_357.py` | `verify_indep_elem.py` |
| §4 small-m, `m=9,11,13` (zone extension) | `sm3/m91113_final.tex` (+ `sm3/strip_tables.tex`) | `sm3/validate_m91113.py` (drives `sm3/validate_zoneB_91113.py`, `sm3/validate_zoneC_91113_v2.py`) | `sm3/verify_indep_zoneB.py`, `sm3/verify_indep_zoneC2.py` |
| §4 small-m (superseded first draft, `m=3..13` via one certificate) | `smallm_regionII_proof_v2.tex` | `validate_smallm_v2.py` | `verify_independent_smallm.py` |
| §5 Zone B analytic | `zoneB_analytic.tex` | `validate_zoneB.py` | `verify_independent_zoneB.py` |
| §6 Zone C analytic | `proof_zoneC_analytic_v2.tex` | `validate_zoneC_analytic_v2.py` | `verify_independent_zoneC_v3.py` |
| §7 residual strip | `strip_final*.tex` (see provenance note in §7) | `validate_strip_final.py` | `verify_independent_strip*.py` |
| §8 Appendix-B constants | `app_constants_analytic.tex` | `validate_app_constants.py` | `verify_independent_appconst.py` |

`scan_scalar.py` is the calibration scan quoted in §1 (scalar inequality
for m ≤ 13 and the failure of the frontier route for q ≤ 1/3).  Note its
raw float64 corner margins for m=3,5 are cancellation artifacts; the
corrected corner analysis is in §1 and in the small-m note.

## Verification pipeline (what "verified" means in the provenance notes)

For each section: (i) numeric cartography of the target inequality;
(ii) analytic proof draft; (iii) author validation script checking every
displayed inequality (dense float grids over the exact stated domains +
exact `fractions.Fraction` at corners/extremes); (iv) an independent
verifier agent that re-derived every displayed claim with its own script,
without reusing the author's; (v) an adversarial reviewer hunting for
band-accounting bugs, out-of-domain monotonicity, unsafe roundings,
degenerate cases.  Repairs were re-verified from scratch.

## Relationship to the two source papers

- [R1] = `../paper_new.tex` (Region I; the appendix note here is a
  drop-in replacement for its Appendix B, labels preserved).
- [R2] = `../paper_region2_v2.tex` (Region II; the zone notes prove
  Lemma `zoneB-battle` — statement unchanged — and Lemma `zoneC-mod` —
  certificate eliminated; the small-m note extends Theorem `scalar` to
  all odd m ≥ 3).

Nothing in this directory modifies the source papers; integration edits
(deleting certificate paragraphs, updating the four "computer-assisted"
mentions in [R1], fixing the stale "2997 boxes" count in [R2]) are listed
in the consolidated note and remain for the authors.
