# Goodman-style odd-cycle bound: audit package

This package audits the supplied Claude proof for the range `1/2 < p < 2/3`
and replaces its computer-assisted scalar stage by an analytic proof.

## Files

- `goodman_odd_cycles_claude_audit_and_analytic_completion.tex` — the audit,
  exact repairs, and the complete analytic five-atom scalar argument.
- `verify_analytic_scalar_lemma.py` — exact SymPy identity checks and an
  optional high-precision stress test. It is **not** used as a proof.
- `verify_analytic_scalar_lemma.log` — output of a reference run.
- `original_script_audit_status.tsv` and `*.rerun.log` — rerun status/logs for
  the three supplied programs.

## Run the checker

```bash
python verify_analytic_scalar_lemma.py --points 2000 --max-k 50
```

The proof itself is contained in the TeX file. The key replacement is the
signed measure

```text
nu = beta delta_beta + p delta_q - p delta_p
     - gamma delta_gamma - c delta_L,
```

whose even moments are exactly the desired scalar gaps. The TeX file proves
that its quadratic stop-loss transform is nonnegative for every threshold.
