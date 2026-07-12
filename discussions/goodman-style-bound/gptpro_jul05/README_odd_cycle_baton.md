# Odd-cycle spectral-shift baton package

This package is intended to let Claude and collaborators catch up from the original `paper.tex` state.

Main document:

- `odd_cycle_high_density_baton.tex` / `.pdf`: self-contained note.

Main results recorded in the note:

1. For every graphon `W` of edge density `p >= 2/3` and every odd `m >= 3`,
   `t(C_m,W) >= p^m - p(1-p)^(m-1)`.
2. The same lower bound holds for every rank-two complement graphon
   `1-W(x,y)=q+u(psi(x)+psi(y))+lambda psi(x)psi(y)`, hence for every bipodal graphon.
3. The remaining part of the full conjecture is the one-frontier region `1/2 < p < 2/3`.

Checkers and logs:

- `clean_two_sided_shift_checker.py`: exact rational checker for the finite residual strip through `m=61` and for the main algebraic identities.
- `clean_checker_m61.log`: successful run log for the finite strip certificate.
- `regionI_constant_certifier_exact.py`: exact rational constant checker supporting the analytic residual-strip proof.
- `regionI_constant_certifier_exact.log`: successful run log.

Suggested audit order:

1. Read Sections 1-7 for the algebraic spectral-shift reduction.
2. Read Sections 8-12 for the Region-I/high-density proof.
3. Audit `clean_two_sided_shift_checker.py` and `clean_checker_m61.log` for the finite part `m <= 61`.
4. Audit Appendix A and `regionI_constant_certifier_exact.py` for the constant inequalities.
5. Read Section 13 for the independent bipodal/rank-two complement theorem.
6. Read Section 14 for the remaining Region-II target.
