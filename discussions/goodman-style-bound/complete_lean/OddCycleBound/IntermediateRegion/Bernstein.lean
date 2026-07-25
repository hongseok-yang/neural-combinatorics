import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The two Bernstein positivity certificates (paper Appendix, `paper_new_region2_v2.tex` lines 3831–3939)

The `N = 7` corner of the linear branch (paper §9, `lem:N7-small-v` and `lem:N7-middle-v`) needs two
fixed univariate positivity facts:

* `bernsteinP9_pos` — the degree-nine polynomial `P₉` of `eq:P9-small` (line 3420) is positive on
  `[0, 1/2]` (`lem:bernstein-P9`, line 3868);
* `bernsteinQ10_pos` — the degree-ten polynomial `Q₁₀` of `eq:Q10` (line 3506) is positive on
  `[9/20, 5/7]` (`lem:bernstein-Q10`, line 3906).

Both are proved by the Bernstein partition-of-unity principle of `eq:power-to-bernstein` (line 3856),
*without* `decide`/`native_decide`.  On an interval `[c,d]` put `t = (x−c)/(d−c)`; then the Bernstein
basis functions `Bᵢₙ(x) = C(n,i) tⁱ (1−t)ⁿ⁻ⁱ` are nonnegative on `[c,d]` and sum to `(t + (1−t))ⁿ = 1`.
If `P = Σ βᵢ Bᵢₙ` with every `βᵢ` bounded below by a positive constant `β₀`, then, since the basis is a
partition of unity,
```
      P − β₀ = Σ (βᵢ − β₀) Bᵢₙ ≥ 0,   so   P ≥ β₀ > 0.
```
The Bernstein coefficients `βᵢ` printed in the paper (lines 3888–3898 for `P₉`, 3914–3925 for `Q₁₀`) are
used verbatim; the resulting identity is a single polynomial identity closed by `ring`, and the
coefficient/positivity side-conditions are closed by `norm_num`.  For `P₉` the interval is `[0, 1/2]`, so
`t = 2s`, `1 − t = 1 − 2s`, and `β₀ = 1/2` (the minimal coefficient is `≈ 0.6487`).  For `Q₁₀` the
interval is `[9/20, 5/7]`, so `t = (140y − 63)/37`, `1 − t = (100 − 140y)/37`, and `β₀ = 90` (the minimal
coefficient is `≈ 94.69`); we clear the common denominator `37¹⁰` to keep the identity division-free.
-/

noncomputable section

namespace OddCycleBound.IntermediateRegion

open Set

/-- Paper `eq:P9-small` (line 3420): the degree-nine certificate polynomial. -/
def bernsteinP9 (s : ℝ) : ℝ :=
  10395 / 128 * s ^ 9 - 333333 / 2048 * s ^ 8 + 13635 / 128 * s ^ 7 + 51005 / 2048 * s ^ 6
    - 18765 / 128 * s ^ 5 + 264969 / 2048 * s ^ 4 - 4995 / 64 * s ^ 3 + 11913 / 256 * s ^ 2
    - 135 / 8 * s + 3

/-- Paper `eq:Q10` (line 3506): the degree-ten certificate polynomial. -/
def bernsteinQ10 (y : ℝ) : ℝ :=
  58 * y ^ 10 + 319 * y ^ 9 - 1793 * y ^ 8 - 11280 * y ^ 7 + 9788 * y ^ 6 - 11354 * y ^ 5
    + 350 * y ^ 4 + 5880 * y ^ 3 - 6174 * y ^ 2 + 5635 * y - 1029

/-- Paper `lem:bernstein-P9` (line 3868): `P₉ > 0` on `[0, 1/2]`.

The Bernstein coefficients of `P₉` on `[0, 1/2]` (line 3888) are, in increasing index order,
`3, 33/16, 17795/12288, 29843/28672, 361761/458752, 918263/1376256, 7142309/11010048,
1096445/1572864, 390495/524288, 361511/524288`; each exceeds `β₀ = 1/2`, so the
partition-of-unity identity below (checked by `ring`) gives `P₉ s ≥ 1/2`. -/
theorem bernsteinP9_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : 0 < bernsteinP9 s := by
  obtain ⟨h0, h1⟩ := hs
  have hA : (0 : ℝ) ≤ 2 * s := by linarith
  have hB : (0 : ℝ) ≤ 1 - 2 * s := by linarith
  -- Every Bernstein term `c · (2s)ⁱ (1−2s)ʲ` with `c ≥ 0` is nonnegative on the interval.
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (2 * s) ^ i * (1 - 2 * s) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg hA i)) (pow_nonneg hB j)
  -- `P₉ = 1/2 + Σ (βᵢ − 1/2) C(9,i) (2s)ⁱ (1−2s)⁹⁻ⁱ` (partition-of-unity identity).
  have key : bernsteinP9 s = 1 / 2
      + (3 - 1 / 2) * 1 * (2 * s) ^ 0 * (1 - 2 * s) ^ 9
      + (33 / 16 - 1 / 2) * 9 * (2 * s) ^ 1 * (1 - 2 * s) ^ 8
      + (17795 / 12288 - 1 / 2) * 36 * (2 * s) ^ 2 * (1 - 2 * s) ^ 7
      + (29843 / 28672 - 1 / 2) * 84 * (2 * s) ^ 3 * (1 - 2 * s) ^ 6
      + (361761 / 458752 - 1 / 2) * 126 * (2 * s) ^ 4 * (1 - 2 * s) ^ 5
      + (918263 / 1376256 - 1 / 2) * 126 * (2 * s) ^ 5 * (1 - 2 * s) ^ 4
      + (7142309 / 11010048 - 1 / 2) * 84 * (2 * s) ^ 6 * (1 - 2 * s) ^ 3
      + (1096445 / 1572864 - 1 / 2) * 36 * (2 * s) ^ 7 * (1 - 2 * s) ^ 2
      + (390495 / 524288 - 1 / 2) * 9 * (2 * s) ^ 8 * (1 - 2 * s) ^ 1
      + (361511 / 524288 - 1 / 2) * 1 * (2 * s) ^ 9 * (1 - 2 * s) ^ 0 := by
    unfold bernsteinP9; ring
  linarith [key,
    term (((3 : ℝ) - 1 / 2) * 1) 0 9 (by norm_num),
    term (((33 : ℝ) / 16 - 1 / 2) * 9) 1 8 (by norm_num),
    term (((17795 : ℝ) / 12288 - 1 / 2) * 36) 2 7 (by norm_num),
    term (((29843 : ℝ) / 28672 - 1 / 2) * 84) 3 6 (by norm_num),
    term (((361761 : ℝ) / 458752 - 1 / 2) * 126) 4 5 (by norm_num),
    term (((918263 : ℝ) / 1376256 - 1 / 2) * 126) 5 4 (by norm_num),
    term (((7142309 : ℝ) / 11010048 - 1 / 2) * 84) 6 3 (by norm_num),
    term (((1096445 : ℝ) / 1572864 - 1 / 2) * 36) 7 2 (by norm_num),
    term (((390495 : ℝ) / 524288 - 1 / 2) * 9) 8 1 (by norm_num),
    term (((361511 : ℝ) / 524288 - 1 / 2) * 1) 9 0 (by norm_num)]

/-- Paper `lem:bernstein-Q10` (line 3906): `Q₁₀ > 0` on `[9/20, 5/7]`.

The Bernstein coefficients of `Q₁₀` on `[9/20, 5/7]` (line 3914) are all `≥ β₀ = 90` (the minimal one is
`26748047904/282475249 ≈ 94.69`).  With `t = (140y − 63)/37` and `1 − t = (100 − 140y)/37`, clearing the
common denominator `37¹⁰` turns `Q₁₀ − 90` into the manifestly nonnegative Bernstein sum below. -/
theorem bernsteinQ10_pos {y : ℝ} (hy : y ∈ Icc (9 / 20 : ℝ) (5 / 7)) : 0 < bernsteinQ10 y := by
  obtain ⟨h0, h1⟩ := hy
  have hA : (0 : ℝ) ≤ 140 * y - 63 := by linarith
  have hB : (0 : ℝ) ≤ 100 - 140 * y := by linarith
  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (140 * y - 63) ^ i * (100 - 140 * y) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg hA i)) (pow_nonneg hB j)
  -- `37¹⁰·(Q₁₀ − 90) = Σ (βᵢ − 90) C(10,i) (140y−63)ⁱ (100−140y)¹⁰⁻ⁱ` (division-free identity).
  have key : 37 ^ 10 * (bernsteinQ10 y - 90) =
        (3243737479716939 / 5120000000000 - 90) * 1 * (140 * y - 63) ^ 0 * (100 - 140 * y) ^ 10
      + (24439395309190297 / 35840000000000 - 90) * 10 * (140 * y - 63) ^ 1 * (100 - 140 * y) ^ 9
      + (2256629681468091 / 3136000000000 - 90) * 45 * (140 * y - 63) ^ 2 * (100 - 140 * y) ^ 8
      + (653354162075429 / 878080000000 - 90) * 120 * (140 * y - 63) ^ 3 * (100 - 140 * y) ^ 7
      + (3033296182962901 / 4033680000000 - 90) * 210 * (140 * y - 63) ^ 4 * (100 - 140 * y) ^ 6
      + (625950152734243 / 847072800000 - 90) * 252 * (140 * y - 63) ^ 5 * (100 - 140 * y) ^ 5
      + (1151767076423 / 1647086000 - 90) * 210 * (140 * y - 63) ^ 6 * (100 - 140 * y) ^ 4
      + (6182915802683 / 9882516000 - 90) * 120 * (140 * y - 63) ^ 7 * (100 - 140 * y) ^ 3
      + (7481469276 / 14706125 - 90) * 45 * (140 * y - 63) ^ 8 * (100 - 140 * y) ^ 2
      + (67938971678 / 201768035 - 90) * 10 * (140 * y - 63) ^ 9 * (100 - 140 * y) ^ 1
      + (26748047904 / 282475249 - 90) * 1 * (140 * y - 63) ^ 10 * (100 - 140 * y) ^ 0 := by
    unfold bernsteinQ10; ring
  have hsum : 0 ≤ 37 ^ 10 * (bernsteinQ10 y - 90) := by
    rw [key]
    linarith [term (((3243737479716939 : ℝ) / 5120000000000 - 90) * 1) 0 10 (by norm_num),
      term (((24439395309190297 : ℝ) / 35840000000000 - 90) * 10) 1 9 (by norm_num),
      term (((2256629681468091 : ℝ) / 3136000000000 - 90) * 45) 2 8 (by norm_num),
      term (((653354162075429 : ℝ) / 878080000000 - 90) * 120) 3 7 (by norm_num),
      term (((3033296182962901 : ℝ) / 4033680000000 - 90) * 210) 4 6 (by norm_num),
      term (((625950152734243 : ℝ) / 847072800000 - 90) * 252) 5 5 (by norm_num),
      term (((1151767076423 : ℝ) / 1647086000 - 90) * 210) 6 4 (by norm_num),
      term (((6182915802683 : ℝ) / 9882516000 - 90) * 120) 7 3 (by norm_num),
      term (((7481469276 : ℝ) / 14706125 - 90) * 45) 8 2 (by norm_num),
      term (((67938971678 : ℝ) / 201768035 - 90) * 10) 9 1 (by norm_num),
      term (((26748047904 : ℝ) / 282475249 - 90) * 1) 10 0 (by norm_num)]
  have h37 : (0 : ℝ) < 37 ^ 10 := by positivity
  by_contra hcon
  have hle : bernsteinQ10 y ≤ 0 := not_lt.mp hcon
  have hneg : 37 ^ 10 * (bernsteinQ10 y - 90) < 0 :=
    mul_neg_of_pos_of_neg h37 (by linarith)
  linarith

end OddCycleBound.IntermediateRegion
