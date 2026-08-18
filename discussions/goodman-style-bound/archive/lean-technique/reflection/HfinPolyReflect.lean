/-
# Dense bivariate ℤ-polynomial reflection for the `Hfin` certificates

The per-pair `Hfin` obligation is a polynomial identity of degree up to `2(m-2r-1)`
(≤ 112).  A single `ring` on it blows up in memory.  We replace it by *computational
reflection*: dense bivariate polynomials with **ℤ coefficients** (`BP := List (List ℤ)`),
an evaluation homomorphism `bpEval` into `ℝ`, and per-pair the identity is discharged as a
**data equality** `lhsBP = rhsBP` by `decide` (kernel `Int`/`List` reduction; no
`native_decide`).

`BP` layout: `p` is a list of rows indexed by the power of `q`; row `i` is a list of ℤ
indexed by the power of `ℓ`.  So `p[i][j]` is the coefficient of `qⁱ ℓʲ`.  Evaluation is
Horner in each variable.

Everything here is generic (no `sorry`, no `native_decide`); the per-pair files feed it
Python-generated data.
-/

import OddCycleBound.HighDensity.SymmetricPoly
import Mathlib.Tactic

namespace OddCycleBound.HighDensity

/-- Dense bivariate polynomial with ℤ coefficients: `p[i][j]` = coeff of `qⁱ ℓʲ`. -/
abbrev BP := List (List ℤ)

/-! ### Row (univariate in ℓ) and BP (bivariate) evaluation, Horner form -/

/-- Evaluate a coefficient row `[c₀, c₁, …]` at `ℓ`: `c₀ + ℓ(c₁ + ℓ(…))`. -/
def rowEval (l : ℝ) : List ℤ → ℝ
  | [] => 0
  | c :: cs => (c : ℝ) + l * rowEval l cs

/-- Evaluate a `BP` at `(q, ℓ)`, Horner in `q` over row evaluations. -/
def bpEval (q l : ℝ) : BP → ℝ
  | [] => 0
  | r :: rs => rowEval l r + q * bpEval q l rs

@[simp] lemma rowEval_nil (l : ℝ) : rowEval l [] = 0 := rfl
@[simp] lemma rowEval_cons (l : ℝ) (c : ℤ) (cs : List ℤ) :
    rowEval l (c :: cs) = (c : ℝ) + l * rowEval l cs := rfl
@[simp] lemma bpEval_nil (q l : ℝ) : bpEval q l [] = 0 := rfl
@[simp] lemma bpEval_cons (q l : ℝ) (r : List ℤ) (rs : BP) :
    bpEval q l (r :: rs) = rowEval l r + q * bpEval q l rs := rfl

/-! ### Ring operations on rows and BPs -/

def addRow : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => (x + y) :: addRow xs ys

def addBP : BP → BP → BP
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => addRow x y :: addBP xs ys

def smulRow (k : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => k * x :: smulRow k xs

def smulBP (k : ℤ) : BP → BP
  | [] => []
  | r :: rs => smulRow k r :: smulBP k rs

/-- Multiply two rows (convolution in `ℓ`). -/
def mulRow : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | x :: xs, b => addRow (smulRow x b) (0 :: mulRow xs b)

/-- Multiply two BPs (convolution in `q`, rows multiplied in `ℓ`). -/
def mulBP : BP → BP → BP
  | [], _ => []
  | r :: rs, b => addBP (b.map (mulRow r)) ([] :: mulBP rs b)

def powBP (b : BP) : ℕ → BP
  | 0 => [[1]]
  | n + 1 => mulBP b (powBP b n)

/-- Boolean equality of rows up to trailing zeros. -/
def eqRow : List ℤ → List ℤ → Bool
  | [], ys => ys.all (· == 0)
  | x :: xs, [] => (x == 0) && eqRow xs []
  | x :: xs, y :: ys => (x == y) && eqRow xs ys

/-- Boolean equality of BPs up to trailing/padding zeros (robust to layout). -/
def eqBP : BP → BP → Bool
  | [], ss => ss.all (fun r => r.all (· == 0))
  | r :: rs, [] => r.all (· == 0) && eqBP rs []
  | r :: rs, s :: ss => eqRow r s && eqBP rs ss

/-! ### Soundness of `eqBP` (reflection: data equality ⇒ equal evaluation) -/

lemma rowEval_eq_zero (l : ℝ) : ∀ (s : List ℤ), s.all (· == 0) = true → rowEval l s = 0
  | [], _ => rfl
  | c :: cs, h => by
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      simp only [rowEval_cons, rowEval_eq_zero l cs h.2, h.1, Int.cast_zero, mul_zero, add_zero]

lemma eqRow_sound (l : ℝ) : ∀ (a b : List ℤ), eqRow a b = true → rowEval l a = rowEval l b
  | [], b, h => by
      rw [rowEval_nil, rowEval_eq_zero l b (by simpa [eqRow] using h)]
  | x :: xs, [], h => by
      simp only [eqRow, Bool.and_eq_true, beq_iff_eq] at h
      rw [rowEval_cons, eqRow_sound l xs [] h.2, rowEval_nil, h.1]
      simp
  | x :: xs, y :: ys, h => by
      simp only [eqRow, Bool.and_eq_true, beq_iff_eq] at h
      rw [rowEval_cons, rowEval_cons, eqRow_sound l xs ys h.2, h.1]

lemma bpEval_eq_zero (q l : ℝ) : ∀ (ss : BP), ss.all (fun r => r.all (· == 0)) = true →
    bpEval q l ss = 0
  | [], _ => rfl
  | s :: ss, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp only [bpEval_cons, rowEval_eq_zero l s h.1, bpEval_eq_zero q l ss h.2,
        mul_zero, add_zero]

lemma eqBP_sound (q l : ℝ) : ∀ (a b : BP), eqBP a b = true → bpEval q l a = bpEval q l b
  | [], b, h => by
      rw [bpEval_nil, bpEval_eq_zero q l b (by simpa [eqBP] using h)]
  | x :: xs, [], h => by
      simp only [eqBP, Bool.and_eq_true] at h
      rw [bpEval_cons, eqBP_sound q l xs [] h.2, rowEval_eq_zero l x h.1]
      simp
  | x :: xs, y :: ys, h => by
      simp only [eqBP, Bool.and_eq_true] at h
      rw [bpEval_cons, bpEval_cons, eqBP_sound q l xs ys h.2, eqRow_sound l x y h.1]

/-! ### Evaluation is a ring homomorphism -/

lemma rowEval_addRow (l : ℝ) : ∀ (a b : List ℤ),
    rowEval l (addRow a b) = rowEval l a + rowEval l b
  | [], b => by simp [addRow]
  | a, [] => by cases a <;> simp [addRow]
  | x :: xs, y :: ys => by
      simp only [addRow, rowEval_cons, rowEval_addRow l xs ys, Int.cast_add]
      ring

lemma rowEval_smulRow (l : ℝ) (k : ℤ) : ∀ (a : List ℤ),
    rowEval l (smulRow k a) = (k : ℝ) * rowEval l a
  | [] => by simp [smulRow]
  | x :: xs => by
      simp only [smulRow, rowEval_cons, rowEval_smulRow l k xs, Int.cast_mul]
      ring

lemma rowEval_mulRow (l : ℝ) : ∀ (a b : List ℤ),
    rowEval l (mulRow a b) = rowEval l a * rowEval l b
  | [], b => by simp [mulRow]
  | x :: xs, b => by
      simp only [mulRow, rowEval_addRow, rowEval_smulRow, rowEval_cons,
        rowEval_mulRow l xs b, Int.cast_zero, zero_add]
      ring

lemma eval_addBP (q l : ℝ) : ∀ (a b : BP),
    bpEval q l (addBP a b) = bpEval q l a + bpEval q l b
  | [], b => by simp [addBP]
  | a, [] => by cases a <;> simp [addBP]
  | x :: xs, y :: ys => by
      simp only [addBP, bpEval_cons, rowEval_addRow, eval_addBP q l xs ys]
      ring

lemma eval_smulBP (q l : ℝ) (k : ℤ) : ∀ (a : BP),
    bpEval q l (smulBP k a) = (k : ℝ) * bpEval q l a
  | [] => by simp [smulBP]
  | r :: rs => by
      simp only [smulBP, bpEval_cons, rowEval_smulRow, eval_smulBP q l k rs]
      ring

lemma eval_map_mulRow (q l : ℝ) (r : List ℤ) : ∀ (b : BP),
    bpEval q l (b.map (mulRow r)) = rowEval l r * bpEval q l b
  | [] => by simp
  | brow :: brest => by
      simp only [List.map_cons, bpEval_cons, rowEval_mulRow,
        eval_map_mulRow q l r brest]
      ring

lemma eval_mulBP (q l : ℝ) : ∀ (a b : BP),
    bpEval q l (mulBP a b) = bpEval q l a * bpEval q l b
  | [], b => by simp [mulBP]
  | r :: rs, b => by
      simp only [mulBP, eval_addBP, eval_map_mulRow, bpEval_cons, rowEval_nil,
        zero_add, eval_mulBP q l rs b]
      ring

lemma eval_powBP (q l : ℝ) (b : BP) : ∀ n : ℕ,
    bpEval q l (powBP b n) = (bpEval q l b) ^ n
  | 0 => by simp [powBP, bpEval, rowEval]
  | n + 1 => by
      simp only [powBP, eval_mulBP, eval_powBP q l b n, pow_succ]
      ring

/-! ### Finite BP sums (for the LHS closed-form bridge) -/

/-- `bpSum f N = f 0 + f 1 + … + f (N-1)` in the BP algebra. -/
def bpSum (f : ℕ → BP) (N : ℕ) : BP :=
  (List.range N).foldr (fun j acc => addBP (f j) acc) []

lemma eval_foldr_addBP (q l : ℝ) (f : ℕ → BP) : ∀ (L : List ℕ),
    bpEval q l (L.foldr (fun j acc => addBP (f j) acc) [])
      = (L.map (fun j => bpEval q l (f j))).sum
  | [] => rfl
  | j :: js => by
      simp only [List.foldr_cons, eval_addBP, eval_foldr_addBP q l f js,
        List.map_cons, List.sum_cons]

lemma sum_range_eq_list (q l : ℝ) (g : ℕ → ℝ) : ∀ N : ℕ,
    ∑ j ∈ Finset.range N, g j = ((List.range N).map g).sum
  | 0 => by simp
  | N + 1 => by
      rw [Finset.sum_range_succ, sum_range_eq_list q l g N, List.range_succ,
        List.map_append, List.sum_append]
      simp

lemma eval_bpSum (q l : ℝ) (f : ℕ → BP) (N : ℕ) :
    bpEval q l (bpSum f N) = ∑ j ∈ Finset.range N, bpEval q l (f j) := by
  rw [bpSum, eval_foldr_addBP, sum_range_eq_list q l]

/-! ### The certificate side (`certZ`)

The nonnegativity carrier.  A term `(K, a, b, c, e)` (`K : ℕ`) stands for
`K · (3q)^a (1-3q)^b ℓ^c (m q + r - m ℓ)^e`; on the strip every factor is `≥ 0`, so the
whole sum is `≥ 0` for free.  The cleared factor `m q + r - m ℓ = m (q + r/m - ℓ)` keeps the
coefficients integral, so the whole identity lands in ℤ.  -/

/-! Certificate **grid**: `grid[e][i] = K_{i, dy-e} : ℕ`.  Row `e` collects the terms whose
`(m q + r - m ℓ)`-power is `e`; column `i` the `(3q)`-power (`(1-3q)`-power is `dx - i`,
`ℓ`-power is `dy - e`).  Grouping this way lets the RHS be built by Horner in
`u = m q + r - m ℓ` (`dy` multiplications total) instead of term-by-term, which is what makes
the in-kernel `decide` tractable for the largest pairs. -/

/-- Inner Bernstein row value `Σ_i c_i (3q)^i (1-3q)^(dx-i)` (`c_i` from `i` onward). -/
def innerReal (dx : ℕ) (q : ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | i, c :: cs => (c : ℝ) * (3 * q) ^ i * (1 - 3 * q) ^ (dx - i) + innerReal dx q (i + 1) cs

/-- Horner fold in `u`: `Σ_k Rs[k] · u^k`. -/
def uFoldReal (u : ℝ) : List ℝ → ℝ
  | [] => 0
  | rv :: rest => rv + u * uFoldReal u rest

/-- Row values `R_e = ℓ^(dy-e) · innerReal(row_e)`. -/
def RsReal (dx dy : ℕ) (q l : ℝ) : ℕ → List (List ℕ) → List ℝ
  | _, [] => []
  | e, row :: rows => (l ^ (dy - e) * innerReal dx q 0 row) :: RsReal dx dy q l (e + 1) rows

/-- The real value of the Horner certificate. -/
def certReal (m r : ℤ) (dx dy : ℕ) (q l : ℝ) (grid : List (List ℕ)) : ℝ :=
  uFoldReal ((m : ℝ) * q + (r : ℝ) - (m : ℝ) * l) (RsReal dx dy q l 0 grid)

lemma innerReal_nonneg (dx : ℕ) {q : ℝ} (h1 : (0:ℝ) ≤ 3 * q) (h2 : (0:ℝ) ≤ 1 - 3 * q) :
    ∀ (i : ℕ) (row : List ℕ), 0 ≤ innerReal dx q i row
  | _, [] => le_refl 0
  | i, c :: cs =>
      add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg c) (pow_nonneg h1 i))
        (pow_nonneg h2 (dx - i))) (innerReal_nonneg dx h1 h2 (i + 1) cs)

lemma RsReal_mem_nonneg (dx dy : ℕ) {q l : ℝ} (h1 : (0:ℝ) ≤ 3 * q) (h2 : (0:ℝ) ≤ 1 - 3 * q)
    (h3 : (0:ℝ) ≤ l) : ∀ (e : ℕ) (grid : List (List ℕ)),
    ∀ x ∈ RsReal dx dy q l e grid, 0 ≤ x
  | _, [], x, hx => by simp [RsReal] at hx
  | e, row :: rows, x, hx => by
      simp only [RsReal, List.mem_cons] at hx
      rcases hx with h | h
      · rw [h]; exact mul_nonneg (pow_nonneg h3 _) (innerReal_nonneg dx h1 h2 0 row)
      · exact RsReal_mem_nonneg dx dy h1 h2 h3 (e + 1) rows x h

lemma uFoldReal_nonneg {u : ℝ} (hu : 0 ≤ u) :
    ∀ (Rs : List ℝ), (∀ x ∈ Rs, 0 ≤ x) → 0 ≤ uFoldReal u Rs
  | [], _ => le_refl 0
  | rv :: rest, h =>
      add_nonneg (h rv (List.mem_cons.mpr (Or.inl rfl)))
        (mul_nonneg hu (uFoldReal_nonneg hu rest (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))))

lemma certReal_nonneg (m r : ℤ) (dx dy : ℕ) {q l : ℝ} (h1 : (0:ℝ) ≤ 3 * q)
    (h2 : (0:ℝ) ≤ 1 - 3 * q) (h3 : (0:ℝ) ≤ l)
    (h4 : (0:ℝ) ≤ (m : ℝ) * q + (r : ℝ) - (m : ℝ) * l) (grid : List (List ℕ)) :
    0 ≤ certReal m r dx dy q l grid :=
  uFoldReal_nonneg h4 _ (RsReal_mem_nonneg dx dy h1 h2 h3 0 grid)

/-! ### The RHS bridge: `expandCert` (a BP) evaluates to `certZ`

`expandTerm m r (K,a,b,c,e)` builds the BP `K · Xq3^a · X13^b · Xl^c · MQRL^e`, whose
`bpEval` is exactly the `certZ` term.  Hence `bpEval (expandCert …) = certZ …`, generically.
-/

/-- `3q` as a BP. -/  def Xq3 : BP := [[0], [3]]
/-- `1-3q` as a BP. -/ def X13 : BP := [[1], [-3]]
/-- `ℓ` as a BP. -/    def Xl : BP := [[0, 1]]
/-- `m q + r - m ℓ` as a BP (per-pair `m r`). -/
def MQRL (m r : ℤ) : BP := [[r, -m], [m]]

@[simp] lemma eval_Xq3 (q l : ℝ) : bpEval q l Xq3 = 3 * q := by
  simp only [Xq3, bpEval, rowEval]; push_cast; ring
@[simp] lemma eval_X13 (q l : ℝ) : bpEval q l X13 = 1 - 3 * q := by
  simp only [X13, bpEval, rowEval]; push_cast; ring
@[simp] lemma eval_Xl (q l : ℝ) : bpEval q l Xl = l := by
  simp only [Xl, bpEval, rowEval]; push_cast; ring
@[simp] lemma eval_MQRL (m r : ℤ) (q l : ℝ) :
    bpEval q l (MQRL m r) = (m : ℝ) * q + (r : ℝ) - (m : ℝ) * l := by
  simp only [MQRL, bpEval, rowEval]; push_cast; ring

/-- Inner Bernstein BP `Σ_i c_i · Xq3^i · X13^(dx-i)` (columns `i` from the given index on). -/
def innerBern (dx : ℕ) : ℕ → List ℕ → BP
  | _, [] => []
  | i, c :: cs =>
      addBP (smulBP (c : ℤ) (mulBP (powBP Xq3 i) (powBP X13 (dx - i)))) (innerBern dx (i + 1) cs)

/-- Row BPs `R_e = Xl^(dy-e) · innerBern(row_e)`. -/
def hornerRs (dx dy : ℕ) : ℕ → List (List ℕ) → List BP
  | _, [] => []
  | e, row :: rows =>
      mulBP (powBP Xl (dy - e)) (innerBern dx 0 row) :: hornerRs dx dy (e + 1) rows

/-- The Horner-assembled RHS BP: `Σ_e R_e · (MQRL)^e`. -/
def hornerBP (m r : ℤ) (dx dy : ℕ) (grid : List (List ℕ)) : BP :=
  (hornerRs dx dy 0 grid).foldr (fun R acc => addBP R (mulBP (MQRL m r) acc)) []

lemma eval_innerBern (dx : ℕ) (q l : ℝ) : ∀ (i : ℕ) (row : List ℕ),
    bpEval q l (innerBern dx i row) = innerReal dx q i row
  | _, [] => rfl
  | i, c :: cs => by
      simp only [innerBern, eval_addBP, eval_smulBP, eval_mulBP, eval_powBP, eval_Xq3,
        eval_X13, eval_innerBern dx q l (i + 1) cs, innerReal, Int.cast_natCast]
      ring

lemma eval_hornerBP (m r : ℤ) (dx dy : ℕ) (q l : ℝ) (grid : List (List ℕ)) :
    bpEval q l (hornerBP m r dx dy grid) = certReal m r dx dy q l grid := by
  rw [hornerBP, certReal]
  suffices H : ∀ (e : ℕ) (g : List (List ℕ)),
      bpEval q l ((hornerRs dx dy e g).foldr (fun R acc => addBP R (mulBP (MQRL m r) acc)) [])
        = uFoldReal ((m : ℝ) * q + (r : ℝ) - (m : ℝ) * l) (RsReal dx dy q l e g) from H 0 grid
  intro e g
  induction g generalizing e with
  | nil => rfl
  | cons row rows ih =>
      simp only [hornerRs, List.foldr_cons, eval_addBP, eval_mulBP, eval_MQRL, eval_powBP,
        eval_Xl, eval_innerBern, RsReal, uFoldReal, ih (e + 1)]

/-! ### The LHS bridge: `dkClearedBP` evaluates to `D · (q+r/m)^dy · diagKernel`

`diagKernel m r q ℓ = (m/r)(H₁ + H₂) − H₃` with three `hsym` terms.  Each `hsym` has a
closed form (a `Finset.range` sum, `hsym_replicate_append'` + `hsym_replicate'`).  We build a
matching `bpSum` for each, assemble the cleared quantity
`(m q + r)^dy · (m(H₁+H₂) − r H₃)` as a BP, and show it evaluates to
`(r · m^dy · (q+r/m)^dy) · diagKernel` — an identity that, once the three `hsym` closed forms
are substituted, is pure algebra in the *atoms* `H₁, H₂, H₃, (q+r/m)` (no expansion). -/

/-- `q` as a BP. -/    def Qbp : BP := [[0], [1]]
/-- `1-q` as a BP. -/  def Pbp : BP := [[1], [-1]]
/-- `m q + r` as a BP. -/
def MQR (m r : ℤ) : BP := [[r], [m]]

@[simp] lemma eval_Qbp (q l : ℝ) : bpEval q l Qbp = q := by
  simp only [Qbp, bpEval, rowEval]; push_cast; ring
@[simp] lemma eval_Pbp (q l : ℝ) : bpEval q l Pbp = 1 - q := by
  simp only [Pbp, bpEval, rowEval]; push_cast; ring
@[simp] lemma eval_MQR (m r : ℤ) (q l : ℝ) :
    bpEval q l (MQR m r) = (m : ℝ) * q + (r : ℝ) := by
  simp only [MQR, bpEval, rowEval]; push_cast; ring

def dkT1coeff (r n j : ℕ) : ℤ :=
  (Nat.choose (n - j + (r - 1)) (r - 1) * Nat.choose (j + (r - 1)) (r - 1) : ℤ) * (-1) ^ j
def dkT2coeff (r n j : ℕ) : ℤ :=
  (Nat.choose (n - j + (r - 1)) (r - 1) * Nat.choose (j + (r - 1)) (r - 1) : ℤ)
def dkT3coeff (r n j : ℕ) : ℤ :=
  (Nat.choose (n - 1 - j + r) r * Nat.choose (j + (r - 1)) (r - 1) : ℤ)

def dkT1BP (r n : ℕ) : BP :=
  bpSum (fun j => smulBP (dkT1coeff r n j) (mulBP (powBP Pbp (n - j)) (powBP Xl j))) (n + 1)
def dkT2BP (r n : ℕ) : BP :=
  bpSum (fun j => smulBP (dkT2coeff r n j) (mulBP (powBP Qbp (n - j)) (powBP Xl j))) (n + 1)
def dkT3BP (r n : ℕ) : BP :=
  bpSum (fun j => smulBP (dkT3coeff r n j) (mulBP (powBP Qbp (n - 1 - j)) (powBP Xl j)))
    ((n - 1) + 1)

/-- The cleared diagonal kernel as a BP: `(mq+r)^dy · (m(H₁+H₂) − r H₃)`, `dy = m-2r-1`. -/
def dkClearedBP (m r : ℕ) : BP :=
  mulBP (powBP (MQR (m : ℤ) (r : ℤ)) (m - 2 * r - 1))
    (addBP (smulBP (m : ℤ) (addBP (dkT1BP r (m - 2 * r)) (dkT2BP r (m - 2 * r))))
      (smulBP (-(r : ℤ)) (dkT3BP r (m - 2 * r))))

lemma eval_dkT1BP (r n : ℕ) (q l : ℝ) :
    bpEval q l (dkT1BP r n)
      = ∑ j ∈ Finset.range (n + 1), (dkT1coeff r n j : ℝ) * (1 - q) ^ (n - j) * l ^ j := by
  rw [dkT1BP, eval_bpSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eval_smulBP, eval_mulBP, eval_powBP, eval_Pbp, eval_Xl]; ring

lemma eval_dkT2BP (r n : ℕ) (q l : ℝ) :
    bpEval q l (dkT2BP r n)
      = ∑ j ∈ Finset.range (n + 1), (dkT2coeff r n j : ℝ) * q ^ (n - j) * l ^ j := by
  rw [dkT2BP, eval_bpSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eval_smulBP, eval_mulBP, eval_powBP, eval_Qbp, eval_Xl]; ring

lemma eval_dkT3BP (r n : ℕ) (q l : ℝ) :
    bpEval q l (dkT3BP r n)
      = ∑ j ∈ Finset.range ((n - 1) + 1),
          (dkT3coeff r n j : ℝ) * q ^ (n - 1 - j) * l ^ j := by
  rw [dkT3BP, eval_bpSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eval_smulBP, eval_mulBP, eval_powBP, eval_Qbp, eval_Xl]; ring

/-- `H₁ = hsym (replicate r (1-q) ++ replicate r (-ℓ)) n` matches `dkT1BP`. -/
lemma hsym1_eq (r n : ℕ) (hr : r ≠ 0) (q l : ℝ) :
    hsym (List.replicate r (1 - q) ++ List.replicate r (-l)) n
      = bpEval q l (dkT1BP r n) := by
  rw [eval_dkT1BP, hsym_replicate_append' (1 - q) hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym_replicate' (-l) hr, dkT1coeff]
  push_cast
  rw [neg_pow]
  ring

lemma hsym2_eq (r n : ℕ) (hr : r ≠ 0) (q l : ℝ) :
    hsym (List.replicate r q ++ List.replicate r l) n = bpEval q l (dkT2BP r n) := by
  rw [eval_dkT2BP, hsym_replicate_append' q hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym_replicate' l hr, dkT2coeff]
  push_cast
  ring

lemma hsym3_eq (r n : ℕ) (hr : r ≠ 0) (q l : ℝ) :
    hsym (List.replicate (r + 1) q ++ List.replicate r l) (n - 1)
      = bpEval q l (dkT3BP r n) := by
  rw [eval_dkT3BP, hsym_replicate_append' q (by omega : r + 1 ≠ 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym_replicate' l hr, dkT3coeff]
  push_cast
  ring

/-- **LHS bridge.**  `bpEval (dkClearedBP m r) = (r · m^dy · (q+r/m)^dy) · diagKernel m r q ℓ`. -/
lemma eval_dkClearedBP (m r : ℕ) (hr : r ≠ 0) (hm : (m : ℝ) ≠ 0) (q l : ℝ) :
    bpEval q l (dkClearedBP m r)
      = ((r : ℝ) * (m : ℝ) ^ (m - 2 * r - 1) * (q + (r : ℝ) / (m : ℝ)) ^ (m - 2 * r - 1))
          * diagKernel m r q l := by
  rw [dkClearedBP]
  rw [eval_mulBP, eval_powBP, eval_MQR, eval_addBP, eval_smulBP, eval_smulBP, eval_addBP,
    ← hsym1_eq r (m - 2 * r) hr, ← hsym2_eq r (m - 2 * r) hr, ← hsym3_eq r (m - 2 * r) hr]
  rw [diagKernel]
  push_cast
  have hmq : ((m : ℝ) * q + (r : ℝ)) ^ (m - 2 * r - 1)
      = (m : ℝ) ^ (m - 2 * r - 1) * (q + (r : ℝ) / (m : ℝ)) ^ (m - 2 * r - 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hmq]
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  set H1 := hsym (List.replicate r (1 - q) ++ List.replicate r (-l)) (m - 2 * r)
  set H2 := hsym (List.replicate r q ++ List.replicate r l) (m - 2 * r)
  set H3 := hsym (List.replicate (r + 1) q ++ List.replicate r l) (m - 2 * r - 1)
  set Mp := (m : ℝ) ^ (m - 2 * r - 1)
  set Y := (q + (r : ℝ) / (m : ℝ)) ^ (m - 2 * r - 1)
  field_simp
  ring

end OddCycleBound.HighDensity
