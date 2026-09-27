import EvenCycleApex.Host.EdgeDensity
import EvenCycleApex.Graph.DensityAlgebra
import EvenCycleApex.Foundation.FiniteBridge

/-!
# The Euclidean model of a host kernel

Plan D2.  The kernel operator `(T f)(i) = ∑ⱼ wⱼ L(i, j) f(j)` on `L²(w)` is modelled on ordinary
Euclidean `ℝ^d` by the symmetric matrix `hostMatrix w L = (√wᵢ · L(i, j) · √wⱼ)`, the image of `T`
under the isometry `f ↦ (√wᵢ fᵢ)`.  The constant function `1` becomes the unit vector
`hostUnit w = (√wᵢ)` — **not** the all-ones vector.

* `hostMatrix_isHermitian`: symmetric kernels give symmetric matrices.
* `hostUnit_dot_self`, `hostUnit_rayleigh`: `‖u‖ = 1` and `⟨u, S u⟩ = ∑ᵢⱼ wᵢ L(i, j) wⱼ`.
* `hostDensity_cycle_eq_trace` (blueprint `lem:cycle-trace`): `t(C_n, L) = Tr S^n` for `n ≥ 3`,
  from the copied closed-walk expansion `trace_weighted_pow_eq_sum` and the bijection
  `i ↦ {i, i + 1}` between `Fin n` and the edges of `cycleGraph n`.
-/

open Finset Matrix SimpleGraph

namespace EvenCycleApex

variable {d : ℕ}

/-- The Euclidean matrix `√wᵢ · L(i, j) · √wⱼ` of the kernel operator of `L`. -/
noncomputable def hostMatrix (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => L i j * Real.sqrt (w i) * Real.sqrt (w j)

lemma hostMatrix_apply (w : Fin d → ℝ) (L : Fin d → Fin d → ℝ) (i j : Fin d) :
    hostMatrix w L i j = L i j * Real.sqrt (w i) * Real.sqrt (w j) := rfl

lemma hostMatrix_isHermitian (w : Fin d → ℝ) {L : Fin d → Fin d → ℝ}
    (hL : ∀ i j, L i j = L j i) : (hostMatrix w L).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, hostMatrix_apply, hL j i]
  ring

/-- The unit vector `uᵢ = √wᵢ`, the image of the constant function `1`. -/
noncomputable def hostUnit (w : Fin d → ℝ) : Fin d → ℝ := fun i => Real.sqrt (w i)

lemma hostUnit_dot_self {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    hostUnit w ⬝ᵥ hostUnit w = 1 := by
  simp only [dotProduct, hostUnit, Real.mul_self_sqrt (hw _), hsum]

/-- The Rayleigh value at the unit vector is the double mean `∑ᵢⱼ wᵢ L(i, j) wⱼ`. -/
lemma hostUnit_rayleigh {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i) (L : Fin d → Fin d → ℝ) :
    hostUnit w ⬝ᵥ (hostMatrix w L *ᵥ hostUnit w) = ∑ i, ∑ j, w i * L i j * w j := by
  simp only [dotProduct, mulVec, hostUnit, hostMatrix_apply, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hi := Real.mul_self_sqrt (hw i)
  have hj := Real.mul_self_sqrt (hw j)
  calc Real.sqrt (w i) * (L i j * Real.sqrt (w i) * Real.sqrt (w j) * Real.sqrt (w j))
      = (Real.sqrt (w i) * Real.sqrt (w i)) * L i j * (Real.sqrt (w j) * Real.sqrt (w j)) := by
        ring
    _ = w i * L i j * w j := by rw [hi, hj]

/-! ### The cycle -/

/-- The edges of the cycle `C_{m+3}`, each written as `{i, i + 1}` exactly once: for a symmetric
`g`, `∏ᵢ g(i, i + 1) = ∏_{edges} g`. -/
lemma prod_cycle_eq_prod_edgePairs (m : ℕ) {β : Type*} [CommMonoid β]
    (g : Fin (m + 3) → Fin (m + 3) → β) (hg : ∀ a b, g a b = g b a) :
    ∏ i : Fin (m + 3), g i (i + 1) = ∏ p ∈ edgePairs (cycleGraph (m + 3)), g p.1 p.2 := by
  have hadj : ∀ i : Fin (m + 3), (cycleGraph (m + 3)).Adj i (i + 1) := fun i => by
    rw [cycleGraph_adj]
    right
    exact add_sub_cancel_left i 1
  have htwo : (1 + 1 : Fin (m + 3)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < m + 3 by omega),
      Nat.mod_eq_of_lt (show 1 + 1 < m + 3 by omega)] at h'
    omega
  refine prod_nbij (fun i => sortPair i (i + 1)) (fun i _ => sortPair_mem_edgePairs (hadj i))
    (fun i _ j _ hij => ?_) (fun p hp => ?_) (fun i _ => (apply_sortPair g hg i (i + 1)).symm)
  · -- injectivity: `{i, i + 1} = {j, j + 1}` forces `i = j`, since `2 ≠ 0` in `Fin (m + 3)`
    have hs := congrArg (fun q : Fin (m + 3) × Fin (m + 3) => s(q.1, q.2)) hij
    simp only [sym2_sortPair_eq] at hs
    rcases Sym2.eq_iff.mp hs with ⟨h, _⟩ | ⟨h₁, h₂⟩
    · exact h
    · exfalso
      apply htwo
      rw [← h₂, add_assoc] at h₁
      exact add_eq_left.mp h₁.symm
  · -- surjectivity: an edge `p` with `p.1 < p.2` is `{p.1, p.1 + 1}` or `{p.2, p.2 + 1}`
    rw [mem_coe, mem_edgePairs, cycleGraph_adj] at hp
    obtain ⟨hlt, h | h⟩ := hp
    · refine ⟨p.2, mem_coe.mpr (mem_univ _), ?_⟩
      have h' : p.1 = p.2 + 1 := by rw [← h]; exact (add_sub_cancel p.2 p.1).symm
      simp only [← h', sortPair_of_gt hlt]
    · refine ⟨p.1, mem_coe.mpr (mem_univ _), ?_⟩
      have h' : p.2 = p.1 + 1 := by rw [← h]; exact (add_sub_cancel p.1 p.2).symm
      simp only [← h', sortPair_of_lt hlt]

/-- **`lem:cycle-trace`.**  For a symmetric kernel and `n ≥ 3`, `t(C_n, L) = Tr S^n`. -/
theorem hostDensity_cycle_eq_trace {w : Fin d → ℝ} (hw : ∀ i, 0 ≤ w i)
    {L : Fin d → Fin d → ℝ} (hL : ∀ i j, L i j = L j i) {n : ℕ} (hn : 3 ≤ n) :
    hostDensity w (cycleGraph n) L = trace (hostMatrix w L ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 = (m + 2) + 1 from rfl, hostMatrix, trace_weighted_pow_eq_sum w hw L (m + 2)]
  unfold hostDensity
  refine sum_congr rfl fun x _ => ?_
  rw [prod_cycle_eq_prod_edgePairs m (fun a b => L (x a) (x b)) (fun a b => hL _ _)]

end EvenCycleApex
