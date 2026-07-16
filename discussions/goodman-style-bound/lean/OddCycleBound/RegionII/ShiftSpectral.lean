import OddCycleBound.RegionII.DirectedKernel

/-!
# Spectral lower bound for the one-sided linear term

This file evaluates the finite return polynomial on the complete nonzero
spectrum.  Its constant term automatically pays for a possible zero-eigenspace
residual, while orthogonality removes the distinguished frontier mode from the
safe-spectrum comparison.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.RegionII

open OddCycleBound.HighDensity
open OddCycleBound.LowBand
open OddCycleBound.LowBand.InfiniteSpectral

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/-- The two iterator APIs used by the Krylov bridge and the infinite spectral
expansion have identical recursions. -/
lemma linearIter_toLinearMap_eq_opIter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E) (n : Nat) (v : E) :
    linearIter T.toLinearMap n v = opIter T n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T (linearIter T.toLinearMap n v) = T (opIter T n v)
      rw [ih]

/-- Split the leading term from the finite directed geometric polynomial. -/
lemma oneSidedGeom_eq_head_add
    (p x : Real) {m : Nat} (hm2 : 2 <= m) :
    oneSidedGeom p m x =
      p ^ (m - 2) +
        ∑ k ∈ Finset.range (m - 2),
          p ^ (m - 3 - k) * x ^ (k + 1) := by
  unfold oneSidedGeom
  have hrange : m - 1 = (m - 2) + 1 := by omega
  rw [hrange, Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < m - 2 := Finset.mem_range.mp hk
  have hexp : m - 2 - (k + 1) = m - 3 - k := by omega
  rw [hexp]

/-- Quadratic evaluation of the finite return polynomial on the centered
graphon operator. -/
noncomputable def centeredReturnQuadratic
    (hW : IsGraphon W mu) (p : Real) (m : Nat) (v : Lp Real 2 mu) : Real :=
  p ^ (m - 2) * inner Real v v +
    ∑ k ∈ Finset.range (m - 2),
      p ^ (m - 3 - k) *
        inner Real v (opIter (centeredGraphonOp hW) (k + 1) v)

/-- The unsigned graphon coefficient is the return polynomial evaluated on
the centered degree vector. -/
theorem unsignedUCoeff_eq_centeredReturnQuadratic
    (hW : IsGraphon W mu) {m : Nat} (hm2 : 2 <= m) :
    unsignedUCoeff (edgeDensity W mu) (specMoment W mu) m =
      centeredReturnQuadratic hW (edgeDensity W mu) m
        (centeredDegreeL2 hW) := by
  rw [unsignedUCoeff, if_pos hm2]
  have hrange : m - 1 = (m - 2) + 1 := by omega
  rw [hrange, Finset.sum_range_succ']
  unfold centeredReturnQuadratic
  simp only [Nat.sub_zero, pow_zero, mul_one]
  rw [← inner_linearIter_centeredGraphonOp_eq_specMoment hW 0,
    linearIter_toLinearMap_eq_opIter]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < m - 2 := Finset.mem_range.mp hk
  have hindex : m - 2 - (k + 1) = m - 3 - k := by omega
  rw [hindex]
  rw [← inner_linearIter_centeredGraphonOp_eq_specMoment hW (k + 1),
    linearIter_toLinearMap_eq_opIter]

/-- Spectral series for the nonconstant part of the return polynomial. -/
theorem centeredReturnQuadratic_tail_hasSum
    (hW : IsGraphon W mu) (p : Real) {m : Nat} (hm2 : 2 <= m)
    (v : Lp Real 2 mu) :
    HasSum
      (fun j : CenteredEigenIndex hW =>
        (oneSidedGeom p m (centeredEigenvalue hW j) - p ^ (m - 2)) *
          inner Real v (centeredEigenmode hW j) ^ 2)
      (centeredReturnQuadratic hW p m v -
        p ^ (m - 2) * inner Real v v) := by
  classical
  let s := Finset.range (m - 2)
  have hfinite : HasSum
      (fun j : CenteredEigenIndex hW =>
        ∑ k ∈ s,
          (p ^ (m - 3 - k) * centeredEigenvalue hW j ^ (k + 1)) *
            inner Real v (centeredEigenmode hW j) ^ 2)
      (∑ k ∈ s,
        p ^ (m - 3 - k) *
          inner Real v (opIter (centeredGraphonOp hW) (k + 1) v)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have haSeries := indexed_quadratic_expansion_iter
          (centeredGraphonOp hW)
          (centeredEigenmode hW) (centeredEigenvalue hW)
          (centeredEigenmode_diagonal hW)
          (centeredGraphonOp_action_expansion hW) a v
        have haScaled := haSeries.mul_left (p ^ (m - 3 - a))
        simpa [Finset.sum_insert, ha, mul_assoc] using haScaled.add ih
  have hconverted : HasSum
      (fun j : CenteredEigenIndex hW =>
        (oneSidedGeom p m (centeredEigenvalue hW j) - p ^ (m - 2)) *
          inner Real v (centeredEigenmode hW j) ^ 2)
      (∑ k ∈ s,
        p ^ (m - 3 - k) *
          inner Real v (opIter (centeredGraphonOp hW) (k + 1) v)) :=
    hfinite.congr_fun (fun j => by
      rw [oneSidedGeom_eq_head_add p (centeredEigenvalue hW j) hm2]
      rw [add_sub_cancel_left]
      rw [Finset.sum_mul])
  convert hconverted using 1
  unfold centeredReturnQuadratic
  dsimp [s]
  ring

/-- The safe endpoint gives a quadratic lower bound for the whole return
polynomial on vectors orthogonal to the frontier mode. -/
theorem centeredReturnQuadratic_safe_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {p : Real} {m : Nat} (hp : 0 < p) (hm : Odd m) (hm2 : 2 <= m)
    {v : Lp Real 2 mu}
    (horth : inner Real v (centeredEigenmode hW i) = 0) :
    directedKernel p m (frontierSafeRadius hW i) * inner Real v v <=
      centeredReturnQuadratic hW p m v := by
  let L := frontierSafeRadius hW i
  let K := directedKernel p m L
  let a0 := p ^ (m - 2)
  have htail := centeredReturnQuadratic_tail_hasSum hW p hm2 v
  have hcoord : Summable (fun j : CenteredEigenIndex hW =>
      inner Real v (centeredEigenmode hW j) ^ 2) :=
    summable_inner_sq_of_orthonormal (centeredEigenmode_orthonormal hW) v
  have hlower : Summable (fun j : CenteredEigenIndex hW =>
      (K - a0) * inner Real v (centeredEigenmode hW j) ^ 2) :=
    hcoord.mul_left (K - a0)
  have hpoint : forall j : CenteredEigenIndex hW,
      (K - a0) * inner Real v (centeredEigenmode hW j) ^ 2 <=
        (oneSidedGeom p m (centeredEigenvalue hW j) - a0) *
          inner Real v (centeredEigenmode hW j) ^ 2 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [horth]
    · have habs := abs_complementEigenvalue_le_frontierSafeRadius hW hji
      have hmem : complementEigenvalue hW j ∈ Set.Icc (-L) L := by
        exact abs_le.mp habs
      have hkernel := directedKernel_safe_lower_bound hp
        (frontierSafeRadius_nonneg hW i) hmem hm hm2
      have hidentify :
          directedKernel p m (complementEigenvalue hW j) =
            oneSidedGeom p m (centeredEigenvalue hW j) := by
        simp [directedKernel, complementEigenvalue]
      rw [hidentify] at hkernel
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right hkernel a0) (sq_nonneg _)
  have hseriesLower :
      (∑' j : CenteredEigenIndex hW,
        (K - a0) * inner Real v (centeredEigenmode hW j) ^ 2) <=
        centeredReturnQuadratic hW p m v - a0 * inner Real v v :=
    hasSum_le hpoint hlower.hasSum htail
  rw [hcoord.tsum_mul_left (K - a0)] at hseriesLower
  have hbessel :
      (∑' j : CenteredEigenIndex hW,
        inner Real v (centeredEigenmode hW j) ^ 2) <= inner Real v v :=
    tsum_inner_sq_le_self_of_orthonormal
      (centeredEigenmode_orthonormal hW) v
  have hKle : K <= a0 := by
    dsimp [K, L, a0]
    exact directedKernel_le_zero_value hp
      (frontierSafeRadius_nonneg hW i) hm hm2
  have hresidual :
      (K - a0) * inner Real v v <=
        (K - a0) *
          (∑' j : CenteredEigenIndex hW,
            inner Real v (centeredEigenmode hW j) ^ 2) :=
    mul_le_mul_of_nonpos_left hbessel (sub_nonpos.mpr hKle)
  linarith

/-- Linear-term lower bound with the frontier coupling split off exactly. -/
theorem graphon_oneSidedUCoeff_frontier_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hp : 0 < edgeDensity W mu)
    (hm : Odd m) (hm2 : 2 <= m) :
    let p := edgeDensity W mu
    let alpha := complementEigenvalue hW i
    let L := frontierSafeRadius hW i
    let c := inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hW - c • centeredEigenmode hW i
    directedKernel p m alpha * c ^ 2 +
        directedKernel p m L * ‖gs‖ ^ 2 <=
      oneSidedUCoeff p (complementCompressionMoment hW) m := by
  dsimp only
  let p := edgeDensity W mu
  let alpha := complementEigenvalue hW i
  let L := frontierSafeRadius hW i
  let phi := centeredEigenmode hW i
  let g := centeredDegreeL2 hW
  let c := inner Real g phi
  let gs := g - c • phi
  have hp' : 0 < p := hp
  have hphiNorm : ‖phi‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have horth : inner Real gs phi = 0 := by
    dsimp [gs, c]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      hphiNorm]
    simp
  have hdecomp : g = c • phi + gs := by
    dsimp [gs]
    abel
  have hquadDecomp :
      centeredReturnQuadratic hW p m g =
        directedKernel p m alpha * c ^ 2 +
          centeredReturnQuadratic hW p m gs := by
    unfold centeredReturnQuadratic
    have hdiag : forall n : Nat,
        opIter (centeredGraphonOp hW) n phi =
          centeredEigenvalue hW i ^ n • phi := by
      intro n
      induction n with
      | zero => simp [opIter]
      | succ n ih =>
          change centeredGraphonOp hW
              (opIter (centeredGraphonOp hW) n phi) = _
          rw [ih, map_smul, centeredEigenmode_diagonal]
          simp [phi, pow_succ, mul_comm, smul_smul]
    have hopAdd : forall n : Nat, forall x y : Lp Real 2 mu,
        opIter (centeredGraphonOp hW) n (x + y) =
          opIter (centeredGraphonOp hW) n x +
            opIter (centeredGraphonOp hW) n y := by
      intro n
      induction n with
      | zero => intro x y; rfl
      | succ n ih =>
          intro x y
          change centeredGraphonOp hW
              (opIter (centeredGraphonOp hW) n (x + y)) =
            centeredGraphonOp hW (opIter (centeredGraphonOp hW) n x) +
              centeredGraphonOp hW (opIter (centeredGraphonOp hW) n y)
          rw [ih, map_add]
    have hopSmul : forall n : Nat, forall r : Real, forall x : Lp Real 2 mu,
        opIter (centeredGraphonOp hW) n (r • x) =
          r • opIter (centeredGraphonOp hW) n x := by
      intro n
      induction n with
      | zero => intro r x; rfl
      | succ n ih =>
          intro r x
          change centeredGraphonOp hW
              (opIter (centeredGraphonOp hW) n (r • x)) =
            r • centeredGraphonOp hW
              (opIter (centeredGraphonOp hW) n x)
          rw [ih, map_smul]
    have hcross : forall n : Nat,
        inner Real (c • phi)
          (opIter (centeredGraphonOp hW) n gs) = 0 := by
      intro n
      cases n with
      | zero =>
          change inner Real (c • phi) gs = 0
          have horthSym : inner Real phi gs = 0 := by
            rw [real_inner_comm, horth]
          rw [inner_smul_left, horthSym]
          simp
      | succ n =>
          have hsym := indexed_action_expansion_iter
            (centeredGraphonOp hW) (centeredEigenmode hW)
            (centeredEigenvalue hW) (centeredEigenmode_diagonal hW)
            (centeredGraphonOp_action_expansion hW) n gs
          have hpair := hsym.mapL ((innerSL Real) (c • phi))
          have hpair' : HasSum
              (fun j : CenteredEigenIndex hW =>
                inner Real (c • phi)
                  ((centeredEigenvalue hW j ^ (n + 1) *
                    inner Real gs (centeredEigenmode hW j)) •
                      centeredEigenmode hW j))
              (inner Real (c • phi)
                (opIter (centeredGraphonOp hW) (n + 1) gs)) := by
            simpa [inner_smul_left, inner_smul_right, mul_assoc,
              mul_comm, mul_left_comm] using hpair
          have hzeroTerms : (fun j : CenteredEigenIndex hW =>
              inner Real (c • phi)
                ((centeredEigenvalue hW j ^ (n + 1) *
                  inner Real gs (centeredEigenmode hW j)) •
                    centeredEigenmode hW j)) = 0 := by
            funext j
            by_cases hji : j = i
            · subst j
              change inner Real (c • phi)
                ((centeredEigenvalue hW i ^ (n + 1) *
                  inner Real gs phi) • phi) = 0
              rw [horth]
              simp
            · have hmodeOrth :
                  inner Real phi (centeredEigenmode hW j) = 0 := by
                dsimp [phi]
                exact (centeredEigenmode_orthonormal hW).2 (Ne.symm hji)
              rw [inner_smul_left, inner_smul_right, hmodeOrth]
              simp
          rw [hzeroTerms] at hpair'
          exact hpair'.unique hasSum_zero
    rw [hdecomp]
    simp_rw [hopAdd]
    simp only [inner_add_left, inner_add_right]
    simp_rw [hcross]
    have hcrossRight : forall n : Nat,
        inner Real gs (opIter (centeredGraphonOp hW) n (c • phi)) = 0 := by
      intro n
      rw [hopSmul, hdiag]
      simp only [inner_smul_right]
      rw [horth]
      simp
    simp_rw [hcrossRight]
    simp_rw [hopSmul, hdiag]
    simp only [inner_smul_left, inner_smul_right]
    simp only [map_mul, starRingEnd_apply, star_trivial]
    have hfrontPoly :
        p ^ (m - 2) +
            ∑ k ∈ Finset.range (m - 2),
              p ^ (m - 3 - k) * centeredEigenvalue hW i ^ (k + 1) =
          directedKernel p m alpha := by
      rw [← oneSidedGeom_eq_head_add p (centeredEigenvalue hW i) hm2]
      simp [directedKernel, alpha, complementEigenvalue]
    rw [← hfrontPoly]
    rw [real_inner_self_eq_norm_sq, hphiNorm]
    have horth' : inner Real phi gs = 0 := by
      rw [real_inner_comm, horth]
    rw [horth, horth']
    simp only [one_pow, mul_one, mul_zero, add_zero, zero_add]
    ring_nf
    rw [Finset.sum_add_distrib]
    have hfrontSum :
        (∑ x ∈ Finset.range (m - 2),
          p ^ (m - 3 - x) * c ^ 2 * centeredEigenvalue hW i *
            centeredEigenvalue hW i ^ x) =
          c ^ 2 * ∑ x ∈ Finset.range (m - 2),
            p ^ (m - 3 - x) * centeredEigenvalue hW i *
              centeredEigenvalue hW i ^ x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hfrontSum]
    ring
  have hsafe := centeredReturnQuadratic_safe_lower_bound
    hW i hp' hm hm2 horth
  have hsafe' :
      directedKernel p m (frontierSafeRadius hW i) * ‖gs‖ ^ 2 <=
        centeredReturnQuadratic hW p m gs := by
    simpa [real_inner_self_eq_norm_sq] using hsafe
  have hcoeff := oneSidedUCoeff_complementCompressionMoment hW m
  rw [hcoeff, unsignedUCoeff_eq_centeredReturnQuadratic hW hm2]
  rw [hquadDecomp]
  simpa [p, alpha, L, c, gs, g, phi] using
    (add_le_add_left hsafe' (directedKernel p m alpha * c ^ 2))

/-- The full one-sided graphon shift dominates the exact frontier contribution
and the safe-endpoint payment for the orthogonal component. -/
theorem graphonOneSidedShift_frontier_lower_bound
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hp : 1 / 2 < edgeDensity W mu)
    (hm : Odd m) (hm2 : 2 <= m) :
    let p := edgeDensity W mu
    let alpha := complementEigenvalue hW i
    let L := frontierSafeRadius hW i
    let c := inner Real (centeredDegreeL2 hW) (centeredEigenmode hW i)
    let gs := centeredDegreeL2 hW - c • centeredEigenmode hW i
    (m : Real) *
        (directedKernel p m alpha * c ^ 2 +
          directedKernel p m L * ‖gs‖ ^ 2) <=
      graphonOneSidedShift hW m := by
  dsimp only
  have hcoeff := graphon_oneSidedUCoeff_frontier_lower_bound
    hW i (by linarith) hm hm2
  have hweighted := mul_le_mul_of_nonneg_left hcoeff
    (Nat.cast_nonneg m : (0 : Real) <= m)
  exact hweighted.trans
    (graphonOneSidedShift_linear_lower_bound hW hp (by omega))

end OddCycleBound.RegionII
