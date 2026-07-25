import OddCycleBound.Fisher.FiniteGraphon
import Mathlib.Probability.Independence.Integration

/-!
# Deterministic rounding of finite weighted graphons

A finite weighted graphon is converted to a sequence of finite simple graphs.
Each atom is copied `n + 3` times and every copy receives a finite coordinate
label.  Threshold tests on two independent label coordinates realize the
desired edge weight, while three such tests factor correctly around a triangle.
Copy collisions contribute explicit coefficients tending to one.

The final theorem, `roundingGraph_density_tendsto`, proves simultaneous
convergence of edge and triangle densities.  `GraphonSampling` subsequently
turns the nonuniform vertex measure into a uniform finite blow-up.
-/

open MeasureTheory ProbabilityTheory Filter

namespace OddCycleBound

universe u

private def testBit {m : Nat} (t : Nat) (j : Fin m) : Real :=
  if j.val < t then 1 else 0

private noncomputable def labelMeasure (A : Type u) [Fintype A] (n : Nat) :
    Measure (A -> Fin (n + 1)) :=
  Measure.pi (fun _ => finiteUniformMeasure (V := Fin (n + 1)))

private theorem integral_testBit_labelMeasure
    {A : Type u} [Fintype A] [DecidableEq A]
    (n : Nat) (a : A) (t : Nat) (ht : t <= n + 1) :
    (∫ l, testBit t (l a) ∂labelMeasure A n) = (t : Real) / (n + 1) := by
  let beta : A -> Measure (Fin (n + 1)) := fun _ => finiteUniformMeasure
  have hmap :
      (∫ j, testBit t j ∂Measure.map (Function.eval a) (Measure.pi beta)) =
        ∫ l, testBit t (l a) ∂Measure.pi beta :=
    integral_map
      (measurable_pi_apply a).aemeasurable
      (measurable_of_finite (testBit t)).aestronglyMeasurable
  rw [(measurePreserving_eval beta a).map_eq] at hmap
  rw [show labelMeasure A n = Measure.pi beta by rfl, ← hmap]
  rw [finiteUniform_integral]
  simp only [testBit, Finset.sum_boole]
  rw [Fin.card_filter_val_lt]
  simp [min_eq_right ht]

private theorem integral_testBit_mul_labelMeasure
    {A : Type u} [Fintype A] [DecidableEq A]
    (n : Nat) {a b : A} (hab : a ≠ b)
    (s t : Nat) (hs : s <= n + 1) (ht : t <= n + 1) :
    (∫ l, testBit s (l a) * testBit t (l b) ∂labelMeasure A n) =
      (s : Real) / (n + 1) * ((t : Real) / (n + 1)) := by
  let beta : A -> Measure (Fin (n + 1)) := fun _ => finiteUniformMeasure
  have hi : iIndepFun (fun i l => l i) (labelMeasure A n) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hind := hi.indepFun hab
  have hind' : IndepFun (fun l => testBit s (l a))
      (fun l => testBit t (l b)) (labelMeasure A n) := by
    simpa [Function.comp_def] using
      hind.comp (measurable_of_finite _) (measurable_of_finite _)
  have hmul := hind'.integral_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable
    (measurable_of_finite _).aestronglyMeasurable
  simp only [Pi.mul_apply] at hmul
  rw [hmul]
  rw [integral_testBit_labelMeasure n a s hs,
    integral_testBit_labelMeasure n b t ht]

private theorem finiteUniform_integral_prod
    {A B : Type u} [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype B] [Nonempty B] [DecidableEq B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (f : A × B -> Real) :
    (∫ x, f x ∂finiteUniformMeasure (V := A × B)) =
      ∫ a, ∫ b, f (a, b) ∂finiteUniformMeasure (V := B)
        ∂finiteUniformMeasure (V := A) := by
  rw [finiteUniform_integral]
  rw [finiteUniform_integral]
  simp_rw [finiteUniform_integral]
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  field_simp
  simp only [Nat.cast_mul]
  ring

private noncomputable def threshold {Q : Type u} (H : Q -> Q -> Real) (n : Nat) (q r : Q) : Nat :=
  Nat.floor (Real.sqrt (H q r) * (n + 3))

noncomputable def roundingGraph
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    (H : Q -> Q -> Real) (n : Nat) :
    SimpleGraph ((Q × Fin (n + 3)) ×
      ((Q × Fin (n + 3)) -> Fin (n + 3))) :=
  let A := Q × Fin (n + 3)
  SimpleGraph.fromRel fun x y : A × (A -> Fin (n + 3)) =>
    x.1 ≠ y.1 ∧
      (x.2 y.1).val < threshold H n x.1.1 y.1.1 ∧
      (y.2 x.1).val < threshold H n y.1.1 x.1.1

private noncomputable instance roundingGraph.instDecidableRel
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {H : Q -> Q -> Real} {n : Nat} :
    DecidableRel (roundingGraph H n).Adj := Classical.decRel _

private theorem threshold_le
    {Q : Type u} {H : Q -> Q -> Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hH1 : ∀ q r, H q r ≤ 1)
    (n : Nat) (q r : Q) : threshold H n q r ≤ n + 3 := by
  have hfloor :
      (Nat.floor (Real.sqrt (H q r) * (n + 3)) : Real) ≤
        Real.sqrt (H q r) * (n + 3) :=
    Nat.floor_le (by positivity)
  have hs : Real.sqrt (H q r) ≤ 1 := by
    exact (Real.sqrt_le_one).2 (hH1 q r)
  have hmul : Real.sqrt (H q r) * (n + 3) ≤ (n + 3 : Nat) := by
    have h := mul_le_mul_of_nonneg_right hs (by positivity : (0 : Real) ≤ n + 3)
    norm_num only [Nat.cast_add, Nat.cast_ofNat, one_mul] at h ⊢
    exact h
  unfold threshold
  exact_mod_cast hfloor.trans hmul

private theorem roundingGraph_adj
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {H : Q -> Q -> Real} (hHsymm : ∀ q r, H q r = H r q)
    (n : Nat)
    (x y : (Q × Fin (n + 3)) ×
      ((Q × Fin (n + 3)) -> Fin (n + 3))) :
    (roundingGraph H n).Adj x y ↔
      x.1 ≠ y.1 ∧
        (x.2 y.1).val < threshold H n x.1.1 y.1.1 ∧
        (y.2 x.1).val < threshold H n y.1.1 x.1.1 := by
  simp only [roundingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rcases h with ⟨hyx, hy, hx⟩
      refine ⟨hyx.symm, ?_, ?_⟩
      · simpa [threshold, hHsymm] using hx
      · simpa [threshold, hHsymm] using hy
  · intro h
    exact ⟨fun hxy => h.1 (congrArg Prod.fst hxy), Or.inl h⟩

private theorem roundingGraph_kernel_of_ne
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {H : Q -> Q -> Real} (hHsymm : ∀ q r, H q r = H r q)
    (n : Nat) {a b : Q × Fin (n + 3)} (hab : a ≠ b)
    (l k : (Q × Fin (n + 3)) -> Fin (n + 3)) :
    finiteGraphKernel (roundingGraph H n) (a, l) (b, k) =
      testBit (threshold H n a.1 b.1) (l b) *
      testBit (threshold H n b.1 a.1) (k a) := by
  have hadj :
      (roundingGraph H n).Adj (a, l) (b, k) ↔
        (l b).val < threshold H n a.1 b.1 ∧
        (k a).val < threshold H n b.1 a.1 := by
    simpa [hab] using roundingGraph_adj hHsymm n (a, l) (b, k)
  rw [finiteGraphKernel]
  by_cases hleft : (l b).val < threshold H n a.1 b.1 <;>
    by_cases hright : (k a).val < threshold H n b.1 a.1 <;>
    simp [hadj, hleft, hright, testBit]

private noncomputable def roundedEdge
    {Q : Type u} (H : Q -> Q -> Real) (n : Nat) (q r : Q) : Real :=
  (threshold H n q r : Real) / (n + 3) *
    ((threshold H n r q : Real) / (n + 3))

private theorem roundingGraph_edge_label_integral
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {H : Q -> Q -> Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hH1 : ∀ q r, H q r ≤ 1)
    (hHsymm : ∀ q r, H q r = H r q)
    (n : Nat) (a b : Q × Fin (n + 3)) :
    let lambda : Measure ((Q × Fin (n + 3)) -> Fin (n + 3)) :=
      labelMeasure (Q × Fin (n + 3)) (n + 2)
    (∫ l, ∫ k,
      finiteGraphKernel (roundingGraph H n) (a, l) (b, k) ∂lambda ∂lambda) =
      if a ≠ b then roundedEdge H n a.1 b.1 else 0 := by
  classical
  let lambda : Measure ((Q × Fin (n + 3)) -> Fin (n + 3)) :=
    labelMeasure (Q × Fin (n + 3)) (n + 2)
  letI : IsProbabilityMeasure lambda := by
    dsimp [lambda, labelMeasure]
    infer_instance
  change (∫ l, ∫ k,
      finiteGraphKernel (roundingGraph H n) (a, l) (b, k) ∂lambda ∂lambda) =
    if a ≠ b then
      (threshold H n a.1 b.1 : Real) / (n + 3) *
      ((threshold H n b.1 a.1 : Real) / (n + 3))
    else 0
  by_cases hab : a ≠ b
  · rw [if_pos hab]
    have hadj (l k) :
        (roundingGraph H n).Adj (a, l) (b, k) ↔
          (l b).val < threshold H n a.1 b.1 ∧
          (k a).val < threshold H n b.1 a.1 := by
      simpa [hab] using roundingGraph_adj hHsymm n (a, l) (b, k)
    have hkern (l k) := roundingGraph_kernel_of_ne hHsymm n hab l k
    simp_rw [hkern]
    have htAB := threshold_le hH0 hH1 n a.1 b.1
    have htBA := threshold_le hH0 hH1 n b.1 a.1
    have hinner (l : (Q × Fin (n + 3)) -> Fin (n + 3)) :
        (∫ k, testBit (threshold H n a.1 b.1) (l b) *
          testBit (threshold H n b.1 a.1) (k a) ∂lambda) =
        testBit (threshold H n a.1 b.1) (l b) *
          ((threshold H n b.1 a.1 : Real) / (n + 3)) := by
      rw [integral_const_mul]
      rw [integral_testBit_labelMeasure (n + 2) a _ htBA]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      congr 1 <;> ring
    simp_rw [hinner]
    rw [integral_mul_const]
    rw [integral_testBit_labelMeasure (n + 2) b _ htAB]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    congr 1 <;> ring
  · rw [if_neg hab]
    have hab' : a = b := not_ne_iff.mp hab
    subst b
    have hkern (l k) :
        finiteGraphKernel (roundingGraph H n) (a, l) (a, k) = 0 := by
      simp [finiteGraphKernel, roundingGraph]
    have hinnerZero (l) :
        (∫ k, finiteGraphKernel (roundingGraph H n) (a, l) (a, k) ∂lambda) = 0 := by
      calc
        _ = ∫ _k, (0 : Real) ∂lambda := by
          apply integral_congr_ae
          exact ae_of_all _ fun k => hkern l k
        _ = 0 := integral_zero _ _
    rw [show (fun l =>
        ∫ k, finiteGraphKernel (roundingGraph H n) (a, l) (a, k) ∂lambda) =
        fun _ => 0 by
      funext l
      exact hinnerZero l]
    exact integral_zero _ _

private theorem roundingGraph_triangle_label_integral
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    {H : Q -> Q -> Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hH1 : ∀ q r, H q r ≤ 1)
    (hHsymm : ∀ q r, H q r = H r q)
    (n : Nat) (a b c : Q × Fin (n + 3)) :
    let lambda : Measure ((Q × Fin (n + 3)) -> Fin (n + 3)) :=
      labelMeasure (Q × Fin (n + 3)) (n + 2)
    (∫ l, ∫ k, ∫ h,
      finiteGraphKernel (roundingGraph H n) (a, l) (b, k) *
      finiteGraphKernel (roundingGraph H n) (b, k) (c, h) *
      finiteGraphKernel (roundingGraph H n) (c, h) (a, l)
      ∂lambda ∂lambda ∂lambda) =
      if a ≠ b ∧ b ≠ c ∧ c ≠ a then
        roundedEdge H n a.1 b.1 * roundedEdge H n b.1 c.1 *
          roundedEdge H n c.1 a.1
      else 0 := by
  classical
  let lambda : Measure ((Q × Fin (n + 3)) -> Fin (n + 3)) :=
    labelMeasure (Q × Fin (n + 3)) (n + 2)
  letI : IsProbabilityMeasure lambda := by
    dsimp [lambda, labelMeasure]
    infer_instance
  change (∫ l, ∫ k, ∫ h,
      finiteGraphKernel (roundingGraph H n) (a, l) (b, k) *
      finiteGraphKernel (roundingGraph H n) (b, k) (c, h) *
      finiteGraphKernel (roundingGraph H n) (c, h) (a, l)
      ∂lambda ∂lambda ∂lambda) = _
  by_cases hdistinct : a ≠ b ∧ b ≠ c ∧ c ≠ a
  · rw [if_pos hdistinct]
    rcases hdistinct with ⟨hab, hbc, hca⟩
    have hAB (l k) := roundingGraph_kernel_of_ne hHsymm n hab l k
    have hBC (k h) := roundingGraph_kernel_of_ne hHsymm n hbc k h
    have hCA (h l) := roundingGraph_kernel_of_ne hHsymm n hca l h
    simp_rw [hAB, hBC, hCA]
    have htAB := threshold_le hH0 hH1 n a.1 b.1
    have htBA := threshold_le hH0 hH1 n b.1 a.1
    have htBC := threshold_le hH0 hH1 n b.1 c.1
    have htCB := threshold_le hH0 hH1 n c.1 b.1
    have htCA := threshold_le hH0 hH1 n c.1 a.1
    have htAC := threshold_le hH0 hH1 n a.1 c.1
    have hden : ((n + 2 : Nat) : Real) + 1 = ((n + 3 : Nat) : Real) := by
      push_cast
      ring
    have hinner
        (l k : (Q × Fin (n + 3)) -> Fin (n + 3)) :
        (∫ h,
          (testBit (threshold H n a.1 b.1) (l b) *
              testBit (threshold H n b.1 a.1) (k a)) *
            (testBit (threshold H n b.1 c.1) (k c) *
              testBit (threshold H n c.1 b.1) (h b)) *
            (testBit (threshold H n c.1 a.1) (h a) *
              testBit (threshold H n a.1 c.1) (l c)) ∂lambda) =
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (testBit (threshold H n b.1 a.1) (k a) *
            testBit (threshold H n b.1 c.1) (k c)) *
          (((threshold H n c.1 b.1 : Real) / (n + 3)) *
            ((threshold H n c.1 a.1 : Real) / (n + 3))) := by
      rw [show (∫ h,
          (testBit (threshold H n a.1 b.1) (l b) *
              testBit (threshold H n b.1 a.1) (k a)) *
            (testBit (threshold H n b.1 c.1) (k c) *
              testBit (threshold H n c.1 b.1) (h b)) *
            (testBit (threshold H n c.1 a.1) (h a) *
              testBit (threshold H n a.1 c.1) (l c)) ∂lambda) =
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (testBit (threshold H n b.1 a.1) (k a) *
            testBit (threshold H n b.1 c.1) (k c)) *
          (∫ h, testBit (threshold H n c.1 b.1) (h b) *
            testBit (threshold H n c.1 a.1) (h a) ∂lambda) by
        calc
          _ = ∫ h,
              ((testBit (threshold H n a.1 b.1) (l b) *
                testBit (threshold H n a.1 c.1) (l c)) *
              (testBit (threshold H n b.1 a.1) (k a) *
                testBit (threshold H n b.1 c.1) (k c))) *
              (testBit (threshold H n c.1 b.1) (h b) *
                testBit (threshold H n c.1 a.1) (h a)) ∂lambda := by
                apply integral_congr_ae
                exact ae_of_all _ fun h => by ring
          _ = _ := by rw [integral_const_mul]]
      rw [integral_testBit_mul_labelMeasure (n + 2) hab.symm _ _ htCB htCA]
      rw [hden]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
    simp_rw [hinner]
    have hmiddle
        (l : (Q × Fin (n + 3)) -> Fin (n + 3)) :
        (∫ k,
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (testBit (threshold H n b.1 a.1) (k a) *
            testBit (threshold H n b.1 c.1) (k c)) *
          (((threshold H n c.1 b.1 : Real) / (n + 3)) *
            ((threshold H n c.1 a.1 : Real) / (n + 3))) ∂lambda) =
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (((threshold H n b.1 a.1 : Real) / (n + 3)) *
            ((threshold H n b.1 c.1 : Real) / (n + 3))) *
          (((threshold H n c.1 b.1 : Real) / (n + 3)) *
            ((threshold H n c.1 a.1 : Real) / (n + 3))) := by
      rw [show (∫ k,
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (testBit (threshold H n b.1 a.1) (k a) *
            testBit (threshold H n b.1 c.1) (k c)) *
          (((threshold H n c.1 b.1 : Real) / (n + 3)) *
            ((threshold H n c.1 a.1 : Real) / (n + 3))) ∂lambda) =
          (testBit (threshold H n a.1 b.1) (l b) *
            testBit (threshold H n a.1 c.1) (l c)) *
          (∫ k, testBit (threshold H n b.1 a.1) (k a) *
            testBit (threshold H n b.1 c.1) (k c) ∂lambda) *
          (((threshold H n c.1 b.1 : Real) / (n + 3)) *
            ((threshold H n c.1 a.1 : Real) / (n + 3))) by
        simp only [integral_mul_const, integral_const_mul]]
      rw [integral_testBit_mul_labelMeasure (n + 2) hca.symm _ _ htBA htBC]
      rw [hden]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
    simp_rw [hmiddle]
    rw [show (∫ l,
        (testBit (threshold H n a.1 b.1) (l b) *
          testBit (threshold H n a.1 c.1) (l c)) *
        (((threshold H n b.1 a.1 : Real) / (n + 3)) *
          ((threshold H n b.1 c.1 : Real) / (n + 3))) *
        (((threshold H n c.1 b.1 : Real) / (n + 3)) *
          ((threshold H n c.1 a.1 : Real) / (n + 3))) ∂lambda) =
        (∫ l, testBit (threshold H n a.1 b.1) (l b) *
          testBit (threshold H n a.1 c.1) (l c) ∂lambda) *
        (((threshold H n b.1 a.1 : Real) / (n + 3)) *
          ((threshold H n b.1 c.1 : Real) / (n + 3))) *
        (((threshold H n c.1 b.1 : Real) / (n + 3)) *
          ((threshold H n c.1 a.1 : Real) / (n + 3))) by
      simp only [integral_mul_const]]
    rw [integral_testBit_mul_labelMeasure (n + 2) hbc _ _ htAB htAC]
    rw [hden]
    simp only [roundedEdge]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    ring_nf
  · rw [if_neg hdistinct]
    rcases not_and_or.mp hdistinct with hab | hrest
    · have hab' : a = b := not_ne_iff.mp hab
      subst b
      have hz (l k) : finiteGraphKernel (roundingGraph H n) (a, l) (a, k) = 0 := by
        simp [finiteGraphKernel, roundingGraph]
      simp_rw [hz]
      simp only [zero_mul, integral_zero]
    · rcases not_and_or.mp hrest with hbc | hca
      · have hbc' : b = c := not_ne_iff.mp hbc
        subst c
        have hz (k h) : finiteGraphKernel (roundingGraph H n) (b, k) (b, h) = 0 := by
          simp [finiteGraphKernel, roundingGraph]
        simp_rw [hz]
        simp only [mul_zero, zero_mul, integral_zero]
      · have hca' : c = a := not_ne_iff.mp hca
        subst a
        have hz (h l) : finiteGraphKernel (roundingGraph H n) (c, h) (c, l) = 0 := by
          simp [finiteGraphKernel, roundingGraph]
        simp_rw [hz]
        simp only [mul_zero, integral_zero]

end OddCycleBound

namespace OddCycleBound

private theorem sum_fin_ne (m : Nat) :
    (∑ i : Fin m, ∑ j : Fin m, if i ≠ j then (1 : Real) else 0) =
      (m : Real) * (m - 1) := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    simp [Finset.filter_ne, Nat.cast_sub hm1]
    ring

private theorem sum_fin_pairwise_ne (m : Nat) (hm : 2 ≤ m) :
    (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
      if i ≠ j ∧ j ≠ k ∧ k ≠ i then (1 : Real) else 0) =
      (m : Real) * (m - 1) * (m - 2) := by
  classical
  have hinner (i j : Fin m) (hij : i ≠ j) :
      (∑ k : Fin m,
        if i ≠ j ∧ j ≠ k ∧ k ≠ i then (1 : Real) else 0) =
        (m - 2 : Nat) := by
    have hcond (k : Fin m) :
        (i ≠ j ∧ j ≠ k ∧ k ≠ i) ↔ (j ≠ k ∧ k ≠ i) := by
      simp [hij]
    simp_rw [hcond]
    rw [Finset.sum_boole]
    have hset : (Finset.univ.filter fun k : Fin m => j ≠ k ∧ k ≠ i) =
        (Finset.univ.erase j).erase i := by
      ext k
      simp [ne_comm, and_comm]
    rw [hset]
    have hi : i ∈ (Finset.univ.erase j : Finset (Fin m)) := by simp [hij]
    rw [Finset.card_erase_of_mem hi]
    rw [Finset.card_erase_of_mem (Finset.mem_univ j)]
    rw [Finset.card_fin]
    congr 1
  have hmiddle (i : Fin m) :
      (∑ j : Fin m, ∑ k : Fin m,
        if i ≠ j ∧ j ≠ k ∧ k ≠ i then (1 : Real) else 0) =
        (m - 1 : Nat) * (m - 2 : Nat) := by
    classical
    simp_rw [show ∀ j : Fin m,
      (∑ k : Fin m,
        if i ≠ j ∧ j ≠ k ∧ k ≠ i then (1 : Real) else 0) =
        if i ≠ j then (m - 2 : Nat) else 0 by
          intro j
          by_cases hij : i ≠ j
          · rw [if_pos hij, hinner i j hij]
          · simp [not_ne_iff.mp hij]]
    push_cast
    simp [Finset.sum_ite, Finset.filter_ne,
      Nat.cast_sub (show 1 ≤ m by omega)]
  simp_rw [hmiddle]
  simp [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub hm]
  ring

private noncomputable def copyEdgeCoeff
    {Q : Type u} [DecidableEq Q] (n : Nat) (q r : Q) : Real :=
  let m := n + 3
  (∑ i : Fin m, ∑ j : Fin m,
    if (q, i) ≠ (r, j) then (1 : Real) else 0) / (m : Real) ^ 2

private noncomputable def copyTriangleCoeff
    {Q : Type u} [DecidableEq Q] (n : Nat) (q r s : Q) : Real :=
  let m := n + 3
  (∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin m,
    if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i)
    then (1 : Real) else 0) / (m : Real) ^ 3

private theorem tendsto_inv_n_add_three :
    Tendsto (fun n : Nat => (1 : Real) / (n + 3)) atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).comp
    (tendsto_add_atTop_nat 2)
  convert h using 1
  funext n
  dsimp [Function.comp_def]
  norm_num
  ring

private theorem tendsto_copyEdgeCoeff_one
    {Q : Type u} [DecidableEq Q] (q r : Q) :
    Tendsto (fun n => copyEdgeCoeff n q r) atTop (nhds 1) := by
  by_cases hqr : q = r
  · subst r
    have hform (n : Nat) : copyEdgeCoeff n q q =
        1 - (1 : Real) / (n + 3) := by
      rw [copyEdgeCoeff]
      have hpair (i j : Fin (n + 3)) : ((q, i) ≠ (q, j)) ↔ i ≠ j := by
        simp
      simp_rw [hpair]
      rw [sum_fin_ne]
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      have hm : (n : Real) + 3 ≠ 0 := by positivity
      field_simp [hm] <;> ring
    have ht := (tendsto_const_nhds.sub tendsto_inv_n_add_three :
      Tendsto (fun n : Nat => (1 : Real) - 1 / (n + 3)) atTop (nhds (1 - 0)))
    norm_num at ht
    have ht' : Tendsto (fun n : Nat => (1 : Real) - 1 / (n + 3)) atTop (nhds 1) := by
      simpa [div_eq_mul_inv] using ht
    exact ht'.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)
  · have hform (n : Nat) : copyEdgeCoeff n q r = 1 := by
      rw [copyEdgeCoeff]
      have hneq (i j : Fin (n + 3)) : (q, i) ≠ (r, j) := by
        intro h
        exact hqr (congrArg Prod.fst h)
      have hsum :
          (∑ i : Fin (n + 3), ∑ j : Fin (n + 3),
            if (q, i) ≠ (r, j) then (1 : Real) else 0) =
          ∑ i : Fin (n + 3), ∑ _j : Fin (n + 3), (1 : Real) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact if_pos (hneq i j)
      rw [hsum]
      have hcount :
          (∑ _i : Fin (n + 3), ∑ _j : Fin (n + 3), (1 : Real)) =
            ((n + 3 : Nat) : Real) ^ 2 := by
        simp <;> ring
      rw [hcount]
      exact div_self (by positivity)
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)

private theorem tendsto_copyTriangleCoeff_one
    {Q : Type u} [DecidableEq Q] (q r s : Q) :
    Tendsto (fun n => copyTriangleCoeff n q r s) atTop (nhds 1) := by
  have htwo : Tendsto (fun n : Nat => (2 : Real) * (1 / (n + 3))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_n_add_three)
  have htAll : Tendsto (fun n : Nat =>
      (1 - (1 : Real) / (n + 3)) * (1 - 2 * ((1 : Real) / (n + 3))))
      atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub tendsto_inv_n_add_three).mul
      (tendsto_const_nhds.sub htwo) using 1 <;> norm_num
  have htTwo : Tendsto (fun n : Nat => 1 - (1 : Real) / (n + 3))
      atTop (nhds 1) := by
    have ht := (tendsto_const_nhds.sub tendsto_inv_n_add_three :
      Tendsto (fun n : Nat => (1 : Real) - 1 / (n + 3)) atTop (nhds (1 - 0)))
    norm_num at ht
    simpa [div_eq_mul_inv] using ht
  by_cases hqr : q = r
  · subst r
    by_cases hqs : q = s
    · subst s
      have hform (n : Nat) : copyTriangleCoeff n q q q =
          (1 - (1 : Real) / (n + 3)) *
            (1 - 2 * ((1 : Real) / (n + 3))) := by
        rw [copyTriangleCoeff]
        have hpair (i j : Fin (n + 3)) : ((q, i) ≠ (q, j)) ↔ i ≠ j := by simp
        simp_rw [hpair]
        rw [sum_fin_pairwise_ne (n + 3) (by omega)]
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        have hm : (n : Real) + 3 ≠ 0 := by positivity
        field_simp [hm] <;> ring
      exact htAll.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)
    · have hform (n : Nat) : copyTriangleCoeff n q q s =
          1 - (1 : Real) / (n + 3) := by
        rw [copyTriangleCoeff]
        have hcond (i j k : Fin (n + 3)) :
            ((q, i) ≠ (q, j) ∧ (q, j) ≠ (s, k) ∧ (s, k) ≠ (q, i)) ↔
              i ≠ j := by
          constructor
          · intro h
            exact fun hij => h.1 (by simp [hij])
          · intro hij
            refine ⟨?_, ?_, ?_⟩
            · simpa using hij
            · intro h
              exact hqs (congrArg Prod.fst h)
            · intro h
              exact hqs (congrArg Prod.fst h).symm
        simp_rw [hcond]
        have hinner (i j : Fin (n + 3)) :
            (∑ _k : Fin (n + 3), if i ≠ j then (1 : Real) else 0) =
              (if i ≠ j then (1 : Real) else 0) * (n + 3) := by
          by_cases hij : i ≠ j <;> simp [hij]
        simp_rw [hinner]
        have hfactor (i : Fin (n + 3)) :
            (∑ j : Fin (n + 3),
              (if i ≠ j then (1 : Real) else 0) * (n + 3)) =
            (∑ j : Fin (n + 3), if i ≠ j then (1 : Real) else 0) *
              (n + 3) := by
          rw [Finset.sum_mul]
        simp_rw [hfactor]
        rw [← Finset.sum_mul, sum_fin_ne]
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        have hm : (n : Real) + 3 ≠ 0 := by positivity
        field_simp [hm] <;> ring
      exact htTwo.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)
  · by_cases hrs : r = s
    · subst s
      have hform (n : Nat) : copyTriangleCoeff n q r r =
          1 - (1 : Real) / (n + 3) := by
        rw [copyTriangleCoeff]
        have hcond (i j k : Fin (n + 3)) :
            ((q, i) ≠ (r, j) ∧ (r, j) ≠ (r, k) ∧ (r, k) ≠ (q, i)) ↔
              j ≠ k := by
          constructor
          · intro h
            exact fun hjk => h.2.1 (by simp [hjk])
          · intro hjk
            refine ⟨?_, ?_, ?_⟩
            · intro h
              exact hqr (congrArg Prod.fst h)
            · simpa using hjk
            · intro h
              exact hqr (congrArg Prod.fst h).symm
        simp_rw [hcond]
        have hinner :
            (∑ j : Fin (n + 3), ∑ k : Fin (n + 3),
              if j ≠ k then (1 : Real) else 0) =
              (n + 3 : Real) * (n + 3 - 1) := by
          simpa [Nat.cast_add] using sum_fin_ne (n + 3)
        simp_rw [hinner]
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        have hm : (n : Real) + 3 ≠ 0 := by positivity
        field_simp [hm] <;> ring
      exact htTwo.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)
    · by_cases hsq : s = q
      · subst s
        have hform (n : Nat) : copyTriangleCoeff n q r q =
            1 - (1 : Real) / (n + 3) := by
          rw [copyTriangleCoeff]
          have hcond (i j k : Fin (n + 3)) :
              ((q, i) ≠ (r, j) ∧ (r, j) ≠ (q, k) ∧ (q, k) ≠ (q, i)) ↔
                k ≠ i := by
            constructor
            · intro h
              intro hki
              apply h.2.2
              cases hki
              rfl
            · intro hki
              refine ⟨?_, ?_, ?_⟩
              · intro h
                exact hqr (congrArg Prod.fst h)
              · intro h
                exact hqr (congrArg Prod.fst h).symm
              · intro h
                exact hki (congrArg Prod.snd h)
          simp_rw [hcond]
          have hpair :
              (∑ i : Fin (n + 3), ∑ k : Fin (n + 3),
                if k ≠ i then (1 : Real) else 0) =
                (n + 3 : Real) * (n + 3 - 1) := by
            calc
              _ = ∑ i : Fin (n + 3), ∑ k : Fin (n + 3),
                  if i ≠ k then (1 : Real) else 0 := by
                    apply Finset.sum_congr rfl
                    intro i _
                    apply Finset.sum_congr rfl
                    intro k _
                    exact if_congr (ne_comm) rfl rfl
              _ = _ := by
                have hp := sum_fin_ne (n + 3)
                norm_num only [Nat.cast_add, Nat.cast_ofNat] at hp ⊢
                exact hp
          rw [show (∑ i : Fin (n + 3), ∑ _j : Fin (n + 3),
              ∑ k : Fin (n + 3), if k ≠ i then (1 : Real) else 0) =
              (∑ i : Fin (n + 3), ∑ k : Fin (n + 3),
                if k ≠ i then (1 : Real) else 0) * (n + 3 : Real) by
            simp_rw [show ∀ i : Fin (n + 3),
                (∑ _j : Fin (n + 3), ∑ k : Fin (n + 3),
                  if k ≠ i then (1 : Real) else 0) =
                (∑ k : Fin (n + 3), if k ≠ i then (1 : Real) else 0) *
                  (n + 3 : Real) by
                    intro i
                    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
                    norm_num only [Nat.cast_add, Nat.cast_ofNat]
                    ring]
            rw [← Finset.sum_mul]]
          rw [hpair]
          norm_num only [Nat.cast_add, Nat.cast_ofNat]
          have hm : (n : Real) + 3 ≠ 0 := by positivity
          field_simp [hm] <;> ring
        exact htTwo.congr' (Filter.Eventually.of_forall fun n => (hform n).symm)
      · have hform (n : Nat) : copyTriangleCoeff n q r s = 1 := by
          rw [copyTriangleCoeff]
          have hcond (i j k : Fin (n + 3)) :
              (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) := by
            refine ⟨?_, ?_, ?_⟩
            · intro h
              exact hqr (congrArg Prod.fst h)
            · intro h
              exact hrs (congrArg Prod.fst h)
            · intro h
              exact hsq (congrArg Prod.fst h)
          have hsum :
              (∑ i : Fin (n + 3), ∑ j : Fin (n + 3), ∑ k : Fin (n + 3),
                if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i)
                then (1 : Real) else 0) =
              ∑ _i : Fin (n + 3), ∑ _j : Fin (n + 3),
                ∑ _k : Fin (n + 3), (1 : Real) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact if_pos (hcond i j k)
          rw [hsum]
          have hcount :
              (∑ _i : Fin (n + 3), ∑ _j : Fin (n + 3),
                ∑ _k : Fin (n + 3), (1 : Real)) =
                ((n + 3 : Nat) : Real) ^ 3 := by
            simp <;> ring
          rw [hcount]
          exact div_self (by positivity)
        exact tendsto_const_nhds.congr'
          (Filter.Eventually.of_forall fun n => (hform n).symm)

private theorem tendsto_threshold_div
    {Q : Type u} {H : Q → Q → Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (q r : Q) :
    Tendsto (fun n : Nat => (threshold H n q r : Real) / (n + 3))
      atTop (nhds (Real.sqrt (H q r))) := by
  have hshift : Tendsto (fun n : Nat => ((n + 3 : Nat) : Real)) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop (R := Real)).comp
      (tendsto_add_atTop_nat 3)
  have h := (tendsto_nat_floor_mul_div_atTop
    (Real.sqrt_nonneg (H q r))).comp hshift
  convert h using 1
  funext n
  simp only [Function.comp_apply, threshold]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]

private theorem tendsto_roundedEdge
    {Q : Type u} {H : Q → Q → Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hHsymm : ∀ q r, H q r = H r q)
    (q r : Q) :
    Tendsto (fun n : Nat => roundedEdge H n q r) atTop (nhds (H q r)) := by
  have hq := tendsto_threshold_div hH0 q r
  have hr := tendsto_threshold_div hH0 r q
  have hmul := hq.mul hr
  convert hmul using 1
  · funext n
    rfl
  · congr 1
    rw [hHsymm r q]
    simpa [pow_two] using (Real.sq_sqrt (hH0 q r)).symm

private noncomputable def baseMeasure
    {Q : Type u} [MeasurableSpace Q] (ν : Measure Q) (n : Nat) :
    Measure (Q × Fin (n + 3)) :=
  ν.prod (finiteUniformMeasure (V := Fin (n + 3)))

noncomputable def roundingMeasure
    {Q : Type u} [Fintype Q] [MeasurableSpace Q]
    (ν : Measure Q) (n : Nat) :
    Measure ((Q × Fin (n + 3)) ×
      ((Q × Fin (n + 3)) → Fin (n + 3))) :=
  (baseMeasure ν n).prod (labelMeasure (Q × Fin (n + 3)) (n + 2))

theorem roundingMeasure_isProbability
    {Q : Type u} [Fintype Q] [MeasurableSpace Q]
    (ν : Measure Q) [IsProbabilityMeasure ν] (n : Nat) :
    IsProbabilityMeasure (roundingMeasure ν n) := by
  unfold roundingMeasure baseMeasure labelMeasure
  infer_instance

private theorem copyEdge_average
    {Q : Type u} [DecidableEq Q] (H : Q → Q → Real)
    (n : Nat) (q r : Q) :
    (∫ i : Fin (n + 3), ∫ j : Fin (n + 3),
      if (q, i) ≠ (r, j) then roundedEdge H n q r else 0
        ∂finiteUniformMeasure ∂finiteUniformMeasure) =
      copyEdgeCoeff n q r * roundedEdge H n q r := by
  simp_rw [finiteUniform_integral]
  rw [copyEdgeCoeff]
  simp only [Finset.sum_div]
  have hm : (Fintype.card (Fin (n + 3)) : Real) ≠ 0 := by positivity
  field_simp [hm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all [div_eq_mul_inv, mul_comm]

private theorem copyTriangle_average
    {Q : Type u} [DecidableEq Q] (H : Q → Q → Real)
    (n : Nat) (q r s : Q) :
    (∫ i : Fin (n + 3), ∫ j : Fin (n + 3), ∫ k : Fin (n + 3),
      if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
        roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
      else 0 ∂finiteUniformMeasure ∂finiteUniformMeasure
        ∂finiteUniformMeasure) =
      copyTriangleCoeff n q r s *
        (roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q) := by
  simp_rw [finiteUniform_integral]
  rw [copyTriangleCoeff]
  simp only [Finset.sum_div]
  have hm : (Fintype.card (Fin (n + 3)) : Real) ≠ 0 := by positivity
  field_simp [hm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp_all [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private theorem roundingGraphKernel_isGraphon
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {H : Q → Q → Real} (n : Nat) (ν : Measure Q) :
    IsGraphon (finiteGraphKernel (roundingGraph H n))
      (roundingMeasure ν n) := by
  refine ⟨measurable_of_finite _, ?_, ?_, ?_⟩
  · intro x y
    by_cases h : (roundingGraph H n).Adj x y <;>
      simp [finiteGraphKernel, h]
  · intro x y
    by_cases h : (roundingGraph H n).Adj x y <;>
      simp [finiteGraphKernel, h]
  · intro x y
    simp only [finiteGraphKernel]
    by_cases h : (roundingGraph H n).Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hyx => h hyx.symm)]

private theorem roundingGraph_edge_density_formula
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {ν : Measure Q} [IsProbabilityMeasure ν]
    {H : Q → Q → Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hH1 : ∀ q r, H q r ≤ 1)
    (hHsymm : ∀ q r, H q r = H r q) (n : Nat) :
    edgeDensity (finiteGraphKernel (roundingGraph H n))
        (roundingMeasure ν n) =
      ∫ q, ∫ r, copyEdgeCoeff n q r * roundedEdge H n q r ∂ν ∂ν := by
  let A := Q × Fin (n + 3)
  let lambda : Measure (A → Fin (n + 3)) := labelMeasure A (n + 2)
  let beta : Measure A := baseMeasure ν n
  let K := finiteGraphKernel (roundingGraph H n)
  letI : IsProbabilityMeasure lambda := by
    dsimp [lambda, labelMeasure]
    infer_instance
  letI : IsProbabilityMeasure beta := by
    dsimp [beta, baseMeasure]
    infer_instance
  have hρ : roundingMeasure ν n = beta.prod lambda := by rfl
  change (∫ x, ∫ y, K x y ∂beta.prod lambda ∂beta.prod lambda) = _
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [integral_prod _ Integrable.of_finite]
  have hswap (a : A) :
      (∫ l, ∫ b, ∫ k, K (a, l) (b, k) ∂lambda ∂beta ∂lambda) =
        ∫ b, ∫ l, ∫ k, K (a, l) (b, k) ∂lambda ∂lambda ∂beta := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswap]
  simp_rw [show K = finiteGraphKernel (roundingGraph H n) by rfl]
  simp only [lambda, A]
  simp_rw [roundingGraph_edge_label_integral hH0 hH1 hHsymm n]
  simp only [beta, baseMeasure]
  simp_rw [integral_prod _ Integrable.of_finite]
  have hswapCopy (q : Q) :
      (∫ i : Fin (n + 3), ∫ r : Q, ∫ j : Fin (n + 3),
        (if (q, i) ≠ (r, j) then roundedEdge H n q r else 0)
          ∂finiteUniformMeasure ∂ν ∂finiteUniformMeasure) =
      ∫ r : Q, ∫ i : Fin (n + 3), ∫ j : Fin (n + 3),
        (if (q, i) ≠ (r, j) then roundedEdge H n q r else 0)
          ∂finiteUniformMeasure ∂finiteUniformMeasure ∂ν := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapCopy, copyEdge_average]

private theorem roundingGraph_triangle_density_formula
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {ν : Measure Q} [IsProbabilityMeasure ν]
    {H : Q → Q → Real}
    (hH0 : ∀ q r, 0 ≤ H q r) (hH1 : ∀ q r, H q r ≤ 1)
    (hHsymm : ∀ q r, H q r = H r q) (n : Nat) :
    trace (roundingMeasure ν n)
        (compPow (roundingMeasure ν n)
          (finiteGraphKernel (roundingGraph H n)) 2) =
      ∫ q, ∫ r, ∫ s,
        copyTriangleCoeff n q r s *
          (roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q)
        ∂ν ∂ν ∂ν := by
  let A := Q × Fin (n + 3)
  let lambda : Measure (A → Fin (n + 3)) := labelMeasure A (n + 2)
  let beta : Measure A := baseMeasure ν n
  let K := finiteGraphKernel (roundingGraph H n)
  letI : IsProbabilityMeasure lambda := by
    dsimp [lambda, labelMeasure]
    infer_instance
  letI : IsProbabilityMeasure beta := by
    dsimp [beta, baseMeasure]
    infer_instance
  have hgraphon : IsGraphon K (beta.prod lambda) := by
    exact roundingGraphKernel_isGraphon n ν
  change trace (beta.prod lambda) (compPow (beta.prod lambda) K 2) = _
  rw [trace_compPow_two_eq_triangleIntegral hgraphon]
  rw [integral_prod _ Integrable.of_finite]
  have hexpand (a : A) (l : A → Fin (n + 3)) :
      (∫ y, ∫ z, K (a, l) y * K y z * K z (a, l)
        ∂beta.prod lambda ∂beta.prod lambda) =
      ∫ b, ∫ k, ∫ c, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂beta ∂lambda ∂beta := by
    rw [integral_prod _ Integrable.of_finite]
    simp_rw [integral_prod _ Integrable.of_finite]
  have hexpandAll :
      (∫ a, ∫ l, ∫ y, ∫ z, K (a, l) y * K y z * K z (a, l)
        ∂beta.prod lambda ∂beta.prod lambda ∂lambda ∂beta) =
      ∫ a, ∫ l, ∫ b, ∫ k, ∫ c, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂beta ∂lambda ∂beta ∂lambda ∂beta := by
    apply integral_congr_ae
    filter_upwards with a
    apply integral_congr_ae
    filter_upwards with l
    exact hexpand a l
  rw [hexpandAll]
  have hswapL (a : A) :
      (∫ l, ∫ b, ∫ k, ∫ c, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂beta ∂lambda ∂beta ∂lambda) =
      ∫ b, ∫ l, ∫ k, ∫ c, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂beta ∂lambda ∂lambda ∂beta := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapL]
  have hswapK (a b : A) (l : A → Fin (n + 3)) :
      (∫ k, ∫ c, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂beta ∂lambda) =
      ∫ c, ∫ k, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂lambda ∂beta := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapK]
  have hswapL2 (a b : A) :
      (∫ l, ∫ c, ∫ k, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂lambda ∂beta ∂lambda) =
      ∫ c, ∫ l, ∫ k, ∫ h,
        K (a, l) (b, k) * K (b, k) (c, h) * K (c, h) (a, l)
          ∂lambda ∂lambda ∂lambda ∂beta := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapL2]
  simp_rw [show K = finiteGraphKernel (roundingGraph H n) by rfl]
  simp only [lambda, A]
  simp_rw [roundingGraph_triangle_label_integral hH0 hH1 hHsymm n]
  simp only [beta, baseMeasure]
  simp_rw [integral_prod _ Integrable.of_finite]
  have hswapI (q : Q) :
      (∫ i : Fin (n + 3), ∫ r : Q, ∫ j : Fin (n + 3),
        ∫ s : Q, ∫ k : Fin (n + 3),
          (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
            roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
          else 0) ∂finiteUniformMeasure ∂ν ∂finiteUniformMeasure ∂ν
            ∂finiteUniformMeasure) =
      ∫ r : Q, ∫ i : Fin (n + 3), ∫ j : Fin (n + 3),
        ∫ s : Q, ∫ k : Fin (n + 3),
          (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
            roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
          else 0) ∂finiteUniformMeasure ∂ν ∂finiteUniformMeasure
            ∂finiteUniformMeasure ∂ν := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapI]
  have hswapJ (q r : Q) (i : Fin (n + 3)) :
      (∫ j : Fin (n + 3), ∫ s : Q, ∫ k : Fin (n + 3),
        (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
          roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
        else 0) ∂finiteUniformMeasure ∂ν ∂finiteUniformMeasure) =
      ∫ s : Q, ∫ j : Fin (n + 3), ∫ k : Fin (n + 3),
        (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
          roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
        else 0) ∂finiteUniformMeasure ∂finiteUniformMeasure ∂ν := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapJ]
  have hswapI2 (q r : Q) :
      (∫ i : Fin (n + 3), ∫ s : Q, ∫ j : Fin (n + 3),
        ∫ k : Fin (n + 3),
          (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
            roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
          else 0) ∂finiteUniformMeasure ∂finiteUniformMeasure ∂ν
            ∂finiteUniformMeasure) =
      ∫ s : Q, ∫ i : Fin (n + 3), ∫ j : Fin (n + 3),
        ∫ k : Fin (n + 3),
          (if (q, i) ≠ (r, j) ∧ (r, j) ≠ (s, k) ∧ (s, k) ≠ (q, i) then
            roundedEdge H n q r * roundedEdge H n r s * roundedEdge H n s q
          else 0) ∂finiteUniformMeasure ∂finiteUniformMeasure
            ∂finiteUniformMeasure ∂ν := by
    exact integral_integral_swap Integrable.of_finite
  simp_rw [hswapI2, copyTriangle_average]

theorem roundingGraph_density_tendsto
    {Q : Type u} [Fintype Q] [DecidableEq Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {ν : Measure Q} [IsProbabilityMeasure ν]
    {H : Q → Q → Real} (hH : IsGraphon H ν) :
    Tendsto (fun n => edgeDensity (finiteGraphKernel (roundingGraph H n))
        (roundingMeasure ν n)) atTop (nhds (edgeDensity H ν)) ∧
      Tendsto (fun n => trace (roundingMeasure ν n)
        (compPow (roundingMeasure ν n)
          (finiteGraphKernel (roundingGraph H n)) 2)) atTop
        (nhds (trace ν (compPow ν H 2))) := by
  classical
  have hedgeSeq (n : Nat) :
      edgeDensity (finiteGraphKernel (roundingGraph H n))
          (roundingMeasure ν n) =
        ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} *
          (copyEdgeCoeff n q r * roundedEdge H n q r) := by
    rw [roundingGraph_edge_density_formula hH.nonneg hH.le_one hH.symm n]
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  have hedgeLim :
      edgeDensity H ν =
        ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} * H q r := by
    simp only [edgeDensity, mean, degree]
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  have htriSeq (n : Nat) :
      trace (roundingMeasure ν n)
          (compPow (roundingMeasure ν n)
            (finiteGraphKernel (roundingGraph H n)) 2) =
        ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} * ∑ s : Q,
          ν.real {s} * (copyTriangleCoeff n q r s *
            (roundedEdge H n q r * roundedEdge H n r s *
              roundedEdge H n s q)) := by
    rw [roundingGraph_triangle_density_formula hH.nonneg hH.le_one hH.symm n]
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply congrArg (fun t : Real => ν.real {q} * t)
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  have htriLim :
      trace ν (compPow ν H 2) =
        ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} * ∑ s : Q,
          ν.real {s} * (H q r * H r s * H s q) := by
    rw [trace_compPow_two_eq_triangleIntegral hH]
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    apply congrArg (fun t : Real => ν.real {q} * t)
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul]
  constructor
  · rw [show (fun n => edgeDensity (finiteGraphKernel (roundingGraph H n))
        (roundingMeasure ν n)) = fun n =>
          ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} *
            (copyEdgeCoeff n q r * roundedEdge H n q r) by
        funext n; exact hedgeSeq n]
    rw [hedgeLim]
    apply tendsto_finset_sum
    intro q _
    apply tendsto_const_nhds.mul
    apply tendsto_finset_sum
    intro r _
    apply tendsto_const_nhds.mul
    have hc := tendsto_copyEdgeCoeff_one (Q := Q) q r
    have hw := tendsto_roundedEdge hH.nonneg hH.symm q r
    simpa using hc.mul hw
  · rw [show (fun n => trace (roundingMeasure ν n)
        (compPow (roundingMeasure ν n)
          (finiteGraphKernel (roundingGraph H n)) 2)) = fun n =>
          ∑ q : Q, ν.real {q} * ∑ r : Q, ν.real {r} * ∑ s : Q,
            ν.real {s} * (copyTriangleCoeff n q r s *
              (roundedEdge H n q r * roundedEdge H n r s *
                roundedEdge H n s q)) by
        funext n; exact htriSeq n]
    rw [htriLim]
    apply tendsto_finset_sum
    intro q _
    apply tendsto_const_nhds.mul
    apply tendsto_finset_sum
    intro r _
    apply tendsto_const_nhds.mul
    apply tendsto_finset_sum
    intro s _
    apply tendsto_const_nhds.mul
    have hc := tendsto_copyTriangleCoeff_one (Q := Q) q r s
    have hqr := tendsto_roundedEdge hH.nonneg hH.symm q r
    have hrs := tendsto_roundedEdge hH.nonneg hH.symm r s
    have hsq := tendsto_roundedEdge hH.nonneg hH.symm s q
    simpa [mul_assoc] using hc.mul ((hqr.mul hrs).mul hsq)

end OddCycleBound
