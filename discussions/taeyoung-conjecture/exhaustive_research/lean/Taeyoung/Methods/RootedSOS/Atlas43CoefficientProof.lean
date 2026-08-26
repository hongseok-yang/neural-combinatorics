import Taeyoung.Methods.RootedSOS.Atlas43CommonGramExact
import Taeyoung.Methods.RootedSOS.Atlas43CoefficientChecks
import Taeyoung.Methods.RootedSOS.Atlas43PartitionChecks

/-!
# The Atlas 43 certificate identity

This module turns the kernel-checked rational matrix data into the analytic
rooted-SOS identity.  It proves the full Gram entries, groups the 4,096 flag
pairs into the 33 checked fixed-density rows, expands their five polynomial
coefficients, and integrates the shared-Bernoulli flag products.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

open Taeyoung.Methods.RootedSOS.Atlas43Data
open Taeyoung.Methods.RootedSOS.Atlas43Gram
open Taeyoung.Methods.RootedSOS.Atlas43PSD
open Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData
open Taeyoung.Methods.RootedSOS.Atlas43Flags
open Taeyoung.Methods.RootedSOS.Atlas43Cores
open Taeyoung.Methods.RootedSOS.House

set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def rawGroupPartitionValid : Bool :=
  decide (∀ a b : Fin 64, ∃ row : Fin 33,
    sameRawGroup (rawGroupKey row).1 (rawGroupKey row).2 a b ∧
      ∀ other : Fin 33,
        sameRawGroup (rawGroupKey other).1 (rawGroupKey other).2 a b →
          other = row)

theorem raw_group_partition_valid : rawGroupPartitionValid = true := by
  rw [rawGroupPartitionValid, decide_eq_true_eq]
  exact raw_group_partition_checked

def rawGroupIsolatedLeTwoValid : Bool :=
  decide (∀ row : Fin 33, (rawGroupKey row).2 ≤ 2)

theorem raw_group_isolated_le_two_valid : rawGroupIsolatedLeTwoValid = true := by
  rw [rawGroupIsolatedLeTwoValid, decide_eq_true_eq]
  exact raw_group_isolated_le_two_checked

def rawGroupCoreLt53Valid : Bool :=
  decide (∀ row : Fin 33, (rawGroupKey row).1 < 53)

theorem raw_group_core_lt_53_valid : rawGroupCoreLt53Valid = true := by
  rw [rawGroupCoreLt53Valid, decide_eq_true_eq]
  exact raw_group_core_lt_53_checked

def fullRatGram₀ (a b : Fin 128) : Rat :=
  ∑ j : Fin 107,
    (Rat.ofInt (F₀Int a j) +
      ∑ i : Fin 107, Rat.ofInt (F₀Int a i) * C₀ i j) *
        Rat.ofInt (F₀Int b j)

def fullRatGram₁ (a b : Fin 64) : Rat :=
  ∑ j : Fin 48,
    (Rat.ofInt (F₁Int a j) +
      ∑ i : Fin 48, Rat.ofInt (F₁Int a i) * C₁ i j) *
        Rat.ofInt (F₁Int b j)

def commonOnlyRatGram₀ (a b : Fin 128) : Rat :=
  ∑ j : Fin 107,
    (Rat.ofInt (F₀Int a j) +
      ∑ i : Fin 107, Rat.ofInt (F₀Int a i) * commonC₀ i j) *
        Rat.ofInt (F₀Int b j)

def commonOnlyRatGram₁ (a b : Fin 64) : Rat :=
  ∑ j : Fin 48,
    (Rat.ofInt (F₁Int a j) +
      ∑ i : Fin 48, Rat.ofInt (F₁Int a i) * commonC₁ i j) *
        Rat.ofInt (F₁Int b j)

lemma rat_ofInt_list_sum_div (values : List Int) (denominator : Int) :
    Rat.ofInt values.sum / Rat.ofInt denominator =
      (values.map fun value ↦ Rat.ofInt value / Rat.ofInt denominator).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons, List.map_cons]
      simp only [Rat.ofInt_eq_cast] at ih ⊢
      push_cast at ih ⊢
      rw [add_div, ih]

lemma rat_ofInt_list_sum (values : List Int) :
    Rat.ofInt values.sum = (values.map Rat.ofInt).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons, List.map_cons]
      simp only [Rat.ofInt_eq_cast] at ih ⊢
      push_cast at ih ⊢
      rw [ih]

lemma weighted_double_sum_list {m n : Nat} {R : Type*} [CommRing R]
    (values : List (κ × κ)) (weight : Fin m → Fin n → R)
    (left : κ → Fin m → R) (right : κ → Fin n → R) :
    (∑ i, ∑ j, weight i j *
      (values.map fun pair ↦ left pair.1 i * right pair.2 j).sum) =
      (values.map fun pair ↦
        ∑ i, ∑ j, left pair.1 i * weight i j * right pair.2 j).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma list_sum_map_filter {R α : Type*} [AddCommMonoid R]
    (values : List α) (predicate : α → Bool) (f : α → R) :
    ((values.filter predicate).map f).sum =
      (values.map fun value ↦ if predicate value then f value else 0).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      by_cases h : predicate head <;> simp [h, ih]

lemma list_sum_map_flatten {R α : Type*} [AddCommMonoid R]
    (values : List (List α)) (f : α → R) :
    (values.flatten.map f).sum =
      (values.map fun row ↦ (row.map f).sum).sum := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [Function.comp_def, ih]

lemma common_group_total₀_eq_claim_sum
    (block₀ block₁ : Fin 2) (core isolated : Nat) :
    commonGroupTotal₀ block₀ block₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        Rat.ofInt (claimedCommonGram₀Scaled (extendedIndex block₀ pair.1)
          (extendedIndex block₁ pair.2)) /
            Rat.ofInt commonCorrectionDenominator).sum := by
  unfold commonGroupTotal₀
  rw [rat_ofInt_list_sum_div]
  rw [List.map_map]
  rfl

lemma common_group_total₀_eq_common_sum
    (block₀ block₁ : Fin 2) (core isolated : Nat) :
    commonGroupTotal₀ block₀ block₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        commonOnlyRatGram₀ (extendedIndex block₀ pair.1)
          (extendedIndex block₁ pair.2)).sum := by
  rw [common_group_total₀_eq_claim_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  simpa [commonOnlyRatGram₀, commonRatGram₀] using common_gram₀_rational_exact
    (extendedIndex block₀ pair.1) (extendedIndex block₁ pair.2)

lemma exceptional_group_total₀_eq_difference
    (block₀ block₁ : Fin 2) (core isolated : Nat) :
    exceptionalGroupTotal₀ block₀ block₁ core isolated =
      ∑ i : Fin 107, ∑ j : Fin 107,
        (C₀ i j - commonC₀ i j) * Rat.ofInt
          (((rawGroupPairs core isolated).map fun pair ↦
            F₀Int (extendedIndex block₀ pair.1) i *
              F₀Int (extendedIndex block₁ pair.2) j).sum) := by
  unfold exceptionalGroupTotal₀
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (if _ then 0 else
    C₀ i j * Rat.ofInt
      (((rawGroupPairs core isolated).map fun pair : Fin 64 × Fin 64 ↦
        F₀Int (extendedIndex block₀ pair.1) i *
          F₀Int (extendedIndex block₁ pair.2) j).sum)) = _
  split <;> simp_all [commonC₀, Rat.ofInt_eq_cast]

lemma full_rat_gram₀_eq_common_add_difference (a b : Fin 128) :
    fullRatGram₀ a b = commonOnlyRatGram₀ a b +
      ∑ i : Fin 107, ∑ j : Fin 107,
        Rat.ofInt (F₀Int a i) * (C₀ i j - commonC₀ i j) *
          Rat.ofInt (F₀Int b j) := by
  unfold fullRatGram₀ commonOnlyRatGram₀
  rw [show (∑ i : Fin 107, ∑ j : Fin 107,
      Rat.ofInt (F₀Int a i) * (C₀ i j - commonC₀ i j) *
        Rat.ofInt (F₀Int b j)) =
      ∑ j : Fin 107, ∑ i : Fin 107,
        Rat.ofInt (F₀Int a i) * (C₀ i j - commonC₀ i j) *
          Rat.ofInt (F₀Int b j) by rw [Finset.sum_comm]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∑ i : Fin 107,
      Rat.ofInt (F₀Int a i) * (C₀ i j - commonC₀ i j) *
        Rat.ofInt (F₀Int b j)) =
      (∑ i : Fin 107, Rat.ofInt (F₀Int a i) * C₀ i j *
        Rat.ofInt (F₀Int b j)) -
      (∑ i : Fin 107, Rat.ofInt (F₀Int a i) * commonC₀ i j *
        Rat.ofInt (F₀Int b j)) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  simp only [add_mul, Finset.sum_mul]
  ring

lemma fullRatGram₀_symm (a b : Fin 128) :
    fullRatGram₀ a b = fullRatGram₀ b a := by
  unfold fullRatGram₀
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  apply congrArg₂ (fun x y ↦ x + y)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [C₀_symm i j]
    ring

lemma exceptional_group_total₀_eq_difference_sum
    (block₀ block₁ : Fin 2) (core isolated : Nat) :
    exceptionalGroupTotal₀ block₀ block₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        ∑ i : Fin 107, ∑ j : Fin 107,
          Rat.ofInt (F₀Int (extendedIndex block₀ pair.1) i) *
            (C₀ i j - commonC₀ i j) *
              Rat.ofInt (F₀Int (extendedIndex block₁ pair.2) j)).sum := by
  rw [exceptional_group_total₀_eq_difference]
  simp_rw [rat_ofInt_list_sum]
  simp only [List.map_map, Function.comp_def, Rat.ofInt_eq_cast]
  push_cast
  exact weighted_double_sum_list (rawGroupPairs core isolated)
    (fun i j ↦ C₀ i j - commonC₀ i j)
    (fun pair i ↦ Rat.ofInt (F₀Int (extendedIndex block₀ pair) i))
    (fun pair j ↦ Rat.ofInt (F₀Int (extendedIndex block₁ pair) j))

lemma computed_group_total₀_eq_full_sum
    (block₀ block₁ : Fin 2) (core isolated : Nat) :
    computedGroupTotal₀ block₀ block₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        fullRatGram₀ (extendedIndex block₀ pair.1)
          (extendedIndex block₁ pair.2)).sum := by
  rw [computedGroupTotal₀, common_group_total₀_eq_common_sum,
    exceptional_group_total₀_eq_difference_sum]
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  exact (full_rat_gram₀_eq_common_add_difference
    (extendedIndex block₀ pair.1) (extendedIndex block₁ pair.2)).symm

lemma common_group_total₁_eq_claim_sum (core isolated : Nat) :
    commonGroupTotal₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        Rat.ofInt (claimedCommonGram₁Scaled pair.1 pair.2) /
          Rat.ofInt commonCorrectionDenominator).sum := by
  unfold commonGroupTotal₁
  rw [rat_ofInt_list_sum_div]
  rw [List.map_map]
  rfl

lemma common_group_total₁_eq_common_sum (core isolated : Nat) :
    commonGroupTotal₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        commonOnlyRatGram₁ pair.1 pair.2).sum := by
  rw [common_group_total₁_eq_claim_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  simpa [commonOnlyRatGram₁, commonRatGram₁] using
    common_gram₁_rational_exact pair.1 pair.2

lemma exceptional_group_total₁_eq_difference (core isolated : Nat) :
    exceptionalGroupTotal₁ core isolated =
      ∑ i : Fin 48, ∑ j : Fin 48,
        (C₁ i j - commonC₁ i j) * Rat.ofInt
          (((rawGroupPairs core isolated).map fun pair ↦
            F₁Int pair.1 i * F₁Int pair.2 j).sum) := by
  unfold exceptionalGroupTotal₁
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (if _ then 0 else
    C₁ i j * Rat.ofInt
      (((rawGroupPairs core isolated).map fun pair : Fin 64 × Fin 64 ↦
        F₁Int pair.1 i * F₁Int pair.2 j).sum)) = _
  split <;> simp_all [commonC₁, Rat.ofInt_eq_cast]

lemma full_rat_gram₁_eq_common_add_difference (a b : Fin 64) :
    fullRatGram₁ a b = commonOnlyRatGram₁ a b +
      ∑ i : Fin 48, ∑ j : Fin 48,
        Rat.ofInt (F₁Int a i) * (C₁ i j - commonC₁ i j) *
          Rat.ofInt (F₁Int b j) := by
  unfold fullRatGram₁ commonOnlyRatGram₁
  rw [show (∑ i : Fin 48, ∑ j : Fin 48,
      Rat.ofInt (F₁Int a i) * (C₁ i j - commonC₁ i j) *
        Rat.ofInt (F₁Int b j)) =
      ∑ j : Fin 48, ∑ i : Fin 48,
        Rat.ofInt (F₁Int a i) * (C₁ i j - commonC₁ i j) *
          Rat.ofInt (F₁Int b j) by rw [Finset.sum_comm]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∑ i : Fin 48,
      Rat.ofInt (F₁Int a i) * (C₁ i j - commonC₁ i j) *
        Rat.ofInt (F₁Int b j)) =
      (∑ i : Fin 48, Rat.ofInt (F₁Int a i) * C₁ i j *
        Rat.ofInt (F₁Int b j)) -
      (∑ i : Fin 48, Rat.ofInt (F₁Int a i) * commonC₁ i j *
        Rat.ofInt (F₁Int b j)) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  simp only [add_mul, Finset.sum_mul]
  ring

lemma exceptional_group_total₁_eq_difference_sum (core isolated : Nat) :
    exceptionalGroupTotal₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        ∑ i : Fin 48, ∑ j : Fin 48,
          Rat.ofInt (F₁Int pair.1 i) * (C₁ i j - commonC₁ i j) *
            Rat.ofInt (F₁Int pair.2 j)).sum := by
  rw [exceptional_group_total₁_eq_difference]
  simp_rw [rat_ofInt_list_sum]
  simp only [List.map_map, Function.comp_def, Rat.ofInt_eq_cast]
  push_cast
  exact weighted_double_sum_list (rawGroupPairs core isolated)
    (fun i j ↦ C₁ i j - commonC₁ i j)
    (fun pair i ↦ Rat.ofInt (F₁Int pair i))
    (fun pair j ↦ Rat.ofInt (F₁Int pair j))

lemma computed_group_total₁_eq_full_sum (core isolated : Nat) :
    computedGroupTotal₁ core isolated =
      ((rawGroupPairs core isolated).map fun pair ↦
        fullRatGram₁ pair.1 pair.2).sum := by
  rw [computedGroupTotal₁, common_group_total₁_eq_common_sum,
    exceptional_group_total₁_eq_difference_sum]
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  exact (full_rat_gram₁_eq_common_add_difference pair.1 pair.2).symm

/-! ## Bounded-memory reconstruction of the exceptional group totals -/

lemma staged_correction₀_rational_exact (i j : Fin 107) :
    Rat.ofInt (stagedExceptionalScaledCorrection₀ i j) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int) =
      C₀ i j - commonC₀ i j := by
  have h := all_scaled_correction0_rational_valid i j
  simpa [stagedCorrectionRational₀Valid, beq_iff_eq] using h

lemma staged_correction₁_rational_exact (i j : Fin 48) :
    Rat.ofInt (stagedExceptionalScaledCorrection₁ i j) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₁ : Int) =
      C₁ i j - commonC₁ i j := by
  have h := all_scaled_correction1_rational_valid i j
  simpa [stagedCorrectionRational₁Valid, beq_iff_eq] using h

lemma raw_group_pairs_sum_eq_indicator
    {R : Type*} [AddCommMonoid R]
    (core isolated : Nat) (f : Fin 64 × Fin 64 → R) :
    ((rawGroupPairs core isolated).map f).sum =
      ∑ a : Fin 64, ∑ b : Fin 64,
        if sameRawGroup core isolated a b then f (a, b) else 0 := by
  unfold rawGroupPairs
  rw [list_sum_map_filter, list_sum_map_flatten]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

lemma exists_unique_raw_group (a b : Fin 64) :
    ∃! row : Fin 33,
      sameRawGroup (rawGroupKey row).1 (rawGroupKey row).2 a b := by
  have h := raw_group_partition_valid
  simp only [rawGroupPartitionValid, decide_eq_true_eq] at h
  obtain ⟨row, hrow, hunique⟩ := h a b
  exact ⟨row, hrow, hunique⟩

lemma sum_raw_group_indicators {R : Type*} [AddCommMonoid R]
    (f : Fin 64 × Fin 64 → R) :
    (∑ row : Fin 33, ∑ a : Fin 64, ∑ b : Fin 64,
      if sameRawGroup (rawGroupKey row).1 (rawGroupKey row).2 a b then
        f (a, b) else 0) = ∑ a : Fin 64, ∑ b : Fin 64, f (a, b) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  obtain ⟨row, hrow, hunique⟩ := exists_unique_raw_group a b
  rw [Finset.sum_eq_single row]
  · simp [hrow]
  · intro other _ hne
    have hnot : ¬ sameRawGroup (rawGroupKey other).1
        (rawGroupKey other).2 a b := by
      intro hother
      exact hne (hunique other hother)
    simp [hnot]
  · simp

lemma sum_raw_group_pair_sums {R : Type*} [AddCommMonoid R]
    (f : Fin 64 × Fin 64 → R) :
    (∑ row : Fin 33,
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map f).sum) =
        ∑ a : Fin 64, ∑ b : Fin 64, f (a, b) := by
  simp_rw [raw_group_pairs_sum_eq_indicator]
  exact sum_raw_group_indicators f

lemma mem_rawGroupPairs_iff (core isolated : Nat) (pair : Fin 64 × Fin 64) :
    pair ∈ rawGroupPairs core isolated ↔
      sameRawGroup core isolated pair.1 pair.2 := by
  unfold rawGroupPairs
  rw [List.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [List.mem_flatten, List.mem_ofFn]
    refine ⟨List.ofFn (fun b : Fin 64 ↦ (pair.1, b)), ⟨pair.1, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨pair.2, Prod.eta pair⟩

lemma sameRawGroup_eq (core isolated : Nat) (a b : Fin 64)
    (h : sameRawGroup core isolated a b) :
    coreId a b = core ∧
      isolatedEdgeCountFin5 (gluedOrdinaryGraph a b) = isolated := by
  simpa [sameRawGroup, Bool.and_eq_true, beq_iff_eq] using h

lemma list_sum_map_mul {R α : Type*} [CommRing R]
    (values : List α) (f : α → R) (c : R) :
    (values.map f).sum * c = (values.map fun value ↦ f value * c).sum := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [add_mul, ih]

lemma sum_groups_mul_key (g : Fin 64 × Fin 64 → Real)
    (q : Nat → Nat → Real) :
    (∑ row : Fin 33,
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map g).sum *
        q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        g (a, b) * q (coreId a b)
          (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) := by
  calc
    (∑ row : Fin 33,
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map g).sum *
        q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          g pair * q (rawGroupKey row).1 (rawGroupKey row).2).sum := by
        apply Finset.sum_congr rfl
        intro row _
        exact list_sum_map_mul _ _ _
    _ = ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          g pair * q (coreId pair.1 pair.2)
            (isolatedEdgeCountFin5 (gluedOrdinaryGraph pair.1 pair.2))).sum := by
      apply Finset.sum_congr rfl
      intro row _
      apply congrArg List.sum
      apply List.map_congr_left
      intro pair hpair
      have hkey := sameRawGroup_eq (rawGroupKey row).1 (rawGroupKey row).2
        pair.1 pair.2 ((mem_rawGroupPairs_iff _ _ pair).mp hpair)
      rw [hkey.1, hkey.2]
    _ = ∑ a : Fin 64, ∑ b : Fin 64,
        g (a, b) * q (coreId a b)
          (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) :=
      sum_raw_group_pair_sums _

lemma rawGroupPairs_length_le (core isolated : Nat) :
    (rawGroupPairs core isolated).length ≤ 4096 := by
  unfold rawGroupPairs
  calc
    _ ≤ (List.ofFn fun a : Fin 64 ↦
        List.ofFn fun b : Fin 64 ↦ (a, b)).flatten.length :=
      List.length_filter_le _ _
    _ = 4096 := by norm_num

lemma natAbs_list_sum_le_length_mul (values : List Int) (bound : Nat)
    (h : ∀ value ∈ values, value.natAbs ≤ bound) :
    values.sum.natAbs ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      calc
        (head + tail.sum).natAbs ≤ head.natAbs + tail.sum.natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ bound + tail.length * bound :=
          Nat.add_le_add (h head (by simp))
            (ih (fun value hvalue ↦ h value (by simp [hvalue])))
        _ = (head :: tail).length * bound := by
          simp [Nat.succ_mul, Nat.add_comm]

lemma raw_group_index_eq_of_mem (row : Fin 33) (pair : Fin 64 × Fin 64)
    (hpair : pair ∈ rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2) :
    claimedRawGroupIndex pair.1 pair.2 = row.1 := by
  have hsame := (mem_rawGroupPairs_iff _ _ pair).mp hpair
  have hchecked := raw_group_index_checked pair.1 pair.2
  have hfin : row = claimedRawGroupIndexFin pair.1 pair.2 :=
    hchecked.2.2 row hsame
  have hval := congrArg Fin.val hfin
  simp [claimedRawGroupIndexFin,
    Nat.mod_eq_of_lt hchecked.1] at hval
  omega

lemma actual_exceptional_pair_weight₀_eq_sum
    (entry : Fin 66) (slot : Fin 3) (row : Fin 33) :
    actualExceptionalPairWeight₀ entry slot row =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map
        fun pair ↦ exceptionalPairContribution₀ entry slot pair.1 pair.2).sum := by
  fin_cases slot <;>
    simp [actualExceptionalPairWeight₀, exceptionalPairContribution₀,
      groupPairWeight₀, List.sum_map_add] <;>
    by_cases h : exceptionalLeft₀ entry = exceptionalRight₀ entry <;>
      simp [h]

lemma actual_exceptional_pair_weight₁_eq_sum
    (entry : Fin 15) (row : Fin 33) :
    actualExceptionalPairWeight₁ entry row =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map
        fun pair ↦ exceptionalPairContribution₁ entry pair.1 pair.2).sum := by
  simp [actualExceptionalPairWeight₁, exceptionalPairContribution₁,
    groupPairWeight₁, List.sum_map_add]
  by_cases h : exceptionalLeft₁ entry = exceptionalRight₁ entry <;>
    simp [h]

lemma actual_exceptional_pair_weight₀_bound
    (entry : Fin 66) (slot : Fin 3) (row : Fin 33) :
    (actualExceptionalPairWeight₀ entry slot row).natAbs ≤
      Atlas43RawGroupWitnessData.pairWeightBound₀ := by
  have hv := all_exceptional_pair_weight0_valid entry slot
  simp only [exceptionalPairWeight₀EncodingValid, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hv
  rw [actual_exceptional_pair_weight₀_eq_sum]
  calc
    _ ≤ (rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).length *
        pairWeightTermBound₀ := by
      simpa using natAbs_list_sum_le_length_mul
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map
          fun pair ↦ exceptionalPairContribution₀ entry slot pair.1 pair.2)
        pairWeightTermBound₀ (by
          intro value hvalue
          simp only [List.mem_map] at hvalue
          obtain ⟨pair, _hpair, rfl⟩ := hvalue
          exact hv.1.2 pair.1 pair.2)
    _ ≤ 4096 * pairWeightTermBound₀ :=
      Nat.mul_le_mul_right _ (rawGroupPairs_length_le _ _)
    _ = Atlas43RawGroupWitnessData.pairWeightBound₀ := by
      rfl

lemma actual_exceptional_pair_weight₁_bound
    (entry : Fin 15) (row : Fin 33) :
    (actualExceptionalPairWeight₁ entry row).natAbs ≤
      Atlas43RawGroupWitnessData.pairWeightBound₁ := by
  have hv := all_exceptional_pair_weight1_valid entry
  simp only [exceptionalPairWeight₁EncodingValid, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hv
  rw [actual_exceptional_pair_weight₁_eq_sum]
  calc
    _ ≤ (rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).length *
        pairWeightTermBound₁ := by
      simpa using natAbs_list_sum_le_length_mul
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map
          fun pair ↦ exceptionalPairContribution₁ entry pair.1 pair.2)
        pairWeightTermBound₁ (by
          intro value hvalue
          simp only [List.mem_map] at hvalue
          obtain ⟨pair, _hpair, rfl⟩ := hvalue
          exact hv.1.2 pair.1 pair.2)
    _ ≤ 4096 * pairWeightTermBound₁ :=
      Nat.mul_le_mul_right _ (rawGroupPairs_length_le _ _)
    _ = Atlas43RawGroupWitnessData.pairWeightBound₁ := by
      rfl

lemma actual_pair_weight₀_power_sum (entry : Fin 66) (slot : Fin 3) :
    (∑ row : Fin 33, actualExceptionalPairWeight₀ entry slot row *
      (pairWeightBase₀ : Int) ^ row.1) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        exceptionalPairContribution₀ entry slot a b *
          (pairWeightBase₀ : Int) ^ claimedRawGroupIndex a b := by
  rw [← sum_raw_group_pair_sums
    (fun pair ↦ exceptionalPairContribution₀ entry slot pair.1 pair.2 *
      (pairWeightBase₀ : Int) ^ claimedRawGroupIndex pair.1 pair.2)]
  apply Finset.sum_congr rfl
  intro row _
  rw [actual_exceptional_pair_weight₀_eq_sum, list_sum_map_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair hpair
  rw [raw_group_index_eq_of_mem row pair hpair]

lemma actual_pair_weight₁_power_sum (entry : Fin 15) :
    (∑ row : Fin 33, actualExceptionalPairWeight₁ entry row *
      (pairWeightBase₁ : Int) ^ row.1) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        exceptionalPairContribution₁ entry a b *
          (pairWeightBase₁ : Int) ^ claimedRawGroupIndex a b := by
  rw [← sum_raw_group_pair_sums
    (fun pair ↦ exceptionalPairContribution₁ entry pair.1 pair.2 *
      (pairWeightBase₁ : Int) ^ claimedRawGroupIndex pair.1 pair.2)]
  apply Finset.sum_congr rfl
  intro row _
  rw [actual_exceptional_pair_weight₁_eq_sum, list_sum_map_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair hpair
  rw [raw_group_index_eq_of_mem row pair hpair]

lemma shiftedEncoding_ofFn_eq_bound_add_sum {n base bound : Nat}
    (values : Fin n → Int) (hvalues : ∀ i, (values i).natAbs ≤ bound) :
    shiftedEncoding base bound (List.ofFn values) =
      bound * geometricEncoding base n +
        ∑ i : Fin n, values i * (base : Int) ^ i.1 := by
  rw [shiftedEncoding_ofFn_eq_sum values hvalues]
  rw [geometricEncoding, ← Fin.sum_univ_eq_sum_range]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

lemma actual_pair_weight₀_encoding (entry : Fin 66) (slot : Fin 3) :
    shiftedEncoding pairWeightBase₀
        Atlas43RawGroupWitnessData.pairWeightBound₀
        (List.ofFn fun row : Fin 33 ↦ actualExceptionalPairWeight₀ entry slot row) =
      computedPairWeightEncoding₀ entry slot := by
  rw [shiftedEncoding_ofFn_eq_bound_add_sum _
    (fun row ↦ actual_exceptional_pair_weight₀_bound entry slot row)]
  rw [actual_pair_weight₀_power_sum]
  rfl

lemma actual_pair_weight₁_encoding (entry : Fin 15) :
    shiftedEncoding pairWeightBase₁
        Atlas43RawGroupWitnessData.pairWeightBound₁
        (List.ofFn fun row : Fin 33 ↦ actualExceptionalPairWeight₁ entry row) =
      computedPairWeightEncoding₁ entry := by
  rw [shiftedEncoding_ofFn_eq_bound_add_sum _
    (fun row ↦ actual_exceptional_pair_weight₁_bound entry row)]
  rw [actual_pair_weight₁_power_sum]
  rfl

lemma exceptional_pair_weight₀_exact
    (entry : Fin 66) (slot : Fin 3) (row : Fin 33) :
    claimedExceptionalPairWeight₀ entry slot row =
      actualExceptionalPairWeight₀ entry slot row := by
  have hv := all_exceptional_pair_weight0_valid entry slot
  simp only [exceptionalPairWeight₀EncodingValid, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hv
  have hfun := shiftedEncoding_injective_of_bound
    (n := 33) (base := pairWeightBase₀)
    (bound := Atlas43RawGroupWitnessData.pairWeightBound₀)
    (hbound := by decide +kernel) (hbase := rfl)
    (fun row ↦ claimedExceptionalPairWeight₀ entry slot row)
    (fun row ↦ actualExceptionalPairWeight₀ entry slot row)
    hv.1.1 (fun r ↦ actual_exceptional_pair_weight₀_bound entry slot r)
    (hv.2.trans (actual_pair_weight₀_encoding entry slot).symm)
  exact congrFun hfun row

lemma exceptional_pair_weight₁_exact (entry : Fin 15) (row : Fin 33) :
    claimedExceptionalPairWeight₁ entry row =
      actualExceptionalPairWeight₁ entry row := by
  have hv := all_exceptional_pair_weight1_valid entry
  simp only [exceptionalPairWeight₁EncodingValid, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hv
  have hfun := shiftedEncoding_injective_of_bound
    (n := 33) (base := pairWeightBase₁)
    (bound := Atlas43RawGroupWitnessData.pairWeightBound₁)
    (hbound := by decide +kernel) (hbase := rfl)
    (fun row ↦ claimedExceptionalPairWeight₁ entry row)
    (fun row ↦ actualExceptionalPairWeight₁ entry row)
    hv.1.1 (fun r ↦ actual_exceptional_pair_weight₁_bound entry r)
    (hv.2.trans (actual_pair_weight₁_encoding entry).symm)
  exact congrFun hfun row

lemma computed_exceptional_scaled_total₀_eq_sparse
    (row : Fin 33) (slot : Fin 3) :
    computedExceptionalScaledTotal₀ row slot =
      sparseSymmetricBilinear exceptionalLeft₀ exceptionalRight₀ exceptionalValue₀
        (match slot.1 with
        | 0 => groupPairWeight₀ 0 0 (rawGroupKey row).1 (rawGroupKey row).2
        | 1 => groupPairWeight₀ 0 1 (rawGroupKey row).1 (rawGroupKey row).2
        | _ => groupPairWeight₀ 1 1 (rawGroupKey row).1 (rawGroupKey row).2) := by
  unfold computedExceptionalScaledTotal₀ sparseSymmetricBilinear
  apply Finset.sum_congr rfl
  intro entry _
  rw [exceptional_pair_weight₀_exact entry slot row]
  fin_cases slot <;> rfl

lemma computed_exceptional_scaled_total₁_eq_sparse (row : Fin 33) :
    computedExceptionalScaledTotal₁ row =
      sparseSymmetricBilinear exceptionalLeft₁ exceptionalRight₁ exceptionalValue₁
        (groupPairWeight₁ (rawGroupKey row).1 (rawGroupKey row).2) := by
  unfold computedExceptionalScaledTotal₁ sparseSymmetricBilinear
  apply Finset.sum_congr rfl
  intro entry _
  rw [exceptional_pair_weight₁_exact entry row]
  rfl

lemma rat_double_sum_scaled {n : Nat} (matrix term : Fin n → Fin n → Int)
    (denominator : Nat) :
    (∑ i : Fin n, ∑ j : Fin n,
      (Rat.ofInt (matrix i j) / Rat.ofInt denominator) * Rat.ofInt (term i j)) =
      Rat.ofInt (∑ i : Fin n, ∑ j : Fin n, matrix i j * term i j) /
        Rat.ofInt denominator := by
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
        Rat.ofInt (matrix i j * term i j) / Rat.ofInt denominator := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Rat.ofInt_eq_cast]
      push_cast
      ring
    _ = (∑ i : Fin n, ∑ j : Fin n,
        Rat.ofInt (matrix i j * term i j)) / Rat.ofInt denominator := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div]
    _ = _ := by
      congr 1
      simp only [Rat.ofInt_eq_cast]
      push_cast
      rfl

lemma exceptional_group_total₀_zero_zero_eq_scaled (row : Fin 33) :
    exceptionalGroupTotal₀ 0 0 (rawGroupKey row).1 (rawGroupKey row).2 =
      Rat.ofInt (computedExceptionalScaledTotal₀ row 0) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int) := by
  rw [exceptional_group_total₀_eq_difference]
  simp_rw [← staged_correction₀_rational_exact]
  rw [rat_double_sum_scaled]
  simp only [stagedExceptionalScaledCorrection₀]
  rw [sparseSymmetricMatrix_bilinear]
  rw [show (fun i j : Fin 107 ↦
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        F₀Int (extendedIndex 0 pair.1) i *
          F₀Int (extendedIndex 0 pair.2) j).sum) =
      groupPairWeight₀ 0 0 (rawGroupKey row).1 (rawGroupKey row).2 from rfl]
  have hs : computedExceptionalScaledTotal₀ row 0 =
      sparseSymmetricBilinear exceptionalLeft₀ exceptionalRight₀ exceptionalValue₀
        (groupPairWeight₀ 0 0 (rawGroupKey row).1 (rawGroupKey row).2) := by
    simpa using computed_exceptional_scaled_total₀_eq_sparse row (0 : Fin 3)
  rw [← hs]

lemma exceptional_group_total₀_zero_one_eq_scaled (row : Fin 33) :
    exceptionalGroupTotal₀ 0 1 (rawGroupKey row).1 (rawGroupKey row).2 =
      Rat.ofInt (computedExceptionalScaledTotal₀ row 1) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int) := by
  rw [exceptional_group_total₀_eq_difference]
  simp_rw [← staged_correction₀_rational_exact]
  rw [rat_double_sum_scaled]
  simp only [stagedExceptionalScaledCorrection₀]
  rw [sparseSymmetricMatrix_bilinear]
  rw [show (fun i j : Fin 107 ↦
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        F₀Int (extendedIndex 0 pair.1) i *
          F₀Int (extendedIndex 1 pair.2) j).sum) =
      groupPairWeight₀ 0 1 (rawGroupKey row).1 (rawGroupKey row).2 from rfl]
  have hs : computedExceptionalScaledTotal₀ row 1 =
      sparseSymmetricBilinear exceptionalLeft₀ exceptionalRight₀ exceptionalValue₀
        (groupPairWeight₀ 0 1 (rawGroupKey row).1 (rawGroupKey row).2) := by
    simpa using computed_exceptional_scaled_total₀_eq_sparse row (1 : Fin 3)
  rw [← hs]

lemma exceptional_group_total₀_one_one_eq_scaled (row : Fin 33) :
    exceptionalGroupTotal₀ 1 1 (rawGroupKey row).1 (rawGroupKey row).2 =
      Rat.ofInt (computedExceptionalScaledTotal₀ row 2) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int) := by
  rw [exceptional_group_total₀_eq_difference]
  simp_rw [← staged_correction₀_rational_exact]
  rw [rat_double_sum_scaled]
  simp only [stagedExceptionalScaledCorrection₀]
  rw [sparseSymmetricMatrix_bilinear]
  rw [show (fun i j : Fin 107 ↦
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        F₀Int (extendedIndex 1 pair.1) i *
          F₀Int (extendedIndex 1 pair.2) j).sum) =
      groupPairWeight₀ 1 1 (rawGroupKey row).1 (rawGroupKey row).2 from rfl]
  have hs : computedExceptionalScaledTotal₀ row 2 =
      sparseSymmetricBilinear exceptionalLeft₀ exceptionalRight₀ exceptionalValue₀
        (groupPairWeight₀ 1 1 (rawGroupKey row).1 (rawGroupKey row).2) := by
    simpa using computed_exceptional_scaled_total₀_eq_sparse row (2 : Fin 3)
  rw [← hs]

lemma exceptional_group_total₁_eq_scaled (row : Fin 33) :
    exceptionalGroupTotal₁ (rawGroupKey row).1 (rawGroupKey row).2 =
      Rat.ofInt (computedExceptionalScaledTotal₁ row) /
        Rat.ofInt (Atlas43RawGroupWitnessData.exceptionalDenominator₁ : Int) := by
  rw [exceptional_group_total₁_eq_difference]
  simp_rw [← staged_correction₁_rational_exact]
  rw [rat_double_sum_scaled]
  simp only [stagedExceptionalScaledCorrection₁]
  rw [sparseSymmetricMatrix_bilinear]
  rw [show (fun i j : Fin 48 ↦
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        F₁Int pair.1 i * F₁Int pair.2 j).sum) =
      groupPairWeight₁ (rawGroupKey row).1 (rawGroupKey row).2 from rfl]
  rw [← computed_exceptional_scaled_total₁_eq_sparse row]

theorem all_raw_group_arithmetic_valid (row : Fin 33) :
    rawGroupArithmeticValid row = true := by
  have h0 := all_scaled_group_cells_valid row (0 : Fin 4)
  have h1 := all_scaled_group_cells_valid row (1 : Fin 4)
  have h2 := all_scaled_group_cells_valid row (2 : Fin 4)
  have h3 := all_scaled_group_cells_valid row (3 : Fin 4)
  change ((claimedExceptionalScaledTotal row 0 ==
      computedExceptionalScaledTotal₀ row 0) &&
    (claimedGroupTotal row 0 ==
      commonGroupTotal₀ 0 0 (rawGroupKey row).1 (rawGroupKey row).2 +
        Rat.ofInt (claimedExceptionalScaledTotal row 0) /
          Rat.ofInt
            (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int))) = true at h0
  change ((claimedExceptionalScaledTotal row 1 ==
      computedExceptionalScaledTotal₀ row 1) &&
    (claimedGroupTotal row 1 ==
      commonGroupTotal₀ 0 1 (rawGroupKey row).1 (rawGroupKey row).2 +
        Rat.ofInt (claimedExceptionalScaledTotal row 1) /
          Rat.ofInt
            (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int))) = true at h1
  change ((claimedExceptionalScaledTotal row 2 ==
      computedExceptionalScaledTotal₀ row 2) &&
    (claimedGroupTotal row 2 ==
      commonGroupTotal₀ 1 1 (rawGroupKey row).1 (rawGroupKey row).2 +
        Rat.ofInt (claimedExceptionalScaledTotal row 2) /
          Rat.ofInt
            (Atlas43RawGroupWitnessData.exceptionalDenominator₀ : Int))) = true at h2
  change ((claimedExceptionalScaledTotal row 3 ==
      computedExceptionalScaledTotal₁ row) &&
    (claimedGroupTotal row 3 ==
      commonGroupTotal₁ (rawGroupKey row).1 (rawGroupKey row).2 +
        Rat.ofInt (claimedExceptionalScaledTotal row 3) /
          Rat.ofInt
            (Atlas43RawGroupWitnessData.exceptionalDenominator₁ : Int))) = true at h3
  simp only [Bool.and_eq_true, beq_iff_eq] at h0 h1 h2 h3
  rcases h0 with ⟨h0scaled, h0⟩
  rcases h1 with ⟨h1scaled, h1⟩
  rcases h2 with ⟨h2scaled, h2⟩
  rcases h3 with ⟨h3scaled, h3⟩
  rw [h0scaled, ← exceptional_group_total₀_zero_zero_eq_scaled row] at h0
  rw [h1scaled, ← exceptional_group_total₀_zero_one_eq_scaled row] at h1
  rw [h2scaled, ← exceptional_group_total₀_one_one_eq_scaled row] at h2
  rw [h3scaled, ← exceptional_group_total₁_eq_scaled row] at h3
  simpa [rawGroupArithmeticValid, computedGroupTotal₀,
    computedGroupTotal₁] using ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩

lemma claimed_group_slot₀_exact (row : Fin 33) :
    claimedGroupTotal row 0 =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        fullRatGram₀ (extendedIndex 0 pair.1) (extendedIndex 0 pair.2)).sum := by
  have h := all_raw_group_arithmetic_valid row
  simp only [rawGroupArithmeticValid, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1.1]
  exact computed_group_total₀_eq_full_sum 0 0 _ _

lemma claimed_group_slot₁_exact (row : Fin 33) :
    claimedGroupTotal row 1 =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        fullRatGram₀ (extendedIndex 0 pair.1) (extendedIndex 1 pair.2)).sum := by
  have h := all_raw_group_arithmetic_valid row
  simp only [rawGroupArithmeticValid, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1.2]
  exact computed_group_total₀_eq_full_sum 0 1 _ _

lemma claimed_group_slot₂_exact (row : Fin 33) :
    claimedGroupTotal row 2 =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        fullRatGram₀ (extendedIndex 1 pair.1) (extendedIndex 1 pair.2)).sum := by
  have h := all_raw_group_arithmetic_valid row
  simp only [rawGroupArithmeticValid, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.2]
  exact computed_group_total₀_eq_full_sum 1 1 _ _

lemma claimed_group_slot₃_exact (row : Fin 33) :
    claimedGroupTotal row 3 =
      ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
        fullRatGram₁ pair.1 pair.2).sum := by
  have h := all_raw_group_arithmetic_valid row
  simp only [rawGroupArithmeticValid, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.2]
  exact computed_group_total₁_eq_full_sum _ _

lemma grouped_slot₀_sum (q : Nat → Nat → Real) :
    (∑ row : Fin 33, (claimedGroupTotal row 0 : Real) *
      q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₀ (extendedIndex 0 a) (extendedIndex 0 b) : Real) *
          q (coreId a b) (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) := by
  calc
    _ = ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          (fullRatGram₀ (extendedIndex 0 pair.1)
            (extendedIndex 0 pair.2) : Real)).sum *
              q (rawGroupKey row).1 (rawGroupKey row).2 := by
      apply Finset.sum_congr rfl
      intro row _
      rw [claimed_group_slot₀_exact]
      push_cast
      rw [List.map_map]
      rfl
    _ = _ := sum_groups_mul_key
      (fun pair ↦ (fullRatGram₀ (extendedIndex 0 pair.1)
        (extendedIndex 0 pair.2) : Real)) q

lemma grouped_slot₁_sum (q : Nat → Nat → Real) :
    (∑ row : Fin 33, (claimedGroupTotal row 1 : Real) *
      q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₀ (extendedIndex 0 a) (extendedIndex 1 b) : Real) *
          q (coreId a b) (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) := by
  calc
    _ = ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          (fullRatGram₀ (extendedIndex 0 pair.1)
            (extendedIndex 1 pair.2) : Real)).sum *
              q (rawGroupKey row).1 (rawGroupKey row).2 := by
      apply Finset.sum_congr rfl
      intro row _
      rw [claimed_group_slot₁_exact]
      push_cast
      rw [List.map_map]
      rfl
    _ = _ := sum_groups_mul_key
      (fun pair ↦ (fullRatGram₀ (extendedIndex 0 pair.1)
        (extendedIndex 1 pair.2) : Real)) q

lemma grouped_slot₂_sum (q : Nat → Nat → Real) :
    (∑ row : Fin 33, (claimedGroupTotal row 2 : Real) *
      q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₀ (extendedIndex 1 a) (extendedIndex 1 b) : Real) *
          q (coreId a b) (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) := by
  calc
    _ = ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          (fullRatGram₀ (extendedIndex 1 pair.1)
            (extendedIndex 1 pair.2) : Real)).sum *
              q (rawGroupKey row).1 (rawGroupKey row).2 := by
      apply Finset.sum_congr rfl
      intro row _
      rw [claimed_group_slot₂_exact]
      push_cast
      rw [List.map_map]
      rfl
    _ = _ := sum_groups_mul_key
      (fun pair ↦ (fullRatGram₀ (extendedIndex 1 pair.1)
        (extendedIndex 1 pair.2) : Real)) q

lemma grouped_slot₃_sum (q : Nat → Nat → Real) :
    (∑ row : Fin 33, (claimedGroupTotal row 3 : Real) *
      q (rawGroupKey row).1 (rawGroupKey row).2) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₁ a b : Real) *
          q (coreId a b) (isolatedEdgeCountFin5 (gluedOrdinaryGraph a b)) := by
  calc
    _ = ∑ row : Fin 33,
        ((rawGroupPairs (rawGroupKey row).1 (rawGroupKey row).2).map fun pair ↦
          (fullRatGram₁ pair.1 pair.2 : Real)).sum *
            q (rawGroupKey row).1 (rawGroupKey row).2 := by
      apply Finset.sum_congr rfl
      intro row _
      rw [claimed_group_slot₃_exact]
      push_cast
      rw [List.map_map]
      rfl
    _ = _ := sum_groups_mul_key
      (fun pair ↦ (fullRatGram₁ pair.1 pair.2 : Real)) q

lemma sum_comm_three {R α β γ : Type*} [AddCommMonoid R]
    [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

lemma sum_comm_four {R α β γ δ : Type*} [AddCommMonoid R]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

lemma identity_quadratic_expand {R κ ι : Type*} [CommRing R]
    [Fintype κ] [Fintype ι] (F : κ → ι → R) (v : κ → R) :
    (∑ i, (∑ a, F a i * v a) ^ 2) =
      ∑ a, ∑ b, (∑ i, F a i * F b i) * v a * v b := by
  calc
    (∑ i, (∑ a, F a i * v a) ^ 2) =
        ∑ i, ∑ b, ∑ a, (F a i * v a) * (F b i * v b) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ b, ∑ a, ∑ i, (F a i * v a) * (F b i * v b) :=
      sum_comm_three (α := ι) (β := κ) (γ := κ)
        (fun i b a ↦ (F a i * v a) * (F b i * v b))
    _ = ∑ a, ∑ b, ∑ i, (F a i * v a) * (F b i * v b) := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, F a i * F b i) * v a * v b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma correction_quadratic_expand {R κ ι : Type*} [CommRing R]
    [Fintype κ] [Fintype ι] (F : κ → ι → R)
    (C : ι → ι → R) (v : κ → R) :
    (∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
      ∑ b, F b j * v b) =
      ∑ a, ∑ b, (∑ j, (∑ i, F a i * C i j) * F b j) * v a * v b := by
  calc
    (∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
      ∑ b, F b j * v b) =
        ∑ i, ∑ j, ∑ b, ∑ a,
          (F a i * v a) * C i j * (F b j * v b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ b, ∑ a, ∑ i, ∑ j,
        (F a i * v a) * C i j * (F b j * v b) :=
      sum_comm_four (α := ι) (β := ι) (γ := κ) (δ := κ)
        (fun i j b a ↦ (F a i * v a) * C i j * (F b j * v b))
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        (F a i * v a) * C i j * (F b j * v b) := by rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ j, (∑ i, F a i * C i j) * F b j) * v a * v b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

def expandedGramEntry {R κ ι : Type*} [CommRing R]
    [Fintype ι] (F : κ → ι → R) (C : ι → ι → R)
    (a b : κ) : R :=
  ∑ j, (F a j + ∑ i, F a i * C i j) * F b j

lemma quadratic_eq_expanded_entries {R κ ι : Type*} [CommRing R]
    [Fintype κ] [Fintype ι] (F : κ → ι → R)
    (C : ι → ι → R) (v : κ → R) :
    (∑ i, (∑ a, F a i * v a) ^ 2) +
      ∑ i, ∑ j, (∑ a, F a i * v a) * C i j *
        ∑ a, F a j * v a =
      ∑ a, ∑ b, expandedGramEntry F C a b * v a * v b := by
  unfold expandedGramEntry
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (fun x y ↦ x + y)
    (identity_quadratic_expand F v) (correction_quadratic_expand F C v)

lemma expanded_gram₀_entry_eq (a b : Fin 128) :
    expandedGramEntry F₀ (fun i j ↦ (C₀ i j : Real)) a b =
      (fullRatGram₀ a b : Real) := by
  unfold expandedGramEntry fullRatGram₀ F₀
  simp only [Rat.ofInt_eq_cast]
  push_cast
  rfl

lemma expanded_gram₁_entry_eq (a b : Fin 64) :
    expandedGramEntry F₁ (fun i j ↦ (C₁ i j : Real)) a b =
      (fullRatGram₁ a b : Real) := by
  unfold expandedGramEntry fullRatGram₁ F₁
  simp only [Rat.ofInt_eq_cast]
  push_cast
  rfl

lemma factored_gram₀_eq_entry_sum (v : Fin 128 → Real) :
    factoredRatGramForm F₀ C₀ v =
      ∑ a, ∑ b, (fullRatGram₀ a b : Real) * v a * v b := by
  rw [show factoredRatGramForm F₀ C₀ v =
      (∑ i, (∑ a, F₀ a i * v a) ^ 2) +
        ∑ i, ∑ j, (∑ a, F₀ a i * v a) * (C₀ i j : Real) *
          ∑ a, F₀ a j * v a by rfl]
  rw [quadratic_eq_expanded_entries]
  simp_rw [expanded_gram₀_entry_eq]

lemma factored_gram₁_eq_entry_sum (v : Fin 64 → Real) :
    factoredRatGramForm F₁ C₁ v =
      ∑ a, ∑ b, (fullRatGram₁ a b : Real) * v a * v b := by
  rw [show factoredRatGramForm F₁ C₁ v =
      (∑ i, (∑ a, F₁ a i * v a) ^ 2) +
        ∑ i, ∑ j, (∑ a, F₁ a i * v a) * (C₁ i j : Real) *
          ∑ a, F₁ a j * v a by rfl]
  rw [quadratic_eq_expanded_entries]
  simp_rw [expanded_gram₁_entry_eq]

lemma finProdFinEquiv_eq_extendedIndex (block : Fin 2) (a : Fin 64) :
    finProdFinEquiv (block, a) = extendedIndex block a := by
  apply Fin.ext
  simp [finProdFinEquiv, extendedIndex, Nat.add_comm]
  omega

lemma sum_fin128_eq_blocks {R : Type*} [AddCommMonoid R] (f : Fin 128 → R) :
    (∑ a : Fin 128, f a) =
      ∑ block : Fin 2, ∑ a : Fin 64, f (extendedIndex block a) := by
  rw [← (finProdFinEquiv : Fin 2 × Fin 64 ≃ Fin 128).sum_comp]
  simp only [Fintype.sum_prod_type, finProdFinEquiv_eq_extendedIndex]

lemma extendedFlagVector_extendedIndex
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (W : Graphon Ω μ) (x : Fin 3 → Ω)
    (A : Finset (Sym2 (Fin 3))) (u : Real) (block : Fin 2) (a : Fin 64) :
    extendedFlagVector W x A u (extendedIndex block a) =
      u ^ block.1 * flagVector W x A a := by
  fin_cases block <;> simp [extendedFlagVector, extendedIndex]

lemma weighted_average_quadratic {R σ κ : Type*} [CommRing R] [Fintype κ]
    (samples : Finset σ) (weight : σ → R) (matrix : κ → κ → R)
    (vector : σ → κ → R) :
    (∑ s ∈ samples, weight s *
      ∑ a, ∑ b, matrix a b * vector s a * vector s b) =
      ∑ a, ∑ b, matrix a b *
        ∑ s ∈ samples, weight s * vector s a * vector s b := by
  calc
    (∑ s ∈ samples, weight s *
      ∑ a, ∑ b, matrix a b * vector s a * vector s b) =
        ∑ s ∈ samples, ∑ a, ∑ b,
          weight s * matrix a b * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ s ∈ samples, ∑ b,
        weight s * matrix a b * vector s a * vector s b := by
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ s ∈ samples,
        weight s * matrix a b * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, matrix a b *
        ∑ s ∈ samples, weight s * vector s a * vector s b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

lemma bernoulli_flagVector_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (x : Fin 3 → Ω) (a b : Fin 64) :
    (∑ A ∈ (Finset.univ : Finset (Sym2 (Fin 3))).powerset,
      bernoulliWeight (fun e ↦ edgeValue W x e) A *
        flagVector W x A a * flagVector W x A b) =
      gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
        (flagBranchNeighbors a) (flagBranchNeighbors b) := by
  simpa [flagVector] using bernoulli_rootedFlag_product W x
    (flagLabelEdges a) (flagLabelEdges b)
    (flagBranchNeighbors a) (flagBranchNeighbors b)

lemma bernoulli_extendedFlagVector_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (x : Fin 3 → Ω) (u : Real)
    (block₀ block₁ : Fin 2) (a b : Fin 64) :
    (∑ A ∈ (Finset.univ : Finset (Sym2 (Fin 3))).powerset,
      bernoulliWeight (fun e ↦ edgeValue W x e) A *
        extendedFlagVector W x A u (extendedIndex block₀ a) *
          extendedFlagVector W x A u (extendedIndex block₁ b)) =
      u ^ (block₀.1 + block₁.1) *
        gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
          (flagBranchNeighbors a) (flagBranchNeighbors b) := by
  simp_rw [extendedFlagVector_extendedIndex]
  rw [pow_add]
  rw [← bernoulli_flagVector_product W x a b]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

lemma averagedGram₀_eq_entry_kernels
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (u : Real) (x : Fin 3 → Ω) :
    averagedGram₀ W u x =
      ∑ block₀ : Fin 2, ∑ a : Fin 64,
        ∑ block₁ : Fin 2, ∑ b : Fin 64,
          (fullRatGram₀ (extendedIndex block₀ a)
              (extendedIndex block₁ b) : Real) *
            u ^ (block₀.1 + block₁.1) *
              gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
                (flagBranchNeighbors a) (flagBranchNeighbors b) := by
  unfold averagedGram₀
  simp_rw [factored_gram₀_eq_entry_sum]
  rw [weighted_average_quadratic]
  rw [sum_fin128_eq_blocks]
  apply Finset.sum_congr rfl
  intro block₀ _
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_fin128_eq_blocks]
  apply Finset.sum_congr rfl
  intro block₁ _
  apply Finset.sum_congr rfl
  intro b _
  rw [bernoulli_extendedFlagVector_product]
  ring

lemma averagedGram₁_eq_entry_kernels
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (x : Fin 3 → Ω) :
    averagedGram₁ W x =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₁ a b : Real) *
          gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
            (flagBranchNeighbors a) (flagBranchNeighbors b) := by
  unfold averagedGram₁
  simp_rw [factored_gram₁_eq_entry_sum]
  rw [weighted_average_quadratic]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [bernoulli_flagVector_product]

lemma integrable_rootedGluedKernel
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (L : SimpleGraph (Fin 3)) [DecidableRel L.Adj]
    (N₀ N₁ : Finset (Fin 3)) (W : Graphon Ω μ) :
    MeasureTheory.Integrable (rootedGluedKernel L N₀ N₁ W)
      (assignmentMeasure (Fin 3) μ) := by
  have h := (integrable_splitGluedFlagKernel L N₀ N₁ W).integral_prod_left
  rw [show rootedGluedKernel L N₀ N₁ W =
      (fun x ↦ ∫ y, splitGluedFlagKernel L N₀ N₁ W (x, y)
        ∂(assignmentMeasure (Fin 2) μ)) by
    funext x
    simp only [rootedGluedKernel, splitGluedFlagKernel]
    rw [MeasureTheory.integral_const_mul,
      integral_two_rootedBranchMonomial W x N₀ N₁]]
  exact h

lemma integrable_gluedFlagKernel
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (a b : Fin 64) :
    MeasureTheory.Integrable
      (fun x ↦ gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
        (flagBranchNeighbors a) (flagBranchNeighbors b))
      (assignmentMeasure (Fin 3) μ) := by
  rw [show (fun x ↦ gluedFlagKernel W x (flagLabelEdges a) (flagLabelEdges b)
      (flagBranchNeighbors a) (flagBranchNeighbors b)) =
      rootedGluedKernel (combinedLabelGraph a b)
        (flagBranchNeighbors a) (flagBranchNeighbors b) W by
    funext x
    exact gluedFlagKernel_eq_rootedGluedKernel W x a b]
  exact integrable_rootedGluedKernel (combinedLabelGraph a b)
    (flagBranchNeighbors a) (flagBranchNeighbors b) W

lemma integrable_fintype_sum
    {Ω R ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R]
    [Fintype ι] {μ : MeasureTheory.Measure Ω} (f : ι → Ω → R)
    (hf : ∀ i, MeasureTheory.Integrable (f i) μ) :
    MeasureTheory.Integrable (fun x ↦ ∑ i, f i x) μ :=
  MeasureTheory.integrable_finsetSum Finset.univ (fun i _ ↦ hf i)

lemma integral_fintype_sum
    {Ω R ι : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R]
    [NormedSpace Real R] [Fintype ι] {μ : MeasureTheory.Measure Ω}
    (f : ι → Ω → R) (hf : ∀ i, MeasureTheory.Integrable (f i) μ) :
    (∫ x, ∑ i, f i x ∂μ) = ∑ i, ∫ x, f i x ∂μ := by
  simpa using MeasureTheory.integral_finsetSum Finset.univ (fun i _ ↦ hf i)

lemma integral_fintype_sum_four
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → Ω → Real)
    (hf : ∀ a b c d, MeasureTheory.Integrable (f a b c d) μ) :
    (∫ x, ∑ a, ∑ b, ∑ c, ∑ d, f a b c d x ∂μ) =
      ∑ a, ∑ b, ∑ c, ∑ d, ∫ x, f a b c d x ∂μ := by
  rw [integral_fintype_sum _ (fun a ↦ integrable_fintype_sum _ fun b ↦
    integrable_fintype_sum _ fun c ↦ integrable_fintype_sum _ fun d ↦ hf a b c d)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_fintype_sum _ (fun b ↦ integrable_fintype_sum _ fun c ↦
    integrable_fintype_sum _ fun d ↦ hf a b c d)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_fintype_sum _ (fun c ↦
    integrable_fintype_sum _ fun d ↦ hf a b c d)]
  apply Finset.sum_congr rfl
  intro c _
  rw [integral_fintype_sum _ (hf a b c)]

lemma integral_averagedGram₀_eq_density_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (u : Real) :
    (∫ x, averagedGram₀ W u x ∂(assignmentMeasure (Fin 3) μ)) =
      ∑ block₀ : Fin 2, ∑ a : Fin 64,
        ∑ block₁ : Fin 2, ∑ b : Fin 64,
          (fullRatGram₀ (extendedIndex block₀ a)
              (extendedIndex block₁ b) : Real) *
            u ^ (block₀.1 + block₁.1) *
              homDensity (gluedOrdinaryGraph a b) W := by
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun x ↦
    averagedGram₀_eq_entry_kernels W u x)]
  rw [integral_fintype_sum_four]
  · apply Finset.sum_congr rfl
    intro block₀ _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro block₁ _
    apply Finset.sum_congr rfl
    intro b _
    rw [MeasureTheory.integral_const_mul,
      integral_gluedFlagKernel_eq_homDensity]
  · intro block₀ a block₁ b
    exact (integrable_gluedFlagKernel W a b).const_mul
      ((fullRatGram₀ (extendedIndex block₀ a)
        (extendedIndex block₁ b) : Real) * u ^ (block₀.1 + block₁.1))

lemma integral_averagedGram₁_eq_density_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) :
    (∫ x, averagedGram₁ W x ∂(assignmentMeasure (Fin 3) μ)) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₁ a b : Real) * homDensity (gluedOrdinaryGraph a b) W := by
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun x ↦
    averagedGram₁_eq_entry_kernels W x)]
  rw [integral_fintype_sum _ (fun a ↦ integrable_fintype_sum _ fun b ↦
    (integrable_gluedFlagKernel W a b).const_mul (fullRatGram₁ a b : Real))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_fintype_sum _ (fun b ↦
    (integrable_gluedFlagKernel W a b).const_mul (fullRatGram₁ a b : Real))]
  apply Finset.sum_congr rfl
  intro b _
  rw [MeasureTheory.integral_const_mul,
    integral_gluedFlagKernel_eq_homDensity]

lemma homDensity_gluedOrdinaryGraph_symm
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (a b : Fin 64) :
    homDensity (gluedOrdinaryGraph a b) W =
      homDensity (gluedOrdinaryGraph b a) W := by
  rw [← integral_gluedFlagKernel_eq_homDensity W a b,
    ← integral_gluedFlagKernel_eq_homDensity W b a]
  apply MeasureTheory.integral_congr_ae
  exact MeasureTheory.ae_of_all _ fun x ↦ by
    simp only [gluedFlagKernel, Finset.union_comm]
    ring

lemma reversed_block_density_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) :
    (∑ a : Fin 64, ∑ b : Fin 64,
      (fullRatGram₀ (extendedIndex 1 a) (extendedIndex 0 b) : Real) *
        homDensity (gluedOrdinaryGraph a b) W) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        (fullRatGram₀ (extendedIndex 0 a) (extendedIndex 1 b) : Real) *
          homDensity (gluedOrdinaryGraph a b) W := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [fullRatGram₀_symm, homDensity_gluedOrdinaryGraph_symm μ W]

noncomputable def blockDensitySum₀
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (W : Graphon Ω μ) (block₀ block₁ : Fin 2) : Real :=
  ∑ a : Fin 64, ∑ b : Fin 64,
    (fullRatGram₀ (extendedIndex block₀ a)
      (extendedIndex block₁ b) : Real) * homDensity (gluedOrdinaryGraph a b) W

noncomputable def blockDensitySum₁
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (W : Graphon Ω μ) : Real :=
  ∑ a : Fin 64, ∑ b : Fin 64,
    (fullRatGram₁ a b : Real) * homDensity (gluedOrdinaryGraph a b) W

lemma blockDensitySum₀_reversed
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    blockDensitySum₀ W 1 0 = blockDensitySum₀ W 0 1 := by
  unfold blockDensitySum₀
  exact reversed_block_density_sum μ W

lemma integral_averagedGram₀_eq_block_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (u : Real) :
    (∫ x, averagedGram₀ W u x ∂(assignmentMeasure (Fin 3) μ)) =
      blockDensitySum₀ W 0 0 +
        2 * u * blockDensitySum₀ W 0 1 +
          u ^ 2 * blockDensitySum₀ W 1 1 := by
  rw [integral_averagedGram₀_eq_density_sum]
  calc
    (∑ block₀ : Fin 2, ∑ a : Fin 64,
      ∑ block₁ : Fin 2, ∑ b : Fin 64,
        (fullRatGram₀ (extendedIndex block₀ a)
            (extendedIndex block₁ b) : Real) *
          u ^ (block₀.1 + block₁.1) *
            homDensity (gluedOrdinaryGraph a b) W) =
      ∑ block₀ : Fin 2, ∑ block₁ : Fin 2,
        ∑ a : Fin 64, ∑ b : Fin 64,
          (fullRatGram₀ (extendedIndex block₀ a)
              (extendedIndex block₁ b) : Real) *
            u ^ (block₀.1 + block₁.1) *
              homDensity (gluedOrdinaryGraph a b) W := by
        apply Finset.sum_congr rfl
        intro block₀ _
        rw [Finset.sum_comm]
    _ = ∑ block₀ : Fin 2, ∑ block₁ : Fin 2,
        u ^ (block₀.1 + block₁.1) *
          blockDensitySum₀ W block₀ block₁ := by
      apply Finset.sum_congr rfl
      intro block₀ _
      apply Finset.sum_congr rfl
      intro block₁ _
      unfold blockDensitySum₀
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        Nat.zero_add, Nat.add_zero, pow_two]
      rw [blockDensitySum₀_reversed μ W]
      ring

lemma integral_averagedGram₁_eq_blockDensitySum
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    (∫ x, averagedGram₁ W x ∂(assignmentMeasure (Fin 3) μ)) =
      blockDensitySum₁ W := by
  exact integral_averagedGram₁_eq_density_sum μ W

noncomputable def coreDensityWeight
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (W : Graphon Ω μ) (core isolated : Nat) : Real :=
  cliqueDensity 2 W ^ isolated * homDensity (atlasCoreGraph core) W

lemma blockDensitySum₀_zero_zero_eq_grouped
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    blockDensitySum₀ W 0 0 =
      ∑ row : Fin 33, (claimedGroupTotal row 0 : Real) *
        coreDensityWeight W (rawGroupKey row).1 (rawGroupKey row).2 := by
  unfold blockDensitySum₀
  simp_rw [homDensity_gluedOrdinaryGraph_eq_atlasCore Ω μ]
  exact (grouped_slot₀_sum (coreDensityWeight W)).symm

lemma blockDensitySum₀_zero_one_eq_grouped
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    blockDensitySum₀ W 0 1 =
      ∑ row : Fin 33, (claimedGroupTotal row 1 : Real) *
        coreDensityWeight W (rawGroupKey row).1 (rawGroupKey row).2 := by
  unfold blockDensitySum₀
  simp_rw [homDensity_gluedOrdinaryGraph_eq_atlasCore Ω μ]
  exact (grouped_slot₁_sum (coreDensityWeight W)).symm

lemma blockDensitySum₀_one_one_eq_grouped
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    blockDensitySum₀ W 1 1 =
      ∑ row : Fin 33, (claimedGroupTotal row 2 : Real) *
        coreDensityWeight W (rawGroupKey row).1 (rawGroupKey row).2 := by
  unfold blockDensitySum₀
  simp_rw [homDensity_gluedOrdinaryGraph_eq_atlasCore Ω μ]
  exact (grouped_slot₂_sum (coreDensityWeight W)).symm

lemma blockDensitySum₁_eq_grouped
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    blockDensitySum₁ W =
      ∑ row : Fin 33, (claimedGroupTotal row 3 : Real) *
        coreDensityWeight W (rawGroupKey row).1 (rawGroupKey row).2 := by
  unfold blockDensitySum₁
  simp_rw [homDensity_gluedOrdinaryGraph_eq_atlasCore Ω μ]
  exact (grouped_slot₃_sum (coreDensityWeight W)).symm

lemma certificateSOS_eq_grouped
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (W : Graphon Ω μ) (u : Real) :
    certificateSOS W u =
      ∑ row : Fin 33,
        ((claimedGroupTotal row 0 : Real) +
          2 * u * (claimedGroupTotal row 1 : Real) +
          u ^ 2 * (claimedGroupTotal row 2 : Real) +
          u * (1 - u) * (claimedGroupTotal row 3 : Real)) *
            coreDensityWeight W (rawGroupKey row).1 (rawGroupKey row).2 := by
  unfold certificateSOS
  rw [integral_averagedGram₀_eq_block_polynomial μ W u,
    integral_averagedGram₁_eq_blockDensitySum μ W,
    blockDensitySum₀_zero_zero_eq_grouped μ W,
    blockDensitySum₀_zero_one_eq_grouped μ W,
    blockDensitySum₀_one_one_eq_grouped μ W,
    blockDensitySum₁_eq_grouped μ W]
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  ring

lemma raw_group_isolated_le_two (row : Fin 33) : (rawGroupKey row).2 ≤ 2 := by
  have h : ∀ row : Fin 33, (rawGroupKey row).2 ≤ 2 := by
    simpa [rawGroupIsolatedLeTwoValid] using raw_group_isolated_le_two_valid
  exact h row

lemma raw_group_polynomial_eval (row : Fin 33) (u : Real) :
    (((claimedGroupTotal row 0 : Real) +
      2 * u * (claimedGroupTotal row 1 : Real) +
      u ^ 2 * (claimedGroupTotal row 2 : Real) +
      u * (1 - u) * (claimedGroupTotal row 3 : Real)) *
        ((1 + u) / 2) ^ (rawGroupKey row).2) =
      ((List.range 5).map fun degree ↦
        (rawGroupPolynomialCoefficient row degree : Real) * u ^ degree).sum := by
  have hle := raw_group_isolated_le_two row
  have hcases : (rawGroupKey row).2 = 0 ∨ (rawGroupKey row).2 = 1 ∨
      (rawGroupKey row).2 = 2 := by omega
  rcases hcases with h | h | h <;>
    simp [rawGroupPolynomialCoefficient, shiftedHalfPowerCoefficient,
      halfPowerCoefficient, List.range, List.range.loop, h] <;> ring

lemma list_sum_map_range_eq_finset_sum_range
    {R : Type*} [AddCommMonoid R] (f : Nat → R) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

lemma raw_group_core_lt_53 (row : Fin 33) : (rawGroupKey row).1 < 53 := by
  have h : ∀ row : Fin 33, (rawGroupKey row).1 < 53 := by
    simpa [rawGroupCoreLt53Valid] using raw_group_core_lt_53_valid
  exact h row

lemma certificateSOS_eq_row_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    let p := cliqueDensity 2 W
    let u := 2 * p - 1
    certificateSOS W u =
      ∑ row : Fin 33,
        (∑ degree ∈ Finset.range 5,
          (rawGroupPolynomialCoefficient row degree : Real) * u ^ degree) *
            homDensity (atlasCoreGraph (rawGroupKey row).1) W := by
  dsimp only
  rw [certificateSOS_eq_grouped μ]
  apply Finset.sum_congr rfl
  intro row _
  unfold coreDensityWeight
  have hp : (1 + (2 * cliqueDensity 2 W - 1)) / 2 = cliqueDensity 2 W := by ring
  have hpoly := raw_group_polynomial_eval row (2 * cliqueDensity 2 W - 1)
  rw [hp] at hpoly
  calc
    _ = (((claimedGroupTotal row 0 : Real) +
          2 * (2 * cliqueDensity 2 W - 1) * (claimedGroupTotal row 1 : Real) +
          (2 * cliqueDensity 2 W - 1) ^ 2 * (claimedGroupTotal row 2 : Real) +
          (2 * cliqueDensity 2 W - 1) * (1 - (2 * cliqueDensity 2 W - 1)) *
            (claimedGroupTotal row 3 : Real)) *
          cliqueDensity 2 W ^ (rawGroupKey row).2) *
            homDensity (atlasCoreGraph (rawGroupKey row).1) W := by ring
    _ = ((List.range 5).map fun degree ↦
          (rawGroupPolynomialCoefficient row degree : Real) *
            (2 * cliqueDensity 2 W - 1) ^ degree).sum *
          homDensity (atlasCoreGraph (rawGroupKey row).1) W := by rw [hpoly]
    _ = _ := by rw [list_sum_map_range_eq_finset_sum_range]

lemma certificateCoefficient_eq_finset (core degree : Nat) :
    certificateCoefficient core degree =
      ∑ row ∈ Finset.range 33,
        if (rawGroupKey row).1 == core then
          rawGroupPolynomialCoefficient row degree else 0 := by
  unfold certificateCoefficient
  rw [list_sum_map_range_eq_finset_sum_range]

lemma certificateCoefficient_grouping (degree : Nat) (r : Nat → Real) :
    (∑ row ∈ Finset.range 33,
      (rawGroupPolynomialCoefficient row degree : Real) *
        r (rawGroupKey row).1) =
      ∑ core ∈ Finset.range 53,
        (certificateCoefficient core degree : Real) * r core := by
  simp_rw [certificateCoefficient_eq_finset]
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row hrow
  have hrowlt : row < 33 := Finset.mem_range.mp hrow
  have hcore : (rawGroupKey row).1 < 53 :=
    raw_group_core_lt_53 ⟨row, hrowlt⟩
  rw [Finset.sum_eq_single (rawGroupKey row).1]
  · simp
  · intro core hcoremem hne
    have hfalse : ((rawGroupKey row).1 == core) = false := by
      simp [Ne.symm hne]
    simp [hfalse]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hcore)).elim

lemma certificateSOS_eq_core_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    let p := cliqueDensity 2 W
    let u := 2 * p - 1
    certificateSOS W u =
      ∑ degree ∈ Finset.range 5, ∑ core ∈ Finset.range 53,
        (certificateCoefficient core degree : Real) * u ^ degree *
          homDensity (atlasCoreGraph core) W := by
  dsimp only
  rw [certificateSOS_eq_row_polynomial μ W]
  let rowTerm : Nat → Real := fun row ↦
    (∑ degree ∈ Finset.range 5,
      (rawGroupPolynomialCoefficient row degree : Real) *
        (2 * cliqueDensity 2 W - 1) ^ degree) *
          homDensity (atlasCoreGraph (rawGroupKey row).1) W
  change (∑ row : Fin 33, rowTerm row.1) = _
  rw [Fin.sum_univ_eq_sum_range rowTerm]
  dsimp only [rowTerm]
  calc
    (∑ row ∈ Finset.range 33,
      (∑ degree ∈ Finset.range 5,
        (rawGroupPolynomialCoefficient row degree : Real) *
          (2 * cliqueDensity 2 W - 1) ^ degree) *
            homDensity (atlasCoreGraph (rawGroupKey row).1) W) =
      ∑ row ∈ Finset.range 33, ∑ degree ∈ Finset.range 5,
        ((rawGroupPolynomialCoefficient row degree : Real) *
          (2 * cliqueDensity 2 W - 1) ^ degree) *
            homDensity (atlasCoreGraph (rawGroupKey row).1) W := by
        apply Finset.sum_congr rfl
        intro row _
        rw [Finset.sum_mul]
    _ = ∑ degree ∈ Finset.range 5, ∑ row ∈ Finset.range 33,
        ((rawGroupPolynomialCoefficient row degree : Real) *
          (2 * cliqueDensity 2 W - 1) ^ degree) *
            homDensity (atlasCoreGraph (rawGroupKey row).1) W := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro degree _
      calc
        (∑ row ∈ Finset.range 33,
          ((rawGroupPolynomialCoefficient row degree : Real) *
            (2 * cliqueDensity 2 W - 1) ^ degree) *
              homDensity (atlasCoreGraph (rawGroupKey row).1) W) =
          ∑ row ∈ Finset.range 33,
            (rawGroupPolynomialCoefficient row degree : Real) *
              ((2 * cliqueDensity 2 W - 1) ^ degree *
                homDensity (atlasCoreGraph (rawGroupKey row).1) W) := by
            apply Finset.sum_congr rfl
            intro row _
            ring
        _ = ∑ core ∈ Finset.range 53,
            (certificateCoefficient core degree : Real) *
              ((2 * cliqueDensity 2 W - 1) ^ degree *
                homDensity (atlasCoreGraph core) W) :=
          certificateCoefficient_grouping degree
            (fun core ↦ (2 * cliqueDensity 2 W - 1) ^ degree *
              homDensity (atlasCoreGraph core) W)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro core _
          ring

lemma coefficient_equation_exact (core degree : Nat)
    (hcore : core < 53) (hdegree : degree < 5) :
    certificateCoefficient core degree = targetCoefficient core degree := by
  have h := all_coefficient_equations_valid
  simp only [allCoefficientEquationsValid, List.all_eq_true] at h
  have hc := h core (List.mem_range.mpr hcore)
  have hd := hc degree (List.mem_range.mpr hdegree)
  simpa only [beq_iff_eq] using hd

lemma certificateSOS_eq_target_core_polynomial
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    let p := cliqueDensity 2 W
    let u := 2 * p - 1
    certificateSOS W u =
      ∑ degree ∈ Finset.range 5, ∑ core ∈ Finset.range 53,
        (targetCoefficient core degree : Real) * u ^ degree *
          homDensity (atlasCoreGraph core) W := by
  dsimp only
  rw [certificateSOS_eq_core_polynomial μ W]
  apply Finset.sum_congr rfl
  intro degree hdegree
  apply Finset.sum_congr rfl
  intro core hcore
  rw [coefficient_equation_exact core degree
    (Finset.mem_range.mp hcore) (Finset.mem_range.mp hdegree)]

lemma atlasCoreGraph_zero : atlasCoreGraph 0 = (⊥ : SimpleGraph (Fin 5)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

lemma homDensity_atlasCore_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    homDensity (atlasCoreGraph 0) W = 1 := by
  simpa only [atlasCoreGraph_zero] using homDensity_bot_fin 5 W

lemma target_core_sum_degree_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) (u : Real) :
    (∑ core ∈ Finset.range 53,
      (targetCoefficient core 0 : Real) * u ^ 0 *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 * homDensity (atlasCoreGraph 43) W := by
  rw [Finset.sum_eq_single 43]
  · norm_num [targetCoefficient]
  · intro core _ hne
    simp [targetCoefficient, hne]
  · norm_num

lemma target_core_sum_degree_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) (u : Real) :
    (∑ core ∈ Finset.range 53,
      (targetCoefficient core 1 : Real) * u ^ 1 *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 * (-1 / 8 : Real) * u := by
  rw [Finset.sum_eq_single 0]
  · rw [homDensity_atlasCore_zero]
    norm_num [targetCoefficient]
  · intro core _ hne
    simp [targetCoefficient, hne]
  · norm_num

lemma target_core_sum_degree_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) (u : Real) :
    (∑ core ∈ Finset.range 53,
      (targetCoefficient core 2 : Real) * u ^ 2 *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 * (-1 / 8 : Real) * u ^ 2 := by
  rw [Finset.sum_eq_single 0]
  · rw [homDensity_atlasCore_zero]
    norm_num [targetCoefficient]
  · intro core _ hne
    simp [targetCoefficient, hne]
  · norm_num

lemma target_core_sum_degree_three
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) (u : Real) :
    (∑ core ∈ Finset.range 53,
      (targetCoefficient core 3 : Real) * u ^ 3 *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 * (-3 / 8 : Real) * u ^ 3 := by
  rw [Finset.sum_eq_single 0]
  · rw [homDensity_atlasCore_zero]
    norm_num [targetCoefficient]
  · intro core _ hne
    simp [targetCoefficient, hne]
  · norm_num

lemma target_core_sum_degree_four
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) (u : Real) :
    (∑ core ∈ Finset.range 53,
      (targetCoefficient core 4 : Real) * u ^ 4 *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 * (-3 / 8 : Real) * u ^ 4 := by
  rw [Finset.sum_eq_single 0]
  · rw [homDensity_atlasCore_zero]
    norm_num [targetCoefficient]
  · intro core _ hne
    simp [targetCoefficient, hne]
  · norm_num

lemma target_core_polynomial_eq_certificate_target
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    let p := cliqueDensity 2 W
    let u := 2 * p - 1
    (∑ degree ∈ Finset.range 5, ∑ core ∈ Finset.range 53,
      (targetCoefficient core degree : Real) * u ^ degree *
        homDensity (atlasCoreGraph core) W) =
      (factorDenominator : Real) ^ 2 *
        (homDensity houseGraph W - houseTarget p) := by
  dsimp only
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  rw [target_core_sum_degree_zero W, target_core_sum_degree_one W,
    target_core_sum_degree_two W, target_core_sum_degree_three W,
    target_core_sum_degree_four W]
  rw [← homDensity_house_eq_atlasCore Ω μ W]
  unfold houseTarget
  ring

theorem certificate_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    certificateSOS W (2 * cliqueDensity 2 W - 1) =
      (factorDenominator : Real) ^ 2 *
        (homDensity houseGraph W - houseTarget (cliqueDensity 2 W)) := by
  rw [certificateSOS_eq_target_core_polynomial μ W]
  exact target_core_polynomial_eq_certificate_target μ W

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
