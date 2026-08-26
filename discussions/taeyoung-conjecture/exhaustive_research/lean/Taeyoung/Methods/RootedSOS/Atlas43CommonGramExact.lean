import Taeyoung.Methods.RootedSOS.Atlas43CommonGramChecks

/-!
# Exact common Gram identities for the Atlas 43 certificate

The generated witness stores bounded positional encodings of
`K = F (I + C)` and `G = K Fᵀ`.  The row modules kernel-check those compact
encodings.  This file decodes them and proves the corresponding entrywise
rational identities used by the certificate proof.
-/

namespace Taeyoung.Methods.RootedSOS.Atlas43Coefficients

open Taeyoung.Methods.RootedSOS.Atlas43PSD
open Taeyoung.Methods.RootedSOS.Atlas43GramWitnessData

set_option maxRecDepth 100000

private lemma hall₀ : ∀ row : Fin 128, block₀WitnessRowValid row = true :=
  all_block0_witness_rows_valid

private lemma hall₁ : ∀ row : Fin 64, block₁WitnessRowValid row = true :=
  all_block1_witness_rows_valid

private lemma hformulas : arithmeticBoundFormulasValid = true :=
  arithmetic_bound_formulas_valid

lemma intermediate₀_encoding_valid (a : Fin 128) :
    intermediate₀EncodingValid a = true := by
  have h := hall₀ a
  simp only [block₀WitnessRowValid, Bool.and_eq_true] at h
  aesop

lemma gram₀_encoding_valid (a : Fin 128) : gram₀EncodingValid a = true := by
  have h := hall₀ a
  simp only [block₀WitnessRowValid, Bool.and_eq_true] at h
  aesop

lemma factor₀_bound (a : Fin 128) (j : Fin 107) :
    (F₀Int a j).natAbs ≤ factor0Bound := by
  have h := hall₀ a
  simp only [block₀WitnessRowValid, block₀BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma intermediate₀_claim_bound (a : Fin 128) (j : Fin 107) :
    (claimedIntermediate₀Scaled a j).natAbs ≤ intermediate0Bound := by
  have h := hall₀ a
  simp only [block₀WitnessRowValid, block₀BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma gram₀_claim_bound (a b : Fin 128) :
    (claimedCommonGram₀Scaled a b).natAbs ≤ gram0Bound := by
  have h := hall₀ a
  simp only [block₀WitnessRowValid, block₀BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma common_c₀_claim_bound (i j : Fin 107) :
    (claimedCommonC₀Scaled i j).natAbs ≤ commonCorrection0ScaledBound := by
  let row : Fin 128 := ⟨i.1, by omega⟩
  have h := hall₀ row
  simp only [block₀WitnessRowValid, block₀BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  have hi : row.1 < 107 := by dsimp [row]; omega
  simp only [dif_pos hi, decide_eq_true_eq] at h
  have hc := h.1.1.1.2 j
  simpa [row] using hc

lemma common_c₀_row_valid (i : Fin 107) : commonC₀RowValid i = true := by
  let row : Fin 128 := ⟨i.1, by omega⟩
  have h := hall₀ row
  simp only [block₀WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 107 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.1.1
  simpa [row] using hc

lemma common_c₀_rational_entry_valid (i j : Fin 107) :
    commonC₀RationalEntryValid i j = true := by
  have h := common_c₀_row_valid i
  simp only [commonC₀RowValid, List.all_eq_true] at h
  exact h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

lemma correction₀_encoding_valid (i : Fin 107) :
    correction₀EncodingValid i = true := by
  let row : Fin 128 := ⟨i.1, by omega⟩
  have h := hall₀ row
  simp only [block₀WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 107 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.1.2
  simpa [row] using hc

lemma factor₀_column_encoding_valid (i : Fin 107) :
    factor₀GramColumnEncodingValid i = true := by
  let row : Fin 128 := ⟨i.1, by omega⟩
  have h := hall₀ row
  simp only [block₀WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 107 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.2
  simpa [row] using hc

lemma intermediate₀_bound_formula :
    intermediate0Bound = commonCorrectionDenominator * factor0Bound +
      107 * factor0Bound * commonCorrection0ScaledBound := by
  have h := hformulas
  simp only [arithmeticBoundFormulasValid, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h.1.1.1

lemma expected_intermediate₀_bound (a : Fin 128) (j : Fin 107) :
    (expectedIntermediate₀Scaled a j).natAbs ≤ intermediate0Bound := by
  have h := matrix_product_entry_bound commonCorrectionDenominator factor0Bound
    commonCorrection0ScaledBound (F₀Int a j) (fun i ↦ F₀Int a i)
      (fun i ↦ claimedCommonC₀Scaled i j)
      (factor₀_bound a j) (factor₀_bound a) (fun i ↦ common_c₀_claim_bound i j)
  rw [intermediate₀_bound_formula]
  simpa [expectedIntermediate₀Scaled] using h

lemma correction₀_encoding_eq (i : Fin 107) :
    commonCorrection0EncodedRows[i.1]?.getD 0 =
      ∑ j : Fin 107, claimedCommonC₀Scaled i j *
        (intermediateBase₀ : Int) ^ j.1 := by
  have h := correction₀_encoding_valid i
  simpa only [correction₀EncodingValid, beq_iff_eq] using h

lemma intermediate₀_encoding_eq (a : Fin 128) :
    shiftedEncoding intermediateBase₀ intermediate0Bound
        (List.ofFn fun j : Fin 107 ↦ claimedIntermediate₀Scaled a j) =
      shiftedEncoding intermediateBase₀ intermediate0Bound
        (List.ofFn fun j : Fin 107 ↦ expectedIntermediate₀Scaled a j) := by
  have hvalid := intermediate₀_encoding_valid a
  simp only [intermediate₀EncodingValid, beq_iff_eq] at hvalid
  rw [shiftedEncoding_ofFn_eq_sum _ (expected_intermediate₀_bound a)]
  simp only [expectedIntermediate₀Scaled]
  rw [encoded_matrix_product intermediateBase₀ intermediate0Bound
    (fun j : Fin 107 ↦ F₀Int a j * commonCorrectionDenominator)
    (fun i : Fin 107 ↦ F₀Int a i) claimedCommonC₀Scaled]
  simp_rw [← correction₀_encoding_eq]
  rw [hvalid]
  rw [Finset.mul_sum]
  ring_nf
  rw [show (∑ x : Fin 107, (commonCorrectionDenominator : Int) * F₀Int a x *
      (intermediateBase₀ : Int) ^ x.1) =
      ∑ x : Fin 107, (commonCorrectionDenominator : Int) *
        (intermediateBase₀ : Int) ^ x.1 * F₀Int a x by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  abel

lemma intermediate₀_entries_exact (a : Fin 128) (j : Fin 107) :
    claimedIntermediate₀Scaled a j = expectedIntermediate₀Scaled a j := by
  have hfun := shiftedEncoding_injective_of_bound
    (n := 107) (base := intermediateBase₀) (bound := intermediate0Bound)
    (by unfold intermediate0Bound; omega)
    (by rfl)
    (fun j ↦ claimedIntermediate₀Scaled a j)
    (fun j ↦ expectedIntermediate₀Scaled a j)
    (intermediate₀_claim_bound a) (expected_intermediate₀_bound a)
    (intermediate₀_encoding_eq a)
  exact congrFun hfun j

lemma gram₀_bound_formula :
    gram0Bound = 107 * intermediate0Bound * factor0Bound := by
  have h := hformulas
  simp only [arithmeticBoundFormulasValid, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h.1.2

def expectedCommonGram₀Scaled (a b : Fin 128) : Int :=
  ∑ j : Fin 107, claimedIntermediate₀Scaled a j * F₀Int b j

lemma expected_common_gram₀_bound (a b : Fin 128) :
    (expectedCommonGram₀Scaled a b).natAbs ≤ gram0Bound := by
  have h := natAbs_sum_le_card_mul_bound
    (fun j : Fin 107 ↦ claimedIntermediate₀Scaled a j * F₀Int b j)
    (intermediate0Bound * factor0Bound)
    (fun j ↦ by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (intermediate₀_claim_bound a j) (factor₀_bound b j))
  rw [gram₀_bound_formula]
  simpa [expectedCommonGram₀Scaled, Nat.mul_assoc] using h

lemma factor₀_column_encoding_eq (j : Fin 107) :
    factor0GramEncodedColumns[j.1]?.getD 0 =
      ∑ b : Fin 128, F₀Int b j * (gramBase₀ : Int) ^ b.1 := by
  have h := factor₀_column_encoding_valid j
  simpa only [factor₀GramColumnEncodingValid, beq_iff_eq] using h

lemma gram₀_encoding_eq (a : Fin 128) :
    shiftedEncoding gramBase₀ gram0Bound
        (List.ofFn fun b : Fin 128 ↦ claimedCommonGram₀Scaled a b) =
      shiftedEncoding gramBase₀ gram0Bound
        (List.ofFn fun b : Fin 128 ↦ expectedCommonGram₀Scaled a b) := by
  have hvalid := gram₀_encoding_valid a
  simp only [gram₀EncodingValid, beq_iff_eq] at hvalid
  rw [shiftedEncoding_ofFn_eq_sum _ (expected_common_gram₀_bound a)]
  simp only [expectedCommonGram₀Scaled]
  have hproduct := encoded_matrix_product gramBase₀ gram0Bound
    (fun _b : Fin 128 ↦ (0 : Int))
    (fun j : Fin 107 ↦ claimedIntermediate₀Scaled a j)
    (fun j b ↦ F₀Int b j)
  simp only [zero_add] at hproduct
  rw [hproduct]
  simp_rw [← factor₀_column_encoding_eq]
  exact hvalid

lemma common_gram₀_entries_exact (a b : Fin 128) :
    claimedCommonGram₀Scaled a b = expectedCommonGram₀Scaled a b := by
  have hfun := shiftedEncoding_injective_of_bound
    (n := 128) (base := gramBase₀) (bound := gram0Bound)
    (by unfold gram0Bound; omega)
    (by rfl)
    (fun b ↦ claimedCommonGram₀Scaled a b)
    (fun b ↦ expectedCommonGram₀Scaled a b)
    (gram₀_claim_bound a) (expected_common_gram₀_bound a)
    (gram₀_encoding_eq a)
  exact congrFun hfun b

lemma common_c₀_eq_scaled (i j : Fin 107) :
    commonC₀ i j =
      Rat.ofInt (claimedCommonC₀Scaled i j) /
        Rat.ofInt commonCorrectionDenominator := by
  have h := common_c₀_rational_entry_valid i j
  simpa only [commonC₀RationalEntryValid, beq_iff_eq] using h

lemma intermediate₀_rational_exact (a : Fin 128) (j : Fin 107) :
    Rat.ofInt (claimedIntermediate₀Scaled a j) /
        Rat.ofInt commonCorrectionDenominator =
      Rat.ofInt (F₀Int a j) +
        ∑ i : Fin 107, Rat.ofInt (F₀Int a i) * commonC₀ i j := by
  rw [intermediate₀_entries_exact, expectedIntermediate₀Scaled]
  simp_rw [common_c₀_eq_scaled]
  simp only [Rat.ofInt_eq_cast]
  push_cast
  have hD : (commonCorrectionDenominator : Rat) ≠ 0 := by
    rw [header_eq.2.1]
    norm_num
  rw [show (∑ x : Fin 107, (F₀Int a x : Rat) *
      ((claimedCommonC₀Scaled x j : Rat) /
        (commonCorrectionDenominator : Rat))) =
      (∑ x : Fin 107, (F₀Int a x : Rat) *
        (claimedCommonC₀Scaled x j : Rat)) /
          (commonCorrectionDenominator : Rat) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    field_simp [hD]]
  field_simp [hD]

def commonRatGram₀ (a b : Fin 128) : Rat :=
  ∑ j : Fin 107,
    (Rat.ofInt (F₀Int a j) +
      ∑ i : Fin 107, Rat.ofInt (F₀Int a i) * commonC₀ i j) *
        Rat.ofInt (F₀Int b j)

lemma common_gram₀_rational_exact (a b : Fin 128) :
    Rat.ofInt (claimedCommonGram₀Scaled a b) /
        Rat.ofInt commonCorrectionDenominator = commonRatGram₀ a b := by
  rw [common_gram₀_entries_exact, expectedCommonGram₀Scaled]
  unfold commonRatGram₀
  calc
    Rat.ofInt (∑ j : Fin 107,
        claimedIntermediate₀Scaled a j * F₀Int b j) /
          Rat.ofInt commonCorrectionDenominator =
        ∑ j : Fin 107,
          (Rat.ofInt (claimedIntermediate₀Scaled a j) /
            Rat.ofInt commonCorrectionDenominator) *
              Rat.ofInt (F₀Int b j) := by
        simp only [Rat.ofInt_eq_cast]
        push_cast
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ j : Fin 107,
        (Rat.ofInt (F₀Int a j) +
          ∑ i : Fin 107, Rat.ofInt (F₀Int a i) * commonC₀ i j) *
            Rat.ofInt (F₀Int b j) := by
      simp_rw [intermediate₀_rational_exact]

lemma intermediate₁_encoding_valid (a : Fin 64) :
    intermediate₁EncodingValid a = true := by
  have h := hall₁ a
  simp only [block₁WitnessRowValid, Bool.and_eq_true] at h
  aesop

lemma gram₁_encoding_valid (a : Fin 64) : gram₁EncodingValid a = true := by
  have h := hall₁ a
  simp only [block₁WitnessRowValid, Bool.and_eq_true] at h
  aesop

lemma factor₁_bound (a : Fin 64) (j : Fin 48) :
    (F₁Int a j).natAbs ≤ factor1Bound := by
  have h := hall₁ a
  simp only [block₁WitnessRowValid, block₁BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma intermediate₁_claim_bound (a : Fin 64) (j : Fin 48) :
    (claimedIntermediate₁Scaled a j).natAbs ≤ intermediate1Bound := by
  have h := hall₁ a
  simp only [block₁WitnessRowValid, block₁BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma gram₁_claim_bound (a b : Fin 64) :
    (claimedCommonGram₁Scaled a b).natAbs ≤ gram1Bound := by
  have h := hall₁ a
  simp only [block₁WitnessRowValid, block₁BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

lemma common_c₁_claim_bound (i j : Fin 48) :
    (claimedCommonC₁Scaled i j).natAbs ≤ commonCorrection1ScaledBound := by
  let row : Fin 64 := ⟨i.1, by omega⟩
  have h := hall₁ row
  simp only [block₁WitnessRowValid, block₁BoundsRowValid,
    Bool.and_eq_true, decide_eq_true_eq] at h
  have hi : row.1 < 48 := by dsimp [row]; omega
  simp only [dif_pos hi, decide_eq_true_eq] at h
  have hc := h.1.1.1.2 j
  simpa [row] using hc

lemma common_c₁_row_valid (i : Fin 48) : commonC₁RowValid i = true := by
  let row : Fin 64 := ⟨i.1, by omega⟩
  have h := hall₁ row
  simp only [block₁WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 48 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.1.1
  simpa [row] using hc

lemma common_c₁_rational_entry_valid (i j : Fin 48) :
    commonC₁RationalEntryValid i j = true := by
  have h := common_c₁_row_valid i
  simp only [commonC₁RowValid, List.all_eq_true] at h
  exact h _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

lemma correction₁_encoding_valid (i : Fin 48) :
    correction₁EncodingValid i = true := by
  let row : Fin 64 := ⟨i.1, by omega⟩
  have h := hall₁ row
  simp only [block₁WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 48 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.1.2
  simpa [row] using hc

lemma factor₁_column_encoding_valid (i : Fin 48) :
    factor₁GramColumnEncodingValid i = true := by
  let row : Fin 64 := ⟨i.1, by omega⟩
  have h := hall₁ row
  simp only [block₁WitnessRowValid, Bool.and_eq_true] at h
  have hi : row.1 < 48 := by dsimp [row]; omega
  simp only [dif_pos hi, Bool.and_eq_true] at h
  have hc := h.2.2
  simpa [row] using hc

lemma intermediate₁_bound_formula :
    intermediate1Bound = commonCorrectionDenominator * factor1Bound +
      48 * factor1Bound * commonCorrection1ScaledBound := by
  have h := hformulas
  simp only [arithmeticBoundFormulasValid, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h.1.1.2

lemma expected_intermediate₁_bound (a : Fin 64) (j : Fin 48) :
    (expectedIntermediate₁Scaled a j).natAbs ≤ intermediate1Bound := by
  have h := matrix_product_entry_bound commonCorrectionDenominator factor1Bound
    commonCorrection1ScaledBound (F₁Int a j) (fun i ↦ F₁Int a i)
      (fun i ↦ claimedCommonC₁Scaled i j)
      (factor₁_bound a j) (factor₁_bound a) (fun i ↦ common_c₁_claim_bound i j)
  rw [intermediate₁_bound_formula]
  simpa [expectedIntermediate₁Scaled] using h

lemma correction₁_encoding_eq (i : Fin 48) :
    commonCorrection1EncodedRows[i.1]?.getD 0 =
      ∑ j : Fin 48, claimedCommonC₁Scaled i j *
        (intermediateBase₁ : Int) ^ j.1 := by
  have h := correction₁_encoding_valid i
  simpa only [correction₁EncodingValid, beq_iff_eq] using h

lemma intermediate₁_encoding_eq (a : Fin 64) :
    shiftedEncoding intermediateBase₁ intermediate1Bound
        (List.ofFn fun j : Fin 48 ↦ claimedIntermediate₁Scaled a j) =
      shiftedEncoding intermediateBase₁ intermediate1Bound
        (List.ofFn fun j : Fin 48 ↦ expectedIntermediate₁Scaled a j) := by
  have hvalid := intermediate₁_encoding_valid a
  simp only [intermediate₁EncodingValid, beq_iff_eq] at hvalid
  rw [shiftedEncoding_ofFn_eq_sum _ (expected_intermediate₁_bound a)]
  simp only [expectedIntermediate₁Scaled]
  rw [encoded_matrix_product intermediateBase₁ intermediate1Bound
    (fun j : Fin 48 ↦ F₁Int a j * commonCorrectionDenominator)
    (fun i : Fin 48 ↦ F₁Int a i) claimedCommonC₁Scaled]
  simp_rw [← correction₁_encoding_eq]
  rw [hvalid]
  rw [Finset.mul_sum]
  ring_nf
  rw [show (∑ x : Fin 48, (commonCorrectionDenominator : Int) * F₁Int a x *
      (intermediateBase₁ : Int) ^ x.1) =
      ∑ x : Fin 48, (commonCorrectionDenominator : Int) *
        (intermediateBase₁ : Int) ^ x.1 * F₁Int a x by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  abel

lemma intermediate₁_entries_exact (a : Fin 64) (j : Fin 48) :
    claimedIntermediate₁Scaled a j = expectedIntermediate₁Scaled a j := by
  have hfun := shiftedEncoding_injective_of_bound
    (n := 48) (base := intermediateBase₁) (bound := intermediate1Bound)
    (by unfold intermediate1Bound; omega)
    (by rfl)
    (fun j ↦ claimedIntermediate₁Scaled a j)
    (fun j ↦ expectedIntermediate₁Scaled a j)
    (intermediate₁_claim_bound a) (expected_intermediate₁_bound a)
    (intermediate₁_encoding_eq a)
  exact congrFun hfun j

lemma gram₁_bound_formula :
    gram1Bound = 48 * intermediate1Bound * factor1Bound := by
  have h := hformulas
  simp only [arithmeticBoundFormulasValid, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h.2

def expectedCommonGram₁Scaled (a b : Fin 64) : Int :=
  ∑ j : Fin 48, claimedIntermediate₁Scaled a j * F₁Int b j

lemma expected_common_gram₁_bound (a b : Fin 64) :
    (expectedCommonGram₁Scaled a b).natAbs ≤ gram1Bound := by
  have h := natAbs_sum_le_card_mul_bound
    (fun j : Fin 48 ↦ claimedIntermediate₁Scaled a j * F₁Int b j)
    (intermediate1Bound * factor1Bound)
    (fun j ↦ by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (intermediate₁_claim_bound a j) (factor₁_bound b j))
  rw [gram₁_bound_formula]
  simpa [expectedCommonGram₁Scaled, Nat.mul_assoc] using h

lemma factor₁_column_encoding_eq (j : Fin 48) :
    factor1GramEncodedColumns[j.1]?.getD 0 =
      ∑ b : Fin 64, F₁Int b j * (gramBase₁ : Int) ^ b.1 := by
  have h := factor₁_column_encoding_valid j
  simpa only [factor₁GramColumnEncodingValid, beq_iff_eq] using h

lemma gram₁_encoding_eq (a : Fin 64) :
    shiftedEncoding gramBase₁ gram1Bound
        (List.ofFn fun b : Fin 64 ↦ claimedCommonGram₁Scaled a b) =
      shiftedEncoding gramBase₁ gram1Bound
        (List.ofFn fun b : Fin 64 ↦ expectedCommonGram₁Scaled a b) := by
  have hvalid := gram₁_encoding_valid a
  simp only [gram₁EncodingValid, beq_iff_eq] at hvalid
  rw [shiftedEncoding_ofFn_eq_sum _ (expected_common_gram₁_bound a)]
  simp only [expectedCommonGram₁Scaled]
  have hproduct := encoded_matrix_product gramBase₁ gram1Bound
    (fun _b : Fin 64 ↦ (0 : Int))
    (fun j : Fin 48 ↦ claimedIntermediate₁Scaled a j)
    (fun j b ↦ F₁Int b j)
  simp only [zero_add] at hproduct
  rw [hproduct]
  simp_rw [← factor₁_column_encoding_eq]
  exact hvalid

lemma common_gram₁_entries_exact (a b : Fin 64) :
    claimedCommonGram₁Scaled a b = expectedCommonGram₁Scaled a b := by
  have hfun := shiftedEncoding_injective_of_bound
    (n := 64) (base := gramBase₁) (bound := gram1Bound)
    (by unfold gram1Bound; omega)
    (by rfl)
    (fun b ↦ claimedCommonGram₁Scaled a b)
    (fun b ↦ expectedCommonGram₁Scaled a b)
    (gram₁_claim_bound a) (expected_common_gram₁_bound a)
    (gram₁_encoding_eq a)
  exact congrFun hfun b

lemma common_c₁_eq_scaled (i j : Fin 48) :
    commonC₁ i j =
      Rat.ofInt (claimedCommonC₁Scaled i j) /
        Rat.ofInt commonCorrectionDenominator := by
  have h := common_c₁_rational_entry_valid i j
  simpa only [commonC₁RationalEntryValid, beq_iff_eq] using h

lemma intermediate₁_rational_exact (a : Fin 64) (j : Fin 48) :
    Rat.ofInt (claimedIntermediate₁Scaled a j) /
        Rat.ofInt commonCorrectionDenominator =
      Rat.ofInt (F₁Int a j) +
        ∑ i : Fin 48, Rat.ofInt (F₁Int a i) * commonC₁ i j := by
  rw [intermediate₁_entries_exact, expectedIntermediate₁Scaled]
  simp_rw [common_c₁_eq_scaled]
  simp only [Rat.ofInt_eq_cast]
  push_cast
  have hD : (commonCorrectionDenominator : Rat) ≠ 0 := by
    rw [header_eq.2.1]
    norm_num
  rw [show (∑ x : Fin 48, (F₁Int a x : Rat) *
      ((claimedCommonC₁Scaled x j : Rat) /
        (commonCorrectionDenominator : Rat))) =
      (∑ x : Fin 48, (F₁Int a x : Rat) *
        (claimedCommonC₁Scaled x j : Rat)) /
          (commonCorrectionDenominator : Rat) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    field_simp [hD]]
  field_simp [hD]

def commonRatGram₁ (a b : Fin 64) : Rat :=
  ∑ j : Fin 48,
    (Rat.ofInt (F₁Int a j) +
      ∑ i : Fin 48, Rat.ofInt (F₁Int a i) * commonC₁ i j) *
        Rat.ofInt (F₁Int b j)

lemma common_gram₁_rational_exact (a b : Fin 64) :
    Rat.ofInt (claimedCommonGram₁Scaled a b) /
        Rat.ofInt commonCorrectionDenominator = commonRatGram₁ a b := by
  rw [common_gram₁_entries_exact, expectedCommonGram₁Scaled]
  unfold commonRatGram₁
  calc
    Rat.ofInt (∑ j : Fin 48,
        claimedIntermediate₁Scaled a j * F₁Int b j) /
          Rat.ofInt commonCorrectionDenominator =
        ∑ j : Fin 48,
          (Rat.ofInt (claimedIntermediate₁Scaled a j) /
            Rat.ofInt commonCorrectionDenominator) *
              Rat.ofInt (F₁Int b j) := by
        simp only [Rat.ofInt_eq_cast]
        push_cast
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ j : Fin 48,
        (Rat.ofInt (F₁Int a j) +
          ∑ i : Fin 48, Rat.ofInt (F₁Int a i) * commonC₁ i j) *
            Rat.ofInt (F₁Int b j) := by
      simp_rw [intermediate₁_rational_exact]

end Taeyoung.Methods.RootedSOS.Atlas43Coefficients
