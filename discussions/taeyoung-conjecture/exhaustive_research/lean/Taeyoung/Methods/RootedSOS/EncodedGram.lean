import Taeyoung.Methods.RootedSOS.Encoding

/-!
# Decoding bounded exact Gram witnesses

This is the certificate-independent theorem behind the row-local arithmetic
checks.  Positional equality plus explicit digit bounds recovers the exact
entries of `K = F (D I + C)` and `G = K Fᵀ`.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def expectedIntermediate {m n : Nat} (denominator : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (row : Fin m) (col : Fin n) : Int :=
  factor row col * denominator +
    ∑ i : Fin n, factor row i * correction i col

def expectedGram {m n : Nat} (factor : Fin m → Fin n → Int)
    (intermediate : Fin m → Fin n → Int) (row col : Fin m) : Int :=
  ∑ j : Fin n, intermediate row j * factor col j

theorem expectedIntermediate_bound {m n : Nat}
    (denominator factorBound correctionBound intermediateBound : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (hformula : intermediateBound =
      denominator * factorBound + n * factorBound * correctionBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hcorrection : ∀ i j, (correction i j).natAbs ≤ correctionBound)
    (row : Fin m) (col : Fin n) :
    (expectedIntermediate denominator factor correction row col).natAbs ≤
      intermediateBound := by
  have h := matrix_product_entry_bound denominator factorBound correctionBound
    (factor row col) (fun i => factor row i) (fun i => correction i col)
    (hfactor row col) (hfactor row) (fun i => hcorrection i col)
  rw [hformula]
  simpa [expectedIntermediate] using h

theorem intermediate_entries_exact {m n : Nat}
    (denominator factorBound correctionBound intermediateBound base : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (intermediate : Fin m → Fin n → Int) (correctionEncoding : Fin n → Int)
    (hpositive : 0 < intermediateBound)
    (hbase : base = 2 * intermediateBound + 1)
    (hformula : intermediateBound =
      denominator * factorBound + n * factorBound * correctionBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hcorrection : ∀ i j, (correction i j).natAbs ≤ correctionBound)
    (hintermediate : ∀ row col,
      (intermediate row col).natAbs ≤ intermediateBound)
    (hcorrectionEncoding : ∀ i,
      correctionEncoding i =
        ∑ j : Fin n, correction i j * (base : Int) ^ j.1)
    (hintermediateEncoding : ∀ row,
      shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n => intermediate row j) =
        intermediateBound * geometricEncoding base n +
          denominator *
            (∑ j : Fin n, factor row j * (base : Int) ^ j.1) +
          ∑ i : Fin n, factor row i * correctionEncoding i)
    (row : Fin m) (col : Fin n) :
    intermediate row col =
      expectedIntermediate denominator factor correction row col := by
  have hexpected := expectedIntermediate_bound denominator factorBound
    correctionBound intermediateBound factor correction hformula hfactor
    hcorrection row
  have hencoding :
      shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n => intermediate row j) =
        shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n =>
            expectedIntermediate denominator factor correction row j) := by
    rw [shiftedEncoding_ofFn_eq_sum _ hexpected]
    simp only [expectedIntermediate]
    rw [encoded_matrix_product base intermediateBound
      (fun j : Fin n => factor row j * denominator)
      (fun i : Fin n => factor row i) correction]
    simp_rw [← hcorrectionEncoding]
    rw [hintermediateEncoding]
    rw [Finset.mul_sum]
    ring_nf
    rw [show (∑ x : Fin n,
        (denominator : Int) * factor row x * (base : Int) ^ x.1) =
        ∑ x : Fin n,
          (denominator : Int) * (base : Int) ^ x.1 * factor row x by
      apply Finset.sum_congr rfl
      intro x _
      ring]
    abel
  have hfun := shiftedEncoding_injective_of_bound hpositive hbase
    (fun j : Fin n => intermediate row j)
    (fun j : Fin n => expectedIntermediate denominator factor correction row j)
    (hintermediate row) hexpected hencoding
  exact congrFun hfun col

theorem expectedGram_bound {m n : Nat}
    (factorBound intermediateBound gramBound : Nat)
    (factor : Fin m → Fin n → Int) (intermediate : Fin m → Fin n → Int)
    (hformula : gramBound = n * intermediateBound * factorBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hintermediate : ∀ row col,
      (intermediate row col).natAbs ≤ intermediateBound)
    (row col : Fin m) :
    (expectedGram factor intermediate row col).natAbs ≤ gramBound := by
  have h := natAbs_sum_le_card_mul_bound
    (fun j : Fin n => intermediate row j * factor col j)
    (intermediateBound * factorBound)
    (fun j => by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hintermediate row j) (hfactor col j))
  rw [hformula]
  simpa [expectedGram, Nat.mul_assoc] using h

theorem gram_entries_exact {m n : Nat}
    (factorBound intermediateBound gramBound base : Nat)
    (factor : Fin m → Fin n → Int) (intermediate : Fin m → Fin n → Int)
    (gram : Fin m → Fin m → Int) (factorColumnEncoding : Fin n → Int)
    (hpositive : 0 < gramBound)
    (hbase : base = 2 * gramBound + 1)
    (hformula : gramBound = n * intermediateBound * factorBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hintermediate : ∀ row col,
      (intermediate row col).natAbs ≤ intermediateBound)
    (hgram : ∀ row col, (gram row col).natAbs ≤ gramBound)
    (hfactorColumnEncoding : ∀ j,
      factorColumnEncoding j =
        ∑ col : Fin m, factor col j * (base : Int) ^ col.1)
    (hgramEncoding : ∀ row,
      shiftedEncoding base gramBound
          (List.ofFn fun col : Fin m => gram row col) =
        gramBound * geometricEncoding base m +
          ∑ j : Fin n, intermediate row j * factorColumnEncoding j)
    (row col : Fin m) :
    gram row col = expectedGram factor intermediate row col := by
  have hexpected := expectedGram_bound factorBound intermediateBound gramBound
    factor intermediate hformula hfactor hintermediate row
  have hencoding :
      shiftedEncoding base gramBound
          (List.ofFn fun col : Fin m => gram row col) =
        shiftedEncoding base gramBound
          (List.ofFn fun col : Fin m => expectedGram factor intermediate row col) := by
    rw [shiftedEncoding_ofFn_eq_sum _ hexpected]
    simp only [expectedGram]
    have hproduct := encoded_matrix_product base gramBound
      (fun _col : Fin m => (0 : Int))
      (fun j : Fin n => intermediate row j)
      (fun j col => factor col j)
    simp only [zero_add, zero_mul, Finset.sum_const_zero, add_zero] at hproduct
    rw [hproduct]
    simp_rw [← hfactorColumnEncoding]
    exact hgramEncoding row
  have hfun := shiftedEncoding_injective_of_bound hpositive hbase
    (fun col : Fin m => gram row col)
    (fun col : Fin m => expectedGram factor intermediate row col)
    (hgram row) hexpected hencoding
  exact congrFun hfun col

end Taeyoung.Methods.RootedSOS
