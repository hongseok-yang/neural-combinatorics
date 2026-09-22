import Taeyoung.Methods.RootedSOS.SparseContraction

/-!
Recover a whole vector of finite counting coefficients from one positional
encoding, then evaluate it at arbitrary real densities. Enumeration and its
graphon interpretation remain separate obligations.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS.Induced

variable {I : Type*} [Fintype I] {n base bound code : Nat}

theorem count_coefficient (g : I → Fin n)
    (hbase : base = 2*bound+1) (hcard : Fintype.card I ≤ bound)
    (hcode : (code : Int) = (bound : Int)*geometricEncoding base n +
      ∑ i, (base : Int)^(g i).1) (j : Fin n) :
    decodeSignedDigit base bound code j = ∑ i, if g i = j then (1 : Int) else 0 := by
  apply listedCoefficient_of_encoding (fun i => g i) (fun _ => (1 : Int)) hbase
  · simpa using hcard
  · simpa only [one_mul] using hcode

theorem count_coefficient_nonneg (g : I → Fin n)
    (hbase : base = 2*bound+1) (hcard : Fintype.card I ≤ bound)
    (hcode : (code : Int) = (bound : Int)*geometricEncoding base n +
      ∑ i, (base : Int)^(g i).1) (j : Fin n) :
    0 ≤ decodeSignedDigit base bound code j := by
  rw [count_coefficient g hbase hcard hcode]
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> decide

theorem count_density_sum (g : I → Fin n)
    (hbase : base = 2*bound+1) (hcard : Fintype.card I ≤ bound)
    (hcode : (code : Int) = (bound : Int)*geometricEncoding base n +
      ∑ i, (base : Int)^(g i).1) (density : Fin n → Real) :
    (∑ i, density (g i)) =
      ∑ j : Fin n, (decodeSignedDigit base bound code j : Real)*density j := by
  have hc (j : Fin n) : (decodeSignedDigit base bound code j : Real) =
      ∑ i, if g i = j then (1 : Real) else 0 := by
    exact_mod_cast count_coefficient g hbase hcard hcode j
  simp_rw [hc, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

end Taeyoung.Methods.RootedSOS.Induced
