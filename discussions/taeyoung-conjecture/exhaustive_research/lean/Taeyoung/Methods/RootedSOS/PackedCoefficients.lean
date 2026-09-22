import Taeyoung.Methods.RootedSOS.PackedMatrix

/-! Exact recovery of graph-group coefficients from one bounded positional
encoding. The bounds rule out carries between different graph groups. -/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def decodeSignedDigit (base bound code index : Nat) : Int :=
  ((code / base ^ index % base : Nat) : Int) - bound

theorem decodeSignedDigit_bound {base bound : Nat}
    (hbase : base = 2 * bound + 1) (code index : Nat) :
    (decodeSignedDigit base bound code index).natAbs ≤ bound := by
  have hb : 0 < base := by omega
  have hm := Nat.mod_lt (code / base ^ index) hb
  have ha : |decodeSignedDigit base bound code index| ≤ (bound : Int) := by
    rw [abs_le]
    dsimp only [decodeSignedDigit]
    constructor <;> omega
  rw [← Int.natCast_natAbs] at ha
  exact_mod_cast ha

private theorem head_drop_eq_getD (xs : List Nat) (i : Nat) :
    (xs.drop i).head! = xs.getD i 0 := by
  induction i generalizing xs with
  | zero => cases xs <;> simp
  | succ i ih => cases xs <;> simp [ih]

theorem decodeSignedDigit_of_encoding {n base bound code : Nat}
    (f : Fin n → Int)
    (hbase : base = 2 * bound + 1)
    (hf : ∀ i, (f i).natAbs ≤ bound)
    (hcode : (code : Int) = shiftedEncoding base bound (List.ofFn f))
    (i : Fin n) : decodeSignedDigit base bound code i = f i := by
  have hpos : 0 < base := by omega
  let digits : List Nat := List.ofFn fun i : Fin n => (f i + bound).toNat
  have hd : ∀ x ∈ digits, x < base := by
    intro x hx
    simp only [digits, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [hbase]
    exact shifted_digit_lt (hf j)
  have hc : code = Nat.ofDigits base digits := by
    apply Int.ofNat.inj
    have he := hcode
    unfold shiftedEncoding intEncoding at he
    rw [← Nat.coe_ofDigits Int base] at he
    simpa only [digits, List.map_ofFn, Function.comp_def, Int.ofNat_eq_natCast] using he
  unfold decodeSignedDigit
  rw [hc, Nat.ofDigits_div_pow_eq_ofDigits_drop i.1 hpos digits hd,
    Nat.ofDigits_mod_eq_head!, head_drop_eq_getD]
  rw [List.getD_eq_getElem digits 0 (by simp [digits])]
  simp only [digits, List.getElem_ofFn]
  rw [Nat.mod_eq_of_lt (by simpa only [hbase] using shifted_digit_lt (hf i)),
    Int.toNat_of_nonneg (shifted_digit_nonneg (hf i))]
  omega

def groupedCoefficient {L R : Type*} [Fintype L] [Fintype R] {g : Nat}
    (group : L → R → Fin g) (left : L → Int) (right : R → Int)
    (index : Fin g) : Int :=
  ∑ a, ∑ b, if group a b = index then left a * right b else 0

theorem groupedCoefficient_bound
    {L R : Type*} [Fintype L] [Fintype R] {g : Nat}
    (group : L → R → Fin g) (left : L → Int) (right : R → Int)
    (leftBound rightBound : Nat)
    (hl : ∀ a, (left a).natAbs ≤ leftBound)
    (hr : ∀ b, (right b).natAbs ≤ rightBound) (index : Fin g) :
    (groupedCoefficient group left right index).natAbs ≤
      Fintype.card L * (Fintype.card R * (leftBound * rightBound)) := by
  apply natAbs_sum_le_card_mul_bound
  intro a
  apply natAbs_sum_le_card_mul_bound
  intro b
  split
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (hl a) (hr b)
  · simp

theorem groupedCoefficient_encoding
    {L R : Type*} [Fintype L] [Fintype R] {g : Nat}
    (group : L → R → Fin g) (left : L → Int) (right : R → Int)
    (base : Nat) :
    (∑ index : Fin g, groupedCoefficient group left right index * (base : Int)^index.1) =
      ∑ a, ∑ b, left a * right b * (base : Int)^(group a b).1 := by
  unfold groupedCoefficient
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

theorem groupedCoefficient_of_encoding
    {L R : Type*} [Fintype L] [Fintype R] {g base bound code : Nat}
    (group : L → R → Fin g) (left : L → Int) (right : R → Int)
    (hbase : base = 2 * bound + 1)
    (hbound : ∀ i, (groupedCoefficient group left right i).natAbs ≤ bound)
    (hcode : (code : Int) = bound * geometricEncoding base g +
      ∑ a, ∑ b, left a * right b * (base : Int)^(group a b).1)
    (index : Fin g) :
    decodeSignedDigit base bound code index = groupedCoefficient group left right index := by
  apply decodeSignedDigit_of_encoding _ hbase hbound
  rw [shiftedEncoding_ofFn_eq_sum _ hbound]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [groupedCoefficient_encoding]
  rw [geometricEncoding, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum] at hcode
  simpa only [add_comm] using hcode

end Taeyoung.Methods.RootedSOS
