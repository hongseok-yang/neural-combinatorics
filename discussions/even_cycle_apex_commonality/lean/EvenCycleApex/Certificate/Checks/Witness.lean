import EvenCycleApex.Certificate.Groups

/-!
# Kernel check: the skeleton witnesses

`prop:checked-data`, the relabelling part, in the encoding of DEVIATIONS X3 (i): every one of the
15,548 skeletons `h ∪ F_a ∪ σF_b` of the five groups is mapped by its witness permutation to the
representative of the witnessed orbit.  Shared by the three targets.  Evaluated by the kernel
(`decide +kernel`), one theorem per group (the group `r = 4` in three row ranges).
-/

set_option maxRecDepth 100000

namespace EvenCycleApex.Checks

open EvenCycleApex Certificate

theorem wit0 : ∀ a < schema0.feats.length, (witCert schema0 Data.W0).witRow Data.rep a = true := by
  decide +kernel

theorem wit1 : ∀ a < schema1.feats.length, (witCert schema1 Data.W1).witRow Data.rep a = true := by
  decide +kernel

theorem wit2 : ∀ a < schema2.feats.length, (witCert schema2 Data.W2).witRow Data.rep a = true := by
  decide +kernel

theorem wit3 : ∀ a < schema3.feats.length, (witCert schema3 Data.W3).witRow Data.rep a = true := by
  decide +kernel

theorem wit4_lo : ∀ a, a < 5 → (witCert schema4 Data.W4).witRow Data.rep a = true := by
  decide +kernel

theorem wit4_mid : ∀ a, 5 ≤ a → a < 10 → (witCert schema4 Data.W4).witRow Data.rep a = true := by
  decide +kernel

theorem wit4_hi : ∀ a, 10 ≤ a → a < 15 → (witCert schema4 Data.W4).witRow Data.rep a = true := by
  decide +kernel

theorem wit4 : ∀ a < schema4.feats.length, (witCert schema4 Data.W4).witRow Data.rep a = true := by
  intro a ha
  have h15 : schema4.feats.length = 15 := rfl
  rw [h15] at ha
  by_cases h5 : a < 5
  · exact wit4_lo a h5
  by_cases h10 : a < 10
  · exact wit4_mid a (by omega) h10
  · exact wit4_hi a (by omega) ha

end EvenCycleApex.Checks
