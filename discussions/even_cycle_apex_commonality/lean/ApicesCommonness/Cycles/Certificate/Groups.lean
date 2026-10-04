import ApicesCommonness.Cycles.Certificate.Sound
import ApicesCommonness.Cycles.Certificate.Data.Witnesses
import ApicesCommonness.Cycles.Certificate.Data.Target_MeanThree
import ApicesCommonness.Cycles.Certificate.Data.Target_Neg
import ApicesCommonness.Cycles.Certificate.Data.Target_Pos

/-!
# The group certificates of the three targets

Each target's certificate is five `GroupCert`s (the groups `r = 0, …, 4` of `schemas`), assembled
from the generated data: the skeleton witnesses `W{r}` (shared), and the target's merged matrices
`M{r}` and factorizations `ldl{r}`.  `witCert S W` is the witness-only certificate used by the
target-independent witness checks; `witRow` does not look at the matrices (`witRow_witCert`).
-/

namespace ApicesCommonness

open Certificate

/-- A certificate carrying only the schema and the skeleton witnesses. -/
def witCert (S : Schema) (W : List (List (List ℕ))) : GroupCert := ⟨S, W, [], []⟩

lemma witRow_witCert (rep : ℕ → ℕ) (S : Schema) (W : List (List (List ℕ)))
    (M : List (List (List ℤ))) (L : List (List (List (ℤ × ℕ)) × List (ℤ × ℕ))) (a : ℕ) :
    GroupCert.witRow rep ⟨S, W, M, L⟩ a = (witCert S W).witRow rep a := rfl

def meanThreeG0 : GroupCert := ⟨schema0, Data.W0, Data.MeanThree.M0, Data.MeanThree.ldl0⟩
def meanThreeG1 : GroupCert := ⟨schema1, Data.W1, Data.MeanThree.M1, Data.MeanThree.ldl1⟩
def meanThreeG2 : GroupCert := ⟨schema2, Data.W2, Data.MeanThree.M2, Data.MeanThree.ldl2⟩
def meanThreeG3 : GroupCert := ⟨schema3, Data.W3, Data.MeanThree.M3, Data.MeanThree.ldl3⟩
def meanThreeG4 : GroupCert := ⟨schema4, Data.W4, Data.MeanThree.M4, Data.MeanThree.ldl4⟩

/-- The certificate of `P_mean,3`. -/
def meanThreeGroups : List GroupCert :=
  [meanThreeG0, meanThreeG1, meanThreeG2, meanThreeG3, meanThreeG4]

def negG0 : GroupCert := ⟨schema0, Data.W0, Data.Neg.M0, Data.Neg.ldl0⟩
def negG1 : GroupCert := ⟨schema1, Data.W1, Data.Neg.M1, Data.Neg.ldl1⟩
def negG2 : GroupCert := ⟨schema2, Data.W2, Data.Neg.M2, Data.Neg.ldl2⟩
def negG3 : GroupCert := ⟨schema3, Data.W3, Data.Neg.M3, Data.Neg.ldl3⟩
def negG4 : GroupCert := ⟨schema4, Data.W4, Data.Neg.M4, Data.Neg.ldl4⟩

/-- The certificate of `P₋`. -/
def negGroups : List GroupCert := [negG0, negG1, negG2, negG3, negG4]

def posG0 : GroupCert := ⟨schema0, Data.W0, Data.Pos.M0, Data.Pos.ldl0⟩
def posG1 : GroupCert := ⟨schema1, Data.W1, Data.Pos.M1, Data.Pos.ldl1⟩
def posG2 : GroupCert := ⟨schema2, Data.W2, Data.Pos.M2, Data.Pos.ldl2⟩
def posG3 : GroupCert := ⟨schema3, Data.W3, Data.Pos.M3, Data.Pos.ldl3⟩
def posG4 : GroupCert := ⟨schema4, Data.W4, Data.Pos.M4, Data.Pos.ldl4⟩

/-- The certificate of `P₊`. -/
def posGroups : List GroupCert := [posG0, posG1, posG2, posG3, posG4]

/-- The scale `64𝒟` of identity (C). -/
def certScale : ℕ := 64 * 90315258984881964711936

end ApicesCommonness
