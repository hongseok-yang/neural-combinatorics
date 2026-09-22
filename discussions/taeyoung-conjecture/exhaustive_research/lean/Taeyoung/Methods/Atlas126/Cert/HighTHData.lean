import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.HighTHData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 0, 0, (96 : ℤ)⟩,
  ⟨0, 1, 0, (-128 : ℤ)⟩,
  ⟨0, 1, 1, (-32 : ℤ)⟩,
  ⟨0, 2, 0, (-80 : ℤ)⟩,
  ⟨0, 2, 1, (-96 : ℤ)⟩,
  ⟨0, 2, 2, (-128 : ℤ)⟩,
  ⟨0, 3, 0, (160 : ℤ)⟩,
  ⟨0, 3, 1, (224 : ℤ)⟩,
  ⟨0, 3, 2, (448 : ℤ)⟩,
  ⟨0, 3, 3, (384 : ℤ)⟩,
  ⟨0, 4, 0, (-48 : ℤ)⟩,
  ⟨0, 4, 1, (-96 : ℤ)⟩,
  ⟨0, 4, 2, (-192 : ℤ)⟩,
  ⟨0, 4, 3, (-128 : ℤ)⟩,
  ⟨1, 0, 0, (408 : ℤ)⟩,
  ⟨1, 1, 0, (-336 : ℤ)⟩,
  ⟨1, 1, 1, (-176 : ℤ)⟩,
  ⟨1, 2, 0, (-40 : ℤ)⟩,
  ⟨1, 2, 1, (64 : ℤ)⟩,
  ⟨1, 2, 2, (128 : ℤ)⟩,
  ⟨1, 3, 0, (-144 : ℤ)⟩,
  ⟨1, 3, 1, (-624 : ℤ)⟩,
  ⟨1, 3, 2, (-1504 : ℤ)⟩,
  ⟨1, 3, 3, (-1216 : ℤ)⟩,
  ⟨1, 4, 0, (112 : ℤ)⟩,
  ⟨1, 4, 1, (384 : ℤ)⟩,
  ⟨1, 4, 2, (768 : ℤ)⟩,
  ⟨1, 4, 3, (512 : ℤ)⟩,
  ⟨2, 0, 0, (876 : ℤ)⟩,
  ⟨2, 1, 0, (-352 : ℤ)⟩,
  ⟨2, 1, 1, (-296 : ℤ)⟩,
  ⟨2, 2, 0, (64 : ℤ)⟩,
  ⟨2, 2, 1, (56 : ℤ)⟩,
  ⟨2, 2, 2, (96 : ℤ)⟩,
  ⟨2, 3, 0, (-16 : ℤ)⟩,
  ⟨2, 3, 1, (784 : ℤ)⟩,
  ⟨2, 3, 2, (1824 : ℤ)⟩,
  ⟨2, 3, 3, (1344 : ℤ)⟩,
  ⟨2, 4, 0, (-96 : ℤ)⟩,
  ⟨2, 4, 1, (-576 : ℤ)⟩,
  ⟨2, 4, 2, (-1152 : ℤ)⟩,
  ⟨2, 4, 3, (-768 : ℤ)⟩,
  ⟨3, 0, 0, (990 : ℤ)⟩,
  ⟨3, 1, 0, (228 : ℤ)⟩,
  ⟨3, 1, 1, (236 : ℤ)⟩,
  ⟨3, 2, 0, (264 : ℤ)⟩,
  ⟨3, 2, 1, (240 : ℤ)⟩,
  ⟨3, 2, 2, (-64 : ℤ)⟩,
  ⟨3, 3, 0, (-536 : ℤ)⟩,
  ⟨3, 3, 1, (-752 : ℤ)⟩,
  ⟨3, 3, 2, (-928 : ℤ)⟩,
  ⟨3, 3, 3, (-576 : ℤ)⟩,
  ⟨3, 4, 0, (176 : ℤ)⟩,
  ⟨3, 4, 1, (384 : ℤ)⟩,
  ⟨3, 4, 2, (768 : ℤ)⟩,
  ⟨3, 4, 3, (512 : ℤ)⟩,
  ⟨4, 0, 0, (519 : ℤ)⟩,
  ⟨4, 1, 0, (308 : ℤ)⟩,
  ⟨4, 1, 1, (284 : ℤ)⟩,
  ⟨4, 2, 0, (-172 : ℤ)⟩,
  ⟨4, 2, 1, (-328 : ℤ)⟩,
  ⟨4, 2, 2, (-32 : ℤ)⟩,
  ⟨4, 3, 0, (728 : ℤ)⟩,
  ⟨4, 3, 1, (432 : ℤ)⟩,
  ⟨4, 3, 2, (160 : ℤ)⟩,
  ⟨4, 3, 3, (64 : ℤ)⟩,
  ⟨4, 4, 0, (-304 : ℤ)⟩,
  ⟨4, 4, 1, (-96 : ℤ)⟩,
  ⟨4, 4, 2, (-192 : ℤ)⟩,
  ⟨4, 4, 3, (-128 : ℤ)⟩,
  ⟨5, 0, 0, (69 : ℤ)⟩,
  ⟨5, 1, 0, (154 : ℤ)⟩,
  ⟨5, 1, 1, (8 : ℤ)⟩,
  ⟨5, 2, 0, (-40 : ℤ)⟩,
  ⟨5, 2, 1, (-32 : ℤ)⟩,
  ⟨5, 3, 0, (-8 : ℤ)⟩,
  ⟨5, 3, 1, (32 : ℤ)⟩,
  ⟨5, 4, 0, (144 : ℤ)⟩,
  ⟨6, 0, 0, (-33 : ℤ)⟩,
  ⟨6, 1, 0, (98 : ℤ)⟩,
  ⟨6, 1, 1, (-24 : ℤ)⟩,
  ⟨6, 2, 0, (20 : ℤ)⟩,
  ⟨6, 2, 1, (96 : ℤ)⟩,
  ⟨6, 3, 0, (-200 : ℤ)⟩,
  ⟨6, 3, 1, (-96 : ℤ)⟩,
  ⟨6, 4, 0, (64 : ℤ)⟩,
  ⟨7, 0, 0, (-9 : ℤ)⟩,
  ⟨7, 1, 0, (28 : ℤ)⟩,
  ⟨7, 2, 0, (-16 : ℤ)⟩,
  ⟨7, 3, 0, (16 : ℤ)⟩,
  ⟨7, 4, 0, (-48 : ℤ)⟩]

def commonCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff commonCoeffTerms i j k

def commonCoeff (i j k : ℕ) : ℚ :=
  (commonCoeffNumer i j k : ℚ) / 5832

theorem commonCoeffExpansion (x d u : ℝ) :
    msum commonCoeff 7 4 3 x d u = sparseEval (commonCoeffTerms.map IntTerm.toRat) x d u / 5832 := by
  have he : ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonCoeffNumer i j k = intSparseCoeff commonCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ commonCoeffTerms, t.i ≤ 7 ∧ t.j ≤ 4 ∧ t.k ≤ 3 := by decide +kernel
  exact msum_intSparse_scaled commonCoeffNumer commonCoeffTerms 5832 7 4 3 he hb x d u

theorem commonIdentity (x d u : ℝ) :
    msum commonCoeff 7 4 3 x d u = highTHTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,highTHTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-128 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-80 : ℤ))
    (.leaf (-96 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (160 : ℤ))
    (.node 1 (.leaf (224 : ℤ))
    (.leaf (448 : ℤ)))))
    (.node 2 (.node 1 (.leaf (384 : ℤ))
    (.leaf (-48 : ℤ)))
    (.node 1 (.leaf (-96 : ℤ))
    (.node 1 (.leaf (-192 : ℤ))
    (.leaf (-128 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (408 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-336 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-176 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-40 : ℤ))
    (.leaf (64 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-144 : ℤ))
    (.node 1 (.leaf (-624 : ℤ))
    (.leaf (-1504 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1216 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (384 : ℤ))
    (.node 1 (.leaf (768 : ℤ))
    (.leaf (512 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (876 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-352 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-296 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (64 : ℤ))
    (.leaf (56 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-16 : ℤ))
    (.node 1 (.leaf (784 : ℤ))
    (.leaf (1824 : ℤ)))))
    (.node 2 (.node 1 (.leaf (1344 : ℤ))
    (.leaf (-96 : ℤ)))
    (.node 1 (.leaf (-576 : ℤ))
    (.node 1 (.leaf (-1152 : ℤ))
    (.leaf (-768 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (990 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (228 : ℤ)))))
    (.node 2 (.node 1 (.leaf (236 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (264 : ℤ))
    (.leaf (240 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-64 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-536 : ℤ))
    (.node 1 (.leaf (-752 : ℤ))
    (.leaf (-928 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-576 : ℤ))
    (.leaf (176 : ℤ)))
    (.node 1 (.leaf (384 : ℤ))
    (.node 1 (.leaf (768 : ℤ))
    (.leaf (512 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (519 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (308 : ℤ)))))
    (.node 2 (.node 1 (.leaf (284 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-172 : ℤ))
    (.leaf (-328 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (728 : ℤ))
    (.node 1 (.leaf (432 : ℤ))
    (.leaf (160 : ℤ)))))
    (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (-304 : ℤ)))
    (.node 1 (.leaf (-96 : ℤ))
    (.node 1 (.leaf (-192 : ℤ))
    (.leaf (-128 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (69 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (154 : ℤ)))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-40 : ℤ))
    (.leaf (-32 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-8 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (-33 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (98 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-24 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (20 : ℤ))
    (.leaf (96 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-200 : ℤ))
    (.node 1 (.leaf (-96 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (64 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (-9 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (28 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-48 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))

def commonInputNumer (i j k : ℕ) : ℤ :=
  commonInputData.get ((i * 5 + j) * 4 + k)

def commonInput (i j k : ℕ) : ℚ :=
  (commonInputNumer i j k : ℚ) / 5832

theorem commonInputNumerCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonInputNumer i j k = commonCoeffNumer i j k := by
  decide +kernel

theorem commonInputCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonInput i j k = commonCoeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/5832)
    (commonInputNumerCorrect i hi j hj k hk)


end Taeyoung.Methods.Atlas126.HighTHData
