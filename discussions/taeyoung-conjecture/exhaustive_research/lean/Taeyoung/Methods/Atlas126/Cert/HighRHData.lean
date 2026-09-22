import Taeyoung.Methods.Atlas126.HighRh
import Taeyoung.Methods.Atlas126.HighRhLocal
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.HighRHData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 3, 0, (6561 : ℤ)⟩,
  ⟨0, 4, 0, (-3645 : ℤ)⟩,
  ⟨1, 2, 0, (4374 : ℤ)⟩,
  ⟨1, 2, 1, (-5832 : ℤ)⟩,
  ⟨1, 3, 0, (-30618 : ℤ)⟩,
  ⟨1, 3, 1, (4374 : ℤ)⟩,
  ⟨1, 4, 0, (17010 : ℤ)⟩,
  ⟨2, 0, 2, (648 : ℤ)⟩,
  ⟨2, 1, 1, (-4536 : ℤ)⟩,
  ⟨2, 1, 2, (1620 : ℤ)⟩,
  ⟨2, 2, 0, (-14256 : ℤ)⟩,
  ⟨2, 2, 1, (22680 : ℤ)⟩,
  ⟨2, 2, 2, (-2916 : ℤ)⟩,
  ⟨2, 3, 0, (57915 : ℤ)⟩,
  ⟨2, 3, 1, (-14580 : ℤ)⟩,
  ⟨2, 4, 0, (-32967 : ℤ)⟩,
  ⟨3, 0, 2, (432 : ℤ)⟩,
  ⟨3, 0, 3, (432 : ℤ)⟩,
  ⟨3, 1, 1, (10368 : ℤ)⟩,
  ⟨3, 1, 2, (-7776 : ℤ)⟩,
  ⟨3, 1, 3, (648 : ℤ)⟩,
  ⟨3, 2, 0, (17874 : ℤ)⟩,
  ⟨3, 2, 1, (-30996 : ℤ)⟩,
  ⟨3, 2, 2, (7776 : ℤ)⟩,
  ⟨3, 3, 0, (-57834 : ℤ)⟩,
  ⟨3, 3, 1, (17496 : ℤ)⟩,
  ⟨3, 4, 0, (34911 : ℤ)⟩,
  ⟨4, 0, 2, (-2160 : ℤ)⟩,
  ⟨4, 1, 1, (-7560 : ℤ)⟩,
  ⟨4, 1, 2, (10368 : ℤ)⟩,
  ⟨4, 1, 3, (-1296 : ℤ)⟩,
  ⟨4, 2, 0, (-11286 : ℤ)⟩,
  ⟨4, 2, 1, (16992 : ℤ)⟩,
  ⟨4, 2, 2, (-7128 : ℤ)⟩,
  ⟨4, 3, 0, (34155 : ℤ)⟩,
  ⟨4, 3, 1, (-8748 : ℤ)⟩,
  ⟨4, 4, 0, (-22599 : ℤ)⟩,
  ⟨5, 0, 2, (1632 : ℤ)⟩,
  ⟨5, 0, 3, (-288 : ℤ)⟩,
  ⟨5, 1, 1, (1608 : ℤ)⟩,
  ⟨5, 1, 2, (-5208 : ℤ)⟩,
  ⟨5, 1, 3, (864 : ℤ)⟩,
  ⟨5, 2, 0, (4248 : ℤ)⟩,
  ⟨5, 2, 1, (-2448 : ℤ)⟩,
  ⟨5, 2, 2, (2592 : ℤ)⟩,
  ⟨5, 3, 0, (-13122 : ℤ)⟩,
  ⟨5, 3, 1, (1458 : ℤ)⟩,
  ⟨5, 4, 0, (9396 : ℤ)⟩,
  ⟨6, 0, 2, (-472 : ℤ)⟩,
  ⟨6, 0, 3, (128 : ℤ)⟩,
  ⟨6, 1, 1, (192 : ℤ)⟩,
  ⟨6, 1, 2, (1068 : ℤ)⟩,
  ⟨6, 1, 3, (-240 : ℤ)⟩,
  ⟨6, 2, 0, (-1098 : ℤ)⟩,
  ⟨6, 2, 1, (-504 : ℤ)⟩,
  ⟨6, 2, 2, (-324 : ℤ)⟩,
  ⟨6, 3, 0, (3321 : ℤ)⟩,
  ⟨6, 4, 0, (-2349 : ℤ)⟩,
  ⟨7, 0, 2, (48 : ℤ)⟩,
  ⟨7, 0, 3, (-16 : ℤ)⟩,
  ⟨7, 1, 1, (-72 : ℤ)⟩,
  ⟨7, 1, 2, (-72 : ℤ)⟩,
  ⟨7, 1, 3, (24 : ℤ)⟩,
  ⟨7, 2, 0, (144 : ℤ)⟩,
  ⟨7, 2, 1, (108 : ℤ)⟩,
  ⟨7, 3, 0, (-378 : ℤ)⟩,
  ⟨7, 4, 0, (243 : ℤ)⟩]

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
    msum commonCoeff 7 4 3 x d u = highRhTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,highRhTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (6561 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-3645 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4374 : ℤ))
    (.leaf (-5832 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-30618 : ℤ))
    (.node 1 (.leaf (4374 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (648 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-4536 : ℤ))
    (.leaf (1620 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-14256 : ℤ))
    (.leaf (22680 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-2916 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (57915 : ℤ))
    (.node 1 (.leaf (-14580 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-32967 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (432 : ℤ))
    (.node 1 (.leaf (432 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (10368 : ℤ))
    (.leaf (-7776 : ℤ)))
    (.node 1 (.leaf (648 : ℤ))
    (.node 1 (.leaf (17874 : ℤ))
    (.leaf (-30996 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (7776 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-57834 : ℤ))
    (.node 1 (.leaf (17496 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (34911 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-2160 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-7560 : ℤ))
    (.leaf (10368 : ℤ)))
    (.node 1 (.leaf (-1296 : ℤ))
    (.node 1 (.leaf (-11286 : ℤ))
    (.leaf (16992 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-7128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (34155 : ℤ))
    (.node 1 (.leaf (-8748 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-22599 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1632 : ℤ))
    (.node 1 (.leaf (-288 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (1608 : ℤ))
    (.leaf (-5208 : ℤ)))
    (.node 1 (.leaf (864 : ℤ))
    (.node 1 (.leaf (4248 : ℤ))
    (.leaf (-2448 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (2592 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-13122 : ℤ))
    (.node 1 (.leaf (1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (9396 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-472 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (1068 : ℤ)))
    (.node 1 (.leaf (-240 : ℤ))
    (.node 1 (.leaf (-1098 : ℤ))
    (.leaf (-504 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-324 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (3321 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2349 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (48 : ℤ))
    (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-72 : ℤ))
    (.leaf (-72 : ℤ)))
    (.node 1 (.leaf (24 : ℤ))
    (.node 1 (.leaf (144 : ℤ))
    (.leaf (108 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-378 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (243 : ℤ)))
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


end Taeyoung.Methods.Atlas126.HighRHData
