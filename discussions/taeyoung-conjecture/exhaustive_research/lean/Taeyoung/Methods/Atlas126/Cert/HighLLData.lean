import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.HighLLData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 1, 0, (243 : ℤ)⟩,
  ⟨0, 2, 0, (-486 : ℤ)⟩,
  ⟨0, 3, 0, (243 : ℤ)⟩,
  ⟨1, 0, 2, (9 : ℤ)⟩,
  ⟨1, 1, 0, (-333 : ℤ)⟩,
  ⟨1, 1, 1, (90 : ℤ)⟩,
  ⟨1, 2, 0, (477 : ℤ)⟩,
  ⟨1, 2, 1, (-108 : ℤ)⟩,
  ⟨1, 3, 0, (-45 : ℤ)⟩,
  ⟨1, 4, 0, (-90 : ℤ)⟩,
  ⟨2, 0, 2, (-3 : ℤ)⟩,
  ⟨2, 1, 0, (156 : ℤ)⟩,
  ⟨2, 1, 1, (-84 : ℤ)⟩,
  ⟨2, 1, 2, (15 : ℤ)⟩,
  ⟨2, 2, 0, (-111 : ℤ)⟩,
  ⟨2, 2, 1, (6 : ℤ)⟩,
  ⟨2, 3, 0, (-93 : ℤ)⟩,
  ⟨2, 3, 1, (54 : ℤ)⟩,
  ⟨2, 4, 0, (60 : ℤ)⟩,
  ⟨3, 0, 3, (2 : ℤ)⟩,
  ⟨3, 1, 0, (-24 : ℤ)⟩,
  ⟨3, 1, 1, (18 : ℤ)⟩,
  ⟨3, 1, 2, (-11 : ℤ)⟩,
  ⟨3, 2, 0, (-22 : ℤ)⟩,
  ⟨3, 2, 1, (34 : ℤ)⟩,
  ⟨3, 2, 2, (-18 : ℤ)⟩,
  ⟨3, 3, 0, (55 : ℤ)⟩,
  ⟨3, 4, 0, (-34 : ℤ)⟩,
  ⟨4, 1, 3, (2 : ℤ)⟩,
  ⟨4, 2, 0, (8 : ℤ)⟩,
  ⟨4, 2, 1, (-6 : ℤ)⟩,
  ⟨4, 3, 0, (-10 : ℤ)⟩,
  ⟨4, 4, 0, (6 : ℤ)⟩]

def commonCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff commonCoeffTerms i j k

def commonCoeff (i j k : ℕ) : ℚ :=
  (commonCoeffNumer i j k : ℚ) / 729

theorem commonCoeffExpansion (x d u : ℝ) :
    msum commonCoeff 4 4 3 x d u = sparseEval (commonCoeffTerms.map IntTerm.toRat) x d u / 729 := by
  have he : ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonCoeffNumer i j k = intSparseCoeff commonCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ commonCoeffTerms, t.i ≤ 4 ∧ t.j ≤ 4 ∧ t.k ≤ 3 := by decide +kernel
  exact msum_intSparse_scaled commonCoeffNumer commonCoeffTerms 729 4 4 3 he hb x d u

theorem commonIdentity (x d u : ℝ) :
    msum commonCoeff 4 4 3 x d u = highLLTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,highLLTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-486 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (243 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (9 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-333 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (477 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-45 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-3 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (156 : ℤ))
    (.leaf (-84 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-111 : ℤ))
    (.leaf (6 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-93 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (60 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (-24 : ℤ))))
    (.node 1 (.leaf (18 : ℤ))
    (.node 1 (.leaf (-11 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-22 : ℤ))
    (.node 1 (.leaf (34 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (55 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-34 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (8 : ℤ))
    (.leaf (-6 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-10 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (6 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

def commonInputNumer (i j k : ℕ) : ℤ :=
  commonInputData.get ((i * 5 + j) * 4 + k)

def commonInput (i j k : ℕ) : ℚ :=
  (commonInputNumer i j k : ℚ) / 729

theorem commonInputNumerCorrect :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonInputNumer i j k = commonCoeffNumer i j k := by
  decide +kernel

theorem commonInputCorrect :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      commonInput i j k = commonCoeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/729)
    (commonInputNumerCorrect i hi j hj k hk)


end Taeyoung.Methods.Atlas126.HighLLData
