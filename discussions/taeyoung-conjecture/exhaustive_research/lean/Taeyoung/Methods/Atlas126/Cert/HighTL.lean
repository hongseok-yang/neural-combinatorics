import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate HTL.
Regenerate with `codes/generate_atlas126_junction_lean.py`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein

private def leaf0CoeffTerms : List IntTerm := [
  ⟨0, 0, 0, (96 : ℤ)⟩,
  ⟨0, 1, 0, (-112 : ℤ)⟩,
  ⟨0, 1, 1, (-16 : ℤ)⟩,
  ⟨0, 2, 0, (-64 : ℤ)⟩,
  ⟨0, 2, 1, (16 : ℤ)⟩,
  ⟨0, 2, 2, (-32 : ℤ)⟩,
  ⟨0, 3, 0, (112 : ℤ)⟩,
  ⟨0, 3, 1, (32 : ℤ)⟩,
  ⟨0, 3, 2, (-32 : ℤ)⟩,
  ⟨0, 3, 3, (48 : ℤ)⟩,
  ⟨0, 4, 0, (-32 : ℤ)⟩,
  ⟨0, 4, 3, (-16 : ℤ)⟩,
  ⟨1, 0, 0, (408 : ℤ)⟩,
  ⟨1, 1, 0, (-248 : ℤ)⟩,
  ⟨1, 1, 1, (-88 : ℤ)⟩,
  ⟨1, 2, 0, (-40 : ℤ)⟩,
  ⟨1, 2, 1, (-32 : ℤ)⟩,
  ⟨1, 2, 2, (32 : ℤ)⟩,
  ⟨1, 3, 0, (-56 : ℤ)⟩,
  ⟨1, 3, 1, (-16 : ℤ)⟩,
  ⟨1, 3, 2, (80 : ℤ)⟩,
  ⟨1, 3, 3, (-152 : ℤ)⟩,
  ⟨1, 4, 0, (48 : ℤ)⟩,
  ⟨1, 4, 3, (64 : ℤ)⟩,
  ⟨2, 0, 0, (876 : ℤ)⟩,
  ⟨2, 1, 0, (-204 : ℤ)⟩,
  ⟨2, 1, 1, (-148 : ℤ)⟩,
  ⟨2, 2, 0, (60 : ℤ)⟩,
  ⟨2, 2, 1, (-20 : ℤ)⟩,
  ⟨2, 2, 2, (24 : ℤ)⟩,
  ⟨2, 3, 0, (-120 : ℤ)⟩,
  ⟨2, 3, 1, (-16 : ℤ)⟩,
  ⟨2, 3, 2, (-48 : ℤ)⟩,
  ⟨2, 3, 3, (168 : ℤ)⟩,
  ⟨2, 4, 3, (-96 : ℤ)⟩,
  ⟨3, 0, 0, (990 : ℤ)⟩,
  ⟨3, 1, 0, (110 : ℤ)⟩,
  ⟨3, 1, 1, (118 : ℤ)⟩,
  ⟨3, 2, 0, (128 : ℤ)⟩,
  ⟨3, 2, 1, (152 : ℤ)⟩,
  ⟨3, 2, 2, (-16 : ℤ)⟩,
  ⟨3, 3, 0, (-320 : ℤ)⟩,
  ⟨3, 3, 1, (-128 : ℤ)⟩,
  ⟨3, 3, 2, (-16 : ℤ)⟩,
  ⟨3, 3, 3, (-72 : ℤ)⟩,
  ⟨3, 4, 0, (112 : ℤ)⟩,
  ⟨3, 4, 3, (64 : ℤ)⟩,
  ⟨4, 0, 0, (519 : ℤ)⟩,
  ⟨4, 1, 0, (166 : ℤ)⟩,
  ⟨4, 1, 1, (142 : ℤ)⟩,
  ⟨4, 2, 0, (-16 : ℤ)⟩,
  ⟨4, 2, 1, (-148 : ℤ)⟩,
  ⟨4, 2, 2, (-8 : ℤ)⟩,
  ⟨4, 3, 0, (544 : ℤ)⟩,
  ⟨4, 3, 1, (160 : ℤ)⟩,
  ⟨4, 3, 2, (16 : ℤ)⟩,
  ⟨4, 3, 3, (8 : ℤ)⟩,
  ⟨4, 4, 0, (-288 : ℤ)⟩,
  ⟨4, 4, 3, (-16 : ℤ)⟩,
  ⟨5, 0, 0, (69 : ℤ)⟩,
  ⟨5, 1, 0, (150 : ℤ)⟩,
  ⟨5, 1, 1, (4 : ℤ)⟩,
  ⟨5, 2, 0, (-24 : ℤ)⟩,
  ⟨5, 2, 1, (-16 : ℤ)⟩,
  ⟨5, 3, 0, (-24 : ℤ)⟩,
  ⟨5, 3, 1, (16 : ℤ)⟩,
  ⟨5, 4, 0, (144 : ℤ)⟩,
  ⟨6, 0, 0, (-33 : ℤ)⟩,
  ⟨6, 1, 0, (110 : ℤ)⟩,
  ⟨6, 1, 1, (-12 : ℤ)⟩,
  ⟨6, 2, 0, (-28 : ℤ)⟩,
  ⟨6, 2, 1, (48 : ℤ)⟩,
  ⟨6, 3, 0, (-152 : ℤ)⟩,
  ⟨6, 3, 1, (-48 : ℤ)⟩,
  ⟨6, 4, 0, (64 : ℤ)⟩,
  ⟨7, 0, 0, (-9 : ℤ)⟩,
  ⟨7, 1, 0, (28 : ℤ)⟩,
  ⟨7, 2, 0, (-16 : ℤ)⟩,
  ⟨7, 3, 0, (16 : ℤ)⟩,
  ⟨7, 4, 0, (-48 : ℤ)⟩]

private def leaf0CoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff leaf0CoeffTerms i j k

private def leaf0Coeff (i j k : ℕ) : ℚ :=
  (leaf0CoeffNumer i j k : ℚ) / 5832

private theorem leaf0CoeffExpansion (x d u : ℝ) :
    msum leaf0Coeff 7 4 3 x d u = sparseEval (leaf0CoeffTerms.map IntTerm.toRat) x d u / 5832 := by
  have he : ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0CoeffNumer i j k = intSparseCoeff leaf0CoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ leaf0CoeffTerms, t.i ≤ 7 ∧ t.j ≤ 4 ∧ t.k ≤ 3 := by decide +kernel
  exact msum_intSparse_scaled leaf0CoeffNumer leaf0CoeffTerms 5832 7 4 3 he hb x d u

private theorem leaf0Identity (x d u : ℝ) :
    msum leaf0Coeff 7 4 3 x d u = highTLTarget x d u := by
  rw [leaf0CoeffExpansion]
  simp only [sparseEval, IntTerm.toRat, leaf0CoeffTerms, highTLTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

private def leaf0InputData : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-112 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-64 : ℤ))
    (.leaf (16 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (112 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (-32 : ℤ)))))
    (.node 2 (.node 1 (.leaf (48 : ℤ))
    (.leaf (-32 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-16 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (408 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-248 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-88 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-40 : ℤ))
    (.leaf (-32 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-56 : ℤ))
    (.node 1 (.leaf (-16 : ℤ))
    (.leaf (80 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-152 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (64 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (876 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-204 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-148 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (60 : ℤ))
    (.leaf (-20 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-120 : ℤ))
    (.node 1 (.leaf (-16 : ℤ))
    (.leaf (-48 : ℤ)))))
    (.node 2 (.node 1 (.leaf (168 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-96 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (990 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (110 : ℤ)))))
    (.node 2 (.node 1 (.leaf (118 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (152 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-320 : ℤ))
    (.node 1 (.leaf (-128 : ℤ))
    (.leaf (-16 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-72 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (64 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (519 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (166 : ℤ)))))
    (.node 2 (.node 1 (.leaf (142 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-16 : ℤ))
    (.leaf (-148 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-8 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (544 : ℤ))
    (.node 1 (.leaf (160 : ℤ))
    (.leaf (16 : ℤ)))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (-288 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-16 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (69 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 2 (.node 1 (.leaf (4 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-24 : ℤ))
    (.leaf (-16 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-24 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
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
    (.leaf (110 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-12 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-28 : ℤ))
    (.leaf (48 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-152 : ℤ))
    (.node 1 (.leaf (-48 : ℤ))
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

private def leaf0InputNumer (i j k : ℕ) : ℤ :=
  leaf0InputData.get ((i * 5 + j) * 4 + k)

private def leaf0Input (i j k : ℕ) : ℚ :=
  (leaf0InputNumer i j k : ℚ) / 5832

private theorem leaf0InputNumerCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0InputNumer i j k = leaf0CoeffNumer i j k := by
  decide +kernel

private theorem leaf0InputCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0Input i j k = leaf0Coeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/5832)
    (leaf0InputNumerCorrect i hi j hj k hk)

private def leaf0W1Data : IntTable :=
  (.node 32 (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (7 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (21 : ℤ))
    (.leaf (6 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (35 : ℤ))
    (.leaf (15 : ℤ)))
    (.node 1 (.leaf (5 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (35 : ℤ))
    (.leaf (20 : ℤ)))
    (.node 1 (.leaf (10 : ℤ))
    (.leaf (4 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (21 : ℤ))
    (.leaf (15 : ℤ)))
    (.node 1 (.leaf (10 : ℤ))
    (.leaf (6 : ℤ))))
    (.node 2 (.node 1 (.leaf (3 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (7 : ℤ))
    (.leaf (6 : ℤ)))
    (.node 1 (.leaf (5 : ℤ))
    (.leaf (4 : ℤ))))
    (.node 2 (.node 1 (.leaf (3 : ℤ))
    (.leaf (2 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))))))

private def leaf0W1Numer (k i : ℕ) : ℤ :=
  leaf0W1Data.get (k * 8 + i)

private def leaf0W1 (k i : ℕ) : ℚ :=
  (leaf0W1Numer k i : ℚ) / 1

private theorem leaf0W1NumerCorrect :
    ∀ k ∈ range 8, ∀ i ∈ range 8,
      leaf0W1Numer k i = intTransWeight 7 (0) 1 1 k i := by
  decide +kernel

private theorem leaf0W1Correct : WeightsCorrect 7 (0 : ℚ) (1 : ℚ) leaf0W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 7 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf0W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^7 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf0W1, neg_div] using he

private def leaf0W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (3 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (4 : ℤ))
    (.node 1 (.leaf (3 : ℤ))
    (.leaf (2 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))))))

private def leaf0W2Numer (k i : ℕ) : ℤ :=
  leaf0W2Data.get (k * 5 + i)

private def leaf0W2 (k i : ℕ) : ℚ :=
  (leaf0W2Numer k i : ℚ) / 1

private theorem leaf0W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf0W2Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf0W2Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf0W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf0W2NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf0W2, neg_div] using he

private def leaf0W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (3 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (3 : ℤ))
    (.leaf (2 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))))

private def leaf0W3Numer (k i : ℕ) : ℤ :=
  leaf0W3Data.get (k * 4 + i)

private def leaf0W3 (k i : ℕ) : ℚ :=
  (leaf0W3Numer k i : ℚ) / 1

private theorem leaf0W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf0W3Numer k i = intTransWeight 3 (0) 1 1 k i := by
  decide +kernel

private theorem leaf0W3Correct : WeightsCorrect 3 (0 : ℚ) (1 : ℚ) leaf0W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf0W3NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^3 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf0W3, neg_div] using he

private def leaf0S1Data : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-112 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-64 : ℤ))
    (.leaf (16 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (112 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (-32 : ℤ)))))
    (.node 2 (.node 1 (.leaf (48 : ℤ))
    (.leaf (-32 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-16 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (1080 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-1032 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-200 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-488 : ℤ))
    (.leaf (80 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-192 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (728 : ℤ))
    (.node 1 (.leaf (208 : ℤ))
    (.leaf (-144 : ℤ)))))
    (.node 2 (.node 1 (.leaf (184 : ℤ))
    (.leaf (-176 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-48 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (5340 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-4044 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1012 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1524 : ℤ))
    (.leaf (124 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-456 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1896 : ℤ))
    (.node 1 (.leaf (560 : ℤ))
    (.leaf (-240 : ℤ)))))
    (.node 2 (.node 1 (.leaf (264 : ℤ))
    (.leaf (-384 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-48 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (14850 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-8550 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-2502 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-2412 : ℤ))
    (.leaf (132 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-536 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (2160 : ℤ))
    (.node 1 (.leaf (672 : ℤ))
    (.leaf (-176 : ℤ)))))
    (.node 2 (.node 1 (.leaf (168 : ℤ))
    (.leaf (-288 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-16 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24759 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-10314 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-3186 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1944 : ℤ))
    (.leaf (180 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-312 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (864 : ℤ))
    (.node 1 (.leaf (288 : ℤ))
    (.leaf (-48 : ℤ)))))
    (.node 2 (.node 1 (.leaf (40 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24462 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-6804 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1998 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-648 : ℤ))
    (.leaf (108 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-72 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (13122 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-1944 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-486 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (2916 : ℤ))
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
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))

private def leaf0S1Numer (i j k : ℕ) : ℤ :=
  leaf0S1Data.get ((i * 5 + j) * 4 + k)

private def leaf0S1 (i j k : ℕ) : ℚ :=
  (leaf0S1Numer i j k : ℚ) / 5832

private theorem leaf0S1NumerCorrect :
    ∀ h ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0S1Numer h j k = ∑ i ∈ range 8, leaf0InputNumer i j k * leaf0W1Numer h i := by
  decide +kernel

private theorem leaf0S1Correct : Axis1Correct 7 4 3 leaf0W1 leaf0Input leaf0S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => leaf0InputNumer i j k) (leaf0W1Numer h) (leaf0S1Numer h j k) 5832 1 7
    (leaf0S1NumerCorrect h hh j hj k hk)
  norm_num only [show (5832 : ℚ)*1 = 5832 by norm_num] at he
  exact he

private def leaf0S2Data : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (272 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-16 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (176 : ℤ))
    (.leaf (-32 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-32 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (-96 : ℤ)))))
    (.node 2 (.node 1 (.leaf (48 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (-64 : ℤ))
    (.leaf (32 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (1080 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3288 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-200 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (2896 : ℤ))
    (.leaf (-520 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-192 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (976 : ℤ))
    (.node 1 (.leaf (-232 : ℤ))
    (.leaf (-528 : ℤ)))))
    (.node 2 (.node 1 (.leaf (184 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (88 : ℤ))
    (.node 1 (.leaf (-336 : ℤ))
    (.leaf (136 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (5340 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (17316 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1012 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (18384 : ℤ))
    (.leaf (-2912 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-456 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (8076 : ℤ))
    (.node 1 (.leaf (-2228 : ℤ))
    (.leaf (-1152 : ℤ)))))
    (.node 2 (.node 1 (.leaf (264 : ℤ))
    (.leaf (1284 : ℤ)))
    (.node 1 (.leaf (-328 : ℤ))
    (.node 1 (.leaf (-696 : ℤ))
    (.leaf (216 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (14850 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (50850 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-2502 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (61038 : ℤ))
    (.leaf (-7374 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-536 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (31086 : ℤ))
    (.node 1 (.leaf (-6570 : ℤ))
    (.leaf (-1248 : ℤ)))))
    (.node 2 (.node 1 (.leaf (168 : ℤ))
    (.leaf (5760 : ℤ)))
    (.node 1 (.leaf (-1698 : ℤ))
    (.node 1 (.leaf (-712 : ℤ))
    (.leaf (152 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24759 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (88722 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-3186 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (115668 : ℤ))
    (.leaf (-9378 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-312 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (65070 : ℤ))
    (.node 1 (.leaf (-8910 : ℤ))
    (.leaf (-672 : ℤ)))))
    (.node 2 (.node 1 (.leaf (40 : ℤ))
    (.leaf (13365 : ℤ)))
    (.node 1 (.leaf (-2718 : ℤ))
    (.node 1 (.leaf (-360 : ℤ))
    (.leaf (40 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24462 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (91044 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1998 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (125712 : ℤ))
    (.leaf (-5886 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-72 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (76140 : ℤ))
    (.node 1 (.leaf (-5778 : ℤ))
    (.leaf (-144 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (-1890 : ℤ))
    (.node 1 (.leaf (-72 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (13122 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (50544 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-486 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (72900 : ℤ))
    (.leaf (-1458 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (46656 : ℤ))
    (.node 1 (.leaf (-1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (11178 : ℤ)))
    (.node 1 (.leaf (-486 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (2916 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (11664 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (17496 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (11664 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (2916 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))

private def leaf0S2Numer (i j k : ℕ) : ℤ :=
  leaf0S2Data.get ((i * 5 + j) * 4 + k)

private def leaf0S2 (i j k : ℕ) : ℚ :=
  (leaf0S2Numer i j k : ℚ) / 5832

private theorem leaf0S2NumerCorrect :
    ∀ k ∈ range 8, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf0S2Numer k j h = ∑ i ∈ range 5, leaf0S1Numer k i h * leaf0W2Numer j i := by
  decide +kernel

private theorem leaf0S2Correct : Axis2Correct 7 4 3 leaf0W2 leaf0S1 leaf0S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S1Numer k i h) (leaf0W2Numer j) (leaf0S2Numer k j h) 5832 1 4
    (leaf0S2NumerCorrect k hk j hj h hh)
  norm_num only [show (5832 : ℚ)*1 = 5832 by norm_num] at he
  exact he

private def leaf0S3Data : IntTable :=
  (.node 80 (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (288 : ℤ)))
    (.node 1 (.leaf (288 : ℤ))
    (.node 1 (.leaf (96 : ℤ))
    (.leaf (272 : ℤ)))))
    (.node 2 (.node 1 (.leaf (800 : ℤ))
    (.leaf (784 : ℤ)))
    (.node 1 (.leaf (256 : ℤ))
    (.node 1 (.leaf (176 : ℤ))
    (.leaf (496 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (432 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (112 : ℤ))
    (.leaf (32 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (1080 : ℤ))
    (.leaf (3240 : ℤ)))
    (.node 1 (.leaf (3240 : ℤ))
    (.node 1 (.leaf (1080 : ℤ))
    (.leaf (3288 : ℤ)))))
    (.node 2 (.node 1 (.leaf (9664 : ℤ))
    (.leaf (9464 : ℤ)))
    (.node 1 (.leaf (3088 : ℤ))
    (.node 1 (.leaf (2896 : ℤ))
    (.leaf (8168 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (7456 : ℤ))
    (.leaf (2184 : ℤ)))
    (.node 1 (.leaf (976 : ℤ))
    (.node 1 (.leaf (2696 : ℤ))
    (.leaf (1936 : ℤ)))))
    (.node 2 (.node 1 (.leaf (400 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (424 : ℤ))
    (.node 1 (.leaf (176 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (5340 : ℤ))
    (.leaf (16020 : ℤ)))
    (.node 1 (.leaf (16020 : ℤ))
    (.node 1 (.leaf (5340 : ℤ))
    (.leaf (17316 : ℤ)))))
    (.node 2 (.node 1 (.leaf (50936 : ℤ))
    (.leaf (49924 : ℤ)))
    (.node 1 (.leaf (16304 : ℤ))
    (.node 1 (.leaf (18384 : ℤ))
    (.leaf (52240 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (48872 : ℤ))
    (.leaf (15016 : ℤ)))
    (.node 1 (.leaf (8076 : ℤ))
    (.node 1 (.leaf (22000 : ℤ))
    (.leaf (18620 : ℤ)))))
    (.node 2 (.node 1 (.leaf (4960 : ℤ))
    (.leaf (1284 : ℤ)))
    (.node 1 (.leaf (3524 : ℤ))
    (.node 1 (.leaf (2500 : ℤ))
    (.leaf (476 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (14850 : ℤ))
    (.leaf (44550 : ℤ)))
    (.node 1 (.leaf (44550 : ℤ))
    (.node 1 (.leaf (14850 : ℤ))
    (.leaf (50850 : ℤ)))))
    (.node 2 (.node 1 (.leaf (150048 : ℤ))
    (.leaf (147546 : ℤ)))
    (.node 1 (.leaf (48348 : ℤ))
    (.node 1 (.leaf (61038 : ℤ))
    (.leaf (175740 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (167830 : ℤ))
    (.leaf (53128 : ℤ)))
    (.node 1 (.leaf (31086 : ℤ))
    (.node 1 (.leaf (86688 : ℤ))
    (.leaf (78870 : ℤ)))))
    (.node 2 (.node 1 (.leaf (23436 : ℤ))
    (.leaf (5760 : ℤ)))
    (.node 1 (.leaf (15582 : ℤ))
    (.node 1 (.leaf (13172 : ℤ))
    (.leaf (3502 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24759 : ℤ))
    (.leaf (74277 : ℤ)))
    (.node 1 (.leaf (74277 : ℤ))
    (.node 1 (.leaf (24759 : ℤ))
    (.leaf (88722 : ℤ)))))
    (.node 2 (.node 1 (.leaf (262980 : ℤ))
    (.leaf (259794 : ℤ)))
    (.node 1 (.leaf (85536 : ℤ))
    (.node 1 (.leaf (115668 : ℤ))
    (.leaf (337626 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (327936 : ℤ))
    (.leaf (105978 : ℤ)))
    (.node 1 (.leaf (65070 : ℤ))
    (.node 1 (.leaf (186300 : ℤ))
    (.leaf (176718 : ℤ)))))
    (.node 2 (.node 1 (.leaf (55528 : ℤ))
    (.leaf (13365 : ℤ)))
    (.node 1 (.leaf (37377 : ℤ))
    (.node 1 (.leaf (34299 : ℤ))
    (.leaf (10327 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (24462 : ℤ))
    (.leaf (73386 : ℤ)))
    (.node 1 (.leaf (73386 : ℤ))
    (.node 1 (.leaf (24462 : ℤ))
    (.leaf (91044 : ℤ)))))
    (.node 2 (.node 1 (.leaf (271134 : ℤ))
    (.leaf (269136 : ℤ)))
    (.node 1 (.leaf (89046 : ℤ))
    (.node 1 (.leaf (125712 : ℤ))
    (.leaf (371250 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (365292 : ℤ))
    (.leaf (119754 : ℤ)))
    (.node 1 (.leaf (76140 : ℤ))
    (.node 1 (.leaf (222642 : ℤ))
    (.leaf (216720 : ℤ)))))
    (.node 2 (.node 1 (.leaf (70218 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (49140 : ℤ))
    (.node 1 (.leaf (47178 : ℤ))
    (.leaf (15048 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (13122 : ℤ))
    (.leaf (39366 : ℤ)))
    (.node 1 (.leaf (39366 : ℤ))
    (.node 1 (.leaf (13122 : ℤ))
    (.leaf (50544 : ℤ)))))
    (.node 2 (.node 1 (.leaf (151146 : ℤ))
    (.leaf (150660 : ℤ)))
    (.node 1 (.leaf (50058 : ℤ))
    (.node 1 (.leaf (72900 : ℤ))
    (.leaf (217242 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (215784 : ℤ))
    (.leaf (71442 : ℤ)))
    (.node 1 (.leaf (46656 : ℤ))
    (.node 1 (.leaf (138510 : ℤ))
    (.leaf (137052 : ℤ)))))
    (.node 2 (.node 1 (.leaf (45198 : ℤ))
    (.leaf (11178 : ℤ)))
    (.node 1 (.leaf (33048 : ℤ))
    (.node 1 (.leaf (32562 : ℤ))
    (.leaf (10692 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (2916 : ℤ))
    (.leaf (8748 : ℤ)))
    (.node 1 (.leaf (8748 : ℤ))
    (.node 1 (.leaf (2916 : ℤ))
    (.leaf (11664 : ℤ)))))
    (.node 2 (.node 1 (.leaf (34992 : ℤ))
    (.leaf (34992 : ℤ)))
    (.node 1 (.leaf (11664 : ℤ))
    (.node 1 (.leaf (17496 : ℤ))
    (.leaf (52488 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (52488 : ℤ))
    (.leaf (17496 : ℤ)))
    (.node 1 (.leaf (11664 : ℤ))
    (.node 1 (.leaf (34992 : ℤ))
    (.leaf (34992 : ℤ)))))
    (.node 2 (.node 1 (.leaf (11664 : ℤ))
    (.leaf (2916 : ℤ)))
    (.node 1 (.leaf (8748 : ℤ))
    (.node 1 (.leaf (8748 : ℤ))
    (.leaf (2916 : ℤ))))))))))

private def leaf0S3Numer (i j k : ℕ) : ℤ :=
  leaf0S3Data.get ((i * 5 + j) * 4 + k)

private def leaf0S3 (i j k : ℕ) : ℚ :=
  (leaf0S3Numer i j k : ℚ) / 5832

private theorem leaf0S3NumerCorrect :
    ∀ k ∈ range 8, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf0S3Numer k j h = ∑ i ∈ range 4, leaf0S2Numer k j i * leaf0W3Numer h i := by
  decide +kernel

private theorem leaf0S3Correct : Axis3Correct 7 4 3 leaf0W3 leaf0S2 leaf0S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S2Numer k j i) (leaf0W3Numer h) (leaf0S3Numer k j h) 5832 1 3
    (leaf0S3NumerCorrect k hk j hj h hh)
  norm_num only [show (5832 : ℚ)*1 = 5832 by norm_num] at he
  exact he

private theorem leaf0NumerSigns :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf0S3Numer i j k := by
  decide +kernel

private theorem leaf0Signs :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf0S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf0NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf0Certificate :
    ∀ i ∈ range 8, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 leaf0Coeff 7 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 leaf0Coeff leaf0S1 leaf0S2 leaf0S3 7 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) leaf0W1 leaf0W2 leaf0W3
    leaf0W1Correct leaf0W2Correct leaf0W3Correct
    (axis1Correct_of_table leaf0InputCorrect leaf0S1Correct) leaf0S2Correct leaf0S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf0Signs i hi j hj k hk

private theorem leaf0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) :
    0 ≤ highTLTarget x d u := by
  have h : 0 ≤ msum leaf0Coeff 7 4 3 x d u :=
    msum_nonneg_on_box leaf0Coeff 7 4 3
      (by norm_num) (by norm_num) (by norm_num)
      (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith)
      (by push_cast; linarith) (by push_cast; linarith) leaf0Certificate
  rwa [leaf0Identity] at h

private theorem region0 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highTLTarget x d u := by
  have hb := leaf0 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
  push_cast at hb
  linarith only [hb]

theorem junctionFaceHTL {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highTLTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 

end Taeyoung.Methods.Atlas126
