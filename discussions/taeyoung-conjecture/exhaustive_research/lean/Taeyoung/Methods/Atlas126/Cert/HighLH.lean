import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate HLH.
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
  ⟨0, 0, 2, (81 : ℤ)⟩,
  ⟨1, 0, 1, (54 : ℤ)⟩,
  ⟨1, 0, 2, (-81 : ℤ)⟩,
  ⟨1, 0, 3, (54 : ℤ)⟩,
  ⟨1, 1, 0, (243 : ℤ)⟩,
  ⟨1, 1, 1, (270 : ℤ)⟩,
  ⟨1, 1, 2, (135 : ℤ)⟩,
  ⟨1, 2, 0, (-486 : ℤ)⟩,
  ⟨1, 2, 1, (-324 : ℤ)⟩,
  ⟨1, 3, 0, (243 : ℤ)⟩,
  ⟨2, 0, 0, (9 : ℤ)⟩,
  ⟨2, 0, 1, (-36 : ℤ)⟩,
  ⟨2, 0, 2, (81 : ℤ)⟩,
  ⟨2, 0, 3, (-54 : ℤ)⟩,
  ⟨2, 1, 0, (-243 : ℤ)⟩,
  ⟨2, 1, 1, (-252 : ℤ)⟩,
  ⟨2, 1, 2, (-189 : ℤ)⟩,
  ⟨2, 1, 3, (54 : ℤ)⟩,
  ⟨2, 2, 0, (369 : ℤ)⟩,
  ⟨2, 2, 1, (126 : ℤ)⟩,
  ⟨2, 2, 2, (-162 : ℤ)⟩,
  ⟨2, 3, 0, (-45 : ℤ)⟩,
  ⟨2, 3, 1, (162 : ℤ)⟩,
  ⟨2, 4, 0, (-90 : ℤ)⟩,
  ⟨3, 0, 0, (-3 : ℤ)⟩,
  ⟨3, 0, 1, (24 : ℤ)⟩,
  ⟨3, 0, 2, (-39 : ℤ)⟩,
  ⟨3, 0, 3, (18 : ℤ)⟩,
  ⟨3, 1, 0, (87 : ℤ)⟩,
  ⟨3, 1, 1, (42 : ℤ)⟩,
  ⟨3, 1, 2, (135 : ℤ)⟩,
  ⟨3, 1, 3, (-54 : ℤ)⟩,
  ⟨3, 2, 0, (-105 : ℤ)⟩,
  ⟨3, 2, 1, (-12 : ℤ)⟩,
  ⟨3, 2, 2, (108 : ℤ)⟩,
  ⟨3, 3, 0, (-39 : ℤ)⟩,
  ⟨3, 3, 1, (-54 : ℤ)⟩,
  ⟨3, 4, 0, (60 : ℤ)⟩,
  ⟨4, 0, 0, (2 : ℤ)⟩,
  ⟨4, 0, 1, (-6 : ℤ)⟩,
  ⟨4, 0, 2, (6 : ℤ)⟩,
  ⟨4, 0, 3, (-2 : ℤ)⟩,
  ⟨4, 1, 0, (-17 : ℤ)⟩,
  ⟨4, 1, 1, (22 : ℤ)⟩,
  ⟨4, 1, 2, (-47 : ℤ)⟩,
  ⟨4, 1, 3, (18 : ℤ)⟩,
  ⟨4, 2, 0, (-6 : ℤ)⟩,
  ⟨4, 2, 1, (-16 : ℤ)⟩,
  ⟨4, 2, 2, (-18 : ℤ)⟩,
  ⟨4, 3, 0, (55 : ℤ)⟩,
  ⟨4, 4, 0, (-34 : ℤ)⟩,
  ⟨5, 1, 0, (2 : ℤ)⟩,
  ⟨5, 1, 1, (-6 : ℤ)⟩,
  ⟨5, 1, 2, (6 : ℤ)⟩,
  ⟨5, 1, 3, (-2 : ℤ)⟩,
  ⟨5, 2, 0, (2 : ℤ)⟩,
  ⟨5, 2, 1, (6 : ℤ)⟩,
  ⟨5, 3, 0, (-10 : ℤ)⟩,
  ⟨5, 4, 0, (6 : ℤ)⟩]

private def leaf0CoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff leaf0CoeffTerms i j k

private def leaf0Coeff (i j k : ℕ) : ℚ :=
  (leaf0CoeffNumer i j k : ℚ) / 729

private theorem leaf0CoeffExpansion (x d u : ℝ) :
    msum leaf0Coeff 5 4 3 x d u = sparseEval (leaf0CoeffTerms.map IntTerm.toRat) x d u / 729 := by
  have he : ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0CoeffNumer i j k = intSparseCoeff leaf0CoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ leaf0CoeffTerms, t.i ≤ 5 ∧ t.j ≤ 4 ∧ t.k ≤ 3 := by decide +kernel
  exact msum_intSparse_scaled leaf0CoeffNumer leaf0CoeffTerms 729 5 4 3 he hb x d u

private theorem leaf0Identity (x d u : ℝ) :
    msum leaf0Coeff 5 4 3 x d u = highLHTarget x d u := by
  rw [leaf0CoeffExpansion]
  simp only [sparseEval, IntTerm.toRat, leaf0CoeffTerms, highLHTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

private def leaf0InputData : IntTable :=
  (.node 60 (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (81 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (54 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-81 : ℤ))
    (.leaf (54 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (270 : ℤ))))
    (.node 2 (.node 1 (.leaf (135 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-486 : ℤ))
    (.leaf (-324 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (243 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (9 : ℤ))))
    (.node 2 (.node 1 (.leaf (-36 : ℤ))
    (.leaf (81 : ℤ)))
    (.node 1 (.leaf (-54 : ℤ))
    (.leaf (-243 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (-252 : ℤ))
    (.node 1 (.leaf (-189 : ℤ))
    (.leaf (54 : ℤ))))
    (.node 2 (.node 1 (.leaf (369 : ℤ))
    (.leaf (126 : ℤ)))
    (.node 1 (.leaf (-162 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-45 : ℤ))
    (.leaf (162 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-90 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (-3 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (-39 : ℤ))))
    (.node 2 (.node 1 (.leaf (18 : ℤ))
    (.leaf (87 : ℤ)))
    (.node 1 (.leaf (42 : ℤ))
    (.leaf (135 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-54 : ℤ))
    (.leaf (-105 : ℤ)))
    (.node 1 (.leaf (-12 : ℤ))
    (.leaf (108 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-39 : ℤ)))
    (.node 1 (.leaf (-54 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (60 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (-6 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (6 : ℤ))
    (.leaf (-2 : ℤ)))
    (.node 1 (.leaf (-17 : ℤ))
    (.leaf (22 : ℤ))))
    (.node 2 (.node 1 (.leaf (-47 : ℤ))
    (.leaf (18 : ℤ)))
    (.node 1 (.leaf (-6 : ℤ))
    (.leaf (-16 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (55 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-34 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (2 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (-6 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (-2 : ℤ))))
    (.node 2 (.node 1 (.leaf (2 : ℤ))
    (.leaf (6 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-10 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (6 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf0InputNumer (i j k : ℕ) : ℤ :=
  leaf0InputData.get ((i * 5 + j) * 4 + k)

private def leaf0Input (i j k : ℕ) : ℚ :=
  (leaf0InputNumer i j k : ℚ) / 729

private theorem leaf0InputNumerCorrect :
    ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0InputNumer i j k = leaf0CoeffNumer i j k := by
  decide +kernel

private theorem leaf0InputCorrect :
    ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0Input i j k = leaf0Coeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/729)
    (leaf0InputNumerCorrect i hi j hj k hk)

private def leaf0W1Data : IntTable :=
  (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (5 : ℤ))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (10 : ℤ))))
    (.node 2 (.node 1 (.leaf (4 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (10 : ℤ))
    (.leaf (6 : ℤ)))
    (.node 1 (.leaf (3 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (5 : ℤ))
    (.node 1 (.leaf (4 : ℤ))
    (.leaf (3 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))))))

private def leaf0W1Numer (k i : ℕ) : ℤ :=
  leaf0W1Data.get (k * 6 + i)

private def leaf0W1 (k i : ℕ) : ℚ :=
  (leaf0W1Numer k i : ℚ) / 1

private theorem leaf0W1NumerCorrect :
    ∀ k ∈ range 6, ∀ i ∈ range 6,
      leaf0W1Numer k i = intTransWeight 5 (0) 1 1 k i := by
  decide +kernel

private theorem leaf0W1Correct : WeightsCorrect 5 (0 : ℚ) (1 : ℚ) leaf0W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 5 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf0W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^5 = 1 by norm_num,
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
  (.node 60 (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (81 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (54 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (324 : ℤ))
    (.leaf (54 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (270 : ℤ))))
    (.node 2 (.node 1 (.leaf (135 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-486 : ℤ))
    (.leaf (-324 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (243 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (9 : ℤ))))
    (.node 2 (.node 1 (.leaf (180 : ℤ))
    (.leaf (567 : ℤ)))
    (.node 1 (.leaf (162 : ℤ))
    (.leaf (729 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (828 : ℤ))
    (.node 1 (.leaf (351 : ℤ))
    (.leaf (54 : ℤ))))
    (.node 2 (.node 1 (.leaf (-1575 : ℤ))
    (.leaf (-1170 : ℤ)))
    (.node 1 (.leaf (-162 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (927 : ℤ))
    (.leaf (162 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-90 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (24 : ℤ))
    (.node 1 (.leaf (240 : ℤ))
    (.leaf (528 : ℤ))))
    (.node 2 (.node 1 (.leaf (180 : ℤ))
    (.leaf (816 : ℤ)))
    (.node 1 (.leaf (906 : ℤ))
    (.leaf (378 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (108 : ℤ))
    (.leaf (-1914 : ℤ)))
    (.node 1 (.leaf (-1578 : ℤ))
    (.leaf (-378 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1284 : ℤ)))
    (.node 1 (.leaf (432 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-210 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (23 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (252 : ℤ))
    (.leaf (88 : ℤ)))
    (.node 1 (.leaf (400 : ℤ))
    (.leaf (430 : ℤ))))
    (.node 2 (.node 1 (.leaf (196 : ℤ))
    (.leaf (72 : ℤ)))
    (.node 1 (.leaf (-1053 : ℤ))
    (.leaf (-958 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (-288 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (814 : ℤ))))
    (.node 2 (.node 1 (.leaf (378 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-184 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (36 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (72 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (76 : ℤ))
    (.node 1 (.leaf (40 : ℤ))
    (.leaf (16 : ℤ))))
    (.node 2 (.node 1 (.leaf (-226 : ℤ))
    (.leaf (-220 : ℤ)))
    (.node 1 (.leaf (-72 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (204 : ℤ))
    (.leaf (108 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf0S1Numer (i j k : ℕ) : ℤ :=
  leaf0S1Data.get ((i * 5 + j) * 4 + k)

private def leaf0S1 (i j k : ℕ) : ℚ :=
  (leaf0S1Numer i j k : ℚ) / 729

private theorem leaf0S1NumerCorrect :
    ∀ h ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf0S1Numer h j k = ∑ i ∈ range 6, leaf0InputNumer i j k * leaf0W1Numer h i := by
  decide +kernel

private theorem leaf0S1Correct : Axis1Correct 5 4 3 leaf0W1 leaf0Input leaf0S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => leaf0InputNumer i j k) (leaf0W1Numer h) (leaf0S1Numer h j k) 729 1 5
    (leaf0S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf0S2Data : IntTable :=
  (.node 60 (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (81 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (324 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (486 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (324 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (81 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (54 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (324 : ℤ))
    (.leaf (54 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (486 : ℤ))))
    (.node 2 (.node 1 (.leaf (1431 : ℤ))
    (.leaf (216 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (810 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (2349 : ℤ))
    (.node 1 (.leaf (324 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (378 : ℤ))
    (.leaf (1701 : ℤ)))
    (.node 1 (.leaf (216 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (459 : ℤ)))
    (.node 1 (.leaf (54 : ℤ))
    (.leaf (9 : ℤ))))
    (.node 2 (.node 1 (.leaf (180 : ℤ))
    (.leaf (567 : ℤ)))
    (.node 1 (.leaf (162 : ℤ))
    (.leaf (765 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (1548 : ℤ))
    (.node 1 (.leaf (2619 : ℤ))
    (.leaf (702 : ℤ))))
    (.node 2 (.node 1 (.leaf (666 : ℤ))
    (.leaf (2394 : ℤ)))
    (.node 1 (.leaf (4293 : ℤ))
    (.leaf (1134 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1026 : ℤ)))
    (.node 1 (.leaf (2997 : ℤ))
    (.leaf (810 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (756 : ℤ))
    (.leaf (216 : ℤ))))))))
    (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (24 : ℤ))
    (.node 1 (.leaf (240 : ℤ))
    (.leaf (528 : ℤ))))
    (.node 2 (.node 1 (.leaf (180 : ℤ))
    (.leaf (912 : ℤ)))
    (.node 1 (.leaf (1866 : ℤ))
    (.leaf (2490 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (828 : ℤ))
    (.leaf (678 : ℤ)))
    (.node 1 (.leaf (2580 : ℤ))
    (.leaf (3924 : ℤ))))
    (.node 2 (.node 1 (.leaf (1404 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (954 : ℤ))
    (.leaf (2490 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (1044 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (528 : ℤ))
    (.leaf (288 : ℤ)))
    (.node 1 (.leaf (23 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (252 : ℤ))
    (.leaf (88 : ℤ)))
    (.node 1 (.leaf (492 : ℤ))
    (.leaf (1030 : ℤ))))
    (.node 2 (.node 1 (.leaf (1204 : ℤ))
    (.leaf (424 : ℤ)))
    (.node 1 (.leaf (285 : ℤ))
    (.leaf (1232 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (1812 : ℤ))
    (.node 1 (.leaf (744 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (352 : ℤ))
    (.leaf (1020 : ℤ)))
    (.node 1 (.leaf (568 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (160 : ℤ)))
    (.node 1 (.leaf (160 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (36 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (104 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (220 : ℤ))
    (.node 1 (.leaf (232 : ℤ))
    (.leaf (80 : ℤ))))
    (.node 2 (.node 1 (.leaf (38 : ℤ))
    (.leaf (224 : ℤ)))
    (.node 1 (.leaf (336 : ℤ))
    (.leaf (144 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (40 : ℤ)))
    (.node 1 (.leaf (168 : ℤ))
    (.leaf (112 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (32 : ℤ)))))))))

private def leaf0S2Numer (i j k : ℕ) : ℤ :=
  leaf0S2Data.get ((i * 5 + j) * 4 + k)

private def leaf0S2 (i j k : ℕ) : ℚ :=
  (leaf0S2Numer i j k : ℚ) / 729

private theorem leaf0S2NumerCorrect :
    ∀ k ∈ range 6, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf0S2Numer k j h = ∑ i ∈ range 5, leaf0S1Numer k i h * leaf0W2Numer j i := by
  decide +kernel

private theorem leaf0S2Correct : Axis2Correct 5 4 3 leaf0W2 leaf0S1 leaf0S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S1Numer k i h) (leaf0W2Numer j) (leaf0S2Numer k j h) 729 1 4
    (leaf0S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf0S3Data : IntTable :=
  (.node 60 (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (81 : ℤ))))
    (.node 2 (.node 1 (.leaf (81 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (324 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (324 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (486 : ℤ))))
    (.node 2 (.node 1 (.leaf (486 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (324 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (324 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (81 : ℤ))
    (.leaf (81 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (54 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (432 : ℤ))
    (.leaf (432 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (1215 : ℤ))))
    (.node 2 (.node 1 (.leaf (3132 : ℤ))
    (.leaf (2376 : ℤ)))
    (.node 1 (.leaf (243 : ℤ))
    (.leaf (1539 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (4698 : ℤ))
    (.node 1 (.leaf (3726 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (378 : ℤ))
    (.leaf (2457 : ℤ)))
    (.node 1 (.leaf (2295 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (459 : ℤ)))
    (.node 1 (.leaf (513 : ℤ))
    (.leaf (9 : ℤ))))
    (.node 2 (.node 1 (.leaf (207 : ℤ))
    (.leaf (954 : ℤ)))
    (.node 1 (.leaf (918 : ℤ))
    (.leaf (765 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (3843 : ℤ))
    (.node 1 (.leaf (8010 : ℤ))
    (.leaf (5634 : ℤ))))
    (.node 2 (.node 1 (.leaf (666 : ℤ))
    (.leaf (4392 : ℤ)))
    (.node 1 (.leaf (11079 : ℤ))
    (.leaf (8487 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1026 : ℤ)))
    (.node 1 (.leaf (5049 : ℤ))
    (.leaf (4833 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (756 : ℤ))
    (.leaf (972 : ℤ))))))))
    (.node 30 (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (24 : ℤ))
    (.node 1 (.leaf (312 : ℤ))
    (.leaf (1080 : ℤ))))
    (.node 2 (.node 1 (.leaf (972 : ℤ))
    (.leaf (912 : ℤ)))
    (.node 1 (.leaf (4602 : ℤ))
    (.leaf (8958 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (6096 : ℤ))
    (.leaf (678 : ℤ)))
    (.node 1 (.leaf (4614 : ℤ))
    (.leaf (11118 : ℤ))))
    (.node 2 (.node 1 (.leaf (8586 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (954 : ℤ))
    (.leaf (4398 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (4488 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (528 : ℤ))
    (.leaf (816 : ℤ)))
    (.node 1 (.leaf (23 : ℤ))
    (.leaf (219 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (621 : ℤ))
    (.leaf (513 : ℤ)))
    (.node 1 (.leaf (492 : ℤ))
    (.leaf (2506 : ℤ))))
    (.node 2 (.node 1 (.leaf (4740 : ℤ))
    (.leaf (3150 : ℤ)))
    (.node 1 (.leaf (285 : ℤ))
    (.leaf (2087 : ℤ)))))))
    (.node 15 (.node 7 (.node 3 (.node 1 (.leaf (5131 : ℤ))
    (.node 1 (.leaf (4073 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (352 : ℤ))
    (.leaf (1724 : ℤ)))
    (.node 1 (.leaf (1940 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (160 : ℤ)))
    (.node 1 (.leaf (320 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (60 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (104 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (532 : ℤ))
    (.node 1 (.leaf (984 : ℤ))
    (.leaf (636 : ℤ))))
    (.node 2 (.node 1 (.leaf (38 : ℤ))
    (.leaf (338 : ℤ)))
    (.node 1 (.leaf (898 : ℤ))
    (.leaf (742 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (40 : ℤ)))
    (.node 1 (.leaf (248 : ℤ))
    (.leaf (320 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (48 : ℤ)))))))))

private def leaf0S3Numer (i j k : ℕ) : ℤ :=
  leaf0S3Data.get ((i * 5 + j) * 4 + k)

private def leaf0S3 (i j k : ℕ) : ℚ :=
  (leaf0S3Numer i j k : ℚ) / 729

private theorem leaf0S3NumerCorrect :
    ∀ k ∈ range 6, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf0S3Numer k j h = ∑ i ∈ range 4, leaf0S2Numer k j i * leaf0W3Numer h i := by
  decide +kernel

private theorem leaf0S3Correct : Axis3Correct 5 4 3 leaf0W3 leaf0S2 leaf0S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S2Numer k j i) (leaf0W3Numer h) (leaf0S3Numer k j h) 729 1 3
    (leaf0S3NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private theorem leaf0NumerSigns :
    ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf0S3Numer i j k := by
  decide +kernel

private theorem leaf0Signs :
    ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf0S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf0NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf0Certificate :
    ∀ i ∈ range 6, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 leaf0Coeff 5 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 leaf0Coeff leaf0S1 leaf0S2 leaf0S3 5 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) leaf0W1 leaf0W2 leaf0W3
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
    0 ≤ highLHTarget x d u := by
  have h : 0 ≤ msum leaf0Coeff 5 4 3 x d u :=
    msum_nonneg_on_box leaf0Coeff 5 4 3
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
    0 ≤ highLHTarget x d u := by
  have hb := leaf0 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
  push_cast at hb
  linarith only [hb]

theorem junctionFaceHLH {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highLHTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 

end Taeyoung.Methods.Atlas126
