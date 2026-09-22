import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate HRL.
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
  ⟨0, 3, 0, (6561 : ℤ)⟩,
  ⟨0, 4, 0, (-3645 : ℤ)⟩,
  ⟨1, 2, 0, (4374 : ℤ)⟩,
  ⟨1, 3, 0, (-30618 : ℤ)⟩,
  ⟨1, 4, 0, (17010 : ℤ)⟩,
  ⟨2, 2, 0, (-12312 : ℤ)⟩,
  ⟨2, 2, 1, (-1944 : ℤ)⟩,
  ⟨2, 3, 0, (56457 : ℤ)⟩,
  ⟨2, 3, 1, (1458 : ℤ)⟩,
  ⟨2, 4, 0, (-32967 : ℤ)⟩,
  ⟨3, 1, 0, (1512 : ℤ)⟩,
  ⟨3, 1, 1, (-1512 : ℤ)⟩,
  ⟨3, 2, 0, (10962 : ℤ)⟩,
  ⟨3, 2, 1, (6912 : ℤ)⟩,
  ⟨3, 3, 0, (-53460 : ℤ)⟩,
  ⟨3, 3, 1, (-4374 : ℤ)⟩,
  ⟨3, 4, 0, (34911 : ℤ)⟩,
  ⟨4, 0, 0, (72 : ℤ)⟩,
  ⟨4, 0, 1, (-144 : ℤ)⟩,
  ⟨4, 0, 2, (72 : ℤ)⟩,
  ⟨4, 1, 0, (-2772 : ℤ)⟩,
  ⟨4, 1, 1, (2592 : ℤ)⟩,
  ⟨4, 1, 2, (180 : ℤ)⟩,
  ⟨4, 2, 0, (-3582 : ℤ)⟩,
  ⟨4, 2, 1, (-7380 : ℤ)⟩,
  ⟨4, 2, 2, (-324 : ℤ)⟩,
  ⟨4, 3, 0, (29781 : ℤ)⟩,
  ⟨4, 3, 1, (4374 : ℤ)⟩,
  ⟨4, 4, 0, (-22599 : ℤ)⟩,
  ⟨5, 0, 0, (96 : ℤ)⟩,
  ⟨5, 0, 1, (-192 : ℤ)⟩,
  ⟨5, 0, 2, (96 : ℤ)⟩,
  ⟨5, 1, 0, (792 : ℤ)⟩,
  ⟨5, 1, 1, (-48 : ℤ)⟩,
  ⟨5, 1, 2, (-744 : ℤ)⟩,
  ⟨5, 2, 0, (1908 : ℤ)⟩,
  ⟨5, 2, 1, (1692 : ℤ)⟩,
  ⟨5, 2, 2, (648 : ℤ)⟩,
  ⟨5, 3, 0, (-11664 : ℤ)⟩,
  ⟨5, 3, 1, (-1458 : ℤ)⟩,
  ⟨5, 4, 0, (9396 : ℤ)⟩,
  ⟨6, 0, 0, (-200 : ℤ)⟩,
  ⟨6, 0, 1, (416 : ℤ)⟩,
  ⟨6, 0, 2, (-232 : ℤ)⟩,
  ⟨6, 0, 3, (16 : ℤ)⟩,
  ⟨6, 1, 0, (588 : ℤ)⟩,
  ⟨6, 1, 1, (-1176 : ℤ)⟩,
  ⟨6, 1, 2, (564 : ℤ)⟩,
  ⟨6, 1, 3, (24 : ℤ)⟩,
  ⟨6, 2, 0, (-1602 : ℤ)⟩,
  ⟨6, 2, 1, (828 : ℤ)⟩,
  ⟨6, 2, 2, (-324 : ℤ)⟩,
  ⟨6, 3, 0, (3321 : ℤ)⟩,
  ⟨6, 4, 0, (-2349 : ℤ)⟩,
  ⟨7, 0, 0, (32 : ℤ)⟩,
  ⟨7, 0, 1, (-48 : ℤ)⟩,
  ⟨7, 0, 3, (16 : ℤ)⟩,
  ⟨7, 1, 0, (-120 : ℤ)⟩,
  ⟨7, 1, 1, (144 : ℤ)⟩,
  ⟨7, 1, 3, (-24 : ℤ)⟩,
  ⟨7, 2, 0, (252 : ℤ)⟩,
  ⟨7, 2, 1, (-108 : ℤ)⟩,
  ⟨7, 3, 0, (-378 : ℤ)⟩,
  ⟨7, 4, 0, (243 : ℤ)⟩]

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
    msum leaf0Coeff 7 4 3 x d u = highRLTarget x d u := by
  rw [leaf0CoeffExpansion]
  simp only [sparseEval, IntTerm.toRat, leaf0CoeffTerms, highRLTarget, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

private def leaf0InputData : IntTable :=
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
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-30618 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-12312 : ℤ))
    (.leaf (-1944 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (56457 : ℤ))
    (.node 1 (.leaf (1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-32967 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1512 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1512 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (10962 : ℤ))
    (.leaf (6912 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-53460 : ℤ))
    (.node 1 (.leaf (-4374 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (34911 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (72 : ℤ))
    (.leaf (-144 : ℤ)))
    (.node 1 (.leaf (72 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2772 : ℤ)))))
    (.node 2 (.node 1 (.leaf (2592 : ℤ))
    (.leaf (180 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-3582 : ℤ))
    (.leaf (-7380 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-324 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (29781 : ℤ))
    (.node 1 (.leaf (4374 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-22599 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (96 : ℤ))
    (.leaf (-192 : ℤ)))
    (.node 1 (.leaf (96 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (792 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-48 : ℤ))
    (.leaf (-744 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1908 : ℤ))
    (.leaf (1692 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (648 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-11664 : ℤ))
    (.node 1 (.leaf (-1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (9396 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (-200 : ℤ))
    (.leaf (416 : ℤ)))
    (.node 1 (.leaf (-232 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (588 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1176 : ℤ))
    (.leaf (564 : ℤ)))
    (.node 1 (.leaf (24 : ℤ))
    (.node 1 (.leaf (-1602 : ℤ))
    (.leaf (828 : ℤ))))))
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
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (32 : ℤ))
    (.leaf (-48 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (-120 : ℤ)))))
    (.node 2 (.node 1 (.leaf (144 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-24 : ℤ))
    (.node 1 (.leaf (252 : ℤ))
    (.leaf (-108 : ℤ))))))
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
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (15309 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-8505 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (13932 : ℤ))
    (.leaf (-1944 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (10530 : ℤ))
    (.node 1 (.leaf (1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-7452 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1512 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1512 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (15012 : ℤ))
    (.leaf (-2808 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-810 : ℤ))
    (.node 1 (.leaf (2916 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2349 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (72 : ℤ))
    (.leaf (-144 : ℤ)))
    (.node 1 (.leaf (72 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3276 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-3456 : ℤ))
    (.leaf (180 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4626 : ℤ))
    (.leaf (828 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-324 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-2214 : ℤ))
    (.node 1 (.leaf (1458 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (312 : ℤ))
    (.leaf (-624 : ℤ)))
    (.node 1 (.leaf (312 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1548 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1344 : ℤ))
    (.leaf (-204 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-576 : ℤ))
    (.leaf (1584 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-324 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (208 : ℤ))
    (.leaf (-400 : ℤ)))
    (.node 1 (.leaf (176 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (-96 : ℤ)))))
    (.node 2 (.node 1 (.leaf (456 : ℤ))
    (.leaf (-384 : ℤ)))
    (.node 1 (.leaf (24 : ℤ))
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
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (-64 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
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
    (.leaf (2916 : ℤ)))
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
    (.leaf (0 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (24057 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (11178 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (13932 : ℤ))
    (.leaf (-1944 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (38394 : ℤ))
    (.node 1 (.leaf (-2430 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (-486 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1512 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1512 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (19548 : ℤ))
    (.leaf (-7344 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (33750 : ℤ))
    (.node 1 (.leaf (-7236 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (13365 : ℤ)))
    (.node 1 (.leaf (-1404 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (72 : ℤ))
    (.leaf (-144 : ℤ)))
    (.node 1 (.leaf (72 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3564 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-4032 : ℤ))
    (.leaf (468 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (14886 : ℤ))
    (.leaf (-10404 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (648 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (17154 : ℤ))
    (.node 1 (.leaf (-7830 : ℤ))
    (.leaf (180 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (5760 : ℤ)))
    (.node 1 (.leaf (-1314 : ℤ))
    (.node 1 (.leaf (-72 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (312 : ℤ))
    (.leaf (-624 : ℤ)))
    (.node 1 (.leaf (312 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (2796 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-3840 : ℤ))
    (.leaf (1044 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (5940 : ℤ))
    (.leaf (-6192 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (936 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (4740 : ℤ))
    (.node 1 (.leaf (-3360 : ℤ))
    (.leaf (-12 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1284 : ℤ)))
    (.node 1 (.leaf (-384 : ℤ))
    (.node 1 (.leaf (-216 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (208 : ℤ))
    (.leaf (-400 : ℤ)))
    (.node 1 (.leaf (176 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (736 : ℤ)))))
    (.node 2 (.node 1 (.leaf (-1144 : ℤ))
    (.leaf (320 : ℤ)))
    (.node 1 (.leaf (88 : ℤ))
    (.node 1 (.leaf (960 : ℤ))
    (.leaf (-1032 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-96 : ℤ))
    (.leaf (168 : ℤ)))
    (.node 1 (.leaf (544 : ℤ))
    (.node 1 (.leaf (-232 : ℤ))
    (.leaf (-448 : ℤ)))))
    (.node 2 (.node 1 (.leaf (136 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (56 : ℤ))
    (.node 1 (.leaf (-208 : ℤ))
    (.leaf (40 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (-64 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (128 : ℤ))
    (.leaf (-256 : ℤ)))
    (.node 1 (.leaf (128 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (192 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (-384 : ℤ))
    (.leaf (192 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (-256 : ℤ)))))
    (.node 2 (.node 1 (.leaf (128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (-64 : ℤ))
    (.leaf (32 : ℤ))))))))))

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
    (.node 1 (.leaf (19683 : ℤ))
    (.leaf (19683 : ℤ)))))
    (.node 2 (.node 1 (.leaf (6561 : ℤ))
    (.leaf (2916 : ℤ)))
    (.node 1 (.leaf (8748 : ℤ))
    (.node 1 (.leaf (8748 : ℤ))
    (.leaf (2916 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4374 : ℤ))
    (.leaf (13122 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (13122 : ℤ))
    (.leaf (4374 : ℤ)))
    (.node 1 (.leaf (24057 : ℤ))
    (.node 1 (.leaf (72171 : ℤ))
    (.leaf (72171 : ℤ)))))
    (.node 2 (.node 1 (.leaf (24057 : ℤ))
    (.leaf (11178 : ℤ)))
    (.node 1 (.leaf (33534 : ℤ))
    (.node 1 (.leaf (33534 : ℤ))
    (.leaf (11178 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (13932 : ℤ))
    (.leaf (39852 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (37908 : ℤ))
    (.leaf (11988 : ℤ)))
    (.node 1 (.leaf (38394 : ℤ))
    (.node 1 (.leaf (112752 : ℤ))
    (.leaf (110322 : ℤ)))))
    (.node 2 (.node 1 (.leaf (35964 : ℤ))
    (.leaf (17010 : ℤ)))
    (.node 1 (.leaf (50544 : ℤ))
    (.node 1 (.leaf (50058 : ℤ))
    (.leaf (16524 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1512 : ℤ)))))
    (.node 2 (.node 1 (.leaf (3024 : ℤ))
    (.leaf (1512 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (19548 : ℤ))
    (.leaf (51300 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (43956 : ℤ))
    (.leaf (12204 : ℤ)))
    (.node 1 (.leaf (33750 : ℤ))
    (.node 1 (.leaf (94014 : ℤ))
    (.leaf (86778 : ℤ)))))
    (.node 2 (.node 1 (.leaf (26514 : ℤ))
    (.leaf (13365 : ℤ)))
    (.node 1 (.leaf (38691 : ℤ))
    (.node 1 (.leaf (37287 : ℤ))
    (.leaf (11961 : ℤ)))))))))
    (.node 40 (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (72 : ℤ))
    (.leaf (72 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3564 : ℤ)))))
    (.node 2 (.node 1 (.leaf (6660 : ℤ))
    (.leaf (3096 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (14886 : ℤ))
    (.leaf (34254 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (24498 : ℤ))
    (.leaf (5130 : ℤ)))
    (.node 1 (.leaf (17154 : ℤ))
    (.node 1 (.leaf (43632 : ℤ))
    (.leaf (35982 : ℤ)))))
    (.node 2 (.node 1 (.leaf (9504 : ℤ))
    (.leaf (5760 : ℤ)))
    (.node 1 (.leaf (15966 : ℤ))
    (.node 1 (.leaf (14580 : ℤ))
    (.leaf (4374 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (312 : ℤ))
    (.leaf (312 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (2796 : ℤ)))))
    (.node 2 (.node 1 (.leaf (4548 : ℤ))
    (.leaf (1752 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (5940 : ℤ))
    (.leaf (11628 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (6372 : ℤ))
    (.leaf (684 : ℤ)))
    (.node 1 (.leaf (4740 : ℤ))
    (.node 1 (.leaf (10860 : ℤ))
    (.leaf (7488 : ℤ)))))
    (.node 2 (.node 1 (.leaf (1368 : ℤ))
    (.leaf (1284 : ℤ)))
    (.node 1 (.leaf (3468 : ℤ))
    (.node 1 (.leaf (2868 : ℤ))
    (.leaf (684 : ℤ))))))))
    (.node 20 (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (208 : ℤ))
    (.leaf (224 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (736 : ℤ)))))
    (.node 2 (.node 1 (.leaf (1064 : ℤ))
    (.leaf (240 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (960 : ℤ))
    (.leaf (1848 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (720 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (544 : ℤ))
    (.node 1 (.leaf (1400 : ℤ))
    (.leaf (720 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (392 : ℤ))
    (.node 1 (.leaf (240 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 10 (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (192 : ℤ))))))
    (.node 5 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))

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
    0 ≤ highRLTarget x d u := by
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
    0 ≤ highRLTarget x d u := by
  have hb := leaf0 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
  push_cast at hb
  linarith only [hb]

theorem junctionFaceHRL {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highRLTarget x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 

end Taeyoung.Methods.Atlas126
