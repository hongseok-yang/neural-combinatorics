import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.HighBoundaries
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact Bernstein certificate for Atlas 126 junction candidate HD1.
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
  ⟨0, 1, 0, (6144 : ℤ)⟩,
  ⟨0, 2, 0, (-7808 : ℤ)⟩,
  ⟨0, 3, 0, (2688 : ℤ)⟩,
  ⟨0, 4, 0, (-256 : ℤ)⟩,
  ⟨0, 5, 1, (192 : ℤ)⟩,
  ⟨0, 6, 2, (-128 : ℤ)⟩,
  ⟨0, 6, 3, (64 : ℤ)⟩,
  ⟨1, 1, 0, (23808 : ℤ)⟩,
  ⟨1, 2, 0, (-30656 : ℤ)⟩,
  ⟨1, 3, 0, (11264 : ℤ)⟩,
  ⟨1, 4, 0, (-1152 : ℤ)⟩,
  ⟨1, 5, 1, (480 : ℤ)⟩,
  ⟨1, 6, 2, (-384 : ℤ)⟩,
  ⟨1, 6, 3, (192 : ℤ)⟩,
  ⟨2, 1, 0, (48000 : ℤ)⟩,
  ⟨2, 2, 0, (-62688 : ℤ)⟩,
  ⟨2, 3, 0, (24384 : ℤ)⟩,
  ⟨2, 4, 0, (-2688 : ℤ)⟩,
  ⟨2, 5, 1, (480 : ℤ)⟩,
  ⟨2, 6, 2, (-480 : ℤ)⟩,
  ⟨2, 6, 3, (240 : ℤ)⟩,
  ⟨3, 1, 0, (50112 : ℤ)⟩,
  ⟨3, 2, 0, (-67280 : ℤ)⟩,
  ⟨3, 3, 0, (28608 : ℤ)⟩,
  ⟨3, 4, 0, (-3520 : ℤ)⟩,
  ⟨3, 5, 1, (240 : ℤ)⟩,
  ⟨3, 6, 2, (-320 : ℤ)⟩,
  ⟨3, 6, 3, (160 : ℤ)⟩,
  ⟨4, 1, 0, (27168 : ℤ)⟩,
  ⟨4, 2, 0, (-38912 : ℤ)⟩,
  ⟨4, 3, 0, (18536 : ℤ)⟩,
  ⟨4, 4, 0, (-2640 : ℤ)⟩,
  ⟨4, 5, 1, (60 : ℤ)⟩,
  ⟨4, 6, 2, (-120 : ℤ)⟩,
  ⟨4, 6, 3, (60 : ℤ)⟩,
  ⟨5, 1, 0, (7296 : ℤ)⟩,
  ⟨5, 2, 0, (-12192 : ℤ)⟩,
  ⟨5, 3, 0, (6576 : ℤ)⟩,
  ⟨5, 4, 0, (-1128 : ℤ)⟩,
  ⟨5, 5, 1, (6 : ℤ)⟩,
  ⟨5, 6, 2, (-24 : ℤ)⟩,
  ⟨5, 6, 3, (12 : ℤ)⟩,
  ⟨6, 1, 0, (768 : ℤ)⟩,
  ⟨6, 2, 0, (-1952 : ℤ)⟩,
  ⟨6, 3, 0, (1176 : ℤ)⟩,
  ⟨6, 4, 0, (-256 : ℤ)⟩,
  ⟨6, 6, 2, (-2 : ℤ)⟩,
  ⟨6, 6, 3, (1 : ℤ)⟩,
  ⟨7, 2, 0, (-128 : ℤ)⟩,
  ⟨7, 3, 0, (80 : ℤ)⟩,
  ⟨7, 4, 0, (-24 : ℤ)⟩]

private def leaf0CoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff leaf0CoeffTerms i j k

private def leaf0Coeff (i j k : ℕ) : ℚ :=
  (leaf0CoeffNumer i j k : ℚ) / 46656

private theorem leaf0CoeffExpansion (x d u : ℝ) :
    msum leaf0Coeff 7 6 3 x d u = sparseEval (leaf0CoeffTerms.map IntTerm.toRat) x d u / 46656 := by
  have he : ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      leaf0CoeffNumer i j k = intSparseCoeff leaf0CoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ leaf0CoeffTerms, t.i ≤ 7 ∧ t.j ≤ 6 ∧ t.k ≤ 3 := by decide +kernel
  exact msum_intSparse_scaled leaf0CoeffNumer leaf0CoeffTerms 46656 7 6 3 he hb x d u

private theorem leaf0Identity (x d u : ℝ) :
    msum leaf0Coeff 7 6 3 x d u = highD1Target x d u := by
  rw [leaf0CoeffExpansion]
  simp only [sparseEval, IntTerm.toRat, leaf0CoeffTerms, highD1Target, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

private def leaf0InputData : IntTable :=
  (.node 112 (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (6144 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-7808 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (2688 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-256 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (192 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-128 : ℤ))
    (.leaf (64 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (23808 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-30656 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (11264 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-1152 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (480 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-384 : ℤ))
    (.leaf (192 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (48000 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-62688 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (24384 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2688 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (480 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-480 : ℤ))
    (.leaf (240 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (50112 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-67280 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (28608 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-3520 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (240 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-320 : ℤ))
    (.leaf (160 : ℤ)))))))))
    (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (27168 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-38912 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (18536 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2640 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (60 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-120 : ℤ))
    (.leaf (60 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (7296 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-12192 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (6576 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-1128 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (6 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-24 : ℤ))
    (.leaf (12 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (768 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1952 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1176 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-256 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-2 : ℤ))
    (.leaf (1 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-128 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (80 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-24 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))

private def leaf0InputNumer (i j k : ℕ) : ℤ :=
  leaf0InputData.get ((i * 7 + j) * 4 + k)

private def leaf0Input (i j k : ℕ) : ℚ :=
  (leaf0InputNumer i j k : ℚ) / 46656

private theorem leaf0InputNumerCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      leaf0InputNumer i j k = leaf0CoeffNumer i j k := by
  decide +kernel

private theorem leaf0InputCorrect :
    ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      leaf0Input i j k = leaf0Coeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/46656)
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
  (.node 24 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (15 : ℤ))))
    (.node 1 (.leaf (5 : ℤ))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (20 : ℤ))
    (.node 1 (.leaf (10 : ℤ))
    (.leaf (4 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (15 : ℤ))
    (.leaf (10 : ℤ)))))
    (.node 3 (.node 1 (.leaf (6 : ℤ))
    (.node 1 (.leaf (3 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (6 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (5 : ℤ))
    (.node 1 (.leaf (4 : ℤ))
    (.leaf (3 : ℤ))))
    (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1 : ℤ))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ)))
    (.node 1 (.leaf (1 : ℤ))
    (.leaf (1 : ℤ))))))))

private def leaf0W2Numer (k i : ℕ) : ℤ :=
  leaf0W2Data.get (k * 7 + i)

private def leaf0W2 (k i : ℕ) : ℚ :=
  (leaf0W2Numer k i : ℚ) / 1

private theorem leaf0W2NumerCorrect :
    ∀ k ∈ range 7, ∀ i ∈ range 7,
      leaf0W2Numer k i = intTransWeight 6 (0) 1 1 k i := by
  decide +kernel

private theorem leaf0W2Correct : WeightsCorrect 6 (0 : ℚ) (1 : ℚ) leaf0W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 6 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf0W2NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^6 = 1 by norm_num,
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
  (.node 112 (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (6144 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-7808 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (2688 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-256 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (192 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-128 : ℤ))
    (.leaf (64 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (66816 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-85312 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (30080 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-2944 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1824 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1280 : ℤ))
    (.leaf (640 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (319872 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-410592 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (148416 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-14976 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (7392 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-5472 : ℤ))
    (.leaf (2736 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (862272 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1113840 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (413568 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-43200 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (16560 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-12960 : ℤ))
    (.leaf (6480 : ℤ)))))))))
    (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1398816 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1821312 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (696168 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-75600 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (22140 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-18360 : ℤ))
    (.leaf (9180 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1355616 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-1783296 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (703080 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-79704 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (17658 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-15552 : ℤ))
    (.leaf (7776 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (723168 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-964224 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (392688 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-46656 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (7776 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-7290 : ℤ))
    (.leaf (3645 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (163296 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-221616 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (93312 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-11664 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1458 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1458 : ℤ))
    (.leaf (729 : ℤ))))))))))

private def leaf0S1Numer (i j k : ℕ) : ℤ :=
  leaf0S1Data.get ((i * 7 + j) * 4 + k)

private def leaf0S1 (i j k : ℕ) : ℚ :=
  (leaf0S1Numer i j k : ℚ) / 46656

private theorem leaf0S1NumerCorrect :
    ∀ h ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      leaf0S1Numer h j k = ∑ i ∈ range 8, leaf0InputNumer i j k * leaf0W1Numer h i := by
  decide +kernel

private theorem leaf0S1Correct : Axis1Correct 7 6 3 leaf0W1 leaf0Input leaf0S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => leaf0InputNumer i j k) (leaf0W1Numer h) (leaf0S1Numer h j k) 46656 1 7
    (leaf0S1NumerCorrect h hh j hj k hk)
  norm_num only [show (46656 : ℚ)*1 = 46656 by norm_num] at he
  exact he

private def leaf0S2Data : IntTable :=
  (.node 112 (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (6144 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (22912 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (32896 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (22400 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (7040 : ℤ)))))
    (.node 3 (.node 1 (.leaf (192 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (768 : ℤ))
    (.leaf (192 : ℤ)))
    (.node 1 (.leaf (-128 : ℤ))
    (.leaf (64 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (66816 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (248768 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (356992 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (243584 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (77184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1824 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (8640 : ℤ))
    (.leaf (1824 : ℤ)))
    (.node 1 (.leaf (-1280 : ℤ))
    (.leaf (640 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (319872 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1188768 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1704768 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1165440 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (372288 : ℤ)))))
    (.node 3 (.node 1 (.leaf (7392 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (42720 : ℤ))
    (.leaf (7392 : ℤ)))
    (.node 1 (.leaf (-5472 : ℤ))
    (.leaf (2736 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (862272 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (3197520 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (4580928 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3137184 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1010304 : ℤ)))))
    (.node 3 (.node 1 (.leaf (16560 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (118800 : ℤ))
    (.leaf (16560 : ℤ)))
    (.node 1 (.leaf (-12960 : ℤ))
    (.leaf (6480 : ℤ)))))))))
    (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1398816 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (5172768 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (7399080 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (5073192 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1646136 : ℤ)))))
    (.node 3 (.node 1 (.leaf (22140 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (198072 : ℤ))
    (.leaf (22140 : ℤ)))
    (.node 1 (.leaf (-18360 : ℤ))
    (.leaf (9180 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1355616 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4994784 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (7126056 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4885920 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1594728 : ℤ)))))
    (.node 3 (.node 1 (.leaf (17658 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (195696 : ℤ))
    (.leaf (17658 : ℤ)))
    (.node 1 (.leaf (-15552 : ℤ))
    (.leaf (7776 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (723168 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (2651616 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (3767472 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (2577744 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (843696 : ℤ)))))
    (.node 3 (.node 1 (.leaf (7776 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (104976 : ℤ))
    (.leaf (7776 : ℤ)))
    (.node 1 (.leaf (-7290 : ℤ))
    (.leaf (3645 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (163296 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (594864 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (839808 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (571536 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (186624 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1458 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (23328 : ℤ))
    (.leaf (1458 : ℤ)))
    (.node 1 (.leaf (-1458 : ℤ))
    (.leaf (729 : ℤ))))))))))

private def leaf0S2Numer (i j k : ℕ) : ℤ :=
  leaf0S2Data.get ((i * 7 + j) * 4 + k)

private def leaf0S2 (i j k : ℕ) : ℚ :=
  (leaf0S2Numer i j k : ℚ) / 46656

private theorem leaf0S2NumerCorrect :
    ∀ k ∈ range 8, ∀ j ∈ range 7, ∀ h ∈ range 4,
      leaf0S2Numer k j h = ∑ i ∈ range 7, leaf0S1Numer k i h * leaf0W2Numer j i := by
  decide +kernel

private theorem leaf0S2Correct : Axis2Correct 7 6 3 leaf0W2 leaf0S1 leaf0S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S1Numer k i h) (leaf0W2Numer j) (leaf0S2Numer k j h) 46656 1 6
    (leaf0S2NumerCorrect k hk j hj h hh)
  norm_num only [show (46656 : ℚ)*1 = 46656 by norm_num] at he
  exact he

private def leaf0S3Data : IntTable :=
  (.node 112 (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (6144 : ℤ)))
    (.node 1 (.leaf (18432 : ℤ))
    (.leaf (18432 : ℤ)))))
    (.node 3 (.node 1 (.leaf (6144 : ℤ))
    (.node 1 (.leaf (22912 : ℤ))
    (.leaf (68736 : ℤ))))
    (.node 2 (.node 1 (.leaf (68736 : ℤ))
    (.leaf (22912 : ℤ)))
    (.node 1 (.leaf (32896 : ℤ))
    (.leaf (98688 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (98688 : ℤ))
    (.node 1 (.leaf (32896 : ℤ))
    (.leaf (22400 : ℤ))))
    (.node 2 (.node 1 (.leaf (67200 : ℤ))
    (.leaf (67200 : ℤ)))
    (.node 1 (.leaf (22400 : ℤ))
    (.leaf (7040 : ℤ)))))
    (.node 3 (.node 1 (.leaf (21312 : ℤ))
    (.node 1 (.leaf (21504 : ℤ))
    (.leaf (7232 : ℤ))))
    (.node 2 (.node 1 (.leaf (768 : ℤ))
    (.leaf (2496 : ℤ)))
    (.node 1 (.leaf (2560 : ℤ))
    (.leaf (896 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (66816 : ℤ)))
    (.node 1 (.leaf (200448 : ℤ))
    (.leaf (200448 : ℤ)))))
    (.node 3 (.node 1 (.leaf (66816 : ℤ))
    (.node 1 (.leaf (248768 : ℤ))
    (.leaf (746304 : ℤ))))
    (.node 2 (.node 1 (.leaf (746304 : ℤ))
    (.leaf (248768 : ℤ)))
    (.node 1 (.leaf (356992 : ℤ))
    (.leaf (1070976 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (1070976 : ℤ))
    (.node 1 (.leaf (356992 : ℤ))
    (.leaf (243584 : ℤ))))
    (.node 2 (.node 1 (.leaf (730752 : ℤ))
    (.leaf (730752 : ℤ)))
    (.node 1 (.leaf (243584 : ℤ))
    (.leaf (77184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (233376 : ℤ))
    (.node 1 (.leaf (235200 : ℤ))
    (.leaf (79008 : ℤ))))
    (.node 2 (.node 1 (.leaf (8640 : ℤ))
    (.leaf (27744 : ℤ)))
    (.node 1 (.leaf (28288 : ℤ))
    (.leaf (9824 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (319872 : ℤ)))
    (.node 1 (.leaf (959616 : ℤ))
    (.leaf (959616 : ℤ)))))
    (.node 3 (.node 1 (.leaf (319872 : ℤ))
    (.node 1 (.leaf (1188768 : ℤ))
    (.leaf (3566304 : ℤ))))
    (.node 2 (.node 1 (.leaf (3566304 : ℤ))
    (.leaf (1188768 : ℤ)))
    (.node 1 (.leaf (1704768 : ℤ))
    (.leaf (5114304 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (5114304 : ℤ))
    (.node 1 (.leaf (1704768 : ℤ))
    (.leaf (1165440 : ℤ))))
    (.node 2 (.node 1 (.leaf (3496320 : ℤ))
    (.leaf (3496320 : ℤ)))
    (.node 1 (.leaf (1165440 : ℤ))
    (.leaf (372288 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1124256 : ℤ))
    (.node 1 (.leaf (1131648 : ℤ))
    (.leaf (379680 : ℤ))))
    (.node 2 (.node 1 (.leaf (42720 : ℤ))
    (.leaf (135552 : ℤ)))
    (.node 1 (.leaf (137472 : ℤ))
    (.leaf (47376 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (862272 : ℤ)))
    (.node 1 (.leaf (2586816 : ℤ))
    (.leaf (2586816 : ℤ)))))
    (.node 3 (.node 1 (.leaf (862272 : ℤ))
    (.node 1 (.leaf (3197520 : ℤ))
    (.leaf (9592560 : ℤ))))
    (.node 2 (.node 1 (.leaf (9592560 : ℤ))
    (.leaf (3197520 : ℤ)))
    (.node 1 (.leaf (4580928 : ℤ))
    (.leaf (13742784 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (13742784 : ℤ))
    (.node 1 (.leaf (4580928 : ℤ))
    (.leaf (3137184 : ℤ))))
    (.node 2 (.node 1 (.leaf (9411552 : ℤ))
    (.leaf (9411552 : ℤ)))
    (.node 1 (.leaf (3137184 : ℤ))
    (.leaf (1010304 : ℤ)))))
    (.node 3 (.node 1 (.leaf (3047472 : ℤ))
    (.node 1 (.leaf (3064032 : ℤ))
    (.leaf (1026864 : ℤ))))
    (.node 2 (.node 1 (.leaf (118800 : ℤ))
    (.leaf (372960 : ℤ)))
    (.node 1 (.leaf (376560 : ℤ))
    (.leaf (128880 : ℤ)))))))))
    (.node 56 (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1398816 : ℤ)))
    (.node 1 (.leaf (4196448 : ℤ))
    (.leaf (4196448 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1398816 : ℤ))
    (.node 1 (.leaf (5172768 : ℤ))
    (.leaf (15518304 : ℤ))))
    (.node 2 (.node 1 (.leaf (15518304 : ℤ))
    (.leaf (5172768 : ℤ)))
    (.node 1 (.leaf (7399080 : ℤ))
    (.leaf (22197240 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (22197240 : ℤ))
    (.node 1 (.leaf (7399080 : ℤ))
    (.leaf (5073192 : ℤ))))
    (.node 2 (.node 1 (.leaf (15219576 : ℤ))
    (.leaf (15219576 : ℤ)))
    (.node 1 (.leaf (5073192 : ℤ))
    (.leaf (1646136 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4960548 : ℤ))
    (.node 1 (.leaf (4982688 : ℤ))
    (.leaf (1668276 : ℤ))))
    (.node 2 (.node 1 (.leaf (198072 : ℤ))
    (.leaf (616356 : ℤ)))
    (.node 1 (.leaf (620136 : ℤ))
    (.leaf (211032 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1355616 : ℤ)))
    (.node 1 (.leaf (4066848 : ℤ))
    (.leaf (4066848 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1355616 : ℤ))
    (.node 1 (.leaf (4994784 : ℤ))
    (.leaf (14984352 : ℤ))))
    (.node 2 (.node 1 (.leaf (14984352 : ℤ))
    (.leaf (4994784 : ℤ)))
    (.node 1 (.leaf (7126056 : ℤ))
    (.leaf (21378168 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (21378168 : ℤ))
    (.node 1 (.leaf (7126056 : ℤ))
    (.leaf (4885920 : ℤ))))
    (.node 2 (.node 1 (.leaf (14657760 : ℤ))
    (.leaf (14657760 : ℤ)))
    (.node 1 (.leaf (4885920 : ℤ))
    (.leaf (1594728 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4801842 : ℤ))
    (.node 1 (.leaf (4819500 : ℤ))
    (.leaf (1612386 : ℤ))))
    (.node 2 (.node 1 (.leaf (195696 : ℤ))
    (.leaf (604746 : ℤ)))
    (.node 1 (.leaf (606852 : ℤ))
    (.leaf (205578 : ℤ))))))))
    (.node 28 (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (723168 : ℤ)))
    (.node 1 (.leaf (2169504 : ℤ))
    (.leaf (2169504 : ℤ)))))
    (.node 3 (.node 1 (.leaf (723168 : ℤ))
    (.node 1 (.leaf (2651616 : ℤ))
    (.leaf (7954848 : ℤ))))
    (.node 2 (.node 1 (.leaf (7954848 : ℤ))
    (.leaf (2651616 : ℤ)))
    (.node 1 (.leaf (3767472 : ℤ))
    (.leaf (11302416 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (11302416 : ℤ))
    (.node 1 (.leaf (3767472 : ℤ))
    (.leaf (2577744 : ℤ))))
    (.node 2 (.node 1 (.leaf (7733232 : ℤ))
    (.leaf (7733232 : ℤ)))
    (.node 1 (.leaf (2577744 : ℤ))
    (.leaf (843696 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2538864 : ℤ))
    (.node 1 (.leaf (2546640 : ℤ))
    (.leaf (851472 : ℤ))))
    (.node 2 (.node 1 (.leaf (104976 : ℤ))
    (.leaf (322704 : ℤ)))
    (.node 1 (.leaf (323190 : ℤ))
    (.leaf (109107 : ℤ)))))))
    (.node 14 (.node 7 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (163296 : ℤ)))
    (.node 1 (.leaf (489888 : ℤ))
    (.leaf (489888 : ℤ)))))
    (.node 3 (.node 1 (.leaf (163296 : ℤ))
    (.node 1 (.leaf (594864 : ℤ))
    (.leaf (1784592 : ℤ))))
    (.node 2 (.node 1 (.leaf (1784592 : ℤ))
    (.leaf (594864 : ℤ)))
    (.node 1 (.leaf (839808 : ℤ))
    (.leaf (2519424 : ℤ))))))
    (.node 7 (.node 3 (.node 1 (.leaf (2519424 : ℤ))
    (.node 1 (.leaf (839808 : ℤ))
    (.leaf (571536 : ℤ))))
    (.node 2 (.node 1 (.leaf (1714608 : ℤ))
    (.leaf (1714608 : ℤ)))
    (.node 1 (.leaf (571536 : ℤ))
    (.leaf (186624 : ℤ)))))
    (.node 3 (.node 1 (.leaf (561330 : ℤ))
    (.node 1 (.leaf (562788 : ℤ))
    (.leaf (188082 : ℤ))))
    (.node 2 (.node 1 (.leaf (23328 : ℤ))
    (.leaf (71442 : ℤ)))
    (.node 1 (.leaf (71442 : ℤ))
    (.leaf (24057 : ℤ))))))))))

private def leaf0S3Numer (i j k : ℕ) : ℤ :=
  leaf0S3Data.get ((i * 7 + j) * 4 + k)

private def leaf0S3 (i j k : ℕ) : ℚ :=
  (leaf0S3Numer i j k : ℚ) / 46656

private theorem leaf0S3NumerCorrect :
    ∀ k ∈ range 8, ∀ j ∈ range 7, ∀ h ∈ range 4,
      leaf0S3Numer k j h = ∑ i ∈ range 4, leaf0S2Numer k j i * leaf0W3Numer h i := by
  decide +kernel

private theorem leaf0S3Correct : Axis3Correct 7 6 3 leaf0W3 leaf0S2 leaf0S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf0S2Numer k j i) (leaf0W3Numer h) (leaf0S3Numer k j h) 46656 1 3
    (leaf0S3NumerCorrect k hk j hj h hh)
  norm_num only [show (46656 : ℚ)*1 = 46656 by norm_num] at he
  exact he

private theorem leaf0NumerSigns :
    ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      0 ≤ leaf0S3Numer i j k := by
  decide +kernel

private theorem leaf0Signs :
    ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      0 ≤ leaf0S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf0NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf0Certificate :
    ∀ i ∈ range 8, ∀ j ∈ range 7, ∀ k ∈ range 4,
      0 ≤ trans3 leaf0Coeff 7 6 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 leaf0Coeff leaf0S1 leaf0S2 leaf0S3 7 6 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) (0 : ℚ) (1 : ℚ) leaf0W1 leaf0W2 leaf0W3
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
    0 ≤ highD1Target x d u := by
  have h : 0 ≤ msum leaf0Coeff 7 6 3 x d u :=
    msum_nonneg_on_box leaf0Coeff 7 6 3
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
    0 ≤ highD1Target x d u := by
  have hb := leaf0 (x := x) (d := d) (u := u) hx0 hx1 hd0 hd1 hu0 hu1
  push_cast at hb
  linarith only [hb]

theorem junctionFaceHD1 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ))
     :
    0 ≤ highD1Target x d u := by
  exact region0 hx0 hx1 hd0 hd1 hu0 hu1 

end Taeyoung.Methods.Atlas126
