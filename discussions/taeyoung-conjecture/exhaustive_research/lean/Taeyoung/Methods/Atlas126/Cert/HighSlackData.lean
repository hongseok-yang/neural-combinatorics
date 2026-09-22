import Taeyoung.Methods.Atlas126.HighScaledSlack
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.HighSlackData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 0, 1, (64 : ℤ)⟩,
  ⟨0, 0, 2, (-352 : ℤ)⟩,
  ⟨0, 0, 3, (784 : ℤ)⟩,
  ⟨0, 0, 4, (-1104 : ℤ)⟩,
  ⟨0, 0, 5, (1296 : ℤ)⟩,
  ⟨0, 0, 6, (-864 : ℤ)⟩,
  ⟨0, 0, 7, (288 : ℤ)⟩,
  ⟨0, 1, 0, (72 : ℤ)⟩,
  ⟨0, 1, 1, (240 : ℤ)⟩,
  ⟨0, 1, 2, (-1440 : ℤ)⟩,
  ⟨0, 1, 3, (2592 : ℤ)⟩,
  ⟨0, 1, 4, (-2592 : ℤ)⟩,
  ⟨0, 1, 5, (1296 : ℤ)⟩,
  ⟨0, 2, 0, (108 : ℤ)⟩,
  ⟨0, 2, 1, (972 : ℤ)⟩,
  ⟨0, 2, 2, (-1944 : ℤ)⟩,
  ⟨0, 2, 3, (1944 : ℤ)⟩,
  ⟨0, 3, 1, (972 : ℤ)⟩,
  ⟨1, 0, 1, (392 : ℤ)⟩,
  ⟨1, 0, 2, (-1688 : ℤ)⟩,
  ⟨1, 0, 3, (2576 : ℤ)⟩,
  ⟨1, 0, 4, (-2400 : ℤ)⟩,
  ⟨1, 0, 5, (2400 : ℤ)⟩,
  ⟨1, 0, 6, (-1296 : ℤ)⟩,
  ⟨1, 0, 7, (432 : ℤ)⟩,
  ⟨1, 1, 0, (432 : ℤ)⟩,
  ⟨1, 1, 1, (648 : ℤ)⟩,
  ⟨1, 1, 2, (-3312 : ℤ)⟩,
  ⟨1, 1, 3, (3960 : ℤ)⟩,
  ⟨1, 1, 4, (-2592 : ℤ)⟩,
  ⟨1, 1, 5, (1296 : ℤ)⟩,
  ⟨1, 2, 0, (432 : ℤ)⟩,
  ⟨1, 2, 1, (1512 : ℤ)⟩,
  ⟨1, 2, 2, (-972 : ℤ)⟩,
  ⟨1, 2, 3, (972 : ℤ)⟩,
  ⟨2, 0, 1, (1568 : ℤ)⟩,
  ⟨2, 0, 2, (-5492 : ℤ)⟩,
  ⟨2, 0, 3, (5972 : ℤ)⟩,
  ⟨2, 0, 4, (-3300 : ℤ)⟩,
  ⟨2, 0, 5, (2532 : ℤ)⟩,
  ⟨2, 0, 6, (-648 : ℤ)⟩,
  ⟨2, 0, 7, (216 : ℤ)⟩,
  ⟨2, 1, 0, (1512 : ℤ)⟩,
  ⟨2, 1, 1, (1704 : ℤ)⟩,
  ⟨2, 1, 2, (-6048 : ℤ)⟩,
  ⟨2, 1, 3, (4644 : ℤ)⟩,
  ⟨2, 1, 4, (-648 : ℤ)⟩,
  ⟨2, 1, 5, (324 : ℤ)⟩,
  ⟨2, 2, 0, (1080 : ℤ)⟩,
  ⟨2, 2, 1, (2484 : ℤ)⟩,
  ⟨3, 0, 1, (3816 : ℤ)⟩,
  ⟨3, 0, 2, (-10320 : ℤ)⟩,
  ⟨3, 0, 3, (6576 : ℤ)⟩,
  ⟨3, 0, 4, (-516 : ℤ)⟩,
  ⟨3, 0, 5, (900 : ℤ)⟩,
  ⟨3, 0, 6, (-108 : ℤ)⟩,
  ⟨3, 0, 7, (36 : ℤ)⟩,
  ⟨3, 1, 0, (3168 : ℤ)⟩,
  ⟨3, 1, 1, (1200 : ℤ)⟩,
  ⟨3, 1, 2, (-2664 : ℤ)⟩,
  ⟨3, 1, 3, (216 : ℤ)⟩,
  ⟨3, 2, 0, (1296 : ℤ)⟩,
  ⟨3, 2, 1, (-1080 : ℤ)⟩,
  ⟨4, 0, 1, (6784 : ℤ)⟩,
  ⟨4, 0, 2, (-14392 : ℤ)⟩,
  ⟨4, 0, 3, (5332 : ℤ)⟩,
  ⟨4, 0, 4, (1536 : ℤ)⟩,
  ⟨4, 0, 5, (-204 : ℤ)⟩,
  ⟨4, 1, 0, (4536 : ℤ)⟩,
  ⟨4, 1, 1, (936 : ℤ)⟩,
  ⟨4, 1, 2, (-1440 : ℤ)⟩,
  ⟨4, 1, 3, (-720 : ℤ)⟩,
  ⟨4, 2, 0, (972 : ℤ)⟩,
  ⟨5, 0, 1, (7864 : ℤ)⟩,
  ⟨5, 0, 2, (-12256 : ℤ)⟩,
  ⟨5, 0, 3, (1552 : ℤ)⟩,
  ⟨5, 0, 4, (816 : ℤ)⟩,
  ⟨5, 0, 5, (-120 : ℤ)⟩,
  ⟨5, 1, 0, (3888 : ℤ)⟩,
  ⟨5, 1, 1, (-1416 : ℤ)⟩,
  ⟨5, 1, 2, (-648 : ℤ)⟩,
  ⟨6, 0, 1, (6560 : ℤ)⟩,
  ⟨6, 0, 2, (-7796 : ℤ)⟩,
  ⟨6, 0, 3, (344 : ℤ)⟩,
  ⟨6, 0, 4, (108 : ℤ)⟩,
  ⟨6, 1, 0, (1944 : ℤ)⟩,
  ⟨6, 1, 1, (576 : ℤ)⟩,
  ⟨7, 0, 1, (2904 : ℤ)⟩,
  ⟨7, 0, 2, (-2136 : ℤ)⟩,
  ⟨7, 0, 3, (192 : ℤ)⟩,
  ⟨8, 0, 1, (1152 : ℤ)⟩]

def commonCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff commonCoeffTerms i j k

def commonCoeff (i j k : ℕ) : ℚ :=
  (commonCoeffNumer i j k : ℚ) / 243

theorem commonCoeffExpansion (x d u : ℝ) :
    msum commonCoeff 8 3 7 x d u = sparseEval (commonCoeffTerms.map IntTerm.toRat) x d u / 243 := by
  have he : ∀ i ∈ range 9, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonCoeffNumer i j k = intSparseCoeff commonCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ commonCoeffTerms, t.i ≤ 8 ∧ t.j ≤ 3 ∧ t.k ≤ 7 := by decide +kernel
  exact msum_intSparse_scaled commonCoeffNumer commonCoeffTerms 243 8 3 7 he hb x d u

theorem commonIdentity (x d u : ℝ) :
    msum commonCoeff 8 3 7 x d u = highScaledSlackTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,highScaledSlackTarget, highSlackPolynomial, highDensityParameter, highGammaReduced, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 144 (.node 72 (.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (64 : ℤ)))
    (.node 1 (.leaf (-352 : ℤ))
    (.leaf (784 : ℤ))))
    (.node 2 (.node 1 (.leaf (-1104 : ℤ))
    (.leaf (1296 : ℤ)))
    (.node 1 (.leaf (-864 : ℤ))
    (.node 1 (.leaf (288 : ℤ))
    (.leaf (72 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (240 : ℤ))
    (.leaf (-1440 : ℤ)))
    (.node 1 (.leaf (2592 : ℤ))
    (.leaf (-2592 : ℤ))))
    (.node 2 (.node 1 (.leaf (1296 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (972 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-1944 : ℤ))
    (.leaf (1944 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (972 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (392 : ℤ))
    (.node 1 (.leaf (-1688 : ℤ))
    (.leaf (2576 : ℤ))))))))
    (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-2400 : ℤ))
    (.leaf (2400 : ℤ)))
    (.node 1 (.leaf (-1296 : ℤ))
    (.leaf (432 : ℤ))))
    (.node 2 (.node 1 (.leaf (432 : ℤ))
    (.leaf (648 : ℤ)))
    (.node 1 (.leaf (-3312 : ℤ))
    (.node 1 (.leaf (3960 : ℤ))
    (.leaf (-2592 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (1296 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (432 : ℤ))))
    (.node 2 (.node 1 (.leaf (1512 : ℤ))
    (.leaf (-972 : ℤ)))
    (.node 1 (.leaf (972 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1568 : ℤ))
    (.leaf (-5492 : ℤ))))
    (.node 2 (.node 1 (.leaf (5972 : ℤ))
    (.leaf (-3300 : ℤ)))
    (.node 1 (.leaf (2532 : ℤ))
    (.node 1 (.leaf (-648 : ℤ))
    (.leaf (216 : ℤ)))))))))
    (.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1512 : ℤ))
    (.leaf (1704 : ℤ)))
    (.node 1 (.leaf (-6048 : ℤ))
    (.leaf (4644 : ℤ))))
    (.node 2 (.node 1 (.leaf (-648 : ℤ))
    (.leaf (324 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1080 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (2484 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (3816 : ℤ))
    (.leaf (-10320 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (6576 : ℤ))
    (.leaf (-516 : ℤ)))
    (.node 1 (.leaf (900 : ℤ))
    (.leaf (-108 : ℤ))))
    (.node 2 (.node 1 (.leaf (36 : ℤ))
    (.leaf (3168 : ℤ)))
    (.node 1 (.leaf (1200 : ℤ))
    (.node 1 (.leaf (-2664 : ℤ))
    (.leaf (216 : ℤ))))))))
    (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (1296 : ℤ))
    (.leaf (-1080 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (6784 : ℤ))))
    (.node 2 (.node 1 (.leaf (-14392 : ℤ))
    (.leaf (5332 : ℤ)))
    (.node 1 (.leaf (1536 : ℤ))
    (.node 1 (.leaf (-204 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (4536 : ℤ)))
    (.node 1 (.leaf (936 : ℤ))
    (.leaf (-1440 : ℤ))))
    (.node 2 (.node 1 (.leaf (-720 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))
    (.node 72 (.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (972 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (7864 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-12256 : ℤ))
    (.leaf (1552 : ℤ)))
    (.node 1 (.leaf (816 : ℤ))
    (.leaf (-120 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (3888 : ℤ))
    (.node 1 (.leaf (-1416 : ℤ))
    (.leaf (-648 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (6560 : ℤ))
    (.leaf (-7796 : ℤ)))
    (.node 1 (.leaf (344 : ℤ))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (1944 : ℤ))
    (.leaf (576 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 36 (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (2904 : ℤ))
    (.leaf (-2136 : ℤ)))
    (.node 1 (.leaf (192 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1152 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))))

def commonInputNumer (i j k : ℕ) : ℤ :=
  commonInputData.get ((i * 4 + j) * 8 + k)

def commonInput (i j k : ℕ) : ℚ :=
  (commonInputNumer i j k : ℚ) / 243

theorem commonInputNumerCorrect :
    ∀ i ∈ range 9, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInputNumer i j k = commonCoeffNumer i j k := by
  decide +kernel

theorem commonInputCorrect :
    ∀ i ∈ range 9, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInput i j k = commonCoeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/243)
    (commonInputNumerCorrect i hi j hj k hk)


end Taeyoung.Methods.Atlas126.HighSlackData
