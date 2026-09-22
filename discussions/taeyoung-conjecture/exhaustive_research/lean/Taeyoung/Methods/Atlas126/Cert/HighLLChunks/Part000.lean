import Taeyoung.Methods.Atlas126.Cert.HighLLData
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset

namespace Taeyoung.Methods.Atlas126.HighLLData
open Taeyoung.Methods.Bernstein


private def leaf1W1Data : IntTable :=
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

private def leaf1W1Numer (k i : ℕ) : ℤ :=
  leaf1W1Data.get (k * 5 + i)

private def leaf1W1 (k i : ℕ) : ℚ :=
  (leaf1W1Numer k i : ℚ) / 1

private theorem leaf1W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf1W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf1W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf1W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf1W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf1W1, neg_div] using he

private def leaf1W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (16 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (64 : ℤ)))))
    (.node 3 (.node 1 (.leaf (8 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (96 : ℤ))
    (.leaf (24 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (4 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (64 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (8 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (16 : ℤ))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ)))))))

private def leaf1W2Numer (k i : ℕ) : ℤ :=
  leaf1W2Data.get (k * 5 + i)

private def leaf1W2 (k i : ℕ) : ℚ :=
  (leaf1W2Numer k i : ℚ) / 16

private theorem leaf1W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf1W2Numer k i = intTransWeight 4 (0) 1 2 k i := by
  decide +kernel

private theorem leaf1W2Correct : WeightsCorrect 4 (0 : ℚ) ((1/2) : ℚ) leaf1W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 2 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf1W2NumerCorrect k hk i hi] at he
  norm_num only [show (2 : ℚ)^4 = 16 by norm_num,
    show (0 : ℚ)/2 = 0 by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num] at he
  simpa only [leaf1W2, neg_div] using he

private def leaf1W3Data : IntTable :=
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

private def leaf1W3Numer (k i : ℕ) : ℤ :=
  leaf1W3Data.get (k * 4 + i)

private def leaf1W3 (k i : ℕ) : ℚ :=
  (leaf1W3Numer k i : ℚ) / 1

private theorem leaf1W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf1W3Numer k i = intTransWeight 3 (0) 1 1 k i := by
  decide +kernel

private theorem leaf1W3Correct : WeightsCorrect 3 (0 : ℚ) (1 : ℚ) leaf1W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf1W3NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^3 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf1W3, neg_div] using he

private def leaf1S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf1S1Numer (i j k : ℕ) : ℤ :=
  leaf1S1Data.get ((i * 5 + j) * 4 + k)

private def leaf1S1 (i j k : ℕ) : ℚ :=
  (leaf1S1Numer i j k : ℚ) / 729

private theorem leaf1S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf1S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf1W1Numer h i := by
  decide +kernel

private theorem leaf1S1Correct : Axis1Correct 4 4 3 leaf1W1 commonInput leaf1S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf1W1Numer h) (leaf1S1Numer h j k) 729 1 4
    (leaf1S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf1S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1944 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (3888 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2430 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (486 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (5112 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (720 : ℤ))
    (.node 1 (.leaf (576 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (9468 : ℤ))
    (.node 1 (.leaf (1728 : ℤ))
    (.leaf (864 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (5454 : ℤ))
    (.leaf (1296 : ℤ))))
    (.node 1 (.leaf (576 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1008 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (288 : ℤ))
    (.node 1 (.leaf (144 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4920 : ℤ))
    (.leaf (1488 : ℤ))))
    (.node 2 (.node 1 (.leaf (1656 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (8376 : ℤ))
    (.leaf (3192 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2664 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4452 : ℤ))))
    (.node 1 (.leaf (2028 : ℤ))
    (.node 1 (.leaf (1896 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (786 : ℤ))
    (.node 1 (.leaf (324 : ℤ))
    (.leaf (504 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (336 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (2088 : ℤ))))
    (.node 1 (.leaf (960 : ℤ))
    (.node 1 (.leaf (1496 : ℤ))
    (.leaf (128 : ℤ)))))
    (.node 3 (.node 1 (.leaf (3236 : ℤ))
    (.node 1 (.leaf (1768 : ℤ))
    (.leaf (2400 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (1620 : ℤ)))
    (.node 1 (.leaf (872 : ℤ))
    (.leaf (1656 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (128 : ℤ))
    (.node 1 (.leaf (288 : ℤ))
    (.leaf (64 : ℤ))))
    (.node 1 (.leaf (416 : ℤ))
    (.node 1 (.leaf (32 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (96 : ℤ))
    (.leaf (32 : ℤ))))
    (.node 1 (.leaf (336 : ℤ))
    (.node 1 (.leaf (192 : ℤ))
    (.leaf (416 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (144 : ℤ))
    (.node 1 (.leaf (472 : ℤ))
    (.leaf (280 : ℤ))))
    (.node 1 (.leaf (600 : ℤ))
    (.node 1 (.leaf (240 : ℤ))
    (.leaf (236 : ℤ)))))
    (.node 3 (.node 1 (.leaf (92 : ℤ))
    (.node 1 (.leaf (336 : ℤ))
    (.leaf (176 : ℤ))))
    (.node 2 (.node 1 (.leaf (42 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (56 : ℤ))
    (.leaf (48 : ℤ)))))))))

private def leaf1S2Numer (i j k : ℕ) : ℤ :=
  leaf1S2Data.get ((i * 5 + j) * 4 + k)

private def leaf1S2 (i j k : ℕ) : ℚ :=
  (leaf1S2Numer i j k : ℚ) / 11664

private theorem leaf1S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf1S2Numer k j h = ∑ i ∈ range 5, leaf1S1Numer k i h * leaf1W2Numer j i := by
  decide +kernel

private theorem leaf1S2Correct : Axis2Correct 4 4 3 leaf1W2 leaf1S1 leaf1S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf1S1Numer k i h) (leaf1W2Numer j) (leaf1S2Numer k j h) 729 16 4
    (leaf1S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*16 = 11664 by norm_num] at he
  exact he

private def leaf1S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1944 : ℤ))
    (.leaf (5832 : ℤ)))))
    (.node 3 (.node 1 (.leaf (5832 : ℤ))
    (.node 1 (.leaf (1944 : ℤ))
    (.leaf (3888 : ℤ))))
    (.node 1 (.leaf (11664 : ℤ))
    (.node 1 (.leaf (11664 : ℤ))
    (.leaf (3888 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2430 : ℤ))
    (.node 1 (.leaf (7290 : ℤ))
    (.leaf (7290 : ℤ))))
    (.node 1 (.leaf (2430 : ℤ))
    (.node 1 (.leaf (486 : ℤ))
    (.leaf (1458 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1458 : ℤ))
    (.node 1 (.leaf (486 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (144 : ℤ))
    (.leaf (5112 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (16056 : ℤ))
    (.node 1 (.leaf (17352 : ℤ))
    (.leaf (6408 : ℤ))))
    (.node 1 (.leaf (9468 : ℤ))
    (.node 1 (.leaf (30132 : ℤ))
    (.leaf (32724 : ℤ)))))
    (.node 3 (.node 1 (.leaf (12060 : ℤ))
    (.node 1 (.leaf (5454 : ℤ))
    (.leaf (17658 : ℤ))))
    (.node 1 (.leaf (19530 : ℤ))
    (.node 1 (.leaf (7326 : ℤ))
    (.leaf (1008 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (3312 : ℤ))
    (.node 1 (.leaf (3744 : ℤ))
    (.leaf (1440 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (384 : ℤ))
    (.node 1 (.leaf (4920 : ℤ))
    (.leaf (16248 : ℤ))))
    (.node 2 (.node 1 (.leaf (19392 : ℤ))
    (.leaf (8064 : ℤ)))
    (.node 1 (.leaf (8376 : ℤ))
    (.leaf (28320 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (34176 : ℤ))
    (.node 1 (.leaf (14232 : ℤ))
    (.leaf (4452 : ℤ))))
    (.node 1 (.leaf (15384 : ℤ))
    (.node 1 (.leaf (19308 : ℤ))
    (.leaf (8376 : ℤ)))))
    (.node 3 (.node 1 (.leaf (786 : ℤ))
    (.node 1 (.leaf (2682 : ℤ))
    (.leaf (3510 : ℤ))))
    (.node 1 (.leaf (1614 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (336 : ℤ))
    (.node 1 (.leaf (368 : ℤ))
    (.leaf (2088 : ℤ))))
    (.node 1 (.leaf (7224 : ℤ))
    (.node 1 (.leaf (9680 : ℤ))
    (.leaf (4672 : ℤ)))))
    (.node 3 (.node 1 (.leaf (3236 : ℤ))
    (.node 1 (.leaf (11476 : ℤ))
    (.leaf (15644 : ℤ))))
    (.node 2 (.node 1 (.leaf (7596 : ℤ))
    (.leaf (1620 : ℤ)))
    (.node 1 (.leaf (5732 : ℤ))
    (.leaf (8260 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (4276 : ℤ))
    (.node 1 (.leaf (288 : ℤ))
    (.leaf (928 : ℤ))))
    (.node 1 (.leaf (1408 : ℤ))
    (.node 1 (.leaf (800 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (96 : ℤ))
    (.leaf (128 : ℤ))))
    (.node 1 (.leaf (336 : ℤ))
    (.node 1 (.leaf (1200 : ℤ))
    (.leaf (1808 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1088 : ℤ))
    (.node 1 (.leaf (472 : ℤ))
    (.leaf (1696 : ℤ))))
    (.node 1 (.leaf (2576 : ℤ))
    (.node 1 (.leaf (1592 : ℤ))
    (.leaf (236 : ℤ)))))
    (.node 3 (.node 1 (.leaf (800 : ℤ))
    (.node 1 (.leaf (1228 : ℤ))
    (.leaf (840 : ℤ))))
    (.node 2 (.node 1 (.leaf (42 : ℤ))
    (.leaf (130 : ℤ)))
    (.node 1 (.leaf (190 : ℤ))
    (.leaf (150 : ℤ)))))))))

private def leaf1S3Numer (i j k : ℕ) : ℤ :=
  leaf1S3Data.get ((i * 5 + j) * 4 + k)

private def leaf1S3 (i j k : ℕ) : ℚ :=
  (leaf1S3Numer i j k : ℚ) / 11664

private theorem leaf1S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf1S3Numer k j h = ∑ i ∈ range 4, leaf1S2Numer k j i * leaf1W3Numer h i := by
  decide +kernel

private theorem leaf1S3Correct : Axis3Correct 4 4 3 leaf1W3 leaf1S2 leaf1S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf1S2Numer k j i) (leaf1W3Numer h) (leaf1S3Numer k j h) 11664 1 3
    (leaf1S3NumerCorrect k hk j hj h hh)
  norm_num only [show (11664 : ℚ)*1 = 11664 by norm_num] at he
  exact he

private theorem leaf1NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf1S3Numer i j k := by
  decide +kernel

private theorem leaf1Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf1S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf1NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf1Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) ((1/2) : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf1S1 leaf1S2 leaf1S3 4 4 3 (0 : ℚ) (1 : ℚ) (0 : ℚ) ((1/2) : ℚ) (0 : ℚ) (1 : ℚ) leaf1W1 leaf1W2 leaf1W3
    leaf1W1Correct leaf1W2Correct leaf1W3Correct
    (axis1Correct_of_table commonInputCorrect leaf1S1Correct) leaf1S2Correct leaf1S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf1Signs i hi j hj k hk

theorem leaf1 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (0 : ℝ) ≤ d)
    (hd1 : d ≤ (1/2 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf1Certificate
  rwa [commonIdentity] at hb


private def leaf4W1Data : IntTable :=
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

private def leaf4W1Numer (k i : ℕ) : ℤ :=
  leaf4W1Data.get (k * 5 + i)

private def leaf4W1 (k i : ℕ) : ℚ :=
  (leaf4W1Numer k i : ℚ) / 1

private theorem leaf4W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf4W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf4W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf4W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf4W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf4W1, neg_div] using he

private def leaf4W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (256 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (64 : ℤ))))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (1024 : ℤ)))))
    (.node 3 (.node 1 (.leaf (576 : ℤ))
    (.node 1 (.leaf (320 : ℤ))
    (.leaf (176 : ℤ))))
    (.node 1 (.leaf (96 : ℤ))
    (.node 1 (.leaf (1536 : ℤ))
    (.leaf (960 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (592 : ℤ))
    (.node 1 (.leaf (360 : ℤ))
    (.leaf (216 : ℤ))))
    (.node 1 (.leaf (1024 : ℤ))
    (.node 1 (.leaf (704 : ℤ))
    (.leaf (480 : ℤ)))))
    (.node 3 (.node 1 (.leaf (324 : ℤ))
    (.node 1 (.leaf (216 : ℤ))
    (.leaf (256 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (81 : ℤ)))))))

private def leaf4W2Numer (k i : ℕ) : ℤ :=
  leaf4W2Data.get (k * 5 + i)

private def leaf4W2 (k i : ℕ) : ℚ :=
  (leaf4W2Numer k i : ℚ) / 256

private theorem leaf4W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf4W2Numer k i = intTransWeight 4 (2) 1 4 k i := by
  decide +kernel

private theorem leaf4W2Correct : WeightsCorrect 4 ((1/2) : ℚ) ((1/4) : ℚ) leaf4W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (2) 1 4 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf4W2NumerCorrect k hk i hi] at he
  norm_num only [show (4 : ℚ)^4 = 256 by norm_num,
    show (2 : ℚ)/4 = (1/2) by norm_num,
    show (1 : ℚ)/4 = (1/4) by norm_num] at he
  simpa only [leaf4W2, neg_div] using he

private def leaf4W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (8 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ))))))

private def leaf4W3Numer (k i : ℕ) : ℤ :=
  leaf4W3Data.get (k * 4 + i)

private def leaf4W3 (k i : ℕ) : ℚ :=
  (leaf4W3Numer k i : ℚ) / 8

private theorem leaf4W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf4W3Numer k i = intTransWeight 3 (0) 1 2 k i := by
  decide +kernel

private theorem leaf4W3Correct : WeightsCorrect 3 (0 : ℚ) ((1/2) : ℚ) leaf4W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (0) 1 2 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf4W3NumerCorrect k hk i hi] at he
  norm_num only [show (2 : ℚ)^3 = 8 by norm_num,
    show (0 : ℚ)/2 = 0 by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num] at he
  simpa only [leaf4W3, neg_div] using he

private def leaf4S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf4S1Numer (i j k : ℕ) : ℤ :=
  leaf4S1Data.get ((i * 5 + j) * 4 + k)

private def leaf4S1 (i j k : ℕ) : ℚ :=
  (leaf4S1Numer i j k : ℚ) / 729

private theorem leaf4S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf4S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf4W1Numer h i := by
  decide +kernel

private theorem leaf4S1Correct : Axis1Correct 4 4 3 leaf4W1 commonInput leaf4S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf4W1Numer h) (leaf4S1Numer h j k) 729 1 4
    (leaf4S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf4S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (7776 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (27216 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (33048 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (16524 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (2916 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (16128 : ℤ))))
    (.node 2 (.node 1 (.leaf (4608 : ℤ))
    (.leaf (2304 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (53136 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (17280 : ℤ))
    (.node 1 (.leaf (9216 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (59256 : ℤ))
    (.node 1 (.leaf (22464 : ℤ))
    (.leaf (13824 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (26604 : ℤ))
    (.leaf (11520 : ℤ))))
    (.node 1 (.leaf (9216 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4266 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1728 : ℤ))
    (.node 1 (.leaf (2304 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (12576 : ℤ))
    (.node 1 (.leaf (5184 : ℤ))
    (.leaf (8064 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (39840 : ℤ))
    (.leaf (14880 : ℤ))))
    (.node 2 (.node 1 (.leaf (33216 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (43008 : ℤ))
    (.leaf (9744 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (51264 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (20040 : ℤ))))
    (.node 1 (.leaf (-4200 : ℤ))
    (.node 1 (.leaf (35136 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4086 : ℤ))
    (.node 1 (.leaf (-4248 : ℤ))
    (.leaf (9024 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4608 : ℤ))
    (.leaf (1024 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (6656 : ℤ))
    (.node 1 (.leaf (512 : ℤ))
    (.leaf (14688 : ℤ))))
    (.node 1 (.leaf (-832 : ℤ))
    (.node 1 (.leaf (26688 : ℤ))
    (.leaf (2048 : ℤ)))))
    (.node 3 (.node 1 (.leaf (16832 : ℤ))
    (.node 1 (.leaf (-10496 : ℤ))
    (.leaf (39840 : ℤ))))
    (.node 2 (.node 1 (.leaf (3072 : ℤ))
    (.leaf (9384 : ℤ)))
    (.node 1 (.leaf (-13968 : ℤ))
    (.leaf (26240 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2048 : ℤ))
    (.node 1 (.leaf (2448 : ℤ))
    (.leaf (-5328 : ℤ))))
    (.node 1 (.leaf (6432 : ℤ))
    (.node 1 (.leaf (512 : ℤ))
    (.leaf (672 : ℤ)))))
    (.node 3 (.node 1 (.leaf (64 : ℤ))
    (.node 1 (.leaf (896 : ℤ))
    (.leaf (768 : ℤ))))
    (.node 1 (.leaf (2144 : ℤ))
    (.node 1 (.leaf (-352 : ℤ))
    (.leaf (2688 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (3200 : ℤ))
    (.node 1 (.leaf (2464 : ℤ))
    (.leaf (-1328 : ℤ))))
    (.node 1 (.leaf (2400 : ℤ))
    (.node 1 (.leaf (4992 : ℤ))
    (.leaf (1320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-1128 : ℤ))
    (.node 1 (.leaf (320 : ℤ))
    (.leaf (3456 : ℤ))))
    (.node 2 (.node 1 (.leaf (270 : ℤ))
    (.leaf (-216 : ℤ)))
    (.node 1 (.leaf (-288 : ℤ))
    (.leaf (896 : ℤ)))))))))

private def leaf4S2Numer (i j k : ℕ) : ℤ :=
  leaf4S2Data.get ((i * 5 + j) * 4 + k)

private def leaf4S2 (i j k : ℕ) : ℚ :=
  (leaf4S2Numer i j k : ℚ) / 186624

private theorem leaf4S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf4S2Numer k j h = ∑ i ∈ range 5, leaf4S1Numer k i h * leaf4W2Numer j i := by
  decide +kernel

private theorem leaf4S2Correct : Axis2Correct 4 4 3 leaf4W2 leaf4S1 leaf4S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf4S1Numer k i h) (leaf4W2Numer j) (leaf4S2Numer k j h) 729 256 4
    (leaf4S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*256 = 186624 by norm_num] at he
  exact he

private def leaf4S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (62208 : ℤ))
    (.node 1 (.leaf (186624 : ℤ))
    (.leaf (186624 : ℤ))))
    (.node 1 (.leaf (62208 : ℤ))
    (.node 1 (.leaf (217728 : ℤ))
    (.leaf (653184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (653184 : ℤ))
    (.node 1 (.leaf (217728 : ℤ))
    (.leaf (264384 : ℤ))))
    (.node 1 (.leaf (793152 : ℤ))
    (.node 1 (.leaf (793152 : ℤ))
    (.leaf (264384 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (132192 : ℤ))
    (.node 1 (.leaf (396576 : ℤ))
    (.leaf (396576 : ℤ))))
    (.node 1 (.leaf (132192 : ℤ))
    (.node 1 (.leaf (23328 : ℤ))
    (.leaf (69984 : ℤ)))))
    (.node 3 (.node 1 (.leaf (69984 : ℤ))
    (.node 1 (.leaf (23328 : ℤ))
    (.leaf (129024 : ℤ))))
    (.node 2 (.node 1 (.leaf (405504 : ℤ))
    (.leaf (428544 : ℤ)))
    (.node 1 (.leaf (152064 : ℤ))
    (.leaf (425088 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1344384 : ℤ))
    (.node 1 (.leaf (1431936 : ℤ))
    (.leaf (512640 : ℤ))))
    (.node 1 (.leaf (474048 : ℤ))
    (.node 1 (.leaf (1512000 : ℤ))
    (.leaf (1629504 : ℤ)))))
    (.node 3 (.node 1 (.leaf (591552 : ℤ))
    (.node 1 (.leaf (212832 : ℤ))
    (.leaf (684576 : ℤ))))
    (.node 1 (.leaf (749088 : ℤ))
    (.node 1 (.leaf (277344 : ℤ))
    (.leaf (34128 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (109296 : ℤ))
    (.node 1 (.leaf (120816 : ℤ))
    (.leaf (45648 : ℤ))))
    (.node 1 (.leaf (100608 : ℤ))
    (.node 1 (.leaf (322560 : ℤ))
    (.leaf (359424 : ℤ)))))
    (.node 3 (.node 1 (.leaf (137472 : ℤ))
    (.node 1 (.leaf (318720 : ℤ))
    (.leaf (1015680 : ℤ))))
    (.node 2 (.node 1 (.leaf (1141632 : ℤ))
    (.leaf (444672 : ℤ)))
    (.node 1 (.leaf (344064 : ℤ))
    (.leaf (1071168 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1212672 : ℤ))
    (.node 1 (.leaf (485568 : ℤ))
    (.leaf (160320 : ℤ))))
    (.node 1 (.leaf (464160 : ℤ))
    (.node 1 (.leaf (517632 : ℤ))
    (.leaf (213792 : ℤ)))))
    (.node 3 (.node 1 (.leaf (32688 : ℤ))
    (.node 1 (.leaf (81072 : ℤ))
    (.leaf (82128 : ℤ))))
    (.node 1 (.leaf (33744 : ℤ))
    (.node 1 (.leaf (36864 : ℤ))
    (.leaf (114688 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (132096 : ℤ))
    (.node 1 (.leaf (54784 : ℤ))
    (.leaf (117504 : ℤ))))
    (.node 1 (.leaf (349184 : ℤ))
    (.node 1 (.leaf (399232 : ℤ))
    (.leaf (169600 : ℤ)))))
    (.node 3 (.node 1 (.leaf (134656 : ℤ))
    (.node 1 (.leaf (361984 : ℤ))
    (.leaf (399680 : ℤ))))
    (.node 2 (.node 1 (.leaf (175424 : ℤ))
    (.leaf (75072 : ℤ)))
    (.node 1 (.leaf (169344 : ℤ))
    (.leaf (165952 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (73728 : ℤ))
    (.node 1 (.leaf (19584 : ℤ))
    (.leaf (37440 : ℤ))))
    (.node 1 (.leaf (28992 : ℤ))
    (.node 1 (.leaf (11648 : ℤ))
    (.leaf (5376 : ℤ)))))
    (.node 3 (.node 1 (.leaf (16384 : ℤ))
    (.node 1 (.leaf (18432 : ℤ))
    (.leaf (8192 : ℤ))))
    (.node 1 (.leaf (17152 : ℤ))
    (.node 1 (.leaf (50048 : ℤ))
    (.leaf (54016 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (24320 : ℤ))
    (.node 1 (.leaf (19712 : ℤ))
    (.leaf (53824 : ℤ))))
    (.node 1 (.leaf (53312 : ℤ))
    (.node 1 (.leaf (24192 : ℤ))
    (.leaf (10560 : ℤ)))))
    (.node 3 (.node 1 (.leaf (27168 : ℤ))
    (.node 1 (.leaf (23296 : ℤ))
    (.leaf (10144 : ℤ))))
    (.node 2 (.node 1 (.leaf (2160 : ℤ))
    (.leaf (5616 : ℤ)))
    (.node 1 (.leaf (4176 : ℤ))
    (.leaf (1616 : ℤ)))))))))

private def leaf4S3Numer (i j k : ℕ) : ℤ :=
  leaf4S3Data.get ((i * 5 + j) * 4 + k)

private def leaf4S3 (i j k : ℕ) : ℚ :=
  (leaf4S3Numer i j k : ℚ) / 1492992

private theorem leaf4S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf4S3Numer k j h = ∑ i ∈ range 4, leaf4S2Numer k j i * leaf4W3Numer h i := by
  decide +kernel

private theorem leaf4S3Correct : Axis3Correct 4 4 3 leaf4W3 leaf4S2 leaf4S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf4S2Numer k j i) (leaf4W3Numer h) (leaf4S3Numer k j h) 186624 8 3
    (leaf4S3NumerCorrect k hk j hj h hh)
  norm_num only [show (186624 : ℚ)*8 = 1492992 by norm_num] at he
  exact he

private theorem leaf4NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf4S3Numer i j k := by
  decide +kernel

private theorem leaf4Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf4S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf4NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf4Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) (0 : ℚ) ((1/2) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf4S1 leaf4S2 leaf4S3 4 4 3 (0 : ℚ) (1 : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) (0 : ℚ) ((1/2) : ℚ) leaf4W1 leaf4W2 leaf4W3
    leaf4W1Correct leaf4W2Correct leaf4W3Correct
    (axis1Correct_of_table commonInputCorrect leaf4S1Correct) leaf4S2Correct leaf4S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf4Signs i hi j hj k hk

theorem leaf4 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (1/2 : ℝ) ≤ d)
    (hd1 : d ≤ (3/4 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf4Certificate
  rwa [commonIdentity] at hb


private def leaf6W1Data : IntTable :=
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

private def leaf6W1Numer (k i : ℕ) : ℤ :=
  leaf6W1Data.get (k * 5 + i)

private def leaf6W1 (k i : ℕ) : ℚ :=
  (leaf6W1Numer k i : ℚ) / 1

private theorem leaf6W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf6W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf6W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf6W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf6W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf6W1, neg_div] using he

private def leaf6W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (4096 : ℤ))
    (.node 1 (.leaf (3072 : ℤ))
    (.leaf (2304 : ℤ))))
    (.node 1 (.leaf (1728 : ℤ))
    (.node 1 (.leaf (1296 : ℤ))
    (.leaf (16384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (12800 : ℤ))
    (.node 1 (.leaf (9984 : ℤ))
    (.leaf (7776 : ℤ))))
    (.node 1 (.leaf (6048 : ℤ))
    (.node 1 (.leaf (24576 : ℤ))
    (.leaf (19968 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (16192 : ℤ))
    (.node 1 (.leaf (13104 : ℤ))
    (.leaf (10584 : ℤ))))
    (.node 1 (.leaf (16384 : ℤ))
    (.node 1 (.leaf (13824 : ℤ))
    (.leaf (11648 : ℤ)))))
    (.node 3 (.node 1 (.leaf (9800 : ℤ))
    (.node 1 (.leaf (8232 : ℤ))
    (.leaf (4096 : ℤ))))
    (.node 2 (.node 1 (.leaf (3584 : ℤ))
    (.leaf (3136 : ℤ)))
    (.node 1 (.leaf (2744 : ℤ))
    (.leaf (2401 : ℤ)))))))

private def leaf6W2Numer (k i : ℕ) : ℤ :=
  leaf6W2Data.get (k * 5 + i)

private def leaf6W2 (k i : ℕ) : ℚ :=
  (leaf6W2Numer k i : ℚ) / 4096

private theorem leaf6W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf6W2Numer k i = intTransWeight 4 (6) 1 8 k i := by
  decide +kernel

private theorem leaf6W2Correct : WeightsCorrect 4 ((3/4) : ℚ) ((1/8) : ℚ) leaf6W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (6) 1 8 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf6W2NumerCorrect k hk i hi] at he
  norm_num only [show (8 : ℚ)^4 = 4096 by norm_num,
    show (6 : ℚ)/8 = (3/4) by norm_num,
    show (1 : ℚ)/8 = (1/8) by norm_num] at he
  simpa only [leaf6W2, neg_div] using he

private def leaf6W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (8 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ))))))

private def leaf6W3Numer (k i : ℕ) : ℤ :=
  leaf6W3Data.get (k * 4 + i)

private def leaf6W3 (k i : ℕ) : ℚ :=
  (leaf6W3Numer k i : ℚ) / 8

private theorem leaf6W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf6W3Numer k i = intTransWeight 3 (0) 1 2 k i := by
  decide +kernel

private theorem leaf6W3Correct : WeightsCorrect 3 (0 : ℚ) ((1/2) : ℚ) leaf6W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (0) 1 2 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf6W3NumerCorrect k hk i hi] at he
  norm_num only [show (2 : ℚ)^3 = 8 by norm_num,
    show (0 : ℚ)/2 = 0 by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num] at he
  simpa only [leaf6W3, neg_div] using he

private def leaf6S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf6S1Numer (i j k : ℕ) : ℤ :=
  leaf6S1Data.get ((i * 5 + j) * 4 + k)

private def leaf6S1 (i j k : ℕ) : ℚ :=
  (leaf6S1Numer i j k : ℚ) / 729

private theorem leaf6S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf6S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf6W1Numer h i := by
  decide +kernel

private theorem leaf6S1Correct : Axis1Correct 4 4 3 leaf6W1 commonInput leaf6S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf6W1Numer h) (leaf6S1Numer h j k) 729 1 4
    (leaf6S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf6S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (46656 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (147744 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (167184 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (79704 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (13608 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (68256 : ℤ))))
    (.node 2 (.node 1 (.leaf (27648 : ℤ))
    (.leaf (36864 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (196704 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (73728 : ℤ))
    (.node 1 (.leaf (147456 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (200736 : ℤ))
    (.node 1 (.leaf (48384 : ℤ))
    (.leaf (221184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (89640 : ℤ))
    (.leaf (-13824 : ℤ))))
    (.node 1 (.leaf (147456 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (17262 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-16128 : ℤ))
    (.node 1 (.leaf (36864 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (65376 : ℤ))
    (.node 1 (.leaf (-67968 : ℤ))
    (.leaf (144384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (231936 : ℤ))
    (.leaf (-374208 : ℤ))))
    (.node 2 (.node 1 (.leaf (585216 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (333168 : ℤ))
    (.leaf (-727392 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (889344 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (236832 : ℤ))))
    (.node 1 (.leaf (-603600 : ℤ))
    (.node 1 (.leaf (600576 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (70014 : ℤ))
    (.node 1 (.leaf (-182448 : ℤ))
    (.leaf (152064 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (39168 : ℤ))
    (.leaf (-85248 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (102912 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (159936 : ℤ))))
    (.node 1 (.leaf (-399744 : ℤ))
    (.node 1 (.leaf (407552 : ℤ))
    (.leaf (32768 : ℤ)))))
    (.node 3 (.node 1 (.leaf (258272 : ℤ))
    (.node 1 (.leaf (-689984 : ℤ))
    (.leaf (604032 : ℤ))))
    (.node 2 (.node 1 (.leaf (49152 : ℤ))
    (.leaf (194640 : ℤ)))
    (.node 1 (.leaf (-520864 : ℤ))
    (.leaf (397056 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (32768 : ℤ))
    (.node 1 (.leaf (56952 : ℤ))
    (.leaf (-145376 : ℤ))))
    (.node 1 (.leaf (97664 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (4320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-3456 : ℤ))
    (.node 1 (.leaf (-4608 : ℤ))
    (.leaf (14336 : ℤ))))
    (.node 1 (.leaf (15360 : ℤ))
    (.node 1 (.leaf (-11712 : ℤ))
    (.leaf (-30208 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (58368 : ℤ))
    (.node 1 (.leaf (20656 : ℤ))
    (.leaf (-11360 : ℤ))))
    (.node 1 (.leaf (-64128 : ℤ))
    (.node 1 (.leaf (89088 : ℤ))
    (.leaf (12320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-976 : ℤ))
    (.node 1 (.leaf (-56064 : ℤ))
    (.leaf (60416 : ℤ))))
    (.node 2 (.node 1 (.leaf (2646 : ℤ))
    (.leaf (2128 : ℤ)))
    (.node 1 (.leaf (-17536 : ℤ))
    (.leaf (15360 : ℤ)))))))))

private def leaf6S2Numer (i j k : ℕ) : ℤ :=
  leaf6S2Data.get ((i * 5 + j) * 4 + k)

private def leaf6S2 (i j k : ℕ) : ℚ :=
  (leaf6S2Numer i j k : ℚ) / 2985984

private theorem leaf6S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf6S2Numer k j h = ∑ i ∈ range 5, leaf6S1Numer k i h * leaf6W2Numer j i := by
  decide +kernel

private theorem leaf6S2Correct : Axis2Correct 4 4 3 leaf6W2 leaf6S1 leaf6S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf6S1Numer k i h) (leaf6W2Numer j) (leaf6S2Numer k j h) 729 4096 4
    (leaf6S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*4096 = 2985984 by norm_num] at he
  exact he

private def leaf6S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (373248 : ℤ))
    (.node 1 (.leaf (1119744 : ℤ))
    (.leaf (1119744 : ℤ))))
    (.node 1 (.leaf (373248 : ℤ))
    (.node 1 (.leaf (1181952 : ℤ))
    (.leaf (3545856 : ℤ)))))
    (.node 3 (.node 1 (.leaf (3545856 : ℤ))
    (.node 1 (.leaf (1181952 : ℤ))
    (.leaf (1337472 : ℤ))))
    (.node 1 (.leaf (4012416 : ℤ))
    (.node 1 (.leaf (4012416 : ℤ))
    (.leaf (1337472 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (637632 : ℤ))
    (.node 1 (.leaf (1912896 : ℤ))
    (.leaf (1912896 : ℤ))))
    (.node 1 (.leaf (637632 : ℤ))
    (.node 1 (.leaf (108864 : ℤ))
    (.leaf (326592 : ℤ)))))
    (.node 3 (.node 1 (.leaf (326592 : ℤ))
    (.node 1 (.leaf (108864 : ℤ))
    (.leaf (546048 : ℤ))))
    (.node 2 (.node 1 (.leaf (1748736 : ℤ))
    (.leaf (1933056 : ℤ)))
    (.node 1 (.leaf (730368 : ℤ))
    (.leaf (1573632 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (5015808 : ℤ))
    (.node 1 (.leaf (5605632 : ℤ))
    (.leaf (2163456 : ℤ))))
    (.node 1 (.leaf (1605888 : ℤ))
    (.node 1 (.leaf (5011200 : ℤ))
    (.leaf (5647104 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2241792 : ℤ))
    (.node 1 (.leaf (717120 : ℤ))
    (.leaf (2096064 : ℤ))))
    (.node 1 (.leaf (2335680 : ℤ))
    (.node 1 (.leaf (956736 : ℤ))
    (.leaf (138096 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (349776 : ℤ))
    (.node 1 (.leaf (358992 : ℤ))
    (.leaf (147312 : ℤ))))
    (.node 1 (.leaf (523008 : ℤ))
    (.node 1 (.leaf (1297152 : ℤ))
    (.leaf (1314048 : ℤ)))))
    (.node 3 (.node 1 (.leaf (539904 : ℤ))
    (.node 1 (.leaf (1855488 : ℤ))
    (.leaf (4069632 : ℤ))))
    (.node 2 (.node 1 (.leaf (3743232 : ℤ))
    (.leaf (1529088 : ℤ)))
    (.node 1 (.leaf (2665344 : ℤ))
    (.leaf (5086464 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (3955584 : ℤ))
    (.node 1 (.leaf (1534464 : ℤ))
    (.leaf (1894656 : ℤ))))
    (.node 1 (.leaf (3269568 : ℤ))
    (.node 1 (.leaf (2056320 : ℤ))
    (.leaf (681408 : ℤ)))))
    (.node 3 (.node 1 (.leaf (560112 : ℤ))
    (.node 1 (.leaf (950544 : ℤ))
    (.leaf (524880 : ℤ))))
    (.node 1 (.leaf (134448 : ℤ))
    (.node 1 (.leaf (313344 : ℤ))
    (.leaf (599040 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (463872 : ℤ))
    (.node 1 (.leaf (186368 : ℤ))
    (.leaf (1279488 : ℤ))))
    (.node 1 (.leaf (2239488 : ℤ))
    (.node 1 (.leaf (1455616 : ℤ))
    (.leaf (528384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2066176 : ℤ))
    (.node 1 (.leaf (3438592 : ℤ))
    (.leaf (1886720 : ℤ))))
    (.node 2 (.node 1 (.leaf (563456 : ℤ))
    (.leaf (1557120 : ℤ)))
    (.node 1 (.leaf (2587904 : ℤ))
    (.leaf (1298560 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (300544 : ℤ))
    (.node 1 (.leaf (455616 : ℤ))
    (.leaf (785344 : ℤ))))
    (.node 1 (.leaf (399168 : ℤ))
    (.node 1 (.leaf (77632 : ℤ))
    (.leaf (34560 : ℤ)))))
    (.node 3 (.node 1 (.leaf (89856 : ℤ))
    (.node 1 (.leaf (66816 : ℤ))
    (.leaf (25856 : ℤ))))
    (.node 1 (.leaf (122880 : ℤ))
    (.node 1 (.leaf (321792 : ℤ))
    (.leaf (214528 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (73984 : ℤ))
    (.node 1 (.leaf (165248 : ℤ))
    (.leaf (450304 : ℤ))))
    (.node 1 (.leaf (276608 : ℤ))
    (.node 1 (.leaf (80640 : ℤ))
    (.leaf (98560 : ℤ)))))
    (.node 3 (.node 1 (.leaf (291776 : ℤ))
    (.node 1 (.leaf (175744 : ℤ))
    (.leaf (42944 : ℤ))))
    (.node 2 (.node 1 (.leaf (21168 : ℤ))
    (.leaf (72016 : ℤ)))
    (.node 1 (.leaf (45456 : ℤ))
    (.leaf (9968 : ℤ)))))))))

private def leaf6S3Numer (i j k : ℕ) : ℤ :=
  leaf6S3Data.get ((i * 5 + j) * 4 + k)

private def leaf6S3 (i j k : ℕ) : ℚ :=
  (leaf6S3Numer i j k : ℚ) / 23887872

private theorem leaf6S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf6S3Numer k j h = ∑ i ∈ range 4, leaf6S2Numer k j i * leaf6W3Numer h i := by
  decide +kernel

private theorem leaf6S3Correct : Axis3Correct 4 4 3 leaf6W3 leaf6S2 leaf6S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf6S2Numer k j i) (leaf6W3Numer h) (leaf6S3Numer k j h) 2985984 8 3
    (leaf6S3NumerCorrect k hk j hj h hh)
  norm_num only [show (2985984 : ℚ)*8 = 23887872 by norm_num] at he
  exact he

private theorem leaf6NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf6S3Numer i j k := by
  decide +kernel

private theorem leaf6Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf6S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf6NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf6Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((3/4) : ℚ) ((1/8) : ℚ) (0 : ℚ) ((1/2) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf6S1 leaf6S2 leaf6S3 4 4 3 (0 : ℚ) (1 : ℚ) ((3/4) : ℚ) ((1/8) : ℚ) (0 : ℚ) ((1/2) : ℚ) leaf6W1 leaf6W2 leaf6W3
    leaf6W1Correct leaf6W2Correct leaf6W3Correct
    (axis1Correct_of_table commonInputCorrect leaf6S1Correct) leaf6S2Correct leaf6S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf6Signs i hi j hj k hk

theorem leaf6 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (3/4 : ℝ) ≤ d)
    (hd1 : d ≤ (7/8 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf6Certificate
  rwa [commonIdentity] at hb


private def leaf7W1Data : IntTable :=
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

private def leaf7W1Numer (k i : ℕ) : ℤ :=
  leaf7W1Data.get (k * 5 + i)

private def leaf7W1 (k i : ℕ) : ℚ :=
  (leaf7W1Numer k i : ℚ) / 1

private theorem leaf7W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf7W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf7W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf7W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf7W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf7W1, neg_div] using he

private def leaf7W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (4096 : ℤ))
    (.node 1 (.leaf (3584 : ℤ))
    (.leaf (3136 : ℤ))))
    (.node 1 (.leaf (2744 : ℤ))
    (.node 1 (.leaf (2401 : ℤ))
    (.leaf (16384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (14848 : ℤ))
    (.node 1 (.leaf (13440 : ℤ))
    (.leaf (12152 : ℤ))))
    (.node 1 (.leaf (10976 : ℤ))
    (.node 1 (.leaf (24576 : ℤ))
    (.leaf (23040 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21568 : ℤ))
    (.node 1 (.leaf (20160 : ℤ))
    (.leaf (18816 : ℤ))))
    (.node 1 (.leaf (16384 : ℤ))
    (.node 1 (.leaf (15872 : ℤ))
    (.leaf (15360 : ℤ)))))
    (.node 3 (.node 1 (.leaf (14848 : ℤ))
    (.node 1 (.leaf (14336 : ℤ))
    (.leaf (4096 : ℤ))))
    (.node 2 (.node 1 (.leaf (4096 : ℤ))
    (.leaf (4096 : ℤ)))
    (.node 1 (.leaf (4096 : ℤ))
    (.leaf (4096 : ℤ)))))))

private def leaf7W2Numer (k i : ℕ) : ℤ :=
  leaf7W2Data.get (k * 5 + i)

private def leaf7W2 (k i : ℕ) : ℚ :=
  (leaf7W2Numer k i : ℚ) / 4096

private theorem leaf7W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf7W2Numer k i = intTransWeight 4 (7) 1 8 k i := by
  decide +kernel

private theorem leaf7W2Correct : WeightsCorrect 4 ((7/8) : ℚ) ((1/8) : ℚ) leaf7W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (7) 1 8 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf7W2NumerCorrect k hk i hi] at he
  norm_num only [show (8 : ℚ)^4 = 4096 by norm_num,
    show (7 : ℚ)/8 = (7/8) by norm_num,
    show (1 : ℚ)/8 = (1/8) by norm_num] at he
  simpa only [leaf7W2, neg_div] using he

private def leaf7W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (8 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ))))))

private def leaf7W3Numer (k i : ℕ) : ℤ :=
  leaf7W3Data.get (k * 4 + i)

private def leaf7W3 (k i : ℕ) : ℚ :=
  (leaf7W3Numer k i : ℚ) / 8

private theorem leaf7W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf7W3Numer k i = intTransWeight 3 (0) 1 2 k i := by
  decide +kernel

private theorem leaf7W3Correct : WeightsCorrect 3 (0 : ℚ) ((1/2) : ℚ) leaf7W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (0) 1 2 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf7W3NumerCorrect k hk i hi] at he
  norm_num only [show (2 : ℚ)^3 = 8 by norm_num,
    show (0 : ℚ)/2 = 0 by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num] at he
  simpa only [leaf7W3, neg_div] using he

private def leaf7S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf7S1Numer (i j k : ℕ) : ℤ :=
  leaf7S1Data.get ((i * 5 + j) * 4 + k)

private def leaf7S1 (i j k : ℕ) : ℚ :=
  (leaf7S1Numer i j k : ℚ) / 729

private theorem leaf7S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf7S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf7W1Numer h i := by
  decide +kernel

private theorem leaf7S1Correct : Axis1Correct 4 4 3 leaf7W1 commonInput leaf7S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf7W1Numer h) (leaf7S1Numer h j k) 729 1 4
    (leaf7S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf7S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (13608 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (29160 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (15552 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (17262 : ℤ))))
    (.node 2 (.node 1 (.leaf (-16128 : ℤ))
    (.leaf (36864 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (48456 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (-115200 : ℤ))
    (.node 1 (.leaf (147456 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (77184 : ℤ))
    (.node 1 (.leaf (-255744 : ℤ))
    (.leaf (221184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (82944 : ℤ))
    (.leaf (-230400 : ℤ))))
    (.node 1 (.leaf (147456 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (36864 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-73728 : ℤ))
    (.node 1 (.leaf (36864 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (70014 : ℤ))
    (.node 1 (.leaf (-182448 : ℤ))
    (.leaf (152064 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (323280 : ℤ))
    (.leaf (-855984 : ℤ))))
    (.node 2 (.node 1 (.leaf (615936 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (592512 : ℤ))
    (.leaf (-1484544 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (935424 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (499200 : ℤ))))
    (.node 1 (.leaf (-1130496 : ℤ))
    (.node 1 (.leaf (631296 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (159744 : ℤ))
    (.node 1 (.leaf (-319488 : ℤ))
    (.leaf (159744 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (56952 : ℤ))
    (.leaf (-145376 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (97664 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (260976 : ℤ))))
    (.node 1 (.leaf (-642144 : ℤ))
    (.node 1 (.leaf (384256 : ℤ))
    (.leaf (32768 : ℤ)))))
    (.node 3 (.node 1 (.leaf (457280 : ℤ))
    (.node 1 (.leaf (-1053824 : ℤ))
    (.leaf (565632 : ℤ))))
    (.node 2 (.node 1 (.leaf (49152 : ℤ))
    (.leaf (359936 : ℤ)))
    (.node 1 (.leaf (-761856 : ℤ))
    (.leaf (369152 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (32768 : ℤ))
    (.node 1 (.leaf (106496 : ℤ))
    (.leaf (-204800 : ℤ))))
    (.node 1 (.leaf (90112 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (2646 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2128 : ℤ))
    (.node 1 (.leaf (-17536 : ℤ))
    (.leaf (15360 : ℤ))))
    (.node 1 (.leaf (8848 : ℤ))
    (.node 1 (.leaf (18000 : ℤ))
    (.leaf (-84224 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (62464 : ℤ))
    (.node 1 (.leaf (10240 : ℤ))
    (.leaf (45568 : ℤ))))
    (.node 1 (.leaf (-148608 : ℤ))
    (.node 1 (.leaf (95232 : ℤ))
    (.leaf (4096 : ℤ)))))
    (.node 3 (.node 1 (.leaf (46080 : ℤ))
    (.node 1 (.leaf (-114688 : ℤ))
    (.leaf (64512 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (16384 : ℤ)))
    (.node 1 (.leaf (-32768 : ℤ))
    (.leaf (16384 : ℤ)))))))))

private def leaf7S2Numer (i j k : ℕ) : ℤ :=
  leaf7S2Data.get ((i * 5 + j) * 4 + k)

private def leaf7S2 (i j k : ℕ) : ℚ :=
  (leaf7S2Numer i j k : ℚ) / 2985984

private theorem leaf7S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf7S2Numer k j h = ∑ i ∈ range 5, leaf7S1Numer k i h * leaf7W2Numer j i := by
  decide +kernel

private theorem leaf7S2Correct : Axis2Correct 4 4 3 leaf7W2 leaf7S1 leaf7S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf7S1Numer k i h) (leaf7W2Numer j) (leaf7S2Numer k j h) 729 4096 4
    (leaf7S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*4096 = 2985984 by norm_num] at he
  exact he

private def leaf7S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (108864 : ℤ))
    (.node 1 (.leaf (326592 : ℤ))
    (.leaf (326592 : ℤ))))
    (.node 1 (.leaf (108864 : ℤ))
    (.node 1 (.leaf (233280 : ℤ))
    (.leaf (699840 : ℤ)))))
    (.node 3 (.node 1 (.leaf (699840 : ℤ))
    (.node 1 (.leaf (233280 : ℤ))
    (.leaf (124416 : ℤ))))
    (.node 1 (.leaf (373248 : ℤ))
    (.node 1 (.leaf (373248 : ℤ))
    (.leaf (124416 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (138096 : ℤ))))
    (.node 2 (.node 1 (.leaf (349776 : ℤ))
    (.leaf (358992 : ℤ)))
    (.node 1 (.leaf (147312 : ℤ))
    (.leaf (387648 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (702144 : ℤ))
    (.node 1 (.leaf (536256 : ℤ))
    (.leaf (221760 : ℤ))))
    (.node 1 (.leaf (617472 : ℤ))
    (.node 1 (.leaf (829440 : ℤ))
    (.leaf (248832 : ℤ)))))
    (.node 3 (.node 1 (.leaf (36864 : ℤ))
    (.node 1 (.leaf (663552 : ℤ))
    (.leaf (1069056 : ℤ))))
    (.node 1 (.leaf (442368 : ℤ))
    (.node 1 (.leaf (36864 : ℤ))
    (.leaf (294912 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (589824 : ℤ))
    (.node 1 (.leaf (368640 : ℤ))
    (.leaf (73728 : ℤ))))
    (.node 1 (.leaf (560112 : ℤ))
    (.node 1 (.leaf (950544 : ℤ))
    (.leaf (524880 : ℤ)))))
    (.node 3 (.node 1 (.leaf (134448 : ℤ))
    (.node 1 (.leaf (2586240 : ℤ))
    (.leaf (4334784 : ℤ))))
    (.node 2 (.node 1 (.leaf (2142720 : ℤ))
    (.leaf (394176 : ℤ)))
    (.node 1 (.leaf (4740096 : ℤ))
    (.leaf (8282112 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (4214784 : ℤ))
    (.node 1 (.leaf (672768 : ℤ))
    (.leaf (3993600 : ℤ))))
    (.node 1 (.leaf (7458816 : ℤ))
    (.node 1 (.leaf (4199424 : ℤ))
    (.leaf (734208 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1277952 : ℤ))
    (.node 1 (.leaf (2555904 : ℤ))
    (.leaf (1597440 : ℤ))))
    (.node 1 (.leaf (319488 : ℤ))
    (.node 1 (.leaf (455616 : ℤ))
    (.leaf (785344 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (399168 : ℤ))
    (.node 1 (.leaf (77632 : ℤ))
    (.leaf (2087808 : ℤ))))
    (.node 1 (.leaf (3694848 : ℤ))
    (.node 1 (.leaf (1894784 : ℤ))
    (.leaf (320512 : ℤ)))))
    (.node 3 (.node 1 (.leaf (3658240 : ℤ))
    (.node 1 (.leaf (6759424 : ℤ))
    (.leaf (3675392 : ℤ))))
    (.node 2 (.node 1 (.leaf (623360 : ℤ))
    (.leaf (2879488 : ℤ)))
    (.node 1 (.leaf (5591040 : ℤ))
    (.leaf (3281920 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (603136 : ℤ))
    (.node 1 (.leaf (851968 : ℤ))
    (.leaf (1736704 : ℤ))))
    (.node 1 (.leaf (1097728 : ℤ))
    (.node 1 (.leaf (221184 : ℤ))
    (.leaf (21168 : ℤ)))))
    (.node 3 (.node 1 (.leaf (72016 : ℤ))
    (.node 1 (.leaf (45456 : ℤ))
    (.leaf (9968 : ℤ))))
    (.node 1 (.leaf (70784 : ℤ))
    (.node 1 (.leaf (284352 : ℤ))
    (.leaf (187904 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (36800 : ℤ))
    (.node 1 (.leaf (81920 : ℤ))
    (.leaf (428032 : ℤ))))
    (.node 1 (.leaf (313088 : ℤ))
    (.node 1 (.leaf (62208 : ℤ))
    (.leaf (32768 : ℤ)))))
    (.node 3 (.node 1 (.leaf (282624 : ℤ))
    (.node 1 (.leaf (237568 : ℤ))
    (.leaf (52224 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (65536 : ℤ)))
    (.node 1 (.leaf (65536 : ℤ))
    (.leaf (16384 : ℤ)))))))))

private def leaf7S3Numer (i j k : ℕ) : ℤ :=
  leaf7S3Data.get ((i * 5 + j) * 4 + k)

private def leaf7S3 (i j k : ℕ) : ℚ :=
  (leaf7S3Numer i j k : ℚ) / 23887872

private theorem leaf7S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf7S3Numer k j h = ∑ i ∈ range 4, leaf7S2Numer k j i * leaf7W3Numer h i := by
  decide +kernel

private theorem leaf7S3Correct : Axis3Correct 4 4 3 leaf7W3 leaf7S2 leaf7S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf7S2Numer k j i) (leaf7W3Numer h) (leaf7S3Numer k j h) 2985984 8 3
    (leaf7S3NumerCorrect k hk j hj h hh)
  norm_num only [show (2985984 : ℚ)*8 = 23887872 by norm_num] at he
  exact he

private theorem leaf7NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf7S3Numer i j k := by
  decide +kernel

private theorem leaf7Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf7S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf7NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf7Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((7/8) : ℚ) ((1/8) : ℚ) (0 : ℚ) ((1/2) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf7S1 leaf7S2 leaf7S3 4 4 3 (0 : ℚ) (1 : ℚ) ((7/8) : ℚ) ((1/8) : ℚ) (0 : ℚ) ((1/2) : ℚ) leaf7W1 leaf7W2 leaf7W3
    leaf7W1Correct leaf7W2Correct leaf7W3Correct
    (axis1Correct_of_table commonInputCorrect leaf7S1Correct) leaf7S2Correct leaf7S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf7Signs i hi j hj k hk

theorem leaf7 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (7/8 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (0 : ℝ) ≤ u)
    (hu1 : u ≤ (1/2 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf7Certificate
  rwa [commonIdentity] at hb


private def leaf9W1Data : IntTable :=
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

private def leaf9W1Numer (k i : ℕ) : ℤ :=
  leaf9W1Data.get (k * 5 + i)

private def leaf9W1 (k i : ℕ) : ℚ :=
  (leaf9W1Numer k i : ℚ) / 1

private theorem leaf9W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf9W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf9W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf9W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf9W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf9W1, neg_div] using he

private def leaf9W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (256 : ℤ))
    (.node 1 (.leaf (128 : ℤ))
    (.leaf (64 : ℤ))))
    (.node 1 (.leaf (32 : ℤ))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (1024 : ℤ)))))
    (.node 3 (.node 1 (.leaf (576 : ℤ))
    (.node 1 (.leaf (320 : ℤ))
    (.leaf (176 : ℤ))))
    (.node 1 (.leaf (96 : ℤ))
    (.node 1 (.leaf (1536 : ℤ))
    (.leaf (960 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (592 : ℤ))
    (.node 1 (.leaf (360 : ℤ))
    (.leaf (216 : ℤ))))
    (.node 1 (.leaf (1024 : ℤ))
    (.node 1 (.leaf (704 : ℤ))
    (.leaf (480 : ℤ)))))
    (.node 3 (.node 1 (.leaf (324 : ℤ))
    (.node 1 (.leaf (216 : ℤ))
    (.leaf (256 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (144 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (81 : ℤ)))))))

private def leaf9W2Numer (k i : ℕ) : ℤ :=
  leaf9W2Data.get (k * 5 + i)

private def leaf9W2 (k i : ℕ) : ℚ :=
  (leaf9W2Numer k i : ℚ) / 256

private theorem leaf9W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf9W2Numer k i = intTransWeight 4 (2) 1 4 k i := by
  decide +kernel

private theorem leaf9W2Correct : WeightsCorrect 4 ((1/2) : ℚ) ((1/4) : ℚ) leaf9W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (2) 1 4 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf9W2NumerCorrect k hk i hi] at he
  norm_num only [show (4 : ℚ)^4 = 256 by norm_num,
    show (2 : ℚ)/4 = (1/2) by norm_num,
    show (1 : ℚ)/4 = (1/4) by norm_num] at he
  simpa only [leaf9W2, neg_div] using he

private def leaf9W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (4 : ℤ)))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (1 : ℤ))))
    (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (16 : ℤ)))
    (.node 1 (.leaf (10 : ℤ))
    (.leaf (6 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (24 : ℤ))
    (.leaf (20 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (12 : ℤ))))
    (.node 2 (.node 1 (.leaf (8 : ℤ))
    (.leaf (8 : ℤ)))
    (.node 1 (.leaf (8 : ℤ))
    (.leaf (8 : ℤ))))))

private def leaf9W3Numer (k i : ℕ) : ℤ :=
  leaf9W3Data.get (k * 4 + i)

private def leaf9W3 (k i : ℕ) : ℚ :=
  (leaf9W3Numer k i : ℚ) / 8

private theorem leaf9W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf9W3Numer k i = intTransWeight 3 (1) 1 2 k i := by
  decide +kernel

private theorem leaf9W3Correct : WeightsCorrect 3 ((1/2) : ℚ) ((1/2) : ℚ) leaf9W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (1) 1 2 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf9W3NumerCorrect k hk i hi] at he
  norm_num only [show (2 : ℚ)^3 = 8 by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num,
    show (1 : ℚ)/2 = (1/2) by norm_num] at he
  simpa only [leaf9W3, neg_div] using he

private def leaf9S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf9S1Numer (i j k : ℕ) : ℤ :=
  leaf9S1Data.get ((i * 5 + j) * 4 + k)

private def leaf9S1 (i j k : ℕ) : ℚ :=
  (leaf9S1Numer i j k : ℚ) / 729

private theorem leaf9S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf9S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf9W1Numer h i := by
  decide +kernel

private theorem leaf9S1Correct : Axis1Correct 4 4 3 leaf9W1 commonInput leaf9S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf9W1Numer h) (leaf9S1Numer h j k) 729 1 4
    (leaf9S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf9S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (7776 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (27216 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (33048 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (16524 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (2916 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (16128 : ℤ))))
    (.node 2 (.node 1 (.leaf (4608 : ℤ))
    (.leaf (2304 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (53136 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (17280 : ℤ))
    (.node 1 (.leaf (9216 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (59256 : ℤ))
    (.node 1 (.leaf (22464 : ℤ))
    (.leaf (13824 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (26604 : ℤ))
    (.leaf (11520 : ℤ))))
    (.node 1 (.leaf (9216 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4266 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1728 : ℤ))
    (.node 1 (.leaf (2304 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (12576 : ℤ))
    (.node 1 (.leaf (5184 : ℤ))
    (.leaf (8064 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (39840 : ℤ))
    (.leaf (14880 : ℤ))))
    (.node 2 (.node 1 (.leaf (33216 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (43008 : ℤ))
    (.leaf (9744 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (51264 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (20040 : ℤ))))
    (.node 1 (.leaf (-4200 : ℤ))
    (.node 1 (.leaf (35136 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4086 : ℤ))
    (.node 1 (.leaf (-4248 : ℤ))
    (.leaf (9024 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4608 : ℤ))
    (.leaf (1024 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (6656 : ℤ))
    (.node 1 (.leaf (512 : ℤ))
    (.leaf (14688 : ℤ))))
    (.node 1 (.leaf (-832 : ℤ))
    (.node 1 (.leaf (26688 : ℤ))
    (.leaf (2048 : ℤ)))))
    (.node 3 (.node 1 (.leaf (16832 : ℤ))
    (.node 1 (.leaf (-10496 : ℤ))
    (.leaf (39840 : ℤ))))
    (.node 2 (.node 1 (.leaf (3072 : ℤ))
    (.leaf (9384 : ℤ)))
    (.node 1 (.leaf (-13968 : ℤ))
    (.leaf (26240 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2048 : ℤ))
    (.node 1 (.leaf (2448 : ℤ))
    (.leaf (-5328 : ℤ))))
    (.node 1 (.leaf (6432 : ℤ))
    (.node 1 (.leaf (512 : ℤ))
    (.leaf (672 : ℤ)))))
    (.node 3 (.node 1 (.leaf (64 : ℤ))
    (.node 1 (.leaf (896 : ℤ))
    (.leaf (768 : ℤ))))
    (.node 1 (.leaf (2144 : ℤ))
    (.node 1 (.leaf (-352 : ℤ))
    (.leaf (2688 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (3200 : ℤ))
    (.node 1 (.leaf (2464 : ℤ))
    (.leaf (-1328 : ℤ))))
    (.node 1 (.leaf (2400 : ℤ))
    (.node 1 (.leaf (4992 : ℤ))
    (.leaf (1320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-1128 : ℤ))
    (.node 1 (.leaf (320 : ℤ))
    (.leaf (3456 : ℤ))))
    (.node 2 (.node 1 (.leaf (270 : ℤ))
    (.leaf (-216 : ℤ)))
    (.node 1 (.leaf (-288 : ℤ))
    (.leaf (896 : ℤ)))))))))

private def leaf9S2Numer (i j k : ℕ) : ℤ :=
  leaf9S2Data.get ((i * 5 + j) * 4 + k)

private def leaf9S2 (i j k : ℕ) : ℚ :=
  (leaf9S2Numer i j k : ℚ) / 186624

private theorem leaf9S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf9S2Numer k j h = ∑ i ∈ range 5, leaf9S1Numer k i h * leaf9W2Numer j i := by
  decide +kernel

private theorem leaf9S2Correct : Axis2Correct 4 4 3 leaf9W2 leaf9S1 leaf9S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf9S1Numer k i h) (leaf9W2Numer j) (leaf9S2Numer k j h) 729 256 4
    (leaf9S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*256 = 186624 by norm_num] at he
  exact he

private def leaf9S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (62208 : ℤ))
    (.node 1 (.leaf (186624 : ℤ))
    (.leaf (186624 : ℤ))))
    (.node 1 (.leaf (62208 : ℤ))
    (.node 1 (.leaf (217728 : ℤ))
    (.leaf (653184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (653184 : ℤ))
    (.node 1 (.leaf (217728 : ℤ))
    (.leaf (264384 : ℤ))))
    (.node 1 (.leaf (793152 : ℤ))
    (.node 1 (.leaf (793152 : ℤ))
    (.leaf (264384 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (132192 : ℤ))
    (.node 1 (.leaf (396576 : ℤ))
    (.leaf (396576 : ℤ))))
    (.node 1 (.leaf (132192 : ℤ))
    (.node 1 (.leaf (23328 : ℤ))
    (.leaf (69984 : ℤ)))))
    (.node 3 (.node 1 (.leaf (69984 : ℤ))
    (.node 1 (.leaf (23328 : ℤ))
    (.leaf (152064 : ℤ))))
    (.node 2 (.node 1 (.leaf (483840 : ℤ))
    (.leaf (516096 : ℤ)))
    (.node 1 (.leaf (184320 : ℤ))
    (.leaf (512640 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (1643904 : ℤ))
    (.node 1 (.leaf (1768320 : ℤ))
    (.leaf (637056 : ℤ))))
    (.node 1 (.leaf (591552 : ℤ))
    (.node 1 (.leaf (1919808 : ℤ))
    (.leaf (2092608 : ℤ)))))
    (.node 3 (.node 1 (.leaf (764352 : ℤ))
    (.node 1 (.leaf (277344 : ℤ))
    (.leaf (914976 : ℤ))))
    (.node 1 (.leaf (1016352 : ℤ))
    (.node 1 (.leaf (378720 : ℤ))
    (.leaf (45648 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (153072 : ℤ))
    (.node 1 (.leaf (173808 : ℤ))
    (.leaf (66384 : ℤ))))
    (.node 1 (.leaf (137472 : ℤ))
    (.node 1 (.leaf (465408 : ℤ))
    (.leaf (534528 : ℤ)))))
    (.node 3 (.node 1 (.leaf (206592 : ℤ))
    (.node 1 (.leaf (444672 : ℤ))
    (.leaf (1526400 : ℤ))))
    (.node 2 (.node 1 (.leaf (1785216 : ℤ))
    (.leaf (703488 : ℤ)))
    (.node 1 (.leaf (485568 : ℤ))
    (.leaf (1700736 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2047296 : ℤ))
    (.node 1 (.leaf (832128 : ℤ))
    (.leaf (213792 : ℤ))))
    (.node 1 (.leaf (765120 : ℤ))
    (.node 1 (.leaf (959136 : ℤ))
    (.leaf (407808 : ℤ)))))
    (.node 3 (.node 1 (.leaf (33744 : ℤ))
    (.node 1 (.leaf (120336 : ℤ))
    (.leaf (157488 : ℤ))))
    (.node 1 (.leaf (70896 : ℤ))
    (.node 1 (.leaf (54784 : ℤ))
    (.leaf (196608 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (243712 : ℤ))
    (.node 1 (.leaf (102400 : ℤ))
    (.leaf (169600 : ℤ))))
    (.node 1 (.leaf (618368 : ℤ))
    (.node 1 (.leaf (787456 : ℤ))
    (.leaf (340736 : ℤ)))))
    (.node 3 (.node 1 (.leaf (175424 : ℤ))
    (.node 1 (.leaf (652864 : ℤ))
    (.leaf (868352 : ℤ))))
    (.node 2 (.node 1 (.leaf (393984 : ℤ))
    (.leaf (73728 : ℤ)))
    (.node 1 (.leaf (276416 : ℤ))
    (.leaf (390272 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (189632 : ℤ))
    (.node 1 (.leaf (11648 : ℤ))
    (.leaf (40896 : ℤ))))
    (.node 1 (.leaf (61248 : ℤ))
    (.node 1 (.leaf (32512 : ℤ))
    (.leaf (8192 : ℤ)))))
    (.node 3 (.node 1 (.leaf (30720 : ℤ))
    (.node 1 (.leaf (40960 : ℤ))
    (.leaf (19200 : ℤ))))
    (.node 1 (.leaf (24320 : ℤ))
    (.node 1 (.leaf (91904 : ℤ))
    (.leaf (125824 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (61440 : ℤ))
    (.node 1 (.leaf (24192 : ℤ))
    (.leaf (91840 : ℤ))))
    (.node 1 (.leaf (130880 : ℤ))
    (.node 1 (.leaf (68224 : ℤ))
    (.leaf (10144 : ℤ)))))
    (.node 3 (.node 1 (.leaf (37568 : ℤ))
    (.node 1 (.leaf (55712 : ℤ))
    (.leaf (31744 : ℤ))))
    (.node 2 (.node 1 (.leaf (1616 : ℤ))
    (.leaf (5520 : ℤ)))
    (.node 1 (.leaf (8304 : ℤ))
    (.leaf (5296 : ℤ)))))))))

private def leaf9S3Numer (i j k : ℕ) : ℤ :=
  leaf9S3Data.get ((i * 5 + j) * 4 + k)

private def leaf9S3 (i j k : ℕ) : ℚ :=
  (leaf9S3Numer i j k : ℚ) / 1492992

private theorem leaf9S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf9S3Numer k j h = ∑ i ∈ range 4, leaf9S2Numer k j i * leaf9W3Numer h i := by
  decide +kernel

private theorem leaf9S3Correct : Axis3Correct 4 4 3 leaf9W3 leaf9S2 leaf9S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf9S2Numer k j i) (leaf9W3Numer h) (leaf9S3Numer k j h) 186624 8 3
    (leaf9S3NumerCorrect k hk j hj h hh)
  norm_num only [show (186624 : ℚ)*8 = 1492992 by norm_num] at he
  exact he

private theorem leaf9NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf9S3Numer i j k := by
  decide +kernel

private theorem leaf9Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf9S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf9NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf9Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) ((1/2) : ℚ) ((1/2) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf9S1 leaf9S2 leaf9S3 4 4 3 (0 : ℚ) (1 : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) ((1/2) : ℚ) ((1/2) : ℚ) leaf9W1 leaf9W2 leaf9W3
    leaf9W1Correct leaf9W2Correct leaf9W3Correct
    (axis1Correct_of_table commonInputCorrect leaf9S1Correct) leaf9S2Correct leaf9S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf9Signs i hi j hj k hk

theorem leaf9 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (1/2 : ℝ) ≤ d)
    (hd1 : d ≤ (3/4 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (1 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf9Certificate
  rwa [commonIdentity] at hb


private def leaf12W1Data : IntTable :=
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

private def leaf12W1Numer (k i : ℕ) : ℤ :=
  leaf12W1Data.get (k * 5 + i)

private def leaf12W1 (k i : ℕ) : ℚ :=
  (leaf12W1Numer k i : ℚ) / 1

private theorem leaf12W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf12W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf12W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf12W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf12W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf12W1, neg_div] using he

private def leaf12W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (4096 : ℤ))
    (.node 1 (.leaf (3072 : ℤ))
    (.leaf (2304 : ℤ))))
    (.node 1 (.leaf (1728 : ℤ))
    (.node 1 (.leaf (1296 : ℤ))
    (.leaf (16384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (12800 : ℤ))
    (.node 1 (.leaf (9984 : ℤ))
    (.leaf (7776 : ℤ))))
    (.node 1 (.leaf (6048 : ℤ))
    (.node 1 (.leaf (24576 : ℤ))
    (.leaf (19968 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (16192 : ℤ))
    (.node 1 (.leaf (13104 : ℤ))
    (.leaf (10584 : ℤ))))
    (.node 1 (.leaf (16384 : ℤ))
    (.node 1 (.leaf (13824 : ℤ))
    (.leaf (11648 : ℤ)))))
    (.node 3 (.node 1 (.leaf (9800 : ℤ))
    (.node 1 (.leaf (8232 : ℤ))
    (.leaf (4096 : ℤ))))
    (.node 2 (.node 1 (.leaf (3584 : ℤ))
    (.leaf (3136 : ℤ)))
    (.node 1 (.leaf (2744 : ℤ))
    (.leaf (2401 : ℤ)))))))

private def leaf12W2Numer (k i : ℕ) : ℤ :=
  leaf12W2Data.get (k * 5 + i)

private def leaf12W2 (k i : ℕ) : ℚ :=
  (leaf12W2Numer k i : ℚ) / 4096

private theorem leaf12W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf12W2Numer k i = intTransWeight 4 (6) 1 8 k i := by
  decide +kernel

private theorem leaf12W2Correct : WeightsCorrect 4 ((3/4) : ℚ) ((1/8) : ℚ) leaf12W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (6) 1 8 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf12W2NumerCorrect k hk i hi] at he
  norm_num only [show (8 : ℚ)^4 = 4096 by norm_num,
    show (6 : ℚ)/8 = (3/4) by norm_num,
    show (1 : ℚ)/8 = (1/8) by norm_num] at he
  simpa only [leaf12W2, neg_div] using he

private def leaf12W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (64 : ℤ))
    (.leaf (36 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (128 : ℤ)))
    (.node 1 (.leaf (84 : ℤ))
    (.leaf (54 : ℤ))))
    (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (36 : ℤ))
    (.leaf (27 : ℤ))))))

private def leaf12W3Numer (k i : ℕ) : ℤ :=
  leaf12W3Data.get (k * 4 + i)

private def leaf12W3 (k i : ℕ) : ℚ :=
  (leaf12W3Numer k i : ℚ) / 64

private theorem leaf12W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf12W3Numer k i = intTransWeight 3 (2) 1 4 k i := by
  decide +kernel

private theorem leaf12W3Correct : WeightsCorrect 3 ((1/2) : ℚ) ((1/4) : ℚ) leaf12W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (2) 1 4 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf12W3NumerCorrect k hk i hi] at he
  norm_num only [show (4 : ℚ)^3 = 64 by norm_num,
    show (2 : ℚ)/4 = (1/2) by norm_num,
    show (1 : ℚ)/4 = (1/4) by norm_num] at he
  simpa only [leaf12W3, neg_div] using he

private def leaf12S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf12S1Numer (i j k : ℕ) : ℤ :=
  leaf12S1Data.get ((i * 5 + j) * 4 + k)

private def leaf12S1 (i j k : ℕ) : ℚ :=
  (leaf12S1Numer i j k : ℚ) / 729

private theorem leaf12S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf12S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf12W1Numer h i := by
  decide +kernel

private theorem leaf12S1Correct : Axis1Correct 4 4 3 leaf12W1 commonInput leaf12S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf12W1Numer h) (leaf12S1Numer h j k) 729 1 4
    (leaf12S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf12S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (46656 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (147744 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (167184 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (79704 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (13608 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (68256 : ℤ))))
    (.node 2 (.node 1 (.leaf (27648 : ℤ))
    (.leaf (36864 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (196704 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (73728 : ℤ))
    (.node 1 (.leaf (147456 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (200736 : ℤ))
    (.node 1 (.leaf (48384 : ℤ))
    (.leaf (221184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (89640 : ℤ))
    (.leaf (-13824 : ℤ))))
    (.node 1 (.leaf (147456 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (17262 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-16128 : ℤ))
    (.node 1 (.leaf (36864 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (65376 : ℤ))
    (.node 1 (.leaf (-67968 : ℤ))
    (.leaf (144384 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (231936 : ℤ))
    (.leaf (-374208 : ℤ))))
    (.node 2 (.node 1 (.leaf (585216 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (333168 : ℤ))
    (.leaf (-727392 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (889344 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (236832 : ℤ))))
    (.node 1 (.leaf (-603600 : ℤ))
    (.node 1 (.leaf (600576 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (70014 : ℤ))
    (.node 1 (.leaf (-182448 : ℤ))
    (.leaf (152064 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (39168 : ℤ))
    (.leaf (-85248 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (102912 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (159936 : ℤ))))
    (.node 1 (.leaf (-399744 : ℤ))
    (.node 1 (.leaf (407552 : ℤ))
    (.leaf (32768 : ℤ)))))
    (.node 3 (.node 1 (.leaf (258272 : ℤ))
    (.node 1 (.leaf (-689984 : ℤ))
    (.leaf (604032 : ℤ))))
    (.node 2 (.node 1 (.leaf (49152 : ℤ))
    (.leaf (194640 : ℤ)))
    (.node 1 (.leaf (-520864 : ℤ))
    (.leaf (397056 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (32768 : ℤ))
    (.node 1 (.leaf (56952 : ℤ))
    (.leaf (-145376 : ℤ))))
    (.node 1 (.leaf (97664 : ℤ))
    (.node 1 (.leaf (8192 : ℤ))
    (.leaf (4320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-3456 : ℤ))
    (.node 1 (.leaf (-4608 : ℤ))
    (.leaf (14336 : ℤ))))
    (.node 1 (.leaf (15360 : ℤ))
    (.node 1 (.leaf (-11712 : ℤ))
    (.leaf (-30208 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (58368 : ℤ))
    (.node 1 (.leaf (20656 : ℤ))
    (.leaf (-11360 : ℤ))))
    (.node 1 (.leaf (-64128 : ℤ))
    (.node 1 (.leaf (89088 : ℤ))
    (.leaf (12320 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-976 : ℤ))
    (.node 1 (.leaf (-56064 : ℤ))
    (.leaf (60416 : ℤ))))
    (.node 2 (.node 1 (.leaf (2646 : ℤ))
    (.leaf (2128 : ℤ)))
    (.node 1 (.leaf (-17536 : ℤ))
    (.leaf (15360 : ℤ)))))))))

private def leaf12S2Numer (i j k : ℕ) : ℤ :=
  leaf12S2Data.get ((i * 5 + j) * 4 + k)

private def leaf12S2 (i j k : ℕ) : ℚ :=
  (leaf12S2Numer i j k : ℚ) / 2985984

private theorem leaf12S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf12S2Numer k j h = ∑ i ∈ range 5, leaf12S1Numer k i h * leaf12W2Numer j i := by
  decide +kernel

private theorem leaf12S2Correct : Axis2Correct 4 4 3 leaf12W2 leaf12S1 leaf12S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf12S1Numer k i h) (leaf12W2Numer j) (leaf12S2Numer k j h) 729 4096 4
    (leaf12S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*4096 = 2985984 by norm_num] at he
  exact he

private def leaf12S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2985984 : ℤ))
    (.node 1 (.leaf (8957952 : ℤ))
    (.leaf (8957952 : ℤ))))
    (.node 1 (.leaf (2985984 : ℤ))
    (.node 1 (.leaf (9455616 : ℤ))
    (.leaf (28366848 : ℤ)))))
    (.node 3 (.node 1 (.leaf (28366848 : ℤ))
    (.node 1 (.leaf (9455616 : ℤ))
    (.leaf (10699776 : ℤ))))
    (.node 1 (.leaf (32099328 : ℤ))
    (.node 1 (.leaf (32099328 : ℤ))
    (.leaf (10699776 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (5101056 : ℤ))
    (.node 1 (.leaf (15303168 : ℤ))
    (.leaf (15303168 : ℤ))))
    (.node 1 (.leaf (5101056 : ℤ))
    (.node 1 (.leaf (870912 : ℤ))
    (.leaf (2612736 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2612736 : ℤ))
    (.node 1 (.leaf (870912 : ℤ))
    (.leaf (5842944 : ℤ))))
    (.node 2 (.node 1 (.leaf (18561024 : ℤ))
    (.leaf (19740672 : ℤ)))
    (.node 1 (.leaf (7022592 : ℤ))
    (.leaf (17307648 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (55461888 : ℤ))
    (.node 1 (.leaf (59590656 : ℤ))
    (.leaf (21436416 : ℤ))))
    (.node 1 (.leaf (17934336 : ℤ))
    (.node 1 (.leaf (58116096 : ℤ))
    (.leaf (63313920 : ℤ)))))
    (.node 3 (.node 1 (.leaf (23132160 : ℤ))
    (.node 1 (.leaf (7653888 : ℤ))
    (.leaf (25099776 : ℤ))))
    (.node 1 (.leaf (27827712 : ℤ))
    (.node 1 (.leaf (10381824 : ℤ))
    (.leaf (1178496 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (3867264 : ℤ))
    (.node 1 (.leaf (4346496 : ℤ))
    (.leaf (1657728 : ℤ))))
    (.node 1 (.leaf (4319232 : ℤ))
    (.node 1 (.leaf (14180352 : ℤ))
    (.leaf (15980544 : ℤ)))))
    (.node 3 (.node 1 (.leaf (6119424 : ℤ))
    (.node 1 (.leaf (12232704 : ℤ))
    (.leaf (40074240 : ℤ))))
    (.node 2 (.node 1 (.leaf (45791232 : ℤ))
    (.leaf (17949696 : ℤ)))
    (.node 1 (.leaf (12275712 : ℤ))
    (.leaf (39418368 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (45566976 : ℤ))
    (.node 1 (.leaf (18424320 : ℤ))
    (.leaf (5451264 : ℤ))))
    (.node 1 (.leaf (16305408 : ℤ))
    (.node 1 (.leaf (18659328 : ℤ))
    (.leaf (7805184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1075584 : ℤ))
    (.node 1 (.leaf (2740608 : ℤ))
    (.leaf (2862720 : ℤ))))
    (.node 1 (.leaf (1197696 : ℤ))
    (.node 1 (.leaf (1490944 : ℤ))
    (.leaf (4853760 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (5695488 : ℤ))
    (.node 1 (.leaf (2340864 : ℤ))
    (.leaf (4227072 : ℤ))))
    (.node 1 (.leaf (13199360 : ℤ))
    (.node 1 (.leaf (15544320 : ℤ))
    (.leaf (6604800 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4507648 : ℤ))
    (.node 1 (.leaf (12737536 : ℤ))
    (.leaf (14663168 : ℤ))))
    (.node 2 (.node 1 (.leaf (6482432 : ℤ))
    (.leaf (2404352 : ℤ)))
    (.node 1 (.leaf (5625344 : ℤ))
    (.leaf (5822464 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (2634240 : ℤ))
    (.node 1 (.leaf (621056 : ℤ))
    (.leaf (1198080 : ℤ))))
    (.node 1 (.leaf (972800 : ℤ))
    (.node 1 (.leaf (403968 : ℤ))
    (.leaf (206848 : ℤ)))))
    (.node 3 (.node 1 (.leaf (663552 : ℤ))
    (.node 1 (.leaf (774144 : ℤ))
    (.leaf (331776 : ℤ))))
    (.node 1 (.leaf (591872 : ℤ))
    (.node 1 (.leaf (1805312 : ℤ))
    (.leaf (2064384 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (909312 : ℤ))
    (.node 1 (.leaf (645120 : ℤ))
    (.leaf (1796608 : ℤ))))
    (.node 1 (.leaf (1935872 : ℤ))
    (.node 1 (.leaf (873472 : ℤ))
    (.leaf (343552 : ℤ)))))
    (.node 3 (.node 1 (.leaf (843008 : ℤ))
    (.node 1 (.leaf (793600 : ℤ))
    (.leaf (354560 : ℤ))))
    (.node 2 (.node 1 (.leaf (79744 : ℤ))
    (.leaf (177024 : ℤ)))
    (.node 1 (.leaf (136832 : ℤ))
    (.leaf (54912 : ℤ)))))))))

private def leaf12S3Numer (i j k : ℕ) : ℤ :=
  leaf12S3Data.get ((i * 5 + j) * 4 + k)

private def leaf12S3 (i j k : ℕ) : ℚ :=
  (leaf12S3Numer i j k : ℚ) / 191102976

private theorem leaf12S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf12S3Numer k j h = ∑ i ∈ range 4, leaf12S2Numer k j i * leaf12W3Numer h i := by
  decide +kernel

private theorem leaf12S3Correct : Axis3Correct 4 4 3 leaf12W3 leaf12S2 leaf12S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf12S2Numer k j i) (leaf12W3Numer h) (leaf12S3Numer k j h) 2985984 64 3
    (leaf12S3NumerCorrect k hk j hj h hh)
  norm_num only [show (2985984 : ℚ)*64 = 191102976 by norm_num] at he
  exact he

private theorem leaf12NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf12S3Numer i j k := by
  decide +kernel

private theorem leaf12Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf12S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf12NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf12Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((3/4) : ℚ) ((1/8) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf12S1 leaf12S2 leaf12S3 4 4 3 (0 : ℚ) (1 : ℚ) ((3/4) : ℚ) ((1/8) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) leaf12W1 leaf12W2 leaf12W3
    leaf12W1Correct leaf12W2Correct leaf12W3Correct
    (axis1Correct_of_table commonInputCorrect leaf12S1Correct) leaf12S2Correct leaf12S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf12Signs i hi j hj k hk

theorem leaf12 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (3/4 : ℝ) ≤ d)
    (hd1 : d ≤ (7/8 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf12Certificate
  rwa [commonIdentity] at hb


private def leaf14W1Data : IntTable :=
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

private def leaf14W1Numer (k i : ℕ) : ℤ :=
  leaf14W1Data.get (k * 5 + i)

private def leaf14W1 (k i : ℕ) : ℚ :=
  (leaf14W1Numer k i : ℚ) / 1

private theorem leaf14W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf14W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf14W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf14W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf14W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf14W1, neg_div] using he

private def leaf14W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (65536 : ℤ))
    (.node 1 (.leaf (57344 : ℤ))
    (.leaf (50176 : ℤ))))
    (.node 1 (.leaf (43904 : ℤ))
    (.node 1 (.leaf (38416 : ℤ))
    (.leaf (262144 : ℤ)))))
    (.node 3 (.node 1 (.leaf (233472 : ℤ))
    (.node 1 (.leaf (207872 : ℤ))
    (.leaf (185024 : ℤ))))
    (.node 1 (.leaf (164640 : ℤ))
    (.node 1 (.leaf (393216 : ℤ))
    (.leaf (356352 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (322816 : ℤ))
    (.node 1 (.leaf (292320 : ℤ))
    (.leaf (264600 : ℤ))))
    (.node 1 (.leaf (262144 : ℤ))
    (.node 1 (.leaf (241664 : ℤ))
    (.leaf (222720 : ℤ)))))
    (.node 3 (.node 1 (.leaf (205200 : ℤ))
    (.node 1 (.leaf (189000 : ℤ))
    (.leaf (65536 : ℤ))))
    (.node 2 (.node 1 (.leaf (61440 : ℤ))
    (.leaf (57600 : ℤ)))
    (.node 1 (.leaf (54000 : ℤ))
    (.leaf (50625 : ℤ)))))))

private def leaf14W2Numer (k i : ℕ) : ℤ :=
  leaf14W2Data.get (k * 5 + i)

private def leaf14W2 (k i : ℕ) : ℚ :=
  (leaf14W2Numer k i : ℚ) / 65536

private theorem leaf14W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf14W2Numer k i = intTransWeight 4 (14) 1 16 k i := by
  decide +kernel

private theorem leaf14W2Correct : WeightsCorrect 4 ((7/8) : ℚ) ((1/16) : ℚ) leaf14W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (14) 1 16 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf14W2NumerCorrect k hk i hi] at he
  norm_num only [show (16 : ℚ)^4 = 65536 by norm_num,
    show (14 : ℚ)/16 = (7/8) by norm_num,
    show (1 : ℚ)/16 = (1/16) by norm_num] at he
  simpa only [leaf14W2, neg_div] using he

private def leaf14W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (64 : ℤ))
    (.leaf (36 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (128 : ℤ)))
    (.node 1 (.leaf (84 : ℤ))
    (.leaf (54 : ℤ))))
    (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (36 : ℤ))
    (.leaf (27 : ℤ))))))

private def leaf14W3Numer (k i : ℕ) : ℤ :=
  leaf14W3Data.get (k * 4 + i)

private def leaf14W3 (k i : ℕ) : ℚ :=
  (leaf14W3Numer k i : ℚ) / 64

private theorem leaf14W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf14W3Numer k i = intTransWeight 3 (2) 1 4 k i := by
  decide +kernel

private theorem leaf14W3Correct : WeightsCorrect 3 ((1/2) : ℚ) ((1/4) : ℚ) leaf14W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (2) 1 4 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf14W3NumerCorrect k hk i hi] at he
  norm_num only [show (4 : ℚ)^3 = 64 by norm_num,
    show (2 : ℚ)/4 = (1/2) by norm_num,
    show (1 : ℚ)/4 = (1/4) by norm_num] at he
  simpa only [leaf14W3, neg_div] using he

private def leaf14S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf14S1Numer (i j k : ℕ) : ℤ :=
  leaf14S1Data.get ((i * 5 + j) * 4 + k)

private def leaf14S1 (i j k : ℕ) : ℚ :=
  (leaf14S1Numer i j k : ℚ) / 729

private theorem leaf14S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf14S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf14W1Numer h i := by
  decide +kernel

private theorem leaf14S1Correct : Axis1Correct 4 4 3 leaf14W1 commonInput leaf14S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf14W1Numer h) (leaf14S1Numer h j k) 729 1 4
    (leaf14S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf14S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (217728 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (668736 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (738720 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (346032 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (58320 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (276192 : ℤ))))
    (.node 2 (.node 1 (.leaf (-258048 : ℤ))
    (.leaf (589824 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (940032 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (-1437696 : ℤ))
    (.node 1 (.leaf (2359296 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (1304496 : ℤ))
    (.node 1 (.leaf (-2792448 : ℤ))
    (.leaf (3538944 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (903456 : ℤ))
    (.leaf (-2304000 : ℤ))))
    (.node 1 (.leaf (2359296 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (262710 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-691200 : ℤ))
    (.node 1 (.leaf (589824 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (1120224 : ℤ))
    (.node 1 (.leaf (-2919168 : ℤ))
    (.leaf (2433024 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (4826688 : ℤ))
    (.leaf (-12686208 : ℤ))))
    (.node 2 (.node 1 (.leaf (9793536 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (7929744 : ℤ))
    (.leaf (-20588736 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (14782464 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (5868240 : ℤ))))
    (.node 1 (.leaf (-14794656 : ℤ))
    (.node 1 (.leaf (9916416 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1644750 : ℤ))
    (.node 1 (.leaf (-3972960 : ℤ))
    (.leaf (2494464 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (911232 : ℤ))
    (.leaf (-2326016 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1562624 : ℤ))
    (.node 1 (.leaf (131072 : ℤ))
    (.leaf (3910272 : ℤ))))
    (.node 1 (.leaf (-9789184 : ℤ))
    (.node 1 (.leaf (6199296 : ℤ))
    (.leaf (524288 : ℤ)))))
    (.node 3 (.node 1 (.leaf (6327680 : ℤ))
    (.node 1 (.leaf (-15410048 : ℤ))
    (.leaf (9217536 : ℤ))))
    (.node 2 (.node 1 (.leaf (786432 : ℤ))
    (.leaf (4570464 : ℤ)))
    (.node 1 (.leaf (-10754880 : ℤ))
    (.leaf (6087680 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (524288 : ℤ))
    (.node 1 (.leaf (1241640 : ℤ))
    (.leaf (-2808000 : ℤ))))
    (.node 1 (.leaf (1506816 : ℤ))
    (.node 1 (.leaf (131072 : ℤ))
    (.leaf (42336 : ℤ)))))
    (.node 3 (.node 1 (.leaf (34048 : ℤ))
    (.node 1 (.leaf (-280576 : ℤ))
    (.leaf (245760 : ℤ))))
    (.node 1 (.leaf (155456 : ℤ))
    (.node 1 (.leaf (212096 : ℤ))
    (.leaf (-1234944 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (991232 : ℤ))
    (.node 1 (.leaf (210640 : ℤ))
    (.leaf (449344 : ℤ))))
    (.node 1 (.leaf (-2025984 : ℤ))
    (.node 1 (.leaf (1499136 : ℤ))
    (.leaf (123408 : ℤ)))))
    (.node 3 (.node 1 (.leaf (399456 : ℤ))
    (.node 1 (.leaf (-1469440 : ℤ))
    (.leaf (1007616 : ℤ))))
    (.node 2 (.node 1 (.leaf (25830 : ℤ))
    (.leaf (128160 : ℤ)))
    (.node 1 (.leaf (-397824 : ℤ))
    (.leaf (253952 : ℤ)))))))))

private def leaf14S2Numer (i j k : ℕ) : ℤ :=
  leaf14S2Data.get ((i * 5 + j) * 4 + k)

private def leaf14S2 (i j k : ℕ) : ℚ :=
  (leaf14S2Numer i j k : ℚ) / 47775744

private theorem leaf14S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf14S2Numer k j h = ∑ i ∈ range 5, leaf14S1Numer k i h * leaf14W2Numer j i := by
  decide +kernel

private theorem leaf14S2Correct : Axis2Correct 4 4 3 leaf14W2 leaf14S1 leaf14S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf14S1Numer k i h) (leaf14W2Numer j) (leaf14S2Numer k j h) 729 65536 4
    (leaf14S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*65536 = 47775744 by norm_num] at he
  exact he

private def leaf14S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (13934592 : ℤ))
    (.node 1 (.leaf (41803776 : ℤ))
    (.leaf (41803776 : ℤ))))
    (.node 1 (.leaf (13934592 : ℤ))
    (.node 1 (.leaf (42799104 : ℤ))
    (.leaf (128397312 : ℤ)))))
    (.node 3 (.node 1 (.leaf (128397312 : ℤ))
    (.node 1 (.leaf (42799104 : ℤ))
    (.leaf (47278080 : ℤ))))
    (.node 1 (.leaf (141834240 : ℤ))
    (.node 1 (.leaf (141834240 : ℤ))
    (.leaf (47278080 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (22146048 : ℤ))
    (.node 1 (.leaf (66438144 : ℤ))
    (.leaf (66438144 : ℤ))))
    (.node 1 (.leaf (22146048 : ℤ))
    (.node 1 (.leaf (3732480 : ℤ))
    (.leaf (11197440 : ℤ)))))
    (.node 3 (.node 1 (.leaf (11197440 : ℤ))
    (.node 1 (.leaf (3732480 : ℤ))
    (.leaf (18855936 : ℤ))))
    (.node 2 (.node 1 (.leaf (61876224 : ℤ))
    (.leaf (69543936 : ℤ)))
    (.node 1 (.leaf (26523648 : ℤ))
    (.leaf (51904512 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (170459136 : ℤ))
    (.node 1 (.leaf (194641920 : ℤ))
    (.leaf (76087296 : ℤ))))
    (.node 1 (.leaf (50752512 : ℤ))
    (.node 1 (.leaf (164201472 : ℤ))
    (.leaf (190301184 : ℤ)))))
    (.node 3 (.node 1 (.leaf (76852224 : ℤ))
    (.node 1 (.leaf (21841920 : ℤ))
    (.leaf (66410496 : ℤ))))
    (.node 1 (.leaf (76732416 : ℤ))
    (.node 1 (.leaf (32163840 : ℤ))
    (.leaf (4132224 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (10774656 : ℤ))
    (.node 1 (.leaf (11511936 : ℤ))
    (.leaf (4869504 : ℤ))))
    (.node 1 (.leaf (17209344 : ℤ))
    (.node 1 (.leaf (43849728 : ℤ))
    (.leaf (45803520 : ℤ)))))
    (.node 3 (.node 1 (.leaf (19163136 : ℤ))
    (.node 1 (.leaf (59645952 : ℤ))
    (.leaf (132655104 : ℤ))))
    (.node 2 (.node 1 (.leaf (125546496 : ℤ))
    (.leaf (52537344 : ℤ)))
    (.node 1 (.leaf (85183488 : ℤ))
    (.leaf (162650112 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (128879616 : ℤ))
    (.node 1 (.leaf (51412992 : ℤ))
    (.leaf (60801024 : ℤ))))
    (.node 1 (.leaf (104351232 : ℤ))
    (.node 1 (.leaf (65965056 : ℤ))
    (.leaf (22414848 : ℤ)))))
    (.node 3 (.node 1 (.leaf (18040704 : ℤ))
    (.node 1 (.leaf (30466176 : ℤ))
    (.leaf (16788096 : ℤ))))
    (.node 1 (.leaf (4362624 : ℤ))
    (.node 1 (.leaf (9936896 : ℤ))
    (.leaf (19169280 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (15564800 : ℤ))
    (.node 1 (.leaf (6463488 : ℤ))
    (.leaf (40386560 : ℤ))))
    (.node 1 (.leaf (70012928 : ℤ))
    (.node 1 (.leaf (46809088 : ℤ))
    (.leaf (17707008 : ℤ)))))
    (.node 3 (.node 1 (.leaf (65622016 : ℤ))
    (.node 1 (.leaf (107223040 : ℤ))
    (.leaf (59168768 : ℤ))))
    (.node 2 (.node 1 (.leaf (18354176 : ℤ))
    (.leaf (49950720 : ℤ)))
    (.node 1 (.leaf (81468416 : ℤ))
    (.leaf (40581120 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (9587712 : ℤ))
    (.node 1 (.leaf (14766592 : ℤ))
    (.leaf (25053696 : ℤ))))
    (.node 1 (.leaf (12621312 : ℤ))
    (.node 1 (.leaf (2465280 : ℤ))
    (.leaf (1275904 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2832384 : ℤ))
    (.node 1 (.leaf (2189312 : ℤ))
    (.leaf (878592 : ℤ))))
    (.node 1 (.leaf (4907008 : ℤ))
    (.node 1 (.leaf (10250240 : ℤ))
    (.leaf (6787072 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2435072 : ℤ))
    (.node 1 (.leaf (7437312 : ℤ))
    (.leaf (15075328 : ℤ))))
    (.node 1 (.leaf (8729600 : ℤ))
    (.node 1 (.leaf (2590720 : ℤ))
    (.leaf (5230592 : ℤ)))))
    (.node 3 (.node 1 (.leaf (10663424 : ℤ))
    (.node 1 (.leaf (5803008 : ℤ))
    (.leaf (1377792 : ℤ))))
    (.node 2 (.node 1 (.leaf (1420672 : ℤ))
    (.leaf (2994816 : ℤ)))
    (.node 1 (.leaf (1660032 : ℤ))
    (.leaf (339840 : ℤ)))))))))

private def leaf14S3Numer (i j k : ℕ) : ℤ :=
  leaf14S3Data.get ((i * 5 + j) * 4 + k)

private def leaf14S3 (i j k : ℕ) : ℚ :=
  (leaf14S3Numer i j k : ℚ) / 3057647616

private theorem leaf14S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf14S3Numer k j h = ∑ i ∈ range 4, leaf14S2Numer k j i * leaf14W3Numer h i := by
  decide +kernel

private theorem leaf14S3Correct : Axis3Correct 4 4 3 leaf14W3 leaf14S2 leaf14S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf14S2Numer k j i) (leaf14W3Numer h) (leaf14S3Numer k j h) 47775744 64 3
    (leaf14S3NumerCorrect k hk j hj h hh)
  norm_num only [show (47775744 : ℚ)*64 = 3057647616 by norm_num] at he
  exact he

private theorem leaf14NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf14S3Numer i j k := by
  decide +kernel

private theorem leaf14Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf14S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf14NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf14Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((7/8) : ℚ) ((1/16) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf14S1 leaf14S2 leaf14S3 4 4 3 (0 : ℚ) (1 : ℚ) ((7/8) : ℚ) ((1/16) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) leaf14W1 leaf14W2 leaf14W3
    leaf14W1Correct leaf14W2Correct leaf14W3Correct
    (axis1Correct_of_table commonInputCorrect leaf14S1Correct) leaf14S2Correct leaf14S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf14Signs i hi j hj k hk

theorem leaf14 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (7/8 : ℝ) ≤ d)
    (hd1 : d ≤ (15/16 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf14Certificate
  rwa [commonIdentity] at hb


private def leaf15W1Data : IntTable :=
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

private def leaf15W1Numer (k i : ℕ) : ℤ :=
  leaf15W1Data.get (k * 5 + i)

private def leaf15W1 (k i : ℕ) : ℚ :=
  (leaf15W1Numer k i : ℚ) / 1

private theorem leaf15W1NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf15W1Numer k i = intTransWeight 4 (0) 1 1 k i := by
  decide +kernel

private theorem leaf15W1Correct : WeightsCorrect 4 (0 : ℚ) (1 : ℚ) leaf15W1 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (0) 1 1 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf15W1NumerCorrect k hk i hi] at he
  norm_num only [show (1 : ℚ)^4 = 1 by norm_num,
    show (0 : ℚ)/1 = 0 by norm_num,
    show (1 : ℚ)/1 = 1 by norm_num] at he
  simpa only [leaf15W1, neg_div] using he

private def leaf15W2Data : IntTable :=
  (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (65536 : ℤ))
    (.node 1 (.leaf (61440 : ℤ))
    (.leaf (57600 : ℤ))))
    (.node 1 (.leaf (54000 : ℤ))
    (.node 1 (.leaf (50625 : ℤ))
    (.leaf (262144 : ℤ)))))
    (.node 3 (.node 1 (.leaf (249856 : ℤ))
    (.node 1 (.leaf (238080 : ℤ))
    (.leaf (226800 : ℤ))))
    (.node 1 (.leaf (216000 : ℤ))
    (.node 1 (.leaf (393216 : ℤ))
    (.leaf (380928 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (368896 : ℤ))
    (.node 1 (.leaf (357120 : ℤ))
    (.leaf (345600 : ℤ))))
    (.node 1 (.leaf (262144 : ℤ))
    (.node 1 (.leaf (258048 : ℤ))
    (.leaf (253952 : ℤ)))))
    (.node 3 (.node 1 (.leaf (249856 : ℤ))
    (.node 1 (.leaf (245760 : ℤ))
    (.leaf (65536 : ℤ))))
    (.node 2 (.node 1 (.leaf (65536 : ℤ))
    (.leaf (65536 : ℤ)))
    (.node 1 (.leaf (65536 : ℤ))
    (.leaf (65536 : ℤ)))))))

private def leaf15W2Numer (k i : ℕ) : ℤ :=
  leaf15W2Data.get (k * 5 + i)

private def leaf15W2 (k i : ℕ) : ℚ :=
  (leaf15W2Numer k i : ℚ) / 65536

private theorem leaf15W2NumerCorrect :
    ∀ k ∈ range 5, ∀ i ∈ range 5,
      leaf15W2Numer k i = intTransWeight 4 (15) 1 16 k i := by
  decide +kernel

private theorem leaf15W2Correct : WeightsCorrect 4 ((15/16) : ℚ) ((1/16) : ℚ) leaf15W2 := by
  intro k hk i hi
  have he := intTransWeight_cast 4 (15) 1 16 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf15W2NumerCorrect k hk i hi] at he
  norm_num only [show (16 : ℚ)^4 = 65536 by norm_num,
    show (15 : ℚ)/16 = (15/16) by norm_num,
    show (1 : ℚ)/16 = (1/16) by norm_num] at he
  simpa only [leaf15W2, neg_div] using he

private def leaf15W3Data : IntTable :=
  (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (32 : ℤ)))
    (.node 1 (.leaf (16 : ℤ))
    (.leaf (8 : ℤ))))
    (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (112 : ℤ)))
    (.node 1 (.leaf (64 : ℤ))
    (.leaf (36 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (192 : ℤ))
    (.leaf (128 : ℤ)))
    (.node 1 (.leaf (84 : ℤ))
    (.leaf (54 : ℤ))))
    (.node 2 (.node 1 (.leaf (64 : ℤ))
    (.leaf (48 : ℤ)))
    (.node 1 (.leaf (36 : ℤ))
    (.leaf (27 : ℤ))))))

private def leaf15W3Numer (k i : ℕ) : ℤ :=
  leaf15W3Data.get (k * 4 + i)

private def leaf15W3 (k i : ℕ) : ℚ :=
  (leaf15W3Numer k i : ℚ) / 64

private theorem leaf15W3NumerCorrect :
    ∀ k ∈ range 4, ∀ i ∈ range 4,
      leaf15W3Numer k i = intTransWeight 3 (2) 1 4 k i := by
  decide +kernel

private theorem leaf15W3Correct : WeightsCorrect 3 ((1/2) : ℚ) ((1/4) : ℚ) leaf15W3 := by
  intro k hk i hi
  have he := intTransWeight_cast 3 (2) 1 4 k i
    (by simp only [mem_range] at hi; omega) (by norm_num)
  rw [← leaf15W3NumerCorrect k hk i hi] at he
  norm_num only [show (4 : ℚ)^3 = 64 by norm_num,
    show (2 : ℚ)/4 = (1/2) by norm_num,
    show (1 : ℚ)/4 = (1/4) by norm_num] at he
  simpa only [leaf15W3, neg_div] using he

private def leaf15S1Data : IntTable :=
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
    (.leaf (639 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (90 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-1467 : ℤ))
    (.node 1 (.leaf (-108 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (927 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-90 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (24 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (615 : ℤ))
    (.leaf (186 : ℤ))))
    (.node 2 (.node 1 (.leaf (15 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1596 : ℤ))
    (.leaf (-318 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1230 : ℤ))))
    (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-210 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (21 : ℤ))
    (.node 1 (.leaf (2 : ℤ))
    (.leaf (261 : ℤ))))
    (.node 1 (.leaf (120 : ℤ))
    (.node 1 (.leaf (19 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-757 : ℤ))
    (.node 1 (.leaf (-278 : ℤ))
    (.leaf (-18 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (706 : ℤ)))
    (.node 1 (.leaf (108 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-184 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (6 : ℤ))
    (.leaf (2 : ℤ))))
    (.node 1 (.leaf (42 : ℤ))
    (.node 1 (.leaf (24 : ℤ))
    (.leaf (4 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (2 : ℤ))
    (.node 1 (.leaf (-134 : ℤ))
    (.leaf (-74 : ℤ))))
    (.node 1 (.leaf (-18 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (150 : ℤ)))))
    (.node 3 (.node 1 (.leaf (54 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-58 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))

private def leaf15S1Numer (i j k : ℕ) : ℤ :=
  leaf15S1Data.get ((i * 5 + j) * 4 + k)

private def leaf15S1 (i j k : ℕ) : ℚ :=
  (leaf15S1Numer i j k : ℚ) / 729

private theorem leaf15S1NumerCorrect :
    ∀ h ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      leaf15S1Numer h j k = ∑ i ∈ range 5, commonInputNumer i j k * leaf15W1Numer h i := by
  decide +kernel

private theorem leaf15S1Correct : Axis1Correct 4 4 3 leaf15W1 commonInput leaf15S1 := by
  intro h hh j hj k hk
  have he := scaled_dot_eq (fun i => commonInputNumer i j k) (leaf15W1Numer h) (leaf15S1Numer h j k) 729 1 4
    (leaf15S1NumerCorrect h hh j hj k hk)
  norm_num only [show (729 : ℚ)*1 = 729 by norm_num] at he
  exact he

private def leaf15S2Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (58320 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (120528 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (62208 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (262710 : ℤ))))
    (.node 2 (.node 1 (.leaf (-691200 : ℤ))
    (.leaf (589824 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1198224 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (-3225600 : ℤ))
    (.node 1 (.leaf (2359296 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (2188800 : ℤ))
    (.node 1 (.leaf (-5557248 : ℤ))
    (.leaf (3538944 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1843200 : ℤ))
    (.leaf (-4202496 : ℤ))))
    (.node 1 (.leaf (2359296 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (589824 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-1179648 : ℤ))
    (.node 1 (.leaf (589824 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (1644750 : ℤ))
    (.node 1 (.leaf (-3972960 : ℤ))
    (.leaf (2494464 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (7289760 : ℤ))
    (.leaf (-16989024 : ℤ))))
    (.node 2 (.node 1 (.leaf (10039296 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (12194304 : ℤ))
    (.leaf (-27171840 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (15151104 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (9105408 : ℤ))))
    (.node 1 (.leaf (-19267584 : ℤ))
    (.node 1 (.leaf (10162176 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2555904 : ℤ))
    (.node 1 (.leaf (-5111808 : ℤ))
    (.leaf (2555904 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (1241640 : ℤ))
    (.leaf (-2808000 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1506816 : ℤ))
    (.node 1 (.leaf (131072 : ℤ))
    (.leaf (5362656 : ℤ))))
    (.node 1 (.leaf (-11709120 : ℤ))
    (.node 1 (.leaf (5966848 : ℤ))
    (.leaf (524288 : ℤ)))))
    (.node 3 (.node 1 (.leaf (8704256 : ℤ))
    (.node 1 (.leaf (-18272768 : ℤ))
    (.leaf (8855040 : ℤ))))
    (.node 2 (.node 1 (.leaf (786432 : ℤ))
    (.leaf (6287360 : ℤ)))
    (.node 1 (.leaf (-12648448 : ℤ))
    (.leaf (5836800 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (524288 : ℤ))
    (.node 1 (.leaf (1703936 : ℤ))
    (.leaf (-3276800 : ℤ))))
    (.node 1 (.leaf (1441792 : ℤ))
    (.node 1 (.leaf (131072 : ℤ))
    (.leaf (25830 : ℤ)))))
    (.node 3 (.node 1 (.leaf (128160 : ℤ))
    (.node 1 (.leaf (-397824 : ℤ))
    (.leaf (253952 : ℤ))))
    (.node 1 (.leaf (83232 : ℤ))
    (.node 1 (.leaf (625824 : ℤ))
    (.leaf (-1713152 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1024000 : ℤ))
    (.node 1 (.leaf (90112 : ℤ))
    (.leaf (1128448 : ℤ))))
    (.node 1 (.leaf (-2757120 : ℤ))
    (.node 1 (.leaf (1548288 : ℤ))
    (.leaf (32768 : ℤ)))))
    (.node 3 (.node 1 (.leaf (892928 : ℤ))
    (.node 1 (.leaf (-1966080 : ℤ))
    (.leaf (1040384 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (262144 : ℤ)))
    (.node 1 (.leaf (-524288 : ℤ))
    (.leaf (262144 : ℤ)))))))))

private def leaf15S2Numer (i j k : ℕ) : ℤ :=
  leaf15S2Data.get ((i * 5 + j) * 4 + k)

private def leaf15S2 (i j k : ℕ) : ℚ :=
  (leaf15S2Numer i j k : ℚ) / 47775744

private theorem leaf15S2NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf15S2Numer k j h = ∑ i ∈ range 5, leaf15S1Numer k i h * leaf15W2Numer j i := by
  decide +kernel

private theorem leaf15S2Correct : Axis2Correct 4 4 3 leaf15W2 leaf15S1 leaf15S2 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf15S1Numer k i h) (leaf15W2Numer j) (leaf15S2Numer k j h) 729 65536 4
    (leaf15S2NumerCorrect k hk j hj h hh)
  norm_num only [show (729 : ℚ)*65536 = 47775744 by norm_num] at he
  exact he

private def leaf15S3Data : IntTable :=
  (.node 50 (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (3732480 : ℤ))
    (.node 1 (.leaf (11197440 : ℤ))
    (.leaf (11197440 : ℤ))))
    (.node 1 (.leaf (3732480 : ℤ))
    (.node 1 (.leaf (7713792 : ℤ))
    (.leaf (23141376 : ℤ)))))
    (.node 3 (.node 1 (.leaf (23141376 : ℤ))
    (.node 1 (.leaf (7713792 : ℤ))
    (.leaf (3981312 : ℤ))))
    (.node 1 (.leaf (11943936 : ℤ))
    (.node 1 (.leaf (11943936 : ℤ))
    (.leaf (3981312 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4132224 : ℤ))))
    (.node 2 (.node 1 (.leaf (10774656 : ℤ))
    (.leaf (11511936 : ℤ)))
    (.node 1 (.leaf (4869504 : ℤ))
    (.leaf (11215872 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (19786752 : ℤ))
    (.node 1 (.leaf (15363072 : ℤ))
    (.leaf (6792192 : ℤ))))
    (.node 1 (.leaf (18874368 : ℤ))
    (.node 1 (.leaf (24330240 : ℤ))
    (.leaf (6193152 : ℤ)))))
    (.node 3 (.node 1 (.leaf (737280 : ℤ))
    (.node 1 (.leaf (21233664 : ℤ))
    (.leaf (34209792 : ℤ))))
    (.node 1 (.leaf (14155776 : ℤ))
    (.node 1 (.leaf (1179648 : ℤ))
    (.leaf (9437184 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (18874368 : ℤ))
    (.node 1 (.leaf (11796480 : ℤ))
    (.leaf (2359296 : ℤ))))
    (.node 1 (.leaf (18040704 : ℤ))
    (.node 1 (.leaf (30466176 : ℤ))
    (.leaf (16788096 : ℤ)))))
    (.node 3 (.node 1 (.leaf (4362624 : ℤ))
    (.node 1 (.leaf (83524608 : ℤ))
    (.leaf (139378176 : ℤ))))
    (.node 2 (.node 1 (.leaf (68339712 : ℤ))
    (.leaf (12486144 : ℤ)))
    (.node 1 (.leaf (153354240 : ℤ))
    (.leaf (267730944 : ℤ))))))))
    (.node 25 (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (136003584 : ℤ))
    (.node 1 (.leaf (21626880 : ℤ))
    (.leaf (128778240 : ℤ))))
    (.node 1 (.leaf (240648192 : ℤ))
    (.node 1 (.leaf (135610368 : ℤ))
    (.leaf (23740416 : ℤ)))))
    (.node 3 (.node 1 (.leaf (40894464 : ℤ))
    (.node 1 (.leaf (81788928 : ℤ))
    (.leaf (51118080 : ℤ))))
    (.node 1 (.leaf (10223616 : ℤ))
    (.node 1 (.leaf (14766592 : ℤ))
    (.leaf (25053696 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (12621312 : ℤ))
    (.node 1 (.leaf (2465280 : ℤ))
    (.leaf (68182016 : ℤ))))
    (.node 1 (.leaf (118961152 : ℤ))
    (.node 1 (.leaf (60389376 : ℤ))
    (.leaf (10134528 : ℤ)))))
    (.node 3 (.node 1 (.leaf (120315904 : ℤ))
    (.node 1 (.leaf (219701248 : ℤ))
    (.leaf (118593536 : ℤ))))
    (.node 2 (.node 1 (.leaf (19994624 : ℤ))
    (.leaf (95223808 : ℤ)))
    (.node 1 (.leaf (182976512 : ℤ))
    (.leaf (106774528 : ℤ)))))))
    (.node 12 (.node 6 (.node 3 (.node 1 (.leaf (19546112 : ℤ))
    (.node 1 (.leaf (28311552 : ℤ))
    (.leaf (57147392 : ℤ))))
    (.node 1 (.leaf (35913728 : ℤ))
    (.node 1 (.leaf (7208960 : ℤ))
    (.leaf (1420672 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2994816 : ℤ))
    (.node 1 (.leaf (1660032 : ℤ))
    (.leaf (339840 : ℤ))))
    (.node 1 (.leaf (6134784 : ℤ))
    (.node 1 (.leaf (13295104 : ℤ))
    (.leaf (7477248 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (1340928 : ℤ))
    (.node 1 (.leaf (10149888 : ℤ))
    (.leaf (22970368 : ℤ))))
    (.node 1 (.leaf (13752320 : ℤ))
    (.node 1 (.leaf (2480128 : ℤ))
    (.leaf (7536640 : ℤ)))))
    (.node 3 (.node 1 (.leaf (17924096 : ℤ))
    (.node 1 (.leaf (11616256 : ℤ))
    (.leaf (2269184 : ℤ))))
    (.node 2 (.node 1 (.leaf (2097152 : ℤ))
    (.leaf (5242880 : ℤ)))
    (.node 1 (.leaf (3670016 : ℤ))
    (.leaf (786432 : ℤ)))))))))

private def leaf15S3Numer (i j k : ℕ) : ℤ :=
  leaf15S3Data.get ((i * 5 + j) * 4 + k)

private def leaf15S3 (i j k : ℕ) : ℚ :=
  (leaf15S3Numer i j k : ℚ) / 3057647616

private theorem leaf15S3NumerCorrect :
    ∀ k ∈ range 5, ∀ j ∈ range 5, ∀ h ∈ range 4,
      leaf15S3Numer k j h = ∑ i ∈ range 4, leaf15S2Numer k j i * leaf15W3Numer h i := by
  decide +kernel

private theorem leaf15S3Correct : Axis3Correct 4 4 3 leaf15W3 leaf15S2 leaf15S3 := by
  intro k hk j hj h hh
  have he := scaled_dot_eq (fun i => leaf15S2Numer k j i) (leaf15W3Numer h) (leaf15S3Numer k j h) 47775744 64 3
    (leaf15S3NumerCorrect k hk j hj h hh)
  norm_num only [show (47775744 : ℚ)*64 = 3057647616 by norm_num] at he
  exact he

private theorem leaf15NumerSigns :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf15S3Numer i j k := by
  decide +kernel

private theorem leaf15Signs :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ leaf15S3 i j k := by
  intro i hi j hj k hk
  apply div_nonneg
  · exact_mod_cast leaf15NumerSigns i hi j hj k hk
  · norm_num


private theorem leaf15Certificate :
    ∀ i ∈ range 5, ∀ j ∈ range 5, ∀ k ∈ range 4,
      0 ≤ trans3 commonCoeff 4 4 3 (0 : ℚ) (1 : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) i j k := by
  have exactTable := checked_trans3 commonCoeff leaf15S1 leaf15S2 leaf15S3 4 4 3 (0 : ℚ) (1 : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) ((1/2) : ℚ) ((1/4) : ℚ) leaf15W1 leaf15W2 leaf15W3
    leaf15W1Correct leaf15W2Correct leaf15W3Correct
    (axis1Correct_of_table commonInputCorrect leaf15S1Correct) leaf15S2Correct leaf15S3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact leaf15Signs i hi j hj k hk

theorem leaf15 {x d u : ℝ}
    (hx0 : (0 : ℝ) ≤ x)
    (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d)
    (hd1 : d ≤ (1 : ℝ))
    (hu0 : (1/2 : ℝ) ≤ u)
    (hu1 : u ≤ (3/4 : ℝ)) : 0 ≤ highLLTarget x d u := by
  have hb := msum_nonneg_on_box commonCoeff 4 4 3 (x := x) (y := d) (z := u)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) leaf15Certificate
  rwa [commonIdentity] at hb


end Taeyoung.Methods.Atlas126.HighLLData
