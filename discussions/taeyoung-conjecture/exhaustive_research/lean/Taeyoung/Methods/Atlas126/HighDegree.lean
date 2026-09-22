import Taeyoung.Methods.Atlas126.Convex
import Taeyoung.Methods.Atlas126.Signs
import Taeyoung.Methods.Bernstein.CheckedTensor

/-! Generated exact high-degree certificates for the three low-density planes.
Regenerate with `codes/generate_atlas126_high_degree_lean.py`. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option cbv.warning false
open Finset
namespace Taeyoung.Methods.Atlas126
open Taeyoung.Methods.Bernstein

noncomputable def degreeRemainder (p C beta gamma lam g d : ℝ) : ℝ :=
  (p - 2 + 2*d)^3 - d*(C + beta*(d-p) + gamma*(p-d^2) + lam*(p-g))


private def degreeACoeffTerms : List IntTerm := [
  ⟨0, 0, 0, (-437400 : ℤ)⟩,
  ⟨0, 1, 0, (1745550 : ℤ)⟩,
  ⟨0, 2, 0, (-2340900 : ℤ)⟩,
  ⟨0, 3, 0, (1044900 : ℤ)⟩,
  ⟨1, 0, 0, (291600 : ℤ)⟩,
  ⟨1, 1, 0, (-779571 : ℤ)⟩,
  ⟨1, 2, 0, (468450 : ℤ)⟩,
  ⟨1, 3, 0, (43200 : ℤ)⟩,
  ⟨2, 0, 0, (-210600 : ℤ)⟩,
  ⟨2, 1, 0, (490032 : ℤ)⟩,
  ⟨2, 2, 0, (-331200 : ℤ)⟩,
  ⟨2, 3, 0, (36000 : ℤ)⟩,
  ⟨3, 0, 0, (69600 : ℤ)⟩,
  ⟨3, 1, 0, (-62907 : ℤ)⟩,
  ⟨3, 2, 0, (27600 : ℤ)⟩,
  ⟨3, 3, 0, (-57600 : ℤ)⟩,
  ⟨4, 0, 0, (-23400 : ℤ)⟩,
  ⟨4, 1, 0, (4744 : ℤ)⟩,
  ⟨4, 2, 0, (33600 : ℤ)⟩,
  ⟨4, 3, 0, (14400 : ℤ)⟩,
  ⟨5, 0, 0, (3600 : ℤ)⟩,
  ⟨5, 1, 0, (-6200 : ℤ)⟩,
  ⟨5, 2, 0, (-12000 : ℤ)⟩,
  ⟨6, 0, 0, (-600 : ℤ)⟩,
  ⟨6, 1, 0, (6800 : ℤ)⟩,
  ⟨7, 1, 0, (-5200 : ℤ)⟩,
  ⟨8, 1, 0, (3400 : ℤ)⟩,
  ⟨9, 1, 0, (-1000 : ℤ)⟩,
  ⟨10, 1, 0, (100 : ℤ)⟩]

private def degreeACoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff degreeACoeffTerms i j k

private def degreeACoeff (i j k : ℕ) : ℚ :=
  (degreeACoeffNumer i j k : ℚ) / 129600

private theorem degreeACoeffExpansion (x d u : ℝ) :
    msum degreeACoeff 10 3 0 x d u = sparseEval (degreeACoeffTerms.map IntTerm.toRat) x d u / 129600 := by
  have he : ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      degreeACoeffNumer i j k = intSparseCoeff degreeACoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ degreeACoeffTerms, t.i ≤ 10 ∧ t.j ≤ 3 ∧ t.k ≤ 0 := by decide +kernel
  exact msum_intSparse_scaled degreeACoeffNumer degreeACoeffTerms 129600 10 3 0 he hb x d u

private theorem degreeAIdentity (x d u : ℝ) :
    msum degreeACoeff 10 3 0 x d u = degreeRemainder (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d := by
  simp only [degreeACoeffExpansion, sparseEval, IntTerm.toRat, degreeACoeffTerms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, degreeRemainder, target,
    lowDensity, lowTriangle, betaA, gammaA, lambdaA,
    gammaLow, contactA, betaHigh, gammaHigh]
  push_cast
  ring


private def degreeAW1Data : Array ℚ := #[
    1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 10, (5/8), 0, 0, 0,
    0, 0, 0, 0, 0, 0, 45, (45/8),
    (25/64), 0, 0, 0, 0, 0, 0, 0,
    0, 120, (45/2), (25/8), (125/512), 0, 0, 0,
    0, 0, 0, 0, 210, (105/2), (175/16), (875/512),
    (625/4096), 0, 0, 0, 0, 0, 0, 252,
    (315/4), (175/8), (2625/512), (1875/2048), (3125/32768), 0, 0, 0,
    0, 0, 210, (315/4), (875/32), (4375/512), (9375/4096), (15625/32768),
    (15625/262144), 0, 0, 0, 0, 120, (105/2), (175/8),
    (4375/512), (3125/1024), (15625/16384), (15625/65536), (78125/2097152), 0, 0, 0,
    45, (45/2), (175/16), (2625/512), (9375/4096), (15625/16384), (46875/131072), (234375/2097152),
    (390625/16777216), 0, 0, 10, (45/8), (25/8), (875/512), (1875/2048),
    (15625/32768), (15625/65536), (234375/2097152), (390625/8388608), (1953125/134217728), 0, 1, (5/8),
    (25/64), (125/512), (625/4096), (3125/32768), (15625/262144), (78125/2097152), (390625/16777216), (1953125/134217728),
    (9765625/1073741824)
  ]

private def degreeAW1 (k i : ℕ) : ℚ :=
  (degreeAW1Data[k * 11 + i]?).getD 0

private theorem degreeAW1Correct : WeightsCorrect 10 (0 : ℚ) ((5/8) : ℚ) degreeAW1 := by
  decide +kernel

private def degreeAW2Data : Array ℚ := #[
    1, (15/16), (225/256), (3375/4096), 3, (23/8), (705/256), (675/256),
    3, (47/16), (23/8), (45/16), 1, 1, 1, 1
  ]

private def degreeAW2 (k i : ℕ) : ℚ :=
  (degreeAW2Data[k * 4 + i]?).getD 0

private theorem degreeAW2Correct : WeightsCorrect 3 ((15/16) : ℚ) ((1/16) : ℚ) degreeAW2 := by
  decide +kernel

private def degreeAW3Data : Array ℚ := #[
    1
  ]

private def degreeAW3 (k i : ℕ) : ℚ :=
  (degreeAW3Data[k * 1 + i]?).getD 0

private theorem degreeAW3Correct : WeightsCorrect 0 (0 : ℚ) (1 : ℚ) degreeAW3 := by
  decide +kernel

private def degreeAS1Data : Array ℚ := #[
    (-27/8), (431/32), (-289/16), (129/16), (-1035/32), (1005527/7680), (-136985/768), (485/6),
    (-71605/512), (13218859/23040), (-1828175/2304), (420245/1152), (-9934535/27648), (6602808127/4423680), (-115795685/55296), (1124075/1152),
    (-537484375/884736), (4235404343/1658880), (-133849765/36864), (63145105/36864), (-833148419/1179648), (318577102433/106168320), (-7647098761/1769472), (38004931/18432),
    (-10792504115/18874368), (1042167784817/424673280), (-6327607165/1769472), (63532415/36864), (-1502204155/4718592), (4685310968179/3397386240), (-1797000125/884736), (9101885/9216),
    (-1100927705/9437184), (27704838175301/54358179840), (-670487285/884736), (13688575/36864), (-359659325/14155776), (48643278874867/434865438720), (-98926415/589824), (1524515/18432),
    (-141420761/56623104), (77029617619853/6957847019520), (-29583673/1769472), (305521/36864)
  ]

private def degreeAS1 (i j k : ℕ) : ℚ :=
  (degreeAS1Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeAS1Correct : Axis1Correct 10 3 0 degreeAW1 degreeACoeff degreeAS1 := by
  decide +kernel

private def degreeAS2Data : Array ℚ := #[
    (1311/65536), (233/2048), (95/512), (3/32), (15661/65536), (1296211/983040), (259469/122880), (8077/7680),
    (1907041/1572864), (19542587/2949120), (1293191/122880), (4991/960), (49172711/14155776), (1352305417/70778880), (2146792369/70778880), (66075727/4423680),
    (946079311/150994944), (7464433099/212336640), (745117223/13271040), (367291519/13271040), (3382048361/452984832), (294105701777/6794772480), (118808179111/1698693120), (3676221623/106168320),
    (2701775807/452984832), (246121577507/6794772480), (404402276599/6794772480), (25208286859/849346560), (11428467139/3623878656), (554111654717/27179089920), (1860687715613/54358179840), (58562382979/3397386240),
    (61063939781/57982058496), (3216879916723/434865438720), (11093049842347/869730877440), (353380956101/54358179840), (30789035089/154618822656), (5440475817941/3478923509760), (19369322939549/6957847019520), (625898574067/434865438720),
    (118331134861/7421703487488), (8143408669099/55662776156160), (30114703660771/111325552312320), (989256741773/6957847019520)
  ]

private def degreeAS2 (i j k : ℕ) : ℚ :=
  (degreeAS2Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeAS2Correct : Axis2Correct 10 3 0 degreeAW2 degreeAS1 degreeAS2 := by
  decide +kernel

private def degreeAS3Data : Array ℚ := #[
    (1311/65536), (233/2048), (95/512), (3/32), (15661/65536), (1296211/983040), (259469/122880), (8077/7680),
    (1907041/1572864), (19542587/2949120), (1293191/122880), (4991/960), (49172711/14155776), (1352305417/70778880), (2146792369/70778880), (66075727/4423680),
    (946079311/150994944), (7464433099/212336640), (745117223/13271040), (367291519/13271040), (3382048361/452984832), (294105701777/6794772480), (118808179111/1698693120), (3676221623/106168320),
    (2701775807/452984832), (246121577507/6794772480), (404402276599/6794772480), (25208286859/849346560), (11428467139/3623878656), (554111654717/27179089920), (1860687715613/54358179840), (58562382979/3397386240),
    (61063939781/57982058496), (3216879916723/434865438720), (11093049842347/869730877440), (353380956101/54358179840), (30789035089/154618822656), (5440475817941/3478923509760), (19369322939549/6957847019520), (625898574067/434865438720),
    (118331134861/7421703487488), (8143408669099/55662776156160), (30114703660771/111325552312320), (989256741773/6957847019520)
  ]

private def degreeAS3 (i j k : ℕ) : ℚ :=
  (degreeAS3Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeAS3Correct : Axis3Correct 10 3 0 degreeAW3 degreeAS2 degreeAS3 := by
  decide +kernel

private theorem degreeASigns :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ degreeAS3 i j k := by
  decide +kernel

private theorem degreeACertificate :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ trans3 degreeACoeff 10 3 0 (0 : ℚ) ((5/8) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 degreeACoeff degreeAS1 degreeAS2 degreeAS3 10 3 0 (0 : ℚ) ((5/8) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) degreeAW1 degreeAW2 degreeAW3
    degreeAW1Correct degreeAW2Correct degreeAW3Correct
    degreeAS1Correct degreeAS2Correct degreeAS3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact degreeASigns i hi j hj k hk

theorem highDegreeA_certificate {x d : ℝ}
    (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1) :
    0 ≤ degreeRemainder (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d := by
  have h := msum_nonneg_on_box degreeACoeff 10 3 0 (x := x) (y := d) (z := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by norm_num) (by norm_num) degreeACertificate
  rwa [degreeAIdentity] at h


theorem scalarResidual_highDegreeA {x d a t : ℝ}
    (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ (5/8 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1)
    (haLower : d + lowDensity x - 1 ≤ a)
    (htLower : 2*a - lowDensity x ≤ t) (htA : t ≤ a) :
    0 ≤ scalarResidual (lowDensity x) (target (lowDensity x))
      (betaA x) (gammaA x) (lambdaA x) (lowTriangle x) d a t := by
  have hp := (lowDensity_mem (by linarith : 0 ≤ x) (by linarith : x ≤ 1)).1
  apply scalarResidual_nonneg_of_high_degree
    (lowDensity x) (target (lowDensity x)) (betaA x) (gammaA x)
    (lambdaA x) (lowTriangle x) d a t
    (by linarith) hd1 (gammaA_nonneg hx0 (by linarith)) (lambdaA_nonneg hx0) haLower htLower htA
    (by linarith)
  have hc := highDegreeA_certificate hx0 hx1 hd0 hd1
  exact sub_nonneg.mp hc


private def degreeCCoeffTerms : List IntTerm := [
  ⟨0, 0, 0, (-17496 : ℤ)⟩,
  ⟨0, 1, 0, (51120 : ℤ)⟩,
  ⟨0, 2, 0, (-21114 : ℤ)⟩,
  ⟨0, 3, 0, (-14058 : ℤ)⟩,
  ⟨1, 0, 0, (11664 : ℤ)⟩,
  ⟨1, 1, 0, (40101 : ℤ)⟩,
  ⟨1, 2, 0, (-262278 : ℤ)⟩,
  ⟨1, 3, 0, (217728 : ℤ)⟩,
  ⟨2, 0, 0, (-8424 : ℤ)⟩,
  ⟨2, 1, 0, (-67872 : ℤ)⟩,
  ⟨2, 2, 0, (346356 : ℤ)⟩,
  ⟨2, 3, 0, (-275238 : ℤ)⟩,
  ⟨3, 0, 0, (2784 : ℤ)⟩,
  ⟨3, 1, 0, (31071 : ℤ)⟩,
  ⟨3, 2, 0, (-149364 : ℤ)⟩,
  ⟨3, 3, 0, (115344 : ℤ)⟩,
  ⟨4, 0, 0, (-936 : ℤ)⟩,
  ⟨4, 1, 0, (-4119 : ℤ)⟩,
  ⟨5, 0, 0, (144 : ℤ)⟩,
  ⟨5, 1, 0, (8308 : ℤ)⟩,
  ⟨6, 0, 0, (-24 : ℤ)⟩,
  ⟨6, 1, 0, (-2773 : ℤ)⟩,
  ⟨7, 1, 0, (-128 : ℤ)⟩,
  ⟨8, 1, 0, (136 : ℤ)⟩,
  ⟨9, 1, 0, (-40 : ℤ)⟩,
  ⟨10, 1, 0, (4 : ℤ)⟩]

private def degreeCCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff degreeCCoeffTerms i j k

private def degreeCCoeff (i j k : ℕ) : ℚ :=
  (degreeCCoeffNumer i j k : ℚ) / 5184

private theorem degreeCCoeffExpansion (x d u : ℝ) :
    msum degreeCCoeff 10 3 0 x d u = sparseEval (degreeCCoeffTerms.map IntTerm.toRat) x d u / 5184 := by
  have he : ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      degreeCCoeffNumer i j k = intSparseCoeff degreeCCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ degreeCCoeffTerms, t.i ≤ 10 ∧ t.j ≤ 3 ∧ t.k ≤ 0 := by decide +kernel
  exact msum_intSparse_scaled degreeCCoeffNumer degreeCCoeffTerms 5184 10 3 0 he hb x d u

private theorem degreeCIdentity (x d u : ℝ) :
    msum degreeCCoeff 10 3 0 x d u = degreeRemainder (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d := by
  simp only [degreeCCoeffExpansion, sparseEval, IntTerm.toRat, degreeCCoeffTerms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, degreeRemainder, target,
    lowDensity, lowTriangle, betaC, gammaC, lambdaC,
    gammaLow, contactA, betaHigh, gammaHigh]
  push_cast
  ring


private def degreeCW1Data : Array ℚ := #[
    1, (5/8), (25/64), (125/512), (625/4096), (3125/32768), (15625/262144), (78125/2097152),
    (390625/16777216), (1953125/134217728), (9765625/1073741824), 10, (105/16), (275/64), (2875/1024), (1875/1024),
    (78125/65536), (203125/262144), (2109375/4194304), (2734375/8388608), (56640625/268435456), (146484375/1073741824), 45, (495/16),
    (5425/256), (29625/2048), (80625/8192), (109375/16384), (4734375/1048576), (25546875/8388608), (4296875/2097152), (369140625/268435456),
    (3955078125/4294967296), 120, (345/4), (1975/32), (180125/4096), (255625/8192), (2890625/131072), (8140625/524288),
    (182734375/16777216), (127734375/16777216), (1423828125/268435456), (3955078125/1073741824), 210, (315/2), (7525/64), (357875/4096),
    (4235625/65536), (24953125/524288), (146359375/4194304), (854765625/33554432), (2485546875/134217728), (14396484375/1073741824), (83056640625/8589934592), 252,
    (1575/8), (1225/8), (485625/4096), (2994375/32768), (73515625/1048576), (224578125/4194304), (2731640625/67108864), (516796875/16777216),
    (49833984375/2147483648), (149501953125/8589934592), 210, (1365/8), (17675/128), (455875/4096), (5854375/65536), (74859375/1048576),
    (953015625/16777216), (6039140625/134217728), (9523828125/268435456), (29900390625/1073741824), (747509765625/34359738368), 120, (405/4), (2725/32),
    (292375/4096), (976875/16384), (26015625/524288), (172546875/4194304), (9118828125/268435456), (7498828125/268435456), (98244140625/4294967296), (320361328125/17179869184),
    45, (315/8), (275/8), (122625/4096), (1704375/65536), (2953125/131072), (163265625/8388608), (4499296875/268435456),
    (61794140625/4294967296), (422876953125/34359738368), (2883251953125/274877906944), 10, (145/16), (525/64), (30375/4096), (219375/32768),
    (6328125/1048576), (11390625/2097152), (1309921875/268435456), (9397265625/2147483648), (269103515625/68719476736), (961083984375/274877906944), 1, (15/16),
    (225/256), (3375/4096), (50625/65536), (759375/1048576), (11390625/16777216), (170859375/268435456), (2562890625/4294967296), (38443359375/68719476736),
    (576650390625/1099511627776)
  ]

private def degreeCW1 (k i : ℕ) : ℚ :=
  (degreeCW1Data[k * 11 + i]?).getD 0

private theorem degreeCW1Correct : WeightsCorrect 10 ((5/8) : ℚ) ((5/16) : ℚ) degreeCW1 := by
  decide +kernel

private def degreeCW2Data : Array ℚ := #[
    1, (15/16), (225/256), (3375/4096), 3, (23/8), (705/256), (675/256),
    3, (47/16), (23/8), (45/16), 1, 1, 1, 1
  ]

private def degreeCW2 (k i : ℕ) : ℚ :=
  (degreeCW2Data[k * 4 + i]?).getD 0

private theorem degreeCW2Correct : WeightsCorrect 3 ((15/16) : ℚ) ((1/16) : ℚ) degreeCW2 := by
  decide +kernel

private def degreeCW3Data : Array ℚ := #[
    1
  ]

private def degreeCW3 (k i : ℕ) : ℚ :=
  (degreeCW3Data[k * 1 + i]?).getD 0

private theorem degreeCW3Correct : WeightsCorrect 0 (0 : ℚ) (1 : ℚ) degreeCW3 := by
  decide +kernel

private def degreeCS1Data : Array ℚ := #[
    (-141420761/56623104), (15368652003305/1391569403904), (-408691/24576), (75853/9216), (-1401992765/56623104), (153047389507055/1391569403904), (-8186765/49152), (3053785/36864),
    (-8345922445/75497472), (2742781350813005/5566277615616), (-24558205/32768), (1532175/4096), (-11049326675/37748736), (1820418888140005/1391569403904), (-130805305/65536), (49086415/49152),
    (-153720834485/301989888), (25376325600021185/11132555231232), (-228428375/65536), (85862665/49152), (-183455108519/301989888), (30330512991773645/11132555231232), (-273441637/65536), (34297809/16384),
    (-1825969161385/3623878656), (33584011608283795/14843406974976), (-227329095/65536), (85605205/49152), (-259841035915/905969664), (9569133173670215/7421703487488), (-129664235/65536), (48858925/49152),
    (-21586812625/201326592), (57310335752984135/118747255799808), (-48582605/65536), (6106905/16384), (-398848095/16777216), (12726785389733765/118747255799808), (-32407025/196608), (12234895/147456),
    (-318611987/134217728), (1697975510620985/158329674399744), (-3248633/196608), (1228633/147456)
  ]

private def degreeCS1 (i j k : ℕ) : ℚ :=
  (degreeCS1Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeCS1Correct : Axis1Correct 10 3 0 degreeCW1 degreeCCoeff degreeCS1 := by
  decide +kernel

private def degreeCS2Data : Array ℚ := #[
    (54758571311/2473901162496), (1828271236591/11132555231232), (6401565352903/22265110462464), (205161871337/1391569403904), (176931118355/824633720832), (18371519299705/11132555231232), (64931856617185/22265110462464), (2088516070895/1391569403904),
    (27481331339905/29686813949952), (329131636957675/44530220924928), (1174468231880995/89060441849856), (37923898391885/5566277615616), (17425568917625/7421703487488), (216881474490515/11132555231232), (781388950562315/22265110462464), (25333204571365/1391569403904),
    (231470697199045/59373627899904), (2990450105022295/89060441849856), (10871839049054575/178120883699712), (353832295086785/11132555231232), (265237754671873/59373627899904), (3536380237117291/89060441849856), (12951805590950563/178120883699712), (422861993735117/11132555231232),
    (860045994577565/237494511599616), (3893881582363445/118747255799808), (14321648997671165/237494511599616), (17349342213865/549755813888), (246915639874345/118747255799808), (1114837273091425/59373627899904), (4097670735870985/118747255799808), (14887013862095/824633720832),
    (518706808696675/633318697598976), (6814797632913505/949978046398464), (24869351593367305/1899956092796928), (810548294506055/118747255799808), (127206412010905/633318697598976), (1575540555123955/949978046398464), (5665924611162475/1899956092796928), (183434399295365/118747255799808),
    (19583152769053/844424930131968), (223701506634271/1266637395197952), (786945312767863/2533274790395904), (2801701514673/17592186044416)
  ]

private def degreeCS2 (i j k : ℕ) : ℚ :=
  (degreeCS2Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeCS2Correct : Axis2Correct 10 3 0 degreeCW2 degreeCS1 degreeCS2 := by
  decide +kernel

private def degreeCS3Data : Array ℚ := #[
    (54758571311/2473901162496), (1828271236591/11132555231232), (6401565352903/22265110462464), (205161871337/1391569403904), (176931118355/824633720832), (18371519299705/11132555231232), (64931856617185/22265110462464), (2088516070895/1391569403904),
    (27481331339905/29686813949952), (329131636957675/44530220924928), (1174468231880995/89060441849856), (37923898391885/5566277615616), (17425568917625/7421703487488), (216881474490515/11132555231232), (781388950562315/22265110462464), (25333204571365/1391569403904),
    (231470697199045/59373627899904), (2990450105022295/89060441849856), (10871839049054575/178120883699712), (353832295086785/11132555231232), (265237754671873/59373627899904), (3536380237117291/89060441849856), (12951805590950563/178120883699712), (422861993735117/11132555231232),
    (860045994577565/237494511599616), (3893881582363445/118747255799808), (14321648997671165/237494511599616), (17349342213865/549755813888), (246915639874345/118747255799808), (1114837273091425/59373627899904), (4097670735870985/118747255799808), (14887013862095/824633720832),
    (518706808696675/633318697598976), (6814797632913505/949978046398464), (24869351593367305/1899956092796928), (810548294506055/118747255799808), (127206412010905/633318697598976), (1575540555123955/949978046398464), (5665924611162475/1899956092796928), (183434399295365/118747255799808),
    (19583152769053/844424930131968), (223701506634271/1266637395197952), (786945312767863/2533274790395904), (2801701514673/17592186044416)
  ]

private def degreeCS3 (i j k : ℕ) : ℚ :=
  (degreeCS3Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeCS3Correct : Axis3Correct 10 3 0 degreeCW3 degreeCS2 degreeCS3 := by
  decide +kernel

private theorem degreeCSigns :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ degreeCS3 i j k := by
  decide +kernel

private theorem degreeCCertificate :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ trans3 degreeCCoeff 10 3 0 ((5/8) : ℚ) ((5/16) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 degreeCCoeff degreeCS1 degreeCS2 degreeCS3 10 3 0 ((5/8) : ℚ) ((5/16) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) degreeCW1 degreeCW2 degreeCW3
    degreeCW1Correct degreeCW2Correct degreeCW3Correct
    degreeCS1Correct degreeCS2Correct degreeCS3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact degreeCSigns i hi j hj k hk

theorem highDegreeC_certificate {x d : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x) (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1) :
    0 ≤ degreeRemainder (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d := by
  have h := msum_nonneg_on_box degreeCCoeff 10 3 0 (x := x) (y := d) (z := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by norm_num) (by norm_num) degreeCCertificate
  rwa [degreeCIdentity] at h


theorem scalarResidual_highDegreeC {x d a t : ℝ}
    (hx0 : (5/8 : ℝ) ≤ x) (hx1 : x ≤ (15/16 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1)
    (haLower : d + lowDensity x - 1 ≤ a)
    (htLower : 2*a - lowDensity x ≤ t) (htA : t ≤ a) :
    0 ≤ scalarResidual (lowDensity x) (target (lowDensity x))
      (betaC x) (gammaC x) (lambdaC x) (lowTriangle x) d a t := by
  have hp := (lowDensity_mem (by linarith : 0 ≤ x) (by linarith : x ≤ 1)).1
  apply scalarResidual_nonneg_of_high_degree
    (lowDensity x) (target (lowDensity x)) (betaC x) (gammaC x)
    (lambdaC x) (lowTriangle x) d a t
    (by linarith) hd1 (gammaC_nonneg hx0 (by linarith)) (lambdaC_nonneg hx0 (by linarith)) haLower htLower htA
    (by linarith)
  have hc := highDegreeC_certificate hx0 hx1 hd0 hd1
  exact sub_nonneg.mp hc


private def degreeJCoeffTerms : List IntTerm := [
  ⟨0, 0, 0, (-2187 : ℤ)⟩,
  ⟨0, 1, 0, (972 : ℤ)⟩,
  ⟨0, 2, 0, (12798 : ℤ)⟩,
  ⟨0, 3, 0, (-13446 : ℤ)⟩,
  ⟨1, 0, 0, (1458 : ℤ)⟩,
  ⟨1, 1, 0, (11394 : ℤ)⟩,
  ⟨1, 2, 0, (-46710 : ℤ)⟩,
  ⟨1, 3, 0, (37476 : ℤ)⟩,
  ⟨2, 0, 0, (-1053 : ℤ)⟩,
  ⟨2, 1, 0, (-5391 : ℤ)⟩,
  ⟨2, 2, 0, (22815 : ℤ)⟩,
  ⟨2, 3, 0, (-18234 : ℤ)⟩,
  ⟨3, 0, 0, (348 : ℤ)⟩,
  ⟨3, 1, 0, (1164 : ℤ)⟩,
  ⟨3, 2, 0, (-204 : ℤ)⟩,
  ⟨3, 3, 0, (-72 : ℤ)⟩,
  ⟨4, 0, 0, (-117 : ℤ)⟩,
  ⟨4, 1, 0, (-1615 : ℤ)⟩,
  ⟨4, 2, 0, (741 : ℤ)⟩,
  ⟨4, 3, 0, (-522 : ℤ)⟩,
  ⟨5, 0, 0, (18 : ℤ)⟩,
  ⟨5, 1, 0, (342 : ℤ)⟩,
  ⟨5, 2, 0, (-78 : ℤ)⟩,
  ⟨5, 3, 0, (324 : ℤ)⟩,
  ⟨6, 0, 0, (-3 : ℤ)⟩,
  ⟨6, 1, 0, (89 : ℤ)⟩,
  ⟨6, 2, 0, (-267 : ℤ)⟩,
  ⟨6, 3, 0, (-54 : ℤ)⟩,
  ⟨7, 1, 0, (72 : ℤ)⟩,
  ⟨7, 2, 0, (120 : ℤ)⟩,
  ⟨8, 1, 0, (-69 : ℤ)⟩,
  ⟨8, 2, 0, (-15 : ℤ)⟩,
  ⟨9, 1, 0, (20 : ℤ)⟩,
  ⟨10, 1, 0, (-2 : ℤ)⟩]

private def degreeJCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff degreeJCoeffTerms i j k

private def degreeJCoeff (i j k : ℕ) : ℚ :=
  (degreeJCoeffNumer i j k : ℚ) / 648

private theorem degreeJCoeffExpansion (x d u : ℝ) :
    msum degreeJCoeff 10 3 0 x d u = sparseEval (degreeJCoeffTerms.map IntTerm.toRat) x d u / 648 := by
  have he : ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      degreeJCoeffNumer i j k = intSparseCoeff degreeJCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ degreeJCoeffTerms, t.i ≤ 10 ∧ t.j ≤ 3 ∧ t.k ≤ 0 := by decide +kernel
  exact msum_intSparse_scaled degreeJCoeffNumer degreeJCoeffTerms 648 10 3 0 he hb x d u

private theorem degreeJIdentity (x d u : ℝ) :
    msum degreeJCoeff 10 3 0 x d u = degreeRemainder (lowDensity x) (target (lowDensity x)) (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) d := by
  simp only [degreeJCoeffExpansion, sparseEval, IntTerm.toRat, degreeJCoeffTerms, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, degreeRemainder, target,
    lowDensity, lowTriangle, betaJ, gammaJ, lambdaJ,
    gammaLow, contactA, betaHigh, gammaHigh]
  push_cast
  ring


private def degreeJW1Data : Array ℚ := #[
    1, (15/16), (225/256), (3375/4096), (50625/65536), (759375/1048576), (11390625/16777216), (170859375/268435456),
    (2562890625/4294967296), (38443359375/68719476736), (576650390625/1099511627776), 10, (151/16), (285/32), (34425/4096), (259875/32768),
    (7846875/1048576), (29615625/4194304), (1788328125/268435456), (13497890625/2147483648), (407499609375/68719476736), (192216796875/34359738368), 45, (171/4),
    (2599/64), (157995/4096), (2400975/65536), (18241875/524288), (277171875/8388608), (8422228125/268435456), (127950890625/4294967296), (121481015625/4294967296),
    (115330078125/4294967296), 120, (459/4), (3511/32), (429661/4096), (1642965/16384), (50254875/524288), (384260625/4194304),
    (23502909375/268435456), (2807409375/33554432), (5364984375/67108864), (2562890625/33554432), 210, (1617/8), (24899/128), (766717/4096),
    (11803471/65536), (181692075/1048576), (2796494625/16777216), (2689824375/16777216), (646734375/4194304), (621928125/4194304), (1196015625/8388608), 252,
    (1953/8), (7567/32), (938091/4096), (7267683/32768), (225193951/1048576), (109015245/524288), (211070475/1048576), (25538625/131072),
    (98870625/524288), (47840625/262144), 210, (819/4), (12775/64), (796985/4096), (12428865/65536), (12112805/65536),
    (11803471/65536), (11500755/65536), (5602275/32768), (5457375/32768), (5315625/32768), 120, (471/4), (3697/32),
    (464255/4096), (113855/1024), (223355/2048), (109531/1024), (429661/4096), (52665/512), (103275/1024), (50625/512),
    45, (711/16), (11233/256), (11091/256), (5475/128), (5405/128), (10671/256), (10533/256),
    (2599/64), (2565/64), (10125/256), 10, (159/16), (79/8), (157/16), (39/4),
    (155/16), (77/8), (153/16), (19/2), (151/16), (75/8), 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1,
    1
  ]

private def degreeJW1 (k i : ℕ) : ℚ :=
  (degreeJW1Data[k * 11 + i]?).getD 0

private theorem degreeJW1Correct : WeightsCorrect 10 ((15/16) : ℚ) ((1/16) : ℚ) degreeJW1 := by
  decide +kernel

private def degreeJW2Data : Array ℚ := #[
    1, (15/16), (225/256), (3375/4096), 3, (23/8), (705/256), (675/256),
    3, (47/16), (23/8), (45/16), 1, 1, 1, 1
  ]

private def degreeJW2 (k i : ℕ) : ℚ :=
  (degreeJW2Data[k * 4 + i]?).getD 0

private theorem degreeJW2Correct : WeightsCorrect 3 ((15/16) : ℚ) ((1/16) : ℚ) degreeJW2 := by
  decide +kernel

private def degreeJW3Data : Array ℚ := #[
    1
  ]

private def degreeJW3 (k i : ℕ) : ℚ :=
  (degreeJW3Data[k * 1 + i]?).getD 0

private theorem degreeJW3Correct : WeightsCorrect 0 (0 : ℚ) (1 : ℚ) degreeJW3 := by
  decide +kernel

private def degreeJS1Data : Array ℚ := #[
    (-318611987/134217728), (47171377461711/4398046511104), (-567699143007/34359738368), (558949717/67108864), (-796296723/33554432), (5532006091151/51539607552), (-8530375414045/51539607552), (4203743231/50331648),
    (-21494415019/201326592), (149462845202605/309237645312), (-76892489753885/103079215104), (113779963895/301989888), (-257874229249/905969664), (1168353252635/905969664), (-1804610521037/905969664), (152032006141/150994944),
    (-1804767160321/3623878656), (24547567260401/10871635968), (-12646930831309/3623878656), (1066176409597/603979776), (-176218115/294912), (153485583859/56623104), (-3708734015/884736), (156416515/73728),
    (-293658625/589824), (23990034737/10616832), (-6185994773/1769472), (261011969/147456), (-10241/36), (278971/216), (-3454003/1728), (145787/144),
    (-30721/288), (279017/576), (-10366003/13824), (437627/1152), (-640/27), (8720/81), (-500/3), (760/9),
    (-64/27), (872/81), (-50/3), (76/9)
  ]

private def degreeJS1 (i j k : ℕ) : ℚ :=
  (degreeJS1Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeJS1Correct : Axis1Correct 10 3 0 degreeJW1 degreeJCoeff degreeJS1 := by
  decide +kernel

private def degreeJS2Data : Array ℚ := #[
    (1600318560809/70368744177664), (6155524960029/35184372088832), (21718651753473/70368744177664), (696938220111/4398046511104), (1079639793649/4398046511104), (23919300759107/13194139533312), (868713509721/274877906944), (13858663187/8589934592),
    (10352952217969/8796093022208), (665905595541193/79164837199872), (71830644247073/4947802324992), (126702083347/17179869184), (6136947868273/1855425871872), (5339793416093/231928233984), (571197560261/14495514624), (18060539195/905969664),
    (14946851044219/2473901162496), (114610634660567/2783138807808), (12175627205551/173946175488), (383648658257/10871635968), (31473655/4194304), (22787936687/452984832), (2853263399/33554432), (2420612339/56623104),
    (11637152345/1811939328), (57776269021/1358954496), (12154802851/169869312), (381072617/10616832), (2207441/589824), (10859609/442368), (189779/4608), (35641/1728),
    (6707921/4718592), (3644881/393216), (1716217/110592), (107321/13824), (1465/4608), (10715/5184), (280/81), (140/81),
    (293/9216), (2143/10368), (28/81), (14/81)
  ]

private def degreeJS2 (i j k : ℕ) : ℚ :=
  (degreeJS2Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeJS2Correct : Axis2Correct 10 3 0 degreeJW2 degreeJS1 degreeJS2 := by
  decide +kernel

private def degreeJS3Data : Array ℚ := #[
    (1600318560809/70368744177664), (6155524960029/35184372088832), (21718651753473/70368744177664), (696938220111/4398046511104), (1079639793649/4398046511104), (23919300759107/13194139533312), (868713509721/274877906944), (13858663187/8589934592),
    (10352952217969/8796093022208), (665905595541193/79164837199872), (71830644247073/4947802324992), (126702083347/17179869184), (6136947868273/1855425871872), (5339793416093/231928233984), (571197560261/14495514624), (18060539195/905969664),
    (14946851044219/2473901162496), (114610634660567/2783138807808), (12175627205551/173946175488), (383648658257/10871635968), (31473655/4194304), (22787936687/452984832), (2853263399/33554432), (2420612339/56623104),
    (11637152345/1811939328), (57776269021/1358954496), (12154802851/169869312), (381072617/10616832), (2207441/589824), (10859609/442368), (189779/4608), (35641/1728),
    (6707921/4718592), (3644881/393216), (1716217/110592), (107321/13824), (1465/4608), (10715/5184), (280/81), (140/81),
    (293/9216), (2143/10368), (28/81), (14/81)
  ]

private def degreeJS3 (i j k : ℕ) : ℚ :=
  (degreeJS3Data[(i * 4 + j) * 1 + k]?).getD 0

private theorem degreeJS3Correct : Axis3Correct 10 3 0 degreeJW3 degreeJS2 degreeJS3 := by
  decide +kernel

private theorem degreeJSigns :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ degreeJS3 i j k := by
  decide +kernel

private theorem degreeJCertificate :
    ∀ i ∈ range 11, ∀ j ∈ range 4, ∀ k ∈ range 1,
      0 ≤ trans3 degreeJCoeff 10 3 0 ((15/16) : ℚ) ((1/16) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) i j k := by
  have exactTable := checked_trans3 degreeJCoeff degreeJS1 degreeJS2 degreeJS3 10 3 0 ((15/16) : ℚ) ((1/16) : ℚ) ((15/16) : ℚ) ((1/16) : ℚ) (0 : ℚ) (1 : ℚ) degreeJW1 degreeJW2 degreeJW3
    degreeJW1Correct degreeJW2Correct degreeJW3Correct
    degreeJS1Correct degreeJS2Correct degreeJS3Correct
  intro i hi j hj k hk
  rw [← exactTable i hi j hj k hk]
  exact degreeJSigns i hi j hj k hk

theorem highDegreeJ_certificate {x d : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1) :
    0 ≤ degreeRemainder (lowDensity x) (target (lowDensity x)) (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) d := by
  have h := msum_nonneg_on_box degreeJCoeff 10 3 0 (x := x) (y := d) (z := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith)
    (by norm_num) (by norm_num) degreeJCertificate
  rwa [degreeJIdentity] at h


theorem scalarResidual_highDegreeJ {x d a t : ℝ}
    (hx0 : (15/16 : ℝ) ≤ x) (hx1 : x ≤ (1 : ℝ))
    (hd0 : (15/16 : ℝ) ≤ d) (hd1 : d ≤ 1)
    (haLower : d + lowDensity x - 1 ≤ a)
    (htLower : 2*a - lowDensity x ≤ t) (htA : t ≤ a) :
    0 ≤ scalarResidual (lowDensity x) (target (lowDensity x))
      (betaJ x) (gammaJ x) (lambdaJ x) (lowTriangle x) d a t := by
  have hp := (lowDensity_mem (by linarith : 0 ≤ x) (by linarith : x ≤ 1)).1
  apply scalarResidual_nonneg_of_high_degree
    (lowDensity x) (target (lowDensity x)) (betaJ x) (gammaJ x)
    (lambdaJ x) (lowTriangle x) d a t
    (by linarith) hd1 (gammaJ_nonneg hx0 hx1) (lambdaJ_nonneg) haLower htLower htA
    (by linarith)
  have hc := highDegreeJ_certificate hx0 hx1 hd0 hd1
  exact sub_nonneg.mp hc


end Taeyoung.Methods.Atlas126
