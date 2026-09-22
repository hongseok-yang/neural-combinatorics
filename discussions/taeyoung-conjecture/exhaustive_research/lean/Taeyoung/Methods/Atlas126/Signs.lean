import Taeyoung.Methods.Atlas126.Coefficients
import Taeyoung.Methods.Bernstein.Univariate

/-!
# Atlas 126: exact univariate sign certificates

The supporting planes have seven polynomial sign obligations.  They are kept
separate from the three-variable face certificates: each proof below is one
small rational Bernstein check on either `[0,5/8]` or `[5/8,1]`.
-/

open Finset

namespace Taeyoung.Methods.Atlas126

open Taeyoung.Methods.Bernstein

private def coeffAt (xs : List ℚ) (i : ℕ) : ℚ := xs.getD i 0

private def betaCCoeffs : List ℚ :=
  [(-1337/96 : ℚ), (1747/32 : ℚ), (-1101/16 : ℚ), (461/16 : ℚ)]

private theorem betaC_certificate :
    ∀ k ∈ range 4,
      0 ≤ trans (coeffAt betaCCoeffs) 3 (5/8 : ℚ) (3/8 : ℚ) k := by
  decide +kernel

private lemma betaC_polynomial (x : ℝ) :
    ∑ i ∈ range 4, ((coeffAt betaCCoeffs i : ℚ) : ℝ) * x ^ i = betaC x := by
  simp only [coeffAt, betaCCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [betaC]
  ring

theorem betaC_nonneg {x : ℝ} (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ betaC x := by
  have h := nonneg_on_interval_rat (coeffAt betaCCoeffs) 3
    (l := (5/8 : ℚ)) (W := (3/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) betaC_certificate
  rw [betaC_polynomial] at h
  exact h

private def gammaCCoeffs : List ℚ :=
  [(-3085/288 : ℚ), (42 : ℚ), (-1699/32 : ℚ), (89/4 : ℚ)]

private theorem gammaC_certificate :
    ∀ k ∈ range 4,
      0 ≤ trans (coeffAt gammaCCoeffs) 3 (5/8 : ℚ) (3/8 : ℚ) k := by
  decide +kernel

private lemma gammaC_polynomial (x : ℝ) :
    ∑ i ∈ range 4, ((coeffAt gammaCCoeffs i : ℚ) : ℝ) * x ^ i = gammaC x := by
  simp only [coeffAt, gammaCCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gammaC]
  ring

theorem gammaC_nonneg {x : ℝ} (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gammaC x := by
  have h := nonneg_on_interval_rat (coeffAt gammaCCoeffs) 3
    (l := (5/8 : ℚ)) (W := (3/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gammaC_certificate
  rw [gammaC_polynomial] at h
  exact h

private def lambdaCCoeffs : List ℚ :=
  [(65/16 : ℚ), (-63/4 : ℚ), (659/32 : ℚ), (-285/32 : ℚ)]

private theorem lambdaC_certificate :
    ∀ k ∈ range 4,
      0 ≤ trans (coeffAt lambdaCCoeffs) 3 (5/8 : ℚ) (3/8 : ℚ) k := by
  decide +kernel

private lemma lambdaC_polynomial (x : ℝ) :
    ∑ i ∈ range 4, ((coeffAt lambdaCCoeffs i : ℚ) : ℝ) * x ^ i = lambdaC x := by
  simp only [coeffAt, lambdaCCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [lambdaC]
  ring

theorem lambdaC_nonneg {x : ℝ} (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ lambdaC x := by
  have h := nonneg_on_interval_rat (coeffAt lambdaCCoeffs) 3
    (l := (5/8 : ℚ)) (W := (3/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) lambdaC_certificate
  rw [lambdaC_polynomial] at h
  exact h

private def gapZeroACoeffs : List ℚ :=
  [(1/32 : ℚ), (13/64 : ℚ), (1261/3600 : ℚ), (-313/43200 : ℚ),
    (-4357/16200 : ℚ), (41/648 : ℚ), (11/324 : ℚ), (-13/324 : ℚ),
    (17/648 : ℚ), (-5/648 : ℚ), (1/1296 : ℚ)]

private theorem gapZeroA_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapZeroACoeffs) 10 (0 : ℚ) (5/8 : ℚ) k := by
  decide +kernel

private lemma gapZeroA_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapZeroACoeffs i : ℚ) : ℝ) * x ^ i = gapZeroA x := by
  simp only [coeffAt, gapZeroACoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapZeroA, betaA, gammaA, gammaLow, contactA, lambdaA, lowDensity,
    lowTriangle, target]
  ring

theorem gapZeroA_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (5 : ℝ) / 8) :
    0 ≤ gapZeroA x := by
  have h := nonneg_on_interval_rat (coeffAt gapZeroACoeffs) 10
    (l := (0 : ℚ)) (W := (5/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapZeroA_certificate
  rw [gapZeroA_polynomial] at h
  exact h

private def gapOneACoeffs : List ℚ :=
  [(3/32 : ℚ), (877/4800 : ℚ), (-73/600 : ℚ), (-7769/43200 : ℚ),
    (917/4050 : ℚ), (-73/648 : ℚ), (31/648 : ℚ), (-13/324 : ℚ),
    (17/648 : ℚ), (-5/648 : ℚ), (1/1296 : ℚ)]

private theorem gapOneA_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapOneACoeffs) 10 (0 : ℚ) (5/8 : ℚ) k := by
  decide +kernel

private lemma gapOneA_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapOneACoeffs i : ℚ) : ℝ) * x ^ i = gapOneA x := by
  simp only [coeffAt, gapOneACoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapOneA, betaA, gammaA, gammaLow, contactA, lambdaA, lowDensity,
    lowTriangle, target]
  ring

theorem gapOneA_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (5 : ℝ) / 8) :
    0 ≤ gapOneA x := by
  have h := nonneg_on_interval_rat (coeffAt gapOneACoeffs) 10
    (l := (0 : ℚ)) (W := (5/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapOneA_certificate
  rw [gapOneA_polynomial] at h
  exact h

private def gapZeroCCoeffs : List ℚ :=
  [(-1337/192 : ℚ), (14195/576 : ℚ), (-4445/192 : ℚ), (-1621/864 : ℚ),
    (15385/1728 : ℚ), (-3221/5184 : ℚ), (-2773/5184 : ℚ), (-2/81 : ℚ),
    (17/648 : ℚ), (-5/648 : ℚ), (1/1296 : ℚ)]

private theorem gapZeroC_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapZeroCCoeffs) 10 (5/8 : ℚ) (3/8 : ℚ) k := by
  decide +kernel

private lemma gapZeroC_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapZeroCCoeffs i : ℚ) : ℝ) * x ^ i = gapZeroC x := by
  simp only [coeffAt, gapZeroCCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapZeroC, betaC, lambdaC, lowDensity, lowTriangle, target]
  ring

theorem gapZeroC_nonneg {x : ℝ} (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gapZeroC x := by
  have h := nonneg_on_interval_rat (coeffAt gapZeroCCoeffs) 10
    (l := (5/8 : ℚ)) (W := (3/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapZeroC_certificate
  rw [gapZeroC_polynomial] at h
  exact h

private def gapOneCCoeffs : List ℚ :=
  [(-43/144 : ℚ), (2405/1728 : ℚ), (-863/864 : ℚ), (-55/1728 : ℚ),
    (-1685/1728 : ℚ), (2113/1296 : ℚ), (-2797/5184 : ℚ), (-2/81 : ℚ),
    (17/648 : ℚ), (-5/648 : ℚ), (1/1296 : ℚ)]

private theorem gapOneC_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapOneCCoeffs) 10 (5/8 : ℚ) (3/8 : ℚ) k := by
  decide +kernel

private lemma gapOneC_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapOneCCoeffs i : ℚ) : ℝ) * x ^ i = gapOneC x := by
  simp only [coeffAt, gapOneCCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapOneC, betaC, gammaC, lambdaC, lowDensity, lowTriangle, target]
  ring

theorem gapOneC_nonneg {x : ℝ} (hx0 : (5 : ℝ) / 8 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gapOneC x := by
  have h := nonneg_on_interval_rat (coeffAt gapOneCCoeffs) 10
    (l := (5/8 : ℚ)) (W := (3/8 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapOneC_certificate
  rw [gapOneC_polynomial] at h
  exact h

/-! ### The quadratic junction plane on `[15/16,1]` -/

private def betaJCoeffs : List ℚ :=
  [(-151/4 : ℚ), 913/12, -893/24, 17/54, -247/216, 13/108, 89/216,
    -5/27, 5/216]

private theorem betaJ_certificate :
    ∀ k ∈ range 9,
      0 ≤ trans (coeffAt betaJCoeffs) 8 (15/16 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private lemma betaJ_polynomial (x : ℝ) :
    ∑ i ∈ range 9, ((coeffAt betaJCoeffs i : ℚ) : ℝ) * x ^ i = betaJ x := by
  simp only [coeffAt, betaJCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [betaJ, betaHigh, lowDensity]
  ring

theorem betaJ_nonneg {x : ℝ} (hx0 : (15 : ℝ) / 16 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ betaJ x := by
  have h := nonneg_on_interval_rat (coeffAt betaJCoeffs) 8
    (l := (15/16 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) betaJ_certificate
  rw [betaJ_polynomial] at h
  exact h

private def gammaJCoeffs : List ℚ :=
  [(-115/4 : ℚ), 347/6, -1013/36, -1/9, -29/36, 1/2, -1/12]

private theorem gammaJ_certificate :
    ∀ k ∈ range 7,
      0 ≤ trans (coeffAt gammaJCoeffs) 6 (15/16 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private lemma gammaJ_polynomial (x : ℝ) :
    ∑ i ∈ range 7, ((coeffAt gammaJCoeffs i : ℚ) : ℝ) * x ^ i = gammaJ x := by
  simp only [coeffAt, gammaJCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gammaJ, gammaHigh, lowDensity]
  ring

theorem gammaJ_nonneg {x : ℝ} (hx0 : (15 : ℝ) / 16 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gammaJ x := by
  have h := nonneg_on_interval_rat (coeffAt gammaJCoeffs) 6
    (l := (15/16 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gammaJ_certificate
  rw [gammaJ_polynomial] at h
  exact h

theorem lambdaJ_nonneg {x : ℝ} : 0 ≤ lambdaJ x := by
  simp only [lambdaJ]
  positivity

private def gapZeroJCoeffs : List ℚ :=
  [(-151/8 : ℚ), 395/12, -503/72, -119/18, -589/648, 19/36, 257/648,
    0, -5/54, 5/162, -1/324]

private theorem gapZeroJ_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapZeroJCoeffs) 10 (15/16 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private lemma gapZeroJ_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapZeroJCoeffs i : ℚ) : ℝ) * x ^ i = gapZeroJ x := by
  simp only [coeffAt, gapZeroJCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapZeroJ, betaJ, lambdaJ, betaHigh, lowDensity, lowTriangle, target]
  ring

theorem gapZeroJ_nonneg {x : ℝ} (hx0 : (15 : ℝ) / 16 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gapZeroJ x := by
  have h := nonneg_on_interval_rat (coeffAt gapZeroJCoeffs) 10
    (l := (15/16 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapZeroJ_certificate
  rw [gapZeroJ_polynomial] at h
  exact h

private def gapOneJCoeffs : List ℚ :=
  [(-23/8 : ℚ), 67/12, -23/8, 103/54, -1513/648, 101/108, -235/648,
    8/27, -7/54, 5/162, -1/324]

private theorem gapOneJ_certificate :
    ∀ k ∈ range 11,
      0 ≤ trans (coeffAt gapOneJCoeffs) 10 (15/16 : ℚ) (1/16 : ℚ) k := by
  decide +kernel

private lemma gapOneJ_polynomial (x : ℝ) :
    ∑ i ∈ range 11, ((coeffAt gapOneJCoeffs i : ℚ) : ℝ) * x ^ i = gapOneJ x := by
  simp only [coeffAt, gapOneJCoeffs, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [gapOneJ, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity,
    lowTriangle, target]
  ring

theorem gapOneJ_nonneg {x : ℝ} (hx0 : (15 : ℝ) / 16 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ gapOneJ x := by
  have h := nonneg_on_interval_rat (coeffAt gapOneJCoeffs) 10
    (l := (15/16 : ℚ)) (W := (1/16 : ℚ)) (x := x)
    (by norm_num) (by push_cast; linarith) (by push_cast; linarith) gapOneJ_certificate
  rw [gapOneJ_polynomial] at h
  exact h

end Taeyoung.Methods.Atlas126
