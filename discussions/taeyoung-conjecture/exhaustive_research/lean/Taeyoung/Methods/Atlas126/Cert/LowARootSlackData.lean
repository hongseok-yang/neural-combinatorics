import Taeyoung.Methods.Atlas126.ARootSlack
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.LowARootSlackData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 0, 1, (72900 : ℤ)⟩,
  ⟨0, 0, 2, (-1239300 : ℤ)⟩,
  ⟨0, 0, 3, (7970400 : ℤ)⟩,
  ⟨0, 0, 4, (-25174800 : ℤ)⟩,
  ⟨0, 0, 5, (43545600 : ℤ)⟩,
  ⟨0, 0, 6, (-37324800 : ℤ)⟩,
  ⟨0, 0, 7, (12441600 : ℤ)⟩,
  ⟨0, 1, 0, (6075 : ℤ)⟩,
  ⟨0, 1, 1, (243000 : ℤ)⟩,
  ⟨0, 1, 2, (-3256200 : ℤ)⟩,
  ⟨0, 1, 3, (12441600 : ℤ)⟩,
  ⟨0, 1, 4, (-18662400 : ℤ)⟩,
  ⟨0, 1, 5, (9331200 : ℤ)⟩,
  ⟨0, 2, 0, (6075 : ℤ)⟩,
  ⟨0, 2, 1, (388800 : ℤ)⟩,
  ⟨0, 2, 2, (-2332800 : ℤ)⟩,
  ⟨0, 2, 3, (2332800 : ℤ)⟩,
  ⟨0, 3, 1, (194400 : ℤ)⟩,
  ⟨1, 0, 1, (518400 : ℤ)⟩,
  ⟨1, 0, 2, (-6835104 : ℤ)⟩,
  ⟨1, 0, 3, (33885216 : ℤ)⟩,
  ⟨1, 0, 4, (-95510016 : ℤ)⟩,
  ⟨1, 0, 5, (196473600 : ℤ)⟩,
  ⟨1, 0, 6, (-223948800 : ℤ)⟩,
  ⟨1, 0, 7, (99532800 : ℤ)⟩,
  ⟨1, 1, 0, (64800 : ℤ)⟩,
  ⟨1, 1, 1, (1701000 : ℤ)⟩,
  ⟨1, 1, 2, (-18434304 : ℤ)⟩,
  ⟨1, 1, 3, (60912000 : ℤ)⟩,
  ⟨1, 1, 4, (-111974400 : ℤ)⟩,
  ⟨1, 1, 5, (74649600 : ℤ)⟩,
  ⟨1, 2, 0, (64800 : ℤ)⟩,
  ⟨1, 2, 1, (2948400 : ℤ)⟩,
  ⟨1, 2, 2, (-13996800 : ℤ)⟩,
  ⟨1, 2, 3, (18662400 : ℤ)⟩,
  ⟨1, 3, 1, (1555200 : ℤ)⟩,
  ⟨2, 0, 1, (806004 : ℤ)⟩,
  ⟨2, 0, 2, (-6316704 : ℤ)⟩,
  ⟨2, 0, 3, (20562336 : ℤ)⟩,
  ⟨2, 0, 4, (-67191552 : ℤ)⟩,
  ⟨2, 0, 5, (161740800 : ℤ)⟩,
  ⟨2, 0, 6, (-286156800 : ℤ)⟩,
  ⟨2, 0, 7, (215654400 : ℤ)⟩,
  ⟨2, 1, 0, (226800 : ℤ)⟩,
  ⟨2, 1, 1, (2336904 : ℤ)⟩,
  ⟨2, 1, 2, (-18482688 : ℤ)⟩,
  ⟨2, 1, 3, (62208000 : ℤ)⟩,
  ⟨2, 1, 4, (-143078400 : ℤ)⟩,
  ⟨2, 1, 5, (161740800 : ℤ)⟩,
  ⟨2, 2, 0, (226800 : ℤ)⟩,
  ⟨2, 2, 1, (5443200 : ℤ)⟩,
  ⟨2, 2, 2, (-17884800 : ℤ)⟩,
  ⟨2, 2, 3, (40435200 : ℤ)⟩,
  ⟨2, 3, 1, (3369600 : ℤ)⟩,
  ⟨3, 0, 1, (-925992 : ℤ)⟩,
  ⟨3, 0, 2, (10431360 : ℤ)⟩,
  ⟨3, 0, 3, (-38250144 : ℤ)⟩,
  ⟨3, 0, 4, (131811840 : ℤ)⟩,
  ⟨3, 0, 5, (-164736000 : ℤ)⟩,
  ⟨3, 0, 6, (221184000 : ℤ)⟩,
  ⟨3, 0, 7, (-29491200 : ℤ)⟩,
  ⟨3, 1, 0, (201600 : ℤ)⟩,
  ⟨3, 1, 1, (-4353192 : ℤ)⟩,
  ⟨3, 1, 2, (27308160 : ℤ)⟩,
  ⟨3, 1, 3, (-56102400 : ℤ)⟩,
  ⟨3, 1, 4, (110592000 : ℤ)⟩,
  ⟨3, 1, 5, (-22118400 : ℤ)⟩,
  ⟨3, 2, 0, (201600 : ℤ)⟩,
  ⟨3, 2, 1, (-3729600 : ℤ)⟩,
  ⟨3, 2, 2, (13824000 : ℤ)⟩,
  ⟨3, 2, 3, (-5529600 : ℤ)⟩,
  ⟨3, 3, 1, (-460800 : ℤ)⟩,
  ⟨4, 0, 1, (-1224912 : ℤ)⟩,
  ⟨4, 0, 2, (3449328 : ℤ)⟩,
  ⟨4, 0, 3, (-27810432 : ℤ)⟩,
  ⟨4, 0, 4, (21044736 : ℤ)⟩,
  ⟨4, 0, 5, (-166656000 : ℤ)⟩,
  ⟨4, 0, 6, (165888000 : ℤ)⟩,
  ⟨4, 0, 7, (-287539200 : ℤ)⟩,
  ⟨4, 1, 0, (-319200 : ℤ)⟩,
  ⟨4, 1, 1, (-4593312 : ℤ)⟩,
  ⟨4, 1, 2, (8745984 : ℤ)⟩,
  ⟨4, 1, 3, (-76070400 : ℤ)⟩,
  ⟨4, 1, 4, (82944000 : ℤ)⟩,
  ⟨4, 1, 5, (-215654400 : ℤ)⟩,
  ⟨4, 2, 0, (-319200 : ℤ)⟩,
  ⟨4, 2, 1, (-8601600 : ℤ)⟩,
  ⟨4, 2, 2, (10368000 : ℤ)⟩,
  ⟨4, 2, 3, (-53913600 : ℤ)⟩,
  ⟨4, 3, 1, (-4492800 : ℤ)⟩,
  ⟨5, 0, 1, (1749664 : ℤ)⟩,
  ⟨5, 0, 2, (-3691360 : ℤ)⟩,
  ⟨5, 0, 3, (40519552 : ℤ)⟩,
  ⟨5, 0, 4, (-74563584 : ℤ)⟩,
  ⟨5, 0, 5, (181555200 : ℤ)⟩,
  ⟨5, 0, 6, (-132710400 : ℤ)⟩,
  ⟨5, 0, 7, (176947200 : ℤ)⟩,
  ⟨5, 1, 0, (-268800 : ℤ)⟩,
  ⟨5, 1, 1, (8268064 : ℤ)⟩,
  ⟨5, 1, 2, (-14724096 : ℤ)⟩,
  ⟨5, 1, 3, (82483200 : ℤ)⟩,
  ⟨5, 1, 4, (-66355200 : ℤ)⟩,
  ⟨5, 1, 5, (132710400 : ℤ)⟩,
  ⟨5, 2, 0, (-268800 : ℤ)⟩,
  ⟨5, 2, 1, (9273600 : ℤ)⟩,
  ⟨5, 2, 2, (-8294400 : ℤ)⟩,
  ⟨5, 2, 3, (33177600 : ℤ)⟩,
  ⟨5, 3, 1, (2764800 : ℤ)⟩,
  ⟨6, 0, 1, (-918208 : ℤ)⟩,
  ⟨6, 0, 2, (-1515392 : ℤ)⟩,
  ⟨6, 0, 3, (-13637632 : ℤ)⟩,
  ⟨6, 0, 4, (32716800 : ℤ)⟩,
  ⟨6, 0, 5, (-57139200 : ℤ)⟩,
  ⟨6, 0, 6, (22118400 : ℤ)⟩,
  ⟨6, 0, 7, (-29491200 : ℤ)⟩,
  ⟨6, 1, 0, (403200 : ℤ)⟩,
  ⟨6, 1, 1, (-4043008 : ℤ)⟩,
  ⟨6, 1, 2, (3225600 : ℤ)⟩,
  ⟨6, 1, 3, (-27187200 : ℤ)⟩,
  ⟨6, 1, 4, (11059200 : ℤ)⟩,
  ⟨6, 1, 5, (-22118400 : ℤ)⟩,
  ⟨6, 2, 0, (403200 : ℤ)⟩,
  ⟨6, 2, 1, (-3225600 : ℤ)⟩,
  ⟨6, 2, 2, (1382400 : ℤ)⟩,
  ⟨6, 2, 3, (-5529600 : ℤ)⟩,
  ⟨6, 3, 1, (-460800 : ℤ)⟩,
  ⟨7, 0, 1, (432000 : ℤ)⟩,
  ⟨7, 0, 2, (1401600 : ℤ)⟩,
  ⟨7, 0, 3, (1804800 : ℤ)⟩,
  ⟨7, 0, 4, (-5529600 : ℤ)⟩,
  ⟨7, 0, 5, (6144000 : ℤ)⟩,
  ⟨7, 1, 0, (-153600 : ℤ)⟩,
  ⟨7, 1, 1, (969600 : ℤ)⟩,
  ⟨7, 1, 2, (460800 : ℤ)⟩,
  ⟨7, 1, 3, (3072000 : ℤ)⟩,
  ⟨7, 2, 0, (-153600 : ℤ)⟩,
  ⟨7, 2, 1, (384000 : ℤ)⟩,
  ⟨8, 0, 1, (-411200 : ℤ)⟩,
  ⟨8, 0, 2, (-64000 : ℤ)⟩,
  ⟨8, 0, 3, (-1414400 : ℤ)⟩,
  ⟨8, 0, 4, (307200 : ℤ)⟩,
  ⟨8, 1, 0, (19200 : ℤ)⟩,
  ⟨8, 1, 1, (-430400 : ℤ)⟩,
  ⟨8, 1, 2, (-153600 : ℤ)⟩,
  ⟨8, 2, 0, (19200 : ℤ)⟩,
  ⟨9, 0, 1, (360000 : ℤ)⟩,
  ⟨9, 0, 2, (-288000 : ℤ)⟩,
  ⟨9, 0, 3, (1440000 : ℤ)⟩,
  ⟨9, 1, 1, (360000 : ℤ)⟩,
  ⟨10, 0, 1, (-170400 : ℤ)⟩,
  ⟨10, 0, 2, (163200 : ℤ)⟩,
  ⟨10, 0, 3, (-681600 : ℤ)⟩,
  ⟨10, 1, 1, (-170400 : ℤ)⟩,
  ⟨11, 0, 1, (38400 : ℤ)⟩,
  ⟨11, 0, 2, (-38400 : ℤ)⟩,
  ⟨11, 0, 3, (153600 : ℤ)⟩,
  ⟨11, 1, 1, (38400 : ℤ)⟩,
  ⟨12, 0, 1, (-3200 : ℤ)⟩,
  ⟨12, 0, 2, (3200 : ℤ)⟩,
  ⟨12, 0, 3, (-12800 : ℤ)⟩,
  ⟨12, 1, 1, (-3200 : ℤ)⟩]

def commonCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff commonCoeffTerms i j k

def commonCoeff (i j k : ℕ) : ℚ :=
  (commonCoeffNumer i j k : ℚ) / 1555200

theorem commonCoeffExpansion (x d u : ℝ) :
    msum commonCoeff 12 3 7 x d u = sparseEval (commonCoeffTerms.map IntTerm.toRat) x d u / 1555200 := by
  have he : ∀ i ∈ range 13, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonCoeffNumer i j k = intSparseCoeff commonCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ commonCoeffTerms, t.i ≤ 12 ∧ t.j ≤ 3 ∧ t.k ≤ 7 := by decide +kernel
  exact msum_intSparse_scaled commonCoeffNumer commonCoeffTerms 1555200 12 3 7 he hb x d u

theorem commonIdentity (x d u : ℝ) :
    msum commonCoeff 12 3 7 x d u = aRootSlackTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,aRootSlackTarget, aGammaRoot, contactA, lambdaA, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 208 (.node 104 (.node 52 (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (72900 : ℤ))
    (.leaf (-1239300 : ℤ))))
    (.node 1 (.leaf (7970400 : ℤ))
    (.node 1 (.leaf (-25174800 : ℤ))
    (.leaf (43545600 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-37324800 : ℤ))
    (.node 1 (.leaf (12441600 : ℤ))
    (.leaf (6075 : ℤ))))
    (.node 2 (.node 1 (.leaf (243000 : ℤ))
    (.leaf (-3256200 : ℤ)))
    (.node 1 (.leaf (12441600 : ℤ))
    (.leaf (-18662400 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (9331200 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (6075 : ℤ))
    (.node 1 (.leaf (388800 : ℤ))
    (.leaf (-2332800 : ℤ)))))
    (.node 3 (.node 1 (.leaf (2332800 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (194400 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (518400 : ℤ))
    (.leaf (-6835104 : ℤ))))
    (.node 2 (.node 1 (.leaf (33885216 : ℤ))
    (.leaf (-95510016 : ℤ)))
    (.node 1 (.leaf (196473600 : ℤ))
    (.leaf (-223948800 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (99532800 : ℤ))
    (.node 1 (.leaf (64800 : ℤ))
    (.leaf (1701000 : ℤ))))
    (.node 1 (.leaf (-18434304 : ℤ))
    (.node 1 (.leaf (60912000 : ℤ))
    (.leaf (-111974400 : ℤ)))))
    (.node 3 (.node 1 (.leaf (74649600 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (64800 : ℤ))
    (.leaf (2948400 : ℤ)))
    (.node 1 (.leaf (-13996800 : ℤ))
    (.leaf (18662400 : ℤ))))))))
    (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1555200 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (806004 : ℤ))
    (.node 1 (.leaf (-6316704 : ℤ))
    (.leaf (20562336 : ℤ))))
    (.node 1 (.leaf (-67191552 : ℤ))
    (.node 1 (.leaf (161740800 : ℤ))
    (.leaf (-286156800 : ℤ)))))
    (.node 3 (.node 1 (.leaf (215654400 : ℤ))
    (.node 1 (.leaf (226800 : ℤ))
    (.leaf (2336904 : ℤ))))
    (.node 2 (.node 1 (.leaf (-18482688 : ℤ))
    (.leaf (62208000 : ℤ)))
    (.node 1 (.leaf (-143078400 : ℤ))
    (.leaf (161740800 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (226800 : ℤ))))
    (.node 1 (.leaf (5443200 : ℤ))
    (.node 1 (.leaf (-17884800 : ℤ))
    (.leaf (40435200 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (3369600 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-925992 : ℤ))
    (.node 1 (.leaf (10431360 : ℤ))
    (.leaf (-38250144 : ℤ))))
    (.node 2 (.node 1 (.leaf (131811840 : ℤ))
    (.leaf (-164736000 : ℤ)))
    (.node 1 (.leaf (221184000 : ℤ))
    (.leaf (-29491200 : ℤ)))))))))
    (.node 52 (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (201600 : ℤ))
    (.node 1 (.leaf (-4353192 : ℤ))
    (.leaf (27308160 : ℤ))))
    (.node 1 (.leaf (-56102400 : ℤ))
    (.node 1 (.leaf (110592000 : ℤ))
    (.leaf (-22118400 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (201600 : ℤ))))
    (.node 2 (.node 1 (.leaf (-3729600 : ℤ))
    (.leaf (13824000 : ℤ)))
    (.node 1 (.leaf (-5529600 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-460800 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-1224912 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (3449328 : ℤ))
    (.node 1 (.leaf (-27810432 : ℤ))
    (.leaf (21044736 : ℤ))))
    (.node 1 (.leaf (-166656000 : ℤ))
    (.node 1 (.leaf (165888000 : ℤ))
    (.leaf (-287539200 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-319200 : ℤ))
    (.node 1 (.leaf (-4593312 : ℤ))
    (.leaf (8745984 : ℤ))))
    (.node 2 (.node 1 (.leaf (-76070400 : ℤ))
    (.leaf (82944000 : ℤ)))
    (.node 1 (.leaf (-215654400 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-319200 : ℤ))
    (.leaf (-8601600 : ℤ))))
    (.node 1 (.leaf (10368000 : ℤ))
    (.node 1 (.leaf (-53913600 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-4492800 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (1749664 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-3691360 : ℤ))
    (.node 1 (.leaf (40519552 : ℤ))
    (.leaf (-74563584 : ℤ))))
    (.node 2 (.node 1 (.leaf (181555200 : ℤ))
    (.leaf (-132710400 : ℤ)))
    (.node 1 (.leaf (176947200 : ℤ))
    (.leaf (-268800 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (8268064 : ℤ))
    (.node 1 (.leaf (-14724096 : ℤ))
    (.leaf (82483200 : ℤ))))
    (.node 1 (.leaf (-66355200 : ℤ))
    (.node 1 (.leaf (132710400 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-268800 : ℤ))
    (.leaf (9273600 : ℤ))))
    (.node 2 (.node 1 (.leaf (-8294400 : ℤ))
    (.leaf (33177600 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (2764800 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-918208 : ℤ))
    (.leaf (-1515392 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (-13637632 : ℤ))
    (.node 1 (.leaf (32716800 : ℤ))
    (.leaf (-57139200 : ℤ))))
    (.node 1 (.leaf (22118400 : ℤ))
    (.node 1 (.leaf (-29491200 : ℤ))
    (.leaf (403200 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-4043008 : ℤ))
    (.node 1 (.leaf (3225600 : ℤ))
    (.leaf (-27187200 : ℤ))))
    (.node 2 (.node 1 (.leaf (11059200 : ℤ))
    (.leaf (-22118400 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))
    (.node 104 (.node 52 (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (403200 : ℤ))
    (.node 1 (.leaf (-3225600 : ℤ))
    (.leaf (1382400 : ℤ))))
    (.node 1 (.leaf (-5529600 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-460800 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (432000 : ℤ))
    (.leaf (1401600 : ℤ)))))
    (.node 3 (.node 1 (.leaf (1804800 : ℤ))
    (.node 1 (.leaf (-5529600 : ℤ))
    (.leaf (6144000 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-153600 : ℤ))
    (.leaf (969600 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (460800 : ℤ))
    (.node 1 (.leaf (3072000 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-153600 : ℤ))
    (.node 1 (.leaf (384000 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
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
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-411200 : ℤ)))
    (.node 1 (.leaf (-64000 : ℤ))
    (.leaf (-1414400 : ℤ))))))))
    (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (307200 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (19200 : ℤ))
    (.leaf (-430400 : ℤ)))))
    (.node 3 (.node 1 (.leaf (-153600 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (19200 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (360000 : ℤ))
    (.node 1 (.leaf (-288000 : ℤ))
    (.leaf (1440000 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (360000 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 52 (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-170400 : ℤ))
    (.leaf (163200 : ℤ)))
    (.node 1 (.leaf (-681600 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (-170400 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))
    (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (38400 : ℤ))))
    (.node 1 (.leaf (-38400 : ℤ))
    (.node 1 (.leaf (153600 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (38400 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 26 (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
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
    (.leaf (-3200 : ℤ))))
    (.node 2 (.node 1 (.leaf (3200 : ℤ))
    (.leaf (-12800 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 13 (.node 6 (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 1 (.leaf (-3200 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 3 (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
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
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))))

def commonInputNumer (i j k : ℕ) : ℤ :=
  commonInputData.get ((i * 4 + j) * 8 + k)

def commonInput (i j k : ℕ) : ℚ :=
  (commonInputNumer i j k : ℚ) / 1555200

theorem commonInputNumerCorrect :
    ∀ i ∈ range 13, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInputNumer i j k = commonCoeffNumer i j k := by
  decide +kernel

theorem commonInputCorrect :
    ∀ i ∈ range 13, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInput i j k = commonCoeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/1555200)
    (commonInputNumerCorrect i hi j hj k hk)


end Taeyoung.Methods.Atlas126.LowARootSlackData
