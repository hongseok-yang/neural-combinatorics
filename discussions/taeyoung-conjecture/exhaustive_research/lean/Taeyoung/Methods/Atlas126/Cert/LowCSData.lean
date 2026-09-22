import Taeyoung.Methods.Atlas126.LowCandidates
import Taeyoung.Methods.Bernstein.CheckedTensor


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open Finset


namespace Taeyoung.Methods.Atlas126.LowCSData

open Taeyoung.Methods.Bernstein

def commonCoeffTerms : List IntTerm := [
  ⟨0, 0, 1, (-475471043775 : ℤ)⟩,
  ⟨0, 0, 2, (692493473070 : ℤ)⟩,
  ⟨0, 0, 3, (211253925312 : ℤ)⟩,
  ⟨0, 0, 4, (155284858944 : ℤ)⟩,
  ⟨0, 0, 5, (-30027055104 : ℤ)⟩,
  ⟨0, 0, 6, (-2579890176 : ℤ)⟩,
  ⟨0, 0, 7, (1719926784 : ℤ)⟩,
  ⟨0, 1, 0, (-528491504250 : ℤ)⟩,
  ⟨0, 1, 1, (157831364160 : ℤ)⟩,
  ⟨0, 1, 2, (7487966592 : ℤ)⟩,
  ⟨0, 1, 3, (-61344055296 : ℤ)⟩,
  ⟨0, 1, 4, (-5159780352 : ℤ)⟩,
  ⟨0, 1, 5, (5159780352 : ℤ)⟩,
  ⟨0, 2, 0, (49337294400 : ℤ)⟩,
  ⟨0, 2, 1, (-31317000192 : ℤ)⟩,
  ⟨0, 2, 2, (-2579890176 : ℤ)⟩,
  ⟨0, 2, 3, (5159780352 : ℤ)⟩,
  ⟨0, 3, 1, (1719926784 : ℤ)⟩,
  ⟨1, 0, 1, (5246762841330 : ℤ)⟩,
  ⟨1, 0, 2, (-8615522204352 : ℤ)⟩,
  ⟨1, 0, 3, (-1642935744000 : ℤ)⟩,
  ⟨1, 0, 4, (-1072892418048 : ℤ)⟩,
  ⟨1, 0, 5, (124533448704 : ℤ)⟩,
  ⟨1, 0, 6, (-1719926784 : ℤ)⟩,
  ⟨1, 1, 0, (6216499094400 : ℤ)⟩,
  ⟨1, 1, 1, (-1222063255296 : ℤ)⟩,
  ⟨1, 1, 2, (88219404288 : ℤ)⟩,
  ⟨1, 1, 3, (247346970624 : ℤ)⟩,
  ⟨1, 1, 4, (-3439853568 : ℤ)⟩,
  ⟨1, 2, 0, (-386893946880 : ℤ)⟩,
  ⟨1, 2, 1, (122813521920 : ℤ)⟩,
  ⟨1, 2, 2, (-1719926784 : ℤ)⟩,
  ⟨2, 0, 1, (-24864373944714 : ℤ)⟩,
  ⟨2, 0, 2, (46303454168334 : ℤ)⟩,
  ⟨2, 0, 3, (5086986954048 : ℤ)⟩,
  ⟨2, 0, 4, (3198905654400 : ℤ)⟩,
  ⟨2, 0, 5, (-155886280704 : ℤ)⟩,
  ⟨2, 0, 6, (859963392 : ℤ)⟩,
  ⟨2, 1, 0, (-32232824577090 : ℤ)⟩,
  ⟨2, 1, 1, (3873850346304 : ℤ)⟩,
  ⟨2, 1, 2, (-543746566656 : ℤ)⟩,
  ⟨2, 1, 3, (-311485906944 : ℤ)⟩,
  ⟨2, 1, 4, (1719926784 : ℤ)⟩,
  ⟨2, 2, 0, (1247574628224 : ℤ)⟩,
  ⟨2, 2, 1, (-155599626240 : ℤ)⟩,
  ⟨2, 2, 2, (859963392 : ℤ)⟩,
  ⟨3, 0, 1, (65189164408590 : ℤ)⟩,
  ⟨3, 0, 2, (-141790179039912 : ℤ)⟩,
  ⟨3, 0, 3, (-7891090848000 : ℤ)⟩,
  ⟨3, 0, 4, (-5288409513216 : ℤ)⟩,
  ⟨3, 0, 5, (64676413440 : ℤ)⟩,
  ⟨3, 1, 0, (96774699770928 : ℤ)⟩,
  ⟨3, 1, 1, (-6424371930240 : ℤ)⟩,
  ⟨3, 1, 2, (1079246405376 : ℤ)⟩,
  ⟨3, 1, 3, (129926135808 : ℤ)⟩,
  ⟨3, 2, 0, (-2122626290688 : ℤ)⟩,
  ⟨3, 2, 1, (65249722368 : ℤ)⟩,
  ⟨4, 0, 1, (-99644081639100 : ℤ)⟩,
  ⟨4, 0, 2, (273823717187754 : ℤ)⟩,
  ⟨4, 0, 3, (6071598696384 : ℤ)⟩,
  ⟨4, 0, 4, (5047042519872 : ℤ)⟩,
  ⟨4, 0, 5, (143327232 : ℤ)⟩,
  ⟨4, 1, 0, (-185589229498254 : ℤ)⟩,
  ⟨4, 1, 1, (5852974372416 : ℤ)⟩,
  ⟨4, 1, 2, (-1000174656384 : ℤ)⟩,
  ⟨4, 1, 3, (143327232 : ℤ)⟩,
  ⟨4, 2, 0, (2015731096128 : ℤ)⟩,
  ⟨5, 0, 1, (79476206482402 : ℤ)⟩,
  ⟨5, 0, 2, (-347232590445744 : ℤ)⟩,
  ⟨5, 0, 3, (-1451946723840 : ℤ)⟩,
  ⟨5, 0, 4, (-2595588053760 : ℤ)⟩,
  ⟨5, 1, 0, (235999615028256 : ℤ)⟩,
  ⟨5, 1, 1, (-2757506144256 : ℤ)⟩,
  ⟨5, 1, 2, (452176701696 : ℤ)⟩,
  ⟨5, 2, 0, (-1015905659904 : ℤ)⟩,
  ⟨6, 0, 1, (-5149119301666 : ℤ)⟩,
  ⟨6, 0, 2, (290211351420426 : ℤ)⟩,
  ⟨6, 0, 3, (-834053124672 : ℤ)⟩,
  ⟨6, 0, 4, (553703454720 : ℤ)⟩,
  ⟨6, 1, 0, (-199199394194742 : ℤ)⟩,
  ⟨6, 1, 1, (565655055552 : ℤ)⟩,
  ⟨6, 1, 2, (-84907948032 : ℤ)⟩,
  ⟨6, 2, 0, (212867813376 : ℤ)⟩,
  ⟨7, 0, 1, (-53580681309686 : ℤ)⟩,
  ⟨7, 0, 2, (-154711757883816 : ℤ)⟩,
  ⟨7, 0, 3, (461122829568 : ℤ)⟩,
  ⟨7, 1, 0, (107728706181168 : ℤ)⟩,
  ⟨7, 1, 1, (-121277206656 : ℤ)⟩,
  ⟨8, 0, 1, (50243134555771 : ℤ)⟩,
  ⟨8, 0, 2, (47921706296784 : ℤ)⟩,
  ⟨8, 0, 3, (8651279232 : ℤ)⟩,
  ⟨8, 1, 0, (-33905851399296 : ℤ)⟩,
  ⟨8, 1, 1, (93758541696 : ℤ)⟩,
  ⟨9, 0, 1, (-17109991256140 : ℤ)⟩,
  ⟨9, 0, 2, (-6617015665728 : ℤ)⟩,
  ⟨9, 0, 3, (-16178319360 : ℤ)⟩,
  ⟨9, 1, 0, (4736308847616 : ℤ)⟩,
  ⟨9, 1, 1, (-16178319360 : ℤ)⟩,
  ⟨10, 0, 1, (-1084248592100 : ℤ)⟩,
  ⟨10, 0, 2, (17062286400 : ℤ)⟩,
  ⟨10, 0, 3, (-3912168960 : ℤ)⟩,
  ⟨10, 1, 1, (-3912168960 : ℤ)⟩,
  ⟨11, 0, 1, (1972500433920 : ℤ)⟩,
  ⟨11, 0, 2, (-2274481152 : ℤ)⟩,
  ⟨11, 0, 3, (1764301824 : ℤ)⟩,
  ⟨11, 1, 1, (1764301824 : ℤ)⟩,
  ⟨12, 0, 1, (-74237455872 : ℤ)⟩,
  ⟨12, 0, 2, (-1057257984 : ℤ)⟩,
  ⟨12, 0, 3, (-365741568 : ℤ)⟩,
  ⟨12, 1, 1, (-365741568 : ℤ)⟩,
  ⟨13, 0, 1, (-196396604064 : ℤ)⟩,
  ⟨13, 0, 2, (401200128 : ℤ)⟩,
  ⟨13, 0, 3, (29528064 : ℤ)⟩,
  ⟨13, 1, 1, (29528064 : ℤ)⟩,
  ⟨14, 0, 1, (59914485648 : ℤ)⟩,
  ⟨14, 0, 2, (-70799616 : ℤ)⟩,
  ⟨15, 0, 1, (-9705505536 : ℤ)⟩,
  ⟨15, 0, 2, (4921344 : ℤ)⟩,
  ⟨16, 0, 1, (656999424 : ℤ)⟩]

def commonCoeffNumer (i j k : ℕ) : ℤ :=
  intSparseCoeff commonCoeffTerms i j k

def commonCoeff (i j k : ℕ) : ℚ :=
  (commonCoeffNumer i j k : ℚ) / 429981696

theorem commonCoeffExpansion (x d u : ℝ) :
    msum commonCoeff 16 3 7 x d u = sparseEval (commonCoeffTerms.map IntTerm.toRat) x d u / 429981696 := by
  have he : ∀ i ∈ range 17, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonCoeffNumer i j k = intSparseCoeff commonCoeffTerms i j k := by intros; rfl
  have hb : ∀ t ∈ commonCoeffTerms, t.i ≤ 16 ∧ t.j ≤ 3 ∧ t.k ≤ 7 := by decide +kernel
  exact msum_intSparse_scaled commonCoeffNumer commonCoeffTerms 429981696 16 3 7 he hb x d u

theorem commonIdentity (x d u : ℝ) :
    msum commonCoeff 16 3 7 x d u = cSlackTarget x d u := by
  rw [commonCoeffExpansion]
  simp only [sparseEval,IntTerm.toRat,commonCoeffTerms,cSlackTarget, betaC, gammaC, lambdaC, gammaLow, contactA, slackPolynomial, scalarResidual, betaJ, gammaJ, lambdaJ, betaHigh, gammaHigh, lowDensity, lowTriangle, target,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  push_cast
  ring


def commonInputData : IntTable :=
  (.node 272 (.node 136 (.node 68 (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-475471043775 : ℤ)))
    (.node 1 (.leaf (692493473070 : ℤ))
    (.leaf (211253925312 : ℤ))))
    (.node 2 (.node 1 (.leaf (155284858944 : ℤ))
    (.leaf (-30027055104 : ℤ)))
    (.node 1 (.leaf (-2579890176 : ℤ))
    (.leaf (1719926784 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-528491504250 : ℤ))
    (.leaf (157831364160 : ℤ)))
    (.node 1 (.leaf (7487966592 : ℤ))
    (.leaf (-61344055296 : ℤ))))
    (.node 2 (.node 1 (.leaf (-5159780352 : ℤ))
    (.leaf (5159780352 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (49337294400 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-31317000192 : ℤ))
    (.leaf (-2579890176 : ℤ)))
    (.node 1 (.leaf (5159780352 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (1719926784 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (5246762841330 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-8615522204352 : ℤ))
    (.leaf (-1642935744000 : ℤ)))
    (.node 1 (.leaf (-1072892418048 : ℤ))
    (.leaf (124533448704 : ℤ))))
    (.node 2 (.node 1 (.leaf (-1719926784 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (6216499094400 : ℤ))
    (.leaf (-1222063255296 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (88219404288 : ℤ))
    (.leaf (247346970624 : ℤ)))
    (.node 1 (.leaf (-3439853568 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-386893946880 : ℤ))
    (.node 1 (.leaf (122813521920 : ℤ))
    (.leaf (-1719926784 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (-24864373944714 : ℤ))
    (.node 1 (.leaf (46303454168334 : ℤ))
    (.leaf (5086986954048 : ℤ)))))))))
    (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (3198905654400 : ℤ))
    (.leaf (-155886280704 : ℤ)))
    (.node 1 (.leaf (859963392 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-32232824577090 : ℤ))
    (.leaf (3873850346304 : ℤ)))
    (.node 1 (.leaf (-543746566656 : ℤ))
    (.leaf (-311485906944 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (1719926784 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (1247574628224 : ℤ))
    (.leaf (-155599626240 : ℤ)))
    (.node 1 (.leaf (859963392 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (65189164408590 : ℤ))
    (.leaf (-141790179039912 : ℤ)))
    (.node 1 (.leaf (-7891090848000 : ℤ))
    (.node 1 (.leaf (-5288409513216 : ℤ))
    (.leaf (64676413440 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (96774699770928 : ℤ))
    (.leaf (-6424371930240 : ℤ))))
    (.node 2 (.node 1 (.leaf (1079246405376 : ℤ))
    (.leaf (129926135808 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-2122626290688 : ℤ))
    (.leaf (65249722368 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-99644081639100 : ℤ))
    (.leaf (273823717187754 : ℤ))))
    (.node 2 (.node 1 (.leaf (6071598696384 : ℤ))
    (.leaf (5047042519872 : ℤ)))
    (.node 1 (.leaf (143327232 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))
    (.node 68 (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-185589229498254 : ℤ))
    (.leaf (5852974372416 : ℤ)))
    (.node 1 (.leaf (-1000174656384 : ℤ))
    (.leaf (143327232 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (2015731096128 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (79476206482402 : ℤ))
    (.leaf (-347232590445744 : ℤ)))
    (.node 1 (.leaf (-1451946723840 : ℤ))
    (.leaf (-2595588053760 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (235999615028256 : ℤ))
    (.leaf (-2757506144256 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (452176701696 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-1015905659904 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-5149119301666 : ℤ))
    (.leaf (290211351420426 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-834053124672 : ℤ))
    (.leaf (553703454720 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-199199394194742 : ℤ)))
    (.node 1 (.leaf (565655055552 : ℤ))
    (.node 1 (.leaf (-84907948032 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (212867813376 : ℤ))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (-53580681309686 : ℤ))
    (.leaf (-154711757883816 : ℤ)))
    (.node 1 (.leaf (461122829568 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (107728706181168 : ℤ))))
    (.node 2 (.node 1 (.leaf (-121277206656 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (50243134555771 : ℤ))
    (.leaf (47921706296784 : ℤ))))
    (.node 2 (.node 1 (.leaf (8651279232 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-33905851399296 : ℤ)))
    (.node 1 (.leaf (93758541696 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))))
    (.node 136 (.node 68 (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-17109991256140 : ℤ))
    (.leaf (-6617015665728 : ℤ)))
    (.node 1 (.leaf (-16178319360 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (4736308847616 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-16178319360 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (-1084248592100 : ℤ))
    (.leaf (17062286400 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (-3912168960 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-3912168960 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (1972500433920 : ℤ)))
    (.node 1 (.leaf (-2274481152 : ℤ))
    (.node 1 (.leaf (1764301824 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (1764301824 : ℤ))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (-74237455872 : ℤ))))
    (.node 2 (.node 1 (.leaf (-1057257984 : ℤ))
    (.leaf (-365741568 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (-365741568 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))
    (.node 68 (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-196396604064 : ℤ)))
    (.node 1 (.leaf (401200128 : ℤ))
    (.leaf (29528064 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (29528064 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (59914485648 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (-70799616 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))))
    (.node 34 (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (-9705505536 : ℤ)))
    (.node 1 (.leaf (4921344 : ℤ))
    (.leaf (0 : ℤ)))))
    (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
    (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))
    (.node 17 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (656999424 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))))))
    (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ)))
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))
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
    (.node 1 (.leaf (0 : ℤ))
    (.leaf (0 : ℤ))))))))))))

def commonInputNumer (i j k : ℕ) : ℤ :=
  commonInputData.get ((i * 4 + j) * 8 + k)

def commonInput (i j k : ℕ) : ℚ :=
  (commonInputNumer i j k : ℚ) / 429981696

theorem commonInputNumerCorrect :
    ∀ i ∈ range 17, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInputNumer i j k = commonCoeffNumer i j k := by
  decide +kernel

theorem commonInputCorrect :
    ∀ i ∈ range 17, ∀ j ∈ range 4, ∀ k ∈ range 8,
      commonInput i j k = commonCoeff i j k := by
  intro i hi j hj k hk
  exact congrArg (fun v : ℤ => (v : ℚ)/429981696)
    (commonInputNumerCorrect i hi j hj k hk)


end Taeyoung.Methods.Atlas126.LowCSData
