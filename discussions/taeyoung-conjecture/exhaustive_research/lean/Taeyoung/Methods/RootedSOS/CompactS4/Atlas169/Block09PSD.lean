import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (2554015292812172082711435130709186161431654864267582612737145639596710186730037010954843165902933747027201245323866))
(.node 1 (.leaf (1798406753346219113937828248174745394747454201513643540085613830745272255215926430494549758704416636449112964731984))
(.leaf (1434559967876751287352564643844755842210509515412557393079473887836495107646620934246810884392598864700302165286750))))
(.node 1 (.leaf (971929601684062419209924184654697178274535969390468008374979755896023462952094510318140240974327633880511599884498))
(.node 1 (.leaf (2907319939452222626599797167910327586974740382473046348447170320394557684794124266201873585527193009889718613416647))
(.leaf (3955330668889109441650598591700746338643505117925688581901257767143641471124578092351614372861772345535594493909328)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 10116668941344 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 24273712 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1473414649689174893568 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (2946829299378349787137 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 2946829299378349787137 1473414649689174893568 (List.ofFn fun j : Fin 6 => K i j) =
      1473414649689174893568 * geometricEncoding 2946829299378349787137 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    10116668941344 24273712 1473414649689174893568 2946829299378349787137 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (35440431619526729255765372538469259644984942264974482076520303146353697828302246430183354566489332300501403521201643010885267449773562099563962360599803872))
(.node 1 (.leaf (-86223608626796592112731756728730102783876692247502233175980800115142072421242642990475003670613324540917622060380565549045376309049404416740906399832161888))
(.leaf (-41109920322585008998991880666781035949805567999620067948167621125054135699047010475978865135311084206761847274664208647143826852449853449375861898136540096))))
(.node 1 (.leaf (97163049220387268846295576499605160141531160031940838700358771954237716156976617547429538457570933274813889402211330516659471885597684008329541033672652352))
(.node 1 (.leaf (144455748822245942315762682969877308630959485026891537765622438470864167754398010826528873213263264320020390660911316369993835587376593998766076444199071040))
(.leaf (2589085305317264417494122944934798025527830274299583009194642649471976647790020319302663991409873030407390836293917992711092698642473376844733976805080260080062944)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 24273712 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 111140517723077839536 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 16186757512445323382874465792 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (32373515024890646765748931585 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 32373515024890646765748931585 16186757512445323382874465792 (List.ofFn fun j : Fin 6 => B i j) =
      16186757512445323382874465792 * geometricEncoding 32373515024890646765748931585 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    24273712 111140517723077839536 16186757512445323382874465792 32373515024890646765748931585 (fun i => PKEnc.get i)
    PK_left_bound PK_right_bound PK_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    PK_encoded PK_product i j

private theorem upper : ∀ i j : Fin 6, j < i → P i j = 0 := by decide +kernel
private theorem diagonal : ∀ i : Fin 6, P i i ≠ 0 := by decide +kernel
private theorem symm : ∀ i j : Fin 6, B i j = B j i := by decide +kernel
private theorem dominant : ∀ i : Fin 6,
    (∑ j : Fin 6, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat := by decide +kernel
private theorem positive : ∀ i : Fin 6, 0 ≤ B i i := by decide +kernel

theorem gram_nonneg (x : Fin 6 → Real) :
    0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x :=
  matrixQuadratic_nonneg_of_integer_congruence
    (fun i j => G i j) (fun i j => P i j) (fun i j => K i j) (fun i j => B i j)
    upper diagonal GP_exact PK_exact symm dominant positive x

#print axioms gram_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09
