import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5264692596576))
(.leaf (-1490086590912)))
(.node 1 (.leaf (261806714784))
(.leaf (610956820800))))
(.node 2 (.node 1 (.leaf (-840273953472))
(.leaf (-119972194848)))
(.node 1 (.leaf (-1490086590912))
(.node 1 (.leaf (12529489351968))
(.leaf (373879722240))))))
(.node 4 (.node 2 (.node 1 (.leaf (2043466828416))
(.leaf (-2430545906304)))
(.node 1 (.leaf (-187959481344))
(.leaf (261806714784))))
(.node 2 (.node 1 (.leaf (373879722240))
(.leaf (14606351612064)))
(.node 1 (.leaf (80694561312))
(.node 1 (.leaf (-275112726048))
(.leaf (137913899616)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (610956820800))
(.leaf (2043466828416)))
(.node 1 (.leaf (80694561312))
(.leaf (12277399309056))))
(.node 2 (.node 1 (.leaf (901273617504))
(.leaf (-1082052857088)))
(.node 1 (.leaf (-840273953472))
(.node 1 (.leaf (-2430545906304))
(.leaf (-275112726048))))))
(.node 4 (.node 2 (.node 1 (.leaf (901273617504))
(.leaf (12407653623168)))
(.node 1 (.leaf (-1201791002112))
(.leaf (-119972194848))))
(.node 2 (.node 1 (.leaf (-187959481344))
(.leaf (137913899616)))
(.node 1 (.leaf (-1082052857088))
(.node 1 (.leaf (-1201791002112))
(.leaf (11208572028288))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (66565967))
(.leaf (12423547)))
(.node 1 (.leaf (-2408303))
(.leaf (-7469086))))
(.node 2 (.node 1 (.leaf (10927701))
(.leaf (1750828)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (43894199))
(.leaf (-1480143))))))
(.node 4 (.node 2 (.node 1 (.leaf (-8142507))
(.leaf (10951404)))
(.node 1 (.leaf (1237052))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (40004449)))
(.node 1 (.leaf (96668))
(.node 1 (.leaf (403598))
(.leaf (-430937)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (44461562))))
(.node 2 (.node 1 (.leaf (-5675946))
(.leaf (3433917)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (45045256)))
(.node 1 (.leaf (4562808))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (46055686))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (350449353648822328992))
(.leaf (-1434608944416)))
(.node 1 (.leaf (-368045436096))
(.leaf (1628544476160))))
(.node 2 (.node 1 (.leaf (-2300761301472))
(.leaf (-1026764680608)))
(.node 1 (.leaf (-99189054837790691904))
(.node 1 (.leaf (531459738187399428768))
(.leaf (-3670252583328))))))
(.node 4 (.node 2 (.node 1 (.leaf (-568305515232))
(.leaf (6245544553920)))
(.node 1 (.leaf (4252055026176))
(.leaf (17427417136690156128))))
(.node 2 (.node 1 (.leaf (19663718956101904608))
(.leaf (583135142790532140864)))
(.node 1 (.leaf (-2085125131008))
(.node 1 (.leaf (6536345033376))
(.leaf (974673466560)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (40668931571797713600))
(.leaf (97286590394570136384)))
(.node 1 (.leaf (-1267850803631968800))
(.leaf (524677919168716546176))))
(.node 2 (.node 1 (.leaf (-2248373728512))
(.leaf (2817349223904)))
(.node 1 (.leaf (-55933648257776687424))
(.node 1 (.leaf (-117126048643778335680))
(.leaf (-5384543226075188064))))))
(.node 4 (.node 2 (.node 1 (.leaf (66112253704560803904))
(.leaf (517879165802634032832)))
(.node 1 (.leaf (391853106432))
(.leaf (-7986065163169538016))))
(.node 2 (.node 1 (.leaf (-9740811079437609312))
(.leaf (6084305870943366720)))
(.node 1 (.leaf (-45669884298358813632))
(.node 1 (.leaf (-51307088478038448480))
(.leaf (506517254011161829152))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23328000110158836740544615264))
(.leaf (-95496131651900290272)))
(.node 1 (.leaf (-24499300353666944832))
(.leaf (108405637858098846720))))
(.node 2 (.node 1 (.leaf (-153152400868662203424))
(.leaf (-68347583846117667936)))
(.node 1 (.leaf (-95496131651900290272))
(.node 1 (.leaf (23327999490662678171256353280))
(.leaf (-165675227046337466784))))))
(.node 4 (.node 2 (.node 1 (.leaf (-4713016537226799648))
(.leaf (245559559348512148896)))
(.node 1 (.leaf (173884490210446076448))
(.leaf (-24499300353666944832))))
(.node 2 (.node 1 (.leaf (-165675227046337466784))
(.leaf (23328000086190424309385864928)))
(.node 1 (.leaf (-86495137079365372896))
(.node 1 (.leaf (257779512826039601280))
(.leaf (35170385962645790496)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (108405637858098846720))
(.leaf (-4713016537226799648)))
(.node 1 (.leaf (-86495137079365372896))
(.leaf (23327999825413007190716982432))))
(.node 2 (.node 1 (.leaf (-133004158750660247424))
(.leaf (98404572815125421184)))
(.node 1 (.leaf (-153152400868662203424))
(.node 1 (.leaf (245559559348512148896))
(.leaf (257779512826039601280))))))
(.node 4 (.node 2 (.node 1 (.leaf (-133004158750660247424))
(.leaf (23327999659301249171983932000)))
(.node 1 (.leaf (37399172692199585184))
(.leaf (-68347583846117667936))))
(.node 2 (.node 1 (.leaf (173884490210446076448))
(.leaf (35170385962645790496)))
(.node 1 (.leaf (98404572815125421184))
(.node 1 (.leaf (37399172692199585184))
(.leaf (23327999618825105544726254304))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (378546901286009233346508911807190745230773335886589437416962167738253539510773422313162115398712224172126462902439998))
(.node 1 (.leaf (267463280990285907085030826662421086199309415398793765669430328661947547784182642164476094439749405726413631133066853))
(.leaf (-93172982154437192568627044229676654637073359800440330295416567887923645411972860221619255712349910023918101738622286))))
(.node 1 (.leaf (742447938702915973781927358059976764960490348160158322525666570880307344537207375215073730260750891515171714938798989))
(.node 1 (.leaf (986525706444615472215349045302559120383053201628965288474642977542561170427674945559768967111992925879900119773360512))
(.leaf (9957709850368761205611412006244434452619723427969628717598958867151620502684226294700225844906970865944842940247044102)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 14606351612064 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 66565967 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 5833715516394294155328 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (11667431032788588310657 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 11667431032788588310657 5833715516394294155328 (List.ofFn fun j : Fin 6 => K i j) =
      5833715516394294155328 * geometricEncoding 11667431032788588310657 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    14606351612064 66565967 5833715516394294155328 11667431032788588310657 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-22515648157877857348507777488811223215267033168211463993454296958377699182028654758040673970299525563316159852968373440211671967432158468124158315104964165435072))
(.node 1 (.leaf (93242177809061074053220158235488067853475549908900712270207030207950068568735911964654803098056019373019959252851280253864705608259470360228280989054688193026976))
(.leaf (21373353852500156367489335976104698916588166290513186432778119569872819838706900267817974676277681513762760878230010812695785358419142049710967203540578502184672))))
(.node 1 (.leaf (61780897864279790733513249982674052256878737265926900065388077723772707144901533060281729172514067588915973939260466371850278453523518733852650166812007711767872))
(.node 1 (.leaf (8592842002288127828349902504116356319987786248326613262761711646527992831422597325528650241899280156515751626692401838042544601510301173210826477349452488008608))
(.leaf (11107281437122028268234220357813437242967871802754501230533557572784485864941528556189714774025232637733759898068005475193321922636575811055489200827871267004357968901888)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 66565967 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 583135142790532140864 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 232901728029209102407154252928 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (465803456058418204814308505857 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 465803456058418204814308505857 232901728029209102407154252928 (List.ofFn fun j : Fin 6 => B i j) =
      232901728029209102407154252928 * geometricEncoding 465803456058418204814308505857 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    66565967 583135142790532140864 232901728029209102407154252928 465803456058418204814308505857 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09
set_option maxRecDepth 1000000
private def NData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (1))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (1)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (1))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1)))
(.node 1 (.leaf (0))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (1))))))))

def N (i j : Nat) : Int := NData.get (i * 6 + j)

private def NGData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5264692596576))
(.leaf (-1490086590912)))
(.node 1 (.leaf (261806714784))
(.leaf (610956820800))))
(.node 2 (.node 1 (.leaf (-840273953472))
(.leaf (-119972194848)))
(.node 1 (.leaf (-1490086590912))
(.node 1 (.leaf (12529489351968))
(.leaf (373879722240))))))
(.node 4 (.node 2 (.node 1 (.leaf (2043466828416))
(.leaf (-2430545906304)))
(.node 1 (.leaf (-187959481344))
(.leaf (261806714784))))
(.node 2 (.node 1 (.leaf (373879722240))
(.leaf (14606351612064)))
(.node 1 (.leaf (80694561312))
(.node 1 (.leaf (-275112726048))
(.leaf (137913899616)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (610956820800))
(.leaf (2043466828416)))
(.node 1 (.leaf (80694561312))
(.leaf (12277399309056))))
(.node 2 (.node 1 (.leaf (901273617504))
(.leaf (-1082052857088)))
(.node 1 (.leaf (-840273953472))
(.node 1 (.leaf (-2430545906304))
(.leaf (-275112726048))))))
(.node 4 (.node 2 (.node 1 (.leaf (901273617504))
(.leaf (12407653623168)))
(.node 1 (.leaf (-1201791002112))
(.leaf (-119972194848))))
(.node 2 (.node 1 (.leaf (-187959481344))
(.leaf (137913899616)))
(.node 1 (.leaf (-1082052857088))
(.node 1 (.leaf (-1201791002112))
(.leaf (11208572028288))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5264692596576))
(.leaf (-1490086590912)))
(.node 1 (.leaf (261806714784))
(.leaf (610956820800))))
(.node 2 (.node 1 (.leaf (-840273953472))
(.leaf (-119972194848)))
(.node 1 (.leaf (-1490086590912))
(.node 1 (.leaf (12529489351968))
(.leaf (373879722240))))))
(.node 4 (.node 2 (.node 1 (.leaf (2043466828416))
(.leaf (-2430545906304)))
(.node 1 (.leaf (-187959481344))
(.leaf (261806714784))))
(.node 2 (.node 1 (.leaf (373879722240))
(.leaf (14606351612064)))
(.node 1 (.leaf (80694561312))
(.node 1 (.leaf (-275112726048))
(.leaf (137913899616)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (610956820800))
(.leaf (2043466828416)))
(.node 1 (.leaf (80694561312))
(.leaf (12277399309056))))
(.node 2 (.node 1 (.leaf (901273617504))
(.leaf (-1082052857088)))
(.node 1 (.leaf (-840273953472))
(.node 1 (.leaf (-2430545906304))
(.leaf (-275112726048))))))
(.node 4 (.node 2 (.node 1 (.leaf (901273617504))
(.leaf (12407653623168)))
(.node 1 (.leaf (-1201791002112))
(.leaf (-119972194848))))
(.node 2 (.node 1 (.leaf (-187959481344))
(.leaf (137913899616)))
(.node 1 (.leaf (-1082052857088))
(.node 1 (.leaf (-1201791002112))
(.leaf (11208572028288))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-19847032892471072965370452676745289204683921109429766160232238773326808145514640992))
(.node 1 (.leaf (-31094188227635693086527667120522995332406544150057319315564965391994651900939958176))
(.leaf (22815134002303329700269553006017390316950731482062012164464998530170699844375728032))))
(.node 1 (.leaf (-179004299064675197817491050416985868085532633865912066840780793173337147516316567488))
(.node 1 (.leaf (-198812613030959347187555522220689998394207257987766951735217904773215154971526268800))
(.leaf (1854237125568121542709931363098891620145779604654999024566121709373459466081973472960)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 14606351612064 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 87638109672384 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (175276219344769 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 175276219344769 87638109672384 (List.ofFn fun j : Fin 6 => NG i j) =
      87638109672384 * geometricEncoding 175276219344769 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 14606351612064 87638109672384 175276219344769 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (175276219344769))
(.leaf (30721753067795574615687663361))))
(.node 1 (.leaf (5384792729366767067000924183536932068308609))
(.node 1 (.leaf (943826111558606800268692575318857129626827242928061816321))
(.leaf (165430272552866781514733926597098867582290213830936765880082314650174849)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 14606351612064 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 87638109672384 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (175276219344769 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 175276219344769 87638109672384 (List.ofFn fun j : Fin 6 => H i j) =
      87638109672384 * geometricEncoding 175276219344769 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    14606351612064 1 87638109672384 175276219344769 (fun i => FullProductEnc.get i)
    FullProduct_left_bound FullProduct_right_bound FullProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    FullProduct_encoded FullProduct_product i j

theorem expanded_entries_exact (i j : Fin 6) :
    H i j = ∑ k : Fin 6, (∑ l : Fin 6, N i l * G l k) * N j k := by
  rw [FullProduct_exact]
  apply Finset.sum_congr rfl
  intro k _
  rw [NGProduct_exact]
  rfl

#print axioms expanded_entries_exact
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Upper.Block09
