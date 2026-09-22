import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (26260438308480))
(.leaf (-48363859746144)))
(.node 1 (.leaf (-2742128437824))
(.leaf (10368872316864))))
(.node 2 (.node 1 (.leaf (4052645789184))
(.leaf (10796809780224)))
(.node 1 (.leaf (-48363859746144))
(.node 1 (.leaf (115950480517152))
(.leaf (-12530875525056))))))
(.node 4 (.node 2 (.node 1 (.leaf (15792580178784))
(.leaf (-24421110282432)))
(.node 1 (.leaf (-10473586856640))
(.leaf (-2742128437824))))
(.node 2 (.node 1 (.leaf (-12530875525056))
(.leaf (101862313022592)))
(.node 1 (.leaf (-42550538802336))
(.node 1 (.leaf (-8163339153984))
(.leaf (5696841743712)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (10368872316864))
(.leaf (15792580178784)))
(.node 1 (.leaf (-42550538802336))
(.leaf (67509985351680))))
(.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (-15138494761536)))
(.node 1 (.leaf (4052645789184))
(.node 1 (.leaf (-24421110282432))
(.leaf (-8163339153984))))))
(.node 4 (.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (40682467414368)))
(.node 1 (.leaf (-46481435292960))
(.leaf (10796809780224))))
(.node 2 (.node 1 (.leaf (-10473586856640))
(.leaf (5696841743712)))
(.node 1 (.leaf (-15138494761536))
(.node 1 (.leaf (-46481435292960))
(.leaf (71355007321920))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (29804907))
(.leaf (54256688)))
(.node 1 (.leaf (21066423))
(.leaf (-101665248))))
(.node 2 (.node 1 (.leaf (532568340))
(.leaf (-140897882)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (29460105))
(.leaf (10526141))))))
(.node 4 (.node 2 (.node 1 (.leaf (-47007827))
(.leaf (266872177)))
(.node 1 (.leaf (40772826))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (16092858)))
(.node 1 (.leaf (8370377))
(.node 1 (.leaf (-6821166))
(.leaf (59275362)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (40433197))))
(.node 2 (.node 1 (.leaf (-151825457))
(.leaf (105016291)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (117711936)))
(.node 1 (.leaf (383320583))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (295656683))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (782689921563483711360))
(.leaf (21719771529120)))
(.node 1 (.leaf (11012044755744))
(.leaf (-12972718039392))))
(.node 2 (.node 1 (.leaf (15995773963872))
(.leaf (-6201813371904)))
(.node 1 (.leaf (-1441480341894865528608))
(.node 1 (.leaf (791850482113458009888))
(.leaf (-20824048902528))))))
(.node 4 (.node 2 (.node 1 (.leaf (19834072081344))
(.leaf (-32574147278400)))
(.node 1 (.leaf (2974646055456))
(.leaf (-81728883071399602368))))
(.node 2 (.node 1 (.leaf (-517939715817024057792))
(.leaf (1449587138802405775488)))
(.node 1 (.leaf (40759705162656))
(.node 1 (.leaf (-24336658326816))
(.leaf (4939101857664)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (309043275099006051648))
(.leaf (1027831740495822598752)))
(.node 1 (.leaf (-300089802793750666272))
(.leaf (576951633360690435648))))
(.node 2 (.node 1 (.leaf (-376276884192))
(.leaf (-15853824366912)))
(.node 1 (.leaf (120788730850570725888))
(.node 1 (.leaf (-499565334978756312768))
(.leaf (-303056757556214732352))))))
(.node 4 (.node 2 (.node 1 (.leaf (744155180505342916992))
(.leaf (198178711625803648320)))
(.node 1 (.leaf (1205782096320))
(.leaf (321797911396266759168))))
(.node 2 (.node 1 (.leaf (277246171117727790912))
(.leaf (208882175082026001408)))
(.node 1 (.leaf (-1169732812761337825440))
(.node 1 (.leaf (-256939817620771753920))
(.leaf (78902325609060486240))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23328000322036926613099643520))
(.leaf (647355770486669391840)))
(.node 1 (.leaf (328212969824787635808))
(.leaf (-386650654701300896544))))
(.node 2 (.node 1 (.leaf (476752555386226319904))
(.leaf (-184844470780955132928)))
(.node 1 (.leaf (647355770486669391840))
(.node 1 (.leaf (23327999525805962171138272800))
(.leaf (-16001590639171229568))))))
(.node 4 (.node 2 (.node 1 (.leaf (-119542869081300672576))
(.leaf (-91760081830801856064)))
(.node 1 (.leaf (-248856468022053711072))
(.leaf (328212969824787635808))))
(.node 2 (.node 1 (.leaf (-16001590639171229568))
(.leaf (23327999996160924183838063968)))
(.node 1 (.leaf (591427620959317789536))
(.node 1 (.leaf (-397552713319857864672))
(.leaf (-19854215211839340384)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-386650654701300896544))
(.leaf (-119542869081300672576)))
(.node 1 (.leaf (591427620959317789536))
(.leaf (23327999778836634664361217696))))
(.node 2 (.node 1 (.leaf (-313895529554162334912))
(.leaf (-109001411897476820256)))
(.node 1 (.leaf (476752555386226319904))
(.node 1 (.leaf (-91760081830801856064))
(.leaf (-397552713319857864672))))))
(.node 4 (.node 2 (.node 1 (.leaf (-313895529554162334912))
(.leaf (23327999868301040082388946400)))
(.node 1 (.leaf (6219457153370766432))
(.leaf (-184844470780955132928))))
(.node 2 (.node 1 (.leaf (-248856468022053711072))
(.leaf (-19854215211839340384)))
(.node 1 (.leaf (-109001411897476820256))
(.node 1 (.leaf (6219457153370766432))
(.leaf (23327999955726186321060553440))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-31481120665498413770696210110135549419368902567314849077500794292758394674314606250740150425078493242232084020033351533877941972))
(.node 1 (.leaf (9109961320634834155623562593163598645936479258301621725116946724475613153653300544414891787793924955453438016792873397033305662))
(.leaf (13244023239562248257811370613553288314325667694763835231294676533000251216094960090485646847195843678859818574599176257850493111))))
(.node 1 (.leaf (23464018634532029946212043747891908979057942585629316875454749607445711311040458943009827141604276921540934994901115464213369311))
(.node 1 (.leaf (85646152771779777017219933297625573313392595205174966474110414341894025019760146754983568370422441999042113150453530289691967559))
(.leaf (66059216653689752108591749863457350155507994618213644011007658762229582039028247248617848741282252576890030615425731564448911083)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 115950480517152 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 532568340 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 370509329587331893006080 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (741018659174663786012161 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 741018659174663786012161 370509329587331893006080 (List.ofFn fun j : Fin 6 => K i j) =
      370509329587331893006080 * geometricEncoding 741018659174663786012161 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    115950480517152 532568340 370509329587331893006080 741018659174663786012161 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-423178197363952524782783792680736594635980328900742824708048351046570861917840990688863728572810764015944976377752220009453723316707933405614977507025854432079674795200))
(.node 1 (.leaf (202973756231751940511087033465889860187623727993551864204398134064622314865674846503056639076602127943575669595206591493816623090834051522279947248032043292711794593312))
(.leaf (337017593949544993190308911453073863795828618417916777203192945974571929376207552792324821590100259777912798611342364159908696711262180163192281592218363222475371697152))))
(.node 1 (.leaf (-1081779217560495277082041287667985973666376537207470429371413382208662224328772153663441763444672703908090513999604383814366919669573195710189348139120179806510744822368))
(.node 1 (.leaf (82276047880778421129520176625251583327992160540526209388353130180478788481570660015525476256936739701535918387915834329412232082693648272393820701467732163761549772160))
(.leaf (5383867897465440752349368587147666543915523350210652387148746026074698954597806411011416563023326037173037117048184831201870739127826379507937927954670076798499746706941076288)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 532568340 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1449587138802405775488 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 4632025297184080991148341099520 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (9264050594368161982296682199041 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 9264050594368161982296682199041 4632025297184080991148341099520 (List.ofFn fun j : Fin 6 => B i j) =
      4632025297184080991148341099520 * geometricEncoding 9264050594368161982296682199041 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    532568340 1449587138802405775488 4632025297184080991148341099520 9264050594368161982296682199041 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (26260438308480))
(.leaf (-48363859746144)))
(.node 1 (.leaf (-2742128437824))
(.leaf (10368872316864))))
(.node 2 (.node 1 (.leaf (4052645789184))
(.leaf (10796809780224)))
(.node 1 (.leaf (-48363859746144))
(.node 1 (.leaf (115950480517152))
(.leaf (-12530875525056))))))
(.node 4 (.node 2 (.node 1 (.leaf (15792580178784))
(.leaf (-24421110282432)))
(.node 1 (.leaf (-10473586856640))
(.leaf (-2742128437824))))
(.node 2 (.node 1 (.leaf (-12530875525056))
(.leaf (101862313022592)))
(.node 1 (.leaf (-42550538802336))
(.node 1 (.leaf (-8163339153984))
(.leaf (5696841743712)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (10368872316864))
(.leaf (15792580178784)))
(.node 1 (.leaf (-42550538802336))
(.leaf (67509985351680))))
(.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (-15138494761536)))
(.node 1 (.leaf (4052645789184))
(.node 1 (.leaf (-24421110282432))
(.leaf (-8163339153984))))))
(.node 4 (.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (40682467414368)))
(.node 1 (.leaf (-46481435292960))
(.leaf (10796809780224))))
(.node 2 (.node 1 (.leaf (-10473586856640))
(.leaf (5696841743712)))
(.node 1 (.leaf (-15138494761536))
(.node 1 (.leaf (-46481435292960))
(.leaf (71355007321920))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (26260438308480))
(.leaf (-48363859746144)))
(.node 1 (.leaf (-2742128437824))
(.leaf (10368872316864))))
(.node 2 (.node 1 (.leaf (4052645789184))
(.leaf (10796809780224)))
(.node 1 (.leaf (-48363859746144))
(.node 1 (.leaf (115950480517152))
(.leaf (-12530875525056))))))
(.node 4 (.node 2 (.node 1 (.leaf (15792580178784))
(.leaf (-24421110282432)))
(.node 1 (.leaf (-10473586856640))
(.leaf (-2742128437824))))
(.node 2 (.node 1 (.leaf (-12530875525056))
(.leaf (101862313022592)))
(.node 1 (.leaf (-42550538802336))
(.node 1 (.leaf (-8163339153984))
(.leaf (5696841743712)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (10368872316864))
(.leaf (15792580178784)))
(.node 1 (.leaf (-42550538802336))
(.leaf (67509985351680))))
(.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (-15138494761536)))
(.node 1 (.leaf (4052645789184))
(.node 1 (.leaf (-24421110282432))
(.leaf (-8163339153984))))))
(.node 4 (.node 2 (.node 1 (.leaf (1892388541824))
(.leaf (40682467414368)))
(.node 1 (.leaf (-46481435292960))
(.leaf (10796809780224))))
(.node 2 (.node 1 (.leaf (-10473586856640))
(.leaf (5696841743712)))
(.node 1 (.leaf (-15138494761536))
(.node 1 (.leaf (-46481435292960))
(.leaf (71355007321920))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (56307266434274668238543883518952631277150634287521882391773773826069394141640180609259680))
(.node 1 (.leaf (-54621601904994513483671232227038109124093180513215011317875751490186744908171622758675744))
(.leaf (29710034021775088191071307593857896513243605532766378063767503544334207675222812738590976))))
(.node 1 (.leaf (-78949919031915538885894114586987936956231683959553139298238939322009714399253321612406336))
(.node 1 (.leaf (-242408879526809130934508047670305053896310283647457658857802635531623209092097066149137216))
(.leaf (372128942759942683231076191275211238561122790041921284921275179056840582760167039899332224)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 115950480517152 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 695702883102912 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1391405766205825 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1391405766205825 695702883102912 (List.ofFn fun j : Fin 6 => NG i j) =
      695702883102912 * geometricEncoding 1391405766205825 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 115950480517152 695702883102912 1391405766205825 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1391405766205825))
(.leaf (1936010006230818939616263930625))))
(.node 1 (.leaf (2693775486101736659016533768695966507270890625))
(.node 1 (.leaf (3748134744225855589396070922939356162101445445939374812890625))
(.leaf (5215176295632250507099308266610208129989574852479017410001658573206962890625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 115950480517152 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 695702883102912 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1391405766205825 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1391405766205825 695702883102912 (List.ofFn fun j : Fin 6 => H i j) =
      695702883102912 * geometricEncoding 1391405766205825 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    115950480517152 1 695702883102912 1391405766205825 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Upper.Block09
