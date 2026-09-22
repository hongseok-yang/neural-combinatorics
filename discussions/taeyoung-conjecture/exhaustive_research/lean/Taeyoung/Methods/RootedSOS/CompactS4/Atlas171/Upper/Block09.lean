import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (13377286177200))
(.leaf (-25352094639024)))
(.node 1 (.leaf (187228930032))
(.leaf (1332695607552))))
(.node 2 (.node 1 (.leaf (2586062239920))
(.leaf (3611075512608)))
(.node 1 (.leaf (-25352094639024))
(.node 1 (.leaf (62457219855216))
(.leaf (-8774159377680))))))
(.node 4 (.node 2 (.node 1 (.leaf (13198268854800))
(.leaf (-15798043922976)))
(.node 1 (.leaf (-4091624532720))
(.leaf (187228930032))))
(.node 2 (.node 1 (.leaf (-8774159377680))
(.leaf (65171359836864)))
(.node 1 (.leaf (-19784005247808))
(.node 1 (.leaf (-10899445060368))
(.leaf (-399086652672)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1332695607552))
(.leaf (13198268854800)))
(.node 1 (.leaf (-19784005247808))
(.leaf (30320201843712))))
(.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (-16459321992480)))
(.node 1 (.leaf (2586062239920))
(.node 1 (.leaf (-15798043922976))
(.leaf (-10899445060368))))))
(.node 4 (.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (28633455920448)))
(.node 1 (.leaf (-25068214352448))
(.leaf (3611075512608))))
(.node 2 (.node 1 (.leaf (-4091624532720))
(.leaf (-399086652672)))
(.node 1 (.leaf (-16459321992480))
(.node 1 (.leaf (-25068214352448))
(.leaf (38949341741280))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (29528389))
(.leaf (53916697)))
(.node 1 (.leaf (15210782))
(.leaf (-63843262))))
(.node 2 (.node 1 (.leaf (277006669))
(.leaf (-6016139)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (28449684))
(.leaf (8128877))))))
(.node 4 (.node 2 (.node 1 (.leaf (-31946035))
(.leaf (149653615)))
(.node 1 (.leaf (46023542))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (13913795)))
(.node 1 (.leaf (5696405))
(.node 1 (.leaf (7382681))
(.leaf (68130156)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (32328579))))
(.node 2 (.node 1 (.leaf (-80960929))
(.leaf (95970477)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (75384556)))
(.node 1 (.leaf (189775580))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (170543642))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (395009710004684530800))
(.leaf (4280053839984)))
(.node 1 (.leaf (-10269448334208))
(.leaf (3446491807008))))
(.node 2 (.node 1 (.leaf (4401356990544))
(.leaf (-5174443854576)))
(.node 1 (.leaf (-748606512465915252336))
(.node 1 (.leaf (409986963431839568016))
(.leaf (18289078820064))))))
(.node 4 (.node 2 (.node 1 (.leaf (776407476528))
(.leaf (-8152932673152)))
(.node 1 (.leaf (19043626432608))
(.leaf (5528568678038678448))))
(.node 2 (.node 1 (.leaf (-239527296170463108816))
(.leaf (838304776720611878544)))
(.node 1 (.leaf (-19617733376496))
(.node 1 (.leaf (-29514408960384))
(.leaf (4684054652496)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (39352354318386793728))
(.leaf (447341123531713978944)))
(.node 1 (.leaf (-147712146804493626096))
(.leaf (360795340572707082384))))
(.node 2 (.node 1 (.leaf (9981585001584))
(.leaf (-2614681765152)))
(.node 1 (.leaf (76362251798569088880))
(.node 1 (.leaf (-310017423213879595344))
(.leaf (-240736971104337537072))))))
(.node 4 (.node 2 (.node 1 (.leaf (387484210420993149408))
(.leaf (154726667448412182192)))
(.node 1 (.leaf (-23384800507392))
(.leaf (106629242444663428512))))
(.node 2 (.node 1 (.leaf (78291839254873555296))
(.leaf (16114159978640773776)))
(.node 1 (.leaf (-634211510048126212176))
(.node 1 (.leaf (-172174942188067552848))
(.leaf (68393071388196857376))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (11664000375795516647744881200))
(.leaf (126383094727991305776)))
(.node 1 (.leaf (-303240265227895830912))
(.leaf (101769350762645150112))))
(.node 2 (.node 1 (.leaf (129964981344652553616))
(.leaf (-152792990996579558064)))
(.node 1 (.leaf (126383094727991305776))
(.node 1 (.leaf (11663999784521757282855519792))
(.leaf (-33376221110733811200))))))
(.node 4 (.node 2 (.node 1 (.leaf (207912001833891829728))
(.leaf (5358273023543029200)))
(.node 1 (.leaf (262796232771058640400))
(.leaf (-303240265227895830912))))
(.node 2 (.node 1 (.leaf (-33376221110733811200))
(.leaf (11664000803274698252330471952)))
(.node 1 (.leaf (-214221964145461903008))
(.node 1 (.leaf (-409983541022939062176))
(.leaf (141268935665049565104)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (101769350762645150112))
(.leaf (207912001833891829728)))
(.node 1 (.leaf (-214221964145461903008))
(.leaf (11664000313947691827081608880))))
(.node 2 (.node 1 (.leaf (134021317521272487408))
(.leaf (-335861655492859244496)))
(.node 1 (.leaf (129964981344652553616))
(.node 1 (.leaf (5358273023543029200))
(.leaf (-409983541022939062176))))))
(.node 4 (.node 2 (.node 1 (.leaf (134021317521272487408))
(.leaf (11664000100033736022418899168)))
(.node 1 (.leaf (-99992775100588159392))
(.leaf (-152792990996579558064))))
(.node 2 (.node 1 (.leaf (262796232771058640400))
(.leaf (141268935665049565104)))
(.node 1 (.leaf (-335861655492859244496))
(.node 1 (.leaf (-99992775100588159392))
(.leaf (11664000020023440807754827504))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2870510443080774307938759199846254591436593156929066654041755983110342862238272652779225830399700110633377692930081491982464))
(.node 1 (.leaf (21959442416235167730328451444872376909756568754169417636334855177450273170351174884709409778541230568505558685780693542866611))
(.leaf (32507281544977979099336196682967916149759116001482038062839425901077965006068534255593147159184052469950893045536705485780829))))
(.node 1 (.leaf (45790872926297623752091679782452502648586939167800904361669222114318546068429177272586731713025398414553374816625984690389135))
(.node 1 (.leaf (90548570143028764983371131083075837493239272430552364985565270123313346280749329196022647596581620180251003134283186832855496))
(.leaf (81372339529061570993623909971086080520757665368929145673541478234265830141733322118718041710514906112376490163776526686970906)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 65171359836864 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 277006669 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 108317407815660480276096 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (216634815631320960552193 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 216634815631320960552193 108317407815660480276096 (List.ofFn fun j : Fin 6 => K i j) =
      108317407815660480276096 * geometricEncoding 216634815631320960552193 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    65171359836864 277006669 108317407815660480276096 216634815631320960552193 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-869422225132337853560535636417117096701743621278674755874445118463138787703922844685166851295449606624592694197748205322898077612272561467956927407033607782079712288))
(.node 1 (.leaf (3199754897907525684344837492275868918573400553738710833562007921673205064656120033246750769527702230476377823492653078503400435267081044902575449783832623035663362576))
(.leaf (787025878155605349516259840628676090393111895703940638426111077324042745070007009912737476317064443293603899897180906243572052917186787324945760332522468638287559248))))
(.node 1 (.leaf (-439324979101096936509895382175614058292948773656994320244099768627039795622641259600855063339863452673895754682635092104835694886082355457016197399758060222442418128))
(.node 1 (.leaf (-3929169175047227103889323766042803051356750871401639883428831242984657456010126750833142292758372775385899875448354754647624057724736558379882775938142811686163956608))
(.leaf (11491564693928516144659516822391218758756519669422992279729522249093024261673577187491464099720702723548594789976201930849345828377432886113043401990640990075488426615045392)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 277006669 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 838304776720611878544 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 1393296082836992640703836059616 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (2786592165673985281407672119233 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 2786592165673985281407672119233 1393296082836992640703836059616 (List.ofFn fun j : Fin 6 => B i j) =
      1393296082836992640703836059616 * geometricEncoding 2786592165673985281407672119233 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    277006669 838304776720611878544 1393296082836992640703836059616 2786592165673985281407672119233 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (13377286177200))
(.leaf (-25352094639024)))
(.node 1 (.leaf (187228930032))
(.leaf (1332695607552))))
(.node 2 (.node 1 (.leaf (2586062239920))
(.leaf (3611075512608)))
(.node 1 (.leaf (-25352094639024))
(.node 1 (.leaf (62457219855216))
(.leaf (-8774159377680))))))
(.node 4 (.node 2 (.node 1 (.leaf (13198268854800))
(.leaf (-15798043922976)))
(.node 1 (.leaf (-4091624532720))
(.leaf (187228930032))))
(.node 2 (.node 1 (.leaf (-8774159377680))
(.leaf (65171359836864)))
(.node 1 (.leaf (-19784005247808))
(.node 1 (.leaf (-10899445060368))
(.leaf (-399086652672)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1332695607552))
(.leaf (13198268854800)))
(.node 1 (.leaf (-19784005247808))
(.leaf (30320201843712))))
(.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (-16459321992480)))
(.node 1 (.leaf (2586062239920))
(.node 1 (.leaf (-15798043922976))
(.leaf (-10899445060368))))))
(.node 4 (.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (28633455920448)))
(.node 1 (.leaf (-25068214352448))
(.leaf (3611075512608))))
(.node 2 (.node 1 (.leaf (-4091624532720))
(.leaf (-399086652672)))
(.node 1 (.leaf (-16459321992480))
(.node 1 (.leaf (-25068214352448))
(.leaf (38949341741280))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (13377286177200))
(.leaf (-25352094639024)))
(.node 1 (.leaf (187228930032))
(.leaf (1332695607552))))
(.node 2 (.node 1 (.leaf (2586062239920))
(.leaf (3611075512608)))
(.node 1 (.leaf (-25352094639024))
(.node 1 (.leaf (62457219855216))
(.leaf (-8774159377680))))))
(.node 4 (.node 2 (.node 1 (.leaf (13198268854800))
(.leaf (-15798043922976)))
(.node 1 (.leaf (-4091624532720))
(.leaf (187228930032))))
(.node 2 (.node 1 (.leaf (-8774159377680))
(.leaf (65171359836864)))
(.node 1 (.leaf (-19784005247808))
(.node 1 (.leaf (-10899445060368))
(.leaf (-399086652672)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1332695607552))
(.leaf (13198268854800)))
(.node 1 (.leaf (-19784005247808))
(.leaf (30320201843712))))
(.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (-16459321992480)))
(.node 1 (.leaf (2586062239920))
(.node 1 (.leaf (-15798043922976))
(.leaf (-10899445060368))))))
(.node 4 (.node 2 (.node 1 (.leaf (3402241985232))
(.leaf (28633455920448)))
(.node 1 (.leaf (-25068214352448))
(.leaf (3611075512608))))
(.node 2 (.node 1 (.leaf (-4091624532720))
(.leaf (-399086652672)))
(.node 1 (.leaf (-16459321992480))
(.node 1 (.leaf (-25068214352448))
(.leaf (38949341741280))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1056395919238232602389028879580672240407693925898468713730059013094105857521168515651776))
(.node 1 (.leaf (-1196977311698128650591557003875910012307254845393443707732351579285021515415045667229776))
(.leaf (-116750123289633650640690208497892784210701630929786630718070760693903412594859049569712))))
(.node 1 (.leaf (-4815064244869878041515959776255088824793762293741076429718537842188649940352340527246976))
(.node 1 (.leaf (-7333537958996994465248024726794696626032323828035088573550151628153925113101097382897328))
(.leaf (11394368666299909042534205988188926511774685467966078713821607919974101960758917666980528)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 65171359836864 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 391028159021184 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (782056318042369 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 782056318042369 391028159021184 (List.ofFn fun j : Fin 6 => NG i j) =
      391028159021184 * geometricEncoding 782056318042369 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 65171359836864 391028159021184 782056318042369 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (782056318042369))
(.leaf (611612084589987012276479132161))))
(.node 1 (.leaf (478315094944663174900757227824809187548529409))
(.node 1 (.leaf (374069342016509428570786647061927605252483696384499704529921))
(.leaf (292543292309963002872250895543932280395681670656434232928872806072106222849)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 65171359836864 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 391028159021184 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (782056318042369 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 782056318042369 391028159021184 (List.ofFn fun j : Fin 6 => H i j) =
      391028159021184 * geometricEncoding 782056318042369 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    65171359836864 1 391028159021184 782056318042369 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Upper.Block09
