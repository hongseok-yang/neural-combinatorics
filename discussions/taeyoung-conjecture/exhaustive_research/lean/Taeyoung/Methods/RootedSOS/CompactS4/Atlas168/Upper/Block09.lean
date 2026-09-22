import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (18946231006176))
(.leaf (-43918171519104)))
(.node 1 (.leaf (-1573016044608))
(.leaf (796451162400))))
(.node 2 (.node 1 (.leaf (8544084539904))
(.leaf (4724716604544)))
(.node 1 (.leaf (-43918171519104))
(.node 1 (.leaf (110240769718944))
(.leaf (-14343799241088))))))
(.node 4 (.node 2 (.node 1 (.leaf (17026888500000))
(.leaf (-24576605282592)))
(.node 1 (.leaf (-8684161365024))
(.leaf (-1573016044608))))
(.node 2 (.node 1 (.leaf (-14343799241088))
(.leaf (121561274273472)))
(.node 1 (.leaf (-26435127983616))
(.node 1 (.leaf (-13055429819520))
(.leaf (4801538554560)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (796451162400))
(.leaf (17026888500000)))
(.node 1 (.leaf (-26435127983616))
(.leaf (62225577469152))))
(.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (-20797538216832)))
(.node 1 (.leaf (8544084539904))
(.node 1 (.leaf (-24576605282592))
(.leaf (-13055429819520))))))
(.node 4 (.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (42997544106336)))
(.node 1 (.leaf (-43166730869568))
(.leaf (4724716604544))))
(.node 2 (.node 1 (.leaf (-8684161365024))
(.leaf (4801538554560)))
(.node 1 (.leaf (-20797538216832))
(.node 1 (.leaf (-43166730869568))
(.leaf (59838904835712))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (35089513))
(.leaf (121892529)))
(.node 1 (.leaf (84225496))
(.leaf (-220548209))))
(.node 2 (.node 1 (.leaf (453804437))
(.leaf (-91268821)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (52584248))
(.leaf (35734530))))))
(.node 4 (.node 2 (.node 1 (.leaf (-94267448))
(.leaf (203843809)))
(.node 1 (.leaf (54306042))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (16757925)))
(.node 1 (.leaf (-6072128))
(.node 1 (.leaf (23199561))
(.leaf (44899846)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (36351009))))
(.node 2 (.node 1 (.leaf (-56114608))
(.leaf (69061014)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (51000138)))
(.node 1 (.leaf (330937049))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (275634004))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (664814019192215832288))
(.leaf (-10506094214688)))
(.node 1 (.leaf (1231847683776))
(.leaf (-7638791064768))))
(.node 2 (.node 1 (.leaf (-7571144273760))
(.leaf (-7170498704160)))
(.node 1 (.leaf (-1541067250455829556352))
(.node 1 (.leaf (443630979092483220096))
(.leaf (1237878438336))))))
(.node 4 (.node 2 (.node 1 (.leaf (6236354045088))
(.leaf (26218675193184)))
(.node 1 (.leaf (18506394816480))
(.leaf (-55196366946480995904))))
(.node 2 (.node 1 (.leaf (-945996800390429115456))
(.leaf (1392057736311569971392)))
(.node 1 (.leaf (27968054953536))
(.node 1 (.leaf (-13819236035328))
(.leaf (-14291085286080)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (27947083416899911200))
(.leaf (992427573962273709600)))
(.node 1 (.leaf (232531459987983393600))
(.leaf (641742803725403687616))))
(.node 2 (.node 1 (.leaf (25406544722112))
(.leaf (23738347148256)))
(.node 1 (.leaf (299807765536060426752))
(.node 1 (.leaf (-250882234619227833600))
(.leaf (-377385594287875805376))))))
(.node 4 (.node 2 (.node 1 (.leaf (706099023104621824512))
(.leaf (457410522747822172704)))
(.node 1 (.leaf (30221917083936))
(.leaf (165788004716462547072))))
(.node 2 (.node 1 (.leaf (119257560845720509824))
(.leaf (168080997635788063104)))
(.node 1 (.leaf (-1008561110861858810112))
(.node 1 (.leaf (-549185112271404745056))
(.leaf (84633923715234938496))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23328000169027506945875595744))
(.leaf (-368653729525519366944)))
(.node 1 (.leaf (43224935313877841088))
(.leaf (-268041458371460577984))))
(.node 2 (.node 1 (.leaf (-265667765418977078880))
(.leaf (-251609307496105474080)))
(.node 1 (.leaf (-368653729525519366944))
(.node 1 (.leaf (23328000144467558840777381856))
(.leaf (215245936313561840832))))))
(.node 4 (.node 2 (.node 1 (.leaf (-603177573664463744448))
(.leaf (455823395637360626592)))
(.node 1 (.leaf (99114633374413586400))
(.leaf (43224935313877841088))))
(.node 2 (.node 1 (.leaf (215245936313561840832))
(.leaf (23327999288767052566394976576)))
(.node 1 (.leaf (48158781751600336512))
(.node 1 (.leaf (67646932468769684160))
(.leaf (-182110424556616392960)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-268041458371460577984))
(.leaf (-603177573664463744448)))
(.node 1 (.leaf (48158781751600336512))
(.leaf (23327999360918280993120465024))))
(.node 2 (.node 1 (.leaf (205700415177130970400))
(.leaf (786580205756683474944)))
(.node 1 (.leaf (-265667765418977078880))
(.node 1 (.leaf (455823395637360626592))
(.leaf (67646932468769684160))))))
(.node 4 (.node 2 (.node 1 (.leaf (205700415177130970400))
(.leaf (23327999945208316629596654784)))
(.node 1 (.leaf (396116875060955663040))
(.leaf (-251609307496105474080))))
(.node 2 (.node 1 (.leaf (99114633374413586400))
(.leaf (-182110424556616392960)))
(.node 1 (.leaf (786580205756683474944))
(.node 1 (.leaf (396116875060955663040))
(.leaf (23327999926591629886577278272))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-11602419916357385062252245081174662173020842160348096121115872076589933874391863893727697765458309240319428229832316143711996863))
(.node 1 (.leaf (6903578860510761283975075576865181808210981148389635816251261476458963012888429586005823724969811677338878247629405632552577757))
(.leaf (5707829483978756231088276430956224312068049231955736955806103745140327234699362334650677502928355394534568943140001334793021108))))
(.node 1 (.leaf (8779283828783503172322103339022898152072651522106281152674991299501080003867805258460950308192001336874478211902736032653249799))
(.node 1 (.leaf (42069904774798612133474026301325800868771394619217215143203900502083298521998656173292506153335838046858481201316440837360312099))
(.leaf (35039583316573478468385162883122889862378099513075281300400746727118283694001978216192566449051581096739105780201769432669293396)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 121561274273472 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 453804437 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 330990273796053269971584 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (661980547592106539943169 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 661980547592106539943169 330990273796053269971584 (List.ofFn fun j : Fin 6 => K i j) =
      330990273796053269971584 * geometricEncoding 661980547592106539943169 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    121561274273472 453804437 330990273796053269971584 661980547592106539943169 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-298474502688226113384333404686864774881478814982054896165602501572628806364068916655197603675344355465885323367442135432193190810434219462314916376250854038298420424640))
(.node 1 (.leaf (770335121348845578265122182499584533393895388124699026275641909711656057226953215028092544272529780299643215402368183149981894974122031000864366749196591814216668244384))
(.leaf (-594871395927188245300953721846078938677523851546824051158241807889110240899792368431978006371989896174223580594305145346760778063857420123858900796278562685676356127040))))
(.node 1 (.leaf (988116956998487932702727020927097213506336861316658289864568154833353748397299383668995299801734813183748883561931623433099965785003815887769610377084912181889129699040))
(.node 1 (.leaf (1257997810763054937977824057913700524063829365680423166586148394376264236914236853312632967490215018469738017219122443176227060265991541903505983531824881125850926563712))
(.leaf (3522916513017801922960041489003309401367186170433147199204362348173819261688202737858294683288521796954406273063493693119372602441797779381783968885331712618232728348449543072)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 453804437 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1541067250455829556352 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 4196058935833474351129674802944 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (8392117871666948702259349605889 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 8392117871666948702259349605889 4196058935833474351129674802944 (List.ofFn fun j : Fin 6 => B i j) =
      4196058935833474351129674802944 * geometricEncoding 8392117871666948702259349605889 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    453804437 1541067250455829556352 4196058935833474351129674802944 8392117871666948702259349605889 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (18946231006176))
(.leaf (-43918171519104)))
(.node 1 (.leaf (-1573016044608))
(.leaf (796451162400))))
(.node 2 (.node 1 (.leaf (8544084539904))
(.leaf (4724716604544)))
(.node 1 (.leaf (-43918171519104))
(.node 1 (.leaf (110240769718944))
(.leaf (-14343799241088))))))
(.node 4 (.node 2 (.node 1 (.leaf (17026888500000))
(.leaf (-24576605282592)))
(.node 1 (.leaf (-8684161365024))
(.leaf (-1573016044608))))
(.node 2 (.node 1 (.leaf (-14343799241088))
(.leaf (121561274273472)))
(.node 1 (.leaf (-26435127983616))
(.node 1 (.leaf (-13055429819520))
(.leaf (4801538554560)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (796451162400))
(.leaf (17026888500000)))
(.node 1 (.leaf (-26435127983616))
(.leaf (62225577469152))))
(.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (-20797538216832)))
(.node 1 (.leaf (8544084539904))
(.node 1 (.leaf (-24576605282592))
(.leaf (-13055429819520))))))
(.node 4 (.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (42997544106336)))
(.node 1 (.leaf (-43166730869568))
(.leaf (4724716604544))))
(.node 2 (.node 1 (.leaf (-8684161365024))
(.leaf (4801538554560)))
(.node 1 (.leaf (-20797538216832))
(.node 1 (.leaf (-43166730869568))
(.leaf (59838904835712))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (18946231006176))
(.leaf (-43918171519104)))
(.node 1 (.leaf (-1573016044608))
(.leaf (796451162400))))
(.node 2 (.node 1 (.leaf (8544084539904))
(.leaf (4724716604544)))
(.node 1 (.leaf (-43918171519104))
(.node 1 (.leaf (110240769718944))
(.leaf (-14343799241088))))))
(.node 4 (.node 2 (.node 1 (.leaf (17026888500000))
(.leaf (-24576605282592)))
(.node 1 (.leaf (-8684161365024))
(.leaf (-1573016044608))))
(.node 2 (.node 1 (.leaf (-14343799241088))
(.leaf (121561274273472)))
(.node 1 (.leaf (-26435127983616))
(.node 1 (.leaf (-13055429819520))
(.leaf (4801538554560)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (796451162400))
(.leaf (17026888500000)))
(.node 1 (.leaf (-26435127983616))
(.leaf (62225577469152))))
(.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (-20797538216832)))
(.node 1 (.leaf (8544084539904))
(.node 1 (.leaf (-24576605282592))
(.leaf (-13055429819520))))))
(.node 4 (.node 2 (.node 1 (.leaf (5348777649408))
(.leaf (42997544106336)))
(.node 1 (.leaf (-43166730869568))
(.leaf (4724716604544))))
(.node 2 (.node 1 (.leaf (-8684161365024))
(.leaf (4801538554560)))
(.node 1 (.leaf (-20797538216832))
(.node 1 (.leaf (-43166730869568))
(.leaf (59838904835712))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (31207445014978978040215335622009483189010276749072259413457891798055438482851749955905216))
(.node 1 (.leaf (-57360157440881618267504662746372785898990695346411326123317543709527086985682612935158144))
(.leaf (31714865243900560520090667756450499119372417909092524981002058951220269097013697461195072))))
(.node 1 (.leaf (-137370785313238642711769689905562788288145384267445199553102930750231961035607789582095200))
(.node 1 (.leaf (-285122578313552068240994350661075015207283065971766295211174287781144332701886664893595776))
(.leaf (395244728672413205001111563864464715364226050136190251555813312906361381772761739259087584)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 121561274273472 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 729367645640832 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1458735291281665 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1458735291281665 729367645640832 (List.ofFn fun j : Fin 6 => NG i j) =
      729367645640832 * geometricEncoding 1458735291281665 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 121561274273472 729367645640832 1458735291281665 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1458735291281665))
(.leaf (2127908650030604032558365172225))))
(.node 1 (.leaf (3104055444423167722250670378820452418709754625))
(.node 1 (.leaf (4527995222875067671212590366481467968008690487953853911450625))
(.leaf (6605146430362649470462096266725235087995338484683464886380937953475615290625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 121561274273472 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 729367645640832 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1458735291281665 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1458735291281665 729367645640832 (List.ofFn fun j : Fin 6 => H i j) =
      729367645640832 * geometricEncoding 1458735291281665 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    121561274273472 1 729367645640832 1458735291281665 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Upper.Block09
