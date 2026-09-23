import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3026835806976))
(.leaf (-3594220169472)))
(.node 1 (.leaf (-2390974806528))
(.leaf (3888324290304))))
(.node 2 (.node 1 (.leaf (2474915482368))
(.leaf (-3376945976832)))
(.node 1 (.leaf (-3594220169472))
(.node 1 (.leaf (14635109320704))
(.leaf (-10698734016000))))))
(.node 4 (.node 2 (.node 1 (.leaf (15632963774208))
(.leaf (-1021331006208)))
(.node 1 (.leaf (-7232978343168))
(.leaf (-2390974806528))))
(.node 2 (.node 1 (.leaf (-10698734016000))
(.leaf (71841092251392)))
(.node 1 (.leaf (-39021702234624))
(.node 1 (.leaf (-6198280206336))
(.leaf (14407696965888)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3888324290304))
(.leaf (15632963774208)))
(.node 1 (.leaf (-39021702234624))
(.leaf (61282899730944))))
(.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (-34080817837824)))
(.node 1 (.leaf (2474915482368))
(.node 1 (.leaf (-1021331006208))
(.leaf (-6198280206336))))))
(.node 4 (.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (8411233446144)))
(.node 1 (.leaf (-12249711399168))
(.leaf (-3376945976832))))
(.node 2 (.node 1 (.leaf (-7232978343168))
(.leaf (14407696965888)))
(.node 1 (.leaf (-34080817837824))
(.node 1 (.leaf (-12249711399168))
(.leaf (33825067748352))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (248307202))
(.leaf (159319860)))
(.node 1 (.leaf (139849093))
(.leaf (-354474576))))
(.node 2 (.node 1 (.leaf (-7093938))
(.leaf (115253085)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (134169593))
(.leaf (78024853))))))
(.node 4 (.node 2 (.node 1 (.leaf (-191357881))
(.leaf (71116580)))
(.node 1 (.leaf (93015876))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (59750417)))
(.node 1 (.leaf (20282235))
(.node 1 (.leaf (-3899264))
(.leaf (21314753)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (111525754))))
(.node 2 (.node 1 (.leaf (-57868761))
(.leaf (37651658)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (199105910)))
(.node 1 (.leaf (169570881))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (156841432))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (751585130143622641152))
(.leaf (-280045921536)))
(.node 1 (.leaf (166286462976))
(.leaf (1545775425792))))
(.node 2 (.node 1 (.leaf (461137639680))
(.leaf (1836105822720)))
(.node 1 (.leaf (-892470753653558137344))
(.node 1 (.leaf (1390956006859906839552))
(.leaf (3815809295616))))))
(.node 4 (.node 2 (.node 1 (.leaf (-2530804331520))
(.leaf (2475779551488)))
(.node 1 (.leaf (4226543898624))
(.leaf (-593696264261459014656))))
(.node 2 (.node 1 (.leaf (-1816374559981543534080))
(.leaf (3123392412792849903360)))
(.node 1 (.leaf (3074560042752))
(.node 1 (.leaf (8264059706880))
(.leaf (-1047460605696)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (965498924994021969408))
(.leaf (2716955668535063894784)))
(.node 1 (.leaf (-568024654842828352512))
(.leaf (1673371339239040982784))))
(.node 2 (.node 1 (.leaf (6925446812160))
(.leaf (19842680719872)))
(.node 1 (.leaf (614539338613278414336))
(.node 1 (.leaf (257271622741494395136))
(.leaf (-103924343174321037312))))))
(.node 4 (.node 2 (.node 1 (.leaf (486353853586606595328))
(.leaf (937310198733391995648)))
(.node 1 (.leaf (4050222663168))
(.leaf (-838520006812310744064))))
(.node 2 (.node 1 (.leaf (-1508460320737102374144))
(.leaf (-175749002226378192384)))
(.node 1 (.leaf (-927539708249095589376))
(.node 1 (.leaf (-1013383484920319254272))
(.leaf (1189889655345559664640))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (186624000730768796168303176704))
(.leaf (-69537419208115702272)))
(.node 1 (.leaf (41290126352047153152))
(.leaf (383827170898770153984))))
(.node 2 (.node 1 (.leaf (114503797045824975360))
(.leaf (455918299415511229440)))
(.node 1 (.leaf (-69537419208115702272))
(.node 1 (.leaf (186624001276682031667921637376))
(.leaf (538458316159646907648))))))
(.node 4 (.node 2 (.node 1 (.leaf (-93284262694053642240))
(.leaf (405642718975415549184)))
(.node 1 (.leaf (859601797295950559232))
(.leaf (41290126352047153152))))
(.node 2 (.node 1 (.leaf (538458316159646907648))
(.leaf (186623999439991886736013326336)))
(.node 1 (.leaf (202415899986058567680))
(.node 1 (.leaf (751443029821643710464))
(.leaf (523966992366186720000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (383827170898770153984))
(.leaf (-93284262694053642240)))
(.node 1 (.leaf (202415899986058567680))
(.leaf (186624000329334046607042774784))))
(.node 2 (.node 1 (.leaf (302757780442928792832))
(.leaf (732089769113048350464)))
(.node 1 (.leaf (114503797045824975360))
(.node 1 (.leaf (405642718975415549184))
(.leaf (751443029821643710464))))))
(.node 4 (.node 2 (.node 1 (.leaf (302757780442928792832))
(.leaf (186623999810899776490628620800)))
(.node 1 (.leaf (-50211627271493073408))
(.leaf (455918299415511229440))))
(.node 2 (.node 1 (.leaf (859601797295950559232))
(.leaf (523966992366186720000)))
(.node 1 (.leaf (732089769113048350464))
(.node 1 (.leaf (-50211627271493073408))
(.leaf (186623999482719865701224736000))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (307148840959300941329149067148798632731302791261843856801629850176298591357491889353917611068638286093675938871537747958503702))
(.node 1 (.leaf (247886800637172162509623773187320900039038166148495184990034056959255419672054176993682074113658845588197777315331297293199165))
(.leaf (56803700129014183152653149943354406176732877297967180892565689068175214718811463439735758893061062225116228473682048252702925))))
(.node 1 (.leaf (100341462572528891196301862745666857656344591741980226111637627436860239395602588225337341306280361441644882613075111939424875))
(.node 1 (.leaf (451905470119064888938229539875198236969653320727767118396297052015178255453476220224311734598477303819306615528759527617384375))
(.leaf (417981558178655377051397216274637333547537440953129014060200407617109939643238076516120612514157289399988645045609160941975000)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 71841092251392 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 354474576 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 152795044291134387658752 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (305590088582268775317505 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 305590088582268775317505 152795044291134387658752 (List.ofFn fun j : Fin 6 => K i j) =
      152795044291134387658752 * geometricEncoding 305590088582268775317505 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    71841092251392 354474576 152795044291134387658752 305590088582268775317505 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (760084981858202886387343614770085127774792527451168271936407813526658414790345631747898356307538356240912424184080775826259733958838810167399253881200482851326222087424))
(.node 1 (.leaf (1749644548128216253068238088911423250209070858442813832203447230502351871590689470136111737796907390036392620993699698287785362986019246256543442570066177036355676148736))
(.leaf (-433612848249780843089936136028607183258336803166726879235636752865663410596041465242858785203696392563487399565551130102035301497718052253694709443200693697553964555520))))
(.node 1 (.leaf (8214190831680617540723967596043464778429905974113878758276060649759483291456077092077202191304084158548198508377196066777930463122299960350357281718443043141539117070336))
(.node 1 (.leaf (1676653590093861635270543048042969800834481348462593793720527880669757628685482599021092872329175396203525954603899340371988442807552064241882172595418487413024729771264))
(.leaf (492573601099305271981628609950277858566048710707136315131201277326134603294141199922551878877205104316461287683095708828841954798619137438663701110470356244590877734835252003840)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 354474576 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 3123392412792849903360 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 6642979207238174671951061852160 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (13285958414476349343902123704321 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 13285958414476349343902123704321 6642979207238174671951061852160 (List.ofFn fun j : Fin 6 => B i j) =
      6642979207238174671951061852160 * geometricEncoding 13285958414476349343902123704321 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    354474576 3123392412792849903360 6642979207238174671951061852160 13285958414476349343902123704321 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3026835806976))
(.leaf (-3594220169472)))
(.node 1 (.leaf (-2390974806528))
(.leaf (3888324290304))))
(.node 2 (.node 1 (.leaf (2474915482368))
(.leaf (-3376945976832)))
(.node 1 (.leaf (-3594220169472))
(.node 1 (.leaf (14635109320704))
(.leaf (-10698734016000))))))
(.node 4 (.node 2 (.node 1 (.leaf (15632963774208))
(.leaf (-1021331006208)))
(.node 1 (.leaf (-7232978343168))
(.leaf (-2390974806528))))
(.node 2 (.node 1 (.leaf (-10698734016000))
(.leaf (71841092251392)))
(.node 1 (.leaf (-39021702234624))
(.node 1 (.leaf (-6198280206336))
(.leaf (14407696965888)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3888324290304))
(.leaf (15632963774208)))
(.node 1 (.leaf (-39021702234624))
(.leaf (61282899730944))))
(.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (-34080817837824)))
(.node 1 (.leaf (2474915482368))
(.node 1 (.leaf (-1021331006208))
(.leaf (-6198280206336))))))
(.node 4 (.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (8411233446144)))
(.node 1 (.leaf (-12249711399168))
(.leaf (-3376945976832))))
(.node 2 (.node 1 (.leaf (-7232978343168))
(.leaf (14407696965888)))
(.node 1 (.leaf (-34080817837824))
(.node 1 (.leaf (-12249711399168))
(.leaf (33825067748352))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3026835806976))
(.leaf (-3594220169472)))
(.node 1 (.leaf (-2390974806528))
(.leaf (3888324290304))))
(.node 2 (.node 1 (.leaf (2474915482368))
(.leaf (-3376945976832)))
(.node 1 (.leaf (-3594220169472))
(.node 1 (.leaf (14635109320704))
(.leaf (-10698734016000))))))
(.node 4 (.node 2 (.node 1 (.leaf (15632963774208))
(.leaf (-1021331006208)))
(.node 1 (.leaf (-7232978343168))
(.leaf (-2390974806528))))
(.node 2 (.node 1 (.leaf (-10698734016000))
(.leaf (71841092251392)))
(.node 1 (.leaf (-39021702234624))
(.node 1 (.leaf (-6198280206336))
(.leaf (14407696965888)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3888324290304))
(.leaf (15632963774208)))
(.node 1 (.leaf (-39021702234624))
(.leaf (61282899730944))))
(.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (-34080817837824)))
(.node 1 (.leaf (2474915482368))
(.node 1 (.leaf (-1021331006208))
(.leaf (-6198280206336))))))
(.node 4 (.node 2 (.node 1 (.leaf (11602017130752))
(.leaf (8411233446144)))
(.node 1 (.leaf (-12249711399168))
(.leaf (-3376945976832))))
(.node 2 (.node 1 (.leaf (-7232978343168))
(.leaf (14407696965888)))
(.node 1 (.leaf (-34080817837824))
(.node 1 (.leaf (-12249711399168))
(.leaf (33825067748352))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-1608033070916726776134536637726280732934895826968430678582252654803078868294869421353984))
(.node 1 (.leaf (-3444197347791108720867280409012883861555067390822865074892055269948657813654985510193152))
(.leaf (6860652600261329344426486816343091399468170794555217398946246560610106960184796511094272))))
(.node 1 (.leaf (-16228593096571208693915755195187124820836925032559802057252869101846276665977151134150656))
(.node 1 (.leaf (-5833063713245096039515115617102495317085556430012798037401049845298830913247751398268672))
(.leaf (16106810099572631332518723750853290400357615199845270864368200354405356693401978148796928)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 71841092251392 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 431046553508352 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (862093107016705 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 862093107016705 431046553508352 (List.ofFn fun j : Fin 6 => NG i j) =
      431046553508352 * geometricEncoding 862093107016705 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 71841092251392 431046553508352 862093107016705 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (862093107016705))
(.leaf (743204525165715979705149057025))))
(.node 1 (.leaf (640711498248987010416454179909776941672602625))
(.node 1 (.leaf (552352966226797356990811675890563450398884597573246701850625))
(.leaf (476179684824352856448415657968904345980766674495278276478369042296289690625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 71841092251392 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 431046553508352 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (862093107016705 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 862093107016705 431046553508352 (List.ofFn fun j : Fin 6 => H i j) =
      431046553508352 * geometricEncoding 862093107016705 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    71841092251392 1 431046553508352 862093107016705 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas127.Lower.Block09
