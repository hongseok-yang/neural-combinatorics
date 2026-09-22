import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4708510953984))
(.leaf (-5012156187936)))
(.node 1 (.leaf (36355521600))
(.leaf (112954891392))))
(.node 2 (.node 1 (.leaf (-703688466816))
(.leaf (-316668797568)))
(.node 1 (.leaf (-5012156187936))
(.node 1 (.leaf (18431198688096))
(.leaf (-2626061451264))))))
(.node 4 (.node 2 (.node 1 (.leaf (4758954892416))
(.leaf (-6853091147712)))
(.node 1 (.leaf (-459295202016))
(.leaf (36355521600))))
(.node 2 (.node 1 (.leaf (-2626061451264))
(.leaf (25206807804480)))
(.node 1 (.leaf (-2047561273440))
(.node 1 (.leaf (-1723315953600))
(.leaf (-166854935232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (112954891392))
(.leaf (4758954892416)))
(.node 1 (.leaf (-2047561273440))
(.leaf (14374365732864))))
(.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (-5208120625824)))
(.node 1 (.leaf (-703688466816))
(.node 1 (.leaf (-6853091147712))
(.leaf (-1723315953600))))))
(.node 4 (.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (15540404638752)))
(.node 1 (.leaf (-5377210181280))
(.leaf (-316668797568))))
(.node 2 (.node 1 (.leaf (-459295202016))
(.leaf (-166854935232)))
(.node 1 (.leaf (-5208120625824))
(.node 1 (.leaf (-5377210181280))
(.leaf (14780553141024))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (40638375))
(.leaf (25938978)))
(.node 1 (.leaf (3594942))
(.leaf (-10265815))))
(.node 2 (.node 1 (.leaf (29083433))
(.leaf (11065977)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (24367549))
(.leaf (3505865))))))
(.node 4 (.node 2 (.node 1 (.leaf (-9074003))
(.leaf (22823824)))
(.node 1 (.leaf (7131623))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (17744781)))
(.node 1 (.leaf (1094984))
(.node 1 (.leaf (3398252))
(.leaf (2184492)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (24935387))))
(.node 2 (.node 1 (.leaf (-12361489))
(.leaf (5457962)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (30226935)))
(.node 1 (.leaf (12255623))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (26624812))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (191346233839609536000))
(.leaf (542966299488)))
(.node 1 (.leaf (1601051673888))
(.leaf (551592713952))))
(.node 2 (.node 1 (.leaf (1195850511360))
(.leaf (-337677971040)))
(.node 1 (.leaf (-203685882723913644000))
(.node 1 (.leaf (319112928069479227296))
(.leaf (-1747151189856))))))
(.node 4 (.node 2 (.node 1 (.leaf (2672862504768))
(.leaf (-1515181445856)))
(.node 1 (.leaf (-9780959780928))
(.leaf (1477429320101400000))))
(.node 2 (.node 1 (.leaf (-63047656015725707136))
(.leaf (438213363261284502720)))
(.node 1 (.leaf (-11094478707168))
(.node 1 (.leaf (10879513644384))
(.leaf (-4427113392576)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4590303234472368000))
(.leaf (118894000972546085760)))
(.node 1 (.leaf (-19243206704203357536))
(.leaf (311845980606043207680))))
(.node 2 (.node 1 (.leaf (-106773507936))
(.leaf (-7204813430112)))
(.node 1 (.leaf (-28596755797643664000))
(.node 1 (.leaf (-185245994002932351936))
(.leaf (-57135595811283937152))))))
(.node 4 (.node 2 (.node 1 (.leaf (127531310413488276960))
(.leaf (257254003485630982656)))
(.node 1 (.leaf (8424452591712))
(.leaf (-12868905346367472000))))
(.node 2 (.node 1 (.leaf (-19405963313992584288))
(.leaf (-5709437218343549088)))
(.node 1 (.leaf (-122630697498919382208))
(.node 1 (.leaf (-118416160533571419456))
(.leaf (292058400266913621312))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (7776000005611742177544000000))
(.leaf (22065268090955652000)))
(.node 1 (.leaf (65064138317838252000))
(.leaf (22415831556849108000))))
(.node 2 (.node 1 (.leaf (48597421524589440000))
(.leaf (-13722684016362660000)))
(.node 1 (.leaf (22065268090955652000))
(.node 1 (.leaf (7775999925350501372778060768))
(.leaf (-1044148083380376480))))))
(.node 4 (.node 2 (.node 1 (.leaf (79438859327358194688))
(.leaf (-5902118020331136864)))
(.node 1 (.leaf (-247097038190683502592))
(.leaf (65064138317838252000))))
(.node 2 (.node 1 (.leaf (-1044148083380376480))
(.leaf (7776000161975350979866073376)))
(.node 1 (.leaf (-185515456048300795104))
(.node 1 (.leaf (192041578635439555584))
(.leaf (-114062814896357768256)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22415831556849108000))
(.leaf (79438859327358194688)))
(.node 1 (.leaf (-185515456048300795104))
(.leaf (7776000168741794105901029664))))
(.node 2 (.node 1 (.leaf (10722835494614961792))
(.leaf (-92283431498404599744)))
(.node 1 (.leaf (48597421524589440000))
(.node 1 (.leaf (-5902118020331136864))
(.leaf (192041578635439555584))))))
(.node 4 (.node 2 (.node 1 (.leaf (10722835494614961792))
(.leaf (7776000080338353268497958368)))
(.node 1 (.leaf (95603416685796733344))
(.leaf (-13722684016362660000))))
(.node 2 (.node 1 (.leaf (-247097038190683502592))
(.leaf (-114062814896357768256)))
(.node 1 (.leaf (-92283431498404599744))
(.node 1 (.leaf (95603416685796733344))
(.leaf (7775999980888793828573914560))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3105752985200451257345645529998793607110865907326199611536589055344442507238459946096462282458447160312979693947415890))
(.node 1 (.leaf (2001545766955253729270009833223540398292156368257238693174775586832488780947553446201748869812543559636225020014994858))
(.leaf (613094763358581367741945597789159924835121713914051213546709584791527384906268151445624631150776323817873446481702509))))
(.node 1 (.leaf (1531819718639450031880421105387045531252773558023858424641078940580681737706916895842068301407583901074253900503631860))
(.node 1 (.leaf (3439636438584800062380728900947348968606860123863139657306625821308427869797242459517927049902413215724387955721682558))
(.leaf (7472461703959876027392226786092770726847589700333703790516820831390355548491237819340438709286008969099412670129024812)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 25206807804480 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 40638375 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 6146182248668309520000 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (12292364497336619040001 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 12292364497336619040001 6146182248668309520000 (List.ofFn fun j : Fin 6 => K i j) =
      6146182248668309520000 * geometricEncoding 12292364497336619040001 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    25206807804480 40638375 6146182248668309520000 12292364497336619040001 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-150493836476023272515727957120807647262933710917325004582721975903216158511393909927729516510591855708827149885392774454671055480121975108274062347362805636352))
(.node 1 (.leaf (-4359106273104130302138954012059856741201755150266288203442394886472066113644114393353785014547792752613339576272736212538855654162425394673164468584177058888576))
(.leaf (-1973043361138365262277353485044701989859155064126099646785089438294324334598884312123417149278925996440615586022749444535538298320065911142232416002390386899776))))
(.node 1 (.leaf (-3210988300042504473877809160595649137433122922230464572529940706105581822017732360227784243348184782498981668795385820956265752821888114157459361935074667194144))
(.node 1 (.leaf (3754548118233434464586959492504604911271186674755819041075615127472094331208363621121977939815046460427075285250505246964288793615009804371734983934765917338240))
(.leaf (130162441440431873937792451859606114189324209074613978616348721935434036418127128893748432044666507871220058299017828498763378874011015612112655608807352390693250094272)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 40638375 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 438213363261284502720 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 106849673917339815619343280000 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (213699347834679631238686560001 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 213699347834679631238686560001 106849673917339815619343280000 (List.ofFn fun j : Fin 6 => B i j) =
      106849673917339815619343280000 * geometricEncoding 213699347834679631238686560001 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    40638375 438213363261284502720 106849673917339815619343280000 213699347834679631238686560001 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4708510953984))
(.leaf (-5012156187936)))
(.node 1 (.leaf (36355521600))
(.leaf (112954891392))))
(.node 2 (.node 1 (.leaf (-703688466816))
(.leaf (-316668797568)))
(.node 1 (.leaf (-5012156187936))
(.node 1 (.leaf (18431198688096))
(.leaf (-2626061451264))))))
(.node 4 (.node 2 (.node 1 (.leaf (4758954892416))
(.leaf (-6853091147712)))
(.node 1 (.leaf (-459295202016))
(.leaf (36355521600))))
(.node 2 (.node 1 (.leaf (-2626061451264))
(.leaf (25206807804480)))
(.node 1 (.leaf (-2047561273440))
(.node 1 (.leaf (-1723315953600))
(.leaf (-166854935232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (112954891392))
(.leaf (4758954892416)))
(.node 1 (.leaf (-2047561273440))
(.leaf (14374365732864))))
(.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (-5208120625824)))
(.node 1 (.leaf (-703688466816))
(.node 1 (.leaf (-6853091147712))
(.leaf (-1723315953600))))))
(.node 4 (.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (15540404638752)))
(.node 1 (.leaf (-5377210181280))
(.leaf (-316668797568))))
(.node 2 (.node 1 (.leaf (-459295202016))
(.leaf (-166854935232)))
(.node 1 (.leaf (-5208120625824))
(.node 1 (.leaf (-5377210181280))
(.leaf (14780553141024))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4708510953984))
(.leaf (-5012156187936)))
(.node 1 (.leaf (36355521600))
(.leaf (112954891392))))
(.node 2 (.node 1 (.leaf (-703688466816))
(.leaf (-316668797568)))
(.node 1 (.leaf (-5012156187936))
(.node 1 (.leaf (18431198688096))
(.leaf (-2626061451264))))))
(.node 4 (.node 2 (.node 1 (.leaf (4758954892416))
(.leaf (-6853091147712)))
(.node 1 (.leaf (-459295202016))
(.leaf (36355521600))))
(.node 2 (.node 1 (.leaf (-2626061451264))
(.leaf (25206807804480)))
(.node 1 (.leaf (-2047561273440))
(.node 1 (.leaf (-1723315953600))
(.leaf (-166854935232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (112954891392))
(.leaf (4758954892416)))
(.node 1 (.leaf (-2047561273440))
(.leaf (14374365732864))))
(.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (-5208120625824)))
(.node 1 (.leaf (-703688466816))
(.node 1 (.leaf (-6853091147712))
(.leaf (-1723315953600))))))
(.node 4 (.node 2 (.node 1 (.leaf (2406596238432))
(.leaf (15540404638752)))
(.node 1 (.leaf (-5377210181280))
(.leaf (-316668797568))))
(.node 2 (.node 1 (.leaf (-459295202016))
(.leaf (-166854935232)))
(.node 1 (.leaf (-5208120625824))
(.node 1 (.leaf (-5377210181280))
(.leaf (14780553141024))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-801864068698431096572381599582451093146043478601487481930415080029279545782979173984))
(.node 1 (.leaf (-1163020550969022064106608798928491547426532370129021175643629253165144784467598266336))
(.leaf (-422507611343734575232734310371513140993462172463526248999290393339916365780079795296))))
(.node 1 (.leaf (-13187926399343578638206988742736838713120272600815238514863600755864154268888517674400))
(.node 1 (.leaf (-13616092483130870790945529574623042734965781993737877496870538649161943444949868361504))
(.leaf (37427099134166308880588789613582400050460929733641146697993845052558669909356447861184)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 25206807804480 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 151240846826880 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (302481693653761 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 302481693653761 151240846826880 (List.ofFn fun j : Fin 6 => NG i j) =
      151240846826880 * geometricEncoding 302481693653761 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 25206807804480 151240846826880 302481693653761 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (302481693653761))
(.leaf (91495174995647717622149445121))))
(.node 1 (.leaf (27675615493830766358263345979584713244750081))
(.node 1 (.leaf (8371367047484199324397237076894130830150809578368190704641))
(.leaf (2532185282720305294723450110058569983894896192235649922450239360469804801)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 25206807804480 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 151240846826880 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (302481693653761 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 302481693653761 151240846826880 (List.ofFn fun j : Fin 6 => H i j) =
      151240846826880 * geometricEncoding 302481693653761 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    25206807804480 1 151240846826880 302481693653761 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Upper.Block09
