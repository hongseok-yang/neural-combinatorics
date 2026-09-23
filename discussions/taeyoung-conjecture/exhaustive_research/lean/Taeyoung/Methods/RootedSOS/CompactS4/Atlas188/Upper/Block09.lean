import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23584253484384))
(.leaf (-48149790867360)))
(.node 1 (.leaf (-5900208062688))
(.leaf (4122967765248))))
(.node 2 (.node 1 (.leaf (7379576324064))
(.leaf (9767493856224)))
(.node 1 (.leaf (-48149790867360))
(.node 1 (.leaf (115605876805056))
(.leaf (-15247139882688))))))
(.node 4 (.node 2 (.node 1 (.leaf (12935076655104))
(.leaf (-25180394855328)))
(.node 1 (.leaf (-10329124624128))
(.leaf (-5900208062688))))
(.node 2 (.node 1 (.leaf (-15247139882688))
(.leaf (78514487068608)))
(.node 1 (.leaf (-60332721690816))
(.node 1 (.leaf (-9956832022368))
(.leaf (11846690829216)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4122967765248))
(.leaf (12935076655104)))
(.node 1 (.leaf (-60332721690816))
(.leaf (49090567536864))))
(.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (-18103113416160)))
(.node 1 (.leaf (7379576324064))
(.node 1 (.leaf (-25180394855328))
(.leaf (-9956832022368))))))
(.node 4 (.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (35208589539168)))
(.node 1 (.leaf (-41841492407136))
(.leaf (9767493856224))))
(.node 2 (.node 1 (.leaf (-10329124624128))
(.leaf (11846690829216)))
(.node 1 (.leaf (-18103113416160))
(.node 1 (.leaf (-41841492407136))
(.leaf (69334516823904))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (31450510))
(.leaf (74963800)))
(.node 1 (.leaf (90924008))
(.leaf (-7248263))))
(.node 2 (.node 1 (.leaf (700240168))
(.leaf (4619827)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (36718026))
(.leaf (41325135))))))
(.node 4 (.node 2 (.node 1 (.leaf (-4176453))
(.leaf (358877133)))
(.node 1 (.leaf (148243668))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (26198780)))
(.node 1 (.leaf (69985346))
(.node 1 (.leaf (-139659208))
(.leaf (297501331)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (92840313))))
(.node 2 (.node 1 (.leaf (-374099066))
(.leaf (337039460)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (201040982)))
(.node 1 (.leaf (513286882))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (369268071))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (741736800053153835840))
(.leaf (-11609621732160)))
(.node 1 (.leaf (-8315849523168))
(.leaf (-18320797878336))))
(.node 2 (.node 1 (.leaf (-13091489378784))
(.leaf (-26566345394208)))
(.node 1 (.leaf (-1514335479171814353600))
(.node 1 (.leaf (635328297658241571456))
(.leaf (32324371583040))))))
(.node 4 (.node 2 (.node 1 (.leaf (41740046166816))
(.leaf (55730384474112)))
(.node 1 (.leaf (70005736960416))
(.leaf (-185564552677649570880))))
(.node 2 (.node 1 (.leaf (-1002146895807905628288))
(.leaf (890423094413831921856)))
(.node 1 (.leaf (489365009568))
(.node 1 (.leaf (-66742362675072))
(.leaf (-9663168030912)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (129669438930609876480))
(.leaf (784023811894599727104)))
(.node 1 (.leaf (-671223159300243891456))
(.leaf (251270158412151185760))))
(.node 2 (.node 1 (.leaf (52608748434048))
(.leaf (4979906892000)))
(.node 1 (.leaf (232091438975738072640))
(.node 1 (.leaf (-371373309346330859328))
(.leaf (-630459411674903651808))))))
(.node 4 (.node 2 (.node 1 (.leaf (467566008848748903456))
(.leaf (116036040452772131424)))
(.node 1 (.leaf (-30170351613024))
(.leaf (307192663200111474240))))
(.node 2 (.node 1 (.leaf (352943389433232559872))
(.leaf (771616066761995524992)))
(.node 1 (.leaf (-879262219990067470272))
(.node 1 (.leaf (-161291452513307421312))
(.leaf (63173635259958523872))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23328000647439715245624278400))
(.leaf (-365128524383515401600)))
(.node 1 (.leaf (-261537708586890415680))
(.leaf (-576198436880585151360))))
(.node 2 (.node 1 (.leaf (-411734017622339979840))
(.leaf (-835525111483992646080)))
(.node 1 (.leaf (-365128524383515401600))
(.node 1 (.leaf (23328000081649691529706457856))
(.leaf (563499435734862560640))))))
(.node 4 (.node 2 (.node 1 (.leaf (159215472402345988416))
(.leaf (1064921914617152723712)))
(.node 1 (.leaf (578958266999385988416))
(.leaf (-261537708586890415680))))
(.node 2 (.node 1 (.leaf (563499435734862560640))
(.leaf (23327999337165862365650828736)))
(.node 1 (.leaf (71933436119068156512))
(.node 1 (.leaf (-635833499418311853312))
(.leaf (224314716165052823136)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-576198436880585151360))
(.leaf (159215472402345988416)))
(.node 1 (.leaf (71933436119068156512))
(.leaf (23328000147260698962673480128))))
(.node 2 (.node 1 (.leaf (75360553133951249568))
(.leaf (-313759855314859843296)))
(.node 1 (.leaf (-411734017622339979840))
(.node 1 (.leaf (1064921914617152723712))
(.leaf (-635833499418311853312))))))
(.node 4 (.node 2 (.node 1 (.leaf (75360553133951249568))
(.leaf (23327999993492771653814967360)))
(.node 1 (.leaf (-58269226743709963488))
(.leaf (-835525111483992646080))))
(.node 2 (.node 1 (.leaf (578958266999385988416))
(.leaf (224314716165052823136)))
(.node 1 (.leaf (-313759855314859843296))
(.node 1 (.leaf (-58269226743709963488))
(.leaf (23328000003251846526201399744))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3996378380561020081971842598436366736642764577500090156157662916318851744893175323992035680496683926471360785337688682402605730))
(.node 1 (.leaf (128238089835456071141424918460026299423776896555183103494101067435022264205565689387013068736808309040217356048887396699231449717))
(.leaf (257353335394708070476268092386181243679675066150582649218150176973657441879877625837388966235038619187814798520602658114561100297))))
(.node 1 (.leaf (291555768503877029481132921322909667545320111602187465294316452785614448463003216819955158058064343701848508788029616963010567523))
(.node 1 (.leaf (444018487759471384667519424419444448694430586555217575161600038486303157536988503326787693176429010528700108721639192442934613816))
(.leaf (319435107759635108297729315633728441748984948585879118156424427316273919258766796632245183448676769523078834442971298138351398247)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 115605876805056 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 700240168 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 485711271574558300136448 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (971422543149116600272897 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 971422543149116600272897 485711271574558300136448 (List.ofFn fun j : Fin 6 => K i j) =
      485711271574558300136448 * geometricEncoding 971422543149116600272897 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    115605876805056 700240168 485711271574558300136448 971422543149116600272897 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-8863058803015617273744124022811299267967100855511019077993826188124582265520212277329949648703760472699767298149019221806293843245649506178193444731436319052100557238816))
(.node 1 (.leaf (23355299873647080074776933573465667583239149888080163891331981590245957107215750360277918285381219527440396109684185373935803244665552593341204492594111829081817594293440))
(.leaf (-3223824173424549380103490283644447582429887740375123076081640134125197985522666522478454843007842826614442004362792897139455397171759912457221727605813374308758380365728))))
(.node 1 (.leaf (1661395534929751601568265958855563348117317214958679938862777489482731802488509978831113968033429357247396676620513884953000928209086881864014361006268710918041405990336))
(.node 1 (.leaf (-10065426632305538809439806106652861819464861853752831634319116470306806229204646131988770695980282504891822315246557886875901314966301354150746869962467876700808409576640))
(.leaf (21075975479538304818974736531454106797675496155301569564922879670560101819109811482362794136266575904619710888865263063077532344187927347560540502760240289484356163454988586592)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 700240168 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1514335479171814353600 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 6362391182061790702978052428800 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (12724782364123581405956104857601 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 12724782364123581405956104857601 6362391182061790702978052428800 (List.ofFn fun j : Fin 6 => B i j) =
      6362391182061790702978052428800 * geometricEncoding 12724782364123581405956104857601 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    700240168 1514335479171814353600 6362391182061790702978052428800 12724782364123581405956104857601 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23584253484384))
(.leaf (-48149790867360)))
(.node 1 (.leaf (-5900208062688))
(.leaf (4122967765248))))
(.node 2 (.node 1 (.leaf (7379576324064))
(.leaf (9767493856224)))
(.node 1 (.leaf (-48149790867360))
(.node 1 (.leaf (115605876805056))
(.leaf (-15247139882688))))))
(.node 4 (.node 2 (.node 1 (.leaf (12935076655104))
(.leaf (-25180394855328)))
(.node 1 (.leaf (-10329124624128))
(.leaf (-5900208062688))))
(.node 2 (.node 1 (.leaf (-15247139882688))
(.leaf (78514487068608)))
(.node 1 (.leaf (-60332721690816))
(.node 1 (.leaf (-9956832022368))
(.leaf (11846690829216)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4122967765248))
(.leaf (12935076655104)))
(.node 1 (.leaf (-60332721690816))
(.leaf (49090567536864))))
(.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (-18103113416160)))
(.node 1 (.leaf (7379576324064))
(.node 1 (.leaf (-25180394855328))
(.leaf (-9956832022368))))))
(.node 4 (.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (35208589539168)))
(.node 1 (.leaf (-41841492407136))
(.leaf (9767493856224))))
(.node 2 (.node 1 (.leaf (-10329124624128))
(.leaf (11846690829216)))
(.node 1 (.leaf (-18103113416160))
(.node 1 (.leaf (-41841492407136))
(.leaf (69334516823904))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23584253484384))
(.leaf (-48149790867360)))
(.node 1 (.leaf (-5900208062688))
(.leaf (4122967765248))))
(.node 2 (.node 1 (.leaf (7379576324064))
(.leaf (9767493856224)))
(.node 1 (.leaf (-48149790867360))
(.node 1 (.leaf (115605876805056))
(.leaf (-15247139882688))))))
(.node 4 (.node 2 (.node 1 (.leaf (12935076655104))
(.leaf (-25180394855328)))
(.node 1 (.leaf (-10329124624128))
(.leaf (-5900208062688))))
(.node 2 (.node 1 (.leaf (-15247139882688))
(.leaf (78514487068608)))
(.node 1 (.leaf (-60332721690816))
(.node 1 (.leaf (-9956832022368))
(.leaf (11846690829216)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4122967765248))
(.leaf (12935076655104)))
(.node 1 (.leaf (-60332721690816))
(.leaf (49090567536864))))
(.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (-18103113416160)))
(.node 1 (.leaf (7379576324064))
(.node 1 (.leaf (-25180394855328))
(.leaf (-9956832022368))))))
(.node 4 (.node 2 (.node 1 (.leaf (11985340004064))
(.leaf (35208589539168)))
(.node 1 (.leaf (-41841492407136))
(.leaf (9767493856224))))
(.node 2 (.node 1 (.leaf (-10329124624128))
(.leaf (11846690829216)))
(.node 1 (.leaf (-18103113416160))
(.node 1 (.leaf (-41841492407136))
(.leaf (69334516823904))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (50186734298552878592089828100560762930852932484680918185063955009484321033488276778744224))
(.node 1 (.leaf (-53072470858779130720342522013589880809228530005589738040060144804652583364036440240716608))
(.leaf (60869935903170423223152708596862923605659751481600231066390165413733279960616741766278048))))
(.node 1 (.leaf (-93016300431502750425535396227895548970005865157759195040749876127907777870180591819226592))
(.node 1 (.leaf (-214987374755681909001979692892227839810521649183004275776738306221930074243031028878479424))
(.leaf (356250336553066677348723773632663518260034173706786922391608527798449594064373795413839520)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 115605876805056 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 693635260830336 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1387270521660673 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1387270521660673 693635260830336 (List.ofFn fun j : Fin 6 => NG i j) =
      693635260830336 * geometricEncoding 1387270521660673 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 115605876805056 693635260830336 1387270521660673 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1387270521660673))
(.leaf (1924519500268675795277754812929))))
(.node 1 (.leaf (2669829171083863582296067102735811471531241217))
(.node 1 (.leaf (3703775306914393614452280790369559246434698443215223785559041))
(.leaf (5138138302137050075265341874135301944957659317816823940698414628407009294593)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 115605876805056 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 693635260830336 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1387270521660673 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1387270521660673 693635260830336 (List.ofFn fun j : Fin 6 => H i j) =
      693635260830336 * geometricEncoding 1387270521660673 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    115605876805056 1 693635260830336 1387270521660673 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Upper.Block09
