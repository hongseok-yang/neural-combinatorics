import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (14727835259136))
(.leaf (-29524078012032)))
(.node 1 (.leaf (-130704513408))
(.leaf (-926718843456))))
(.node 2 (.node 1 (.leaf (8953826832000))
(.leaf (-1069084122048)))
(.node 1 (.leaf (-29524078012032))
(.node 1 (.leaf (59786312124096))
(.leaf (-1680268281984))))))
(.node 4 (.node 2 (.node 1 (.leaf (4183030724544))
(.leaf (-16298829839232)))
(.node 1 (.leaf (-619064016192))
(.leaf (-130704513408))))
(.node 2 (.node 1 (.leaf (-1680268281984))
(.leaf (7020748659456)))
(.node 1 (.leaf (-8365520395008))
(.node 1 (.leaf (-6071402464704))
(.leaf (9967523159232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-926718843456))
(.leaf (4183030724544)))
(.node 1 (.leaf (-8365520395008))
(.leaf (10097386651584))))
(.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (-11846614569984)))
(.node 1 (.leaf (8953826832000))
(.node 1 (.leaf (-16298829839232))
(.leaf (-6071402464704))))))
(.node 4 (.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (10597522657536)))
(.node 1 (.leaf (-9175483749312))
(.leaf (-1069084122048))))
(.node 2 (.node 1 (.leaf (-619064016192))
(.leaf (9967523159232)))
(.node 1 (.leaf (-11846614569984))
(.node 1 (.leaf (-9175483749312))
(.leaf (14266211619456))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (32495533))
(.leaf (322466697)))
(.node 1 (.leaf (938635480))
(.leaf (-106590200))))
(.node 2 (.node 1 (.leaf (-205086775))
(.leaf (25270444)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (160859770))
(.leaf (467589771))))))
(.node 4 (.node 2 (.node 1 (.leaf (-73770513))
(.leaf (129032625)))
(.node 1 (.leaf (58053444))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (144691674)))
(.node 1 (.leaf (652636421))
(.node 1 (.leaf (276370923))
(.leaf (-299720460)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (564206664))))
(.node 2 (.node 1 (.leaf (-323050114))
(.leaf (357555254)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (733407062)))
(.node 1 (.leaf (263929244))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (682081864))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (478588856681817439488))
(.leaf (-8503799758848)))
(.node 1 (.leaf (-13656493344384))
(.leaf (1989871121664))))
(.node 2 (.node 1 (.leaf (8902699632000))
(.leaf (7995688018560)))
(.node 1 (.leaf (-959400651334560253056))
(.node 1 (.leaf (96680498920008719616))
(.leaf (28170101125440))))))
(.node 4 (.node 2 (.node 1 (.leaf (-3023971672896))
(.leaf (-18060570896832)))
(.node 1 (.leaf (-17240878491264))
(.leaf (-4247312828698606464))))
(.node 2 (.node 1 (.leaf (-312435422099911357056))
(.leaf (107483721397598067840)))
(.node 1 (.leaf (-3478864546944))
(.node 1 (.leaf (587562740352))
(.leaf (4247508056832)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-30114222759246282048))
(.leaf (374045395756164810048)))
(.node 1 (.leaf (-124329957711723142848))
(.leaf (27564371831182729536))))
(.node 2 (.node 1 (.leaf (-1370217669120))
(.leaf (-5650485671808)))
(.node 1 (.leaf (290959375295541456000))
(.node 1 (.leaf (265484944817017407360))
(.leaf (-95267951949006010368))))))
(.node 4 (.node 2 (.node 1 (.leaf (12141518233597509312))
(.leaf (21205145627404781760)))
(.node 1 (.leaf (1176550230528))
(.leaf (-34740458367786811584))))
(.node 2 (.node 1 (.leaf (-444326520911884831296))
(.leaf (149269321918585999296)))
(.node 1 (.leaf (-19147684908436708608))
(.node 1 (.leaf (-8205256381208000832))
(.leaf (22800787736486768640))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (15551999985736269104857807104))
(.leaf (-276335505689037225984)))
(.node 1 (.leaf (-443775030136710636672))
(.leaf (64661922699779526912))))
(.node 2 (.node 1 (.leaf (289297969680743856000))
(.leaf (259824143864821092480)))
(.node 1 (.leaf (-276335505689037225984))
(.node 1 (.leaf (15552000077565630850313163264))
(.leaf (127671686549027569152))))))
(.node 4 (.node 2 (.node 1 (.leaf (155231780270109429888))
(.leaf (-34395135818933744640)))
(.node 1 (.leaf (-195020643115156152960))
(.leaf (-443775030136710636672))))
(.node 2 (.node 1 (.leaf (127671686549027569152))
(.leaf (15551999930350032883585894080)))
(.node 1 (.leaf (-49577321535279452352))
(.node 1 (.leaf (-3533030919237916224))
(.leaf (57957086733864465024)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (64661922699779526912))
(.leaf (155231780270109429888)))
(.node 1 (.leaf (-49577321535279452352))
(.leaf (15552000016672652719218203328))))
(.node 2 (.node 1 (.leaf (-6224050254409140672))
(.leaf (3643251344207736192)))
(.node 1 (.leaf (289297969680743856000))
(.node 1 (.leaf (-34395135818933744640))
(.leaf (-3533030919237916224))))))
(.node 4 (.node 2 (.node 1 (.leaf (-6224050254409140672))
(.leaf (15552000002682490623470709696)))
(.node 1 (.leaf (-2277668249943561216))
(.leaf (259824143864821092480))))
(.node 2 (.node 1 (.leaf (-195020643115156152960))
(.leaf (57957086733864465024)))
(.node 1 (.leaf (3643251344207736192))
(.node 1 (.leaf (-2277668249943561216))
(.leaf (15552000018233552893617771264))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3499554488131540004472492097375167001033214001365343457318379354678741030914319998202141042375734693802397079257276511317417099))
(.node 1 (.leaf (8039478471438531997435687654919532040863607808008136862341852097604161564780206138901263261113471578350755208814221542445721577))
(.leaf (-41506515713687092741580187246425584168438063772823059835737305202685168597093855979617267871787275461501169762762669178410794562))))
(.node 1 (.leaf (49515714638441365403407096806623046928580316053251228853425812704410518960035809609306851215590788075095565174502859998620282364))
(.node 1 (.leaf (36550001669514169435891051248527489791919476348684609033388175989073109247671426269276909147967779715771292993622588122669548786))
(.leaf (94457487507315925412358980058658318201670304879355369841632472121268581068721044129131586833373190298102639654658433204515733064)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 59786312124096 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 938635480 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 336705322668184011156480 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (673410645336368022312961 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 673410645336368022312961 336705322668184011156480 (List.ofFn fun j : Fin 6 => K i j) =
      336705322668184011156480 * geometricEncoding 673410645336368022312961 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    59786312124096 938635480 336705322668184011156480 673410645336368022312961 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1178275769762872757353992424452567871707068740379338861893030662685906046547258933751864058397150879109733142581111321053941579290017108600370970569896711943589093331840))
(.node 1 (.leaf (-2540683094253698701913213792753456863654907012203976623266683118186374464756347818367764099578219734896759833326660316974917306378997240174243292551707813384338491091392))
(.leaf (625929352623624121190354414960957153326601311872390483013182008372215141486895744641771848894907584995514440889091810710788226698314143387183243984741635215308545804160))))
(.node 1 (.leaf (-832677605608067504023126262841177723217949793423443794047452784588993033561450702201511438137296240683284493968523972086200689265821958035719779406302696283366703107840))
(.node 1 (.leaf (173381030540725534528674353671184151094998072532526142681202035839999685649282822568778860481577743429538087913099000472818595887662871285212742722564826935700622609792))
(.leaf (3360013004390238229219926970932302707465931965374417961944381331951091805235273978734901444340390233913159886315107097819488308508544917449395178487670656216048786575165808256)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 938635480 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 959400651334560253056 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 5403164945266365622296840161280 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (10806329890532731244593680322561 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 10806329890532731244593680322561 5403164945266365622296840161280 (List.ofFn fun j : Fin 6 => B i j) =
      5403164945266365622296840161280 * geometricEncoding 10806329890532731244593680322561 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    938635480 959400651334560253056 5403164945266365622296840161280 10806329890532731244593680322561 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (14727835259136))
(.leaf (-29524078012032)))
(.node 1 (.leaf (-130704513408))
(.leaf (-926718843456))))
(.node 2 (.node 1 (.leaf (8953826832000))
(.leaf (-1069084122048)))
(.node 1 (.leaf (-29524078012032))
(.node 1 (.leaf (59786312124096))
(.leaf (-1680268281984))))))
(.node 4 (.node 2 (.node 1 (.leaf (4183030724544))
(.leaf (-16298829839232)))
(.node 1 (.leaf (-619064016192))
(.leaf (-130704513408))))
(.node 2 (.node 1 (.leaf (-1680268281984))
(.leaf (7020748659456)))
(.node 1 (.leaf (-8365520395008))
(.node 1 (.leaf (-6071402464704))
(.leaf (9967523159232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-926718843456))
(.leaf (4183030724544)))
(.node 1 (.leaf (-8365520395008))
(.leaf (10097386651584))))
(.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (-11846614569984)))
(.node 1 (.leaf (8953826832000))
(.node 1 (.leaf (-16298829839232))
(.leaf (-6071402464704))))))
(.node 4 (.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (10597522657536)))
(.node 1 (.leaf (-9175483749312))
(.leaf (-1069084122048))))
(.node 2 (.node 1 (.leaf (-619064016192))
(.leaf (9967523159232)))
(.node 1 (.leaf (-11846614569984))
(.node 1 (.leaf (-9175483749312))
(.leaf (14266211619456))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (14727835259136))
(.leaf (-29524078012032)))
(.node 1 (.leaf (-130704513408))
(.leaf (-926718843456))))
(.node 2 (.node 1 (.leaf (8953826832000))
(.leaf (-1069084122048)))
(.node 1 (.leaf (-29524078012032))
(.node 1 (.leaf (59786312124096))
(.leaf (-1680268281984))))))
(.node 4 (.node 2 (.node 1 (.leaf (4183030724544))
(.leaf (-16298829839232)))
(.node 1 (.leaf (-619064016192))
(.leaf (-130704513408))))
(.node 2 (.node 1 (.leaf (-1680268281984))
(.leaf (7020748659456)))
(.node 1 (.leaf (-8365520395008))
(.node 1 (.leaf (-6071402464704))
(.leaf (9967523159232)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-926718843456))
(.leaf (4183030724544)))
(.node 1 (.leaf (-8365520395008))
(.leaf (10097386651584))))
(.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (-11846614569984)))
(.node 1 (.leaf (8953826832000))
(.node 1 (.leaf (-16298829839232))
(.leaf (-6071402464704))))))
(.node 4 (.node 2 (.node 1 (.leaf (6604985877120))
(.leaf (10597522657536)))
(.node 1 (.leaf (-9175483749312))
(.leaf (-1069084122048))))
(.node 2 (.node 1 (.leaf (-619064016192))
(.leaf (9967523159232)))
(.node 1 (.leaf (-11846614569984))
(.node 1 (.leaf (-9175483749312))
(.leaf (14266211619456))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-203201512034434819050023010784285850378103259058659809947760104054761053133715888289408))
(.node 1 (.leaf (-117665898821273824337740301389011077592877009843287961301771962420218924646271077181760))
(.leaf (1894533587604131798812205786642102757336604176336815631879854358787573278779957094708480))))
(.node 1 (.leaf (-2251693710031416571636591382396672796150423820418048225364421086944777692668553756249920))
(.node 1 (.leaf (-1743990143578140915875097206432799437916447874971204389269092951164051702146022646043392))
(.leaf (2711588089554057793313985426313783598941481637922739307693626538028527911226768822152832)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 59786312124096 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 358717872744576 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (717435745489153 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 717435745489153 358717872744576 (List.ofFn fun j : Fin 6 => NG i j) =
      358717872744576 * geometricEncoding 717435745489153 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 59786312124096 358717872744576 717435745489153 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (717435745489153))
(.leaf (514714048905576719187240657409))))
(.node 1 (.leaf (369274257390312789349063364463112013998584577))
(.node 1 (.leaf (264930552140772422634917011784261684698749585928954506593281))
(.leaf (190070648177967982279851802211753122102109465604828449714763849992968180993)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 59786312124096 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 358717872744576 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (717435745489153 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 717435745489153 358717872744576 (List.ofFn fun j : Fin 6 => H i j) =
      358717872744576 * geometricEncoding 717435745489153 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    59786312124096 1 358717872744576 717435745489153 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas147.Lower.Block09
