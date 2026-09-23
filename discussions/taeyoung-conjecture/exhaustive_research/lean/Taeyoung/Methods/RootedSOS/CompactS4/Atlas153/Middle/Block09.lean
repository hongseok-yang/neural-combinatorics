import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5957066567687040))
(.leaf (-10664962001815680)))
(.node 1 (.leaf (977730105006720))
(.leaf (-1446602074968960))))
(.node 2 (.node 1 (.leaf (2428945559314560))
(.leaf (-3984979817894400)))
(.node 1 (.leaf (-10664962001815680))
(.node 1 (.leaf (19188040540855680))
(.leaf (-2500502483306880))))))
(.node 4 (.node 2 (.node 1 (.leaf (3624716227017600))
(.leaf (-3993348897457920)))
(.node 1 (.leaf (6723467069379840))
(.leaf (977730105006720))))
(.node 2 (.node 1 (.leaf (-2500502483306880))
(.leaf (7098073640311680)))
(.node 1 (.leaf (-9801273256519680))
(.node 1 (.leaf (-2904939023201280))
(.leaf (3175596126443520)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-1446602074968960))
(.leaf (3624716227017600)))
(.node 1 (.leaf (-9801273256519680))
(.leaf (13550621076869760))))
(.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (-4315589690780160)))
(.node 1 (.leaf (2428945559314560))
(.node 1 (.leaf (-3993348897457920))
(.leaf (-2904939023201280))))))
(.node 4 (.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (2570503778219520)))
(.node 1 (.leaf (-3450800922042240))
(.leaf (-3984979817894400))))
(.node 2 (.node 1 (.leaf (6723467069379840))
(.leaf (3175596126443520)))
(.node 1 (.leaf (-4315589690780160))
(.node 1 (.leaf (-3450800922042240))
(.leaf (4788047709020160))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (31908707))
(.leaf (453530485)))
(.node 1 (.leaf (1102063078))
(.leaf (-60842489))))
(.node 2 (.node 1 (.leaf (-206469193))
(.leaf (277033863)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (253325918))
(.leaf (622767140))))))
(.node 4 (.node 2 (.node 1 (.leaf (-40267597))
(.leaf (164298450)))
(.node 1 (.leaf (-227005285))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (78472344)))
(.node 1 (.leaf (871679519))
(.node 1 (.leaf (173675262))
(.leaf (-172377401)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (635473264))))
(.node 2 (.node 1 (.leaf (-237912398))
(.leaf (235539964)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1016167423)))
(.node 1 (.leaf (149496782))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (984988745))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (190082291687821427057280))
(.leaf (75313776620160)))
(.node 1 (.leaf (6495892256505600))
(.leaf (147040055360640))))
(.node 2 (.node 1 (.leaf (-2708895696549120))
(.leaf (2182384248670080)))
(.node 1 (.leaf (-340305147682070001125760))
(.node 1 (.leaf (23942595443445410509440))
(.leaf (-11684196648034560))))))
(.node 4 (.node 2 (.node 1 (.leaf (-488557497317760))
(.leaf (5461349450094720)))
(.node 1 (.leaf (-3647211925968000))
(.leaf (31198103445738661511040))))
(.node 2 (.node 1 (.leaf (-190011678322196401856640))
(.leaf (77291945324916074138880)))
(.node 1 (.leaf (2073454367287680))
(.node 1 (.leaf (-6071304915561600))
(.leaf (-2053001721513600)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-46159201755776578734720))
(.leaf (262156425036051133411200)))
(.node 1 (.leaf (-106021463993749902124800))
(.leaf (9544505679753909096960))))
(.node 2 (.node 1 (.leaf (8420340162199680))
(.leaf (2799169176960000)))
(.node 1 (.leaf (77504512171119415873920))
(.node 1 (.leaf (89982082211713213991040))
(.leaf (-38032626827061370333440))))))
(.node 4 (.node 2 (.node 1 (.leaf (2234627814953146204800))
(.leaf (5968781781040913028480)))
(.node 1 (.leaf (2041151674648320))
(.leaf (-127155553410105766540800))))
(.node 2 (.node 1 (.leaf (-104081362031441252090880))
(.leaf (44651705444625985505280)))
(.node 1 (.leaf (-2621534505364689258240))
(.node 1 (.leaf (-905913606743196854400))
(.leaf (6157712231805950300160))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (6065280151355229384292619736960))
(.leaf (2403165231236135733120)))
(.node 1 (.leaf (207275522716406034259200))
(.leaf (4691858043766441092480))))
(.node 2 (.node 1 (.leaf (-86437359074746781187840))
(.leaf (69637059552228722386560)))
(.node 1 (.leaf (2403165231236135733120))
(.node 1 (.leaf (6065280004170519337913561243520))
(.leaf (-13824676355148634510080))))))
(.node 4 (.node 2 (.node 1 (.leaf (-57077128881666180593280))
(.leaf (154934583893704911029760)))
(.node 1 (.leaf (65844477469310348764800))
(.leaf (207275522716406034259200))))
(.node 2 (.node 1 (.leaf (-13824676355148634510080))
(.leaf (6065280004315290807813203013120)))
(.node 1 (.leaf (20498685047999423965440))
(.node 1 (.leaf (-60654479606656490280960))
(.leaf (-27342494964124740092160)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4691858043766441092480))
(.leaf (-57077128881666180593280)))
(.node 1 (.leaf (20498685047999423965440))
(.leaf (6065279995694214338859711093120))))
(.node 2 (.node 1 (.leaf (3569436251100341256960))
(.leaf (3320390620808649348480)))
(.node 1 (.leaf (-86437359074746781187840))
(.node 1 (.leaf (154934583893704911029760))
(.leaf (-60654479606656490280960))))))
(.node 4 (.node 2 (.node 1 (.leaf (3569436251100341256960))
(.leaf (6065279999745660939618606879360)))
(.node 1 (.leaf (1812793114072408590720))
(.leaf (69637059552228722386560))))
(.node 2 (.node 1 (.leaf (65844477469310348764800))
(.leaf (-27342494964124740092160)))
(.node 1 (.leaf (3320390620808649348480))
(.node 1 (.leaf (1812793114072408590720))
(.leaf (6065279994161328846819592798080))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (291490555734906946260191946029886789173734836994112487881942501145725340782879118556446980648514223856913534275282020862493685508567856951811))
(.node 1 (.leaf (-238851294072345718199347192688969881035078521512573709616243751654828873537645355792782274424150982612100451997067439715597447845388345048414))
(.leaf (-181372716928936966717236864887659114497496104484643011377182857291606017264433587923560401914583207177221156285784342779175554555437196584836))))
(.node 1 (.leaf (247831345455916252611600573642968138494989006543077495997636606303652374009179790117197329551835171949909681767871169211885693075077421632030))
(.node 1 (.leaf (157298099206594948052778775023042688257064172699053449859197099943718746192623129567645058531967877115917760480887356470473483431175935932365))
(.leaf (1036389247016631124580639837601162437165735468107098933469436304047952439815433779517730253598316259842200480291641360583224297334285340956745)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 19188040540855680 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1102063078 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 126878586115465172727498240 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (253757172230930345454996481 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 253757172230930345454996481 126878586115465172727498240 (List.ofFn fun j : Fin 6 => K i j) =
      126878586115465172727498240 * geometricEncoding 253757172230930345454996481 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    19188040540855680 1102063078 126878586115465172727498240 253757172230930345454996481 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (4029139505581431537693155441235651783338256069449798646431033493325348390065312690963792488663120023506271736201313825821038945108382471538265649600843660379273041544679301292708176640))
(.node 1 (.leaf (-6733518932378864859750380437780150540344337400814912884467084165058803035214285987697023220575715407052027294821677487602280235717503330080590602245348734707365334722555889288632462720))
(.leaf (-3790272197124723981578615519296179021041074787724427973421765729257034792086643515901507459259189308227387969501659330114055468205028190595520740248808070952351327580016556177708768640))))
(.node 1 (.leaf (5167853974646412244582911421664017807498566091311195242054134819729970058736439504161906389012757502578385946538901465545856330267896129854868847849272100569340474503640232209867656320))
(.node 1 (.leaf (3768394522743144931706639348527454975680658602134054185235474300998513032193047465212632012049001155784196832874245166884316671915182621889969518331130213813905540959253993429021265920))
(.leaf (11368429566099765331700661530407678453361948891269370812311751808204719524428965715097087559256935795584425100466896729910852420777394423867578946468409551407133819412998366286819945728814720)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1102063078 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 340305147682070001125760 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 2250226431082479785112711184135680 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (4500452862164959570225422368271361 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 4500452862164959570225422368271361 2250226431082479785112711184135680 (List.ofFn fun j : Fin 6 => B i j) =
      2250226431082479785112711184135680 * geometricEncoding 4500452862164959570225422368271361 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1102063078 340305147682070001125760 2250226431082479785112711184135680 4500452862164959570225422368271361 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5957066567687040))
(.leaf (-10664962001815680)))
(.node 1 (.leaf (977730105006720))
(.leaf (-1446602074968960))))
(.node 2 (.node 1 (.leaf (2428945559314560))
(.leaf (-3984979817894400)))
(.node 1 (.leaf (-10664962001815680))
(.node 1 (.leaf (19188040540855680))
(.leaf (-2500502483306880))))))
(.node 4 (.node 2 (.node 1 (.leaf (3624716227017600))
(.leaf (-3993348897457920)))
(.node 1 (.leaf (6723467069379840))
(.leaf (977730105006720))))
(.node 2 (.node 1 (.leaf (-2500502483306880))
(.leaf (7098073640311680)))
(.node 1 (.leaf (-9801273256519680))
(.node 1 (.leaf (-2904939023201280))
(.leaf (3175596126443520)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-1446602074968960))
(.leaf (3624716227017600)))
(.node 1 (.leaf (-9801273256519680))
(.leaf (13550621076869760))))
(.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (-4315589690780160)))
(.node 1 (.leaf (2428945559314560))
(.node 1 (.leaf (-3993348897457920))
(.leaf (-2904939023201280))))))
(.node 4 (.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (2570503778219520)))
(.node 1 (.leaf (-3450800922042240))
(.leaf (-3984979817894400))))
(.node 2 (.node 1 (.leaf (6723467069379840))
(.leaf (3175596126443520)))
(.node 1 (.leaf (-4315589690780160))
(.node 1 (.leaf (-3450800922042240))
(.leaf (4788047709020160))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (5957066567687040))
(.leaf (-10664962001815680)))
(.node 1 (.leaf (977730105006720))
(.leaf (-1446602074968960))))
(.node 2 (.node 1 (.leaf (2428945559314560))
(.leaf (-3984979817894400)))
(.node 1 (.leaf (-10664962001815680))
(.node 1 (.leaf (19188040540855680))
(.leaf (-2500502483306880))))))
(.node 4 (.node 2 (.node 1 (.leaf (3624716227017600))
(.leaf (-3993348897457920)))
(.node 1 (.leaf (6723467069379840))
(.leaf (977730105006720))))
(.node 2 (.node 1 (.leaf (-2500502483306880))
(.leaf (7098073640311680)))
(.node 1 (.leaf (-9801273256519680))
(.node 1 (.leaf (-2904939023201280))
(.leaf (3175596126443520)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-1446602074968960))
(.leaf (3624716227017600)))
(.node 1 (.leaf (-9801273256519680))
(.leaf (13550621076869760))))
(.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (-4315589690780160)))
(.node 1 (.leaf (2428945559314560))
(.node 1 (.leaf (-3993348897457920))
(.leaf (-2904939023201280))))))
(.node 4 (.node 2 (.node 1 (.leaf (3967737354996480))
(.leaf (2570503778219520)))
(.node 1 (.leaf (-3450800922042240))
(.leaf (-3984979817894400))))
(.node 2 (.node 1 (.leaf (6723467069379840))
(.leaf (3175596126443520)))
(.node 1 (.leaf (-4315589690780160))
(.node 1 (.leaf (-3450800922042240))
(.leaf (4788047709020160))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2579202810548786057658043887555295971996525620756187294936578823810492665814339318229525793140943771520))
(.node 1 (.leaf (4351636885112130856064099623777395013108093245896016849471939703977843788172480051915122558283426551040))
(.leaf (2055344525889894818110304779570741988783696620212012357580035557730571351559372380164454485008873777280))))
(.node 1 (.leaf (-2793183797231094386217723906061404446576723718475993080284865957394305073651492669067407169934514834560))
(.node 1 (.leaf (-2233465624294798309354309268292902719082150089342603058750312726781594008203083841896660411268424628480))
(.leaf (3098973312911700277183592947080846030627104935834326536050996492811325016715874692522499185607330165120)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 19188040540855680 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 115128243245134080 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (230256486490268161 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 230256486490268161 115128243245134080 (List.ofFn fun j : Fin 6 => NG i j) =
      115128243245134080 * geometricEncoding 230256486490268161 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 19188040540855680 115128243245134080 230256486490268161 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (230256486490268161))
(.leaf (53018049570843044139447361690321921))))
(.node 1 (.leaf (12207749814749189063996101954673231310445585706657281))
(.node 1 (.leaf (2810913580296370296850547152427469736294526129526509724345316613130241))
(.leaf (647231084826822494849411154907197395614926521116227252861990977200186057875237708556801)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 19188040540855680 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 115128243245134080 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (230256486490268161 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 230256486490268161 115128243245134080 (List.ofFn fun j : Fin 6 => H i j) =
      115128243245134080 * geometricEncoding 230256486490268161 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    19188040540855680 1 115128243245134080 230256486490268161 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas153.Middle.Block09
