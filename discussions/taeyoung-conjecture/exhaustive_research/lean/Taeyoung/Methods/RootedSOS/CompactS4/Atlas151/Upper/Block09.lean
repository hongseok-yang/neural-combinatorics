import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22841364133152))
(.leaf (-48818622659904)))
(.node 1 (.leaf (-945187364448))
(.leaf (2872616825088))))
(.node 2 (.node 1 (.leaf (9884015419968))
(.leaf (5444060002272)))
(.node 1 (.leaf (-48818622659904))
(.node 1 (.leaf (106481554921152))
(.leaf (-10437638781888))))))
(.node 4 (.node 2 (.node 1 (.leaf (-421191005760))
(.leaf (-18515111207040)))
(.node 1 (.leaf (-15994491670368))
(.leaf (-945187364448))))
(.node 2 (.node 1 (.leaf (-10437638781888))
(.leaf (111129548556384)))
(.node 1 (.leaf (-31157370723744))
(.node 1 (.leaf (-3758529071232))
(.leaf (10886183523936)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2872616825088))
(.leaf (-421191005760)))
(.node 1 (.leaf (-31157370723744))
(.leaf (26852209062336))))
(.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (-28429295563008)))
(.node 1 (.leaf (9884015419968))
(.node 1 (.leaf (-18515111207040))
(.leaf (-3758529071232))))))
(.node 4 (.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (28252706452128)))
(.node 1 (.leaf (-29327089949280))
(.leaf (5444060002272))))
(.node 2 (.node 1 (.leaf (-15994491670368))
(.leaf (10886183523936)))
(.node 1 (.leaf (-28429295563008))
(.node 1 (.leaf (-29327089949280))
(.leaf (43885438882560))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (31957863))
(.leaf (223045351)))
(.node 1 (.leaf (306457464))
(.leaf (-300229467))))
(.node 2 (.node 1 (.leaf (81199438))
(.leaf (-51801743)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (104358947))
(.leaf (142910246))))))
(.node 4 (.node 2 (.node 1 (.leaf (-137723117))
(.leaf (52547728)))
(.node 1 (.leaf (87205513))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (24572022)))
(.node 1 (.leaf (-2634116))
(.node 1 (.leaf (-25135896))
(.leaf (-3830240)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (45849475))))
(.node 2 (.node 1 (.leaf (-122392907))
(.leaf (19956150)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (105061709)))
(.node 1 (.leaf (376161044))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (305203706))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (729961185700385374176))
(.leaf (25619778015264)))
(.node 1 (.leaf (-11875073003712))
(.leaf (7585809747552))))
(.node 2 (.node 1 (.leaf (-14924133349632))
(.leaf (6766516810656)))
(.node 1 (.leaf (-1560138854813907625152))
(.node 1 (.leaf (223536119979249440640))
(.leaf (22140623462400))))))
(.node 4 (.node 2 (.node 1 (.leaf (-21061868764608))
(.leaf (29863135173312)))
(.node 1 (.leaf (-17541311140800))
(.leaf (-30206168302360254624))))
(.node 2 (.node 1 (.leaf (-1300080639908263433184))
(.leaf (949372463285203624128)))
(.node 1 (.leaf (33815875863168))
(.node 1 (.leaf (28294906337568))
(.leaf (38987923827168)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (91802694947657266944))
(.leaf (596768778193274031168)))
(.node 1 (.leaf (54542758128057549504))
(.leaf (508795336713923209728))))
(.node 2 (.node 1 (.leaf (-3091869652032))
(.leaf (1812785520960)))
(.node 1 (.leaf (315872010681224808384))
(.node 1 (.leaf (272366179481581581888))
(.leaf (290676543398892638208))))))
(.node 4 (.node 2 (.node 1 (.leaf (592727287738779942336))
(.leaf (222040933129291803552)))
(.node 1 (.leaf (16091602985088))
(.leaf (173980523716388264736))))
(.node 2 (.node 1 (.leaf (-454896034448056545024))
(.leaf (-349908376050937513728)))
(.node 1 (.leaf (-763799731507606273344))
(.node 1 (.leaf (-273663624213896342688))
(.leaf (76434182957354296320))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (23327999567930474835120345888))
(.leaf (818753355902218820832)))
(.node 1 (.leaf (-379501956167626587456))
(.leaf (242426268656331401376))))
(.node 2 (.node 1 (.leaf (-476943408981270556416))
(.leaf (216243417222141388128)))
(.node 1 (.leaf (818753355902218820832))
(.node 1 (.leaf (23327999811872513432171643744))
(.leaf (-338107675804009250112))))))
(.node 4 (.node 2 (.node 1 (.leaf (-506014848364724517024))
(.leaf (-212273220533972338368)))
(.node 1 (.leaf (-321352642573088677344))
(.leaf (-379501956167626587456))))
(.node 2 (.node 1 (.leaf (-338107675804009250112))
(.leaf (23328000578955403799066590848)))
(.node 1 (.leaf (145695616910453840256))
(.node 1 (.leaf (389398996237882824000))
(.leaf (524828613628233593280)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (242426268656331401376))
(.leaf (-506014848364724517024)))
(.node 1 (.leaf (145695616910453840256))
(.leaf (23327999604929263526970581664))))
(.node 2 (.node 1 (.leaf (151527875719686999552))
(.leaf (364752861531704105760)))
(.node 1 (.leaf (-476943408981270556416))
(.node 1 (.leaf (-212273220533972338368))
(.leaf (389398996237882824000))))))
(.node 4 (.node 2 (.node 1 (.leaf (151527875719686999552))
(.leaf (23327999927131870274546114784)))
(.node 1 (.leaf (116424137562117651072))
(.leaf (216243417222141388128))))
(.node 2 (.node 1 (.leaf (-321352642573088677344))
(.leaf (524828613628233593280)))
(.node 1 (.leaf (364752861531704105760))
(.node 1 (.leaf (116424137562117651072))
(.leaf (23327999963327462553577613664))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-1645384642177595042944104478146800029170995157991636631594931583035626350203860921371458427433194276172163159138620983175834838))
(.node 1 (.leaf (2769918606858819650647629406433991105646536222866412118182435055980709863817272519380306502266669916406542988506506410735526773))
(.leaf (-121660347835290245683168013807455328572260168243518967164891249579041193181769033189257731924190800530134496080692146965773830))))
(.node 1 (.leaf (633869457384714126631775531751181492245989087414980530613438304272267074560059943389936251951180609930719531062828429304408558))
(.node 1 (.leaf (11948045933185888837043214024547463378153258914789446400294124161241343294516418546595446062465599537848664705637538199332737121))
(.leaf (9694219952948029514639524905414214416379436856561847553349324721552593364064463929898725899305828239501747942389184754340888058)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 111129548556384 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 376161044 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 250815642025308589829376 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (501631284050617179658753 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 501631284050617179658753 250815642025308589829376 (List.ofFn fun j : Fin 6 => K i j) =
      250815642025308589829376 * geometricEncoding 501631284050617179658753 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    111129548556384 376161044 250815642025308589829376 501631284050617179658753 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (117207862488065174931715710250827362977337455168964861247295837238746405630276756519118575101754097843977341820407531818010084271853475887987073915676356085492969146432))
(.node 1 (.leaf (-303846076435289168213070023117787205852088760779953341241907615668542823927373888645628349176943550153179948083869128690127727010119049574166831348594195290490532783104))
(.leaf (675338781015581991497474045386513663407261237637820957559439145504088451835516572819406235698187249930371213537849487553381933216423461731442494833880448632174204795328))))
(.node 1 (.leaf (31400604181819282819124533691113653577971572477458086043484270410491663771072165988014543159230763867694295862046235982977671274461884688628781540354934085604144561408))
(.node 1 (.leaf (278734604917930217464210349381651902066617327098444140385881534736041838764214752331295511830195556035120308871769752172812207981652188303548336570911744952072347965408))
(.leaf (1323973242975608698241533934587713968941291932631544142155106587335386333189474404453045407654913083321652791999123697993099882057329772759254428397990009129281077850285416256)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 376161044 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1560138854813907625152 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 3521180762470583507980421872128 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (7042361524941167015960843744257 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 7042361524941167015960843744257 3521180762470583507980421872128 (List.ofFn fun j : Fin 6 => B i j) =
      3521180762470583507980421872128 * geometricEncoding 7042361524941167015960843744257 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    376161044 1560138854813907625152 3521180762470583507980421872128 7042361524941167015960843744257 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22841364133152))
(.leaf (-48818622659904)))
(.node 1 (.leaf (-945187364448))
(.leaf (2872616825088))))
(.node 2 (.node 1 (.leaf (9884015419968))
(.leaf (5444060002272)))
(.node 1 (.leaf (-48818622659904))
(.node 1 (.leaf (106481554921152))
(.leaf (-10437638781888))))))
(.node 4 (.node 2 (.node 1 (.leaf (-421191005760))
(.leaf (-18515111207040)))
(.node 1 (.leaf (-15994491670368))
(.leaf (-945187364448))))
(.node 2 (.node 1 (.leaf (-10437638781888))
(.leaf (111129548556384)))
(.node 1 (.leaf (-31157370723744))
(.node 1 (.leaf (-3758529071232))
(.leaf (10886183523936)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2872616825088))
(.leaf (-421191005760)))
(.node 1 (.leaf (-31157370723744))
(.leaf (26852209062336))))
(.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (-28429295563008)))
(.node 1 (.leaf (9884015419968))
(.node 1 (.leaf (-18515111207040))
(.leaf (-3758529071232))))))
(.node 4 (.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (28252706452128)))
(.node 1 (.leaf (-29327089949280))
(.leaf (5444060002272))))
(.node 2 (.node 1 (.leaf (-15994491670368))
(.leaf (10886183523936)))
(.node 1 (.leaf (-28429295563008))
(.node 1 (.leaf (-29327089949280))
(.leaf (43885438882560))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22841364133152))
(.leaf (-48818622659904)))
(.node 1 (.leaf (-945187364448))
(.leaf (2872616825088))))
(.node 2 (.node 1 (.leaf (9884015419968))
(.leaf (5444060002272)))
(.node 1 (.leaf (-48818622659904))
(.node 1 (.leaf (106481554921152))
(.leaf (-10437638781888))))))
(.node 4 (.node 2 (.node 1 (.leaf (-421191005760))
(.leaf (-18515111207040)))
(.node 1 (.leaf (-15994491670368))
(.leaf (-945187364448))))
(.node 2 (.node 1 (.leaf (-10437638781888))
(.leaf (111129548556384)))
(.node 1 (.leaf (-31157370723744))
(.node 1 (.leaf (-3758529071232))
(.leaf (10886183523936)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2872616825088))
(.leaf (-421191005760)))
(.node 1 (.leaf (-31157370723744))
(.leaf (26852209062336))))
(.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (-28429295563008)))
(.node 1 (.leaf (9884015419968))
(.node 1 (.leaf (-18515111207040))
(.leaf (-3758529071232))))))
(.node 4 (.node 2 (.node 1 (.leaf (21817932277248))
(.leaf (28252706452128)))
(.node 1 (.leaf (-29327089949280))
(.leaf (5444060002272))))
(.node 2 (.node 1 (.leaf (-15994491670368))
(.leaf (10886183523936)))
(.node 1 (.leaf (-28429295563008))
(.node 1 (.leaf (-29327089949280))
(.leaf (43885438882560))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (22960264350756145669351338703547664691034401119101134742660136143744137554227005173994656))
(.node 1 (.leaf (-67456596134935129256414758205653912808320624485801573750011926398059248745921576118958176))
(.leaf (45912361615431013327268733780797947396299301778483455088578453410275759557788205804560000))))
(.node 1 (.leaf (-119900247455029485962389813310985012749481148106557130974513284450264094330877079110523936))
(.node 1 (.leaf (-123686685597303279422995621970041903505135448643302452914738274224602618874413313740568704))
(.leaf (185086365225954873889526339156800307811634053788554799169939140140105358117575474421003904)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 111129548556384 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 666777291338304 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1333554582676609 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1333554582676609 666777291338304 (List.ofFn fun j : Fin 6 => NG i j) =
      666777291338304 * geometricEncoding 1333554582676609 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 111129548556384 666777291338304 1333554582676609 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1333554582676609))
(.leaf (1778367824977784788802675738881))))
(.node 1 (.leaf (2371550562683758629008104513611982731750534529))
(.node 1 (.leaf (3162592120916216991362691131476685528881292226244159295132161))
(.leaf (4217489215984757499278971844540417496990049301399721530668217973631778322049)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 111129548556384 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 666777291338304 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1333554582676609 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1333554582676609 666777291338304 (List.ofFn fun j : Fin 6 => H i j) =
      666777291338304 * geometricEncoding 1333554582676609 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    111129548556384 1 666777291338304 1333554582676609 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Upper.Block09
