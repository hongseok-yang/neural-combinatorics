import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2648313665769600))
(.leaf (-5375813730652800)))
(.node 1 (.leaf (107165724710400))
(.leaf (15644556950400))))
(.node 2 (.node 1 (.leaf (1317464243136000))
(.leaf (-393845403945600)))
(.node 1 (.leaf (-5375813730652800))
(.node 1 (.leaf (11179432407628800))
(.leaf (-840694125744000))))))
(.node 4 (.node 2 (.node 1 (.leaf (872285827132800))
(.leaf (-2208514856860800)))
(.node 1 (.leaf (-104094038304000))
(.leaf (107165724710400))))
(.node 2 (.node 1 (.leaf (-840694125744000))
(.leaf (1479685417200000)))
(.node 1 (.leaf (-2138159547417600))
(.node 1 (.leaf (-1050113946412800))
(.leaf (2122125076944000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (15644556950400))
(.leaf (872285827132800)))
(.node 1 (.leaf (-2138159547417600))
(.leaf (3104405043811200))))
(.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (-3104382443644800)))
(.node 1 (.leaf (1317464243136000))
(.node 1 (.leaf (-2208514856860800))
(.leaf (-1050113946412800))))))
(.node 4 (.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (1482708023827200)))
(.node 1 (.leaf (-1796372868614400))
(.leaf (-393845403945600))))
(.node 2 (.node 1 (.leaf (-104094038304000))
(.leaf (2122125076944000)))
(.node 1 (.leaf (-3104382443644800))
(.node 1 (.leaf (-1796372868614400))
(.leaf (3160788154963200))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (29679327))
(.leaf (189716685)))
(.node 1 (.leaf (1554322182))
(.leaf (-327887686))))
(.node 2 (.node 1 (.leaf (-296156361))
(.leaf (121475228)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (93461067))
(.leaf (772311557))))))
(.node 4 (.node 2 (.node 1 (.leaf (-137156825))
(.leaf (163855226)))
(.node 1 (.leaf (57550654))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (330986400)))
(.node 1 (.leaf (1105438866))
(.node 1 (.leaf (317565012))
(.leaf (-425547008)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (802498760))))
(.node 2 (.node 1 (.leaf (-470307672))
(.leaf (621355730)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1243673817)))
(.node 1 (.leaf (350580467))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (1112916184))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (78600167284944665059200))
(.leaf (2249945191238400)))
(.node 1 (.leaf (562267125417600))
(.leaf (-1832250191875200))))
(.node 2 (.node 1 (.leaf (1705885327209600))
(.leaf (-2453245823232000)))
(.node 1 (.leaf (-159550533603134374665600))
(.node 1 (.leaf (24960121114434485961600))
(.leaf (-922917055968000))))))
(.node 4 (.node 2 (.node 1 (.leaf (3802639463884800))
(.leaf (-3153215694873600)))
(.node 1 (.leaf (4750407355363200))
(.leaf (3180606586871941900800))))
(.node 2 (.node 1 (.leaf (-58241043974986735824000))
(.leaf (7048023224903902684800)))
(.node 1 (.leaf (-269088580310400))
(.node 1 (.leaf (-665067740428800))
(.leaf (446241899865600)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (464319921501044380800))
(.leaf (84492797615732636121600)))
(.node 1 (.leaf (-9708624027846113097600))
(.leaf (2906920652853127536000))))
(.node 2 (.node 1 (.leaf (1076307714230400))
(.leaf (-805617545414400)))
(.node 1 (.leaf (39101452082840849472000))
(.node 1 (.leaf (43534793806233285686400))
(.leaf (-5471085374636123433600))))))
(.node 4 (.node 2 (.node 1 (.leaf (1099280203275705667200))
(.leaf (1875734383774422758400)))
(.node 1 (.leaf (-1628912405376000))
(.leaf (-11689066531148552611200))))
(.node 2 (.node 1 (.leaf (-84447784327275862704000))
(.leaf (9838863139041280972800)))
(.node 1 (.leaf (-1969257086920696262400))
(.node 1 (.leaf (-590877213881621673600))
(.leaf (2096115880751550835200))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2332800067104574891197471158400))
(.leaf (66776859062842008556800)))
(.node 1 (.leaf (16687709876618961955200))
(.leaf (-54379952590476803990400))))
(.node 2 (.node 1 (.leaf (50629528450755715939200))
(.leaf (-72810684999086724864000)))
(.node 1 (.leaf (66776859062842008556800))
(.node 1 (.leaf (2332799978656419273007949731200))
(.leaf (20414642315438314800000))))))
(.node 4 (.node 2 (.node 1 (.leaf (7790309217804495369600))
(.leaf (28932005944312526044800)))
(.node 1 (.leaf (-21443524956778181385600))
(.leaf (16687709876618961955200))))
(.node 2 (.node 1 (.leaf (20414642315438314800000))
(.leaf (2332799995492089865041757747200)))
(.node 1 (.leaf (-149371620914557612800))
(.node 1 (.leaf (-3897895995120459168000))
(.leaf (3360100022132188118400)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-54379952590476803990400))
(.leaf (7790309217804495369600)))
(.node 1 (.leaf (-149371620914557612800))
(.leaf (2332800001086370338757346380800))))
(.node 2 (.node 1 (.leaf (1690137984458499897600))
(.leaf (-375635629742982422400)))
(.node 1 (.leaf (50629528450755715939200))
(.node 1 (.leaf (28932005944312526044800))
(.leaf (-3897895995120459168000))))))
(.node 4 (.node 2 (.node 1 (.leaf (1690137984458499897600))
(.leaf (2332800001469197713535354339200)))
(.node 1 (.leaf (-313355708760611692800))
(.leaf (-72810684999086724864000))))
(.node 2 (.node 1 (.leaf (-21443524956778181385600))
(.leaf (3360100022132188118400)))
(.node 1 (.leaf (-375635629742982422400))
(.node 1 (.leaf (-313355708760611692800))
(.leaf (2332800001071414215374730284800))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (47884830037842467071727923900287993834403081885816881634118869074004011599542710911731414898361283690836214535438168872051862994880856019775))
(.node 1 (.leaf (22686133878725288162878829915620990494645821086697931314252310409154238761121897260361823608933967308774743622402390536565880571967397637679))
(.leaf (-167748161388035333736622742302194648837366558643296085982130080365471256314843453027129541135171532002788154039145248654649787767421550481530))))
(.node 1 (.leaf (244934823452972105163321584844643665715239887005710055560058817536686212359935427932678175766129509877303446986340367172429975038705453873218))
(.node 1 (.leaf (138196785906690702226453104823862493719483423447798442215423212829224742782764567210980822434756476572752002972464215486932235989934739751884))
(.leaf (438705102222193104643632329518593171875262080228136900965278852879823436028211387938133888347898861858678779067774323135616359881141885780184)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 11179432407628800 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1554322182 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 104258638640082659172249600 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (208517277280165318344499201 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 208517277280165318344499201 104258638640082659172249600 (List.ofFn fun j : Fin 6 => K i j) =
      104258638640082659172249600 * geometricEncoding 208517277280165318344499201 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    11179432407628800 1554322182 104258638640082659172249600 208517277280165318344499201 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-572590090985687980523922364480422645081651534552548970233848779664075085811074327412275820547806255255153639849928983590930835907051625814440187754921689249902969699035708164871622400))
(.node 1 (.leaf (1108749948361479841574798476670116344782376840230906573950109836650183612386456533099798859535852634792037051962919266064746186837520203515103268727852640870080307811648600712980342400))
(.leaf (104153317056929357482686330802258886043735717276754506652584103503529325825799292382604941368942293059347080803065888032308156387228416222826829573754470689162337123670428902970768000))))
(.node 1 (.leaf (-188031961273566387193107572385185169287365461854541443280067403295729964723699166282929187963739982145411254303333893140632310238738473276294986715369764236342372563261976138294643200))
(.node 1 (.leaf (-380189825890821730154338299133985294560323193128138529806284696004976271113243491085194533621628508683723183637941913470390496707568547925328592155475320187770936713481501627923465600))
(.leaf (489235596168208917194124052644878559572739561949631635597455921868127329861524822048294323415638993780302987501732694851464659556388969372390138444985045593357179003430991522471008952956800)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1554322182 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 159550533603134374665600 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 1487957601175728859616645474035200 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (2975915202351457719233290948070401 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 2975915202351457719233290948070401 1487957601175728859616645474035200 (List.ofFn fun j : Fin 6 => B i j) =
      1487957601175728859616645474035200 * geometricEncoding 2975915202351457719233290948070401 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1554322182 159550533603134374665600 1487957601175728859616645474035200 2975915202351457719233290948070401 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2648313665769600))
(.leaf (-5375813730652800)))
(.node 1 (.leaf (107165724710400))
(.leaf (15644556950400))))
(.node 2 (.node 1 (.leaf (1317464243136000))
(.leaf (-393845403945600)))
(.node 1 (.leaf (-5375813730652800))
(.node 1 (.leaf (11179432407628800))
(.leaf (-840694125744000))))))
(.node 4 (.node 2 (.node 1 (.leaf (872285827132800))
(.leaf (-2208514856860800)))
(.node 1 (.leaf (-104094038304000))
(.leaf (107165724710400))))
(.node 2 (.node 1 (.leaf (-840694125744000))
(.leaf (1479685417200000)))
(.node 1 (.leaf (-2138159547417600))
(.node 1 (.leaf (-1050113946412800))
(.leaf (2122125076944000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (15644556950400))
(.leaf (872285827132800)))
(.node 1 (.leaf (-2138159547417600))
(.leaf (3104405043811200))))
(.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (-3104382443644800)))
(.node 1 (.leaf (1317464243136000))
(.node 1 (.leaf (-2208514856860800))
(.leaf (-1050113946412800))))))
(.node 4 (.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (1482708023827200)))
(.node 1 (.leaf (-1796372868614400))
(.leaf (-393845403945600))))
(.node 2 (.node 1 (.leaf (-104094038304000))
(.leaf (2122125076944000)))
(.node 1 (.leaf (-3104382443644800))
(.node 1 (.leaf (-1796372868614400))
(.leaf (3160788154963200))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2648313665769600))
(.leaf (-5375813730652800)))
(.node 1 (.leaf (107165724710400))
(.leaf (15644556950400))))
(.node 2 (.node 1 (.leaf (1317464243136000))
(.leaf (-393845403945600)))
(.node 1 (.leaf (-5375813730652800))
(.node 1 (.leaf (11179432407628800))
(.leaf (-840694125744000))))))
(.node 4 (.node 2 (.node 1 (.leaf (872285827132800))
(.leaf (-2208514856860800)))
(.node 1 (.leaf (-104094038304000))
(.leaf (107165724710400))))
(.node 2 (.node 1 (.leaf (-840694125744000))
(.leaf (1479685417200000)))
(.node 1 (.leaf (-2138159547417600))
(.node 1 (.leaf (-1050113946412800))
(.leaf (2122125076944000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (15644556950400))
(.leaf (872285827132800)))
(.node 1 (.leaf (-2138159547417600))
(.leaf (3104405043811200))))
(.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (-3104382443644800)))
(.node 1 (.leaf (1317464243136000))
(.node 1 (.leaf (-2208514856860800))
(.leaf (-1050113946412800))))))
(.node 4 (.node 2 (.node 1 (.leaf (1608729546988800))
(.leaf (1482708023827200)))
(.node 1 (.leaf (-1796372868614400))
(.leaf (-393845403945600))))
(.node 2 (.node 1 (.leaf (-104094038304000))
(.leaf (2122125076944000)))
(.node 1 (.leaf (-3104382443644800))
(.node 1 (.leaf (-1796372868614400))
(.leaf (3160788154963200))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-17113182603373043849661103867032201225842073791212930383951259334883668396890625405233362882522912000))
(.node 1 (.leaf (-4523044493023750031256531127145178423818819869511552853844756726803724440657137361760768533595200000))
(.leaf (92209566457086151753744161033348628982700250434270640917735880608915887200788107526186592830666480000))))
(.node 1 (.leaf (-134890144956818932573217951642407342726745706684316752830498438401285846338812935159628509623642739200))
(.node 1 (.leaf (-78055136904909726128610675875683651715159329760611834042707926768552220243417229567128598285283856000))
(.leaf (137341059015976658842988720773796484287094880299660397864689844549512401918854071823174199885114198400)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 11179432407628800 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 67076594445772800 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (134153188891545601 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 134153188891545601 67076594445772800 (List.ofFn fun j : Fin 6 => NG i j) =
      67076594445772800 * geometricEncoding 134153188891545601 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 11179432407628800 67076594445772800 134153188891545601 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (134153188891545601))
(.leaf (17997078089770714037905534662451201))))
(.node 1 (.leaf (2414365416472907279009943516935959190440176128716801))
(.node 1 (.leaf (323894819769305093370542826779085695018172165901317484534261706342401))
(.leaf (43451522937504704572307776324347837908882364184005643520373706573059471796709411328001)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 11179432407628800 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 67076594445772800 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (134153188891545601 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 134153188891545601 67076594445772800 (List.ofFn fun j : Fin 6 => H i j) =
      67076594445772800 * geometricEncoding 134153188891545601 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    11179432407628800 1 67076594445772800 134153188891545601 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas188.Middle.Block09
