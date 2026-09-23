import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3247264858273920000))
(.leaf (-6401542434376320000)))
(.node 1 (.leaf (181341509469120000))
(.leaf (-578329330550400000))))
(.node 2 (.node 1 (.leaf (934165899216000000))
(.leaf (-448485449037120000)))
(.node 1 (.leaf (-6401542434376320000))
(.node 1 (.leaf (12706808054212800000))
(.leaf (-850753916337600000))))))
(.node 4 (.node 2 (.node 1 (.leaf (1704750374986560000))
(.leaf (-1481471881971840000)))
(.node 1 (.leaf (442061362702080000))
(.leaf (181341509469120000))))
(.node 2 (.node 1 (.leaf (-850753916337600000))
(.leaf (3100060039348800000)))
(.node 1 (.leaf (-3521832303052800000))
(.node 1 (.leaf (-1997816256817920000))
(.leaf (2477399526423360000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-578329330550400000))
(.leaf (1704750374986560000)))
(.node 1 (.leaf (-3521832303052800000))
(.leaf (4065706479700800000))))
(.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (-2854709773597440000)))
(.node 1 (.leaf (934165899216000000))
(.node 1 (.leaf (-1481471881971840000))
(.leaf (-1997816256817920000))))))
(.node 4 (.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (2023933423881600000)))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (-448485449037120000))))
(.node 2 (.node 1 (.leaf (442061362702080000))
(.leaf (2477399526423360000)))
(.node 1 (.leaf (-2854709773597440000))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (2738112848982720000))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (28110996))
(.leaf (338497161)))
(.node 1 (.leaf (1037864933))
(.leaf (-697770350))))
(.node 2 (.node 1 (.leaf (-385873079))
(.leaf (-8149031)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (171707045))
(.leaf (529115063))))))
(.node 4 (.node 2 (.node 1 (.leaf (-379862390))
(.leaf (-121875778)))
(.node 1 (.leaf (73205111))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (93360876)))
(.node 1 (.leaf (407564754))
(.node 1 (.leaf (-700816064))
(.leaf (114191136)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (414588137))))
(.node 2 (.node 1 (.leaf (-719083380))
(.leaf (80268866)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (197030478)))
(.node 1 (.leaf (907311135))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (728623832))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (91283849441878732024320000))
(.leaf (691924955166720000)))
(.node 1 (.leaf (-1717284107911680000))
(.leaf (79536563124480000))))
(.node 2 (.node 1 (.leaf (-4087848401366400000))
(.leaf (2779697789447040000)))
(.node 1 (.leaf (-179953733766582994014720000))
(.node 1 (.leaf (14944522313666563548480000))
(.leaf (3493367786082240000))))))
(.node 4 (.node 2 (.node 1 (.leaf (-380848152991680000))
(.leaf (8328322755624960000)))
(.node 1 (.leaf (-5571228212573760000))
(.leaf (5097690447320394443520000))))
(.node 2 (.node 1 (.leaf (-84696854869754781223680000))
(.leaf (27485602461019578648960000)))
(.node 1 (.leaf (1403408833833600000))
(.node 1 (.leaf (-1873890012392640000))
(.leaf (734453538192000000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-16257413497784972198400000))
(.leaf (96954812837243164900800000)))
(.node 1 (.leaf (-27019978781445312822720000))
(.leaf (6189466382642509560000000))))
(.node 2 (.node 1 (.leaf (2599652696952960000))
(.leaf (-1143238380894720000)))
(.node 1 (.leaf (26260333856197379136000000))
(.node 1 (.leaf (61833345683654706163200000))
(.leaf (-848935585122076995840000))))))
(.node 4 (.node 2 (.node 1 (.leaf (22589111200601804633280000))
(.leaf (13023771854956416892800000)))
(.node 1 (.leaf (443642704369920000))
(.leaf (-12607372663940684171520000))))
(.node 2 (.node 1 (.leaf (-75906000950627931462720000))
(.leaf (-273804751538517418560000)))
(.node 1 (.leaf (-28810715183131800695040000))
(.node 1 (.leaf (-16217715289078903406400000))
(.leaf (3521817328530673402560000))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2566079926525255268420731422720000))
(.leaf (19450699646991845253120000)))
(.node 1 (.leaf (-48274566688368804833280000))
(.leaf (2235852007846004782080000))))
(.node 2 (.node 1 (.leaf (-114913490059417264934400000))
(.leaf (78140073440354583651840000)))
(.node 1 (.leaf (19450699646991845253120000))
(.node 1 (.leaf (2566079999630881691201216723520000))
(.leaf (18540064487852238640320000))))))
(.node 4 (.node 2 (.node 1 (.leaf (-38471410130575512784320000))
(.leaf (46306611713704089052800000)))
(.node 1 (.leaf (-15699323235873374285760000))
(.leaf (-48274566688368804833280000))))
(.node 2 (.node 1 (.leaf (18540064487852238640320000))
(.leaf (2566079989233104331172209752640000)))
(.node 1 (.leaf (12059193407455638417600000))
(.node 1 (.leaf (-10941500756089256031360000))
(.leaf (5699319028262438293440000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (2235852007846004782080000))
(.leaf (-38471410130575512784320000)))
(.node 1 (.leaf (12059193407455638417600000))
(.leaf (2566079997755497431642862401600000))))
(.node 2 (.node 1 (.leaf (2816469678180147010560000))
(.leaf (2073669762622844453760000)))
(.node 1 (.leaf (-114913490059417264934400000))
(.node 1 (.leaf (46306611713704089052800000))
(.leaf (-10941500756089256031360000))))))
(.node 4 (.node 2 (.node 1 (.leaf (2816469678180147010560000))
(.leaf (2566080000200018036011367249280000)))
(.node 1 (.leaf (1165243475682942036480000))
(.leaf (78140073440354583651840000))))
(.node 2 (.node 1 (.leaf (-15699323235873374285760000))
(.leaf (5699319028262438293440000)))
(.node 1 (.leaf (2073669762622844453760000))
(.node 1 (.leaf (1165243475682942036480000))
(.leaf (2566080001647400119094848888000000))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-808907273292242299915942940495767638808468964200916221195237428979481042776035273013413152290165682336733187310502595627172705283351398350095157434519370))
(.node 1 (.leaf (7266648848196298799727463745114957630560446186397401963936043811987652824532310417012744038237485023258209157694112451427181930920927326344281021379489051))
(.leaf (11335094989318804679311470143526472172795471109554264383471136264999154335518585464921067191825729912377476328491792229188155186379176104898651887568700702))))
(.node 1 (.leaf (7967827036898052788298956665055921649811245814106865082139082720785241608285630157140103507720067924324239057465328015781346357793818488230299156620573623))
(.node 1 (.leaf (90063539608640530123366151597393381589505517125264433144514101519085260086390259495963555581377890779342300527572076323976994333354178195506592324169941613))
(.leaf (72326282376256126702334010389826902699842271539905974587862889589100486579468073713947985352474604550839172360219875612786470256101865146277647653336623832)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 12706808054212800000 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1037864933 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 79127702938976568238454400000 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (158255405877953136476908800001 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 158255405877953136476908800001 79127702938976568238454400000 (List.ofFn fun j : Fin 6 => K i j) =
      79127702938976568238454400000 * geometricEncoding 158255405877953136476908800001 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    12706808054212800000 1037864933 79127702938976568238454400000 158255405877953136476908800001 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (157185439667927437462742802653293859466083128915007699843295259642375956919944936572028835116866210753962566312803593039369161945022959884501547127570629538696273299478571699948365801588603898484480000))
(.node 1 (.leaf (-315039987227522485587362819463547028137630229011488160999621614718303768777093535677952463307881690950261369656451431766453257538451775643268325891273199509611748823269602358533072933636299579124480000))
(.leaf (41531637991243569874430596638118427690412251772670865369181877236784481851592597325849301864963038066489873443087693266001206432311629943744469535292064883966731693965270616841045366401908489101760000))))
(.node 1 (.leaf (-64647469314257188647171994889061965322263475794125311930178058450901566835116423445755696307623001442269117363270172780582555310084186576155306605664180464527019628000996652924425745843577462502080000))
(.node 1 (.leaf (25086962261363784775238301111176787933036275629917557439676634880080552629780561903530402785873440141557471018658712480945448152368431285527758873467383516714181692357574643168713705913692393399360000))
(.leaf (199150572165379837060978143683176616266150401203116340854495816975853711699525005542619084456244979903564383483307937977941550945545758906024665293565204547893322623179002702839651349423421136214705048320000)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1037864933 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 179953733766582994014720000 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 1120606019032526980332160642882560000 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (2241212038065053960664321285765120001 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 2241212038065053960664321285765120001 1120606019032526980332160642882560000 (List.ofFn fun j : Fin 6 => B i j) =
      1120606019032526980332160642882560000 * geometricEncoding 2241212038065053960664321285765120001 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1037864933 179953733766582994014720000 1120606019032526980332160642882560000 2241212038065053960664321285765120001 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3247264858273920000))
(.leaf (-6401542434376320000)))
(.node 1 (.leaf (181341509469120000))
(.leaf (-578329330550400000))))
(.node 2 (.node 1 (.leaf (934165899216000000))
(.leaf (-448485449037120000)))
(.node 1 (.leaf (-6401542434376320000))
(.node 1 (.leaf (12706808054212800000))
(.leaf (-850753916337600000))))))
(.node 4 (.node 2 (.node 1 (.leaf (1704750374986560000))
(.leaf (-1481471881971840000)))
(.node 1 (.leaf (442061362702080000))
(.leaf (181341509469120000))))
(.node 2 (.node 1 (.leaf (-850753916337600000))
(.leaf (3100060039348800000)))
(.node 1 (.leaf (-3521832303052800000))
(.node 1 (.leaf (-1997816256817920000))
(.leaf (2477399526423360000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-578329330550400000))
(.leaf (1704750374986560000)))
(.node 1 (.leaf (-3521832303052800000))
(.leaf (4065706479700800000))))
(.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (-2854709773597440000)))
(.node 1 (.leaf (934165899216000000))
(.node 1 (.leaf (-1481471881971840000))
(.leaf (-1997816256817920000))))))
(.node 4 (.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (2023933423881600000)))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (-448485449037120000))))
(.node 2 (.node 1 (.leaf (442061362702080000))
(.leaf (2477399526423360000)))
(.node 1 (.leaf (-2854709773597440000))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (2738112848982720000))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (3247264858273920000))
(.leaf (-6401542434376320000)))
(.node 1 (.leaf (181341509469120000))
(.leaf (-578329330550400000))))
(.node 2 (.node 1 (.leaf (934165899216000000))
(.leaf (-448485449037120000)))
(.node 1 (.leaf (-6401542434376320000))
(.node 1 (.leaf (12706808054212800000))
(.leaf (-850753916337600000))))))
(.node 4 (.node 2 (.node 1 (.leaf (1704750374986560000))
(.leaf (-1481471881971840000)))
(.node 1 (.leaf (442061362702080000))
(.leaf (181341509469120000))))
(.node 2 (.node 1 (.leaf (-850753916337600000))
(.leaf (3100060039348800000)))
(.node 1 (.leaf (-3521832303052800000))
(.node 1 (.leaf (-1997816256817920000))
(.leaf (2477399526423360000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-578329330550400000))
(.leaf (1704750374986560000)))
(.node 1 (.leaf (-3521832303052800000))
(.leaf (4065706479700800000))))
(.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (-2854709773597440000)))
(.node 1 (.leaf (934165899216000000))
(.node 1 (.leaf (-1481471881971840000))
(.leaf (-1997816256817920000))))))
(.node 4 (.node 2 (.node 1 (.leaf (2233316239577280000))
(.leaf (2023933423881600000)))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (-448485449037120000))))
(.node 2 (.node 1 (.leaf (442061362702080000))
(.leaf (2477399526423360000)))
(.node 1 (.leaf (-2854709773597440000))
(.node 1 (.leaf (-2293922119737600000))
(.leaf (2738112848982720000))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-36968934646436844564219096267984288658675880962617035342668706971195272310141462956468748857837677236041848115004800000))
(.node 1 (.leaf (36439393212276502008509374451408963973163997668221425541331036834880926254735212718190300298874022176836060711215680000))
(.leaf (204213584592525712523038274329798890167670333237671840395698134292394238044104675071249537937218355309871862791032960000))))
(.node 1 (.leaf (-235315503058680881856854514192835268687136674607144336566911232911458118283030712290828233503264719526212495304936000000))
(.node 1 (.leaf (-189089427785596247781286044379916619335379841196917560448733522217723862538940658923271435287541156455607321479852480000))
(.leaf (225704346007071965571524648516835347424145843139224095502384645742778098844072458202682003616835550160641271243736000000)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 12706808054212800000 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 76240848325276800000 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (152481696650553600001 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 152481696650553600001 76240848325276800000 (List.ofFn fun j : Fin 6 => NG i j) =
      76240848325276800000 * geometricEncoding 152481696650553600001 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 12706808054212800000 76240848325276800000 152481696650553600001 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (152481696650553600001))
(.leaf (23250667813431448957336149866261107200001))))
(.node 1 (.leaf (3545301276450444565207255913942376959286981660508831660800001))
(.node 1 (.leaf (540593553770537155739762208036429210525112693650424603954566119669624362214400001))
(.leaf (82430622277283782880972190272133060542597950379251557201626529196230932626429533380833212852768000001)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 12706808054212800000 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 76240848325276800000 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (152481696650553600001 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 152481696650553600001 76240848325276800000 (List.ofFn fun j : Fin 6 => H i j) =
      76240848325276800000 * geometricEncoding 152481696650553600001 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    12706808054212800000 1 76240848325276800000 152481696650553600001 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas171.Middle.Block09
