import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (46379714422190865408))
(.leaf (-86615894984504320512)))
(.node 1 (.leaf (2818595811834899712))
(.leaf (-3422342281716433152))))
(.node 2 (.node 1 (.leaf (10966172105128230144))
(.leaf (-11460301283280503808)))
(.node 1 (.leaf (-86615894984504320512))
(.node 1 (.leaf (164445800314835305728))
(.leaf (-12301195774881936384))))))
(.node 4 (.node 2 (.node 1 (.leaf (14856149523421350144))
(.leaf (-12793166713441433088)))
(.node 1 (.leaf (9312819794246884608))
(.leaf (2818595811834899712))))
(.node 2 (.node 1 (.leaf (-12301195774881936384))
(.leaf (36718856709338022912)))
(.node 1 (.leaf (-46752208340988648960))
(.node 1 (.leaf (-16420862538751410432))
(.leaf (20686067921778336000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-3422342281716433152))
(.leaf (14856149523421350144)))
(.node 1 (.leaf (-46752208340988648960))
(.leaf (59785407866260581120))))
(.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (-23245487768474383104)))
(.node 1 (.leaf (10966172105128230144))
(.node 1 (.leaf (-12793166713441433088))
(.leaf (-16420862538751410432))))))
(.node 4 (.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (25846301303625116160)))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (-11460301283280503808))))
(.node 2 (.node 1 (.leaf (9312819794246884608))
(.leaf (20686067921778336000)))
(.node 1 (.leaf (-23245487768474383104))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (65440537451009183232))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (26712347))
(.leaf (207246833)))
(.node 1 (.leaf (206418589))
(.leaf (467685522))))
(.node 2 (.node 1 (.leaf (-1252204225))
(.leaf (161188470)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (110973268))
(.leaf (111920528))))))
(.node 4 (.node 2 (.node 1 (.leaf (253325875))
(.leaf (-642071495)))
(.node 1 (.leaf (142561283))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (42738117)))
(.node 1 (.leaf (912769836))
(.node 1 (.leaf (326545920))
(.leaf (4426830)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (678425067))))
(.node 2 (.node 1 (.leaf (270811749))
(.leaf (-121308097)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (225209552)))
(.node 1 (.leaf (1033975551))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (601571550))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (1238911025406466897008792576))
(.leaf (2268227970001179648)))
(.node 1 (.leaf (-13024776715201278720))
(.leaf (9044019070041441024))))
(.node 2 (.node 1 (.leaf (149177328706264320))
(.leaf (1851792008484160512)))
(.node 1 (.leaf (-2313713842541639032515761664))
(.node 1 (.leaf (298217946813598257486340608))
(.leaf (26678565087262437888))))))
(.node 4 (.node 2 (.node 1 (.leaf (-18747886197384368640))
(.leaf (-2626295787121628160)))
(.node 1 (.leaf (-6383706958108795392))
(.leaf (75291309378480547817144064))))
(.node 2 (.node 1 (.leaf (-780958839936593910515970816))
(.leaf (774349038434037457509592320)))
(.node 1 (.leaf (10903533118476235776))
(.node 1 (.leaf (16576807006768732416))
(.leaf (6904910187145910016)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-91418794581981117958527744))
(.leaf (939365863182985191643742976)))
(.node 1 (.leaf (-1041828316244229529683714816))
(.leaf (48780937912446020953115136))))
(.node 2 (.node 1 (.leaf (-21476001615990679296))
(.leaf (-8151022262101694976)))
(.node 1 (.leaf (292932194533905763102387968))
(.node 1 (.leaf (853004920661353399860442368))
(.leaf (130007054889264229148279808))))))
(.node 4 (.node 2 (.node 1 (.leaf (-58658504065349862545625600))
(.leaf (146948560600349837939436288)))
(.node 1 (.leaf (-8376101615850490368))
(.leaf (-306131544603534116054117376))))
(.node 2 (.node 1 (.leaf (-1341637099323055881083781120))
(.leaf (-439239920757778827540741888)))
(.node 1 (.leaf (110658462818158447436192256))
(.node 1 (.leaf (-252573814873164665196062208))
(.leaf (55012955397353045175638016))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (33094221212783359796912129341135872))
(.leaf (60589692609777101166713856)))
(.node 1 (.leaf (-347922355213976732012355840))
(.leaf (241586975673564277013123328))))
(.node 2 (.node 1 (.leaf (3984876568934793589559040))
(.leaf (49465710702455839600241664)))
(.node 1 (.leaf (60589692609777101166713856))
(.node 1 (.leaf (33094220604238248777128170942921728))
(.leaf (261263828526609933808084224))))))
(.node 4 (.node 2 (.node 1 (.leaf (-206169889558142609117238528))
(.leaf (-260532097301746122815128320)))
(.node 1 (.leaf (-324642793962620727417922560))
(.leaf (-347922355213976732012355840))))
(.node 2 (.node 1 (.leaf (261263828526609933808084224))
(.leaf (33094220100754448898302803808500224)))
(.node 1 (.leaf (234576807362687896879627008))
(.node 1 (.leaf (445318079865209930445276672))
(.leaf (-37120700383300021644769536)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (241586975673564277013123328))
(.leaf (-206169889558142609117238528)))
(.node 1 (.leaf (234576807362687896879627008))
(.leaf (33094220504422272668590849047461376))))
(.node 2 (.node 1 (.leaf (-34589023683483467371574016))
(.leaf (21634076047911718380853248)))
(.node 1 (.leaf (3984876568934793589559040))
(.node 1 (.leaf (-260532097301746122815128320))
(.leaf (445318079865209930445276672))))))
(.node 4 (.node 2 (.node 1 (.leaf (-34589023683483467371574016))
(.leaf (33094220596453954649280349776264192)))
(.node 1 (.leaf (-59025944381213115374745600))
(.leaf (49465710702455839600241664))))
(.node 2 (.node 1 (.leaf (-324642793962620727417922560))
(.leaf (-37120700383300021644769536)))
(.node 1 (.leaf (21634076047911718380853248))
(.node 1 (.leaf (-59025944381213115374745600))
(.leaf (33094220595552182948254165995890688))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (14850119927779275876837781038080857481437216667698067090283183735664227145608396018488775025201373970152126555359525295045840947689441152792817128100767472906736))
(.node 1 (.leaf (13134017275603403331596509649013207696447363043007750113901078665800478949849518048750909188484160742554702866145205965885192327236828364958095414406268980075859))
(.leaf (407839074345026860977474345621473978082286785860206810136041773872240376096268192535976249693460454756176380855955265108771568835347329835731859628508439171903))))
(.node 1 (.leaf (-11175984167234054598676925188484693242840703491140637657754087622360911832279983385476176516377631393214389787179186043872751503704350461364842613048112288436081))
(.node 1 (.leaf (95259052553459046922738039429970597791197842521665937767033312646370183223710448340137397855405798423795530641743823855375206713676054803326876730964736970749903))
(.leaf (55422138212739825913769843697052250523146420937070156424928058440270172596235480474339832679335054964159866527375304147801568411670805090785788179101496415971550)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 164445800314835305728 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1252204225 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1235518355626458600070609804800 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (2471036711252917200141219609601 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 2471036711252917200141219609601 1235518355626458600070609804800 (List.ofFn fun j : Fin 6 => K i j) =
      1235518355626458600070609804800 * geometricEncoding 2471036711252917200141219609601 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    164445800314835305728 1252204225 1235518355626458600070609804800 2471036711252917200141219609601 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (94063792362299794049560546476062174714864195108230828373867501983081674800553818768398828712364446827209316006022318955484224020817187165692663854841112487596129574049909806871255968230285438405419732015360))
(.node 1 (.leaf (-324267349172141320484164737595461317602056341750546565382047424807239711125035634135953304292950684613380879820051204190820028449949496433882937503562256070714669360980787142825861785956532539490400096668160))
(.leaf (350742434975562252902606496792493608377801694488575200798986210506624294640845539513212148902614940386473694564660960324273993227707224238469630651486262980656846073877619953441099348237006413296368734264576))))
(.node 1 (.leaf (-414040055303206147522496275336503186081757397917805421025772408074231750696204689008846302653880826374985287867348563117972212277846076382615057287538122643885084519433591266689972552289042759703394066936320))
(.node 1 (.leaf (-425473206272141441299155781316962630588853641110608482614949338812654621044834462897363103752882348744096126206770291787821207046018842724288883557958457930007513707073509257943140281609090842332886170388736))
(.leaf (2794442999010997810360193624933389291541579036483022032432417963526938836184070989174037396865237343667225276589572360374171726948583927305693933700138275566949559037282626381582060649091783451590576804129834983680)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1252204225 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 2313713842541639032515761664 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 17383453494429750809646894808522982400 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (34766906988859501619293789617045964801 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 34766906988859501619293789617045964801 17383453494429750809646894808522982400 (List.ofFn fun j : Fin 6 => B i j) =
      17383453494429750809646894808522982400 * geometricEncoding 34766906988859501619293789617045964801 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1252204225 2313713842541639032515761664 17383453494429750809646894808522982400 34766906988859501619293789617045964801 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (46379714422190865408))
(.leaf (-86615894984504320512)))
(.node 1 (.leaf (2818595811834899712))
(.leaf (-3422342281716433152))))
(.node 2 (.node 1 (.leaf (10966172105128230144))
(.leaf (-11460301283280503808)))
(.node 1 (.leaf (-86615894984504320512))
(.node 1 (.leaf (164445800314835305728))
(.leaf (-12301195774881936384))))))
(.node 4 (.node 2 (.node 1 (.leaf (14856149523421350144))
(.leaf (-12793166713441433088)))
(.node 1 (.leaf (9312819794246884608))
(.leaf (2818595811834899712))))
(.node 2 (.node 1 (.leaf (-12301195774881936384))
(.leaf (36718856709338022912)))
(.node 1 (.leaf (-46752208340988648960))
(.node 1 (.leaf (-16420862538751410432))
(.leaf (20686067921778336000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-3422342281716433152))
(.leaf (14856149523421350144)))
(.node 1 (.leaf (-46752208340988648960))
(.leaf (59785407866260581120))))
(.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (-23245487768474383104)))
(.node 1 (.leaf (10966172105128230144))
(.node 1 (.leaf (-12793166713441433088))
(.leaf (-16420862538751410432))))))
(.node 4 (.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (25846301303625116160)))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (-11460301283280503808))))
(.node 2 (.node 1 (.leaf (9312819794246884608))
(.leaf (20686067921778336000)))
(.node 1 (.leaf (-23245487768474383104))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (65440537451009183232))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (46379714422190865408))
(.leaf (-86615894984504320512)))
(.node 1 (.leaf (2818595811834899712))
(.leaf (-3422342281716433152))))
(.node 2 (.node 1 (.leaf (10966172105128230144))
(.leaf (-11460301283280503808)))
(.node 1 (.leaf (-86615894984504320512))
(.node 1 (.leaf (164445800314835305728))
(.leaf (-12301195774881936384))))))
(.node 4 (.node 2 (.node 1 (.leaf (14856149523421350144))
(.leaf (-12793166713441433088)))
(.node 1 (.leaf (9312819794246884608))
(.leaf (2818595811834899712))))
(.node 2 (.node 1 (.leaf (-12301195774881936384))
(.leaf (36718856709338022912)))
(.node 1 (.leaf (-46752208340988648960))
(.node 1 (.leaf (-16420862538751410432))
(.leaf (20686067921778336000)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-3422342281716433152))
(.leaf (14856149523421350144)))
(.node 1 (.leaf (-46752208340988648960))
(.leaf (59785407866260581120))))
(.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (-23245487768474383104)))
(.node 1 (.leaf (10966172105128230144))
(.node 1 (.leaf (-12793166713441433088))
(.leaf (-16420862538751410432))))))
(.node 4 (.node 2 (.node 1 (.leaf (19223832318660490752))
(.leaf (25846301303625116160)))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (-11460301283280503808))))
(.node 2 (.node 1 (.leaf (9312819794246884608))
(.leaf (20686067921778336000)))
(.node 1 (.leaf (-23245487768474383104))
(.node 1 (.leaf (-40333614514597426176))
(.leaf (65440537451009183232))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-342938464639748058887115444066782388667430902416124854113197056081464381466994495661062909096504097248539959200873027269755136))
(.node 1 (.leaf (278677151914411064447096087144636261107867627655128165529576112416830459005912498478263840460020252610860409657957150758805248))
(.leaf (619010634814440039797971087583179830780494268337106060761779209329723745863003677951371772562581431130182346987779506865913600))))
(.node 1 (.leaf (-695598805657291909519547146326046804204102790995036324874493395905287603964903671614891676828425510430828509283823783376578560))
(.node 1 (.leaf (-1206944520314400705688237599910883586415656238273330584846335275070748022298027236114122401060018262022322002589090387926273536))
(.leaf (1958244978375035463791666877449844347405124902270075303874330602936289535827429002664351313325875105330798636900211482679288064)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 164445800314835305728 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 986674801889011834368 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1973349603778023668737 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1973349603778023668737 986674801889011834368 (List.ofFn fun j : Fin 6 => NG i j) =
      986674801889011834368 * geometricEncoding 1973349603778023668737 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 164445800314835305728 986674801889011834368 1973349603778023668737 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1973349603778023668737))
(.leaf (3894108658730883005258845751936981111175169))))
(.node 1 (.leaf (7684437778775159167393310078938089393000016077748682854835991553))
(.node 1 (.leaf (15164082246002836642061251514784838777900744088650118360873525827412892409496202178561))
(.leaf (29924035691807060926550157696349198822192037383909708308426513573831583233661346036799979418115321187347457)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 164445800314835305728 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 986674801889011834368 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1973349603778023668737 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1973349603778023668737 986674801889011834368 (List.ofFn fun j : Fin 6 => H i j) =
      986674801889011834368 * geometricEncoding 1973349603778023668737 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    164445800314835305728 1 986674801889011834368 1973349603778023668737 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas174.Middle.Block09
