import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (100976949824256))
(.leaf (-205129683055872)))
(.node 1 (.leaf (-9703627974144))
(.leaf (22206312311040))))
(.node 2 (.node 1 (.leaf (81110831369472))
(.leaf (-15770980433664)))
(.node 1 (.leaf (-205129683055872))
(.node 1 (.leaf (417011789521152))
(.leaf (19722032036352))))))
(.node 4 (.node 2 (.node 1 (.leaf (-45132977212416))
(.leaf (-164852815541760)))
(.node 1 (.leaf (32053554918144))
(.leaf (-9703627974144))))
(.node 2 (.node 1 (.leaf (19722032036352))
(.leaf (1031161985280)))
(.node 1 (.leaf (-2135008419840))
(.node 1 (.leaf (-7798336342272))
(.leaf (1516287714048)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22206312311040))
(.leaf (-45132977212416)))
(.node 1 (.leaf (-2135008419840))
(.leaf (4984085240064))))
(.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (-3469956765696)))
(.node 1 (.leaf (81110831369472))
(.node 1 (.leaf (-164852815541760))
(.leaf (-7798336342272))))))
(.node 4 (.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (65283068717568)))
(.node 1 (.leaf (-12674373937920))
(.leaf (-15770980433664))))
(.node 2 (.node 1 (.leaf (32053554918144))
(.leaf (1516287714048)))
(.node 1 (.leaf (-3469956765696))
(.node 1 (.leaf (-12674373937920))
(.leaf (2562587331840))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (42990513))
(.leaf (1599645713)))
(.node 1 (.leaf (43196292))
(.leaf (-98374273))))
(.node 2 (.node 1 (.leaf (-340667866))
(.leaf (62926668)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (787440133))
(.leaf (-43895304))))))
(.node 4 (.node 2 (.node 1 (.leaf (99991293))
(.leaf (346149308)))
(.node 1 (.leaf (-63932167))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (1377429097)))
(.node 1 (.leaf (4728977))
(.node 1 (.leaf (16366962))
(.leaf (-3014115)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (1373060238))))
(.node 2 (.node 1 (.leaf (-37461384))
(.leaf (6912068)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (1311733540)))
(.node 1 (.leaf (25270805))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (1376008522))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (4341050874120025283328))
(.leaf (-9576480296448)))
(.node 1 (.leaf (88989952015872))
(.leaf (-36762865431552))))
(.node 2 (.node 1 (.leaf (9730021086720))
(.leaf (68292017547264)))
(.node 1 (.leaf (-8818630306099344942336))
(.node 1 (.leaf (237000893729552916480))
(.leaf (-180926474162688))))))
(.node 4 (.node 2 (.node 1 (.leaf (74770347967488))
(.leaf (-19751852312064)))
(.node 1 (.leaf (-138858771329280))
(.leaf (-417163944569601295872))))
(.node 2 (.node 1 (.leaf (7552640348955270144))
(.leaf (135487183081054927104)))
(.node 1 (.leaf (3555287417088))
(.node 1 (.leaf (-924705123840))
(.leaf (-6533668915200)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (954660758089825163520))
(.leaf (-17285288936565719808)))
(.node 1 (.leaf (-466613832656526336))
(.leaf (135918282203811903744))))
(.node 2 (.node 1 (.leaf (2154815571456))
(.leaf (15060735585792)))
(.node 1 (.leaf (3486996250430093819136))
(.node 1 (.leaf (-63129317586157580544))
(.leaf (-1703776378051595520))))))
(.node 4 (.node 2 (.node 1 (.leaf (3881618000374265856))
(.leaf (142272805046775192576)))
(.node 1 (.leaf (54874497883392))
(.leaf (-678002539356177829632))))
(.node 2 (.node 1 (.leaf (12274307348616990720))
(.leaf (330403401868084992)))
(.node 1 (.leaf (-754036660495980288))
(.node 1 (.leaf (-2612883691903785984))
(.leaf (135627056279920818432))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (186624004037518310503241067264))
(.leaf (-411697800678691597824)))
(.node 1 (.leaf (3825723689007721422336))
(.leaf (-1580454444252386866176))))
(.node 2 (.node 1 (.leaf (418298598018910287360))
(.leaf (2935908868161881106432)))
(.node 1 (.leaf (-411697800678691597824))
(.node 1 (.leaf (186623999960542362741536764416))
(.leaf (-116371635622749600768))))))
(.node 4 (.node 2 (.node 1 (.leaf (69612662796978659328))
(.leaf (11185307163215566848)))
(.node 1 (.leaf (-99936262143197515008))
(.leaf (3825723689007721422336))))
(.node 2 (.node 1 (.leaf (-116371635622749600768))
(.leaf (186624000032269703411194308864)))
(.node 1 (.leaf (27069712338292128000))
(.node 1 (.leaf (13598650107062217216))
(.leaf (45544237845063671808)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-1580454444252386866176))
(.leaf (69612662796978659328)))
(.node 1 (.leaf (27069712338292128000))
(.leaf (186624000021033941040574633728))))
(.node 2 (.node 1 (.leaf (22121669617991041536))
(.leaf (45553950335662089984)))
(.node 1 (.leaf (418298598018910287360))
(.node 1 (.leaf (11185307163215566848))
(.leaf (13598650107062217216))))))
(.node 4 (.node 2 (.node 1 (.leaf (22121669617991041536))
(.leaf (186623999962083772460253978624)))
(.node 1 (.leaf (-21176433674676467712))
(.leaf (2935908868161881106432))))
(.node 2 (.node 1 (.leaf (-99936262143197515008))
(.leaf (45544237845063671808)))
(.node 1 (.leaf (45553950335662089984))
(.node 1 (.leaf (-21176433674676467712))
(.leaf (186623999940392730398307820032))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (2068243485670244142182626423276881779895413632678574427361995630556047542548330706578532585936990026645196402411687149663713602120247))
(.node 1 (.leaf (-2101291743629778004911866888959488393864265876929099386698571636556886659170518530623585833177397481979450431866678257837681905791569))
(.leaf (-99066483447224123206631360634589100709593290437691266095225415745776380971740177838886711817113424819645001866064752912741790796151))))
(.node 1 (.leaf (227182529567746270744352493693271390324002833191689583286068145198644105492269345747647053808455855115264477547670951519480323309386))
(.node 1 (.leaf (830588675359277469124692904379110677071807493903465119102389997606920588574453470273457941134265809119180195927607694838874361429305))
(.leaf (45225986887677587210940130557742785840637538996567599093854784041386299791855465394614682747789646724409754970429521798757890839023946)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 417011789521152 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1599645713 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 4002426728267814717728256 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (8004853456535629435456513 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 8004853456535629435456513 4002426728267814717728256 (List.ofFn fun j : Fin 6 => K i j) =
      4002426728267814717728256 * geometricEncoding 8004853456535629435456513 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    417011789521152 1599645713 4002426728267814717728256 8004853456535629435456513 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (9492943332227277608260308650737836767504455122899507966925073752198500961539664326254121582452428310287183266095807755686875567437279491313364673230865010703405933451423814912))
(.node 1 (.leaf (-19302086755589948904034655780520537654757778714062641316450707186396483821494839777350222597304562351883230815828604410537303862132260407047080410789190615331780704671856019968))
(.leaf (-908213741387895822782712096816898881940810233404846487868304533468134504920196899108846968324754478939295813506176069915634326342967776094219348896023465219994870094790731264))))
(.node 1 (.leaf (2093520071487624679454412537384175031878297575843748972972026944276592638538340201461374171906623045827334509716043582944788591671769036718769842500653229720231719435518076672))
(.node 1 (.leaf (7627838765064215201777742821433981536178886226576054858659406728687294158942586854969938708379943289022838061672506598636805771806337725146703838291694151584834397831418802176))
(.leaf (18852861664118012007711590215619508966534295661650864214384613104033260481629252033750875406136709365353745616191548681766067783312872887909992764098409744114787693075237922169114112)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1599645713 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 8818630306099344942336 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 84640104982102169334696087633408 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (169280209964204338669392175266817 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 169280209964204338669392175266817 84640104982102169334696087633408 (List.ofFn fun j : Fin 6 => B i j) =
      84640104982102169334696087633408 * geometricEncoding 169280209964204338669392175266817 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1599645713 8818630306099344942336 84640104982102169334696087633408 169280209964204338669392175266817 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (100976949824256))
(.leaf (-205129683055872)))
(.node 1 (.leaf (-9703627974144))
(.leaf (22206312311040))))
(.node 2 (.node 1 (.leaf (81110831369472))
(.leaf (-15770980433664)))
(.node 1 (.leaf (-205129683055872))
(.node 1 (.leaf (417011789521152))
(.leaf (19722032036352))))))
(.node 4 (.node 2 (.node 1 (.leaf (-45132977212416))
(.leaf (-164852815541760)))
(.node 1 (.leaf (32053554918144))
(.leaf (-9703627974144))))
(.node 2 (.node 1 (.leaf (19722032036352))
(.leaf (1031161985280)))
(.node 1 (.leaf (-2135008419840))
(.node 1 (.leaf (-7798336342272))
(.leaf (1516287714048)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22206312311040))
(.leaf (-45132977212416)))
(.node 1 (.leaf (-2135008419840))
(.leaf (4984085240064))))
(.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (-3469956765696)))
(.node 1 (.leaf (81110831369472))
(.node 1 (.leaf (-164852815541760))
(.leaf (-7798336342272))))))
(.node 4 (.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (65283068717568)))
(.node 1 (.leaf (-12674373937920))
(.leaf (-15770980433664))))
(.node 2 (.node 1 (.leaf (32053554918144))
(.leaf (1516287714048)))
(.node 1 (.leaf (-3469956765696))
(.node 1 (.leaf (-12674373937920))
(.leaf (2562587331840))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (100976949824256))
(.leaf (-205129683055872)))
(.node 1 (.leaf (-9703627974144))
(.leaf (22206312311040))))
(.node 2 (.node 1 (.leaf (81110831369472))
(.leaf (-15770980433664)))
(.node 1 (.leaf (-205129683055872))
(.node 1 (.leaf (417011789521152))
(.leaf (19722032036352))))))
(.node 4 (.node 2 (.node 1 (.leaf (-45132977212416))
(.leaf (-164852815541760)))
(.node 1 (.leaf (32053554918144))
(.leaf (-9703627974144))))
(.node 2 (.node 1 (.leaf (19722032036352))
(.leaf (1031161985280)))
(.node 1 (.leaf (-2135008419840))
(.node 1 (.leaf (-7798336342272))
(.leaf (1516287714048)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (22206312311040))
(.leaf (-45132977212416)))
(.node 1 (.leaf (-2135008419840))
(.leaf (4984085240064))))
(.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (-3469956765696)))
(.node 1 (.leaf (81110831369472))
(.node 1 (.leaf (-164852815541760))
(.leaf (-7798336342272))))))
(.node 4 (.node 2 (.node 1 (.leaf (17846139843072))
(.leaf (65283068717568)))
(.node 1 (.leaf (-12674373937920))
(.leaf (-15770980433664))))
(.node 2 (.node 1 (.leaf (32053554918144))
(.leaf (1516287714048)))
(.node 1 (.leaf (-3469956765696))
(.node 1 (.leaf (-12674373937920))
(.leaf (2562587331840))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-49488761978387849171949592332537903319623797144690614045489266903086258935186624686625446144))
(.node 1 (.leaf (100582887448087203964151895636092920790895169959840086654960440882487676719882751887635830528))
(.leaf (4758055600088128070964758292397212507801418430997767013011887257053718747745758150414272256))))
(.node 1 (.leaf (-10888597901388053187397844978974225747186688946802311538011592762707110167676959825682780160))
(.node 1 (.leaf (-39771723620931636494595319227960327705205786277645668653328913276720199344722668345353142528))
(.leaf (8041305678343196012970910338292606221290709815335934247229292358797629119534563639588987136)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 417011789521152 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 2502070737126912 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (5004141474253825 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 5004141474253825 2502070737126912 (List.ofFn fun j : Fin 6 => NG i j) =
      2502070737126912 * geometricEncoding 5004141474253825 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 417011789521152 2502070737126912 5004141474253825 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (5004141474253825))
(.leaf (25041431894347245095340527130625))))
(.node 1 (.leaf (125310867917205576789819305453707587340180890625))
(.node 1 (.leaf (627073311319231456047111272915448410084263869795441695812890625))
(.leaf (3137963564570246666256361543020286303057788358292743962917006108827988212890625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 417011789521152 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 2502070737126912 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (5004141474253825 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 5004141474253825 2502070737126912 (List.ofFn fun j : Fin 6 => H i j) =
      2502070737126912 * geometricEncoding 5004141474253825 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    417011789521152 1 2502070737126912 5004141474253825 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas168.Lower.Block09
