import Taeyoung.Methods.RootedSOS.PackedMatrix
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09
set_option maxRecDepth 1000000
private def GData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (213874456700160))
(.leaf (-383840824522752)))
(.node 1 (.leaf (15469394370048))
(.leaf (-17689014565632))))
(.node 2 (.node 1 (.leaf (62514047434752))
(.leaf (-67946580815616)))
(.node 1 (.leaf (-383840824522752))
(.node 1 (.leaf (697432166327808))
(.leaf (-57326982653952))))))
(.node 4 (.node 2 (.node 1 (.leaf (68465386017792))
(.leaf (-92643396005376)))
(.node 1 (.leaf (90366663826944))
(.leaf (15469394370048))))
(.node 2 (.node 1 (.leaf (-57326982653952))
(.leaf (110057265768960)))
(.node 1 (.leaf (-136338735762432))
(.node 1 (.leaf (-67609142975232))
(.leaf (111486325798656)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-17689014565632))
(.leaf (68465386017792)))
(.node 1 (.leaf (-136338735762432))
(.leaf (169413698762496))))
(.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (-138956767218432)))
(.node 1 (.leaf (62514047434752))
(.node 1 (.leaf (-92643396005376))
(.leaf (-67609142975232))))))
(.node 4 (.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (66330953892864)))
(.node 1 (.leaf (-97087148218368))
(.leaf (-67946580815616))))
(.node 2 (.node 1 (.leaf (90366663826944))
(.leaf (111486325798656)))
(.node 1 (.leaf (-138956767218432))
(.node 1 (.leaf (-97087148218368))
(.leaf (146404497344256))))))))

def G (i j : Nat) : Int := GData.get (i * 6 + j)

private def PData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (29539578))
(.leaf (265113068)))
(.node 1 (.leaf (1020186668))
(.leaf (-139771762))))
(.node 2 (.node 1 (.leaf (-159600362))
(.leaf (148982081)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (147719861))
(.leaf (575149084))))))
(.node 4 (.node 2 (.node 1 (.leaf (-76341939))
(.leaf (77353326)))
(.node 1 (.leaf (-53489064))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (166382030)))
(.node 1 (.leaf (737462705))
(.node 1 (.leaf (237081292))
(.leaf (-290055664)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.leaf (611545919))))
(.node 2 (.node 1 (.leaf (-295056213))
(.leaf (360840097)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (0))))))
(.node 4 (.node 2 (.node 1 (.leaf (0))
(.leaf (878827234)))
(.node 1 (.leaf (217783039))
(.leaf (0))))
(.node 2 (.node 1 (.leaf (0))
(.leaf (0)))
(.node 1 (.leaf (0))
(.node 1 (.leaf (0))
(.leaf (811510386))))))))

def P (i j : Nat) : Int := PData.get (i * 6 + j)

private def KData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (6317761195901998932480))
(.leaf (137986256913408)))
(.node 1 (.leaf (-36659887054848))
(.leaf (-100244869781760))))
(.node 2 (.node 1 (.leaf (-96942471881472))
(.leaf (78734992702464)))
(.node 1 (.leaf (-11338495975574145478656))
(.node 1 (.leaf (1263364053996259671552))
(.leaf (55596040574976))))))
(.node 4 (.node 2 (.node 1 (.leaf (187111321920000))
(.leaf (175226225107968)))
(.node 1 (.leaf (-121506836285952))
(.leaf (456959381606793759744))))
(.node 2 (.node 1 (.leaf (-4367195307645847953408))
(.leaf (1121659631341922128896)))
(.node 1 (.leaf (-33605923769856))
(.node 1 (.leaf (-11478322183680))
(.leaf (-67592369583360)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-522526025504622583296))
(.leaf (5424108384468190887936)))
(.node 1 (.leaf (-1352608399863134788608))
(.leaf (305167640156758460160))))
(.node 2 (.node 1 (.leaf (13623365562624))
(.leaf (84596623181568)))
(.node 1 (.leaf (1846638580294556614656))
(.node 1 (.leaf (2888021328042534566400))
(.leaf (-756713050267015070208))))))
(.node 4 (.node 2 (.node 1 (.leaf (102456526476425195520))
(.leaf (212355706035014583552)))
(.node 1 (.leaf (71601970920192))
(.leaf (-2007113323836192450048))))
(.node 2 (.node 1 (.leaf (-4664575480588004335104))
(.leaf (1205429243548523263488)))
(.node 1 (.leaf (-163189530912952023552))
(.node 1 (.leaf (-56989357452415703808))
(.leaf (229971075127581809664))))))))

def K (i j : Nat) : Int := KData.get (i * 6 + j)

private def BData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (186623999631720377821909693440))
(.leaf (4076055799021654861824)))
(.node 1 (.leaf (-1082917593127872774144))
(.leaf (-2961191150018142497280))))
(.node 2 (.node 1 (.leaf (-2863639709655548898816))
(.leaf (2325798458263866120192)))
(.node 1 (.leaf (4076055799021654861824))
(.node 1 (.leaf (186623999030683885351372310016))
(.leaf (-1506375743758422755328))))))
(.node 4 (.node 2 (.node 1 (.leaf (1063833486445769080320))
(.leaf (183677476502968676352)))
(.node 1 (.leaf (2924702507597256506880))
(.leaf (-1082917593127872774144))))
(.node 2 (.node 1 (.leaf (-1506375743758422755328))
(.leaf (186624001007804414890203494400)))
(.node 1 (.leaf (-242996095284394383360))
(.node 1 (.leaf (-28001058731725584384))
(.leaf (-806311393261882338816)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-2961191150018142497280))
(.leaf (1063833486445769080320)))
(.node 1 (.leaf (-242996095284394383360))
(.leaf (186623999892571665868916647680))))
(.node 2 (.node 1 (.leaf (39189405545721600768))
(.leaf (159006780308916951552)))
(.node 1 (.leaf (-2863639709655548898816))
(.node 1 (.leaf (183677476502968676352))
(.leaf (-28001058731725584384))))))
(.node 4 (.node 2 (.node 1 (.leaf (39189405545721600768))
(.leaf (186624000044299789074884752128)))
(.node 1 (.leaf (-24974781801672842496))
(.leaf (2325798458263866120192))))
(.node 2 (.node 1 (.leaf (2924702507597256506880))
(.leaf (-806311393261882338816)))
(.node 1 (.leaf (159006780308916951552))
(.node 1 (.leaf (-24974781801672842496))
(.leaf (186623999900107097410094653440))))))))

def B (i j : Nat) : Int := BData.get (i * 6 + j)

def Pt (i j : Nat) : Int := P j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (6760025802317411836367850638135096318558928178964440990379847296155049276460870246104664446697885022171108439122949680236013661861367))
(.node 1 (.leaf (-2427053309731976357813376727162170082246416790500262553033073412864123586994192485630426542507118808052282693736808625122438514549788))
(.leaf (-13161205425425018925323887262703658497907950472476042054546029210251537710935172107221382699920134502704190761381980580272645089075109))))
(.node 1 (.leaf (16373031909996731162749186087636014303019642464030429237327474732475258423809988300194350218814087885220366550769010595040945912183691))
(.node 1 (.leaf (9881852589688951870250504249544919196724633355179221052819795662286841178588104952038799455611812621915345500427855180613426106077665))
(.leaf (36822087001245220717865016247463718058729962476124199835804379613768733120845574898425558970346959723265701109767594912626726431910514)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 697432166327808 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 1020186668 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 4269065987531929435582464 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (8538131975063858871164929 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 8538131975063858871164929 4269065987531929435582464 (List.ofFn fun j : Fin 6 => K i j) =
      4269065987531929435582464 * geometricEncoding 8538131975063858871164929 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    697432166327808 1020186668 4269065987531929435582464 8538131975063858871164929 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (4057415575207087842528453510192735391522900720747266418994803355485068036167408460348805940534208009360853048616823903750856701618516980679949063804152145937874717421027100160))
(.node 1 (.leaf (-6261558083885246971803206380493961947461561391103000061813448379498420932303765050382438470529797136606318715624879552518219414657448570641943981949328177798923331652834614784))
(.leaf (-3483207703454782425338197847850447823344609280462519944457490157963963368155593487274585873877555941724742236673426977588724673682041282110844469829859306125163640863742771456))))
(.node 1 (.leaf (4359480387632997502346066362450179988492380647700026069917493338770446866241497906196594187686282405457338578005659783763595564029645746198567936758276709625613907814634554624))
(.node 1 (.leaf (3689832716756195910017025604678788774143635165021096579030397199266259276360080728832361370089985950829280598181474411202740314083636991752194145540422724968532034600190617600))
(.leaf (11850997758974440114876722531183910834371285517419414061557215870797446551795534020391845523950078690870187049939475216100121916329294641642442631792816140997678703947469730307733760)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 1020186668 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 11338495975574145478656 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 69404294576714381176903978549248 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (138808589153428762353807957098497 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 138808589153428762353807957098497 69404294576714381176903978549248 (List.ofFn fun j : Fin 6 => B i j) =
      69404294576714381176903978549248 * geometricEncoding 138808589153428762353807957098497 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    1020186668 11338495975574145478656 69404294576714381176903978549248 138808589153428762353807957098497 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09
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
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (213874456700160))
(.leaf (-383840824522752)))
(.node 1 (.leaf (15469394370048))
(.leaf (-17689014565632))))
(.node 2 (.node 1 (.leaf (62514047434752))
(.leaf (-67946580815616)))
(.node 1 (.leaf (-383840824522752))
(.node 1 (.leaf (697432166327808))
(.leaf (-57326982653952))))))
(.node 4 (.node 2 (.node 1 (.leaf (68465386017792))
(.leaf (-92643396005376)))
(.node 1 (.leaf (90366663826944))
(.leaf (15469394370048))))
(.node 2 (.node 1 (.leaf (-57326982653952))
(.leaf (110057265768960)))
(.node 1 (.leaf (-136338735762432))
(.node 1 (.leaf (-67609142975232))
(.leaf (111486325798656)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-17689014565632))
(.leaf (68465386017792)))
(.node 1 (.leaf (-136338735762432))
(.leaf (169413698762496))))
(.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (-138956767218432)))
(.node 1 (.leaf (62514047434752))
(.node 1 (.leaf (-92643396005376))
(.leaf (-67609142975232))))))
(.node 4 (.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (66330953892864)))
(.node 1 (.leaf (-97087148218368))
(.leaf (-67946580815616))))
(.node 2 (.node 1 (.leaf (90366663826944))
(.leaf (111486325798656)))
(.node 1 (.leaf (-138956767218432))
(.node 1 (.leaf (-97087148218368))
(.leaf (146404497344256))))))))

def NG (i j : Nat) : Int := NGData.get (i * 6 + j)

private def HData : PackedTable :=
(.node 18 (.node 9 (.node 4 (.node 2 (.node 1 (.leaf (213874456700160))
(.leaf (-383840824522752)))
(.node 1 (.leaf (15469394370048))
(.leaf (-17689014565632))))
(.node 2 (.node 1 (.leaf (62514047434752))
(.leaf (-67946580815616)))
(.node 1 (.leaf (-383840824522752))
(.node 1 (.leaf (697432166327808))
(.leaf (-57326982653952))))))
(.node 4 (.node 2 (.node 1 (.leaf (68465386017792))
(.leaf (-92643396005376)))
(.node 1 (.leaf (90366663826944))
(.leaf (15469394370048))))
(.node 2 (.node 1 (.leaf (-57326982653952))
(.leaf (110057265768960)))
(.node 1 (.leaf (-136338735762432))
(.node 1 (.leaf (-67609142975232))
(.leaf (111486325798656)))))))
(.node 9 (.node 4 (.node 2 (.node 1 (.leaf (-17689014565632))
(.leaf (68465386017792)))
(.node 1 (.leaf (-136338735762432))
(.leaf (169413698762496))))
(.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (-138956767218432)))
(.node 1 (.leaf (62514047434752))
(.node 1 (.leaf (-92643396005376))
(.leaf (-67609142975232))))))
(.node 4 (.node 2 (.node 1 (.leaf (84420153020160))
(.leaf (66330953892864)))
(.node 1 (.leaf (-97087148218368))
(.leaf (-67946580815616))))
(.node 2 (.node 1 (.leaf (90366663826944))
(.leaf (111486325798656)))
(.node 1 (.leaf (-138956767218432))
(.node 1 (.leaf (-97087148218368))
(.leaf (146404497344256))))))))

def H (i j : Nat) : Int := HData.get (i * 6 + j)

def Nt (i j : Nat) : Int := N j i

end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09



namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2789868321770096680441186628977327841941963290777159147209527702328728893350111709554613919488))
(.node 1 (.leaf (3710430896279870901656325122244414224512970318755025236823191797614039043076874592836509223424))
(.leaf (4577598532886394794927494309796281800398194058430398516693565943700978701794836150148629803008))))
(.node 1 (.leaf (-5705527464439937893740049606353834679919430780565198209876731439404586004154409764537482033152))
(.node 1 (.leaf (-3986372176702257015266777190571515490917941357699330178875449730498680124719825223112780664320))
(.leaf (6011329258992546067161894985146993157408176532031967347985405845597247881771639546449107208704)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 697432166327808 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 4184592997966848 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (8369185995933697 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 8369185995933697 4184592997966848 (List.ofFn fun j : Fin 6 => NG i j) =
      4184592997966848 * geometricEncoding 8369185995933697 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 697432166327808 4184592997966848 8369185995933697 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (8369185995933697))
(.leaf (70043274234532707737818820087809))))
(.node 1 (.leaf (586205189832994677991741886542993971894481999873))
(.node 1 (.leaf (4906060265493953475089518554367359539188256213692665538470420481))
(.leaf (41059730869178750932611687934334609746161148071769840920741977546619579786848257)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 697432166327808 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 4184592997966848 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (8369185995933697 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 8369185995933697 4184592997966848 (List.ofFn fun j : Fin 6 => H i j) =
      4184592997966848 * geometricEncoding 8369185995933697 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    697432166327808 1 4184592997966848 8369185995933697 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas151.Lower.Block09
