import Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (168798199311656109892798225769004071531426302793282683842688945060361794470361587769203060628511175445501836640442787004))
(.node 1 (.leaf (101430292782188259266818885592845636845506205635722810751375489491100976034074351374911857203603471958822268988813472376))
(.leaf (75056215846769907437025473025345552754109472604796907320213729528759256248410673379208040430047512617070226181983071769))))
(.node 1 (.leaf (37070234169874067453619852720831932780262979178947177392048916360595346287250531983940258397280104770092998949349975162))
(.node 1 (.leaf (126967159648590076454863155339331700111317051976168111882336062895847047025108493244232676302740808195755699261624902837))
(.leaf (124848057400953114232336008464544117173919049275362873886127586992857871214454760772015798034789993495087465664329557038)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 68851722425472 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 27562245 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 11386248252977121027840 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (22772496505954242055681 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 22772496505954242055681 11386248252977121027840 (List.ofFn fun j : Fin 6 => K i j) =
      11386248252977121027840 * geometricEncoding 22772496505954242055681 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    68851722425472 27562245 11386248252977121027840 22772496505954242055681 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-3428038044250737981274135892141007499912962264151614809307567335220904270222129203451228348619062677003689308992471657365799018847290532038240850065512163379968))
(.node 1 (.leaf (5310592465660456018821611693688052233200832027765970335307651122854976521983908084002333207653891801508101647699474808824499862643957137704603355722996155323712))
(.leaf (14577688776596315237824832357511019309728378525049869587068311255791529387087908231857817926906696137736023675454806892349298150766843949569155628204029243839808))))
(.node 1 (.leaf (-14015166375117220251565173567699612262838747951224548097458380007439672794609560232781055190229258004303793408701808088989569573104009789139434570282103967727296))
(.node 1 (.leaf (-12853969506661735606976802233669693752874206479840304933210250472398555960841093841992416793613772313789481667371641252458184822752721474712204466917890803473728))
(.leaf (203699516008352799905678078623578816093235494185811012773211030706059344832976214081953491990576555293356058394354603643939317427197498893089806902910601445312929459104)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 27562245 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 669910250805842149344 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 110785382764332412509275503680 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (221570765528664825018551007361 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 221570765528664825018551007361 110785382764332412509275503680 (List.ofFn fun j : Fin 6 => B i j) =
      110785382764332412509275503680 * geometricEncoding 221570765528664825018551007361 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    27562245 669910250805842149344 110785382764332412509275503680 221570765528664825018551007361 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas185.Block09
