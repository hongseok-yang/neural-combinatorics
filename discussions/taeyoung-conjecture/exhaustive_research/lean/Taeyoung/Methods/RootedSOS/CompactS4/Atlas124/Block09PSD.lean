import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (8873825805358185322758377762671223408104443950475867651259297936087948570392494825596402205187386691620861330542676082))
(.node 1 (.leaf (5154262927234115478218924434217141444283895676755611969680268084531097015197243182733787801356215587079939779879268596))
(.leaf (-1529844693089838291578756744566049190132456805734448691954088042221003715881424728954942057163380007466282418870622584))))
(.node 1 (.leaf (1299105790171041667482383964908215453493161617721758235067877818886229076541745200771753973376540906261359694982868913))
(.node 1 (.leaf (7783064830026965894274287103773420765659425945754369397534154235433669746560072732107190736237306688904949857044979948))
(.leaf (12291213196016589059641727259030976949269983032459389076836682249822311655992495130944875206405018078990508579356047028)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 11232978486912 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 93075324 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 6273078672926184956928 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (12546157345852369913857 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 12546157345852369913857 6273078672926184956928 (List.ofFn fun j : Fin 6 => K i j) =
      6273078672926184956928 * geometricEncoding 12546157345852369913857 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    11232978486912 93075324 6273078672926184956928 12546157345852369913857 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2197548916597480957224951798305446931070234078947298084616748336818120199941879647683745289138516994944729116707486286814184411782131414156075300817382345070336))
(.node 1 (.leaf (6204414677091672512300404318746873141431408331936869748007140399370505224958550219345761381278185418431062495134369160130789689886946104121726757440832788335744))
(.leaf (-32248415675621181434380347409302840562090589242362929879724221977329358102390558178253876331035435461872470717153825790584281598158268448578985957174255634689152))))
(.node 1 (.leaf (-5033631915588458892808851857205324162002422276819685506733126871372521007124441108985577551377819517824907948562189480336276958241553749804924799868240591952256))
(.node 1 (.leaf (-6911933016414277823727433583876269573540186228004195510217328212533987999663642020751628614263675691330144478153910635757559825710041933510251040523634900451840))
(.leaf (1972504138458962351876364345356800154693092796150382109781145399556638098299153679173052892751680015857666202992560306059200839385820822740525338792078906436334446118144)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 93075324 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 336710767780823503104 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 188036782832933451229318834176 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (376073565665866902458637668353 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 376073565665866902458637668353 188036782832933451229318834176 (List.ofFn fun j : Fin 6 => B i j) =
      188036782832933451229318834176 * geometricEncoding 376073565665866902458637668353 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    93075324 336710767780823503104 188036782832933451229318834176 376073565665866902458637668353 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09
