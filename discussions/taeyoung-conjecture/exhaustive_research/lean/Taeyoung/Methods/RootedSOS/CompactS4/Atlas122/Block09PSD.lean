import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (141814480968856671190592982966065849450791190814567096987052463077943200380184536328932831968465361673126584398769379))
(.node 1 (.leaf (80367756797532072952070890756519565996554460654120026494155093053859737190956731588083576627916770043898378062533035))
(.leaf (-7200652759651290693984415480214385995516396181428335961558226273750766861231401432597789768356920321409408425029625))))
(.node 1 (.leaf (22577944876994286027691097077959747260517269054284361350820854392470011763817702674754184739885023249067061645384000))
(.node 1 (.leaf (100555995316859543571613644400407517760758293521139315229548131893762734437642394828581817684144301810693256587627500))
(.leaf (326478295486570084818419842313224530555065254811951750719412480861240807670335652367945819806326835959418259656709375)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 6271468478208 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 79358754 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 2986175545085178196992 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (5972351090170356393985 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 5972351090170356393985 2986175545085178196992 (List.ofFn fun j : Fin 6 => K i j) =
      2986175545085178196992 * geometricEncoding 5972351090170356393985 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    6271468478208 79358754 2986175545085178196992 5972351090170356393985 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-916634011509297557863904085812656944814979846637622363978345639166086461775092486821859681646184033788017759492685574464888047644293624526395915372389989891328))
(.node 1 (.leaf (1940255108967622118998255035384040254213909970598135147008205461725894777276736796280747650842098930833566374799918410945675637899597097492018787198795036375040))
(.leaf (-1200882825286356056799345080320953639107835626002643535510365366190351814714177125208540214299128133538465608517858988598129493960222975987211952775715593501184))))
(.node 1 (.leaf (134074918695195105847036582681681525471391640352414701447503022754184821469981424455352413932518268137729888100881182363929422048531313308295014226379849486208))
(.node 1 (.leaf (-4523954223159429912329566241542782127359193537566492509614691726733009891046013422552767849841955713991441886858045110975763743567107865769139058110818556416))
(.leaf (180673346685365851674995332744337004327906444283357486261758143820122034176207010233317838529660570362253781713877795745713088021970735615733729978247704414926932390016)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 79358754 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 248936894756015019264 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 118531930754798915604462222336 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (237063861509597831208924444673 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 237063861509597831208924444673 118531930754798915604462222336 (List.ofFn fun j : Fin 6 => B i j) =
      118531930754798915604462222336 * geometricEncoding 237063861509597831208924444673 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    79358754 248936894756015019264 118531930754798915604462222336 237063861509597831208924444673 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09
