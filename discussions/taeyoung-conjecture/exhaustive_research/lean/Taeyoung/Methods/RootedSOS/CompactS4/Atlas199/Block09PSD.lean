import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (46460145341484235806386516359341528679199437871804867770862340186896980165059597287677232222800405756547625449064463817))
(.node 1 (.leaf (33949124844041476261551501230302087975341420409788553483010648639294254335003023772686763621100384328701026383171119512))
(.leaf (25424305367633766830437760837063657668229553306775212511481417611551691870073517527079605445435330921973730480836462531))))
(.node 1 (.leaf (16116352685375121920005772546495431269681039917482583975141251568936953016305451302584617232218154048537053518030544311))
(.node 1 (.leaf (55031896383367494363913840964377531197041801270074368973867346960484040502434528334408155761668355681179396305959503306))
(.leaf (47107378931267638052349753348612106815305677846158635315686534552114968261748898591256934900451543853071530190755550815)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 31106128485600 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 45398001 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 8472936312572383713600 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (16945872625144767427201 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 16945872625144767427201 8472936312572383713600 (List.ofFn fun j : Fin 6 => K i j) =
      8472936312572383713600 * geometricEncoding 16945872625144767427201 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    31106128485600 45398001 8472936312572383713600 16945872625144767427201 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (576610557509910857520464168751914548524040348812523745558089960541474075840627586165596512465732685327591337617780747054150780271369519904384040138975436437376))
(.node 1 (.leaf (-2721305828305950626792679759316514621934442131094533484671322453371854193271808302244135520748772233639939108659943811583308956228856590505586790092279894817536))
(.leaf (2654294265616763748041132128074897004569974360872322157803620320775607073112638831459320622460259206646384481419989577724410508301828980635157439574161735447008))))
(.node 1 (.leaf (-4316618801005602208552315104183935343512850399570913369496753015296111201333361146956911186049036602690818122632690805993182369478030493958189377820637342412320))
(.node 1 (.leaf (-2889183896860865689312326825958768020374051523983012483030158008208882967395085893457726907008552592587898912483346400559127399722011520397917662600883840510528))
(.leaf (91812589613164889965451352560869407522713498971630235638509648550737512101059382247782454524454722845691432097864017525546407637143640720100258769651728923836222465696)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 45398001 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 383499733444418351520 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 104460727694456626600339869120 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (208921455388913253200679738241 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 208921455388913253200679738241 104460727694456626600339869120 (List.ofFn fun j : Fin 6 => B i j) =
      104460727694456626600339869120 * geometricEncoding 208921455388913253200679738241 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    45398001 383499733444418351520 104460727694456626600339869120 208921455388913253200679738241 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09
