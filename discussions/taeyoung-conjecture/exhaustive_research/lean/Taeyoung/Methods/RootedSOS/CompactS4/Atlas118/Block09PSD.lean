import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (3052544619310778790739269599113252388281461917395132392879818588061242250382710653628002748836357047406307446850422))
(.node 1 (.leaf (734673606286888931158559788213565898967457452271340017710348646900860313146137448578398498467361650702051208367258))
(.leaf (-591218082157306501570802873325424134695095424456733346932355682890456243679579394376920187636370477978458015056095))))
(.node 1 (.leaf (2692289740716517290318959161158345824885393416833745920102709546578432905643531529615174374115248360489922770491177))
(.node 1 (.leaf (2645923745954679804604254545654639903072354978470780459569793245233947770612052941882645227243836810083874546313047))
(.leaf (18858173453585560287872969148269802464421003818794898749201666666692905440853051158873513770526182494095915137738846)))))

private theorem GP_left_bound : ∀ i j : Fin 6, (G i j).natAbs ≤ 3064001655168 := by decide +kernel
private theorem GP_right_bound : ∀ i j : Fin 6, (P i j).natAbs ≤ 89613145 := by decide +kernel
private theorem GP_result_bound : ∀ i j : Fin 6, (K i j).natAbs ≤ 1647448947628859900160 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (3294897895257719800321 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 3294897895257719800321 1647448947628859900160 (List.ofFn fun j : Fin 6 => K i j) =
      1647448947628859900160 * geometricEncoding 3294897895257719800321 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_matrix_product_exact G P K
    3064001655168 89613145 1647448947628859900160 3294897895257719800321 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (4683737667051618402390658379062625120564570483533881398930016874045909249693419256009048060248008436212487324840224188894516044612066566835185347573067275968))
(.node 1 (.leaf (762690148981606357201112268751872692024674006983493376616241822435274385059538802032958376486433066765460961492069387984703940390428243346485513602067570240))
(.leaf (-51770568334456267221797615963679598180143583398454921465698175194820897391787153241491858812708719972086533832386068499012484180092632096150670898716657207424))))
(.node 1 (.leaf (2442096377252759901938333941486045195380514510320467364547216304072478606738159350111031765423722467092985064677726744566643825338694383559739940134892904704))
(.node 1 (.leaf (-29700332887522910327164030838282466290308195055336150023447729880023243804496704083765387744550251863236125594006902072850603932673881378815623749364165667392))
(.leaf (4864211611980468913220929899207084562377692425916445318048753276268714607789857923411724345488731997353687481309829313932173256464402760871390262357331926314416270656)))))

private theorem PK_left_bound : ∀ i j : Fin 6, (Pt i j).natAbs ≤ 89613145 := by decide +kernel
private theorem PK_right_bound : ∀ i j : Fin 6, (K i j).natAbs ≤ 125943133087721928384 := by decide +kernel
private theorem PK_result_bound : ∀ i j : Fin 6, (B i j).natAbs ≤ 67716961482865937327730046080 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (135433922965731874655460092161 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 135433922965731874655460092161 67716961482865937327730046080 (List.ofFn fun j : Fin 6 => B i j) =
      67716961482865937327730046080 * geometricEncoding 135433922965731874655460092161 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_matrix_product_exact Pt K B
    89613145 125943133087721928384 67716961482865937327730046080 135433922965731874655460092161 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09
