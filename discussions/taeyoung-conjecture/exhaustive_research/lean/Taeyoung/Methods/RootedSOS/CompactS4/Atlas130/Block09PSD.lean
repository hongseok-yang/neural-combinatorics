import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (492035151566432897098421541772541646169086945796750417446791630603518123848448665500166284418010897073229476727368815333972993))
(.node 1 (.leaf (867115935006980071376097175070049925991772233765214379490553929999723808197952359609626710059054779092135251013650874067426898))
(.leaf (404590340511292640154835226600458721523887320366485335243026932457780108552390546360877513129885453025812114529520100974635059))))
(.node 1 (.leaf (559576700685394433643662694789982232551207930722354993680786740321792290214634207854983729983004596008235420642721418139708415))
(.node 1 (.leaf (2761153824944751373433288657252963544422317399827242895258153591690557630937525327538192615418090252171860455960495472398527337))
(.leaf (2332241316179646252247392370733160029666152308209300819853737054249281133469347933517921905110366957434873534165119862507002188)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 155912901754464 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 222729900 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 208358790098889547641600 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (416717580197779095283201 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 416717580197779095283201 208358790098889547641600 (List.ofFn fun j : Fin 6 => K i j) =
      208358790098889547641600 * geometricEncoding 416717580197779095283201 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    155912901754464 222729900 208358790098889547641600 416717580197779095283201 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (59334324097157363654154982781300227746395743594004888771208629914788802009813618024024213412954981062534333463156412294837207471826692113025869697610105533209536395552))
(.node 1 (.leaf (-76286644021006560826771462762524495376095995852798299272183949902846418369265580418433037940228210994279678207222111105225282314230037651002385399632291503884276515936))
(.leaf (107637420299163740049398004686615102507695467073271372911783583503405127918662423877671539122440192341433094534061927166904145656954555584449259099301239511524155495936))))
(.node 1 (.leaf (-69651330000359822030614680506384709126542355723792544849748031218758858358228515507147588155973861853233726085584797392472096798012751648856772682654198026510105836640))
(.node 1 (.leaf (-152207799880097259674613570463071002335800121093804213760924209038797525521976241710318952195331498401115347336826865011534719576873762689824952795510765247950089314432))
(.leaf (415630227728016675559108678161599113955878134551074822260281633882266855481389977263192953393419390162112249364489858971078605461964161273937811347879253217473533152419977216)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 222729900 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 1891990663694369048448 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 2528417347953482692343509171200 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (5056834695906965384687018342401 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 5056834695906965384687018342401 2528417347953482692343509171200 (List.ofFn fun j : Fin 6 => B i j) =
      2528417347953482692343509171200 * geometricEncoding 5056834695906965384687018342401 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    222729900 1891990663694369048448 2528417347953482692343509171200 5056834695906965384687018342401 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09
