import Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-34452294857757336616415791053521323483880142527139261584788871728529933677045807872))
(.node 1 (.leaf (18629895027721798432342293121047122065897099476505370141228135866141419414295187712))
(.leaf (89016754464452247540623341174021970065372067891479145036263496922815866573756412544))))
(.node 1 (.leaf (-113042554662567473684236758971191731778089244792237927608290813428691846569713700224))
(.node 1 (.leaf (-112740581565861742814075265373178630794314464559343315907386642540183441558453062144))
(.leaf (406594908936251537211437231517083029720300061554526172336124423822198003245648203136)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 11232978486912 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 67397870921472 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (134795741842945 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 134795741842945 67397870921472 (List.ofFn fun j : Fin 6 => NG i j) =
      67397870921472 * geometricEncoding 134795741842945 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 11232978486912 67397870921472 134795741842945 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (134795741842945))
(.leaf (18169892018989873505046273025))))
(.node 1 (.leaf (2449224073905945698556398533404417140058625))
(.node 1 (.leaf (330144975981751901721319767471185022807889546442842650625))
(.leaf (44502136953181506849622330350703972688489431109713342963662986256090625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 11232978486912 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 67397870921472 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (134795741842945 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 134795741842945 67397870921472 (List.ofFn fun j : Fin 6 => H i j) =
      67397870921472 * geometricEncoding 134795741842945 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    11232978486912 1 67397870921472 134795741842945 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas124.Block09
