import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-13601713186684122560311811643247523275998594014776389955565883162163403649876121634304))
(.node 1 (.leaf (-8030493688519919794801388235995657693164553330518688407389915916557549731122665377856))
(.leaf (63756957475446027404057343643456784116819863943407586111200773835080330029566946463616))))
(.node 1 (.leaf (-153463687064115616111994298781827312724679842448354796327832760272532026802033647025952))
(.node 1 (.leaf (-242069266770701391229108866807325667776056983919808057157388000003983309281149407942112))
(.leaf (447135322161090441407605014158589193483829370758579613960700731777161558879241040038816)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 36645836592672 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 219875019556032 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (439750039112065 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 439750039112065 219875019556032 (List.ofFn fun j : Fin 6 => NG i j) =
      219875019556032 * geometricEncoding 439750039112065 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 36645836592672 219875019556032 439750039112065 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (439750039112065))
(.leaf (193380096899062697253628564225))))
(.node 1 (.leaf (85038905174857740739721815177185639824874625))
(.node 1 (.leaf (37395861876690878218164989789315102241059878240834949850625))
(.leaf (16444831722904194148593668035804577574534665790386795844434556579385290625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 36645836592672 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 219875019556032 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (439750039112065 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 439750039112065 219875019556032 (List.ofFn fun j : Fin 6 => H i j) =
      219875019556032 * geometricEncoding 439750039112065 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    36645836592672 1 219875019556032 439750039112065 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09
