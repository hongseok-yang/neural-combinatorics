import Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-571131093796876495988102020208216624382517859541262267838087052643325182715235072))
(.node 1 (.leaf (-614210448239367831554708726815751394572976996561316616118437059744308627158965632))
(.leaf (572441298743859560501590465257150776238111090624055950041062249761584004270790272))))
(.node 1 (.leaf (-2143485256581596512129001958109034861002719375019864900845691968349693846666954752))
(.node 1 (.leaf (-2945547512342735791306903763691485752106996967527440844919458871501013559260933248))
(.leaf (15025268568369185068024668578630524828981381381158198481492696777629714008301927168)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 6271468478208 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 37628810869248 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (75257621738497 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 75257621738497 37628810869248 (List.ofFn fun j : Fin 6 => NG i j) =
      37628810869248 * geometricEncoding 75257621738497 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 6271468478208 37628810869248 75257621738497 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (75257621738497))
(.leaf (5663709629734696216651819009))))
(.node 1 (.leaf (426237316951256668853100435848635971689473))
(.node 1 (.leaf (32077606769949529714821333454039571897283207908493742081))
(.leaf (2414084396569112263193679841605141312655852317869581913202552346592257)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 6271468478208 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 37628810869248 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (75257621738497 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 75257621738497 37628810869248 (List.ofFn fun j : Fin 6 => H i j) =
      37628810869248 * geometricEncoding 75257621738497 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    6271468478208 1 37628810869248 75257621738497 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas122.Block09
