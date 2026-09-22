import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-4283778894884488217337579610057435124844691064657184003053816692972652968255500864))
(.node 1 (.leaf (-126717953206938196803264483145893329963736389861101440959840685374628225276043359648))
(.leaf (29473118282466484204152710594686447211397802698577565590938514833507623241023028768))))
(.node 1 (.leaf (-437918603442303945522811140189084884064326592750891051288185105488439724791174095584))
(.node 1 (.leaf (-1010943976190130502787639000579795307609982248631385123579243143763487320334680070720))
(.leaf (3217515921326862164806317944388123270104799898340949388917958323913351450398604869408)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 15951509472672 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 95709056836032 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (191418113672065 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 191418113672065 95709056836032 (List.ofFn fun j : Fin 6 => NG i j) =
      95709056836032 * geometricEncoding 191418113672065 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 15951509472672 95709056836032 191418113672065 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (191418113672065))
(.leaf (36640894241771597678361364225))))
(.node 1 (.leaf (7013730859017547593183342065763137672874625))
(.node 1 (.leaf (1342555130836691023940475124474664503727975123203109850625))
(.leaf (256989370645511820972484325654935810141755863092423404513847392385290625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 15951509472672 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 95709056836032 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (191418113672065 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 191418113672065 95709056836032 (List.ofFn fun j : Fin 6 => H i j) =
      95709056836032 * geometricEncoding 191418113672065 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    15951509472672 1 95709056836032 191418113672065 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09
