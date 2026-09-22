import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-203937107775390815190921033469289192702999038045056838906000398551342732638044864))
(.node 1 (.leaf (733938972168685103300095458221049539180084707193664189229663497436476453920900352))
(.leaf (236776199620460623779687621128650172506199275351895399968879633619838255899342112))))
(.node 1 (.leaf (-3135005918670287407438998107388690221605251458082895911991108055721246915782102976))
(.node 1 (.leaf (-1984656475352722531511224531792736886904104299523751453517430394547903450967396000))
(.leaf (24437137674476952611393480952183628169514024600869726338003550567505103422182792352)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 6974980025472 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 41849880152832 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (83699760305665 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 83699760305665 41849880152832 (List.ofFn fun j : Fin 6 => NG i j) =
      41849880152832 * geometricEncoding 83699760305665 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 6974980025472 41849880152832 83699760305665 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (83699760305665))
(.leaf (7005649875225774374231092225))))
(.node 1 (.leaf (586371215341809230048178927869712804954625))
(.node 1 (.leaf (49079130174250908058271483002428885030924687916455450625))
(.leaf (4107911431595331508971792953778929946093414099659815999987705315290625)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 6974980025472 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 41849880152832 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (83699760305665 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 83699760305665 41849880152832 (List.ofFn fun j : Fin 6 => H i j) =
      41849880152832 * geometricEncoding 83699760305665 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    6974980025472 1 41849880152832 83699760305665 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09
