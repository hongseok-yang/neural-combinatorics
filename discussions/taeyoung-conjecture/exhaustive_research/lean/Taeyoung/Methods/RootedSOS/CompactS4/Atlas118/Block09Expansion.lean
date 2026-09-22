import Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-5714607754450525208511027132004484905329851982097675376190179197395254863270464))
(.node 1 (.leaf (-641239766519695701855796737971825426582177120996404240621365654680679675592704))
(.leaf (9947750963628650387263687758986691106940750853409343129048578842158007900121920))))
(.node 1 (.leaf (-24920578460111502359997931780654120529665673726911572251369023661266059596452608))
(.node 1 (.leaf (-19387479679556262526376263850656176502069994618973593182667982550215089963240256))
(.leaf (155258911257037860241144275217200950929710603872277989030166239430394282808659392)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 3064001655168 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 18384009931008 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (36768019862017 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 36768019862017 18384009931008 (List.ofFn fun j : Fin 6 => NG i j) =
      18384009931008 * geometricEncoding 36768019862017 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 3064001655168 18384009931008 36768019862017 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (36768019862017))
(.leaf (1351887284573676611719308289))))
(.node 1 (.leaf (49706218530413169945898141641252464358913))
(.node 1 (.leaf (1827599230191988889352181361183540156512861572624107521))
(.leaf (67197204795506026743897588412141587385279603143360459438886191929857)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 3064001655168 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 18384009931008 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (36768019862017 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 36768019862017 18384009931008 (List.ofFn fun j : Fin 6 => H i j) =
      18384009931008 * geometricEncoding 36768019862017 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    3064001655168 1 18384009931008 36768019862017 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas118.Block09
