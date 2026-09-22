import Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2327913162356937845574284590117179547023291961338345554512079597255318888685867814464))
(.node 1 (.leaf (-24988583205172182878229549565590586623555723494337754556122373622641924108511070010688))
(.leaf (50144709940270279896089120816057508784528141874824714164800200222580668318539154282560))))
(.node 1 (.leaf (-93801313522870097052218614450604857751326293385671980405360041978567775774151399731232))
(.node 1 (.leaf (-107339721822659912611588210484624411422517955225089914700360464732566807139999968877248))
(.leaf (200314328219160832796715216909039822844426231123107080145552369799327256027533638769536)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 31106128485600 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 186636770913600 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (373273541827201 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 373273541827201 186636770913600 (List.ofFn fun j : Fin 6 => NG i j) =
      186636770913600 * geometricEncoding 373273541827201 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 31106128485600 186636770913600 373273541827201 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (373273541827201))
(.leaf (139333137028223174461743494401))))
(.node 1 (.leaf (52009373552419591552479001326703624253001601))
(.node 1 (.leaf (19413723074125615868502562705164542058901952169646318348801))
(.leaf (7246629171931325254681525520572495974244576613842267704353826558787536001)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 31106128485600 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 186636770913600 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (373273541827201 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 373273541827201 186636770913600 (List.ofFn fun j : Fin 6 => H i j) =
      186636770913600 * geometricEncoding 373273541827201 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    31106128485600 1 186636770913600 373273541827201 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas199.Block09
