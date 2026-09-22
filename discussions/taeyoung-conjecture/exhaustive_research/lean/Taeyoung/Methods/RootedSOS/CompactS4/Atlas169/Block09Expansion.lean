import Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-2025544146091876748941142179808790443523692159628449333681048258114096369844465216))
(.node 1 (.leaf (-4861399683739291709947092913277100478780406313056585020778383175157373094689656624))
(.leaf (-6312829848595541005605746188074682821367516858025727848493084517106871278177047632))))
(.node 1 (.leaf (-66919793304048076128430886277859594378158510501658303058646368574885826580475615504))
(.node 1 (.leaf (-77663286351554142422996067944685814820122939593813713909718992032404729691596164640))
(.leaf (187203002160631128133302262171796424723636612856804718349568283438656804049347772352)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 10116668941344 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 60700013648064 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (121400027296129 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 121400027296129 60700013648064 (List.ofFn fun j : Fin 6 => NG i j) =
      60700013648064 * geometricEncoding 121400027296129 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 10116668941344 60700013648064 121400027296129 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (121400027296129))
(.leaf (14737966627500866278658384641))))
(.node 1 (.leaf (1789189550868043428187721449426614092354689))
(.node 1 (.leaf (217207660313329258128164777374671850427693542731504698881))
(.leaf (26369015890966487637575053313969459117246158030632785310318024761931649)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 10116668941344 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 60700013648064 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (121400027296129 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 121400027296129 60700013648064 (List.ofFn fun j : Fin 6 => H i j) =
      60700013648064 * geometricEncoding 121400027296129 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    10116668941344 1 60700013648064 121400027296129 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas169.Block09
