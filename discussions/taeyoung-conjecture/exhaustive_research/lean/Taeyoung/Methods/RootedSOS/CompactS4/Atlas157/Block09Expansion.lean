import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-225707515068989733936093532507486830813565136594063707162920875435895333432494400))
(.node 1 (.leaf (696424466233942224498043288822465341797367732418642162625065898417351828973667008))
(.leaf (565651322025394464440795334397283279229125839684007882411224663936101853082806656))))
(.node 1 (.leaf (-4422114624815164863265586476474482904645534191000065534391069642613209478046476416))
(.node 1 (.leaf (-4509207616915674819251400652649880020727362656132509828925319786214995657281136160))
(.leaf (53654175305485189888369233853650572843641132781194925437657305687054064378904644320)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 7936658699616 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 47619952197696 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (95239904395393 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 95239904395393 47619952197696 (List.ofFn fun j : Fin 6 => NG i j) =
      47619952197696 * geometricEncoding 95239904395393 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 7936658699616 47619952197696 95239904395393 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (95239904395393))
(.leaf (9070639389243598880879624449))))
(.node 1 (.leaf (863886828236646310060677160386450245763457))
(.node 1 (.leaf (82276498929697488529105421404019448783967773411278553601))
(.leaf (7836005892052043297862980622386937401517469391823291794623755447960193)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 7936658699616 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 47619952197696 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (95239904395393 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 95239904395393 47619952197696 (List.ofFn fun j : Fin 6 => H i j) =
      47619952197696 * geometricEncoding 95239904395393 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    7936658699616 1 47619952197696 95239904395393 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09
