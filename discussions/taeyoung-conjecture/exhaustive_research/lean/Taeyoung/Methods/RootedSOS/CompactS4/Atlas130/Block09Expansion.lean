import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09ExpansionData

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def NGProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (233941064455476918133765407386428289743420284622830425244687012526151054540908127287230240))
(.node 1 (.leaf (-87437283092962031483062109162652211538773378649469431070753436518884303910852900009820128))
(.leaf (-48272392782480385735313088106331004512208814665655693737097122384550425140662795679316192))))
(.node 1 (.leaf (-671423480664293621724821622825083270859156303831717424803947395935328554839609826299929056))
(.node 1 (.leaf (-1399954379693254555727491751320287248743035734551987443316358724154059506918271956849142720))
(.leaf (1825563566092970838716951462242396881274088604597204051381261482276277303057188850803080896)))))

private theorem NGProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (N i j).natAbs ≤ 1 := by decide +kernel
private theorem NGProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 155912901754464 := by decide +kernel
private theorem NGProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 935477410526784 := by decide +kernel
private theorem NGProduct_encoded : ∀ i : Fin 6,
    NGProductEnc.get i = ∑ j : Fin 6, G i j * (1870954821053569 : Int)^j.1 := by decide +kernel
private theorem NGProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1870954821053569 935477410526784 (List.ofFn fun j : Fin 6 => NG i j) =
      935477410526784 * geometricEncoding 1870954821053569 6 +
        ∑ j : Fin 6, N i j * NGProductEnc.get j := by decide +kernel

theorem NGProduct_exact (i : Fin 6) (j : Fin 6) :
    NG i j = ∑ k : Fin 6, N i k * G k j :=
  packed_rect_product_exact N G NG
    1 155912901754464 935477410526784 1870954821053569 (fun i => NGProductEnc.get i)
    NGProduct_left_bound NGProduct_right_bound NGProduct_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    NGProduct_encoded NGProduct_product i j

private def FullProductEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1))
(.node 1 (.leaf (1870954821053569))
(.leaf (3500471942423592398615167637761))))
(.node 1 (.leaf (6549224856640171403811691036793540510968219009))
(.node 1 (.leaf (12253303819694797976573178463382151477804785904304448913093121))
(.leaf (22925377855292094255207863938165256869856057157045777921807469780711826398849)))))

private theorem FullProduct_left_bound : ∀ (i : Fin 6) (j : Fin 6), (NG i j).natAbs ≤ 155912901754464 := by decide +kernel
private theorem FullProduct_right_bound : ∀ (i : Fin 6) (j : Fin 6), (Nt i j).natAbs ≤ 1 := by decide +kernel
private theorem FullProduct_result_bound : ∀ (i : Fin 6) (j : Fin 6), (H i j).natAbs ≤ 935477410526784 := by decide +kernel
private theorem FullProduct_encoded : ∀ i : Fin 6,
    FullProductEnc.get i = ∑ j : Fin 6, Nt i j * (1870954821053569 : Int)^j.1 := by decide +kernel
private theorem FullProduct_product : ∀ i : Fin 6,
    shiftedEncoding 1870954821053569 935477410526784 (List.ofFn fun j : Fin 6 => H i j) =
      935477410526784 * geometricEncoding 1870954821053569 6 +
        ∑ j : Fin 6, NG i j * FullProductEnc.get j := by decide +kernel

theorem FullProduct_exact (i : Fin 6) (j : Fin 6) :
    H i j = ∑ k : Fin 6, NG i k * Nt k j :=
  packed_rect_product_exact NG Nt H
    155912901754464 1 935477410526784 1870954821053569 (fun i => FullProductEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Block09
