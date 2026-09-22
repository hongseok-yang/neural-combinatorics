import Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (563387110613069556827593074231197066418675140292071468862139454628872860018159726842024001326670236164578711821037))
(.node 1 (.leaf (-671161697420028075024506581970986876659936759214965562363374508710592490355030851226919390755970821540173169844475))
(.leaf (-445851967550995042037229645688866206479900380864329351325374981210704568085410616162513091377471776572191546715066))))
(.node 1 (.leaf (5088470812801413578729195234511058777558566927634549238393236176491964886047411300823075448493684398002196423056198))
(.node 1 (.leaf (4955535816459874349793421135176549556871630913236667467000817333727893329530226123055364793324303317025556087434431))
(.leaf (68910608280404324549718903172002579326786447191050056653924953907693970370796255043757528201687955817665307839452112)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 7936658699616 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 48169645 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 2293836192279986137920 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (4587672384559972275841 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 4587672384559972275841 2293836192279986137920 (List.ofFn fun j : Fin 6 => K i j) =
      2293836192279986137920 * geometricEncoding 4587672384559972275841 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    7936658699616 48169645 2293836192279986137920 4587672384559972275841 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-24122098989655232364719521204347797931967070750118377205498613927875853355092777964252305458409542767996175859166251988459726135522191381924035145621397440224))
(.node 1 (.leaf (152966965750811556092588833103891426869629815903011179766542309686619741917077691474074236068708025298447982893590437604299198720010919773204281608442549507712))
(.leaf (-100811866831084026662130475380715066523359373559266310850510514722051482177990460429861035595015132858403473609079694688723887579166173420707663432023991997888))))
(.node 1 (.leaf (156617800120025765450573812330999653439639145000022342089225088920867219022677794583102067579728776540900160695717694124127205092526096997073638910423414863456))
(.node 1 (.leaf (162221953643148322441781853519824981891433085508877284657766866264480026608358396151887851293022898574753454605597921654071711971606330189244483798422270506688))
(.leaf (13979688443307004569383037489129816191491923900701261447951615759256968742126512088539675437527986790797034105936481017187321428047092468801945443039610674743186051232)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 48169645 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 248346691509592910592 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 71776631801649627586400279040 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (143553263603299255172800558081 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 143553263603299255172800558081 71776631801649627586400279040 (List.ofFn fun j : Fin 6 => B i j) =
      71776631801649627586400279040 * geometricEncoding 143553263603299255172800558081 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    48169645 248346691509592910592 71776631801649627586400279040 143553263603299255172800558081 (fun i => PKEnc.get i)
    PK_left_bound PK_right_bound PK_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    PK_encoded PK_product i j

private theorem upper : ∀ i j : Fin 6, j < i → P i j = 0 := by decide +kernel
private theorem diagonal : ∀ i : Fin 6, P i i ≠ 0 := by decide +kernel
private theorem symm : ∀ i j : Fin 6, B i j = B j i := by decide +kernel
private theorem dominant : ∀ i : Fin 6,
    (∑ j : Fin 6, if i = j then 0 else (B i j).natAbs : Nat) ≤ (B i i).toNat := by decide +kernel
private theorem positive : ∀ i : Fin 6, 0 ≤ B i i := by decide +kernel

theorem gram_nonneg (x : Fin 6 → Real) :
    0 ≤ matrixQuadratic (fun i j => (G i j : Real)) x :=
  matrixQuadratic_nonneg_of_integer_congruence
    (fun i j => G i j) (fun i j => P i j) (fun i j => K i j) (fun i j => B i j)
    upper diagonal GP_exact PK_exact symm dominant positive x

#print axioms gram_nonneg
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas157.Block09
