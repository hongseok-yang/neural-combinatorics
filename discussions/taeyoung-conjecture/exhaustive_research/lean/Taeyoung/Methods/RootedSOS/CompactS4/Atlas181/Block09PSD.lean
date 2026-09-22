import Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (314471200818063011352434666732618343186728656205680874746247585873718758801594877388518805553061317301319841213853))
(.node 1 (.leaf (-1871099359571346690796366452709986482290883408665088402386880241547786418934435724801360389570335589317525316669026))
(.leaf (-19888625313607743095223345885745488105205161511686960854040566908952807126597241328139329467762656585680049034477))))
(.node 1 (.leaf (7193686183132242734631971767412750667582831863119342055512441376936151378473614355636708901067294133413270517563780))
(.node 1 (.leaf (3786198199275871126295278072300471175460344566301017478482031053395731814208173097732866866430282012552981379807956))
(.leaf (59113578890352975790403086698028838021120486316233015147800363830797228163786156850677338884092743721293080804529863)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 6974980025472 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 52362790 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 2191376485967909921280 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (4382752971935819842561 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 4382752971935819842561 2191376485967909921280 (List.ofFn fun j : Fin 6 => K i j) =
      2191376485967909921280 * geometricEncoding 4382752971935819842561 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    6974980025472 52362790 2191376485967909921280 4382752971935819842561 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (104454920038962934198809179494652321043582902055473166057867112116291497089105688809215145918999987513741465430535795386175325363888987021871139969211513355328))
(.node 1 (.leaf (-303241817967812210161988423184633487948422866971884599178248792617581572154125220929757754243032919973757114251881196020854928608842800230646007249488011648))
(.leaf (44668866319880133214307562544064958260636033864911114520251697168069339810921154408447545058579312042417627870884426801054761641237995343034243579811887836480))))
(.node 1 (.leaf (139821630692191165436192329447975255596946792094719154743418177441602655778458726325249372030579610898094032995402508826842230172703603939903574990250351911392))
(.node 1 (.leaf (-88510248836036390391902741464801539695637730602462514053267893243689329196482773029987584258176287502251321052533235146980417498177646796507693824357272368352))
(.leaf (14218848004293483618956851751780519326598578879646372155573981381762200372526676778307717604944437143746161644590161728099051493981586143176349384607851968828751005568)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 52362790 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 232706260486532514240 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 73110894297249599227926777600 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (146221788594499198455853555201 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 146221788594499198455853555201 73110894297249599227926777600 (List.ofFn fun j : Fin 6 => B i j) =
      73110894297249599227926777600 * geometricEncoding 146221788594499198455853555201 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    52362790 232706260486532514240 73110894297249599227926777600 146221788594499198455853555201 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas181.Block09
