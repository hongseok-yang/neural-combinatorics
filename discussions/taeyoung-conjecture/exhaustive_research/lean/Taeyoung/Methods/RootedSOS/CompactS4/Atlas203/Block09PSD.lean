import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (34065066369627094463338973152977944273091347161964480986818321629907809254718048765996846929712218734357672121754844834757))
(.node 1 (.leaf (28269632266949010391693847454539911125777863706474009475914154165539219904907021640988825192304115185613770789808518124719))
(.leaf (5038819123542721838648980384105018827151006930652669785252876657463147693875907894266669073748938159540423419154714800182))))
(.node 1 (.leaf (-10792227584358035605036953063451203553459174013891183417277596201711963178488662902791173702299043845476589299738111797023))
(.node 1 (.leaf (24483992734798802420180625509196692894237476431983271733228149988458008775225105365169355317561511945418017840731952934929))
(.leaf (7930682995575111756927300435564235616852825697386571131244762430746466117151793976642433217773245061152319183253209780618)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 15951509472672 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 225804372 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 21611523473572512731904 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (43223046947145025463809 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 43223046947145025463809 21611523473572512731904 (List.ofFn fun j : Fin 6 => K i j) =
      21611523473572512731904 * geometricEncoding 43223046947145025463809 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    15951509472672 225804372 21611523473572512731904 43223046947145025463809 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (-75109350495405997906054337434603856276935194013632452710619707338179854390771677002914859233130653075946826827961918586728274437143761978708282669881162604876224))
(.node 1 (.leaf (321681539445913369496419790635845304541677982248398590953371765071563265327418669302419394779463676278910224195804732259589989002762205615167142453531016037215680))
(.leaf (-146684851930397280975395608056181296642886022413604976680091313511952388069625952789638112414682432980884234921885214255427030087903941756086330607771322146753504))))
(.node 1 (.leaf (266686884758810667355612302473075561091444379724529839127169222885492420522940706609371782072542398995186422922100286537318285152505038693074385791850131119158208))
(.node 1 (.leaf (-39583341199675740909808723581628191420784525162210034173584597669578269371011847448441667183547302986579992491889637991721951533370463277314911533824991774317728))
(.leaf (2455875438555224989850640819369811773073136181107634541279210926519578299862743668679049899903881317061111269553118262795894178674366720976003293278420023309767854047744)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 225804372 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 202557078676923735744 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 274429643668784130249407236608 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (548859287337568260498814473217 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 548859287337568260498814473217 274429643668784130249407236608 (List.ofFn fun j : Fin 6 => B i j) =
      274429643668784130249407236608 * geometricEncoding 548859287337568260498814473217 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    225804372 202557078676923735744 274429643668784130249407236608 548859287337568260498814473217 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Block09
