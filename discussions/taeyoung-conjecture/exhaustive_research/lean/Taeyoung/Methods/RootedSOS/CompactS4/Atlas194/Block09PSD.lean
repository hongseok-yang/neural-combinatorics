import Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09Data
import Taeyoung.Methods.RootedSOS.CongruenceDiagonalDominance

namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

private def GPEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (31448337444451128452443453231278935759051717330531132949068370981708861625809307483198685102746928583004018129479507955))
(.node 1 (.leaf (19326283710870438765034481020184814050382328400924266640816072605562462042656524700560518336806406105866327893688189318))
(.leaf (13677111464588714546612305124592645459848579220801947806610494662892311712429383488841872854540058153391776712122155265))))
(.node 1 (.leaf (7728467948358825309701237092633943210709166814737057335735194830811177806587764183345991272534291146356798402593200561))
(.node 1 (.leaf (26898170592258090967208397016999946937470066105143585414992971212982760334211383443950772801930414636903822194545353781))
(.leaf (28665623363727924189243424197121381828117844084035961266284698904486120608322303345045481778209724464612937624453142336)))))

private theorem GP_left_bound : ∀ (i : Fin 6) (j : Fin 6), (G i j).natAbs ≤ 36645836592672 := by decide +kernel
private theorem GP_right_bound : ∀ (i : Fin 6) (j : Fin 6), (P i j).natAbs ≤ 36742195 := by decide +kernel
private theorem GP_result_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 8078690844156541170240 := by decide +kernel
private theorem GP_encoded : ∀ i : Fin 6,
    GPEnc.get i = ∑ j : Fin 6, P i j * (16157381688313082340481 : Int)^j.1 := by decide +kernel
private theorem GP_product : ∀ i : Fin 6,
    shiftedEncoding 16157381688313082340481 8078690844156541170240 (List.ofFn fun j : Fin 6 => K i j) =
      8078690844156541170240 * geometricEncoding 16157381688313082340481 6 +
        ∑ j : Fin 6, G i j * GPEnc.get j := by decide +kernel

theorem GP_exact (i : Fin 6) (j : Fin 6) :
    K i j = ∑ k : Fin 6, G i k * P k j :=
  packed_rect_product_exact G P K
    36645836592672 36742195 8078690844156541170240 16157381688313082340481 (fun i => GPEnc.get i)
    GP_left_bound GP_right_bound GP_result_bound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    GP_encoded GP_product i j

private def PKEnc : PackedTable :=
(.node 3 (.node 1 (.leaf (1407820840752048491586179568567682181204022060059574272131676890169744142492591925737913491617176720859054893644175462883136854818007840241098438657463023551584))
(.node 1 (.leaf (-2931890910630029455664918658500149851225991385783532600090106236102111075614502881229399742668274019450120957512052763655107222517946361599295477394526085312096))
(.leaf (1143428732706075263299872835655320965030827081421660572076953826237290652802071787427368031185033143349819881901953814745195791592369887308195668912493850208736))))
(.node 1 (.leaf (5614760581439894523522684392884056516393381177338407443726114427225630138264028778970889118971474022198576565983911636682694542110658767595360889711160830720224))
(.node 1 (.leaf (7795179997369773609972402988305157429980065523913234700813977929387624846353336557069164909980655719947075456127356468917110680905493972521385458300340237314816))
(.leaf (179720258036728375814571718460793931227780313491978037073982627394763523744084378699051400513004709069084993218361838237868893230065804216464976497376486851664900297664)))))

private theorem PK_left_bound : ∀ (i : Fin 6) (j : Fin 6), (Pt i j).natAbs ≤ 36742195 := by decide +kernel
private theorem PK_right_bound : ∀ (i : Fin 6) (j : Fin 6), (K i j).natAbs ≤ 514663196779873360800 := by decide +kernel
private theorem PK_result_bound : ∀ (i : Fin 6) (j : Fin 6), (B i j).natAbs ≤ 113459133212456874586913736000 := by decide +kernel
private theorem PK_encoded : ∀ i : Fin 6,
    PKEnc.get i = ∑ j : Fin 6, K i j * (226918266424913749173827472001 : Int)^j.1 := by decide +kernel
private theorem PK_product : ∀ i : Fin 6,
    shiftedEncoding 226918266424913749173827472001 113459133212456874586913736000 (List.ofFn fun j : Fin 6 => B i j) =
      113459133212456874586913736000 * geometricEncoding 226918266424913749173827472001 6 +
        ∑ j : Fin 6, Pt i j * PKEnc.get j := by decide +kernel

theorem PK_exact (i : Fin 6) (j : Fin 6) :
    B i j = ∑ k : Fin 6, Pt i k * K k j :=
  packed_rect_product_exact Pt K B
    36742195 514663196779873360800 113459133212456874586913736000 226918266424913749173827472001 (fun i => PKEnc.get i)
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
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas194.Block09
