import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

namespace Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge09
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 6 → Fin 15 := ![0, 1, 2, 5, 9, 14]
def freeIndex : Fin 9 → Fin 15 := ![3, 4, 6, 7, 8, 10, 11, 12, 13]
def edgeMap : Fin 6 ⊕ Fin 9 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 6 ⊕ Fin 9 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inl 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inl 5]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 6 ⊕ Fin 9 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 6 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 6 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 512) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359315566124999008786512267865454429365644685325158576870361051742547844139325124370290302539815950222144552627826701105804654032206101734327663608845214054659615361002903020970704476099006842326142291402488223893945102623604515813568318177640061482875846038711582227508996955144059071949543316748757063252803234139038008072803607479873731108723750251220966981597457152613126331723747698283580531030272177379229070701050741178567368247062127505950417140448692203842774452460779617203010915841409516493124920981336775237846126594850887099568049799674625998428596274673863315456365652570654224120717950548636478885212311148874823368591469960769436526241657423349267419656742927978106202060579563534832495745261944349053375203265472224738146001814016))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974702252006743284560695783772489727514745757273749085771815294820391004113467534265898300404438439934499213413725420753987375934075191736371658962421283706320176697925181182225926287034281520104004938690461343713572680819199150272190731249195099673563022414902631230465293026269351754533219755907151485345798614337906727835993063852633438418336228939225677256268671658849076172301823105257854336443726143459314766421934384581608816457042418117370007195440749199940037380403141039119274811854449380229919492417640887369415752355771145583887652666537908261130775052262166192222621585712844072296884324877616599256951577284968805150652212654949790546285003789247724573869165563967199319832059418418547032006195813733489639879696597280588599630823936
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 512, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 512, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 512, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 512 ≃ Fin 512).sum_comp
    (fun a : Fin 512 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 512, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 9 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 512 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge09
