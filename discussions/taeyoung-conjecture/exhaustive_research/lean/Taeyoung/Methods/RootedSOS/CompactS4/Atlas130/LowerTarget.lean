import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Coloring
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Lower.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.graph130
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 7 → Fin 15 := ![0, 1, 2, 5, 12, 13, 14]
def freeIndex : Fin 8 → Fin 15 := ![3, 4, 6, 7, 8, 9, 10, 11]
def edgeMap : Fin 7 ⊕ Fin 8 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 7 ⊕ Fin 8 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl 4, Sum.inl 5, Sum.inl 6]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 256) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359310084073759236922230404607186323785680850305906513382490391098047406253379046194860064486988700333093080218008713789575747592903609001105003181572892747122341016102467732751052462478845760691229487455876984209235783514160186748454827055240497071675473784314296027946230160137050199674076622294848621061979453180231148234016993318743973622069824876060080803142752803000240669263527721779116502186037959717773244731726921846390142121157907760841682857468259288698864855319439009822374537811488395846613427939103617893589600725555003359792698857173170004161232835602445398500759205217968393327279796485527506519317631607124584397913655289731946749824681221855716872951750557943463570065978861023221617168790378041522444813088257245906182692405504))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974696769955503512696413920514221621934781922254497022283944634175890566227521456090468062351611190045447741003907433437758469494772699003148998535148962398782902353024745894006274273414120438469092134743850104028863361709754821207077240126795535262362650160505345030902526231262342882257753061453243043154974833379099867997206449691503680931682303564064791077813967309236190509841603128753390307599491925797858940452610565249431590331138198372261272912460316284796127783261800431738638433824528259583407999375407730025159226486475261844112301724036452266863411613190748275267015138360158241503446170814507626891056897743218566179974397983912300769868027587754174027164173193932556687837458715906936153429724247425958709489519382301756636321415424
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 256, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 256, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 256, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 256 ≃ Fin 256).sum_comp
    (fun a : Fin 256 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 256, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 8 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 256 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas130.Lower.Target
