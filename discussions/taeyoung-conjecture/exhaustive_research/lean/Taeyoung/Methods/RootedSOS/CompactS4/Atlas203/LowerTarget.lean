import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding
import Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Coloring
namespace Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.graph203
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 12 → Fin 15 := ![0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 12, 14]
def freeIndex : Fin 3 → Fin 15 := ![3, 11, 13]
def edgeMap : Fin 12 ⊕ Fin 3 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 12 ⊕ Fin 3 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr 1, Sum.inl 10, Sum.inr 2, Sum.inl 11]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 12 ⊕ Fin 3 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 12 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 12 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 8) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359282673650290805850915320799271469160288095364003068811516136814650799483070341924618166848523759226142060644486755959712173413033017718982063483338558774703907096536444243517521657363209869748578560422645251921536416526868925460695012449704587596941368794109292496993424620141951430458077295216803645380489126901428073536327313400647185150465600252452221085595755317814879734593583755557626387671146207600382813806197393657506130356806223900240255936624766139610842557502066362388168078952433255646530270059587148958985440808689728239169202770906308874722351459698629687004636705130011696466559480695993970970591945379077230662223490660449168933048033646644824910614093983311630578637797270542434156731739846665815585873818182507944009691365384))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974669359532035081625098836706306767309389167312593577712970379892493959457212751820226164713146248938496721430385475607894895314902107721026058836914628426364468433458722404772743468298484547526441207710618371741163994722463559919317425521259625787628545170300341499949720691267244113041753734375198067473484507100296793299516769773406892460078078940456931360266969824050829575171659162531900193084600173680468509527081037060547578566786514511659845991616823135708105485444427784304431974965473119383324841495891261090555066569609986723488805637769591137424530237286932563770892638272201544642725855024974091342331211515171212444284233354629522953091380012543282064826516619300723696409277125426148692992673716050251850550249307563794463320375304
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 8, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 8, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 8, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 8 ≃ Fin 8).sum_comp
    (fun a : Fin 8 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 8, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 3 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 8 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.CompactS4.Atlas203.Lower.Target
