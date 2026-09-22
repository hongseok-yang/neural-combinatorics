import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

namespace Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge10
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 7 → Fin 15 := ![0, 1, 2, 5, 6, 9, 14]
def freeIndex : Fin 8 → Fin 15 := ![3, 4, 7, 8, 10, 11, 12, 13]
def edgeMap : Fin 7 ⊕ Fin 8 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 7 ⊕ Fin 8 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3, Sum.inl 4, Sum.inr 2, Sum.inr 3, Sum.inl 5, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl 6]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 256) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359310083906470520692818175047999181105964295166287011805526897793564958231841251487126122128290402887982543819152475959934757858413519459227510321904218689283221246115473974911491517529141951339745354096876963970365219714561322554871045734920686893375849301366954579680224668477107484873833646109738962282261424730486059161262053430110022658131168397371785343663599857149187028300927328154759880430280628200411776646587100836153674149026170557507500914040195247623327341860191840118779923474564456692358865938438156691963560396746727102083466013895720170434390621707782663355831139435563984411654385273430114809707750835640060697657018125921898038020468311674241005139149752143956013787457939152061231820048659298176787118427834555160254762320128))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974696769788214796467001690955034479255065367114877520706981140871408118205983661382734119992912892600337204605051195608117479760282609461271505675480288340943782583037752136166713328464416629117608001384850083789992797910155957013493458806475725084063025677558003582636520739602400167457510085268133384375256804929354778924451509802869729967743647085376495618334814363385136868879002735129033685843734594280497472367470744239195122359006461168927090969032252243720590269802553262035043819487604320429153437374742268823533186157666985586403068880759002433136569399296085540122087072577753832587820759602410235181447016971734042479717760820102252058063814677572698159351572388133049131558937794035775768080982528682613051794858959611010708391330048
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
end Taeyoung.Methods.RootedSOS.Induced.Six.HomEdge10
