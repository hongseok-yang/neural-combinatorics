import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

namespace Taeyoung.Methods.RootedSOS.Induced.Six.Hom10
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 6 → Fin 15 := ![0, 1, 2, 5, 6, 9]
def freeIndex : Fin 9 → Fin 15 := ![3, 4, 7, 8, 10, 11, 12, 13, 14]
def edgeMap : Fin 6 ⊕ Fin 9 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 6 ⊕ Fin 9 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inl 3, Sum.inl 4, Sum.inr 2, Sum.inr 3, Sum.inl 5, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inr 8]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 6 ⊕ Fin 9 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 6 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 6 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 512) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359315565790421576444532278304744349429447192419183424565140364922377205332363821763271080222387530820209262210722269505169752909977519989772487202582622241906552932016227527217346302817382612250060794449625243637201162491664848240201033094649990162069823201311313168104928214336049560385117329474180725639962797630312457453392460547638337940372237496802971738364054435931034153384639935339643412016237290896597316617893599734985860534214002425523908041380672805318397549815014715614958442385365925646169976641282008788232412641342170003290214689424980522879554431714096833194594822500817425597659188478737273867583479784984984731849929106000989604901208224279523882118460813488326238587346182860406193726860457993663405828733039984796150324986368))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974702251672165852218715794211779647578548264367773933466594608000220365306506231658879078087010020532563922996620989153352474811846609991816482556158691893567114268938505688472568113752657290027923441737598363456828740687259482698823446166205028352756999577502362171061224285461342242968793768632575147732958177829181177216581916920398045249984716184807682013035268942166983993962715342313917217429691256976683012338777243138027308744194293036943498096372729801415660477757376137531222338398405789382964548077586120919802038402262428487609817556288262785581733209302399709960850755643007273773825562807717394239322745921078966513910671800181343624944554590177981036330883449477419356358826037744120729987794327378099670505164165040646603953996288
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
end Taeyoung.Methods.RootedSOS.Induced.Six.Hom10
