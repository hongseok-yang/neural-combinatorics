import OddCycleBound.Fisher.DependenceRatio

/-!
# Module 3 — Trace-monoid growth (Cartier–Foata)

Corresponds to `fisher.tex`, Definition (graph monoid), Lemma
`lem:cartier-foata`, and Definition (growth factor); Module 3 of the blueprint.

* `traceCount G k` = number of length-`k` trace classes in the graph monoid
  `M(G)` (words modulo `uv = vu` for edges `uv ∈ E(G)`).
* **Cartier–Foata inversion** (`lem:cartier-foata`): as formal power series,
  `(∑ₖ a_k(G) zᵏ) · D_G(z) = 1`.
* `growth G = limsup a_k(G)^{1/k}`.

The blueprint suggests importing Cartier–Foata as a theorem for a first version
and later formalising the sign-reversing involution.  The a_k are nonnegative
integers, which drives Pringsheim/Perron positivity downstream.
-/

namespace Fisher

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A single adjacent commutation in a word of fixed length. -/
def traceSwap (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (w w' : Fin k → V) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < k),
    G.Adj (w ⟨i, Nat.lt_of_succ_lt hi⟩) (w ⟨i + 1, hi⟩) ∧
      w' = w ∘ (Equiv.swap ⟨i, Nat.lt_of_succ_lt hi⟩ ⟨i + 1, hi⟩)

/-- The trace-monoid congruence on words of a fixed length. -/
def traceSetoid (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Setoid (Fin k → V) :=
  Relation.EqvGen.setoid (traceSwap G k)

/-- Trace classes of words of length `k` in the graph monoid of `G`. -/
abbrev TraceClass (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :=
  Quotient (traceSetoid G k)

/-- Number of length-`k` trace classes of the graph monoid `M(G)`. -/
noncomputable def traceCount (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  Nat.card (TraceClass G k)

/-- A word with no adjacent pair that can be commuted.  Such a word is an
isolated vertex of the graph of elementary trace swaps. -/
def IsTraceReduced (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (w : Fin k → V) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < k),
    w ⟨i, Nat.lt_of_succ_lt hi⟩ = w ⟨i + 1, hi⟩ ∨
      ¬G.Adj (w ⟨i, Nat.lt_of_succ_lt hi⟩) (w ⟨i + 1, hi⟩)

private theorem traceSwap_symm {k : ℕ} {w w' : Fin k → V} :
    traceSwap G k w w' → traceSwap G k w' w := by
  rintro ⟨i, hi, hadj, rfl⟩
  let a : Fin k := ⟨i, Nat.lt_of_succ_lt hi⟩
  let b : Fin k := ⟨i + 1, hi⟩
  refine ⟨i, hi, ?_, ?_⟩
  · change G.Adj ((w ∘ Equiv.swap a b) a) ((w ∘ Equiv.swap a b) b)
    simp [Function.comp_apply, a, b, hadj.symm]
  · funext j
    simp [Function.comp_apply, a, b]

private theorem reduced_not_traceSwap {k : ℕ} {w w' : Fin k → V}
    (hw : IsTraceReduced G w) : ¬traceSwap G k w w' := by
  rintro ⟨i, hi, hadj, _⟩
  rcases hw i hi with heq | hnot
  · exact G.loopless.irrefl _ (heq ▸ hadj)
  · exact hnot hadj

private theorem eq_of_reduced_eqvGen {k : ℕ} {w w' : Fin k → V}
    (hw : IsTraceReduced G w)
    (h : Relation.EqvGen (traceSwap G k) w w') : w = w' := by
  have hstrong : ∀ {x y : Fin k → V},
      Relation.EqvGen (traceSwap G k) x y →
        (IsTraceReduced G x → x = y) ∧ (IsTraceReduced G y → x = y) := by
    intro x y hxy
    induction hxy with
    | rel x y hxy =>
        constructor
        · intro hx
          exact (reduced_not_traceSwap G hx hxy).elim
        · intro hy
          exact (reduced_not_traceSwap G hy (traceSwap_symm G hxy)).elim
    | refl x => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | symm x y _ ih =>
        exact ⟨fun hy => (ih.2 hy).symm, fun hx => (ih.1 hx).symm⟩
    | trans x y z _ _ ihxy ihyz =>
        constructor
        · intro hx
          have hxy : x = y := ihxy.1 hx
          subst y
          exact ihyz.1 hx
        · intro hz
          have hyz : y = z := ihyz.2 hz
          subst z
          exact ihxy.2 hz
  exact (hstrong h).1 hw

/-- Reduced words inject into trace classes. -/
theorem card_traceReduced_le_traceCount (k : ℕ) :
    Nat.card {w : Fin k → V // IsTraceReduced G w} ≤ traceCount G k := by
  classical
  let f : {w : Fin k → V // IsTraceReduced G w} → TraceClass G k :=
    fun w => @Quotient.mk _ (traceSetoid G k) w.1
  have hf : Function.Injective f := by
    intro w w' hww'
    apply Subtype.ext
    apply eq_of_reduced_eqvGen G w.2
    exact @Quotient.exact _ (traceSetoid G k) _ _ hww'
  calc
    Nat.card {w : Fin k → V // IsTraceReduced G w} ≤
        Nat.card (TraceClass G k) := Nat.card_le_card_of_injective f hf
    _ = traceCount G k := rfl

private def wordIncl {S : Finset V} {k : ℕ} (w : Fin k → (↑S : Set V)) : Fin k → V :=
  fun i => (w i).1

private def WordIn (S : Finset V) {k : ℕ} (w : Fin k → V) : Prop :=
  ∀ i, w i ∈ S

private def wordRestrict (S : Finset V) {k : ℕ} (w : Fin k → V)
    (hw : WordIn S w) : Fin k → (↑S : Set V) :=
  fun i => ⟨w i, hw i⟩

private theorem traceSwap_map_induce (S : Finset V) {k : ℕ}
    {w w' : Fin k → (↑S : Set V)}
    (h : traceSwap (G.induce (↑S : Set V)) k w w') :
    traceSwap G k (wordIncl w) (wordIncl w') := by
  rcases h with ⟨i, hi, hadj, rfl⟩
  exact ⟨i, hi, hadj, rfl⟩

private theorem traceSwap_restrict (S : Finset V) {k : ℕ}
    {w w' : Fin k → V} (hw : WordIn S w)
    (h : traceSwap G k w w') :
    ∃ hw' : WordIn S w',
      traceSwap (G.induce (↑S : Set V)) k
        (wordRestrict S w hw) (wordRestrict S w' hw') := by
  rcases h with ⟨i, hi, hadj, rfl⟩
  let a : Fin k := ⟨i, Nat.lt_of_succ_lt hi⟩
  let b : Fin k := ⟨i + 1, hi⟩
  have hw' : WordIn S (w ∘ Equiv.swap a b) := fun j => hw (Equiv.swap a b j)
  refine ⟨hw', i, hi, ?_, ?_⟩
  · exact hadj
  · funext j
    apply Subtype.ext
    rfl

private theorem eqvGen_restrict (S : Finset V) {k : ℕ} {w w' : Fin k → V}
    (h : Relation.EqvGen (traceSwap G k) w w') :
    (∀ hw : WordIn S w, ∃ hw' : WordIn S w',
      Relation.EqvGen (traceSwap (G.induce (↑S : Set V)) k)
        (wordRestrict S w hw) (wordRestrict S w' hw')) ∧
    (∀ hw' : WordIn S w', ∃ hw : WordIn S w,
      Relation.EqvGen (traceSwap (G.induce (↑S : Set V)) k)
        (wordRestrict S w hw) (wordRestrict S w' hw')) := by
  induction h with
  | rel x y hxy =>
      constructor
      · intro hx
        obtain ⟨hy, hres⟩ := traceSwap_restrict G S hx hxy
        exact ⟨hy, Relation.EqvGen.rel _ _ hres⟩
      · intro hy
        obtain ⟨hx, hres⟩ := traceSwap_restrict G S hy (traceSwap_symm G hxy)
        exact ⟨hx, Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hres)⟩
  | refl x =>
      exact ⟨fun hx => ⟨hx, Relation.EqvGen.refl _⟩,
        fun hx => ⟨hx, Relation.EqvGen.refl _⟩⟩
  | symm x y _ ih =>
      exact ⟨fun hy => by
          obtain ⟨hx, hres⟩ := ih.2 hy
          exact ⟨hx, Relation.EqvGen.symm _ _ hres⟩,
        fun hx => by
          obtain ⟨hy, hres⟩ := ih.1 hx
          exact ⟨hy, Relation.EqvGen.symm _ _ hres⟩⟩
  | trans x y z _ _ ihxy ihyz =>
      constructor
      · intro hx
        obtain ⟨hy, hxy⟩ := ihxy.1 hx
        obtain ⟨hz, hyz⟩ := ihyz.1 hy
        exact ⟨hz, Relation.EqvGen.trans _ _ _ hxy hyz⟩
      · intro hz
        obtain ⟨hy, hyz⟩ := ihyz.2 hz
        obtain ⟨hx, hxy⟩ := ihxy.2 hy
        exact ⟨hx, Relation.EqvGen.trans _ _ _ hxy hyz⟩

/-- Trace counts are monotone under induced subgraphs (used in Module 4). -/
theorem traceCount_mono_induced (S : Finset V) (k : ℕ) :
    traceCount (G.induce (↑S : Set V)) k ≤ traceCount G k := by
  classical
  let fword : (Fin k → (↑S : Set V)) → (Fin k → V) := wordIncl
  have hmap : ∀ {w w'}, (traceSetoid (G.induce (↑S : Set V)) k).r w w' →
      (traceSetoid G k).r (fword w) (fword w') := by
    intro w w' hww'
    change Relation.EqvGen (traceSwap (G.induce (↑S : Set V)) k) w w' at hww'
    change Relation.EqvGen (traceSwap G k) (wordIncl w) (wordIncl w')
    induction hww' with
    | rel x y hxy =>
        exact Relation.EqvGen.rel _ _ (traceSwap_map_induce G S hxy)
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz
  let f : TraceClass (G.induce (↑S : Set V)) k → TraceClass G k :=
    Quotient.map fword (fun _ _ h => hmap h)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ w =>
      induction y using Quotient.inductionOn with
      | _ w' =>
        apply Quotient.sound
        have hinc : Relation.EqvGen (traceSwap G k) (wordIncl w) (wordIncl w') :=
          @Quotient.exact _ (traceSetoid G k) _ _ hxy
        have hw : WordIn S (wordIncl w) := fun i => (w i).2
        obtain ⟨hw', hres⟩ := (eqvGen_restrict G S hinc).1 hw
        have hl : wordRestrict S (wordIncl w) hw = w := by
          funext i
          apply Subtype.ext
          rfl
        have hr : wordRestrict S (wordIncl w') hw' = w' := by
          funext i
          apply Subtype.ext
          rfl
        rwa [hl, hr] at hres
  simpa [traceCount] using Nat.card_le_card_of_injective f hf

/-- **Cartier–Foata inversion** as a formal power series identity:
`(∑ a_k zᵏ) · D_G = 1`.  Stated as: the generating series is the inverse of the
dependence polynomial in `PowerSeries ℝ`. -/
theorem cartier_foata :
    (PowerSeries.mk (fun k => (traceCount G k : ℝ))) *
        (depPoly G).toPowerSeries = 1 := by
  sorry

end Fisher
