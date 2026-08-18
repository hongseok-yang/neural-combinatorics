import OddCycleBound.RegionII.Certificate.ZoneC

/-!
# Certificate-tree coverage

The generated stream is parsed a second time into a small inductive tree.
Every node stores the exact rational box propagated from the root.  The
boolean validity check below verifies both the split geometry and every leaf
checker.  The accompanying theorem is the trusted, purely logical coverage
bridge: a valid tree sends every real point of its root box to a checked leaf.
-/

namespace OddCycleBound.RegionII.Certificate

/-- Membership of a real chart point in a closed rational certificate box. -/
def RatBox.Contains (b : RatBox) (e k : Real) : Prop :=
  (b.e1 : Real) <= e ∧ e <= (b.e2 : Real) ∧
    (b.k1 : Real) <= k ∧ k <= (b.k2 : Real)

lemma RatBox.contains_splitE {b : RatBox} {e k : Real}
    (h : b.Contains e k) :
    (b.splitE.1).Contains e k ∨ (b.splitE.2).Contains e k := by
  let em : Real := (((b.e1 + b.e2) / 2 : ℚ) : Real)
  by_cases he : e <= em
  · left
    exact ⟨h.1, he, h.2.2⟩
  · right
    exact ⟨le_of_not_ge he, h.2.1, h.2.2⟩

lemma RatBox.contains_splitK {b : RatBox} {e k : Real}
    (h : b.Contains e k) :
    (b.splitK.1).Contains e k ∨ (b.splitK.2).Contains e k := by
  let km : Real := (((b.k1 + b.k2) / 2 : ℚ) : Real)
  by_cases hk : k <= km
  · left
    exact ⟨h.1, h.2.1, h.2.2.1, hk⟩
  · right
    exact ⟨h.1, h.2.1, le_of_not_ge hk, h.2.2.2⟩

/-- A parsed tree whose nodes remember the propagated box. -/
inductive BoxTree where
  | splitE (box : RatBox) (left right : BoxTree)
  | splitK (box : RatBox) (left right : BoxTree)
  | leaf (box : RatBox) (token : RegionCertToken)
  deriving Repr

/-- Structural parser.  It does not trust or evaluate leaf claims. -/
def parseBoxNode (tokens : Array RegionCertToken) :
    Nat → Nat → RatBox → Option (BoxTree × Nat)
  | 0, _, _ => none
  | fuel + 1, index, box =>
      match tokens[index]? with
      | none => none
      | some .splitE =>
          let children := box.splitE
          match parseBoxNode tokens fuel (index + 1) children.1 with
          | none => none
          | some (left, next) =>
              match parseBoxNode tokens fuel next children.2 with
              | none => none
              | some (right, finish) =>
                  some (.splitE box left right, finish)
      | some .splitK =>
          let children := box.splitK
          match parseBoxNode tokens fuel (index + 1) children.1 with
          | none => none
          | some (left, next) =>
              match parseBoxNode tokens fuel next children.2 with
              | none => none
              | some (right, finish) =>
                  some (.splitK box left right, finish)
      | some token => some (.leaf box token, index + 1)

def parseBoxTree (tokens : Array RegionCertToken) (root : RatBox) :
    Option BoxTree := do
  let result ← parseBoxNode tokens (tokens.size + 1) 0 root
  if result.2 = tokens.size then some result.1 else none

/-- Every propagated Zone-C leaf stays ordered and inside the declared root. -/
def wellPlacedC (box : RatBox) : Bool :=
  decide (zoneCRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneCRoot.e2 ∧
    zoneCRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneCRoot.k2)

/-- The exact leaf acceptance predicate used by the Zone-C tree. -/
def leafAcceptedC (box : RatBox) (token : RegionCertToken) : Bool :=
  wellPlacedC box &&
    match token with
    | .cSkip => decide (box.k1 > min (kappaXiQ box.e2) (kappaBarQ box.e1))
    | .cVerified m => checkCRegular box m
    | .cBottom => checkCBottom box
    | _ => false

lemma leafAcceptedC_wellPlaced {box : RatBox} {token : RegionCertToken}
    (h : leafAcceptedC box token = true) :
    zoneCRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneCRoot.e2 ∧
      zoneCRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneCRoot.k2 := by
  simp only [leafAcceptedC, Bool.and_eq_true] at h
  simpa [wellPlacedC] using h.1

/-- A valid tree has the prescribed propagated boxes and accepted leaves. -/
def BoxTree.validC : RatBox → BoxTree → Bool
  | expected, .splitE box left right =>
      decide (box = expected) &&
        left.validC box.splitE.1 && right.validC box.splitE.2
  | expected, .splitK box left right =>
      decide (box = expected) &&
        left.validC box.splitK.1 && right.validC box.splitK.2
  | expected, .leaf box token =>
      decide (box = expected) && leafAcceptedC box token

lemma BoxTree.validC_splitE {box : RatBox} {left right : BoxTree}
    (hleft : left.validC box.splitE.1 = true)
    (hright : right.validC box.splitE.2 = true) :
    (BoxTree.splitE box left right).validC box = true := by
  simp [BoxTree.validC, hleft, hright]

lemma BoxTree.validC_splitK {box : RatBox} {left right : BoxTree}
    (hleft : left.validC box.splitK.1 = true)
    (hright : right.validC box.splitK.2 = true) :
    (BoxTree.splitK box left right).validC box = true := by
  simp [BoxTree.validC, hleft, hright]

/-- Logical coverage theorem for any sound interpretation of accepted leaves.
No computation or interval arithmetic occurs in this proof. -/
theorem BoxTree.validC_covers
    {tree : BoxTree} {root : RatBox} {e k : Real} {Q : Prop}
    (hleaf : ∀ box token, leafAcceptedC box token = true →
      box.Contains e k → Q)
    (hvalid : tree.validC root = true)
    (hpoint : root.Contains e k) : Q := by
  induction tree generalizing root with
  | splitE box left right ihLeft ihRight =>
      simp only [BoxTree.validC, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨⟨hbox, hleft⟩, hright⟩
      subst root
      rcases box.contains_splitE hpoint with hp | hp
      · exact ihLeft hleft hp
      · exact ihRight hright hp
  | splitK box left right ihLeft ihRight =>
      simp only [BoxTree.validC, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨⟨hbox, hleft⟩, hright⟩
      subst root
      rcases box.contains_splitK hpoint with hp | hp
      · exact ihLeft hleft hp
      · exact ihRight hright hp
  | leaf box token =>
      simp only [BoxTree.validC, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨hbox, haccept⟩
      subst root
      exact hleaf box token haccept hpoint

/-- Every propagated Zone-B leaf stays ordered and inside its declared root. -/
def wellPlacedB (box : RatBox) : Bool :=
  decide (zoneBRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneBRoot.e2 ∧
    zoneBRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneBRoot.k2)

/-- The exact leaf acceptance predicate used by the Zone-B tree. -/
def leafAcceptedB (box : RatBox) (token : RegionCertToken) : Bool :=
  wellPlacedB box &&
    match token with
    | .bSkipZoneC => decide (box.k2 < kappaXiQ box.e1)
    | .bSkipOutside => decide (box.k1 > kappaBarQ box.e1)
    | .bVerified => checkBVerified box
    | _ => false

lemma leafAcceptedB_wellPlaced {box : RatBox} {token : RegionCertToken}
    (h : leafAcceptedB box token = true) :
    zoneBRoot.e1 <= box.e1 ∧ box.e1 <= box.e2 ∧ box.e2 <= zoneBRoot.e2 ∧
      zoneBRoot.k1 <= box.k1 ∧ box.k1 <= box.k2 ∧ box.k2 <= zoneBRoot.k2 := by
  simp only [leafAcceptedB, Bool.and_eq_true] at h
  simpa [wellPlacedB] using h.1

/-- Zone-B structural validity, independent of the Zone-C interpretation. -/
def BoxTree.validB : RatBox → BoxTree → Bool
  | expected, .splitE box left right =>
      decide (box = expected) &&
        left.validB box.splitE.1 && right.validB box.splitE.2
  | expected, .splitK box left right =>
      decide (box = expected) &&
        left.validB box.splitK.1 && right.validB box.splitK.2
  | expected, .leaf box token =>
      decide (box = expected) && leafAcceptedB box token

def zoneBBoxTree : BoxTree :=
  (parseBoxTree zoneBTokens zoneBRoot).getD
    (.leaf zoneBRoot .splitE)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zoneB_boxTree_valid :
    (parseBoxTree zoneBTokens zoneBRoot).isSome = true ∧
      zoneBBoxTree.validB zoneBRoot = true := by
  decide +kernel

/-- Logical coverage by accepted Zone-B leaves. -/
theorem BoxTree.validB_covers
    {tree : BoxTree} {root : RatBox} {e k : Real} {Q : Prop}
    (hleaf : ∀ box token, leafAcceptedB box token = true →
      box.Contains e k → Q)
    (hvalid : tree.validB root = true)
    (hpoint : root.Contains e k) : Q := by
  induction tree generalizing root with
  | splitE box left right ihLeft ihRight =>
      simp only [BoxTree.validB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨⟨hbox, hleft⟩, hright⟩
      subst root
      rcases box.contains_splitE hpoint with hp | hp
      · exact ihLeft hleft hp
      · exact ihRight hright hp
  | splitK box left right ihLeft ihRight =>
      simp only [BoxTree.validB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨⟨hbox, hleft⟩, hright⟩
      subst root
      rcases box.contains_splitK hpoint with hp | hp
      · exact ihLeft hleft hp
      · exact ihRight hright hp
  | leaf box token =>
      simp only [BoxTree.validB, Bool.and_eq_true, decide_eq_true_eq] at hvalid
      rcases hvalid with ⟨hbox, haccept⟩
      subst root
      exact hleaf box token haccept hpoint

end OddCycleBound.RegionII.Certificate
