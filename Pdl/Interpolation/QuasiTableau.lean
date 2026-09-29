import Pdl.Interpolation.QFormula
import Pdl.Interpolation.Cluster

/-! ## Quasi-Tableaux (Def 9.8) -/

-- Alternative idea for quasi-tableau:
-- Instead of labelling nodes in Q with finite sequents, label them with the path to where
-- that sequent comes from in `Λ₂[C⁺]`?

inductive Typ | one | two | three -- lower case because these are not `Type`s.
  deriving DecidableEq
open Typ

/-- Simple tree data type for `Q` in Def. 9.8. -/
inductive QuasiTab : Type | QNode : (k : Typ) → (Δ : Sequent) → (next : List QuasiTab) → QuasiTab
open QuasiTab

/-- The type `k(x)` of the root of a quasi-tableau. -/
def QuasiTab.typ : QuasiTab → Typ | .QNode k _ _ => k

/-- The label `Δₓ` of the root of a quasi-tableau. -/
def QuasiTab.label : QuasiTab → Sequent | .QNode _ Δ _ => Δ

/-- The children `⋖Q` of the root of a quasi-tableau. -/
def QuasiTab.children : QuasiTab → List QuasiTab | .QNode _ _ next => next

/-- All nodes of a quasi-tableau, each given by the subtree rooted at it. -/
def QuasiTab.subtrees : QuasiTab → List QuasiTab
  | .QNode k Δ next => .QNode k Δ next :: next.flatMap subtrees

-- TODO use `rep` instead of `X ∈ Hist` maybe?

/-! ### Termination of the construction of `Q`

The construction of `Q` terminates because along a branch of `Q` the label of a node of
type 1 is either a repeat or a new element of the finite list `Λ₂[C]`, and in the latter
case it is added to the history. Hence the number of elements of `Λ₂[C]` that are not yet
in the history decreases. -/

lemma countP_lt_countP_of_mem {α} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x → q x)
    {a : α} (ha : a ∈ l) (hq : q a) (hp : ¬ p a) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have hmono : l.countP p ≤ l.countP q := List.countP_mono_left (fun x hx => h x (by simp [hx]))
    rcases List.mem_cons.mp ha with rfl | ha'
    · simp only [List.countP_cons, hp, hq, Bool.false_eq_true, ite_false, ite_true]
      omega
    · have hlt := ih (fun x hx => h x (by simp [hx])) ha'
      simp only [List.countP_cons]
      by_cases hb : p b
      · have hb' := h b (by simp) hb
        simp only [hb, hb', ite_true]
        omega
      · simp only [hb, Bool.false_eq_true, ite_false]
        split <;> omega

lemma length_filter_notMem_cons_lt {α} [DecidableEq α] {l Hist : List α} {a : α}
    (ha : a ∈ l) (ha' : a ∉ Hist) :
    (l.filter (fun z => decide (z ∉ a :: Hist))).length
      < (l.filter (fun z => decide (z ∉ Hist))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  refine countP_lt_countP_of_mem (fun x _ hx => ?_) ha (by simpa using ha') (by simp)
  simp only [decide_eq_true_eq, List.mem_cons, not_or] at hx ⊢
  exact hx.2

open QuasiTab Typ in
/-- Def 9.8: the quasi-tableau, given the list `inC` of labels `Λ₂[C]` and the function
`step` that maps a label to the labels of the children obtained by applying the right rule.
Both are provided by `LoadedCluster.lambdaTwo` and `LoadedCluster.stepOf` in
`LoadedCluster.Q` below.

Following the paper we make the case distinction at the node of type 1: it is a leaf iff
it is a repeat (i.e. `Δ ∈ Hist`) or `Δ ∉ Λ₂[C]`, and in the latter case `Δ ∈ Λ₂[C⁺] \ Λ₂[C]`
by the invariant. Otherwise it has a unique child of type 2, which has a unique child of
type 3, whose children are given by `step` and are again of type 1.
Note that only nodes of type 1 add their label to the history — this is the "identify
repeats at the first opportunity" from Definition 9.11. -/
def QuasiTab.build (inC : Finset Sequent) (step : Sequent → List Sequent)
    (Hist : List Sequent) (Δ : Sequent) : QuasiTab :=
  -- The hypothesis `_h` is only used in the termination proof below.
  if _h : Δ ∈ inC ∧ Δ ∉ Hist then
    QNode one Δ [ QNode two Δ [ QNode three Δ
      ((step Δ).map (fun Pi => QuasiTab.build inC step (Δ :: Hist) Pi)) ] ]
  else
    QNode one Δ []
termination_by (inC.filter (fun Z => decide (Z ∉ Hist))).card
decreasing_by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨Δ, by simp [_h.1, _h.2], by simp⟩
  · intro z hz
    simp only [Finset.mem_filter, decide_eq_true_eq, List.mem_cons, not_or] at hz ⊢
    exact ⟨hz.1, hz.2.2⟩

open QuasiTab Typ in
/-- A node of `Q` of type 1 that is a repeat or an exit is a leaf. -/
lemma QuasiTab.build_of_leaf {inC step Hist Δ} (h : ¬ (Δ ∈ inC ∧ Δ ∉ Hist)) :
    QuasiTab.build inC step Hist Δ = QNode one Δ [] := by
  rw [QuasiTab.build]
  simp [h]

open QuasiTab Typ in
/-- A node of `Q` of type 1 that is neither a repeat nor an exit has a child of type 2,
which has a child of type 3, whose children are given by `step`. -/
lemma QuasiTab.build_of_node {inC step Hist Δ} (h : Δ ∈ inC ∧ Δ ∉ Hist) :
    QuasiTab.build inC step Hist Δ =
      QNode one Δ [ QNode two Δ [ QNode three Δ
        ((step Δ).map (fun Pi => QuasiTab.build inC step (Δ :: Hist) Pi)) ] ] := by
  rw [QuasiTab.build]
  simp [h]


open QuasiTab Typ in
/-- Remark 9.9: all leaves of the quasi-tableau have type 1. Here we need that a node of
type 3 does have children, which by Lemma 9.7 (d), (e) and (f) holds for all `Δ ∈ Λ₂[C]`. -/
lemma QuasiTab.build_leaf_typ {inC step} (hstep : ∀ Δ ∈ inC, step Δ ≠ []) (Hist Δ) :
    ∀ q ∈ (QuasiTab.build inC step Hist Δ).subtrees, q.children = [] → q.typ = one := by
  induction Hist, Δ using QuasiTab.build.induct (inC := inC) with
  | case1 Hist Δ h IH =>
    rw [QuasiTab.build_of_node h]
    intro q q_in q_leaf
    simp only [QuasiTab.subtrees, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons] at q_in
    rcases q_in with rfl | rfl | rfl | q_in
    · rfl
    · simp [QuasiTab.children] at q_leaf
    · exfalso
      simp only [QuasiTab.children, List.map_eq_nil_iff] at q_leaf
      exact hstep Δ h.1 q_leaf
    · simp only [List.mem_flatMap, List.mem_map] at q_in
      obtain ⟨t, ⟨Pi, Pi_in, rfl⟩, q_in⟩ := q_in
      exact IH Pi q q_in q_leaf
  | case2 Hist Δ h =>
    rw [QuasiTab.build_of_leaf h]
    intro q q_in _
    simp only [QuasiTab.subtrees, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at q_in
    subst q_in
    rfl

open QuasiTab Typ in
/-- Invariant of Def 9.8: if all labels produced by `step` are in `lam`, then all nodes of
the quasi-tableau built from a label in `lam` are again labelled with elements of `lam`. -/
lemma QuasiTab.build_label_mem {inC lam : Finset Sequent} {step : Sequent → List Sequent}
    (hstep : ∀ Δ, ∀ Pi ∈ step Δ, Pi ∈ lam) (Hist Δ) :
    Δ ∈ lam → ∀ q ∈ (QuasiTab.build inC step Hist Δ).subtrees, q.label ∈ lam := by
  induction Hist, Δ using QuasiTab.build.induct (inC := inC) with
  | case1 Hist Δ h IH =>
    intro hΔ q q_in
    rw [QuasiTab.build_of_node h] at q_in
    simp only [QuasiTab.subtrees, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons] at q_in
    rcases q_in with rfl | rfl | rfl | q_in
    · exact hΔ
    · exact hΔ
    · exact hΔ
    · simp only [List.mem_flatMap, List.mem_map] at q_in
      obtain ⟨t, ⟨Pi, Pi_in, rfl⟩, q_in⟩ := q_in
      exact IH Pi (hstep Δ Pi Pi_in) q q_in
  | case2 Hist Δ h =>
    intro hΔ q q_in
    rw [QuasiTab.build_of_leaf h] at q_in
    simp only [QuasiTab.subtrees, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at q_in
    subst q_in
    exact hΔ

open QuasiTab Typ in
/-- The invariant of Def 9.8: every node of the quasi-tableau that is not a leaf has a
label in `Λ₂[C]`, i.e. `C_{Δₓ} ≠ ∅` by `LoadedCluster.mem_lambdaTwo_iff`. -/
lemma QuasiTab.build_inner_label_mem {inC : Finset Sequent} {step : Sequent → List Sequent}
    (Hist Δ) :
    ∀ q ∈ (QuasiTab.build inC step Hist Δ).subtrees, q.children ≠ [] → q.label ∈ inC := by
  induction Hist, Δ using QuasiTab.build.induct (inC := inC) with
  | case1 Hist Δ h IH =>
    intro q q_in q_ne
    rw [QuasiTab.build_of_node h] at q_in
    simp only [QuasiTab.subtrees, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons] at q_in
    rcases q_in with rfl | rfl | rfl | q_in
    · exact h.1
    · exact h.1
    · exact h.1
    · simp only [List.mem_flatMap, List.mem_map] at q_in
      obtain ⟨t, ⟨Pi, Pi_in, rfl⟩, q_in⟩ := q_in
      exact IH Pi q q_in q_ne
  | case2 Hist Δ h =>
    intro q q_in q_ne
    rw [QuasiTab.build_of_leaf h] at q_in
    simp only [QuasiTab.subtrees, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at q_in
    subst q_in
    exact absurd rfl q_ne

/-- The right component of the root of the cluster is in `Λ₂[C]`. -/
lemma LoadedCluster.root_rightOnly_mem_lambdaTwo (C : LoadedCluster tab) :
    (nodeAt C.root).rightOnly ∈ C.lambdaTwo := by
  simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset]
  exact ⟨C.root.toFine, C.root_toFine_mem_fineCL, by simp⟩

/-- Def 9.8: the quasi-tableau associated with the cluster `C`. Its root has type 1 and is
labelled with the right component `Λ₂(r)` of the root `r` of the cluster. -/
noncomputable def LoadedCluster.Q (C : LoadedCluster tab) : QuasiTab :=
  QuasiTab.build C.lambdaTwo (Finset.seqSort ∘ C.stepOf) [] (nodeAt C.root).rightOnly

@[simp]
lemma LoadedCluster.Q_typ (C : LoadedCluster tab) : C.Q.typ = Typ.one := by
  rw [LoadedCluster.Q, QuasiTab.build]
  split <;> rfl

@[simp]
lemma LoadedCluster.Q_label (C : LoadedCluster tab) :
    C.Q.label = (nodeAt C.root).rightOnly := by
  rw [LoadedCluster.Q, QuasiTab.build]
  split <;> rfl


/-- All nodes of `Q` are labelled with elements of `Λ₂[C⁺]`. -/
lemma LoadedCluster.Q_label_mem_lambdaTwoPlus (C : LoadedCluster tab) :
    ∀ q ∈ C.Q.subtrees, q.label ∈ C.lambdaTwoPlus := by
  apply QuasiTab.build_label_mem
  · intro Pi Pi_in
    have := C.stepOf_mem_lambdaTwoPlus Pi Pi_in
    simp_all
  · exact (C.lambdaTwo_subset_lambdaTwoPlus _ C.root_rightOnly_mem_lambdaTwo)

/-- The invariant of Def 9.8 for `Q`: every inner node of `Q` has a label in `Λ₂[C]`. -/
lemma LoadedCluster.Q_inner_label_mem_lambdaTwo (C : LoadedCluster tab) :
    ∀ q ∈ C.Q.subtrees, q.children ≠ [] → q.label ∈ C.lambdaTwo :=
  QuasiTab.build_inner_label_mem _ _

/-- Remark 9.9 for `Q`: all leaves of the quasi-tableau have type 1. Here `h97d` is
Lemma 9.7 (d), which we state as a hypothesis: for every label in `Λ₂[C]` there is a node
of the cluster with that right component where a right rule is applied. -/
lemma LoadedCluster.Q_leaf_typ (C : LoadedCluster tab)
    (h97d : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) :
    ∀ q ∈ C.Q.subtrees, q.children = [] → q.typ = Typ.one := by
  refine QuasiTab.build_leaf_typ (fun Δ hΔ => ?_) _ _
  have := C.stepOf_ne_nil (h97d Δ hΔ)
  simp_all

/-- Def 9.10: the region `Rₓ ⊆ C⁺` represented by a node `x` of the quasi-tableau.
For type 1 and 2 these are all nodes of `C⁺` with right component `Δₓ`, and for type 3
those nodes of `C` with right component `Δₓ` where a right rule is applied. -/
noncomputable def LoadedCluster.region (C : LoadedCluster tab) :
    Typ → Sequent → Finset (FinePathIn tab)
  | .one, Δ => C.plusNodesWithFine Δ
  | .two, Δ => C.plusNodesWithFine Δ
  | .three, Δ => (C.nodesWithFineRight Δ).toFinset -- FIXME make Finset already in Cluster.lean?

/-- Def 9.10, applied to a node of the quasi-tableau. -/
noncomputable def LoadedCluster.regionOf (C : LoadedCluster tab) (q : QuasiTab) :
    Finset (FinePathIn tab) := C.region q.typ q.label

/-! ### Addresses: the nodes of a quasi-tableau

`QuasiTab` is an inductive tree, so its nodes are not determined by their type and label:
several nodes of `Q` may carry the same type and the same label. To speak about the *nodes*
of `Q`, and in particular about the tree order `<_Q` needed for repeats and companions, we
identify a node with its *address*, i.e. with the list of child indices that leads to it
from the root. Hence `r_Q` is the empty address, `x ≤_Q y` becomes "`x` is a prefix of `y`"
and `x <_Q y` becomes "`x` is a proper prefix of `y`". -/

namespace QuasiTab

/-- The subtree of `q` rooted at the node with address `x`, if there is such a node. -/
def at? : QuasiTab → List Nat → Option QuasiTab
  | q, [] => some q
  | q, (i :: rest) =>
    match q.children[i]? with
    | none => none
    | some c => c.at? rest

/-- Is there a node at address `x` in `q`? -/
def isNodeAt (q : QuasiTab) (x : List Nat) : Bool := (q.at? x).isSome

/-- The set `Q` of all nodes, given by their addresses. -/
def addresses : QuasiTab → List (List Nat)
  | .QNode _ _ next =>
      [] :: (next.map addresses).zipIdx.flatMap (fun p => p.1.map (fun a => p.2 :: a))

/-- The label `Δₓ` of the node at address `x`. -/
def labelAt (q : QuasiTab) (x : List Nat) : Option Sequent := (q.at? x).map label

/-- The type `k(x)` of the node at address `x`. -/
def typAt (q : QuasiTab) (x : List Nat) : Option Typ := (q.at? x).map typ

/-- The addresses of the children of the node at address `x`. -/
def childrenAt (q : QuasiTab) (x : List Nat) : List (List Nat) :=
  match q.at? x with
  | none => []
  | some n => (List.range n.children.length).map (fun i => x ++ [i])

/-- Is the node at address `x` a leaf? (Also `false` when there is no node at `x`.) -/
def isLeafAt (q : QuasiTab) (x : List Nat) : Bool :=
  match q.at? x with
  | none => false
  | some n => n.children.isEmpty

/-- `L_Q`, the set of leaves. -/
def leaves (q : QuasiTab) : List (List Nat) := q.addresses.filter q.isLeafAt

/-- `r_Q`, the root. -/
def rootAddress : List Nat := []

/-- `x ≤_Q y`, the reflexive-transitive closure of `⋖Q`, which on addresses is the prefix
order. -/
def qle (x y : List Nat) : Prop := x <+: y

/-- `x <_Q y`, the transitive closure of `⋖Q`, which on addresses is the *proper* prefix
order. -/
def qlt (x y : List Nat) : Prop := x <+: y ∧ x ≠ y

/-- `x ⋖Q y`, i.e. `y` is a child of `x`. -/
def qedge (q : QuasiTab) (x y : List Nat) : Prop := y ∈ q.childrenAt x

/-- The companion `c(x)` of a repeat leaf `x`, that is, the node `z <_Q x` of
type 1 with the same label as `x`. Because repeats are identified at the first opportunity
there is at most one such node in a quasi-tableau; here we simply take the one closest to
the root. -/
def companion? (q : QuasiTab) (x : List Nat) : Option (List Nat) :=
  x.inits.dropLast.find? (fun z => decide (q.labelAt z = q.labelAt x ∧ q.typAt z = some .one))

/-- `x` is a *repeat* leaf of `q`, i.e. a leaf of type 1 that has a companion. -/
def isRepeatLeaf (q : QuasiTab) (x : List Nat) : Bool :=
  q.isLeafAt x && decide (q.typAt x = some .one) && (q.companion? x).isSome

/-- All repeat leaves of `q`. -/
def repeatLeaves (q : QuasiTab) : List (List Nat) := q.leaves.filter q.isRepeatLeaf

/-- `K_Q`, the set of companions. -/
def companions (q : QuasiTab) : List (List Nat) :=
  (q.repeatLeaves.filterMap q.companion?).dedup

/-- `q.cycs x` written L_<x in the paper is the set of repeat leaves `z` with `c(z) <_Q x ≤_Q z`,
i.e. the repeat leaves below `x` whose companion is a proper ancestor of `x` in `q`.
Part of Definition 9.11. -/
def cycs (q : QuasiTab) (x : List Nat) : List (List Nat) :=
  q.repeatLeaves.filter (fun z =>
    match q.companion? z with
    | none => false
    | some c => c.isPrefixOf x && !(c == x) && x.isPrefixOf z)

lemma mem_cycs_iff (q : QuasiTab) (x z : List Nat) :
    z ∈ q.cycs x ↔ z ∈ q.repeatLeaves
      ∧ ∃ c, q.companion? z = some c ∧ qlt c x ∧ qle x z := by
  simp only [cycs, List.mem_filter, qlt, qle]
  constructor
  · rintro ⟨z_in, hz⟩
    refine ⟨z_in, ?_⟩
    cases hc : q.companion? z with
    | none => rw [hc] at hz; simp at hz
    | some c =>
      rw [hc] at hz
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
        ne_eq] at hz
      exact ⟨c, rfl, ⟨List.isPrefixOf_iff_prefix.mp hz.1.1, hz.1.2⟩,
        List.isPrefixOf_iff_prefix.mp hz.2⟩
  · rintro ⟨z_in, c, hc, ⟨hcx, hcx'⟩, hxz⟩
    refine ⟨z_in, ?_⟩
    rw [hc]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    exact ⟨⟨List.isPrefixOf_iff_prefix.mpr hcx, hcx'⟩, List.isPrefixOf_iff_prefix.mpr hxz⟩

/-! ### Basic facts about addresses

These general facts about `at?`, `addresses`, `subtrees` and `childrenAt` are used both
here and in the files building on this one. -/


lemma at?_cons_none {q : QuasiTab} {i : Nat} {rest : List Nat}
    (h : q.children[i]? = none) : q.at? (i :: rest) = none := by
  cases q with
  | QNode k Δ next =>
    simp only [QuasiTab.children] at h
    simp only [at?, show (QNode k Δ next).children = next from rfl, h]

lemma at?_append (q : QuasiTab) (x w : List Nat) :
    q.at? (x ++ w) = (q.at? x).bind (fun n => n.at? w) := by
  induction x generalizing q with
  | nil => simp [at?]
  | cons i rest ih =>
    cases q with
    | QNode k Δ next =>
      simp only [List.cons_append, at?]
      cases hc : next[i]? with
      | none => simp [show (QNode k Δ next).children = next from rfl, hc]
      | some c => simp only [show (QNode k Δ next).children = next from rfl, hc]; exact ih c

lemma isSome_at?_of_isLeafAt {q : QuasiTab} {x : List Nat} (h : q.isLeafAt x) :
    (q.at? x).isSome := by
  unfold isLeafAt at h
  cases hx : q.at? x with
  | none => rw [hx] at h; simp at h
  | some n => simp

/-- Every address of a node of `q` is in `q.addresses`. -/
lemma mem_addresses_of_at? (q : QuasiTab) (x : List Nat) (h : (q.at? x).isSome) :
    x ∈ q.addresses := by
  induction x generalizing q with
  | nil => cases q with | QNode k Δ next => simp [addresses]
  | cons i rest ih =>
    cases q with
    | QNode k Δ next =>
      simp only [at?] at h
      cases hc : next[i]? with
      | none => rw [show (QNode k Δ next).children = next from rfl, hc] at h; simp at h
      | some c =>
        rw [show (QNode k Δ next).children = next from rfl, hc] at h
        simp only [addresses, List.mem_cons, List.mem_flatMap, List.mem_map]
        refine Or.inr ⟨(c.addresses, i), ?_, rest, ih c h, rfl⟩
        rw [List.mem_zipIdx_iff_getElem?]
        simp [hc]

/-- The node at an address is one of the subtrees. -/
lemma mem_subtrees_of_at? {q n : QuasiTab} {x : List Nat} (h : q.at? x = some n) :
    n ∈ q.subtrees := by
  induction x generalizing q with
  | nil =>
    cases q with
    | QNode k Δ next =>
      simp only [at?, Option.some.injEq] at h
      subst h
      simp [subtrees]
  | cons i rest ih =>
    cases q with
    | QNode k Δ next =>
      simp only [at?, show (QNode k Δ next).children = next from rfl] at h
      cases hc : next[i]? with
      | none => rw [hc] at h; simp at h
      | some c =>
        rw [hc] at h
        simp only [subtrees, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨c, List.mem_of_getElem? hc, ih h⟩

lemma childrenAt_of_at? {q n : QuasiTab} {x : List Nat} (hx : q.at? x = some n) :
    q.childrenAt x = (List.range n.children.length).map (fun i => x ++ [i]) := by
  unfold childrenAt; rw [hx]

lemma childrenAt_eq_singleton_iff (q : QuasiTab) {x y : List Nat} :
    q.childrenAt x = [y] ↔ ∃ n, q.at? x = some n ∧ n.children.length = 1 ∧ y = x ++ [0] := by
  cases hx : q.at? x with
  | none => simp [childrenAt, hx]
  | some n =>
    rw [childrenAt_of_at? hx]
    constructor
    · intro h
      have hlen : n.children.length = 1 := by have := congrArg List.length h; simpa using this
      rw [hlen] at h
      refine ⟨n, rfl, hlen, ?_⟩
      simpa using h.symm
    · rintro ⟨n', hn', hlen, rfl⟩
      cases Option.some.inj hn'
      rw [hlen]
      simp

/-! ### Auxiliary facts for Lemma 9.12 -/

/-- A prefix of the address of a node is again the address of a node. -/
lemma isSome_at?_of_prefix {q : QuasiTab} {x z : List Nat} (hxz : x <+: z)
    (hz : (q.at? z).isSome) : (q.at? x).isSome := by
  obtain ⟨w, rfl⟩ := hxz
  rw [at?_append] at hz
  cases hx : q.at? x with
  | none => rw [hx] at hz; simp at hz
  | some n => simp

/-- If `x ++ i :: w` is a node, then `x` is a node with at least `i + 1` children. -/
lemma exists_at?_of_isSome_at?_append_cons {q : QuasiTab} {x w : List Nat} {i : Nat}
    (h : (q.at? (x ++ i :: w)).isSome) : ∃ n, q.at? x = some n ∧ i < n.children.length := by
  rw [at?_append] at h
  cases hx : q.at? x with
  | none => rw [hx] at h; simp at h
  | some n =>
    rw [hx] at h
    refine ⟨n, rfl, ?_⟩
    by_contra hi
    have : n.children[i]? = none := List.getElem?_eq_none (by omega)
    simp [at?_cons_none this] at h

/-- The only node below a leaf is the leaf itself. -/
lemma eq_of_isLeafAt_of_prefix {q : QuasiTab} {x z : List Nat} (hx : q.isLeafAt x)
    (hxz : x <+: z) (hz : (q.at? z).isSome) : x = z := by
  obtain ⟨w, rfl⟩ := hxz
  cases w with
  | nil => simp
  | cons i w =>
    exfalso
    obtain ⟨n, hn, hi⟩ := exists_at?_of_isSome_at?_append_cons hz
    unfold isLeafAt at hx
    rw [hn] at hx
    simp only [List.isEmpty_iff] at hx
    simp [hx] at hi

/-- The elements of `l.inits.dropLast` are the proper prefixes of `l`. -/
lemma qlt_of_mem_inits_dropLast {c l : List Nat} (h : c ∈ l.inits.dropLast) : qlt c l := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_dropLast, List.length_inits, Nat.add_sub_cancel] at hi
  rw [List.getElem_dropLast, List.getElem_inits]
  refine ⟨List.take_prefix _ _, fun h => ?_⟩
  have := congrArg List.length h
  simp only [List.length_take] at this
  omega

/-- The companion of a node is a proper ancestor of it. -/
lemma qlt_of_companion? {q : QuasiTab} {z c : List Nat} (h : q.companion? z = some c) :
    qlt c z :=
  qlt_of_mem_inits_dropLast (List.mem_of_find?_eq_some h)

lemma mem_repeatLeaves (q : QuasiTab) (z : List Nat) :
    z ∈ q.repeatLeaves ↔ q.isRepeatLeaf z := by
  simp only [repeatLeaves, leaves, List.mem_filter, and_iff_right_iff_imp]
  intro h
  have hleaf : q.isLeafAt z := by
    simp only [isRepeatLeaf, Bool.and_eq_true] at h
    exact h.1.1
  exact ⟨mem_addresses_of_at? q z (isSome_at?_of_isLeafAt hleaf), hleaf⟩

lemma isLeafAt_of_isRepeatLeaf {q : QuasiTab} {z : List Nat} (h : q.isRepeatLeaf z) :
    q.isLeafAt z := by
  simp only [isRepeatLeaf, Bool.and_eq_true] at h
  exact h.1.1

/-- Every element of `q.addresses` is the address of a node. -/
theorem isSome_at?_of_mem_addresses :
    ∀ (q : QuasiTab) (x : List Nat), x ∈ q.addresses → (q.at? x).isSome
  | .QNode k Δ next, x, hx => by
    simp only [addresses, List.mem_cons, List.mem_flatMap, List.mem_map] at hx
    rcases hx with rfl | ⟨⟨a, i⟩, hp, w, hw, rfl⟩
    · simp [at?]
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at hp
      cases hc : next[i]? with
      | none => rw [hc] at hp; simp at hp
      | some c =>
        rw [hc] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        have hmem : c ∈ next := List.mem_of_getElem? hc
        simp only [at?, show (QNode k Δ next).children = next from rfl, hc]
        exact isSome_at?_of_mem_addresses c w hw
termination_by q => sizeOf q
decreasing_by
  have := List.sizeOf_lt_of_mem hmem
  simp only [QNode.sizeOf_spec]
  omega

lemma mem_addresses_iff (q : QuasiTab) (x : List Nat) :
    x ∈ q.addresses ↔ (q.at? x).isSome :=
  ⟨isSome_at?_of_mem_addresses q x, mem_addresses_of_at? q x⟩

lemma pairwise_snd_lt_zipIdx {α} (l : List α) (n : Nat) :
    (l.zipIdx n).Pairwise (fun a b => a.2 < b.2) := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, ih (n + 1)⟩
    have := (List.mem_zipIdx (x := b.1) (i := b.2) hb).1
    simp only at this ⊢
    omega

lemma append_lt_append_left {p a b : List Nat} (h : a < b) : p ++ a < p ++ b := by
  induction p with
  | nil => simpa using h
  | cons i p ih => exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, ih⟩)

/-- The addresses are listed in (strictly increasing) lexicographic order. -/
theorem addresses_pairwise : ∀ q : QuasiTab, q.addresses.Pairwise (· < ·)
  | .QNode k Δ next => by
    have ih : ∀ c ∈ next, c.addresses.Pairwise (· < ·) := fun c hc => addresses_pairwise c
    simp only [addresses]
    refine List.Pairwise.cons ?_ ?_
    · intro a ha
      simp only [List.mem_flatMap, List.mem_map] at ha
      obtain ⟨_, _, w, _, rfl⟩ := ha
      exact List.nil_lt_cons _ _
    · rw [List.pairwise_flatMap]
      constructor
      · rintro ⟨a, i⟩ hp
        rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at hp
        cases hc : next[i]? with
        | none => rw [hc] at hp; simp at hp
        | some c =>
          rw [hc] at hp
          simp only [Option.map_some, Option.some.injEq] at hp
          subst hp
          rw [List.pairwise_map]
          exact (ih c (List.mem_of_getElem? hc)).imp
            (fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩))
      · refine (pairwise_snd_lt_zipIdx _ 0).imp ?_
        rintro ⟨a, i⟩ ⟨b, j⟩ hij u hu v hv
        simp only [List.mem_map] at hu hv
        obtain ⟨u, -, rfl⟩ := hu
        obtain ⟨v, -, rfl⟩ := hv
        exact List.cons_lt_cons_iff.2 (Or.inl hij)
termination_by q => sizeOf q
decreasing_by
  have := List.sizeOf_lt_of_mem hc
  simp only [QNode.sizeOf_spec]
  omega

lemma repeatLeaves_pairwise (q : QuasiTab) : q.repeatLeaves.Pairwise (· < ·) :=
  ((addresses_pairwise q).filter _).filter _

lemma cycs_pairwise (q : QuasiTab) (x : List Nat) : (q.cycs x).Pairwise (· < ·) :=
  (repeatLeaves_pairwise q).filter _

/-- A node that is not a leaf and has a unique child `x ++ [0]` lies above every
node strictly below it only via that child. -/
lemma prefix_of_qlt_of_length_eq_one {q n : QuasiTab} {x z : List Nat}
    (hn : q.at? x = some n) (hlen : n.children.length = 1) (hxz : qlt x z)
    (hz : (q.at? z).isSome) : x ++ [0] <+: z := by
  obtain ⟨⟨w, rfl⟩, hne⟩ := hxz
  cases w with
  | nil => simp at hne
  | cons i w =>
    obtain ⟨n', hn', hi⟩ := exists_at?_of_isSome_at?_append_cons hz
    rw [hn] at hn'
    cases Option.some.inj hn'
    have : i = 0 := by omega
    subst this
    exact ⟨w, by simp⟩

/-! ### Lemma 9.12 -/

/-- Lemma 9.12 (a), first half: a repeat leaf has type 1. -/
lemma typAt_of_isRepeatLeaf (q : QuasiTab) {x : List Nat} (h : q.isRepeatLeaf x) :
    q.typAt x = some .one := by
  simp only [isRepeatLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Lemma 9.12 (a), second half: a companion node has type 1. -/
lemma typAt_of_mem_companions (q : QuasiTab) {x : List Nat} (h : x ∈ q.companions) :
    q.typAt x = some .one := by
  simp only [companions, List.mem_dedup, List.mem_filterMap] at h
  obtain ⟨z, -, hz⟩ := h
  have := List.find?_some hz
  simp only [decide_eq_true_eq] at this
  exact this.2

/-- Lemma 9.12 (b) first part: the root has no cycles below it, `cycs(r_Q) = ∅`. -/
lemma cycs_root (q : QuasiTab) : q.cycs rootAddress = [] := by
  simp only [cycs, rootAddress, List.filter_eq_nil_iff]
  intro z _
  cases q.companion? z with
  | none => simp
  | some c => cases c <;> simp [List.isPrefixOf]

/-- Helper for Lemma 9.12 (d).
Note that from `x <_Q y` alone we cannot conclude `cycs(x) ⊆ cycs(y)`, because a repeat
leaf `z ∈ cycs(x)` may lie below a *different* child of `x` than `y` does.
Hence here we additionally demand `y ≤_Q z`. -/
lemma mem_cycs_of_mem_cycs_of_qlt (q : QuasiTab) {x y z : List Nat}
    (hxy : qlt x y) (hz : z ∈ q.cycs x) (hyz : qle y z) : z ∈ q.cycs y := by
  rw [mem_cycs_iff] at hz ⊢
  obtain ⟨z_in, c, hc, ⟨hcx, hcx'⟩, -⟩ := hz
  refine ⟨z_in, c, hc, ⟨hcx.trans hxy.1, ?_⟩, hyz⟩
  rintro rfl
  exact hxy.2 (hxy.1.eq_of_length (le_antisymm hxy.1.length_le hcx.length_le))

/-- Helper for Lemma 9.12 (d) `cycs_of_noRep_noComp`.
Note that when `x` has several children then the inclusion `cycs(y) ⊆ cycs(x)` may be strict.
Still the inclusion holds in general, and it is the direction that we actually use. -/
lemma cycs_subset_of_qedge (q : QuasiTab) {x y : List Nat}
    (hx : x ∉ q.companions) (hxy : q.qedge x y) : ∀ z ∈ q.cycs y, z ∈ q.cycs x := by
  intro z hz
  rw [mem_cycs_iff] at hz ⊢
  obtain ⟨z_in, c, hc, ⟨hcy, hcy'⟩, hyz⟩ := hz
  obtain ⟨i, rfl⟩ : ∃ i, x ++ [i] = y := by
    simp only [qedge, childrenAt] at hxy
    cases h : q.at? x with
    | none => rw [h] at hxy; simp at hxy
    | some n =>
      rw [h] at hxy
      simp only [List.mem_map, List.mem_range] at hxy
      obtain ⟨i, -, rfl⟩ := hxy
      exact ⟨i, rfl⟩
  refine ⟨z_in, c, hc, ⟨?_, ?_⟩, (List.prefix_append x [i]).trans hyz⟩
  · rcases (List.prefix_concat_iff.mp hcy) with h | h
    · exact absurd h hcy'
    · exact h
  · rintro rfl
    exact hx (by
      simp only [companions, List.mem_dedup, List.mem_filterMap]
      exact ⟨z, z_in, hc⟩)

/-- Lemma 9.12 (b) second part: every repeat only has itself in `cycs`. -/
lemma cycs_repeat (q : QuasiTab) : q.isRepeatLeaf r → q.cycs r = [r] := by
  intro isRep
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (cycs_pairwise q r)
    (List.pairwise_singleton _ _) (fun z => ?_)
  rw [mem_cycs_iff, List.mem_singleton]
  constructor
  · rintro ⟨z_in, -, -, -, hrz⟩
    rw [mem_repeatLeaves] at z_in
    exact (eq_of_isLeafAt_of_prefix (isLeafAt_of_isRepeatLeaf isRep) hrz
      (isSome_at?_of_isLeafAt (isLeafAt_of_isRepeatLeaf z_in))).symm
  · rintro rfl
    have hc : (q.companion? z).isSome := by
      simp only [isRepeatLeaf, Bool.and_eq_true] at isRep
      exact isRep.2
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
    exact ⟨(mem_repeatLeaves q z).2 isRep, c, hc, qlt_of_companion? hc, List.prefix_refl _⟩

/-- Lemma 9.12 (c) main part, without the companion assumption:
if `x` has unique child `y`, then `cycs(y)` consists (up to permutation) of
`cycs(x)` together with the repeat leaves whose companion is `x`. -/
lemma cycs_of_one_child (q : QuasiTab) {x y : List Nat}
    (one_child : q.childrenAt x = [y]) :
    (q.cycs y).Perm (q.cycs x ++ q.repeatLeaves.filter (fun z => q.companion? z = some x)) := by
  obtain ⟨n, hn, hlen, rfl⟩ := (childrenAt_eq_singleton_iff q).1 one_child
  have hnodup : (q.cycs x ++ q.repeatLeaves.filter (fun z => q.companion? z = some x)).Nodup := by
    rw [List.nodup_append]
    refine ⟨(cycs_pairwise q x).nodup, ((repeatLeaves_pairwise q).filter _).nodup, ?_⟩
    intro a ha b hb hab
    subst hab
    rw [mem_cycs_iff] at ha
    obtain ⟨-, c, hc, hcx, -⟩ := ha
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    rw [hb.2, Option.some.injEq] at hc
    exact hcx.2 hc.symm
  rw [List.perm_ext_iff_of_nodup (cycs_pairwise q _).nodup hnodup]
  intro z
  rw [List.mem_append, List.mem_filter, mem_cycs_iff, mem_cycs_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨z_in, c, hc, hcy, hyz⟩
    rcases List.prefix_concat_iff.mp hcy.1 with h | h
    · exact absurd h hcy.2
    · by_cases hcx : c = x
      · subst hcx
        exact Or.inr ⟨z_in, hc⟩
      · exact Or.inl ⟨z_in, c, hc, ⟨h, hcx⟩, (List.prefix_append _ _).trans hyz⟩
  · have hc_lt : ∀ c, c <+: x → qlt c (x ++ [0]) := fun c h =>
      ⟨h.trans (List.prefix_append _ _), fun h' => by
        have := congrArg List.length h'
        have := h.length_le
        simp only [List.length_append, List.length_singleton] at *
        omega⟩
    have hzSome : ∀ z, z ∈ q.repeatLeaves → (q.at? z).isSome := fun z hz =>
      isSome_at?_of_isLeafAt (isLeafAt_of_isRepeatLeaf ((mem_repeatLeaves q z).1 hz))
    rintro (⟨z_in, c, hc, hcx, hxz⟩ | ⟨z_in, hc⟩)
    · have hxz' : qlt x z := ⟨hxz, by
        rintro rfl
        have := isLeafAt_of_isRepeatLeaf ((mem_repeatLeaves q x).1 z_in)
        unfold isLeafAt at this
        rw [hn] at this
        simp only [List.isEmpty_iff] at this
        simp [this] at hlen⟩
      exact ⟨z_in, c, hc, hc_lt c hcx.1,
        prefix_of_qlt_of_length_eq_one hn hlen hxz' (hzSome z z_in)⟩
    · exact ⟨z_in, x, hc, hc_lt x (List.prefix_refl _),
        prefix_of_qlt_of_length_eq_one hn hlen (qlt_of_companion? hc) (hzSome z z_in)⟩

/-- Lemma 9.12 (c), disjointness: no element of `cycs(x)` has `x` as its companion -/
lemma cycs_comp_unique_child_disjoint (q : QuasiTab) (x : List Nat) :
    ∀ z ∈ q.cycs x, z ∉ q.repeatLeaves.filter (fun z => q.companion? z = some x) := by
  intro z hz hz'
  rw [mem_cycs_iff] at hz
  obtain ⟨-, c, hc, hcx, -⟩ := hz
  simp only [List.mem_filter, decide_eq_true_eq] at hz'
  rw [hz'.2, Option.some.injEq] at hc
  exact hcx.2 hc.symm

/-- Lemma 9.12 (d): If `x` is neither a repeat leaf nor a companion,
then `cycs x` consists of `cycs y` for all children `y` of `x`. -/
lemma cycs_of_noRep_noComp (q : QuasiTab) {x : List Nat} :
    ¬ q.isRepeatLeaf x → ¬ x ∈ q.companions → q.cycs x = (q.childrenAt x).flatMap q.cycs := by
  intro hRep hComp
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) (cycs_pairwise q x) ?_ (fun z => ?_)
  · rw [List.pairwise_flatMap]
    refine ⟨fun y _ => cycs_pairwise q y, ?_⟩
    cases hn : q.at? x with
    | none => simp [childrenAt, hn]
    | some n =>
      rw [childrenAt_of_at? hn, List.pairwise_map]
      refine (List.pairwise_lt_range (n := n.children.length)).imp ?_
      intro i j hij a ha b hb
      obtain ⟨-, -, -, -, u, rfl⟩ := (mem_cycs_iff q _ a).1 ha
      obtain ⟨-, -, -, -, v, rfl⟩ := (mem_cycs_iff q _ b).1 hb
      simp only [List.append_assoc, List.singleton_append]
      exact append_lt_append_left (List.cons_lt_cons_iff.2 (Or.inl hij))
  · rw [List.mem_flatMap]
    constructor
    · intro hz
      have hz' := hz
      rw [mem_cycs_iff] at hz
      obtain ⟨z_in, c, hc, hcx, hxz⟩ := hz
      have hzRep := (mem_repeatLeaves q z).1 z_in
      have hxz' : x ≠ z := by rintro rfl; exact hRep hzRep
      obtain ⟨w, rfl⟩ := hxz
      cases w with
      | nil => simp at hxz'
      | cons i w =>
        obtain ⟨n, hn, hi⟩ := exists_at?_of_isSome_at?_append_cons
          (isSome_at?_of_isLeafAt (isLeafAt_of_isRepeatLeaf hzRep))
        refine ⟨x ++ [i], by rw [childrenAt_of_at? hn]; simp [hi], ?_⟩
        exact mem_cycs_of_mem_cycs_of_qlt q ⟨List.prefix_append _ _, by simp⟩ hz' ⟨w, by simp⟩
    · rintro ⟨y, hy, hz⟩
      exact cycs_subset_of_qedge q hComp hy z hz

end QuasiTab
