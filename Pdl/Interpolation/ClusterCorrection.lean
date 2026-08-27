import Pdl.Interpolation.Cluster

/-! # Where Lemma 9.12 (c) and (d) fail, and counterexamples

Lemma 9.12 (c) and (d) of the paper are false as stated, because a repeat leaf below a node
`x` need not lie below the particular child `y` of `x` that is considered: this happens
whenever `x` has several children, i.e. at nodes of type 3. The versions that are actually
used in the paper — `QuasiTab.mem_cycs_of_mem_cycs_of_qlt` for (c) and
`QuasiTab.cycs_subset_of_qedge` for (d) — are in `Pdl.InterpolationCluster`.

This file collects the material documenting the failure: the exact conditions under which
(c) and (d) *do* hold, the branching pattern that refutes them, an explicit counterexample
that is produced by the construction of Def 9.8, and the corresponding statements about the
quasi-tableau `LoadedCluster.Q` of a cluster.

Nothing else depends on this file. -/

variable {X : Sequent} {tab : Tableau .nil X}

namespace QuasiTab

/-! ### Where (c) and (d) hold, and where they fail

The reason why Lemma 9.12 (c) and (d) fail in general is purely a matter of the *shape* of
the tree: if `x` has several children then a repeat leaf below one child is not below the
other children. We now make this precise. Using the basic facts about `at?` and addresses
from `Pdl.InterpolationCluster`, we first show
the positive result that (d) does hold at every node with a unique child
(`cycs_eq_of_childrenAt_eq_singleton`, `cycs_eq_of_qedge_of_typ_ne_three`), and finally the
precise branching pattern that refutes (c) and (d) (`cycs_failure_of_shape`). -/

/-- Two sets of cycles that contain each other are equal (both are filters of the same
list of repeat leaves). -/
lemma cycs_eq_of_subsets {q : QuasiTab} {x y : List Nat} (h1 : ∀ z ∈ q.cycs x, z ∈ q.cycs y)
    (h2 : ∀ z ∈ q.cycs y, z ∈ q.cycs x) : q.cycs x = q.cycs y := by
  unfold cycs
  apply List.filter_congr
  intro z hz
  rw [Bool.eq_iff_iff]
  constructor
  · intro hp
    have := h1 z (by rw [cycs]; exact List.mem_filter.mpr ⟨hz, hp⟩)
    rw [cycs] at this
    exact (List.mem_filter.mp this).2
  · intro hp
    have := h2 z (by rw [cycs]; exact List.mem_filter.mpr ⟨hz, hp⟩)
    rw [cycs] at this
    exact (List.mem_filter.mp this).2

/-- The missing half of Lemma 9.12 (d) when `x` has a *unique* child `y`: every repeat leaf
below `x` is then also below `y`. -/
lemma mem_cycs_of_childrenAt_eq_singleton (q : QuasiTab) {x y : List Nat}
    (h : q.childrenAt x = [y]) : ∀ z ∈ q.cycs x, z ∈ q.cycs y := by
  obtain ⟨n, hn, hlen, rfl⟩ := (childrenAt_eq_singleton_iff q).mp h
  intro z hz
  rw [mem_cycs_iff] at hz ⊢
  obtain ⟨z_in, c, hc, ⟨hcx, hcx'⟩, hxz⟩ := hz
  have hzleaf : q.isLeafAt z := by
    simp only [repeatLeaves, List.mem_filter, isRepeatLeaf, Bool.and_eq_true] at z_in
    exact z_in.2.1.1
  have hzsome : (q.at? z).isSome := isSome_at?_of_isLeafAt hzleaf
  have hxne : z ≠ x := by
    rintro rfl
    unfold isLeafAt at hzleaf
    rw [hn] at hzleaf
    simp only [List.isEmpty_iff] at hzleaf
    rw [hzleaf] at hlen
    simp at hlen
  obtain ⟨w, rfl⟩ := hxz
  have hw : w ≠ [] := by rintro rfl; simp at hxne
  obtain ⟨a, t, rfl⟩ : ∃ a t, w = a :: t := by
    cases w with
    | nil => exact absurd rfl hw
    | cons a t => exact ⟨a, t, rfl⟩
  have ha : a = 0 := by
    rw [at?_append, hn] at hzsome
    simp only [Option.bind_some] at hzsome
    cases hnc : n.children[a]? with
    | none => rw [at?_cons_none hnc] at hzsome; simp at hzsome
    | some c' =>
      have h2 : a < n.children.length := List.getElem?_eq_some_iff.mp hnc |>.1
      omega
  subst ha
  refine ⟨z_in, c, hc, ⟨hcx.trans ⟨[0], rfl⟩, ?_⟩, ⟨t, by simp⟩⟩
  rintro rfl
  have := hcx.length_le
  simp at this

/-- Lemma 9.12 (d) *does* hold at every node that has exactly one child. -/
lemma cycs_eq_of_childrenAt_eq_singleton (q : QuasiTab) {x y : List Nat}
    (hx : x ∉ q.companions) (h : q.childrenAt x = [y]) : q.cycs x = q.cycs y :=
  cycs_eq_of_subsets (mem_cycs_of_childrenAt_eq_singleton q h)
    (cycs_subset_of_qedge q hx (by rw [qedge, h]; simp))

/-- Lemma 9.12 (d) holds at every node with at most one child. -/
lemma cycs_eq_of_qedge_of_children_le_one (q : QuasiTab) {x y : List Nat}
    (hx : x ∉ q.companions) (hle : ∀ n, q.at? x = some n → n.children.length ≤ 1)
    (hxy : q.qedge x y) : q.cycs x = q.cycs y := by
  refine cycs_eq_of_childrenAt_eq_singleton q hx ?_
  cases hn : q.at? x with
  | none => rw [qedge, childrenAt, hn] at hxy; simp at hxy
  | some n =>
    rw [qedge, childrenAt_of_at? hn] at hxy
    simp only [List.mem_map, List.mem_range] at hxy
    obtain ⟨i, hi, rfl⟩ := hxy
    have hn1 := hle n hn
    have hi0 : i = 0 := by omega
    subst hi0
    have hlen : n.children.length = 1 := by omega
    rw [childrenAt_of_at? hn, hlen]
    simp

/-- Lemma 9.12 (d) holds at every node that is not of type 3, provided all nodes of `q`
that are not of type 3 have at most one child — which is the case for the quasi-tableaux
of Def 9.8, see `LoadedCluster.Q_cycs_eq_of_qedge_of_typ_ne_three`. -/
lemma cycs_eq_of_qedge_of_typ_ne_three {q : QuasiTab}
    (hq : ∀ n ∈ q.subtrees, n.typ ≠ Typ.three → n.children.length ≤ 1)
    {x y : List Nat} (hx : x ∉ q.companions) (hty : q.typAt x ≠ some Typ.three)
    (hxy : q.qedge x y) : q.cycs x = q.cycs y := by
  refine cycs_eq_of_qedge_of_children_le_one q hx (fun n hn => ?_) hxy
  refine hq n (mem_subtrees_of_at? hn) (fun h => hty ?_)
  rw [typAt, hn]
  simp [h]

/-- The branching pattern that refutes Lemma 9.12 (c) and (d) as stated: a node `x` of
type 3 with at least two children, the first of which is a leaf of type 1 that repeats the
label `D'` of some node `z ≤_Q x` of type 1.

The repeat leaf `x ++ [0]` is then in `cycs(x)`, while it is not in `cycs(y)` for the
sibling `y = x ++ [1]` — even though `x <_Q y`, `x ⋖Q y` and `x` is not a companion. -/
theorem cycs_failure_of_branching_repeat {q : QuasiTab} {x : List Nat} {D D' : Sequent}
    {c1 : QuasiTab} {cs : List QuasiTab}
    (hx : q.at? x = some (QNode Typ.three D (QNode Typ.one D' [] :: c1 :: cs)))
    {z : List Nat} (hz : z <+: x) (hzlab : q.labelAt z = some D')
    (hztyp : q.typAt z = some Typ.one) :
    x ++ [0] ∈ q.cycs x ∧ x ++ [0] ∉ q.cycs (x ++ [1]) ∧ x ∉ q.companions
      ∧ q.qedge x (x ++ [1]) ∧ qlt x (x ++ [1]) := by
  have har : q.at? (x ++ [0]) = some (QNode Typ.one D' []) := by
    rw [at?_append, hx]; rfl
  have hlab_r : q.labelAt (x ++ [0]) = some D' := by rw [labelAt, har]; rfl
  have htyp_r : q.typAt (x ++ [0]) = some Typ.one := by rw [typAt, har]; rfl
  have hleaf_r : q.isLeafAt (x ++ [0]) := by rw [isLeafAt, har]; rfl
  have htyp_x : q.typAt x = some Typ.three := by rw [typAt, hx]; rfl
  have hinits : (x ++ [0]).inits.dropLast = x.inits := by rw [List.inits_append]; simp
  set p : List Nat → Bool :=
    fun w => decide (q.labelAt w = q.labelAt (x ++ [0]) ∧ q.typAt w = some Typ.one) with hp
  have hpz : p z := by simp [hp, hzlab, hztyp, hlab_r]
  have hne : List.find? p x.inits ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    exact hnone z ((List.mem_inits _ _).mpr hz) hpz
  obtain ⟨c, hc⟩ : ∃ c, List.find? p x.inits = some c := Option.ne_none_iff_exists'.mp hne
  have hcomp : q.companion? (x ++ [0]) = some c := by
    rw [companion?, hinits, ← hp, hc]
  have hcp : c <+: x := (List.mem_inits _ _).mp (List.mem_of_find?_eq_some hc)
  have hctyp : q.typAt c = some Typ.one := by
    have := List.find?_some hc
    simp only [hp, decide_eq_true_eq] at this
    exact this.2
  have hcx : c ≠ x := by
    intro h; rw [h, htyp_x] at hctyp; simp at hctyp
  have hrep : q.isRepeatLeaf (x ++ [0]) := by
    simp only [isRepeatLeaf, hcomp, Bool.and_eq_true, decide_eq_true_eq, hleaf_r,
      Option.isSome_some, and_true, htyp_r]
  have hmem : (x ++ [0]) ∈ q.repeatLeaves := by
    simp only [repeatLeaves, leaves, List.mem_filter]
    exact ⟨⟨mem_addresses_of_at? q _ (by rw [har]; rfl), hleaf_r⟩, hrep⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_cycs_iff]
    exact ⟨hmem, c, hcomp, ⟨hcp, hcx⟩, ⟨[0], rfl⟩⟩
  · rw [mem_cycs_iff]
    rintro ⟨-, c', hc', -, hpre⟩
    rw [qle, List.prefix_append_right_inj] at hpre
    simp [List.prefix_iff_eq_take] at hpre
  · intro hin
    rw [typAt_of_mem_companions q hin] at htyp_x
    simp at htyp_x
  · rw [qedge, childrenAt_of_at? hx]
    simp only [List.mem_map, List.mem_range]
    exact ⟨1, by simp [QuasiTab.children], rfl⟩
  · exact ⟨⟨[1], rfl⟩, by simp⟩

/-- The special case of `cycs_failure_of_branching_repeat` where the repeat leaf is at
address `[0,0,0]` and its companion is the root. This is used both for the quasi-tableau
built by `QuasiTab.build` in `QuasiTabCEx` below and for the quasi-tableau
`LoadedCluster.Q` of a cluster. -/
theorem cycs_failure_of_shape {Δ : Sequent} {c1 : QuasiTab} {cs : List QuasiTab}
    {q : QuasiTab}
    (hq : q = QNode Typ.one Δ
      [QNode Typ.two Δ [QNode Typ.three Δ (QNode Typ.one Δ [] :: c1 :: cs)]]) :
    [0,0,0] ∈ q.cycs [0,0] ∧ [0,0,0] ∉ q.cycs [0,0,1] ∧ [0,0] ∉ q.companions
      ∧ q.qedge [0,0] [0,0,1] ∧ qlt [0,0] [0,0,1] := by
  have := cycs_failure_of_branching_repeat (q := q) (x := [0,0]) (z := [])
    (by subst hq; rfl) List.nil_prefix (by subst hq; rfl) (by subst hq; rfl)
  simpa using this

/-- If the rule at every label has at most one conclusion then no node of a quasi-tableau
built by `QuasiTab.build` branches, and hence Lemma 9.12 (d) holds everywhere in it, see
`LoadedCluster.Q_cycs_eq_of_qedge_of_stepOf_le_one`. -/
lemma build_children_length_le_one {inC : List Sequent} {step : Sequent → List Sequent}
    (hstep : ∀ Δ, (step Δ).length ≤ 1) (Hist Δ) :
    ∀ n ∈ (QuasiTab.build inC step Hist Δ).subtrees, n.children.length ≤ 1 := by
  induction Hist, Δ using QuasiTab.build.induct (inC := inC) with
  | case1 Hist Δ h IH =>
    intro n n_in
    rw [QuasiTab.build_of_node h] at n_in
    simp only [QuasiTab.subtrees, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons] at n_in
    rcases n_in with rfl | rfl | rfl | n_in
    · simp [QuasiTab.children]
    · simp [QuasiTab.children]
    · simpa [QuasiTab.children] using hstep Δ
    · simp only [List.mem_flatMap, List.mem_map] at n_in
      obtain ⟨t, ⟨Pi, Pi_in, rfl⟩, n_in⟩ := n_in
      exact IH Pi n n_in
  | case2 Hist Δ h =>
    intro n n_in
    rw [QuasiTab.build_of_leaf h] at n_in
    simp only [QuasiTab.subtrees, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at n_in
    subst n_in
    simp [QuasiTab.children]

/-- In a quasi-tableau built by `QuasiTab.build`, i.e. in one that is constructed as in
Def 9.8, only nodes of type 3 can have more than one child. -/
lemma build_children_length_le_one_of_typ_ne_three {inC : List Sequent}
    {step : Sequent → List Sequent} (Hist Δ) :
    ∀ n ∈ (QuasiTab.build inC step Hist Δ).subtrees, n.typ ≠ Typ.three →
      n.children.length ≤ 1 := by
  induction Hist, Δ using QuasiTab.build.induct (inC := inC) with
  | case1 Hist Δ h IH =>
    intro n n_in hn
    rw [QuasiTab.build_of_node h] at n_in
    simp only [QuasiTab.subtrees, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_cons] at n_in
    rcases n_in with rfl | rfl | rfl | n_in
    · simp [QuasiTab.children]
    · simp [QuasiTab.children]
    · exact absurd rfl hn
    · simp only [List.mem_flatMap, List.mem_map] at n_in
      obtain ⟨t, ⟨Pi, Pi_in, rfl⟩, n_in⟩ := n_in
      exact IH Pi n n_in hn
  | case2 Hist Δ h =>
    intro n n_in hn
    rw [QuasiTab.build_of_leaf h] at n_in
    simp only [QuasiTab.subtrees, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false] at n_in
    subst n_in
    simp [QuasiTab.children]

end QuasiTab

/-! ### Counterexamples to Lemma 9.12 (c) and (d) as stated

The counterexample below is not just an arbitrary value of the data type `QuasiTab`: it is
a quasi-tableau *produced by the construction of Def 9.8*, i.e. one of the form
`QuasiTab.build inC step [] Δ`, which is exactly how `LoadedCluster.Q` is defined. Moreover
the data `inCEx` and `stepEx` used here satisfy all the properties that we know about the
cluster data `LoadedCluster.lambdaTwo` and `LoadedCluster.stepOf`, namely that the labels
produced by the step function are in `Λ₂[C⁺]` (`stepEx_mem`), that the step function is
nonempty on `Λ₂[C]` (`stepEx_ne_nil`, this is Lemma 9.7 (d),(e),(f)) and that the label of
the root is in `Λ₂[C]` (`A_mem_inCEx`). Hence the failure of (c) and (d) cannot be repaired
using any of these properties: what makes them fail is only the branching at a node of
type 3, see `QuasiTab.cycs_failure_of_shape`.

For statements directly about the quasi-tableau `LoadedCluster.Q` of a cluster see
`LoadedCluster.Q_cycs_not_monotone` and `LoadedCluster.Q_cycs_not_eq_of_qedge` below. -/

namespace QuasiTabCEx

/-- A first label. -/
def A : Sequent := ([], [], none)

/-- A second label, different from `A`. -/
def B : Sequent := ([], [⊥], none)

/-- Stand-in for `Λ₂[C]`: the only label of a node inside the cluster is `A`. -/
def inCEx : List Sequent := [A]

/-- Stand-in for `C.stepOf`: the right rule applied at nodes with right component `A`
splits into two children, one labelled `A` (which will become a repeat) and one labelled
`B` (which will become an exit, as `B ∉ inCEx`). -/
def stepEx : Sequent → List Sequent := fun _ => [A, B]

/-- The root label is in the stand-in for `Λ₂[C]`, cf.
`LoadedCluster.root_rightOnly_mem_lambdaTwo`. -/
lemma A_mem_inCEx : A ∈ inCEx := by simp [inCEx]

/-- The stand-in for `C.stepOf` is nonempty on the stand-in for `Λ₂[C]`, cf.
`LoadedCluster.stepOf_ne_nil`. -/
lemma stepEx_ne_nil : ∀ Δ ∈ inCEx, stepEx Δ ≠ [] := by simp [stepEx]

/-- The labels produced by the stand-in for `C.stepOf` are in the stand-in `[A, B]` for
`Λ₂[C⁺]`, cf. `LoadedCluster.stepOf_mem_lambdaTwoPlus`. -/
lemma stepEx_mem : ∀ Δ, ∀ Pi ∈ stepEx Δ, Pi ∈ [A, B] := by simp [stepEx]

/-- A quasi-tableau built by the construction of Def 9.8, in which the type 3 node `[0,0]`
has two children: `[0,0,0]` is a repeat leaf with companion the root `[]`, and `[0,0,1]` is
an exit leaf. -/
def qCEx : QuasiTab := QuasiTab.build inCEx stepEx [] A

open Typ QuasiTab in
lemma qCEx_eq :
    qCEx = .QNode one A [ .QNode two A [ .QNode three A
      [ .QNode one A [], .QNode one B [] ] ] ] := by
  rw [qCEx, QuasiTab.build_of_node ⟨A_mem_inCEx, by simp⟩]
  simp only [stepEx, List.map_cons, List.map_nil]
  rw [QuasiTab.build_of_leaf (by simp), QuasiTab.build_of_leaf (by simp [inCEx, A, B])]

lemma cycs_branching : [0,0,0] ∈ qCEx.cycs [0,0] :=
  (QuasiTab.cycs_failure_of_shape qCEx_eq).1

lemma cycs_child : [0,0,0] ∉ qCEx.cycs [0,0,1] :=
  (QuasiTab.cycs_failure_of_shape qCEx_eq).2.1

lemma branching_not_companion : [0,0] ∉ qCEx.companions :=
  (QuasiTab.cycs_failure_of_shape qCEx_eq).2.2.1

lemma branching_qedge : qCEx.qedge [0,0] [0,0,1] :=
  (QuasiTab.cycs_failure_of_shape qCEx_eq).2.2.2.1

lemma branching_qlt : QuasiTab.qlt [0,0] [0,0,1] :=
  (QuasiTab.cycs_failure_of_shape qCEx_eq).2.2.2.2

/-- Lemma 9.12 (c) as stated in the paper is false, already for quasi-tableaux that are
built by the construction of Def 9.8. -/
theorem build_cycs_not_monotone :
    ¬ ∀ (inC : List Sequent) (step : Sequent → List Sequent) (Hist : List Sequent)
        (Δ : Sequent) (x y : List Nat), QuasiTab.qlt x y →
        ∀ z ∈ (QuasiTab.build inC step Hist Δ).cycs x,
          z ∈ (QuasiTab.build inC step Hist Δ).cycs y := by
  intro h
  exact cycs_child (h inCEx stepEx [] A [0,0] [0,0,1] branching_qlt [0,0,0] cycs_branching)

/-- Lemma 9.12 (d) as stated in the paper is false, already for quasi-tableaux that are
built by the construction of Def 9.8. -/
theorem build_cycs_not_eq_of_qedge :
    ¬ ∀ (inC : List Sequent) (step : Sequent → List Sequent) (Hist : List Sequent)
        (Δ : Sequent) (x y : List Nat), x ∉ (QuasiTab.build inC step Hist Δ).companions →
        (QuasiTab.build inC step Hist Δ).qedge x y →
        (QuasiTab.build inC step Hist Δ).cycs x = (QuasiTab.build inC step Hist Δ).cycs y := by
  intro h
  have := h inCEx stepEx [] A [0,0] [0,0,1] branching_not_companion branching_qedge
  rw [show QuasiTab.build inCEx stepEx [] A = qCEx from rfl] at this
  exact cycs_child (this ▸ cycs_branching)

/-- Lemma 9.12 (c) as stated in the paper is false. -/
theorem cycs_not_monotone :
    ¬ ∀ (q : QuasiTab) (x y : List Nat), QuasiTab.qlt x y → ∀ z ∈ q.cycs x, z ∈ q.cycs y := by
  intro h
  exact cycs_child (h qCEx [0,0] [0,0,1] branching_qlt [0,0,0] cycs_branching)

/-- Lemma 9.12 (d) as stated in the paper is false. -/
theorem cycs_not_eq_of_qedge :
    ¬ ∀ (q : QuasiTab) (x y : List Nat), x ∉ q.companions → q.qedge x y → q.cycs x = q.cycs y := by
  intro h
  have := h qCEx [0,0] [0,0,1] branching_not_companion branching_qedge
  exact cycs_child (this ▸ cycs_branching)

end QuasiTabCEx

/-! ### Lemma 9.12 (c) and (d) for the quasi-tableau of a cluster

We now say exactly where Lemma 9.12 (c) and (d) hold for `C.Q`, the quasi-tableau of a
loaded cluster `C`. The positive result is that (d) holds at every node that is not of
type 3, because in `C.Q` only nodes of type 3 can have more than one child; and at nodes
of type 3 the inclusion `cycs(y) ⊆ cycs(x)` still holds by `QuasiTab.cycs_subset_of_qedge`.
The negative result is that (c) and (d) do fail at a branching node of type 3 whose first
child is a repeat: this is `LoadedCluster.Q_cycs_not_monotone_at` and
`LoadedCluster.Q_cycs_not_eq_of_qedge_at`, where the repeat leaf may repeat the label of
any node of type 1 above it. As a special case, they fail for every cluster whose step
function at the label of the root returns that label together with at least one further
label (`LoadedCluster.Q_cycs_not_monotone`, `LoadedCluster.Q_cycs_not_eq_of_qedge`).

Note that the negative results are conditional on the cluster having such a branching
repeat; whether a given tableau has such a cluster of course depends on the tableau. The
hypothesis is not in conflict with anything we know about clusters, and the corresponding
data is realised by the construction of Def 9.8 in `QuasiTabCEx` above. -/

/-- In `C.Q` only nodes of type 3 can have more than one child. -/
lemma LoadedCluster.Q_children_length_le_one (C : LoadedCluster tab) :
    ∀ n ∈ C.Q.subtrees, n.typ ≠ Typ.three → n.children.length ≤ 1 :=
  QuasiTab.build_children_length_le_one_of_typ_ne_three _ _

/-- Lemma 9.12 (d) holds at every node of `C.Q` that is not of type 3. -/
lemma LoadedCluster.Q_cycs_eq_of_qedge_of_typ_ne_three (C : LoadedCluster tab) {x y : List Nat}
    (hx : x ∉ C.Q.companions) (hty : C.Q.typAt x ≠ some Typ.three) (hxy : C.Q.qedge x y) :
    C.Q.cycs x = C.Q.cycs y :=
  QuasiTab.cycs_eq_of_qedge_of_typ_ne_three C.Q_children_length_le_one hx hty hxy

/-- If no right rule in the cluster branches then Lemma 9.12 (d) holds everywhere in
`C.Q`. -/
lemma LoadedCluster.Q_cycs_eq_of_qedge_of_stepOf_le_one (C : LoadedCluster tab)
    (hstep : ∀ Δ, (C.stepOf Δ).length ≤ 1) {x y : List Nat}
    (hx : x ∉ C.Q.companions) (hxy : C.Q.qedge x y) : C.Q.cycs x = C.Q.cycs y :=
  QuasiTab.cycs_eq_of_qedge_of_children_le_one _ hx
    (fun n hn => QuasiTab.build_children_length_le_one hstep _ _ n
      (QuasiTab.mem_subtrees_of_at? hn)) hxy

open QuasiTab Typ in
/-- Lemma 9.12 (c) as stated is false for the quasi-tableau of any cluster in which some
node `x` of `Q` of type 3 branches and has a repeat leaf as its first child. -/
theorem LoadedCluster.Q_cycs_not_monotone_at (C : LoadedCluster tab) {x : List Nat}
    {D D' : Sequent} {c1 : QuasiTab} {cs : List QuasiTab}
    (hx : C.Q.at? x = some (QNode three D (QNode one D' [] :: c1 :: cs)))
    {z : List Nat} (hz : z <+: x) (hzlab : C.Q.labelAt z = some D')
    (hztyp : C.Q.typAt z = some one) :
    ¬ ∀ u v : List Nat, QuasiTab.qlt u v → ∀ w ∈ C.Q.cycs u, w ∈ C.Q.cycs v := by
  obtain ⟨h_in, h_notin, -, -, h_qlt⟩ :=
    QuasiTab.cycs_failure_of_branching_repeat hx hz hzlab hztyp
  intro h
  exact h_notin (h x (x ++ [1]) h_qlt (x ++ [0]) h_in)

open QuasiTab Typ in
/-- Lemma 9.12 (d) as stated is false for the quasi-tableau of any cluster in which some
node `x` of `Q` of type 3 branches and has a repeat leaf as its first child. -/
theorem LoadedCluster.Q_cycs_not_eq_of_qedge_at (C : LoadedCluster tab) {x : List Nat}
    {D D' : Sequent} {c1 : QuasiTab} {cs : List QuasiTab}
    (hx : C.Q.at? x = some (QNode three D (QNode one D' [] :: c1 :: cs)))
    {z : List Nat} (hz : z <+: x) (hzlab : C.Q.labelAt z = some D')
    (hztyp : C.Q.typAt z = some one) :
    ¬ ∀ u v : List Nat, u ∉ C.Q.companions → C.Q.qedge u v → C.Q.cycs u = C.Q.cycs v := by
  obtain ⟨h_in, h_notin, h_nc, h_edge, -⟩ :=
    QuasiTab.cycs_failure_of_branching_repeat hx hz hzlab hztyp
  intro h
  exact h_notin ((h x (x ++ [1]) h_nc h_edge) ▸ h_in)

open QuasiTab Typ in
/-- The shape of `C.Q` when the right rule at the label `Δ₀` of the root leads back to `Δ₀`
and to at least one further label: the type 3 node `[0,0]` then has a repeat leaf `[0,0,0]`
with companion the root, and at least one further child `[0,0,1]`. -/
lemma LoadedCluster.Q_eq_of_step_repeat (C : LoadedCluster tab)
    (h1 : (nodeAt C.root).rightOnly ∈ C.lambdaTwo)
    {Pi : Sequent} {rest : List Sequent}
    (hstep : C.stepOf (nodeAt C.root).rightOnly
      = (nodeAt C.root).rightOnly :: Pi :: rest) :
    C.Q = QNode one (nodeAt C.root).rightOnly
      [QNode two (nodeAt C.root).rightOnly
        [QNode three (nodeAt C.root).rightOnly
          (QNode one (nodeAt C.root).rightOnly []
            :: QuasiTab.build C.lambdaTwo C.stepOf [(nodeAt C.root).rightOnly] Pi
            :: rest.map (QuasiTab.build C.lambdaTwo C.stepOf [(nodeAt C.root).rightOnly]))]] := by
  rw [LoadedCluster.Q, QuasiTab.build_of_node ⟨h1, by simp⟩, hstep]
  simp only [List.map_cons]
  rw [QuasiTab.build_of_leaf (by simp)]

/-- Lemma 9.12 (c) as stated is false for the quasi-tableau of a cluster in which the right
rule at the root label leads back to the root label and to at least one further label. -/
theorem LoadedCluster.Q_cycs_not_monotone (C : LoadedCluster tab)
    (h1 : (nodeAt C.root).rightOnly ∈ C.lambdaTwo)
    {Pi : Sequent} {rest : List Sequent}
    (hstep : C.stepOf (nodeAt C.root).rightOnly = (nodeAt C.root).rightOnly :: Pi :: rest) :
    ¬ ∀ x y : List Nat, QuasiTab.qlt x y → ∀ z ∈ C.Q.cycs x, z ∈ C.Q.cycs y := by
  obtain ⟨h_in, h_notin, -, -, h_qlt⟩ :=
    QuasiTab.cycs_failure_of_shape (C.Q_eq_of_step_repeat h1 hstep)
  intro h
  exact h_notin (h [0,0] [0,0,1] h_qlt [0,0,0] h_in)

/-- Lemma 9.12 (d) as stated is false for the quasi-tableau of a cluster in which the right
rule at the root label leads back to the root label and to at least one further label. -/
theorem LoadedCluster.Q_cycs_not_eq_of_qedge (C : LoadedCluster tab)
    (h1 : (nodeAt C.root).rightOnly ∈ C.lambdaTwo)
    {Pi : Sequent} {rest : List Sequent}
    (hstep : C.stepOf (nodeAt C.root).rightOnly = (nodeAt C.root).rightOnly :: Pi :: rest) :
    ¬ ∀ x y : List Nat, x ∉ C.Q.companions → C.Q.qedge x y → C.Q.cycs x = C.Q.cycs y := by
  obtain ⟨h_in, h_notin, h_nc, h_edge, -⟩ :=
    QuasiTab.cycs_failure_of_shape (C.Q_eq_of_step_repeat h1 hstep)
  intro h
  exact h_notin ((h [0,0] [0,0,1] h_nc h_edge) ▸ h_in)
