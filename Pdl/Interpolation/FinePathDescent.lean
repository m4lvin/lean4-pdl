import Pdl.Local.PathIn

/-! # Well-founded descent for fine paths

The children of a fine node (`FinePathIn.children`) are *not* structurally smaller than the
node itself: a child of an internal node of a local tableau is again a path in the *same*
local tableau, and a child of the last internal node is a `FinePathIn.loc` step, hence even
structurally bigger. So there is no induction principle for `FinePathIn` that follows the
child relation for free.

This file provides one, in the same way as `PathIn.strong_upwards_inductionOn` is obtained
from `flipEdge.wellFounded` for the coarse `PathIn` nodes: we equip fine paths with a
`FinePathIn.length`, bound it by a size measure `Tableau.fineSize` of the tableau, and
conclude that there is no infinite chain of fine children — the child relation `fineEdge`
has a well-founded flip. From that we get

* `FinePathIn.edge_upwards_inductionOn` — induction from the leaves to the root, and
* `FinePathIn.strong_upwards_inductionOn` — its strong version, where the inductive
  hypothesis is available at all fine *descendants*, not only at the children.

Dually, `FinePathIn.descent` states the descent principle in the contrapositive form in
which it is used: if a property holds somewhere and always propagates to *some* child,
then it holds at a node without children.
-/

/-! ## A length for local paths -/

/-- The number of steps of a local path. -/
def LocalPathIn.length {X} {lt : LocalTableau X} : LocalPathIn lt → ℕ
  | .nil => 0
  | .cons _ tail => tail.length + 1

/-- The number of nodes of a local tableau. -/
def LocalTableau.nodeCount {X} : LocalTableau X → ℕ
  | .byLocalRule lra _ next =>
      1 + (lra.C.attach.map (fun ⟨Y, Y_in⟩ => (next Y Y_in).nodeCount)).sum
  | .sim _ => 1

lemma LocalTableau.nodeCount_pos {X} (lt : LocalTableau X) : 0 < lt.nodeCount := by
  cases lt <;> simp [LocalTableau.nodeCount]

lemma LocalPathIn.length_lt_nodeCount {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    lp.length < lt.nodeCount := by
  induction lp
  case nil X lt => exact lt.nodeCount_pos
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [LocalPathIn.length, LocalTableau.nodeCount]
    have key : ∀ s : ℕ, (next Y Y_in).nodeCount ≤ s → tail.length + 1 < 1 + s := by omega
    apply key
    apply List.le_sum_of_mem
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨Y, Y_in, rfl⟩

/-- Going to a child inside a local tableau increases the length. -/
lemma LocalPathIn.length_lt_of_mem_children {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    ∀ lp' ∈ lp.children, lp.length < lp'.length := by
  induction lp
  case nil X lt =>
    intro lp' h
    cases lt
    · simp only [LocalPathIn.children, List.mem_map, List.mem_attach, true_and,
        Subtype.exists] at h
      obtain ⟨Y, Y_in, rfl⟩ := h
      simp [LocalPathIn.length]
    · simp [LocalPathIn.children] at h
  case cons X lra X_def next Y Y_in tail IH =>
    intro lp' h
    simp only [LocalPathIn.children, List.mem_map] at h
    obtain ⟨lp'', h'', rfl⟩ := h
    have := IH lp'' h''
    simp only [LocalPathIn.length]
    omega

/-! ## A length for fine paths -/

/-- A size measure for tableaux that also counts the intermediate nodes of the local
tableaux, i.e. an upper bound for the length of any `FinePathIn`. -/
def Tableau.fineSize : ∀ {H X}, Tableau H X → ℕ
  | _, _, .loc _ _ lt next =>
      lt.nodeCount + (((endNodesOf lt).attach.map (fun ⟨Y, Y_in⟩ => (next Y Y_in).fineSize)).sum)
  | _, _, .pdl _ _ _ next => 1 + next.fineSize
  | _, _, .lrep _ => 1

/-- The number of steps of a fine path, where a whole local tableau counts with its
`LocalTableau.nodeCount` so that leaving it strictly increases the length. -/
def FinePathIn.length : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → ℕ
  | _, _, _, .inLoc lp _ => lp.length
  | _, _, _, .pdlHere => 0
  | _, _, _, .lrepHere => 0
  | _, _, .loc _ _ lt _, .loc _ tail => lt.nodeCount + tail.length
  | _, _, _, .pdl tail => 1 + tail.length

lemma FinePathIn.length_lt_fineSize {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    f.length < tab.fineSize := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    have := lp.length_lt_nodeCount
    simp only [FinePathIn.length, Tableau.fineSize]
    omega
  case pdlHere => simp [FinePathIn.length, Tableau.fineSize]
  case lrepHere => simp [FinePathIn.length, Tableau.fineSize]
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    simp only [FinePathIn.length, Tableau.fineSize]
    have key : ∀ s : ℕ, (next Y Y_in).fineSize ≤ s →
        lt.nodeCount + tail.length < lt.nodeCount + s := by omega
    apply key
    apply List.le_sum_of_mem
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨Y, Y_in, rfl⟩
  case pdl tail IH =>
    simp only [FinePathIn.length, Tableau.fineSize]
    omega

/-- Going to a fine child strictly increases the length of a fine path. -/
theorem FinePathIn.length_lt_of_mem_children {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    ∀ g ∈ f.children, f.length < g.length := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨lp', lp'_in, rfl⟩ := g_in
    have hlp := lp.length_lt_of_mem_children lp' lp'_in
    split
    · have := lp.length_lt_nodeCount
      simp only [FinePathIn.length]
      omega
    · simpa [FinePathIn.length] using hlp
  case pdlHere Hist X Y nrep bas r next =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_singleton] at g_in
    subst g_in
    simp [FinePathIn.length]
  case lrepHere => simp [FinePathIn.children]
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    have := IH g' g'_in
    simp only [FinePathIn.length]
    omega
  case pdl Hist X Y nrep bas r next tail IH =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    have := IH g' g'_in
    simp only [FinePathIn.length]
    omega

/-! ## The child relation on fine nodes and its well-founded flip -/

/-- The child relation on fine nodes, the fine analogue of `edge`. -/
def fineEdge {H X} {tab : Tableau H X} (f g : FinePathIn tab) : Prop := g ∈ f.children

@[inherit_doc] infixl:50 " ⋖f " => fineEdge

lemma fineEdge_then_length_lt {H X} {tab : Tableau H X} {f g : FinePathIn tab} (h : f ⋖f g) :
    f.length < g.length :=
  f.length_lt_of_mem_children g h

/-- The flipped child relation on fine nodes is well-founded. Compare `flipEdge.wellFounded`. -/
theorem flipFineEdge.wellFounded {H X} {tab : Tableau H X} :
    WellFounded (flip (@fineEdge H X tab)) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hChain
  simp only [not_isEmpty_iff, nonempty_subtype] at hChain
  rcases hChain with ⟨f, all_rel⟩
  have all_lt : ∀ n : ℕ, (f n).length < tab.fineSize := fun n => (f n).length_lt_fineSize
  have increasing : ∀ n : ℕ, (f n).length < (f (n + 1)).length :=
    fun n => fineEdge_then_length_lt (all_rel n)
  have big : ∀ n : ℕ, n < (f (n + 1)).length := by
    intro n
    induction n with
    | zero => exact lt_of_le_of_lt (Nat.zero_le _) (increasing 0)
    | succ k IH => have := increasing (k + 1); omega
  have := big tab.fineSize
  have := all_lt (tab.fineSize + 1)
  omega

/-! ## The induction principles -/

/-- Induction on fine nodes going from the leaves (= childless fine nodes) to the root.
Compare `PathIn.edge_upwards_inductionOn`. -/
theorem FinePathIn.edge_upwards_inductionOn {H X} {tab : Tableau H X}
    {motive : FinePathIn tab → Prop}
    (up : ∀ {u}, (∀ {s}, u ⋖f s → motive s) → motive u)
    (t : FinePathIn tab) : motive t := by
  apply WellFounded.induction flipFineEdge.wellFounded t
  intro u IH
  exact up fun {s} u_s => IH s u_s

/-- Strong induction on fine nodes going from the leaves to the root: the motive may be
assumed at *all* fine descendants. Compare `PathIn.strong_upwards_inductionOn`. -/
theorem FinePathIn.strong_upwards_inductionOn {H X} {tab : Tableau H X}
    {motive : FinePathIn tab → Prop}
    (ups : ∀ {u}, (∀ {s}, Relation.TransGen fineEdge u s → motive s) → motive u)
    (t : FinePathIn tab) : motive t := by
  apply WellFounded.induction (WellFounded.transGen (@flipFineEdge.wellFounded H X tab)) t
  intro u IH
  exact ups fun {s} u_s => IH s (by rw [Relation.TransGen_flip_iff]; exact u_s)

/-- The descent principle for fine nodes: if a property holds at some fine node and, at
every fine node where it holds and which has a child, it also holds at some child, then it
holds at some *childless* fine node.

This is the form in which the well-foundedness is used when following a path downwards in
the fine sense, cf. Lemma 9.7 (d) of the paper. -/
theorem FinePathIn.descent {H X} {tab : Tableau H X} {P : FinePathIn tab → Prop}
    (down : ∀ u, P u → u.children ≠ [] → ∃ g ∈ u.children, P g)
    (t : FinePathIn tab) (ht : P t) :
    ∃ u, P u ∧ u.children = [] := by
  have main : ∀ u : FinePathIn tab, P u → ∃ v, P v ∧ v.children = [] := by
    intro u
    induction u using FinePathIn.edge_upwards_inductionOn with
    | @up u IH =>
      intro hu
      by_cases hc : u.children = []
      · exact ⟨u, hu, hc⟩
      · obtain ⟨g, g_in, hg⟩ := down u hu hc
        exact IH g_in hg
  exact main t ht

/-- The descent principle in the strong form: the property is only required to propagate to
some fine *descendant* (not necessarily a child) as long as the node is not childless. -/
theorem FinePathIn.strong_descent {H X} {tab : Tableau H X} {P : FinePathIn tab → Prop}
    (down : ∀ u, P u → u.children ≠ [] → ∃ g, Relation.TransGen fineEdge u g ∧ P g)
    (t : FinePathIn tab) (ht : P t) :
    ∃ u, P u ∧ u.children = [] := by
  have main : ∀ u : FinePathIn tab, P u → ∃ v, P v ∧ v.children = [] := by
    intro u
    induction u using FinePathIn.strong_upwards_inductionOn with
    | @ups u IH =>
      intro hu
      by_cases hc : u.children = []
      · exact ⟨u, hu, hc⟩
      · obtain ⟨g, hug, hg⟩ := down u hu hc
        exact IH hug hg
  exact main t ht
