import Pdl.Flip
import Pdl.KeepRight
import Pdl.LocalInterpolation

/-! # Defining interpolants (Section 9)

Note that we can skip much of Subsection 8.2 because we worked already with split tableaux anyway.

NOTE: We may need extra work for *uniformity* though.
-/

/-! ## Paths inside a local tableau

The `Tableau` type applies a whole `LocalTableau` in one `loc` step, and thus the `PathIn`
type — and with it the `edge` relation `⋖_` and the clusters defined via `◃` — "jumps over"
the intermediate nodes inside a local tableau. For the quasi-tableau in Definition 9.8 we
need those intermediate nodes, because it is only there that each rule application is
either a left or a right rule.

We therefore first define `LocalPathIn`, the analogue of `PathIn` for local tableaux, in
the same spirit as `LocalTableau.paths` which is used for the completeness proof.
Note that in contrast to `LocalTableau.paths` we here keep the nodes themselves and not
only the sequents labelling them, so that we can still connect them to `PathIn`. -/

/-- A path inside a `LocalTableau`, pointing at an arbitrary node of it — in contrast to
`LocalTableau.paths` which only goes to the end nodes. -/
inductive LocalPathIn : {X : Sequent} → LocalTableau X → Type
  | nil {X} {lt : LocalTableau X} : LocalPathIn lt
  | cons {X} {lra : LocalRuleApp} {X_def : X = lra.X} {next} {Y} (Y_in : Y ∈ lra.C)
      (tail : LocalPathIn (next Y Y_in)) : LocalPathIn (LocalTableau.byLocalRule lra X_def next)

/-- The sequent at the node a local path is pointing at. -/
def LocalPathIn.last {X} {lt : LocalTableau X} : LocalPathIn lt → Sequent
  | .nil => X
  | .cons _ tail => tail.last

/-- The local tableau rooted at the node a local path is pointing at. -/
def LocalPathIn.ltAt {X} {lt : LocalTableau X} : (lp : LocalPathIn lt) → LocalTableau lp.last
  | .nil => lt
  | .cons _ tail => tail.ltAt

/-- Is this the empty local path, i.e. does it point at the root of the local tableau? -/
def LocalPathIn.isNilB {X} {lt : LocalTableau X} : LocalPathIn lt → Bool
  | .nil => true
  | .cons _ _ => false

/-- Is a local rule applied at the root of this local tableau? -/
def LocalTableau.hasRule {X} : LocalTableau X → Prop
  | .byLocalRule .. => True
  | .sim _ => False

instance LocalTableau.instDecidableHasRule {X} (lt : LocalTableau X) : Decidable lt.hasRule := by
  cases lt <;> simp [LocalTableau.hasRule] <;> infer_instance

/-- A local path is *internal* iff a local rule is applied at the node it points at,
i.e. iff that node is not a leaf of the local tableau. -/
def LocalPathIn.isInternal {X} {lt : LocalTableau X} (lp : LocalPathIn lt) : Prop :=
  lp.ltAt.hasRule

instance LocalPathIn.instDecidableIsInternal {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    Decidable lp.isInternal := by
  unfold LocalPathIn.isInternal; infer_instance

/-- If the local path points at a leaf then this gives the end node it reaches. -/
def LocalPathIn.endNodeAt? {X} {lt : LocalTableau X} :
    (lp : LocalPathIn lt) → Option {Y : Sequent // Y ∈ endNodesOf lt}
  | .nil => match lt with
    | .byLocalRule _ _ _ => none
    | .sim _ => some ⟨X, by simp⟩
  | .cons Y_in tail => (tail.endNodeAt?).map
      (fun ⟨Z, hZ⟩ => ⟨Z, by simp only [endNodesOf, List.mem_flatten, List.mem_map,
        List.mem_attach, true_and, Subtype.exists]; exact ⟨_, ⟨_, Y_in, rfl⟩, hZ⟩⟩)

lemma LocalPathIn.isInternal_iff_endNodeAt?_eq_none {X} {lt : LocalTableau X}
    (lp : LocalPathIn lt) : lp.isInternal ↔ lp.endNodeAt? = none := by
  induction lp
  case nil X lt =>
    cases lt <;> simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule,
      LocalPathIn.endNodeAt?]
  case cons IH =>
    simpa [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalPathIn.endNodeAt?] using IH

lemma LocalPathIn.last_of_endNodeAt? {X} {lt : LocalTableau X} (lp : LocalPathIn lt)
    {Yh : {Y : Sequent // Y ∈ endNodesOf lt}} (h : lp.endNodeAt? = some Yh) :
    lp.last = Yh.val := by
  induction lp
  case nil X lt =>
    cases lt
    · simp [LocalPathIn.endNodeAt?] at h
    · simp only [LocalPathIn.endNodeAt?, Option.some.injEq] at h
      subst h
      rfl
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [LocalPathIn.endNodeAt?, Option.map_eq_some_iff] at h
    obtain ⟨Zh, hZ, rfl⟩ := h
    simpa [LocalPathIn.last] using IH hZ

/-- The children of the node a local path points at, inside the same local tableau. -/
def LocalPathIn.children {X} {lt : LocalTableau X} : LocalPathIn lt → List (LocalPathIn lt)
  | .nil => match lt with
    | .byLocalRule _ _ _ => (LocalRuleApp.C _).attach.map (fun ⟨_, Y_in⟩ => .cons Y_in .nil)
    | .sim _ => []
  | .cons Y_in tail => tail.children.map (.cons Y_in)

/-- The sequents labelling the children of the root of a local tableau. -/
def LocalTableau.childLabels {X} : LocalTableau X → List Sequent
  | .byLocalRule lra _ _ => lra.C
  | .sim _ => []

lemma LocalPathIn.map_last_children {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    lp.children.map LocalPathIn.last = lp.ltAt.childLabels := by
  induction lp
  case nil X lt =>
    cases lt
    · simp only [LocalPathIn.children, LocalPathIn.ltAt, LocalTableau.childLabels,
        List.map_attach_eq_pmap, List.map_pmap]
      rw [show (fun (a : Sequent) (h : a ∈ _) => (LocalPathIn.cons h LocalPathIn.nil).last)
            = (fun a (_ : a ∈ _) => a) from rfl]
      simp [List.pmap_eq_map]
    · simp [LocalPathIn.children, LocalPathIn.ltAt, LocalTableau.childLabels]
  case cons X lra X_def next Y Y_in tail IH =>
    simpa [LocalPathIn.children, LocalPathIn.ltAt, LocalPathIn.last, List.map_map,
      Function.comp_def] using IH

/-- The end nodes of the whole local tableau that are below a given local path. -/
def LocalPathIn.endNodesBelow {X} {lt : LocalTableau X} :
    (lp : LocalPathIn lt) → List {Y : Sequent // Y ∈ endNodesOf lt}
  | .nil => (endNodesOf lt).attach
  | .cons Y_in tail => tail.endNodesBelow.map (fun ⟨Z, hZ⟩ => ⟨Z, by
      simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
        Subtype.exists]
      exact ⟨_, ⟨_, Y_in, rfl⟩, hZ⟩⟩)

/-- A leaf of a local tableau is the only end node below itself. -/
lemma LocalPathIn.endNodesBelow_eq_of_endNodeAt? : {X : Sequent} → {lt : LocalTableau X} →
    (lp : LocalPathIn lt) → {Yh : {Y : Sequent // Y ∈ endNodesOf lt}} →
      lp.endNodeAt? = some Yh → ∀ Yh' ∈ lp.endNodesBelow, Yh' = Yh
  | _, .byLocalRule .., .nil, _, h, _, _ => by simp [LocalPathIn.endNodeAt?] at h
  | _, .sim _, .nil, _, h, Yh', _ => by
      simp only [LocalPathIn.endNodeAt?, Option.some.injEq] at h
      subst h
      have := Yh'.2
      simp only [endNodesOf, List.mem_singleton] at this
      exact Subtype.ext this
  | _, .byLocalRule lra X_def next, .cons Y_in tail, _, h, Yh', h' => by
      simp only [LocalPathIn.endNodeAt?, Option.map_eq_some_iff] at h
      obtain ⟨Zh, hZ, rfl⟩ := h
      simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h'
      obtain ⟨W, hW, hW', rfl⟩ := h'
      have := LocalPathIn.endNodesBelow_eq_of_endNodeAt? tail hZ ⟨W, hW⟩ hW'
      simp only [Subtype.mk.injEq]
      exact congrArg Subtype.val this

/-- If an end node is below an internal node of a local tableau, then it is below one of
the children of that node. -/
lemma LocalPathIn.exists_child_endNodesBelow : {X : Sequent} → {lt : LocalTableau X} →
    (lp : LocalPathIn lt) → lp.isInternal → ∀ Yh ∈ lp.endNodesBelow,
      ∃ c ∈ lp.children, Yh ∈ c.endNodesBelow
  | _, .sim _, .nil, h, _, _ => by
      simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule] at h
  | _, .byLocalRule lra X_def next, .nil, _, ⟨Z, hZ⟩, _ => by
      have hZ2 := hZ
      simp only [endNodesOf, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
        Subtype.exists] at hZ2
      obtain ⟨l, ⟨Y, Y_in, rfl⟩, hZ'⟩ := hZ2
      refine ⟨.cons Y_in .nil, ?_, ?_⟩
      · simp only [LocalPathIn.children, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        exact ⟨Y, Y_in, rfl⟩
      · simp only [LocalPathIn.endNodesBelow, List.mem_map, List.mem_attach, true_and,
          Subtype.exists]
        exact ⟨Z, hZ', rfl⟩
  | _, .byLocalRule lra X_def next, .cons Y_in tail, h, Yh, hYh => by
      simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at hYh
      obtain ⟨Z, hZ, hZ', rfl⟩ := hYh
      obtain ⟨c, c_in, hc⟩ := LocalPathIn.exists_child_endNodesBelow tail h ⟨Z, hZ⟩ hZ'
      refine ⟨.cons Y_in c, ?_, ?_⟩
      · simp only [LocalPathIn.children, List.mem_map]
        exact ⟨c, c_in, rfl⟩
      · simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists]
        exact ⟨Z, hZ, hc, rfl⟩

/-- All internal nodes of a local tableau, i.e. those where a local rule is applied.
Compare `allPaths` for `PathIn`. -/
def internalLocalPaths : {X : Sequent} → (lt : LocalTableau X) → List (LocalPathIn lt)
  | _, .sim _ => []
  | _, .byLocalRule lra _ next => .nil ::
      lra.C.attach.flatMap (fun ⟨Y, Y_in⟩ =>
        (internalLocalPaths (next Y Y_in)).map (LocalPathIn.cons Y_in))

lemma internalLocalPaths_isInternal : {X : Sequent} → {lt : LocalTableau X} →
    ∀ lp ∈ internalLocalPaths lt, LocalPathIn.isInternal lp
  | _, .sim _, lp, h => by simp [internalLocalPaths] at h
  | _, .byLocalRule lra X_def next, lp, h => by
      simp only [internalLocalPaths, List.mem_cons, List.mem_flatMap, List.mem_attach, true_and,
        Subtype.exists, List.mem_map] at h
      rcases h with rfl | ⟨Y, Y_in, lp', lp'_in, rfl⟩
      · simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule]
      · have := internalLocalPaths_isInternal lp' lp'_in
        simpa [LocalPathIn.isInternal, LocalPathIn.ltAt] using this

lemma LocalPathIn.mem_internalLocalPaths {X} {lt : LocalTableau X} (lp : LocalPathIn lt)
    (h : lp.isInternal) : lp ∈ internalLocalPaths lt := by
  induction lp
  case nil X lt =>
    cases lt
    · simp [internalLocalPaths]
    · simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule] at h
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [internalLocalPaths, List.mem_cons, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists, List.mem_map]
    exact Or.inr ⟨Y, Y_in, tail, IH (by simpa [LocalPathIn.isInternal, LocalPathIn.ltAt] using h),
      rfl⟩

/-! ## Fine paths: all nodes of a tableau

A `FinePathIn` points at a node of the tableau in the *fine* sense: it may also point at
an intermediate node inside a local tableau. Note that the end nodes of a local tableau
are *not* fine nodes of their own: in the `Tableau` type they are the roots of the tableaux
given by `next`, and that is where they show up here.

Hence a fine node is either
- an internal node of the local tableau applied at a `Tableau.loc` node (`inLoc`),
- a `Tableau.pdl` node (`pdlHere`), or
- a `Tableau.lrep` node, i.e. a loaded-path repeat leaf (`lrepHere`),
possibly below some `loc` and `pdl` steps.
Every node has exactly one representation as a `FinePathIn`. -/

/-- A path in a tableau that may also stop at an intermediate node inside a `LocalTableau`. -/
inductive FinePathIn : ∀ {Hist X}, Tableau Hist X → Type
  | inLoc {Hist X nrep nbas} {lt : LocalTableau X} {next} (lp : LocalPathIn lt)
      (lp_int : lp.isInternal) :
      FinePathIn (@Tableau.loc Hist X nrep nbas lt next)
  | pdlHere {Hist X Y nrep bas} {r : PdlRule X Y} {next} :
      FinePathIn (@Tableau.pdl Hist X Y nrep bas r next)
  | lrepHere {Hist X} {lpr : LoadedPathRepeat Hist X} : FinePathIn (Tableau.lrep lpr)
  | loc {Hist X nrep nbas} {lt : LocalTableau X} {next} {Y} (Y_in : Y ∈ endNodesOf lt)
      (tail : FinePathIn (next Y Y_in)) : FinePathIn (@Tableau.loc Hist X nrep nbas lt next)
  | pdl {Hist X Y nrep bas} {r : PdlRule X Y} {next} (tail : FinePathIn next) :
      FinePathIn (@Tableau.pdl Hist X Y nrep bas r next)

/-- The fine path pointing at the root of a tableau. -/
def rootFine : {H : History} → {X : Sequent} → (tab : Tableau H X) → FinePathIn tab
  | _, _, .loc _ nbas lt _ => match lt, nbas with
      | .byLocalRule .., _ => .inLoc .nil (by
          simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule])
      | .sim bas, nbas => absurd bas nbas
  | _, _, .pdl .. => .pdlHere
  | _, _, .lrep _ => .lrepHere

/-- The sequent at the node a fine path points at, i.e. `Λ(t)` for fine nodes `t`. -/
def FinePathIn.label : ∀ {Hist X} {tab : Tableau Hist X}, FinePathIn tab → Sequent
  | _, _, _, .inLoc lp _ => lp.last
  | _, X, _, .pdlHere => X
  | _, X, _, .lrepHere => X
  | _, _, _, .loc _ tail => tail.label
  | _, _, _, .pdl tail => tail.label

/-- The `PathIn` node in whose local tableau the given fine node lies. -/
def FinePathIn.base : ∀ {Hist X} {tab : Tableau Hist X}, FinePathIn tab → PathIn tab
  | _, _, _, .inLoc _ _ => .nil
  | _, _, _, .pdlHere => .nil
  | _, _, _, .lrepHere => .nil
  | _, _, _, .loc Y_in tail => .loc Y_in tail.base
  | _, _, _, .pdl tail => .pdl tail.base

/-- The children of a fine node. Note that a child of an internal node of a local tableau
may be a node of the tableau in the coarse `PathIn` sense, namely when it is an end node
of that local tableau. -/
def FinePathIn.children : ∀ {Hist X} {tab : Tableau Hist X},
    FinePathIn tab → List (FinePathIn tab)
  | _, _, _, .inLoc lp _ => lp.children.map (fun lp' =>
      match h : lp'.endNodeAt? with
      | some ⟨_, Y_in⟩ => .loc Y_in (rootFine _)
      | none => .inLoc lp' ((LocalPathIn.isInternal_iff_endNodeAt?_eq_none lp').mpr h))
  | _, _, _, .pdlHere => [ .pdl (rootFine _) ]
  | _, _, _, .lrepHere => []
  | _, _, _, .loc Y_in tail => tail.children.map (.loc Y_in)
  | _, _, _, .pdl tail => tail.children.map (.pdl)

/-- Any node in the coarse sense is also a node in the fine sense. -/
def PathIn.toFine : ∀ {Hist X} {tab : Tableau Hist X}, PathIn tab → FinePathIn tab
  | _, _, _, .nil => rootFine _
  | _, _, _, .loc Y_in tail => .loc Y_in tail.toFine
  | _, _, _, .pdl tail => .pdl tail.toFine

/-- All fine nodes of a tableau. Compare `allPaths`. -/
def allFinePaths : {H : History} → {X : Sequent} → (tab : Tableau H X) → List (FinePathIn tab)
  | _, _, .loc _ _ lt next =>
      (internalLocalPaths lt).attach.map
          (fun ⟨lp, lp_in⟩ => .inLoc lp (internalLocalPaths_isInternal lp lp_in))
      ++ (endNodesOf lt).attach.flatMap
          (fun ⟨Y, Y_in⟩ => (allFinePaths (next Y Y_in)).map (.loc Y_in))
  | _, _, .pdl _ _ _ next => .pdlHere :: (allFinePaths next).map (.pdl)
  | _, _, .lrep _ => [ .lrepHere ]

@[simp]
lemma label_rootFine {H X} (tab : Tableau H X) : (rootFine tab).label = X := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.label, LocalPathIn.last]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.label]
  · simp [rootFine, FinePathIn.label]

@[simp]
lemma base_rootFine {H X} (tab : Tableau H X) : (rootFine tab).base = .nil := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.base]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.base]
  · simp [rootFine, FinePathIn.base]

@[simp]
lemma PathIn.base_toFine {H X} {tab : Tableau H X} (p : PathIn tab) : p.toFine.base = p := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.base]

@[simp]
lemma PathIn.label_toFine {H X} {tab : Tableau H X} (p : PathIn tab) :
    p.toFine.label = nodeAt p := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.label]

theorem FinePathIn.mem_allFinePaths {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    f ∈ allFinePaths tab := by
  induction f
  case inLoc lp lp_int =>
    simp only [allFinePaths, List.mem_append, List.mem_map, List.mem_attach, true_and,
      Subtype.exists]
    exact Or.inl ⟨lp, lp.mem_internalLocalPaths lp_int, rfl⟩
  case pdlHere => simp [allFinePaths]
  case lrepHere => simp [allFinePaths]
  case loc Y_in tail IH =>
    simp only [allFinePaths, List.mem_append, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists, List.mem_map]
    exact Or.inr ⟨_, Y_in, tail, IH, rfl⟩
  case pdl tail IH =>
    simp only [allFinePaths, List.mem_cons, List.mem_map]
    exact Or.inr ⟨tail, IH, rfl⟩

/-- Fine children either stay at the same node in the coarse sense, or they are a child
of it. This connects the fine children with the `edge` relation `⋖_`. -/
theorem FinePathIn.base_of_mem_children {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    ∀ g ∈ f.children, g.base = f.base ∨ f.base ⋖_ g.base := by
  induction f
  case inLoc lp lp_int =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨lp', _, rfl⟩ := g_in
    split
    · right; simp [FinePathIn.base]
    · left; rfl
  case pdlHere =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_singleton] at g_in
    subst g_in
    right
    simp [FinePathIn.base]
  case lrepHere => simp [FinePathIn.children]
  case loc Y_in tail IH =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    rcases IH g' g'_in with h | h
    · left; simp [FinePathIn.base, h]
    · right; simpa [FinePathIn.base] using h
  case pdl tail IH =>
    intro g g_in
    simp only [FinePathIn.children, List.mem_map] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    rcases IH g' g'_in with h | h
    · left; simp [FinePathIn.base, h]
    · right; simpa [FinePathIn.base] using h

lemma FinePathIn.map_label_children_inLoc {Hist X nrep nbas} {lt : LocalTableau X} {next}
    (lp : LocalPathIn lt) (h : lp.isInternal) :
    ((@FinePathIn.inLoc Hist X nrep nbas lt next lp h).children).map FinePathIn.label
      = lp.children.map LocalPathIn.last := by
  simp only [FinePathIn.children, List.map_map]
  apply List.map_inj_left.mpr
  intro lp' _
  simp only [Function.comp_apply]
  split
  · rename_i Y Y_in heq
    simp only [FinePathIn.label, label_rootFine]
    exact (lp'.last_of_endNodeAt? heq).symm ▸ rfl
  · simp [FinePathIn.label]

/-- The local rule applied at a fine node, if any. -/
def FinePathIn.lra? : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Option LocalRuleApp
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => some lra
      | .sim _ => none
  | _, _, _, .pdlHere => none
  | _, _, _, .lrepHere => none
  | _, _, _, .loc _ tail => tail.lra?
  | _, _, _, .pdl tail => tail.lra?

/-- If a local rule is applied at a fine node then that node is labelled with the premise
and its children are labelled with the conclusions of that rule. -/
lemma FinePathIn.lra?_spec {H X} {tab : Tableau H X} (f : FinePathIn tab) {lra : LocalRuleApp}
    (h : f.lra? = some lra) : f.label = lra.X ∧ f.children.map FinePathIn.label = lra.C := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lra?] at h
    rcases hlt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨X_def, ?_⟩
      rw [FinePathIn.map_label_children_inLoc, LocalPathIn.map_last_children, hlt]
      rfl
    · rw [hlt] at h
      simp at h
  case pdlHere => simp [FinePathIn.lra?] at h
  case lrepHere => simp [FinePathIn.lra?] at h
  case loc IH =>
    simp only [FinePathIn.lra?] at h
    obtain ⟨h1, h2⟩ := IH h
    refine ⟨h1, ?_⟩
    simpa [FinePathIn.children, FinePathIn.label, List.map_map, Function.comp_def] using h2
  case pdl IH =>
    simp only [FinePathIn.lra?] at h
    obtain ⟨h1, h2⟩ := IH h
    refine ⟨h1, ?_⟩
    simpa [FinePathIn.children, FinePathIn.label, List.map_map, Function.comp_def] using h2

open HasSat in
/-- Local soundness and invertibility at the fine level: whenever a local rule is applied
at a fine node, its label is satisfied exactly if the label of one of its children is.
This is the property of the fine tableau that makes the quasi-tableau work. -/
theorem FinePathIn.locally_sound {H X} {tab : Tableau H X} (f : FinePathIn tab)
    {lra : LocalRuleApp} (h : f.lra? = some lra) {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ f.label ↔ ∃ g ∈ f.children, (M, w) ⊨ g.label := by
  obtain ⟨h1, h2⟩ := f.lra?_spec h
  rw [h1, localRuleTruth lra M w, ← h2]
  simp

/-! ## Left and right rules

At the fine level each rule application is a left rule or a right rule or neither
(the latter for closing rules and loaded-path repeats), but never both.
This is what Lemma 9.7 (a) is about, and it is the reason why we needed the fine nodes:
on the `Tableau` level a `loc` step is in general a mix of left and right rules. -/

/-- Is this a local rule applied to the right component? -/
def LocalRule.isRightRule {X YS} : LocalRule X YS → Bool
  | .oneSidedR _ _ => true
  | .loadedR _ _ _ => true
  | _ => false

/-- Is this a local rule applied to the left component? -/
def LocalRule.isLeftRule {X YS} : LocalRule X YS → Bool
  | .oneSidedL _ _ => true
  | .loadedL _ _ _ => true
  | _ => false

def LocalRuleApp.isRightRule (lra : LocalRuleApp) : Bool := lra.lr.isRightRule

def LocalRuleApp.isLeftRule (lra : LocalRuleApp) : Bool := lra.lr.isLeftRule

lemma LocalRuleApp.not_left_and_right (lra : LocalRuleApp) :
    ¬ (lra.isLeftRule ∧ lra.isRightRule) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp [LocalRuleApp.isLeftRule, LocalRuleApp.isRightRule, LocalRule.isLeftRule,
      LocalRule.isRightRule]

/-- The `(M)`, `(L+)` and `(L-)` rules acting on the right component. -/
def PdlRule.isRightRule {X Y} : PdlRule X Y → Bool
  | .loadR _ _ _ => true
  | .freeR _ _ => true
  | .modR _ _ => true
  | _ => false

/-- The `(M)`, `(L+)` and `(L-)` rules acting on the left component. -/
def PdlRule.isLeftRule {X Y} : PdlRule X Y → Bool
  | .loadL _ _ _ => true
  | .freeL _ _ => true
  | .modL _ _ => true
  | _ => false

/-- Is a right rule applied at this fine node? -/
def FinePathIn.usesRightRule : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => lra.isRightRule
      | .sim _ => false
  | _, _, _, @FinePathIn.pdlHere _ _ _ _ _ r _ => r.isRightRule
  | _, _, _, .lrepHere => false
  | _, _, _, .loc _ tail => tail.usesRightRule
  | _, _, _, .pdl tail => tail.usesRightRule

/-- Is a left rule applied at this fine node? -/
def FinePathIn.usesLeftRule : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => lra.isLeftRule
      | .sim _ => false
  | _, _, _, @FinePathIn.pdlHere _ _ _ _ _ r _ => r.isLeftRule
  | _, _, _, .lrepHere => false
  | _, _, _, .loc _ tail => tail.usesLeftRule
  | _, _, _, .pdl tail => tail.usesLeftRule

/-- No node uses a left and a right rule at the same time. -/
lemma FinePathIn.not_left_and_right {H Y} {tab : Tableau H Y} (f : FinePathIn tab) :
    ¬ (f.usesLeftRule ∧ f.usesRightRule) := by
  induction f
  case inLoc lp lp_int =>
    rintro ⟨hl, hr⟩
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] at hl hr
    rcases h : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [h] at hl hr
      simp only at hl hr
      exact lra.not_left_and_right ⟨hl, hr⟩
    · rw [h] at hl
      simp at hl
  case pdlHere _ _ _ _ _ r _ =>
    rintro ⟨hl, hr⟩
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] at hl hr
    cases r <;> simp_all [PdlRule.isLeftRule, PdlRule.isRightRule]
  case lrepHere => simp [FinePathIn.usesLeftRule]
  case loc IH => simpa [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] using IH
  case pdl IH => simpa [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] using IH

/-- A node where a right rule is applied is not a loaded-path repeat, and neither is the
coarse node it belongs to. -/
lemma FinePathIn.not_isLrep_base_of_usesRightRule {H X} {tab : Tableau H X} (f : FinePathIn tab)
    (h : f.usesRightRule) : ¬ f.base.isLrep := by
  induction f with
  | inLoc lp lp_int => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep]
  | pdlHere => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep]
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simpa [FinePathIn.base, PathIn.isLrep, tabAt] using IH h
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simpa [FinePathIn.base, PathIn.isLrep, tabAt] using IH h

/-- Is this fine node also a node in the coarse sense, i.e. the root of the local tableau
at its base? -/
def FinePathIn.atBigRoot : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => lp.isNilB
  | _, _, _, .pdlHere => true
  | _, _, _, .lrepHere => true
  | _, _, _, .loc _ tail => tail.atBigRoot
  | _, _, _, .pdl tail => tail.atBigRoot

@[simp]
lemma atBigRoot_rootFine {H X} (tab : Tableau H X) : (rootFine tab).atBigRoot = true := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.atBigRoot, LocalPathIn.isNilB]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.atBigRoot]
  · simp [rootFine, FinePathIn.atBigRoot]

@[simp]
lemma PathIn.atBigRoot_toFine {H X} {tab : Tableau H X} (p : PathIn tab) :
    p.toFine.atBigRoot = true := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.atBigRoot]

/-- The labels of those end nodes of the local tableau at `f.base` that are below `f`.
These are the labels of the children of `f.base` that can be reached from `f`. -/
def FinePathIn.endLabelsBelow : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → List Sequent
  | _, _, _, .inLoc lp _ => endNodesOf lp.ltAt
  | _, _, _, .pdlHere => []
  | _, _, _, .lrepHere => []
  | _, _, _, .loc _ tail => tail.endLabelsBelow
  | _, _, _, .pdl tail => tail.endLabelsBelow

/-- The children of `f.base` in the coarse sense that are below the fine node `f`.
Note that when `f` is a coarse node itself, i.e. `f.atBigRoot`, then these are *all*
children of `f.base`, and that they get further restricted the deeper `f` sits inside the
local tableau at `f.base`. -/
def FinePathIn.coarseChildrenBelow : ∀ {H X} {tab : Tableau H X},
    FinePathIn tab → List (PathIn tab)
  | _, _, _, .inLoc lp _ => lp.endNodesBelow.map (fun ⟨_, Y_in⟩ => PathIn.loc Y_in .nil)
  | _, _, _, .pdlHere => [PathIn.pdl .nil]
  | _, _, _, .lrepHere => []
  | _, _, _, .loc Y_in tail => tail.coarseChildrenBelow.map (PathIn.loc Y_in)
  | _, _, _, .pdl tail => tail.coarseChildrenBelow.map (PathIn.pdl)

/-- If a coarse child `q` is below the fine node `f`, then `f` has a fine child `g` that
is either still at the same coarse node and has `q` below it, or `g` *is* `q`. -/
lemma FinePathIn.exists_child_coarseChildrenBelow {H X} {tab : Tableau H X}
    (f : FinePathIn tab) (q : PathIn tab) (hq : q ∈ f.coarseChildrenBelow) :
    ∃ g ∈ f.children,
      (g.base = f.base ∧ q ∈ g.coarseChildrenBelow) ∨ (g.base = q ∧ g.atBigRoot) := by
  induction f with
  | inLoc lp lp_int =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
    obtain ⟨Y, Y_in, hYin, rfl⟩ := hq
    obtain ⟨c, c_in, hc⟩ := LocalPathIn.exists_child_endNodesBelow lp lp_int ⟨Y, Y_in⟩ hYin
    refine ⟨_, List.mem_map_of_mem c_in, ?_⟩
    split
    case _ W W_in h =>
      refine Or.inr ⟨?_, by simp [FinePathIn.atBigRoot]⟩
      have := LocalPathIn.endNodesBelow_eq_of_endNodeAt? c h ⟨Y, Y_in⟩ hc
      simp only [Subtype.mk.injEq] at this
      simp only [FinePathIn.base, base_rootFine]
      subst this
      rfl
    case _ h =>
      refine Or.inl ⟨rfl, ?_⟩
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists]
      exact ⟨Y, Y_in, hc, rfl⟩
  | @pdlHere _ _ _ _ _ _ next =>
    refine ⟨.pdl (rootFine next), by simp [FinePathIn.children], Or.inr ⟨?_, ?_⟩⟩
    · simp only [FinePathIn.coarseChildrenBelow, List.mem_singleton] at hq
      subst hq
      simp [FinePathIn.base]
    · simp [FinePathIn.atBigRoot]
  | lrepHere => simp [FinePathIn.coarseChildrenBelow] at hq
  | loc Y_in tail IH =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨g, g_in, hg⟩ := IH q' hq'
    refine ⟨.loc Y_in g, by simp only [FinePathIn.children, List.mem_map]; exact ⟨g, g_in, rfl⟩, ?_⟩
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [FinePathIn.base, h1], by
        simp only [FinePathIn.coarseChildrenBelow, List.mem_map]; exact ⟨q', h2, rfl⟩⟩
    · exact Or.inr ⟨by simp [FinePathIn.base, h1], by simpa [FinePathIn.atBigRoot] using h2⟩
  | pdl tail IH =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨g, g_in, hg⟩ := IH q' hq'
    refine ⟨.pdl g, by simp only [FinePathIn.children, List.mem_map]; exact ⟨g, g_in, rfl⟩, ?_⟩
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [FinePathIn.base, h1], by
        simp only [FinePathIn.coarseChildrenBelow, List.mem_map]; exact ⟨q', h2, rfl⟩⟩
    · exact Or.inr ⟨by simp [FinePathIn.base, h1], by simpa [FinePathIn.atBigRoot] using h2⟩

/-- A fine node that is a coarse node is the image of that coarse node under `toFine`. -/
lemma FinePathIn.eq_toFine_base_of_atBigRoot {H X} {tab : Tableau H X} (f : FinePathIn tab)
    (h : f.atBigRoot) : f = f.base.toFine := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp lp_int =>
    cases lp with
    | nil =>
      rcases lt with ⟨lra, X_def, lnext⟩ | bas
      · rfl
      · exact absurd bas nbas
    | cons => simp [FinePathIn.atBigRoot, LocalPathIn.isNilB] at h
  | pdlHere => rfl
  | lrepHere => rfl
  | loc Y_in tail IH =>
    simp only [FinePathIn.atBigRoot] at h
    simp only [FinePathIn.base, PathIn.toFine]
    exact congrArg _ (IH h)
  | pdl tail IH =>
    simp only [FinePathIn.atBigRoot] at h
    simp only [FinePathIn.base, PathIn.toFine]
    exact congrArg _ (IH h)

/-- All children of a coarse node are below it in the fine sense. This is the converse of
`FinePathIn.base_of_mem_children` for coarse nodes. -/
lemma PathIn.mem_coarseChildrenBelow_toFine {H X} {tab : Tableau H X} :
    ∀ (p q : PathIn tab), p ⋖_ q → q ∈ p.toFine.coarseChildrenBelow := by
  intro p
  induction p with
  | nil =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · simp only [tabAt] at hh
      obtain ⟨rfl, hh2⟩ := Sigma.mk.injEq .. ▸ hh
      obtain ⟨rfl, -⟩ := hh2
      change PathIn.loc Y_in PathIn.nil ∈ _
      rcases lt with ⟨lra, X_def, lnext⟩ | bas
      · simp only [PathIn.toFine, rootFine, FinePathIn.coarseChildrenBelow,
          LocalPathIn.endNodesBelow, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        exact ⟨Y, Y_in, rfl⟩
      · exact absurd bas nbas
    · simp only [tabAt] at hh
      obtain ⟨rfl, hh2⟩ := Sigma.mk.injEq .. ▸ hh
      obtain ⟨rfl, -⟩ := hh2
      change PathIn.pdl PathIn.nil ∈ _
      simp [PathIn.toFine, rootFine, FinePathIn.coarseChildrenBelow]
  | loc Y_in tail IH =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.loc Y'_in .nil)) :=
        Or.inl ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
      change PathIn.loc Y_in (tail.append (hh ▸ PathIn.loc Y'_in .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.pdl .nil)) :=
        Or.inr ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
      change PathIn.loc Y_in (tail.append (hh ▸ PathIn.pdl .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
  | pdl tail IH =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.loc Y'_in .nil)) :=
        Or.inl ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
      change PathIn.pdl (tail.append (hh ▸ PathIn.loc Y'_in .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.pdl .nil)) :=
        Or.inr ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
      change PathIn.pdl (tail.append (hh ▸ PathIn.pdl .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)

/-- The right component of a sequent, again as a sequent but with empty left component.
This is `Λ₂` from the paper; we use it to label the nodes of the quasi-tableau. -/
def Sequent.rightOnly (X : Sequent) : Sequent := ⟨[], X.2.1, X.2.2⟩


variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Collecting Cluster Nodes in a List

We define the lists `loadedBelow` and `loadedAbove` of nodes that are reachable from / can reach
a given node via `◃` *by filtering `allPaths`*: a tableau has only finitely many nodes and
`PathIn.elem_allPaths` says that `allPaths tab` contains all of them, so we can simply keep
those nodes that are `◃`-related to `p` in the desired direction.
Then `clusterListOf_spec` is immediate. -/

/-- Loaded nodes "below" the given one, also allowing ♥ steps. Includes the node itself. -/
def loadedBelow (p : PathIn tab) : List (PathIn tab) :=
  p :: (allPaths tab).filter (fun q => ((p ◃⁺ q) ∧ (nodeAt q).isLoaded))

/-- Loaded nodes "above" the given one, also allowing *backwards* ♥ steps.
Includes the node itself. -/
def loadedAbove (p : PathIn tab) : List (PathIn tab) :=
  p :: (allPaths tab).filter (fun q => decide ((q ◃⁺ p) ∧ (nodeAt q).isLoaded))

@[simp]
lemma mem_loadedBelow {p q : PathIn tab} :
    q ∈ loadedBelow p  ↔  q = p ∨ ((p ◃⁺ q) ∧ (nodeAt q).isLoaded) := by
  simp [loadedBelow, PathIn.elem_allPaths]

@[simp]
lemma mem_loadedAbove {p q : PathIn tab} :
    q ∈ loadedAbove p  ↔  q = p ∨ ((q ◃⁺ p) ∧ (nodeAt q).isLoaded) := by
  simp [loadedAbove, PathIn.elem_allPaths]

/-- A free node is alone in its cluster (cf. Remark 4.18 in the paper). -/
lemma eq_of_cEquiv_of_isFree {p q : PathIn tab}
    (p_free : (nodeAt p).isFree) (p_q : p ≡ᶜ q) : q = p := by
  rcases p_q with ⟨p_to_q, q_to_p⟩
  rcases Relation.ReflTransGen.cases_head p_to_q with p_eq_q | ⟨l, p_l, l_to_q⟩
  · exact p_eq_q.symm
  · exfalso
    have l_to_p : l ◃* p := Relation.ReflTransGen.trans l_to_q q_to_p
    cases p_l
    case inl p_edge_l =>
      have p_lt_l := ePropB.c_single p l p_free p_edge_l
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp l_to_p with l_eq_p | l_c_p
      · subst l_eq_p
        exact path_is_irreflexive (Relation.TransGen.single p_edge_l)
      · exact p_lt_l.2 l_c_p
    case inr p_heart_l =>
      have := (companion_loaded p_heart_l).1
      simp only [Sequent.isFree, this] at p_free
      simp at p_free

/-- List of all other nodes in the same cluster, essentially a constructive version of `clusterOf`.
Computed as the intersection of `loadedAbove` and `loadedBelow`. -/
def clusterListOf (p : PathIn tab) : List (PathIn tab) :=
  loadedBelow p  ∩  loadedAbove p

lemma clusterListOf_spec {q : PathIn tab} (p : PathIn tab) :
    q ∈ clusterListOf p  ↔  p ≡ᶜ q := by
  rw [clusterListOf, List.mem_inter_iff, mem_loadedBelow, mem_loadedAbove]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | ⟨p_q, -⟩
    · exact (eProp tab).1.refl _
    · rcases h2 with rfl | ⟨q_p, -⟩
      · exact (eProp tab).1.refl _
      · exact ⟨p_q.to_reflTransGen, q_p.to_reflTransGen⟩
  · intro p_c_q
    rcases eq_or_ne q p with rfl | q_ne_p
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have q_loaded : (nodeAt q).isLoaded := by
        by_contra q_not_loaded
        exact q_ne_p (eq_of_cEquiv_of_isFree
          (by simp_all [Sequent.isFree]) ((cEquiv.symm p q).mp p_c_q)).symm
      exact ⟨ Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.1 (Ne.symm q_ne_p), q_loaded⟩
            , Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.2 q_ne_p, q_loaded⟩ ⟩

/-! ## Cluster roots -/

/-- Being a *cluster root*: there is no `◃` path from `s` back to a parent of `s`.
As a parent `p` of `s` always has a `◃` path to `s`, this says that no parent of `s` is
`≡ᶜ` to `s` (see `PathIn.isClusterRoot_iff`), i.e. that `s` is the first node of its own
cluster along the branch leading to `s`.

Note that this is *vacuously true* for `.nil`, the root of the whole tableau, which has no
parent at all. This is why we quantify over all parents instead of demanding that a parent
exists: the root of a tableau may already be loaded. -/
def PathIn.isClusterRoot (s : PathIn tab) : Prop :=
  ∀ p : PathIn tab, p ⋖_ s → ¬ s ◃* p

lemma PathIn.isClusterRoot_flip {p : PathIn tab}
    (h : p.isClusterRoot) : (p.flip).isClusterRoot := by
  intro q q_edge
  rw [← PathIn.flip_unflip q] at q_edge ⊢
  rw [edge_flip] at q_edge
  rw [cReach_flip]
  exact h _ q_edge

/-- The root of the whole tableau is a cluster root, because it has no parent. -/
lemma PathIn.isClusterRoot_nil :
    (PathIn.nil : PathIn tab).isClusterRoot := by
  intro p p_nil
  exfalso
  have := edge_then_length_lt p_nil
  simp at this

/-- Equivalent formulation of `PathIn.isClusterRoot` using `≡ᶜ`. -/
lemma PathIn.isClusterRoot_iff {s : PathIn tab} :
    s.isClusterRoot ↔ ∀ p : PathIn tab, p ⋖_ s → ¬ p ≡ᶜ s := by
  unfold PathIn.isClusterRoot cEquiv
  constructor
  · rintro h p p_s ⟨-, s_p⟩
    exact h p p_s s_p
  · intro h p p_s s_p
    exact h p p_s ⟨Relation.ReflTransGen.single (Or.inl p_s), s_p⟩

/-- If the parent of `t` is free, then `t` is a cluster root.
This is the case for all children of free nodes in the recursion of `tabToIntAt`. -/
lemma PathIn.isClusterRoot_of_edge_from_free {s t : PathIn tab}
    (s_free : (nodeAt s).isFree) (s_t : s ⋖_ t) : t.isClusterRoot := by
  rw [PathIn.isClusterRoot_iff]
  intro p p_t
  have p_eq_s : p = s := edge_leftInjective _ _ _ p_t s_t
  subst p_eq_s
  exact ePropB.h _ _ (ePropB.c_single _ _ s_free s_t)

/-- If all parents of `s` are free — which for a loaded `s` says exactly that `s` is the
first loaded node along the branch leading to it — then `s` is a cluster root. -/
lemma PathIn.isClusterRoot_of_parents_free {s : PathIn tab}
    (h : ∀ p : PathIn tab, p ⋖_ s → (nodeAt p).isFree) : s.isClusterRoot := by
  intro p p_s
  exact PathIn.isClusterRoot_of_edge_from_free (h p p_s) p_s p p_s

/-- Def 8.14: `e` is an *exit* of the cluster of `s`, i.e. `e ∈ C⁺ \ C` where `C` is the
cluster of `s`: it is not in the cluster of `s`, but it is a child of a node in it. -/
def isExitOf (s e : PathIn tab) : Prop :=
  ¬ (e ≡ᶜ s)  ∧  ∃ t : PathIn tab, (t ≡ᶜ s) ∧ t ⋖_ e

lemma isExitOf_flip {s e : PathIn tab} :
    isExitOf s.flip e.flip ↔ isExitOf s e := by
  unfold isExitOf
  rw [cEquiv_flip]
  constructor
  · rintro ⟨no, t, t_s, t_e⟩
    refine ⟨no, t.unflip, ?_, ?_⟩
    · rw [← cEquiv_flip, PathIn.flip_unflip]
      exact t_s
    · rw [← edge_flip, PathIn.flip_unflip]
      exact t_e
  · rintro ⟨no, t, t_s, t_e⟩
    exact ⟨no, t.flip, cEquiv_flip.mpr t_s, edge_flip.mpr t_e⟩

/-- Exits of a cluster are cluster roots.
This is one of the two things needed to keep the `tabToIntAt` recursion going. -/
lemma isClusterRoot_of_isExitOf {s e : PathIn tab}
    (h : isExitOf s e) : e.isClusterRoot := by
  rcases h with ⟨e_not_s, t, t_s, t_e⟩
  rw [PathIn.isClusterRoot_iff]
  intro p p_e p_e_equiv
  absurd e_not_s
  have p_eq_t : p = t := edge_leftInjective _ _ _ p_e t_e
  subst p_eq_t
  exact ⟨p_e_equiv.2.trans t_s.1, t_s.2.trans p_e_equiv.1⟩

-- FIXME move / already exists with other name?
/-- Any `⋖_` path is also a `◃` path. -/
lemma cReach_of_le {s t : PathIn tab} (h : s ≤ t) : s ◃* t :=
  h.mono (fun _ _ h => Or.inl h)

/-- If `u < s` then some parent of `s` is reachable from `u` (possibly `u` itself). -/
lemma exists_parent_of_lt {u s : PathIn tab} (h : u < s) :
    ∃ p : PathIn tab, u ≤ p ∧ p ⋖_ s := by
  cases h with
  | single u_s => exact ⟨u, Relation.ReflTransGen.refl, u_s⟩
  | tail u_d d_s => exact ⟨_, u_d.to_reflTransGen, d_s⟩

/-- Lemma 8.15 (a): clusters are subtrees. Here in the form we need it: the root of a
cluster is `≤` all nodes of its cluster. -/
lemma PathIn.le_of_cEquiv_of_isClusterRoot {s t : PathIn tab}
    (s_cr : s.isClusterRoot) (h : s ≡ᶜ t) : s ≤ t := by
  -- No node of the cluster of `s` is a proper ancestor of `s`:
  have not_lt : ∀ u : PathIn tab, u < s → s ◃* u → False := by
    intro u u_lt_s s_to_u
    obtain ⟨p, u_le_p, p_s⟩ := exists_parent_of_lt u_lt_s
    exact s_cr p p_s (s_to_u.trans (cReach_of_le u_le_p))
  -- Now walk along the `◃` path from `s`, staying inside the cluster.
  have key : ∀ u : PathIn tab, s ◃* u → u ◃* s → s ≤ u := by
    intro u s_to_u
    induction s_to_u with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail v u s_v v_u ih =>
      intro u_to_s
      have s_to_u : s ◃* u := s_v.tail v_u
      have s_le_v : s ≤ v := ih (Relation.ReflTransGen.head v_u u_to_s)
      rcases v_u with v_e_u | v_h_u
      · -- A child step goes down, so we can just extend the path.
        exact s_le_v.tail v_e_u
      · -- A companion step goes up, so we must use that `s` is a cluster root.
        have u_lt_v : u < v := companion_lt v_h_u
        rcases eq_or_ne s v with s_eq_v | s_ne_v
        · exact absurd (s_eq_v ▸ u_lt_v) (fun h => (not_lt u h s_to_u).elim)
        · have s_lt_v : s < v := Relation.TransGen_of_ReflTransGen s_le_v s_ne_v
          rcases path_revEuclidean' s u v s_lt_v u_lt_v with s_le_u | u_le_s
          · exact s_le_u
          · rcases eq_or_ne u s with u_eq_s | u_ne_s
            · exact u_eq_s ▸ Relation.ReflTransGen.refl
            · exact absurd (Relation.TransGen_of_ReflTransGen u_le_s u_ne_s)
                (fun h => (not_lt u h s_to_u).elim)
  exact key t h.1 h.2

/-- Exits of the cluster of a cluster root `s` are proper descendants of `s`.
This is the second thing needed to keep the `tabToIntAt` recursion going, and it needs
that clusters are subtrees, i.e. Lemma 8.15 (a). -/
lemma lt_of_isExitOf {s e : PathIn tab}
    (s_cr : s.isClusterRoot) (h : isExitOf s e) : s < e := by
  obtain ⟨-, t, t_s, t_e⟩ := h
  have s_le_t : s ≤ t := PathIn.le_of_cEquiv_of_isClusterRoot s_cr ((cEquiv.symm t s).mp t_s)
  exact Relation.TransGen.tail' s_le_t t_e

/-! ## Loaded Clusters -/

/-- A cluster, starting at a right-loaded `root` which is not ≡ᶜ to any parent of it.

Note that there is no explicit `parent` field: the root of the whole tableau may itself be
loaded and then has no parent. Instead, `root_not_to_parent` quantifies over all parents of
the root — which is exactly the property `PathIn.isClusterRoot` that `tabToIntAt` maintains
as an invariant. -/
structure LoadedCluster {X} (tab : Tableau .nil X) where
  /-- The root of the cluster. -/
  root : PathIn tab
  /-- There is no ◃ path from the root to any parent of it. -/
  root_not_to_parent : root.isClusterRoot
  /-- The root is loaded on the right. -/
  root_loaded_right : (nodeAt root).2.2.isRight
  /-- List of all paths in the cluster. -/
  CL : List (PathIn tab)
  /-- The root is in the cluster. -/
  root_mem_CL : root ∈ CL
  /-- All elements of `CL` are ≡ᶜ and thus can reach each other. -/
  CL_equiv : ∀ s ∈ CL, ∀ t ∈ CL, s ≡ᶜ t
  /-- All paths that are ≡ᶜ to something in `CL` are also in `CL`. -/
  CL_complete : ∀ s ∈ CL, ∀ t, (s ≡ᶜ t) → t ∈ CL
  /-- The root can reach all nodes of the cluster. -/
  root_reaches_all : ∀ s ∈ CL, root ◃* s

namespace LoadedCluster

-- The entry point is `clusterInterpolation`, which is given a node together with a proof
-- that it is a cluster root, and uses `LoadedCluster.ofClusterRoot` below.

/-- Make the `LoadedCluster` of a right-loaded node that is the first node of its cluster.
This is the way `tabToIntAt` now gets hold of a `LoadedCluster`. -/
def ofClusterRoot (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_loaded_right : (nodeAt s).2.2.isRight) : LoadedCluster tab where
  root := s
  root_not_to_parent := s_cr
  root_loaded_right := s_loaded_right
  CL := clusterListOf s
  root_mem_CL := by
    rw [clusterListOf_spec]
    exact (eProp tab).1.refl s
  CL_equiv := by
    intro u u_in v v_in
    rw [clusterListOf_spec] at u_in v_in
    exact (eProp tab).1.trans ((eProp tab).1.symm u_in) v_in
  CL_complete := by
    intro u u_in v u_v
    rw [clusterListOf_spec] at u_in ⊢
    exact (eProp tab).1.trans u_in u_v
  root_reaches_all := by
    intro u u_in
    rw [clusterListOf_spec] at u_in
    exact u_in.1

/-- The exits of the cluster, i.e. `C⁺ \ C` from Def 8.14. -/
def exits (C : LoadedCluster tab) : List (PathIn tab) :=
  (C.CL.flatMap (fun t => t.children.map Subtype.val)).filter (fun e => e ∉ C.CL)

/-- C⁺, the cluster plus its exits. -/
def CL_plus (C : LoadedCluster tab) : List (PathIn tab) :=
  C.CL ++ C.exits

/-- The list `C.CL` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_CL_iff (C : LoadedCluster tab) (p : PathIn tab) :
    p ∈ C.CL ↔ p ≡ᶜ C.root :=
  ⟨ fun p_in => C.CL_equiv p p_in C.root C.root_mem_CL
  , fun p_c_root => C.CL_complete C.root C.root_mem_CL p ((cEquiv.symm p C.root).mp p_c_root) ⟩

/-- The list `C.exits` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_exits_iff (C : LoadedCluster tab) (e : PathIn tab) :
    e ∈ C.exits ↔ isExitOf C.root e := by
  rw [LoadedCluster.exits, List.mem_filter, List.mem_flatMap]
  simp only [decide_eq_true_eq, isExitOf, ← PathIn.children_spec]
  constructor
  · rintro ⟨⟨t, t_in, t_e⟩, e_not_in⟩
    exact ⟨ fun e_c_root => e_not_in ((C.mem_CL_iff e).mpr e_c_root)
          , t, (C.mem_CL_iff t).mp t_in, t_e ⟩
  · rintro ⟨e_not_root, t, t_root, t_e⟩
    exact ⟨ ⟨t, (C.mem_CL_iff t).mpr t_root, t_e⟩
          , fun e_in => e_not_root ((C.mem_CL_iff e).mp e_in) ⟩

/-- All nodes that are `◃`-between the root of a cluster and itself are loaded. -/
lemma isLoaded_of_between (C : LoadedCluster tab) {v : PathIn tab}
    (h1 : C.root ◃* v) (h2 : v ◃* C.root) : (nodeAt v).isLoaded := by
  by_contra v_free
  have root_eq_v : C.root = v := eq_of_cEquiv_of_isFree v_free ⟨h2, h1⟩
  have v_right := C.root_loaded_right
  rw [root_eq_v] at v_right
  apply v_free
  rcases hh : nodeAt v with ⟨L, R, _|(o|o)⟩ <;> rw [hh] at v_right <;>
    simp_all [Sequent.isLoaded]

/-- Lemma 9.4 (a) -/
lemma all_right_loaded (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).2.2.isRight := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  exact (cReach_inv t_root.2
    (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).1

/-- Lemma 9.4 (b): the left component of a node in the cluster is empty iff the left
component of the root of the cluster is empty. Note that here the left component is the
free side, because a `LoadedCluster` is loaded on the right.
As `Sequent.left ⟨L,R,O⟩ = L ++ O.L` and `O.L = []` for the nodes in the cluster by
`LoadedCluster.all_right_loaded`, this is the same as `Λ₁(t) = ∅ ↔ Λ₁(r) = ∅`. -/
lemma left_empty_iff_root_left_empty (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).1 = [] ↔ (nodeAt C.root).1 = [] := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  constructor
  · exact (cReach_inv t_root.1
      (fun v h1 h2 => C.isLoaded_of_between (t_root.2.trans h1) h2)
      (C.all_right_loaded t t_in)).2
  · exact (cReach_inv t_root.2
      (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).2

/-- Part of Lemma 9.4 (c): All children of t belong to C⁺. -/
lemma children_in_plus (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ∀ c ∈ t.children, c.val ∈ C.CL_plus := by
  intro t t_in c _
  rw [LoadedCluster.CL_plus, List.mem_append]
  by_cases c_in : c.val ∈ C.CL
  · exact Or.inl c_in
  · refine Or.inr ((C.mem_exits_iff c.val).mpr ⟨fun c_root => c_in ?_, t, ?_, c.2⟩)
    · exact (C.mem_CL_iff c.val).mpr c_root
    · exact (C.mem_CL_iff t).mp t_in

/-- Part of Lemma 9.4 (c): If `t` is not an lpr, then at least one child is in C.
This needs that the cluster is proper, i.e. that its root lies on a `◃`-cycle. -/
lemma nonLpr_some_child_in_C (C : LoadedCluster tab)
    (C_proper : C.root ◃⁺ C.root) :
    ∀ t ∈ C.CL, ¬ t.isLrep → ∃ c ∈ t.children, c.val ∈ C.CL := by
  intro t t_in t_not_lrep
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  -- Because the cluster is proper, also `t` lies on a `◃`-cycle:
  have t_cycle : t ◃⁺ t := Relation.TransGen.trans_right t_root.1
    (Relation.TransGen.trans_left C_proper t_root.2)
  obtain ⟨u, t_u, u_t⟩ := Relation.TransGen.head'_iff.mp t_cycle
  -- The first step of that cycle cannot be a ♥ step, because `t` is not an lpr:
  rcases t_u with t_edge_u | ⟨lpr, h_lrep, rfl⟩
  · rw [PathIn.children_spec, List.mem_map] at t_edge_u
    obtain ⟨c, c_in, rfl⟩ := t_edge_u
    exact ⟨c, c_in, (C.mem_CL_iff c.val).mpr ⟨u_t.trans t_root.1,
      t_root.2.trans (Relation.ReflTransGen.single (Or.inl c.2))⟩⟩
  · exact absurd (by unfold PathIn.isLrep; rw [h_lrep]; trivial) t_not_lrep

/-- Part of Lemma 9.4 (c): If t is an lpr, then its companion is in C. -/
lemma lpr_comp_in_C (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, t ♥ comp → comp ∈ C.CL := by
  intro t t_in t_comp
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  refine (C.mem_CL_iff comp).mpr ⟨?_, ?_⟩
  · -- comp ◃* root, because comp is above t.
    exact (cReach_of_le (companion_lt t_comp).to_reflTransGen).trans t_root.1
  · -- root ◃* comp, going via t.
    exact t_root.2.tail (Or.inr t_comp)

/-- Def 9.6: All nodes in cluster with a certain list (WORRY should it be set??) on the right.
TODO: `.right` might not get or not keep track of the loaded formula!
Better use `List WhateverFormula` and `Sequent.wForms` here maybe?
-/
def nodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
  C.CL.filter (fun p => decide ((nodeAt p).right = Δ))

def plusNodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
  C.CL_plus.filter (fun p => decide ((nodeAt p).right = Δ))

/-! ### The cluster at the fine level

The `CL` field of a `LoadedCluster` only contains the nodes in the coarse `PathIn` sense.
For Definition 9.8 we also need the intermediate nodes inside the local tableaux, so we
now determine which fine nodes belong to the cluster.

An intermediate node `v` inside the local tableau at a node `p` of the cluster belongs to
the cluster iff some child of `p` below `v` is again in the cluster: in that case `v` lies
on a `◃` cycle. Note that the children of `p` are exactly the nodes `p.append (loc Y_in nil)`
for the end nodes `Y` of the local tableau at `p`, and they are labelled with `Y`. -/

/-- A fine node belongs to the cluster `C` iff its base node is in `C` and either it *is*
that base node, or one of the children of the base node below it is in `C`. -/
def memFine (C : LoadedCluster tab) (f : FinePathIn tab) : Prop :=
  f.base ∈ C.CL ∧ ( f.atBigRoot ∨ ∃ q ∈ f.coarseChildrenBelow, q ∈ C.CL )

instance instDecidableMemFine (C : LoadedCluster tab) (f : FinePathIn tab) :
    Decidable (C.memFine f) := by
  unfold memFine; infer_instance

/-- Nodes of the cluster in the coarse sense are also fine nodes of the cluster. -/
lemma memFine_toFine (C : LoadedCluster tab) {p : PathIn tab} (p_in : p ∈ C.CL) :
    C.memFine p.toFine := ⟨by simpa using p_in, Or.inl (by simp)⟩

/-- All fine nodes in the cluster `C`. -/
def fineCL (C : LoadedCluster tab) : List (FinePathIn tab) :=
  (allFinePaths tab).filter (fun f => decide (C.memFine f))

lemma mem_fineCL (C : LoadedCluster tab) (f : FinePathIn tab) :
    f ∈ C.fineCL ↔ C.memFine f := by
  simp [fineCL, f.mem_allFinePaths]

lemma root_toFine_mem_fineCL (C : LoadedCluster tab) : C.root.toFine ∈ C.fineCL :=
  (C.mem_fineCL _).mpr (C.memFine_toFine C.root_mem_CL)

/-- If a fine node of the cluster has a coarse child of the cluster below it, then it has
a fine child in the cluster. -/
lemma exists_child_memFine_aux (C : LoadedCluster tab) {f : FinePathIn tab}
    (f_base : f.base ∈ C.CL) {q : PathIn tab} (hq : q ∈ f.coarseChildrenBelow)
    (q_in : q ∈ C.CL) : ∃ g ∈ f.children, C.memFine g := by
  obtain ⟨g, g_in, hg⟩ := f.exists_child_coarseChildrenBelow q hq
  refine ⟨g, g_in, ?_⟩
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ f_base, Or.inr ⟨q, h2, q_in⟩⟩
  · exact ⟨h1 ▸ q_in, Or.inl h2⟩

/-- Lemma 9.7 (c) at the fine level, for nodes that are not coarse nodes: if a fine node
`f` inside a local tableau belongs to the cluster, then so does one of its children. -/
lemma exists_child_memFine (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : C.memFine f) (h_not : ¬ f.atBigRoot) : ∃ g ∈ f.children, C.memFine g := by
  obtain ⟨f_base, hor⟩ := hf
  rcases hor with h | ⟨q, q_below, q_in⟩
  · exact absurd h h_not
  · exact C.exists_child_memFine_aux f_base q_below q_in

/-- Lemma 9.7 (c) at the fine level, in general: any fine node of the cluster that is not
a loaded-path repeat has a child in the cluster. For coarse nodes this uses Lemma 9.4 (c),
i.e. `nonLpr_some_child_in_C`, and hence needs that the cluster is proper. -/
lemma exists_child_memFine_of_not_isLrep (C : LoadedCluster tab) (C_proper : C.root ◃⁺ C.root)
    {f : FinePathIn tab} (hf : C.memFine f) (h_lrep : ¬ f.base.isLrep) :
    ∃ g ∈ f.children, C.memFine g := by
  by_cases hbr : f.atBigRoot
  · obtain ⟨c, -, c_CL⟩ := C.nonLpr_some_child_in_C C_proper f.base hf.1 h_lrep
    have hmem : c.val ∈ f.base.toFine.coarseChildrenBelow :=
      PathIn.mem_coarseChildrenBelow_toFine _ _ c.2
    rw [← f.eq_toFine_base_of_atBigRoot hbr] at hmem
    exact C.exists_child_memFine_aux hf.1 hmem c_CL
  · exact C.exists_child_memFine hf hbr

/-- All fine nodes just outside the cluster `C`, i.e. `C⁺ \ C` at the fine level. -/
def fineExits (C : LoadedCluster tab) : List (FinePathIn tab) :=
  (C.fineCL.flatMap FinePathIn.children).filter (fun f => decide (¬ C.memFine f))

/-- The fine version of `C⁺`. -/
def fineCLplus (C : LoadedCluster tab) : List (FinePathIn tab) :=
  C.fineCL ++ C.fineExits

/-- `Λ₂[C]`, the right components of the fine nodes of the cluster. -/
def lambdaTwo (C : LoadedCluster tab) : List Sequent :=
  (C.fineCL.map (fun f => f.label.rightOnly)).dedup

/-- `Λ₂[C⁺]`, the right components of the fine nodes of the cluster and of its exits. -/
def lambdaTwoPlus (C : LoadedCluster tab) : List Sequent :=
  (C.fineCLplus.map (fun f => f.label.rightOnly)).dedup

/-- `C_Δ` from Def 9.6, at the fine level. -/
def nodesWithFine (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  C.fineCL.filter (fun f => decide (f.label.rightOnly = Δ))

/-- `C⁺_Δ` from Def 9.6, at the fine level. -/
def plusNodesWithFine (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  C.fineCLplus.filter (fun f => decide (f.label.rightOnly = Δ))

/-- `C^R_Δ` from Def 9.6: nodes with right component `Δ` where a right rule is applied. -/
def nodesWithFineRight (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => f.usesRightRule)

/-- `C^L_Δ` from Def 9.6: nodes with right component `Δ` where a left rule is applied. -/
def nodesWithFineLeft (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => f.usesLeftRule)

/-- Nodes with right component `Δ` where no rule is applied at all. These are the
loaded-path repeats and the closing rules, which Lemma 9.7 (a) in the paper does not
mention. -/
def nodesWithFineNoRule (C : LoadedCluster tab) (Δ : Sequent) : List (FinePathIn tab) :=
  (C.nodesWithFine Δ).filter (fun f => !f.usesLeftRule && !f.usesRightRule)

/-- Lemma 9.7 (a), first part: `C_Δ` is the union of `C^L_Δ` and `C^R_Δ` and the nodes
where no rule is applied. -/
lemma mem_nodesWithFine_iff (C : LoadedCluster tab) (Δ : Sequent) (f : FinePathIn tab) :
    f ∈ C.nodesWithFine Δ ↔
      f ∈ C.nodesWithFineLeft Δ ∨ f ∈ C.nodesWithFineRight Δ ∨ f ∈ C.nodesWithFineNoRule Δ := by
  simp only [nodesWithFineLeft, nodesWithFineRight, nodesWithFineNoRule, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h
    by_cases hl : f.usesLeftRule
    · exact Or.inl ⟨h, hl⟩
    · by_cases hr : f.usesRightRule
      · exact Or.inr (Or.inl ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, by simp_all⟩)
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact h

/-- Lemma 9.7 (a), second part: `C^L_Δ` and `C^R_Δ` are disjoint. -/
lemma nodesWithFineLeft_disjoint_right (C : LoadedCluster tab) (Δ : Sequent) :
    ∀ f ∈ C.nodesWithFineLeft Δ, f ∉ C.nodesWithFineRight Δ := by
  intro f f_in f_in'
  simp only [nodesWithFineLeft, nodesWithFineRight, List.mem_filter] at f_in f_in'
  exact f.not_left_and_right ⟨f_in.2, f_in'.2⟩

/-- `Δ ∈ Λ₂[C]` iff `C_Δ ≠ ∅`, the remark after the invariant in Def 9.8. -/
lemma mem_lambdaTwo_iff (C : LoadedCluster tab) (Δ : Sequent) :
    Δ ∈ C.lambdaTwo ↔ C.nodesWithFine Δ ≠ [] := by
  simp only [lambdaTwo, List.mem_dedup, List.mem_map, ne_eq,
    nodesWithFine, List.filter_eq_nil_iff, not_forall, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, by simp⟩
  · rintro ⟨f, hf, hf2⟩
    exact ⟨f, hf, by simpa using hf2⟩

/-- The right components of the children of a node in `C^R_Δ`.

For the quasi-tableau in Def 9.8 we need, given `Δ ∈ Λ₂[C]`, the sequents `Π₁, …, Πₙ`
obtained by applying the right rule to `Δ` — both for local rules (Lemma 9.7 (f)) and for
the modal rule when `Δ` is basic (Lemma 9.7 (e)). Instead of using uniformity to *choose*
such a rule we here simply *look up* the first node of `C^R_Δ` and read off the right
components of its children. By uniformity (which we do not prove here) this does not
depend on the chosen node. When `C^R_Δ` is empty — which by Lemma 9.7 (d) only happens
when `C_Δ` is empty, i.e. when `Δ ∉ Λ₂[C]` — we return the empty list, but note that the
construction of `Q` below never uses `stepOf` in that case. -/
def stepOf (C : LoadedCluster tab) (Δ : Sequent) : List Sequent :=
  match (C.nodesWithFineRight Δ).head? with
  | some f => f.children.map (fun g => g.label.rightOnly)
  | none => []

/-- If some right rule is applied at a node of the cluster with right component `Δ`, then
`stepOf Δ` is non-empty: by Lemma 9.7 (c) that node has a child in the cluster, so the rule
applied there cannot be a closing rule. -/
lemma stepOf_ne_nil (C : LoadedCluster tab) (C_proper : C.root ◃⁺ C.root) {Δ : Sequent}
    (h : C.nodesWithFineRight Δ ≠ []) : C.stepOf Δ ≠ [] := by
  unfold stepOf
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) h
  | some f =>
    have f_in := List.mem_of_mem_head? hh
    simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at f_in
    obtain ⟨⟨f_CL, -⟩, f_right⟩ := f_in
    obtain ⟨g, g_in, -⟩ := C.exists_child_memFine_of_not_isLrep C_proper
      ((C.mem_fineCL f).mp f_CL) (f.not_isLrep_base_of_usesRightRule f_right)
    simp only [ne_eq, List.map_eq_nil_iff]
    intro hnil
    rw [hnil] at g_in
    simp at g_in

/-- A child of a fine node of the cluster is a fine node of `C⁺`. -/
lemma mem_fineCLplus_of_child (C : LoadedCluster tab) {f g : FinePathIn tab}
    (hf : f ∈ C.fineCL) (hg : g ∈ f.children) : g ∈ C.fineCLplus := by
  by_cases h : C.memFine g
  · exact List.mem_append_left _ ((C.mem_fineCL g).mpr h)
  · refine List.mem_append_right _ ?_
    simp only [fineExits, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
    exact ⟨⟨f, hf, hg⟩, h⟩

/-- The right component of a fine node of `C⁺` is in `Λ₂[C⁺]`. -/
lemma mem_lambdaTwoPlus_of_mem_fineCLplus (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineCLplus) : f.label.rightOnly ∈ C.lambdaTwoPlus := by
  simp only [lambdaTwoPlus, List.mem_dedup, List.mem_map]
  exact ⟨f, hf, rfl⟩

/-- `Λ₂[C] ⊆ Λ₂[C⁺]`. -/
lemma lambdaTwo_subset_lambdaTwoPlus (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, Δ ∈ C.lambdaTwoPlus := by
  intro Δ hΔ
  simp only [lambdaTwo, List.mem_dedup, List.mem_map] at hΔ
  obtain ⟨f, hf, rfl⟩ := hΔ
  exact C.mem_lambdaTwoPlus_of_mem_fineCLplus (List.mem_append_left _ hf)

/-- The labels given by `stepOf` are in `Λ₂[C⁺]`. This is the invariant needed in Def 9.8:
a node of `Q` is labelled with an element of `Λ₂[C⁺]`, and it is a leaf exactly when it is
a repeat or its label is not in `Λ₂[C]`, i.e. when it is an exit. -/
lemma stepOf_mem_lambdaTwoPlus (C : LoadedCluster tab) (Δ : Sequent) :
    ∀ Pi ∈ C.stepOf Δ, Pi ∈ C.lambdaTwoPlus := by
  intro Pi hPi
  unfold stepOf at hPi
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => rw [hh] at hPi; simp at hPi
  | some f =>
    rw [hh] at hPi
    simp only [List.mem_map] at hPi
    obtain ⟨g, hg, rfl⟩ := hPi
    have hf : f ∈ C.fineCL := by
      have := List.mem_of_mem_head? hh
      simp only [nodesWithFineRight, nodesWithFine, List.mem_filter] at this
      exact this.1.1
    exact C.mem_lambdaTwoPlus_of_mem_fineCLplus (C.mem_fineCLplus_of_child hf hg)

end LoadedCluster

/-! ## Quasi-Tableaux (Def 9.8) -/

-- Alternative idea for quasi-tableau:
-- Instead of labelling nodes in Q with finite sequents, label them with the path to where
-- that sequent comes from in `Λ₂[C⁺]`?

inductive Typ | one | two | three -- lower case because these are not `Type`s.
open Typ

/-- Simple tree data type for `Q` in Def. 7.31. -/
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
    · simp only [List.countP_cons, hp, hq, Bool.false_eq_true, if_false, if_true]
      omega
    · have hlt := ih (fun x hx => h x (by simp [hx])) ha'
      simp only [List.countP_cons]
      by_cases hb : p b
      · have hb' := h b (by simp) hb
        simp only [hb, hb', if_true]
        omega
      · simp only [hb, Bool.false_eq_true, if_false]
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
def QuasiTab.build (inC : List Sequent) (step : Sequent → List Sequent)
    (Hist : List Sequent) (Δ : Sequent) : QuasiTab :=
  -- The hypothesis `_h` is only used in the termination proof below.
  if _h : Δ ∈ inC ∧ Δ ∉ Hist then
    QNode one Δ [ QNode two Δ [ QNode three Δ
      ((step Δ).map (fun Pi => QuasiTab.build inC step (Δ :: Hist) Pi)) ] ]
  else
    QNode one Δ []
termination_by (inC.filter (fun Z => decide (Z ∉ Hist))).length
decreasing_by exact length_filter_notMem_cons_lt _h.1 _h.2

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
lemma QuasiTab.build_label_mem {inC lam : List Sequent} {step : Sequent → List Sequent}
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
lemma QuasiTab.build_inner_label_mem {inC : List Sequent} {step : Sequent → List Sequent}
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
  simp only [LoadedCluster.lambdaTwo, List.mem_dedup, List.mem_map]
  exact ⟨C.root.toFine, C.root_toFine_mem_fineCL, by simp⟩

/-- Def 9.8: the quasi-tableau associated with the cluster `C`. Its root has type 1 and is
labelled with the right component `Λ₂(r)` of the root `r` of the cluster. -/
def LoadedCluster.Q (C : LoadedCluster tab) : QuasiTab :=
  QuasiTab.build C.lambdaTwo C.stepOf [] (nodeAt C.root).rightOnly

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
    ∀ q ∈ C.Q.subtrees, q.label ∈ C.lambdaTwoPlus :=
  QuasiTab.build_label_mem C.stepOf_mem_lambdaTwoPlus _ _
    (C.lambdaTwo_subset_lambdaTwoPlus _ C.root_rightOnly_mem_lambdaTwo)

/-- The invariant of Def 9.8 for `Q`: every inner node of `Q` has a label in `Λ₂[C]`. -/
lemma LoadedCluster.Q_inner_label_mem_lambdaTwo (C : LoadedCluster tab) :
    ∀ q ∈ C.Q.subtrees, q.children ≠ [] → q.label ∈ C.lambdaTwo :=
  QuasiTab.build_inner_label_mem _ _

/-- Remark 9.9 for `Q`: all leaves of the quasi-tableau have type 1. Here `h97d` is
Lemma 9.7 (d), which we state as a hypothesis: for every label in `Λ₂[C]` there is a node
of the cluster with that right component where a right rule is applied. -/
lemma LoadedCluster.Q_leaf_typ (C : LoadedCluster tab) (C_proper : C.root ◃⁺ C.root)
    (h97d : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []) :
    ∀ q ∈ C.Q.subtrees, q.children = [] → q.typ = Typ.one :=
  QuasiTab.build_leaf_typ (fun Δ hΔ => C.stepOf_ne_nil C_proper (h97d Δ hΔ)) _ _

/-- Def 9.10: the region `Rₓ ⊆ C⁺` represented by a node `x` of the quasi-tableau.
For type 1 and 2 these are all nodes of `C⁺` with right component `Δₓ`, and for type 3
those nodes of `C` with right component `Δₓ` where a right rule is applied. -/
def LoadedCluster.region (C : LoadedCluster tab) : Typ → Sequent → List (FinePathIn tab)
  | .one, Δ => C.plusNodesWithFine Δ
  | .two, Δ => C.plusNodesWithFine Δ
  | .three, Δ => C.nodesWithFineRight Δ

/-- Def 9.10, applied to a node of the quasi-tableau. -/
def LoadedCluster.regionOf (C : LoadedCluster tab) (q : QuasiTab) : List (FinePathIn tab) :=
  C.region q.typ q.label

/-! ### Flipping Interpolants -/

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp_all
  grind

/-- Transport an interpolant to the flipped tableau. -/
def PartInterpolant.flipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p)) : PartInterpolant (nodeAt p.flip) :=
  ⟨~ip.1, by rw [PathIn.nodeAt_flip]; exact IsPartInterpolant.flip ip.2⟩

/-- Transport an interpolant back from the flipped tableau. -/
def PartInterpolant.unflipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p.flip)) : PartInterpolant (nodeAt p) := by
  refine ⟨~ip.1, ?_⟩
  have h : (nodeAt p.flip).flip = nodeAt p := by rw [PathIn.nodeAt_flip, Sequent.flip_flip]
  exact h ▸ IsPartInterpolant.flip ip.2

/-! ## Interpolants for proper clusters -/

/-- Lemma 9.3 for the case where the loaded formula is on the right side:
given interpolants for all exits of the cluster `C`, interpolate the root of `C`. -/
def clusterInterpolation_right (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt C.root) := by
  sorry

/-- Lemma 9.3: Given a loaded node `s` that is the first node of its cluster, and given
interpolants for all exits of that cluster, we get an interpolant for `s`.
Note how `s_cr` is exactly what is needed to make a `LoadedCluster` here. -/
def clusterInterpolation (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_loaded : (nodeAt s).isLoaded)
    (exitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt s) := by
  by_cases s_right : (nodeAt s).2.2.isRight
  case pos =>
    -- The loaded formula is on the right, so we can use `clusterInterpolation_right`.
    exact clusterInterpolation_right (LoadedCluster.ofClusterRoot s s_cr s_right)
      (fun e e_in => exitIPs e ((LoadedCluster.mem_exits_iff _ e).mp e_in))
  case neg =>
    -- The loaded formula is on the left, so we "flip" the whole tableau.
    have s_flip_right : (nodeAt s.flip).2.2.isRight := by
      rw [PathIn.nodeAt_flip]
      rcases hh : nodeAt s with ⟨L, R, O⟩
      rw [hh] at s_right s_loaded
      cases O
      · simp [Sequent.isLoaded] at s_loaded
      case some val => cases val <;> simp_all [Sequent.flip, Olf.flip]
    let C : LoadedCluster tab.flip :=
      LoadedCluster.ofClusterRoot s.flip (PathIn.isClusterRoot_flip s_cr) s_flip_right
    have flipIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e) := by
      intro e e_in
      have e_exit : isExitOf s.flip e := (LoadedCluster.mem_exits_iff _ e).mp e_in
      rw [← PathIn.flip_unflip e] at e_exit ⊢
      exact PartInterpolant.flipPath (exitIPs e.unflip (isExitOf_flip.mp e_exit))
    exact PartInterpolant.unflipPath (clusterInterpolation_right C flipIPs)
