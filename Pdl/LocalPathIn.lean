import Pdl.Flip
import Pdl.KeepRight

/-! # Fine paths in local tableaux and in tableaux

This file collects helper definitions and lemmas that are used in `Pdl.InterpolationCluster`
to define interpolants for proper clusters (Section 9 of the paper).

The two main definitions are `LocalPathIn`, for paths to arbitrary (also intermediate) nodes
of a `LocalTableau`, and `FinePathIn`, for the nodes of a whole `Tableau` in the *fine* sense,
i.e. including those nodes inside a local tableau that a `loc` step jumps over.
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
