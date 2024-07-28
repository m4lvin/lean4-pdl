-- SOUNDNESS

import Pdl.Tableau
import Pdl.LoadSplit

import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

open Classical

open HasSat

/-! ## Soundness of the PDL rules -/

/-- The PDL rules are sound. -/
theorem pdlRuleSat (r : PdlRule X Y) (satX : satisfiable X) : satisfiable Y := by
  rcases satX with ⟨W, M, w, w_⟩
  -- 6 cases, quite some duplication here unfortunately.
  cases r
  -- the loading rules are easy, because loading never changes semantics
  case loadL =>
    use W, M, w
    simp_all [modelCanSemImplyTNode]
    intro φ φ_in
    rcases φ_in with ((in_L | in_R) | φ_def)
    all_goals (apply w_; subst_eqs; try tauto)
    left; exact List.mem_of_mem_erase in_L
  case loadR =>
    use W, M, w
    simp_all [modelCanSemImplyTNode]
    intro φ φ_in
    rcases φ_in with ((in_L | in_R) | φ_def)
    all_goals (apply w_; subst_eqs; try tauto)
    right; exact List.mem_of_mem_erase in_R
  case freeL =>
    use W, M, w
    simp_all [modelCanSemImplyTNode]
    intro φ φ_in
    rcases φ_in with (φ_def | (in_L | in_R))
    all_goals (apply w_; tauto)
  case freeR =>
    use W, M, w
    simp_all [modelCanSemImplyTNode]
    intro φ φ_in
    rcases φ_in with (φ_def | (in_L | in_R))
    all_goals (apply w_;  subst_eqs; try tauto)
  case modL L R a χ X_def x_basic =>
    subst X_def
    use W, M -- but not the same world!
    have := w_ (negUnload (~'⌊·a⌋χ))
    cases χ
    · simp [unload] at *
      rcases this with ⟨v, w_a_b, v_⟩
      use v
      intro φ φ_in
      simp at φ_in
      rcases φ_in with ( φ_def | (in_L | in_R))
      · subst φ_def
        simp only [evaluate]
        assumption
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
    · simp [unload] at *
      rcases this with ⟨v, w_a_b, v_⟩
      use v
      intro φ φ_in
      simp at φ_in
      rcases φ_in with ((in_L | in_R) | φ_def)
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · subst φ_def
        simp only [evaluate]
        assumption
  case modR L R a χ X_def x_basic =>
    subst X_def
    use W, M -- but not the same world!
    have := w_ (negUnload (~'⌊·a⌋χ))
    cases χ
    · simp [unload] at *
      rcases this with ⟨v, w_a_b, v_⟩
      use v
      intro φ φ_in
      simp at φ_in
      rcases φ_in with (in_L | (φ_def | in_R))
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · subst φ_def
        simp only [evaluate]
        assumption
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
    · simp [unload] at *
      rcases this with ⟨v, w_a_b, v_⟩
      use v
      intro φ φ_in
      simp at φ_in
      rcases φ_in with ((in_L | in_R) | φ_def)
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · have := w_ (⌈·a⌉φ) (by simp; tauto)
        simp at this;
        exact this _ w_a_b
      · subst φ_def
        simp only [evaluate]
        assumption

/-! ## Navigating through tableaux with PathIn -/

-- To define ancestor / decendant relations inside tableaux we need to
-- represent both the whole Tableau and a specific node in it.
-- For this we use the type `PathIn`.
-- Its values basically say "go to this child, then to this child, etc."

/-- A path in a tableau. Three constructors for the empty path, a local step or a pdl step.
The `loc` ad `pdl` steps correspond to two out of three constructors of `Tableau`. -/
inductive PathIn : ∀ {H X}, Tableau H X → Type
| nil : PathIn _
| loc : (Y_in : Y ∈ endNodesOf lt) → (tail : PathIn (next Y Y_in)) → PathIn (Tableau.loc lt next)
| pdl : (r : PdlRule Γ Δ) → PathIn (child : Tableau (Γ :: Hist) Δ) → PathIn (Tableau.pdl r child)

def tabAt : PathIn tab → Σ H X, Tableau H X
| .nil => ⟨_,_,tab⟩
| .loc _ tail => tabAt tail
| .pdl _ p_child => tabAt p_child

def PathIn.append (p : PathIn tab) (q : PathIn (tabAt p).2.2) : PathIn tab := match p with
  | .nil => q
  | .loc Y_in tail => .loc Y_in (PathIn.append tail q)
  | .pdl r p_child => .pdl r (PathIn.append p_child q)

@[simp]
theorem tabAt_append (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    tabAt (p.append q) = tabAt q := by
  induction p
  case nil => simp [PathIn.append]
  case loc IH =>
    simp [PathIn.append]
    rw [← IH]
    simp [tabAt]
  case pdl IH =>
    simp [PathIn.append]
    rw [← IH]
    simp [tabAt]

@[simp]
theorem tabAt_nil {tab : Tableau Hist X} : tabAt (.nil : PathIn tab) = ⟨_, _, tab⟩ := by
  simp [tabAt, tabAt]

@[simp]
theorem tabAt_loc : tabAt (.loc Y_in tail : PathIn _) = tabAt tail := by simp [tabAt]

@[simp]
theorem tabAt_pdl : tabAt (.pdl r tail : PathIn _) = tabAt tail := by simp [tabAt]

/-- Given a path to node `t`, this is its label Λ(t). -/
def nodeAt {H X} {tab : (Tableau H X)} (p : PathIn tab) : TNode := (tabAt p).2.1

@[simp]
theorem nodeAt_nil {tab : Tableau Hist X} : nodeAt (.nil : PathIn tab) = X := by
  simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_loc : nodeAt (.loc Y_in tail : PathIn _) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_pdl : nodeAt (.pdl r tail : PathIn _) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_append (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    nodeAt (p.append q) = nodeAt q := by
  unfold nodeAt
  rw [tabAt_append p q]

/-! ## Parents, Children, Ancestors and Descendants -/

/-- One-step children, with changed type. Use `children` instead. -/
def children' (p : PathIn tab) : List (PathIn (tabAt p).2.2) := match tabAt p with
  | ⟨_, _, Tableau.loc lt _next⟩  =>
      ((endNodesOf lt).attach.map (fun ⟨_, Y_in⟩ => [ .loc Y_in .nil ] )).join
  | ⟨_, _, Tableau.pdl r _ct⟩  => [ .pdl r .nil ]
  | ⟨_, _, Tableau.rep _⟩  => [ ]

/-- List of one-step children, given by paths from the same root. -/
def children (p : PathIn tab) : List (PathIn tab) := (children' p).map (PathIn.append p)

/-- The parent-child relation `s ◃ t` in a tableau -/
def edge {H X} {tab : Tableau H X} (s t : PathIn tab) : Prop :=
  t ∈ children s

/-- Notation ◃ for `edge` (because ⋖ in notes is taken in Mathlib). -/
notation s:arg " ◃ " t:arg => edge s t

/-- The ◃ relation is well-founded, i.e. all tableaux are finite. -/
theorem edge.wellFounded : WellFounded (@edge _ _ tab) := by
  constructor
  intro a
  constructor
  -- induction a  OR  induction tab  here?
  sorry

instance edge.isAsymm : IsAsymm (PathIn tab) edge := by
  constructor
  apply WellFounded.asymmetric edge.wellFounded

/-- Enable "<" notation for transitive closure of ⋖ -/
instance : LT (PathIn tab) := ⟨Relation.TransGen edge⟩

/-- Enable "≤" notation for transitive closure of ⋖ -/
instance : LE (PathIn tab) := ⟨Relation.ReflTransGen edge⟩

/-! ## Alternative definitions of `edge` -/

/-- Attempt to define `edge` *recursively* by "going to the end" of the paths.
Note there are no mixed .loc and .pdl cases. -/
-- TODO: try if making this the definition makes life easier?
def edgeRec : PathIn tab → PathIn tab → Prop
| .nil, .nil => false
| .nil, .loc Y_in tail => tail = .nil
| .nil, .pdl _ tail => tail = .nil
| .pdl _ _, .nil => false
| .pdl _ tail, .pdl _ tail2 => edgeRec tail tail2
| .loc _ _, .nil => false
| @PathIn.loc _ _ Y1 _ _ _ tail1,
  @PathIn.loc _ _ Y2 _ _ _ tail2 =>
  if h : Y1 = Y2 then edgeRec tail1 (h ▸ tail2) else false

/-- Alternative definition of `edge` by two cases via `append`. -/
-- TODO: prove that this is equivalent? (or try it out as the definition?)
def edgeCases (s t : PathIn tab) : Prop :=
  ( ∃ Hist X lt next Y, ∃ (Y_in : Y ∈ endNodesOf lt) (h : tabAt s = ⟨Hist, X, Tableau.loc lt next⟩),
      t = s.append (h ▸ PathIn.loc Y_in .nil) )
  ∨
  ( ∃ Hist X Y r, ∃ (next : Tableau (X :: Hist) Y) (h : tabAt s = ⟨Hist, X, Tableau.pdl r next⟩),
      t = s.append (h ▸ PathIn.pdl r .nil) )

/-
/-- Slightly broken attempt to define `edgeCases` *inductively*. -/
inductive edgeIndu : PathIn tab → PathIn tab → Prop
| loc Hist X lt next Y (Y_in : Y ∈ endNodesOf lt)
      (h : tabAt s = ⟨Hist, X, Tableau.loc lt next⟩)
      (h2 : t = s.append (h ▸ PathIn.loc Y_in .nil))
      : edgeIndu s t
| pdl Hist X Y r (next : Tableau (X :: Hist) Y)
      (h : tabAt s = ⟨Hist, X, Tableau.pdl r next⟩)
      (h2 : t = s.append (h ▸ PathIn.pdl r .nil))
      : edgeIndu s t
-/

/-! ## More about Path and History -/

@[simp]
def PathIn.head {tab : Tableau Hist X} (_ : PathIn tab) : TNode := X

@[simp]
def PathIn.last (t : PathIn tab) : TNode := (tabAt t).2.1

/-- Convert a path to a History. Does not include the last node.
The history of `.nil` is `[]`. -/
def PathIn.toHistory {tab : Tableau Hist X} : (t : PathIn tab) → History
| .nil => []
| .pdl _ tail => tail.toHistory ++ [X]
| .loc _ tail => tail.toHistory ++ [X]

/-- Convert a path to a list of nodes. Reverse of the history and does include the last node.
The list of `.nil` is `[X]`. -/
def PathIn.toList {tab : Tableau Hist X} : (t : PathIn tab) → List TNode
| .nil => [X]
| .pdl _ tail => X :: tail.toList
| .loc _ tail => X :: tail.toList

/-- The length of a path is the number of actual steps. -/
@[simp]
def PathIn.length : (t : PathIn tab) → ℕ
| .nil => 0
| .pdl _ tail => tail.length + 1
| .loc _ tail => tail.length + 1

-- TODO: PathIn.length = PathIn.tohistory.length ??

/-- A path gives the same list of nodes as the history of its last node. -/
theorem PathIn.toHistory_eq_Hist {tab : Tableau Hist X} (t : PathIn tab) :
    t.toHistory ++ Hist = (tabAt t).1 := by
  induction tab
  all_goals
    cases t <;> simp_all [tabAt, PathIn.toHistory]

theorem tabAt_fst_length_eq_toHistory_length {tab : Tableau .nil X} (s : PathIn tab) :
    (tabAt s).fst.length = s.toHistory.length := by
  have := PathIn.toHistory_eq_Hist s
  rw [← this]
  simp

def PathIn.isLoaded (t : PathIn tab) : Prop :=
match t with
  | .nil => t.head.isLoaded
  | .pdl _ tail => t.head.isLoaded ∧ tail.isLoaded
  | .loc _ tail => t.head.isLoaded ∧ tail.isLoaded

/-- A path is critical iff the (M) rule is used on it. -/
def PathIn.isCritical (t : PathIn tab) : Prop :=
match t with
  | .nil => False
  | .pdl (.modL _ _) _ => True
  | .pdl (.modR _ _) _ => True
  | .pdl _ tail => tail.isCritical
  | .loc _ tail => tail.isCritical

/-- Prefix of a path, taking only the first `k` steps. -/
def PathIn.prefix {tab : Tableau Hist X} : (t : PathIn tab) → (k : Fin (t.length + 1)) → PathIn tab
| .nil, _ => .nil
| .pdl r tail, k => Fin.cases (.nil) (fun j => .pdl r (tail.prefix j)) k
| .loc Y_in tail, k => Fin.cases (.nil) (fun j => .loc Y_in (tail.prefix j)) k

/-- The list of a prefix of a path is the same as the prefix of the list of the path. -/
theorem PathIn.prefix_toList_eq_toList_take {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.length + 1))
    : (t.prefix k).toList = (t.toList).take (k + 1) := by
  induction tab
  case loc rest Y lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toList, PathIn.prefix]
    case loc Z Z_in tail =>
      simp [PathIn.toList, PathIn.prefix]
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList, PathIn.prefix]
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toList, PathIn.prefix]
    case pdl rest Y Z r tab IH tail =>
      simp [PathIn.toList, PathIn.prefix]
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList, PathIn.prefix]
  case rep =>
    cases t
    simp_all [PathIn.toList, PathIn.prefix]

-- theorem idea : k + j = length → prefix k). append (suffix j) = same ...

/-- Rewinding a path, removing the last `k` steps. Cannot go into Hist.
Used to go to the companion of a repeat. -/
def PathIn.rewind : (t : PathIn tab) → (k : Fin (t.toHistory.length + 1)) → PathIn tab
| .nil, _ => .nil
| .loc Y_in tail, k =>
    have : List.length tail.toHistory + 1 = List.length (loc Y_in tail).toHistory := by simp [toHistory]
    Fin.cases (PathIn.loc Y_in tail) (PathIn.loc Y_in ∘ (this ▸ tail.rewind)) k
| .pdl r tail, k =>
    have : List.length tail.toHistory + 1 = List.length (pdl r tail).toHistory := by simp [toHistory]
    Fin.cases (PathIn.pdl r tail) (PathIn.pdl r ∘ (this ▸ tail.rewind)) k

theorem PathIn.rewind_le (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) : t.rewind k ≤ t := by
  induction tab
  case loc rest Y lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toHistory, PathIn.rewind]
      unfold LE.le instLEPathIn; simp; exact Relation.ReflTransGen.refl
    case loc Z Z_in tail =>
      simp [PathIn.toHistory, PathIn.rewind]
      specialize IH Z Z_in tail
      have : (loc Z_in tail).toHistory.length = tail.toHistory.length + 1 := by simp [PathIn.toHistory]

      sorry
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toHistory, PathIn.rewind]
      unfold LE.le instLEPathIn; simp; exact Relation.ReflTransGen.refl
    case pdl rest Y Z r tab IH tail =>
      simp [PathIn.toHistory, PathIn.rewind]
      specialize IH tail
      have : (pdl r tail).toHistory.length = tail.toHistory.length + 1 := by simp [PathIn.toHistory]
      sorry
  case rep =>
    cases t
    simp_all [PathIn.toList, PathIn.rewind]
    unfold LE.le instLEPathIn; simp; exact Relation.ReflTransGen.refl

/-- The node we get from rewinding `k` steps is element `k+1` in the history. -/
theorem PathIn.nodeAt_rewind_eq_toHistory_get {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1))
    : nodeAt (t.rewind k) = (nodeAt t :: t.toHistory).get k := by
  induction tab
  case loc rest Y lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toHistory, PathIn.rewind]
    case loc Z Z_in tail =>
      cases k using Fin.cases
      · specialize IH Z Z_in tail 0
        simp [PathIn.toHistory, PathIn.rewind] at *
      case succ j =>
        have : List.length (loc Z_in tail).toHistory = List.length tail.toHistory + 1 := by sorry
        specialize IH Z Z_in tail (this ▸ j)
        -- almost there, how to simplify nodeAt tail rewind ??
        -- simp_all [PathIn.rewind, nodeAt, tabAt]
        sorry
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toHistory, PathIn.rewind]
    case pdl rest Y Z r tab IH tail =>
      simp [PathIn.toHistory, PathIn.rewind]
      simp [PathIn.toHistory] at k
      induction k using Fin.inductionOn
      · specialize IH tail
        -- should be similar to `loc` case
        sorry
      · assumption
  case rep =>
    cases t
    simp_all [PathIn.toHistory, PathIn.rewind]


/-! ## Companion, ccEdge, cEdge, etc. -/

/-- To get the companion of an LPR node we go as many steps back as the LPR says. -/
def companionOf {X} {tab : Tableau .nil X} (s : PathIn tab) lpr
  (_ : (tabAt s).2.2 = Tableau.rep lpr) : PathIn tab :=
    s.rewind ((tabAt_fst_length_eq_toHistory_length s ▸ lpr.val).succ)

/-- s ♥ t means s is a LPR and its companion is t -/
def companion {X} {tab : Tableau .nil X} (s t : PathIn tab) : Prop :=
  ∃ (lpr : _) (h : (tabAt s).2.2 = Tableau.rep lpr), t = companionOf s lpr h

notation pa:arg " ♥ " pb:arg => companion pa pb

/-- The node at a companion is the same as the one in the history. -/
theorem nodeAt_companionOf_eq_toHistory_get_lpr_val (s : PathIn tab) lpr h :
    nodeAt (companionOf s lpr h)
    = s.toHistory.get (tabAt_fst_length_eq_toHistory_length s ▸ lpr.val) := by
  unfold companionOf
  rw [PathIn.nodeAt_rewind_eq_toHistory_get]
  simp

/-- Any repeat and companion are both loaded. -/
theorem companion_loaded : s ♥ t → (nodeAt s).isLoaded ∧ (nodeAt t).isLoaded := by
  intro s_comp_t
  unfold companion at s_comp_t
  rcases s_comp_t with ⟨lpr, h, t_def⟩
  constructor
  · simp_all only [nodeAt] -- takes care of s
    exact LoadedPathRepeat_rep_isLoaded lpr
  · subst t_def
    rw [nodeAt_companionOf_eq_toHistory_get_lpr_val]
    have := PathIn.toHistory_eq_Hist s
    simp at this
    have := lpr.2.2 lpr.val (by simp)
    convert this
    simp

/-- Successor relation plus back loops: ◃' (MB: page 26) -/
def ccEdge {X} {ctX : Tableau .nil X} (s t : PathIn ctX) : Prop :=
  s ◃ t  ∨  ∃ u, s ♥ u ∧ u ◃ t

notation pa:arg " ⋖ᶜᶜ " pb:arg => ccEdge pa pb

notation pa:arg " <ᶜᶜ " pb:arg => Relation.TransGen ccEdge pa pb

/-- We have: ⋖ᶜ = ⋖ ∪ ♥ -/
example : pa ⋖ᶜᶜ pb ↔ (pa ◃ pb) ∨ ∃ pc, pa ♥ pc ∧ pc ◃ pb := by
  simp_all [ccEdge]

def cEdge {X} {ctX : Tableau .nil X} (t s : PathIn ctX) : Prop :=
  (t ◃ s) ∨ t ♥ s

notation pa:arg " ⋖ᶜ " pb:arg => cEdge pa pb

notation pa:arg " <ᶜ " pb:arg => Relation.TransGen cEdge pa pb

/-- We have: ⋖ᶜ = ⋖ ∪ ♥ -/
example : pa ⋖ᶜ pb ↔ (pa ◃ pb) ∨ pa ♥ pb := by
  simp_all [cEdge]

/-! ## ≡_E and Clusters -/

-- TODO: how to define the equivalence relation given by E:
-- Use `EqvGen` from Mathlib or manual "both ways Relation.ReflTransGen"?

-- manual
def cEquiv {X} {tab : Tableau .nil X} (pa pb : PathIn tab) : Prop :=
    Relation.ReflTransGen cEdge pa pb
  ∧ Relation.ReflTransGen cEdge pb pa

notation t:arg " ≡_E " s:arg => cEquiv t s

theorem cEquiv.symm (s t : PathIn tab) : s ≡_E t ↔  t ≡_E s := by
  unfold cEquiv
  tauto

def clusterOf {tab : Tableau .nil X} (p : PathIn tab) := Quot.mk cEquiv p

-- better?
def E_equiv_alternative {tab : Tableau .nil X} (pa pb : PathIn tab) : Prop :=
  EqvGen cEdge pa pb

def clusterOf_alternative {tab : Tableau .nil X} (p : PathIn tab) :=
  Quot.mk E_equiv_alternative p

def simpler {X} {tab : Tableau .nil X}
  (s t : PathIn tab) : Prop := Relation.TransGen cEdge t s ∧ ¬ Relation.TransGen cEdge s t

notation s:arg " ⊏_c " t:arg => simpler s t

theorem eProp (tab : Tableau .nil X) :
    Equivalence (@cEquiv _ tab)
    ∧
    WellFounded (@simpler _ tab) := by
  constructor
  · constructor
    · intro _
      simp [cEquiv]
      exact Relation.ReflTransGen.refl
    · intro _ _
      simp [cEquiv]
      tauto
    · intro s u t
      simp [cEquiv]
      intro s_u u_s u_t t_u
      exact ⟨ Relation.ReflTransGen.trans s_u u_t
            , Relation.ReflTransGen.trans t_u u_s ⟩
  · constructor
    intro s
    -- need to show `Acc` but `induction s` does not work
    -- because we fixed Hist = .nil (in many defs above already)
    cases s
    case nil =>
      constructor
      intro t t_c_nil
      simp_all [simpler, cEdge]
      unfold simpler
      sorry
    case loc =>
      sorry
    case pdl =>
      sorry

theorem eProp2.a {tab : Tableau .nil X} (s t : PathIn tab) :
    s ◃ t → (t ⊏_c s) ∨ (t ≡_E s) := by
  simp_all [edge, cEdge, ccEdge, cEquiv, simpler, companion]
  intro t_childOf_s
  if Relation.TransGen cEdge t s
  then
    right
    constructor
    · apply Relation.TransGen.to_reflTransGen
      assumption
    · apply Relation.ReflTransGen.single
      simp [cEdge]
      left
      exact t_childOf_s
  else
    tauto

theorem eProp2.b {tab : Tableau .nil X} (s t : PathIn tab) : s ♥ t → t ≡_E s := by
  intro comp
  constructor
  · simp only [companion, companionOf, exists_prop] at comp
    rcases comp with ⟨lpr, _, t_def⟩
    subst t_def
    have := PathIn.rewind_le s ((tabAt_fst_length_eq_toHistory_length s ▸ lpr.val).succ)
    simp only [LE.le, instLEPathIn] at this
    exact Relation.ReflTransGen_or_left this
  · unfold cEdge
    apply Relation.ReflTransGen_or_right
    exact Relation.ReflTransGen.single comp

theorem eProp2.c_help {tab : Tableau .nil X} (s : PathIn tab) :
    (nodeAt s).isFree → ∀ t, s < t → t ⊏_c s := by
  intro s_free t t_path_s
  constructor
  · apply Relation.TransGen_or_left; exact t_path_s
  · unfold cEdge
    intro hyp
    -- alternative idea: induction t_path_s
    induction hyp -- ((t_s | t_comp_s) | blu)
    case single u t_u =>
      rcases t_u with (t_u | t_comp_u )
      · -- have := edge.isAsymm.1 _ _ t_u
        -- use that TransGen edge is asymm!
        sorry
      · have := (companion_loaded t_comp_u).2
        simp_all [TNode.isFree]
    case tail b s t_b b_s IH =>
      rcases  b_s with (b_s | b_comp_s)
      · have := edge.isAsymm.1 _ _ b_s -- not useful?
        sorry
      · have := (companion_loaded b_comp_s).2
        simp [TNode.isFree] at s_free
        simp_all

theorem eProp2.c {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s ◃ t → t ⊏_c s := by
  intro s_free t_childOf_s
  apply eProp2.c_help _ s_free
  apply Relation.TransGen.single; exact t_childOf_s

theorem eProp2.d {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isLoaded → (nodeAt t).isFree → s ◃ t → t ⊏_c s := by
  intro s_loaded t_free t_childOf_s
  constructor
  · apply Relation.TransGen.single; exact Or.inl t_childOf_s
  ·
    -- need some way to show that cEdge from free only goes down?
    sorry

-- Added for loadedDiamondPaths - change to <ᶜ later? replace the original eProp2.d with this?
theorem eProp2.d_cc {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isLoaded → (nodeAt t).isFree → s ⋖ᶜᶜ t → t ⊏_c s := by
  intro s_loaded t_free s_cc_t
  sorry


/-- ⊏_c is transitive -/
theorem eProp2.e {tab : Tableau .nil X} (s u t : PathIn tab) :
    t ⊏_c u  →  u ⊏_c s  →  t ⊏_c s := by
  rintro ⟨u_t, not_u_t⟩ ⟨s_u, _⟩
  constructor
  · exact Relation.TransGen.trans s_u u_t
  · intro t_s
    absurd not_u_t
    apply Relation.TransGen.trans t_s s_u

theorem eProp.f_helper {tab : Tableau .nil X} (s t : PathIn tab) :
    s ⋖ᶜᶜ t → Relation.ReflTransGen cEdge s t := by
  intro s_cc_t
  unfold cEdge
  rcases s_cc_t with s_c_t | ⟨u, s_comp_u, u_t⟩
  · exact Relation.ReflTransGen.single (Or.inl s_c_t)
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inr s_comp_u)) (Or.inl u_t)

theorem eProp2.f {tab : Tableau .nil X} (s t : PathIn tab) :
    (s ⋖ᶜᶜ t  →  ¬ s ≡_E t  →  t ⊏_c s) := by
  rintro s_cc_t s_nequiv_t
  constructor
  · rcases s_cc_t with s_c_t | ⟨u, s_comp_u, u_t⟩
    · exact Relation.TransGen.single (Or.inl s_c_t)
    · exact Relation.TransGen.tail (Relation.TransGen.single (Or.inr s_comp_u)) ((Or.inl u_t))
  · intro t_c_s
    absurd s_nequiv_t
    constructor
    · exact eProp.f_helper _ _ s_cc_t
    · exact Relation.TransGen.to_reflTransGen t_c_s

theorem eProp2 {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s ◃ t → (t ⊏_c s) ∨ (t ≡_E s))
  ∧ (s ♥ t → t ≡_E s)
  ∧ ((nodeAt s).isFree → edge s t → t ⊏_c s)
  ∧ ((nodeAt s).isLoaded → (nodeAt t).isFree → edge s t → t ⊏_c s)
  ∧ (t ⊏_c u → u ⊏_c s → t ⊏_c s)
  ∧ (s ⋖ᶜᶜ t → ¬ s ≡_E t → t ⊏_c s) :=
  ⟨eProp2.a _ _, eProp2.b _ _, eProp2.c _ _, eProp2.d _ _, eProp2.e _ _ _, eProp2.f _ _⟩

/-! ## Soundness -/

-- TODO: move to LocalTableau / should be possible to make it computable?
noncomputable def TNode.without : (LRO : TNode) → (naf : AnyNegFormula) → TNode
| ⟨L,R,O⟩, ⟨.normal f⟩  => ⟨L \ {~f}, R \ {~f}, O⟩
| ⟨L,R,O⟩, ⟨.loaded lf⟩ => if decide (NegLoadFormula_in_TNode (~'lf) ⟨L,R,O⟩) then ⟨L, R, none⟩  else ⟨L,R,O⟩

@[simp]
theorem TNode.without_normal_isFree_iff_isFree (LRO : TNode) :
    (LRO.without (~''(.normal φ))).isFree ↔ LRO.isFree := by
  rcases LRO with ⟨L, R, O⟩
  simp [TNode.without, isFree, isLoaded]
  aesop

theorem loadedDiamondPaths (α : Program) {X : TNode}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋ξ) (nodeAt t))
  (v_α_w : relate M α v w)
  (w_nξ : (M,w) ⊨ ~''ξ)
  : ∃ s : PathIn tab,
      t ⋖ᶜᶜ s
    ∧ ( ¬ (cEquiv s t) ∨ (AnyNegFormula_in_TNode (~''ξ) (nodeAt s)) )
    ∧ (M,w) ⊨ (nodeAt s)
    ∧ ((nodeAt s).without (~''ξ)).isFree := by
  -- Notes first take care of cases where rule is applied to non-loaded formula.
  -- For this, we need to distinguish what happens at `t`.
  rcases tabAt t with ⟨H, Y, ctY⟩
  cases ctY
  -- applying a local or a pdl rule or being a repeat?
  -- TODO: extra Lemmas / unclear how to get these:
  -- - every loaded node has a ccEdge successor.
  -- - eventually a rule must be applied to the loaded formula (at node t' in Notes)


  -- have := eProp2 tab -- used later!

  -- Notes then do induction on the complexity of α, but
  -- with the assumption that the rule is applied to the loaded formula!
  cases α
  case atom_prog a =>

    sorry
  -- TODO
  all_goals sorry

/-- Any node in a closed tableau is not satisfiable.
This is the main argument for soundness. -/
theorem tableauThenNotSat (tab : Tableau .nil Root) (t : PathIn tab) :
    ¬satisfiable (nodeAt t) :=
  by
  -- by induction on the well-founded strict partial order ⊏
  apply @WellFounded.induction _ simpler ((eProp tab).2 : _) _ t
  clear t
  intro t IH
  cases Classical.em (TNode.isFree $ nodeAt t)
  case inl t_is_free =>
    -- "First assume that t is free.""
    cases t_def : (tabAt t).2.2 -- Now consider what the tableau does at `t`.
    case rep lpr => -- Then t cannot be a LPR.
      exfalso
      have := LoadedPathRepeat_rep_isLoaded lpr
      simp_all [TNode.isFree, nodeAt]
    case loc lt next =>
      simp [nodeAt]
      rw [localTableauSat lt] -- using soundness of local tableaux here!
      simp
      intro Y Y_in
      -- We are given an end node, now need to define a path leading to it.
      let t_to_s : PathIn _ := (@PathIn.loc _ _ _ lt next Y_in .nil)
      let s : PathIn tab := t.append (t_def ▸ t_to_s)
      have t_s : t ◃ s := by
        unfold_let s
        simp [edge, children, children']
        use (t_def ▸ t_to_s)
        unfold_let t_to_s
        simp
        sorry
      have : Y = nodeAt s := by
        unfold_let s t_to_s; simp
        sorry
      rw [this]
      apply IH
      apply eProp2.c t _ t_is_free t_s
    case pdl Y r ctY =>
      simp [nodeAt]
      intro hyp
      have := pdlRuleSat r hyp -- using soundness of pdl rules here!
      absurd this
      -- As in `loc` case, it now remains to define a path leading to `Y`.
      let t_to_s : PathIn _ := (@PathIn.pdl _ _ _ ctY r .nil)
      let s : PathIn tab := t.append (t_def ▸ t_to_s)
      have t_s : t ◃ s := by
        unfold_let s
        sorry
      have : Y = nodeAt s := by
        unfold_let s
        sorry
      rw [this]
      apply IH
      apply eProp2.c t _ t_is_free t_s

  case inr not_free =>
    simp [TNode.isFree] at not_free
    -- have ⟨tH, ⟨L, R, O⟩, tt⟩ := tabAt t -- hmmm
    rcases O_def : (tabAt t).2.1.2.2 with _ | (nlf | nlf)
    -- "none" case is impossible because t is not free:
    · exfalso; simp_all [nodeAt, TNode.isLoaded]; split at not_free <;> simp_all
    -- two goals  remaining, but left and right case are axactly the same :-)
    · sorry -- FIXME replace with all_goals
    ·
      clear not_free
      rcases nlf with ⟨lf⟩
      -- Now we take apart the loaded formula to get all loaded boxes from the front at once ...
      rcases LoadFormula.exists_loadMulti lf with ⟨δ, α, φ, lf_def⟩
      -- Now assume for contradiction, that Λ(t) is satisfiable.
      rintro ⟨W,M,v,v_⟩
      have := v_ (~ unload (loadMulti δ α φ)) (by simp; right; aesop)
      rw [unload_loadMulti] at this
      -- ... so that we can do induction on δ for multiple `loadedDiamondPaths` applications.
      induction δ generalizing lf v t -- α -- amazing that this does not give a wrong motive ;-)
      · simp [evalBoxes] at this
        rcases this with ⟨w, v_α_w, not_w_φ⟩
        simp only [loadMulti, List.foldr_nil] at *
        have in_t : NegLoadFormula_in_TNode (~'⌊α⌋φ) (nodeAt t) := by
          simp_all [nodeAt, NegLoadFormula_in_TNode]; aesop
        have := loadedDiamondPaths α tab t v_ φ in_t v_α_w (not_w_φ)
        rcases this with ⟨s, t_cc_s, s_property, w_s, rest_s_free⟩
        -- We now claim that we have a contradiction with the IH because we left the cluster:
        absurd IH s ?_
        use W, M, w
        -- Remains to show that s is simpler than t, using eProp2 for that.
        rcases s_property with (notequi | not_af_in_s)
        · exact eProp2.f t s t_cc_s (by rw [cEquiv.symm]; exact notequi)
        · -- Follows because s is free, which we get from `loadedDiamondPaths`.
          simp only [TNode.without_normal_isFree_iff_isFree] at rest_s_free
          apply eProp2.d_cc t s ?_ rest_s_free t_cc_s
          unfold TNode.isLoaded
          cases in_t <;> aesop
      case cons β δ IH_inner =>
        -- We make one step with `loadedDiamondPaths` for β before we can apply IH.
        rw [boxes_first] at this
        simp at this
        rcases this with ⟨w, v_β_w, not_w_δαφ⟩
        have in_t : NegLoadFormula_in_TNode (~'⌊β⌋(⌊⌊δ⌋⌋⌊α⌋φ)) (nodeAt t) := by
          simp_all [nodeAt, NegLoadFormula_in_TNode]
          aesop
        have := loadedDiamondPaths β tab t v_ (⌊⌊δ⌋⌋⌊α⌋φ) in_t v_β_w
          (by simp [vDash,modelCanSemImplyAnyNegFormula]; exact not_w_δαφ)
        -- this gets us a node `s` to which we apply the **inner or outer ???** IH
        rcases this with ⟨s, t_cc_s, s_property, w_s, rest_s_free⟩
        rcases s_property with (notequi | not_af_in_s)
        · sorry
        · sorry

theorem correctness : ∀ LR : TNode, satisfiable LR → consistent LR := by
  intro LR
  contrapose
  unfold consistent
  unfold inconsistent
  simp only [not_nonempty_iff, not_isEmpty_iff, Nonempty.forall]
  intro hyp
  apply tableauThenNotSat hyp .nil

theorem soundTableau : ∀ φ, provable φ → ¬satisfiable ({~φ} : Finset Formula) := by
  intro φ prov
  rcases prov with ⟨tabl⟩|⟨tabl⟩
  exact tableauThenNotSat tabl .nil
  exact tableauThenNotSat tabl .nil

/-- All provable formulas are semantic tautologies.
See `tableauThenNotSat` for what the notes call soundness. -/
theorem soundness : ∀ φ, provable φ → tautology φ := by
  intro φ prov
  apply notsatisfnotThenTaut
  rw [← singletonSat_iff_sat]
  apply soundTableau
  exact prov
