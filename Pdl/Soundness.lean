import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Data.Prod.Lex

import Pdl.Tableau

/-! # Soundness (Section 6) -/

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
    simp_all [modelCanSemImplySequent]
    intro φ φ_in
    rcases φ_in with ((in_L | in_R) | φ_def)
    all_goals (apply w_; subst_eqs; try tauto)
    left; exact List.mem_of_mem_erase in_L
  case loadR =>
    use W, M, w
    simp_all [modelCanSemImplySequent]
    intro φ φ_in
    rcases φ_in with ((in_L | in_R) | φ_def)
    all_goals (apply w_; subst_eqs; try tauto)
    right; exact List.mem_of_mem_erase in_R
  case freeL =>
    use W, M, w
    simp_all [modelCanSemImplySequent]
    intro φ φ_in
    rcases φ_in with (φ_def | (in_L | in_R))
    all_goals (apply w_; tauto)
  case freeR =>
    use W, M, w
    simp_all [modelCanSemImplySequent]
    intro φ φ_in
    rcases φ_in with (φ_def | (in_L | in_R))
    all_goals (apply w_;  subst_eqs; try tauto)
  case modL L R a χ X_def x_basic =>
    subst X_def
    use W, M -- but not the same world!
    have := w_ (negUnload (~'⌊·a⌋χ))
    cases χ
    · simp [LoadFormula.unload] at *
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
    · simp [LoadFormula.unload] at *
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
    · simp [LoadFormula.unload] at *
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
    · simp [LoadFormula.unload] at *
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
inductive PathIn : ∀ {Hist X}, Tableau Hist X → Type
| nil : PathIn _
| loc {nrep nbas lt next Y} (Y_in : Y ∈ endNodesOf lt) (tail : PathIn (next Y Y_in))
    : PathIn (Tableau.loc nrep nbas lt next)
| pdl {nrep bas} {r : PdlRule X Y} {next} (tail : PathIn next)
    : PathIn (Tableau.pdl nrep bas r next)
deriving DecidableEq
-- TODO: which of the arguments above should be implicit???

def tabAt : PathIn tab → Σ H X, Tableau H X
| .nil => ⟨_,_,tab⟩
| .loc _ tail => tabAt tail
| .pdl tail => tabAt tail

def PathIn.append (p : PathIn tab) (q : PathIn (tabAt p).2.2) : PathIn tab := match p with
  | .nil => q
  | .loc Y_in tail => .loc Y_in (PathIn.append tail q)
  | .pdl tail => .pdl (PathIn.append tail q)

@[simp]
theorem append_eq_iff_eq (s : PathIn tab) p q : s.append p = s.append q ↔ p = q := by
  induction s <;> simp_all [PathIn.append]

@[simp]
theorem PathIn.eq_append_iff_other_eq_nil (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    p = p.append q ↔ q = nil := by
  induction p <;> cases tab
  all_goals
    unfold PathIn.append
    try simp at *
    aesop

theorem PathIn.nil_eq_append_iff_both_eq_nil (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    .nil = p.append q ↔ p = .nil ∧ q = .nil := by
  constructor
  · intro nil_eq
    cases p
    · simp_all
    case loc IH =>
      simp [append] at nil_eq
    case pdl IH =>
      simp [append] at nil_eq
  · rintro ⟨p_def, q_def⟩
    subst_eqs
    simp

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
theorem tabAt_loc :
    tabAt (.loc Y_in tail : PathIn (.loc nrep nbas lt next)) = tabAt tail := by simp [tabAt]

@[simp]
theorem tabAt_pdl :
    tabAt (.pdl tail : PathIn (.pdl nrep bas r next)) = tabAt tail := by simp [tabAt]

/-- Given a path to node `t`, this is its label Λ(t). -/
def nodeAt {H X} {tab : (Tableau H X)} (p : PathIn tab) : Sequent := (tabAt p).2.1

@[simp]
theorem nodeAt_nil {tab : Tableau Hist X} : nodeAt (.nil : PathIn tab) = X := by
  simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_loc :
  nodeAt (.loc Y_in tail : PathIn (.loc nrep nbas lt next)) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_pdl :
  nodeAt (.pdl tail : PathIn (.pdl nrep bas r next)) = nodeAt tail := by simp [nodeAt, tabAt]

@[simp]
theorem nodeAt_append (p : PathIn tab) (q : PathIn (tabAt p).2.2) :
    nodeAt (p.append q) = nodeAt q := by
  unfold nodeAt
  rw [tabAt_append p q]

@[simp]
def PathIn.head {tab : Tableau Hist X} (_ : PathIn tab) : Sequent := X

@[simp]
def PathIn.last (t : PathIn tab) : Sequent := (tabAt t).2.1

/-- The length of a path is the number of actual steps. -/
@[simp]
def PathIn.length : (t : PathIn tab) → ℕ
| .nil => 0
| .pdl tail => tail.length + 1
| .loc _ tail => tail.length + 1

theorem append_length {p : PathIn tab} q : (p.append q).length = p.length + q.length := by
  induction p <;> simp [PathIn.append]
  case loc IH => rw [IH]; linarith
  case pdl IH => rw [IH]; linarith

/-! ## Edge Relation -/

/-- Relation `s ⋖_ t` says `t` is one more step than `s`. Two cases, both defined via `append`. -/
def edge (s t : PathIn tab) : Prop :=
  ( ∃ Hist X nrep nbas lt next Y,
    ∃ (Y_in : Y ∈ endNodesOf lt)
      (h : tabAt s = ⟨Hist, X, (Tableau.loc nrep nbas lt next : Tableau _ X)⟩),
      t = s.append (h ▸ PathIn.loc Y_in .nil) )
  ∨
  ( ∃ Hist X nrep bas Y r,
    ∃ (next : Tableau (X :: Hist) Y)
      (h : tabAt s = ⟨Hist, X, Tableau.pdl nrep bas r next⟩),
      t = s.append (h ▸ PathIn.pdl .nil) )

/-- Notation ⋖_ for `edge` (because ⋖ is taken in Mathlib). -/
notation s:arg " ⋖_ " t:arg => edge s t

/-- Appending a one-step `loc` path is also a ⋖_ child.
When using this, this may be helpful:
`convert this; rw [← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]`.
-/
theorem edge_append_loc_nil {X} {Hist} {tab : Tableau X Hist} (s : PathIn tab)
    {lt : LocalTableau sX} (next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (sX :: sHist) Y)
    {Y : Sequent} (Y_in : Y ∈ endNodesOf lt)
    (tabAt_s_def : tabAt s = ⟨sHist, sX, Tableau.loc nrep nbas lt next⟩ ) :
    edge s (s.append (tabAt_s_def ▸ PathIn.loc Y_in .nil)) := by
  unfold edge
  left
  use sHist, sX, nrep, nbas, lt, next, (by assumption), Y_in
  constructor
  · rw [append_eq_iff_eq, ← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]
    rw [← tabAt_s_def]

/-- Appending a one-step `pdl` path is also a ⋖_ child. -/
@[simp]
theorem edge_append_pdl_nil (h : (tabAt s).2.2 = Tableau.pdl nrep bas r next) :
    edge s (s.append (h ▸ PathIn.pdl .nil)) := by
  simp only [edge, append_eq_iff_eq]
  right
  use (tabAt s).1, (tabAt s).2.1, nrep, bas, (by assumption), r, next
  constructor
  · rw [← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]
    rw [← h]

-- QUESTION: Does it actually have an effect to mark this with simp?
-- FIXME: implicit `tail` argument?
@[simp]
theorem nil_edge_loc_nil {X Y : Sequent} {Hist : List Sequent} {nrep nbas}
    {lt : LocalTableau X} {Y_in : Y ∈ endNodesOf lt}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    : (.nil : PathIn (.loc nrep nbas lt next)) ⋖_ (.loc Y_in .nil) := by
  left
  use Hist, X, nrep, nbas, lt, next, Y, Y_in, rfl
  simp_all
  rfl

-- same question and note as above
@[simp]
theorem nil_edge_pdl_nil {Hist} {X} {nrep} {bas} {Y} {r : PdlRule X Y}
    {next : Tableau (X :: Hist) Y}
    : (.nil : PathIn (.pdl nrep bas r next)) ⋖_ (.pdl .nil) := by
  right
  use Hist, X, nrep, bas, Y, r, next
  simp_all
  rfl

@[simp]
theorem loc_edge_loc_iff_edge {Y X} {lt : LocalTableau X} {Y_in : Y ∈ endNodesOf lt} {tail}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: tail) Y} {nrep nbas}
    {t s : PathIn (next Y Y_in)}
    : (.loc Y_in t : PathIn (.loc nrep nbas lt next)) ⋖_ (.loc Y_in s) ↔ (t ⋖_ s) := by
  constructor
  · rintro ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
           | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp [PathIn.append] at p_def
      exact p_def
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp [PathIn.append] at p_def
      exact p_def
  · intro t_s
    rcases t_s with ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
                    | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp [PathIn.append] at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp [PathIn.append] at p_def
      rw [p_def]
      rfl

@[simp]
theorem pdl_edge_pdl_iff_edge {X Y} {r : PdlRule X Y} {tail : List Sequent}
    {next : Tableau (X :: tail) Y} {nrep bas} {t s : PathIn next}
    : (.pdl t : PathIn (.pdl nrep bas r next)) ⋖_ (.pdl s) ↔ t ⋖_ s := by
  -- exact same proof as `loc_edge_loc_iff_edge` ;-)
  constructor
  · rintro ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
           | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp [PathIn.append] at p_def
      exact p_def
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp [PathIn.append] at p_def
      exact p_def
  · intro t_s
    rcases t_s with ( ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def, p_def⟩
                    | ⟨Hist, X, nrep, bas, Y, r, next, tab_def, p_def⟩ )
    · left
      use Hist, X, nrep, nbas, lt, next, Y, Y_in, tab_def
      simp [PathIn.append] at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp [PathIn.append] at p_def
      rw [p_def]
      rfl

/-- The root has no parent. Note this holds even when Hist ≠ []. -/
theorem not_edge_nil (tab : Tableau Hist X) (t : PathIn tab) : ¬ edge t .nil := by
  intro t_nil
  rcases t_nil with ( ⟨Hist, Z, nrep, nbas, lt, next, Y, Y_in, tabAt_s_def, t_def⟩
                    | ⟨Hist, Z, nrep, bas, Y, r, next, tabAt_s_def, t_def⟩ )
  all_goals
    rw [PathIn.nil_eq_append_iff_both_eq_nil] at t_def
    rcases t_def with ⟨t_nil, loc_eq_nil⟩
    subst t_nil
    rw [tabAt_nil] at tabAt_s_def
    rw [Sigma.mk.inj_iff] at tabAt_s_def
    rcases tabAt_s_def with ⟨nil_eq_Hist, hyp⟩
    subst nil_eq_Hist
    rw [heq_eq_eq, Sigma.mk.inj_iff] at hyp
    rcases hyp with ⟨X_eq_Z, hyp⟩
    subst X_eq_Z
    rw [heq_eq_eq] at hyp
    subst hyp
    simp_all

theorem nodeAt_loc_nil {H : List Sequent} {lt : LocalTableau X} {nrep nbas}
    (next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: H) Y) (Y_in : Y ∈ endNodesOf lt) :
    nodeAt (@PathIn.loc H X nrep nbas lt next Y Y_in .nil) = Y := by
  simp [nodeAt, tabAt]

theorem nodeAt_pdl_nil {nrep bas} (child : Tableau (X :: Hist) Y) (r : PdlRule X Y) :
    nodeAt (@PathIn.pdl Hist X Y nrep bas r child .nil) = Y := by
  simp [nodeAt, tabAt]

/-- The length of `edge`-related paths differs by one. -/
theorem length_succ_eq_length_of_edge {s t : PathIn tab} : s ⋖_ t → s.length + 1 = t.length := by
  intro s_t
  rcases s_t with ( ⟨Hist', Z', nrep, nbas, lt', next', Y', Y'_in, tabAt_s_def, t_def⟩
                  | ⟨Hist', Z', nrep, bas, Y', r', next', tabAt_s_def, t_def⟩ )
  · subst t_def
    rw [append_length, add_right_inj]
    have : 1 = (.loc Y'_in .nil : PathIn (Tableau.loc nrep nbas lt' next')).length := by simp
    convert this
    · simp_all only [PathIn.length, zero_add]
    · rw [tabAt_s_def]
    · rw [tabAt_s_def]
    · subst_eqs; simp_all only [PathIn.length, zero_add, heq_eq_eq, eqRec_heq_iff_heq]
  · subst t_def
    rw [append_length, add_right_inj]
    have : 1 = (.pdl .nil : PathIn (Tableau.pdl nrep bas r' next')).length := by simp
    convert this
    · simp_all only [PathIn.length, zero_add]
    · rw [tabAt_s_def]
    · rw [tabAt_s_def]
    · subst_eqs; simp_all only [PathIn.length, zero_add, heq_eq_eq, eqRec_heq_iff_heq]

theorem edge_then_length_lt {s t : PathIn tab} (s_t : s ⋖_ t) : s.length < t.length := by
  have := length_succ_eq_length_of_edge s_t
  linarith

def edge_natLT_relHom {Hist X tab} : RelHom (@edge Hist X tab) Nat.lt :=
  ⟨PathIn.length, edge_then_length_lt⟩

/-- The ⋖_ relation in a tableau is well-founded. -/
theorem edge.wellFounded : WellFounded (@edge Hist X tab) := by
  apply @RelHomClass.wellFounded _ Nat (@edge Hist X tab) Nat.lt _ _ _ edge_natLT_relHom
  have := instWellFoundedLTNat
  rcases this with ⟨nat_wf⟩
  convert nat_wf

instance edge.isAsymm : IsAsymm (PathIn tab) edge := by
  constructor
  apply WellFounded.asymmetric edge.wellFounded

/-- Enable "<" notation for transitive closure of ⋖_. -/
instance : LT (PathIn tab) := ⟨Relation.TransGen edge⟩

/-- Enable "≤" notation for reflexive transitive closure of ⋖_ -/
instance : LE (PathIn tab) := ⟨Relation.ReflTransGen edge⟩

/-- The "<" in a tableau is antisymmetric. -/
instance edge.TransGen_isAsymm : IsAsymm (PathIn tab) (Relation.TransGen edge) :=
  ⟨WellFounded.asymmetric (WellFounded.transGen wellFounded)⟩

/-- An induction principle for `PathIn` with a base case at the root of the tableau and
an induction step using the `edge` relation `⋖_`.

QUESTIONS:
- Do we need to add any of these attributes? @[induction_eliminator, elab_as_elim]
- Should it be a def or a theorem? (`motive` to `Prop` or to `Sort u`?)
-/
theorem PathIn.init_inductionOn t {motive : PathIn tab → Prop}
    (root : motive .nil)
    (step : (t : PathIn tab) → motive t → ∀ {s}, (t_s : t ⋖_ s) → motive s)
    : motive t := by
  induction tab -- works only if motive goes to Prop!
  case loc Hist X nrep nbas lt next IH =>
    cases t
    · assumption
    case loc Y nbas nrep Y_in rest =>
      specialize @IH Y Y_in rest (motive ∘ .loc Y_in)
      simp at IH
      apply IH <;> clear IH
      case root =>
        exact step nil root nil_edge_loc_nil
      case step =>
        intro t motive_t s t_edge_s
        apply @step (.loc Y_in t) motive_t (.loc Y_in s)
        rw [loc_edge_loc_iff_edge]
        exact t_edge_s
  case pdl Hist Y X nrep bas r next IH =>
    cases t
    · assumption
    case pdl rest =>
      specialize @IH rest (motive ∘ .pdl)
      simp at IH
      apply IH <;> clear IH
      case root =>
        exact step nil root nil_edge_pdl_nil
      case step =>
        intro t motive_t s t_edge_s
        apply @step (.pdl t) motive_t (.pdl s)
        rw [pdl_edge_pdl_iff_edge]
        exact t_edge_s
  case rep =>
    cases t -- path at rep must be nil
    exact root

theorem PathIn.nil_le_anything : PathIn.nil ≤ t := by
  induction t using PathIn.init_inductionOn
  case root =>
    exact Relation.ReflTransGen.refl
  case step nil_le_s u s_edge_u =>
    apply Relation.ReflTransGen.tail nil_le_s s_edge_u

theorem PathIn.loc_le_loc_of_le {t1 t2} (h : t1 ≤ t2) :
  @loc Hist X Y nrep nbas lt next Z_in t1 ≤ @ loc Hist X Y nrep nbas lt next Z_in t2 := by
  induction h
  · exact Relation.ReflTransGen.refl
  case tail s t _ s_t IH =>
    apply Relation.ReflTransGen.tail IH
    simp
    exact s_t

theorem PathIn.pdl_le_pdl_of_le {t1 t2} (h : t1 ≤ t2) :
  @pdl Hist X Y nrep bas r Z_in t1 ≤ @pdl Hist X Y nrep bas r Z_in t2 := by
  induction h
  · exact Relation.ReflTransGen.refl
  case tail s t _ s_t IH =>
    apply Relation.ReflTransGen.tail IH
    simp
    exact s_t

/-
-- not used YET ?
theorem PathIn.edge_leaf_inductionOn {Hist X} {tab : Tableau Hist X}
    (t : PathIn tab)
    {motive : PathIn tab → Prop}
    (leaf : ∀ {u}, (¬ ∃ s, u ⋖_ s) → motive u)
    (up : ∀ {u}, (∀ {s}, (u_s : u ⋖_ s) → motive s) → motive u)
    : motive t := by
  sorry
  -- try `induction tab` as for init_inductionOn
-/

/-! ## Alternative definitions of `edge` -/

/-- UNUSED definition of `edge` *recursively* by "going to the end" of the paths.
Note there are no mixed .loc and .pdl cases. -/
def edgeRec : PathIn tab → PathIn tab → Prop
| .nil, .nil => false
| .nil, .loc Y_in tail => tail = .nil
| .nil, .pdl tail => tail = .nil
| .pdl _ , .nil => false
| .pdl tail, .pdl tail2 => edgeRec tail tail2
| .loc _ _, .nil => false
| @PathIn.loc _ _ _ _ _ _ Y1 _ tail1,
  @PathIn.loc _ _ _ _ _ _ Y2 _ tail2 =>
  if h : Y1 = Y2 then edgeRec tail1 (h ▸ tail2) else false

/-! ## Path Properties (UNUSED?) -/

def PathIn.isLoaded (t : PathIn tab) : Prop :=
match t with
  | .nil => t.head.isLoaded
  | .pdl tail => t.head.isLoaded ∧ tail.isLoaded
  | .loc _ tail => t.head.isLoaded ∧ tail.isLoaded

/-- A path is critical iff the (M) rule is used on it. -/
def PathIn.isCritical (t : PathIn tab) : Prop :=
match t with
  | .nil => False
  | @PathIn.pdl _ _ _ _ _ (.modL _ _) _ _ => True
  | @PathIn.pdl _ _ _ _ _ (.modR _ _) _ _ => True
  | .pdl tail => tail.isCritical
  | .loc _ tail => tail.isCritical

/-! ## From Path to History -/

/-- Convert a path to a History.
Does not include the last node.
The history of `.nil` is `[]` because this will not go into `Hist`. -/
def PathIn.toHistory {tab : Tableau Hist X} : (t : PathIn tab) → History
| .nil => []
| .pdl tail => tail.toHistory ++ [X]
| .loc _ tail => tail.toHistory ++ [X]

/-- Convert a path to a list of nodes. Reverse of the history and does include the last node.
The list of `.nil` is `[X]`. -/
def PathIn.toList {tab : Tableau Hist X} : (t : PathIn tab) → List Sequent
| .nil => [X]
| .pdl tail => X :: tail.toList
| .loc _ tail => X :: tail.toList

/-- A path gives the same list of nodes as the history of its last node. -/
theorem PathIn.toHistory_eq_Hist {tab : Tableau Hist X} (t : PathIn tab) :
    t.toHistory ++ Hist = (tabAt t).1 := by
  induction tab
  all_goals
    cases t <;> simp_all [tabAt, PathIn.toHistory]

-- TODO generalise [] to Hist with + Hist.length ??
theorem tabAt_fst_length_eq_toHistory_length {tab : Tableau [] X} (s : PathIn tab) :
    (tabAt s).fst.length = s.toHistory.length := by
  have := PathIn.toHistory_eq_Hist s
  rw [← this]
  simp

@[simp]
theorem PathIn.loc_length_eq {X Y Hist} {nrep nbas} {lt : LocalTableau X}
    {next : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    Y_in (tail : PathIn (next Y Y_in))
    : (loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length = tail.toHistory.length + 1 := by
  simp [PathIn.toHistory]

@[simp]
theorem PathIn.pdl_length_eq {X Y Hist} {nrep bas} {next : Tableau (X :: Hist) Y} {r}
    (tail : PathIn next)
    : (pdl tail : PathIn (.pdl nrep bas r next)).toHistory.length = tail.toHistory.length + 1 := by
  simp [PathIn.toHistory]

/-- Prefix of a path, taking only the first `k` steps. -/
def PathIn.prefix {tab : Tableau Hist X} : (t : PathIn tab) → (k : Fin (t.length + 1)) → PathIn tab
| .nil, _ => .nil
| .pdl tail, k => Fin.cases (.nil) (fun j => .pdl (tail.prefix j)) k
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

/-! ## Path Rewinding -/

/-- Rewinding a path, removing the last `k` steps. Cannot go into Hist.
Used to go to the companion of a repeat. Returns `.nil` when `k` is the length of the whole path.
We use +1 in the type because `rewind 0` is always possible, even with history `[]`.
Defined using Fin.lastCases. -/
def PathIn.rewind : (t : PathIn tab) → (k : Fin (t.toHistory.length + 1)) → PathIn tab
| .nil, _ => .nil
| .loc Y_in tail, k => Fin.lastCases (.nil)
    (PathIn.loc Y_in ∘ tail.rewind ∘ Fin.cast (loc_length_eq Y_in tail)) k
| .pdl tail, k => Fin.lastCases (.nil)
    (PathIn.pdl ∘ tail.rewind ∘ Fin.cast (pdl_length_eq tail)) k

/-- Rewinding 0 steps does nothing. -/
theorem PathIn.rewind_zero {tab : Tableau Hist X} {p : PathIn tab} : p.rewind 0 = p := by
  induction p <;> simp only [rewind]
  case loc Hist0 X0 nrep nbas lt next Y Y_in tail IH =>
    by_cases 0 = Fin.last (.loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length
    case pos hyp =>
      rw [PathIn.loc_length_eq] at hyp
      have := @Fin.last_pos tail.toHistory.length
      omega
    case neg _ =>
      simp_all [Fin.lastCases, Fin.reverseInduction]
  case pdl Y Z X0 nrep bas r next tail IH =>
    by_cases 0 = Fin.last (.pdl tail : PathIn (.pdl nrep bas r next)).toHistory.length
    case pos hyp =>
      rw [PathIn.pdl_length_eq] at hyp
      have := @Fin.last_pos tail.toHistory.length
      omega
    case neg _ =>
      simp_all [Fin.lastCases, Fin.reverseInduction]

theorem PathIn.rewind_le (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) : t.rewind k ≤ t := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case loc Z nbas nrep Z_in tail =>
      specialize IH Z Z_in tail
      cases k using Fin.lastCases
      case last =>
        rw [Fin.lastCases_last]
        exact PathIn.nil_le_anything
      case cast j =>
        simp only [Fin.lastCases_castSucc, Function.comp_apply]
        apply PathIn.loc_le_loc_of_le
        apply IH
  case pdl =>
    cases t <;> simp only [rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case pdl rest Y Z r tab IH bas nrep tail =>
      specialize IH tail
      cases k using Fin.lastCases
      case last =>
        rw [Fin.lastCases_last]
        exact PathIn.nil_le_anything
      case cast j =>
        simp only [Fin.lastCases_castSucc, Function.comp_apply]
        apply PathIn.pdl_le_pdl_of_le
        apply IH
  case rep =>
    cases t
    simp only [rewind]
    exact Relation.ReflTransGen.refl

/-- If we rewind by `k > 0` steps then the length goes down. -/
theorem PathIn.rewind_lt_of_gt_zero {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) (k_gt_zero : k > 0)
    : (t.rewind k).length < t.length := by
  induction t
  · exfalso
    rcases k with ⟨k, k_prop⟩
    simp only [toHistory, List.length_nil, zero_add, Nat.lt_one_iff] at k_prop
    subst k_prop
    simp_all
  case loc H Z Y ltX next Y_in tail IH =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH ⟨j, by rcases j with ⟨j,j_lt⟩; rw [loc_length_eq] at j_lt; simp_all⟩ k_gt_zero
        simp only [rewind, Fin.lastCases_castSucc, Function.comp_apply, length,
          add_lt_add_iff_right]
        convert IH <;> simp [Fin.heq_ext_iff _]
  case pdl Z Y H next r tail IH =>
    cases k using Fin.lastCases
    · simp [PathIn.toHistory, PathIn.rewind] at *
    case cast j =>
      specialize IH ⟨j, by rcases j with ⟨j,j_lt⟩; rw [pdl_length_eq] at j_lt; simp_all⟩ k_gt_zero
      simp only [rewind, Fin.lastCases_castSucc, Function.comp_apply, length, add_lt_add_iff_right]
      convert IH <;> simp [Fin.heq_ext_iff _]

/-- The node we get from rewinding `k` steps is element `k+1` in the history. -/
theorem PathIn.nodeAt_rewind_eq_toHistory_get {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1))
    : nodeAt (t.rewind k) = (nodeAt t :: t.toHistory).get k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toHistory, PathIn.rewind]
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH Z Z_in tail
        simp_all only [List.get_eq_getElem, List.length_cons, rewind, toHistory,
          Fin.lastCases_castSucc, Function.comp_apply, nodeAt_loc, Fin.coe_cast, Fin.coe_castSucc]
        rcases j with ⟨j,j_lt⟩
        rw [loc_length_eq] at j_lt
        have := @List.getElem_append _ (nodeAt tail :: tail.toHistory) [Y] j ?_
        · simp only [List.cons_append, List.length_cons, List.getElem_singleton] at this
          simp_all only [dite_true]
        · simp only [List.cons_append, List.length_cons, List.length_append]
          exact Nat.lt_add_right 1 j_lt
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toHistory, PathIn.rewind]
    case pdl rest Z Y _ _ r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      · simp [PathIn.toHistory, PathIn.rewind] at *
      case cast j =>
        specialize IH tail
        simp only [List.get_eq_getElem, List.length_cons, toHistory, nodeAt_pdl] at *
        simp_all only [rewind, Fin.lastCases_castSucc, Function.comp_apply, nodeAt_pdl,
          Fin.coe_cast, Fin.coe_castSucc]
        rcases j with ⟨j,j_lt⟩
        rw [pdl_length_eq] at j_lt
        have := @List.getElem_append _ (nodeAt tail :: tail.toHistory) [Z] j ?_
        · simp only [List.cons_append, List.length_cons, List.getElem_singleton] at this
          rw [this]
          simp_all
        · simp only [List.cons_append, List.length_cons, List.length_append, List.length_singleton]
          exact Nat.lt_add_right 1 j_lt
  case rep =>
    cases t
    simp_all [PathIn.toHistory, PathIn.rewind]

/-! ## Companion, cEdge, etc. -/

/-- To get the companion of an LPR node we go as many steps back as the LPR says. -/
-- TODO DOCUMENTATION: why is there a `succ` here?
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

theorem nodeAt_companionOf_setEq {tab : Tableau .nil X} (s : PathIn tab) lpr
    (h : (tabAt s).2.2 = Tableau.rep lpr)
    : (nodeAt (companionOf s lpr h)).setEqTo (nodeAt s) := by
  rcases lpr with ⟨k, k_same, _⟩
  unfold companionOf
  rw [PathIn.nodeAt_rewind_eq_toHistory_get]
  unfold nodeAt
  simp only [List.get_eq_getElem, List.length_cons, Fin.val_succ, List.getElem_cons_succ]
  convert k_same
  simp only [List.get_eq_getElem]
  have := PathIn.toHistory_eq_Hist s
  have : (tabAt_fst_length_eq_toHistory_length s ▸ k).val = k.val := by
    apply Fin.val_eq_val_of_heq
    simp
  simp_all

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

/-- The companion is strictly before the the repeat. -/
theorem companionOf_length_lt_length {t : PathIn tab} lpr h :
    (companionOf t lpr h).length < t.length := by
  unfold companionOf
  apply PathIn.rewind_lt_of_gt_zero
  simp

def cEdge {X} {ctX : Tableau .nil X} (s t : PathIn ctX) : Prop :=
  (s ⋖_ t) ∨ s ♥ t

notation pa:arg " ◃ " pb:arg => cEdge pa pb

notation pa:arg " ◃⁺ " pb:arg => Relation.TransGen cEdge pa pb

notation pa:arg " ◃* " pb:arg => Relation.ReflTransGen cEdge pa pb

/-- We have: ◃ = ⋖_ ∪ ♥ -/
example : pa ◃ pb ↔ (pa ⋖_ pb) ∨ pa ♥ pb := by
  simp_all [cEdge]

/-! ## ≡ᶜ and Clusters -/

/-- Nodes are c-equivalent iff there are `◃` paths both ways.
Note that this is not a closure, so we do not want `Relation.EqvGen` here. -/
def cEquiv {X} {tab : Tableau .nil X} (s t : PathIn tab) : Prop :=
  s ◃* t  ∧  t ◃* s

notation t:arg " ≡ᶜ " s:arg => cEquiv t s

/-- ≡ᶜ is symmetric. -/
theorem cEquiv.symm (s t : PathIn tab) : s ≡ᶜ t ↔ t ≡ᶜ s := by
  unfold cEquiv
  tauto

def clusterOf {X} {tab : Tableau .nil X} (p : PathIn tab) :=
  Quot.mk cEquiv p

/-- We have `before s t` iff there is a path from s to t but not from t to s.
This means the cluster of `s` comes before the cluster of `t` in `tab`.
NB: The notes use ◃* here but we use ◃⁺. The definitions are equivalent. -/
def before {X} {tab : Tableau .nil X} (s t : PathIn tab) : Prop :=
  s ◃⁺ t  ∧  ¬ t ◃⁺ s

/-- `s <ᶜ t` means there is a ◃-path from `s` to `t` but not from `t` to `s`.
This means `t` is *simpler* to deal with first. -/
notation s:arg " <ᶜ " t:arg => before s t

-- Needed, and tricky to show?
theorem PathIn.before_leaf_inductionOn {tab : Tableau .nil X} (t : PathIn tab) {motive : PathIn tab → Prop}
    (leaf : ∀ {u}, (nodeAt u).isFree → (¬ ∃ s, u ⋖_ s) → motive u)
    (up : ∀ {u}, (∀ {s}, (u_s : u <ᶜ s) → motive s) → motive u)
    : motive t := by
  sorry

/-- ≣ᶜ is an equivalence relation and <ᶜ is well-founded and converse well-founded.
The converse well-founded is what we really need for induction proofs. -/
theorem eProp {X} (tab : Tableau .nil X) :
    Equivalence (@cEquiv X tab)
    ∧
    WellFounded (@before X tab)
    ∧
    WellFounded (flip (@before X tab))
     := by
  refine ⟨?_, ?_, ?_⟩
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
  · sorry -- not important?
  · constructor
    intro s
    -- Here we cannot do `induction s` because we fixed Hist = .nil
    -- in `companionOf`. Hence, use our own induction principle.
    induction s using PathIn.before_leaf_inductionOn
    case leaf l l_isFree l_is_leaf =>
      constructor
      intro k ⟨l_k, not_k_l⟩
      exfalso
      rw [Relation.TransGen.head'_iff] at l_k
      rcases l_k with ⟨j, l_j, _⟩
      cases l_j
      · absurd l_is_leaf
        use j
      case inr ll =>
        have := companion_loaded  ll
        simp_all [Sequent.isLoaded, Sequent.isFree]
    case up l IH =>
      constructor
      intro k l_k
      simp [flip] at *
      apply IH
      exact l_k

-- Unused?
theorem eProp2.a {tab : Tableau .nil X} (s t : PathIn tab) :
    s ⋖_ t → (s <ᶜ t) ∨ (t ≡ᶜ s) := by
  simp_all only [edge, cEdge, cEquiv, flip, before, companion]
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
    rcases t_childOf_s with ( ⟨Hist, Z, nrep, nbas, lt, next, Y, Y_in, tabAt_s_def, t_def⟩
                            | ⟨Hist, Z, nrep, bas, Y, r, next, tabAt_s_def, def_t_append⟩ )
    all_goals
      left
      simp_all
      unfold cEdge
      apply Relation.TransGen.single
      left
      unfold edge
    · left; use Hist, Z, nrep, nbas, lt, next, Y, Y_in, tabAt_s_def
    · right; use Hist, Z, nrep, bas, Y, r, next, tabAt_s_def

-- Unused?
theorem eProp2.b {tab : Tableau .nil X} (s t : PathIn tab) : s ♥ t → t ≡ᶜ s := by
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

-- TODO IMPORTANT
theorem eProp2.c_help {tab : Tableau .nil X} (s : PathIn tab) :
    (nodeAt s).isFree → ∀ t, s < t → s <ᶜ t := by
  intro s_free t t_path_s
  constructor
  · apply Relation.TransGen_or_left; exact t_path_s
  · unfold cEdge
    intro hyp
    -- alternative idea: induction t_path_s
    induction hyp -- ((t_s | t_comp_s) | blu)
    case single u t_u =>
      rcases t_u with (t_u | t_comp_u )
      · absurd edge.TransGen_isAsymm.1 _ _ t_path_s
        exact Relation.TransGen.single t_u
      · have := (companion_loaded t_comp_u).2
        simp_all [Sequent.isFree]
    case tail b s t_b b_s IH =>
      rcases  b_s with (b_s | b_comp_s)
      · apply IH
        · -- PROBLEM: we do not have that `b` is free.
          sorry
        · unfold LT.lt instLTPathIn
          simp
          exact Relation.TransGen.head b_s t_path_s
      · have := (companion_loaded b_comp_s).2
        simp [Sequent.isFree] at s_free
        simp_all

theorem eProp2.c {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s ⋖_ t → s <ᶜ t := by
  intro s_free t_childOf_s
  apply eProp2.c_help _ s_free
  apply Relation.TransGen.single; exact t_childOf_s

/-- A free node and a loaded node cannot be ≡ᶜ equivalent. -/
theorem not_cEquiv_of_free_loaded (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded: (nodeAt t).isLoaded) : ¬ s ≡ᶜ t := by
  rintro ⟨s_t, t_s⟩
  induction s_t using Relation.ReflTransGen.head_induction_on
  · simp [Sequent.isFree] at *
    simp_all
  case head u v u_v v_t IH =>
    cases u_v -- normal edge or companion edge?
    case inl u_v =>
      rcases eProp2.c u v s_free u_v with ⟨-, not_v_u⟩
      absurd not_v_u
      have := Relation.ReflTransGen.trans v_t t_s
      rw [@Relation.reflTransGen_iff_eq_or_transGen] at this
      cases this
      · simp_all
      · assumption
    case inr u_comp_v =>
      have := companion_loaded u_comp_v
      simp_all [Sequent.isFree]

-- Unused?
theorem eProp2.d {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isLoaded → (nodeAt t).isFree → s ⋖_ t → s <ᶜ t := by
  intro s_loaded t_free t_childOf_s
  constructor
  · apply Relation.TransGen.single; exact Or.inl t_childOf_s
  · intro t_s
    absurd not_cEquiv_of_free_loaded _ _ t_free s_loaded
    constructor
    · apply Relation.TransGen.to_reflTransGen; assumption
    · apply Relation.ReflTransGen.single
      left
      assumption

-- Added for loadedDiamondPaths
theorem eProp2.d_help {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt t).isLoaded → (nodeAt s).isFree → t ◃⁺ s → ¬ (s ◃⁺ t) := by
  intro t_loaded s_free t_s
  intro s_t
  absurd not_cEquiv_of_free_loaded _ _ s_free t_loaded
  constructor <;> apply Relation.TransGen.to_reflTransGen <;> assumption

-- Unused?
/-- <ᶜ is transitive -/
theorem eProp2.e {tab : Tableau .nil X} (s u t : PathIn tab) :
    s <ᶜ u  →  u <ᶜ t  →  s <ᶜ t := by
  rintro ⟨s_u, _⟩ ⟨u_t, not_u_t⟩
  constructor
  · exact Relation.TransGen.trans s_u u_t
  · intro t_s
    absurd not_u_t
    apply Relation.TransGen.trans t_s s_u

theorem eProp2.f {tab : Tableau .nil X} (s t : PathIn tab) :
    t ◃⁺ s  →  ¬ t ≡ᶜ s  →  t <ᶜ s := by
  rintro s_c_t s_nequiv_t
  constructor
  · exact s_c_t
  · intro t_c_s
    absurd s_nequiv_t
    constructor
    · exact Relation.TransGen.to_reflTransGen s_c_t
    · exact Relation.TransGen.to_reflTransGen t_c_s

-- TODO: add in notes?
theorem eProp2.f_tweak {tab : Tableau .nil X} (s u t : PathIn tab) :
    s ◃⁺ u  →  u ◃⁺ t  →  ¬ t ≡ᶜ u → ¬ t ≡ᶜ s := by
  intro s_u u_t not_t_u
  intro t_s
  absurd not_t_u
  constructor
  · apply @Relation.ReflTransGen.trans _ _ _ _ _ t_s.1
    exact Relation.TransGen.to_reflTransGen s_u
  · exact Relation.TransGen.to_reflTransGen u_t

theorem eProp2.g {tab : Tableau .nil X} (s t : PathIn tab) :
    (s <ᶜ t → ¬ s ≡ᶜ t) := by
  intro s_lt_t
  rintro ⟨-, t_to_s⟩
  rcases s_lt_t with ⟨s_steps_t', not_t_steps_s⟩
  absurd not_t_steps_s
  by_cases s = t
  · simp_all
  · rw [@Relation.reflTransGen_iff_eq_or_transGen] at t_to_s
    simp_all

theorem eProp2.h {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s <ᶜ u  →  s ≡ᶜ t  →  t <ᶜ u) := by
  rintro s_c_y s_equiv_t
  rcases s_c_y with ⟨s_u, not_u_s⟩
  rcases s_equiv_t with ⟨-, t_to_s⟩
  constructor
  · exact Relation.TransGen.trans_right t_to_s s_u
  · intro u_to_t
    absurd not_u_s
    exact Relation.TransGen.trans_left u_to_t t_to_s

theorem eProp2 {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s ⋖_ t → (s <ᶜ t) ∨ (t ≡ᶜ s))
  ∧ (s ♥ t → t ≡ᶜ s)
  ∧ ((nodeAt s).isFree → s ⋖_ t → s <ᶜ t)
  ∧ ((nodeAt s).isLoaded → (nodeAt t).isFree → s ⋖_ t → s <ᶜ t)
  ∧ (t <ᶜ u → u <ᶜ s → t <ᶜ s)
  ∧ (t ◃⁺ s  →  ¬ t ≡ᶜ s  →  t <ᶜ s)
  ∧ (s <ᶜ t → ¬ s ≡ᶜ t)
  ∧ (s <ᶜ u  →  s ≡ᶜ t  →  t <ᶜ u)
  :=
  ⟨eProp2.a _ _, eProp2.b _ _, eProp2.c _ _, eProp2.d _ _
  , eProp2.e _ _ _, eProp2.f _ _, eProp2.g s t, eProp2.h s u t⟩

/-! ## Soundness -/

/-- Helper to deal with local tableau in `loadedDiamondPaths`. -/
theorem localLoadedDiamond (α : Program) {X : Sequent}
  (ltab : LocalTableau X)
  {W} {M : KripkeModel W} {v w : W}
  (v_α_w : relate M α v w)
  (v_t : (M,v) ⊨ X)
  (ξ : AnyFormula)
  {side : Side}
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side X)
  (w_nξ : (M,w) ⊨ ~''ξ)
  : ∃ Y ∈ endNodesOf ltab, (M,v) ⊨ Y ∧
    (   ( Y.isFree ) -- means we left cluster
      ∨ ( ∃ (F : List Formula) (γ : List Program),
            ( (~''(AnyFormula.loadBoxes γ ξ)).in_side side Y
            ∧ relateSeq M γ v w
            ∧ (M,v) ⊨ F
            ∧ (F,γ) ∈ H α -- "F,γ is a result from unfolding α"
            ∧ (Y.without (~''(AnyFormula.loadBoxes γ ξ))).isFree
            )
        )
    ) := by
  induction ltab generalizing α
  case byLocalRule X B lra next IH =>
    rcases X with ⟨L,R,O⟩

    -- Soundness and invertibility of the local rule:
    have locRulTru := @localRuleTruth (L,R,O) _ lra W M

    -- We distinguish which rule was applied.
    rcases lra with ⟨Lcond, Rcond, Ocond, r, precons⟩
    rename_i resNodes B_def_apply_r_LRO
    cases r

    -- All rules not affecting the loaded formula are easy to deal with.
    case oneSidedL resNodes orule =>
      simp_all only [applyLocalRule, List.empty_eq, List.diff_nil, List.map_map, List.mem_map,
        Function.comp_apply, List.append_nil, Olf.change_none_none, modelCanSemImplyList,
        forall_exists_index, exists_exists_and_eq_and, endNodesOf.eq_1, List.mem_flatten,
        List.mem_attach, true_and, Subtype.exists] -- uses locRulTru
      rcases v_t with ⟨res, res_in, v_⟩
      specialize IH _ res ⟨res_in, rfl⟩ α v_α_w v_
        (by cases side <;> simp_all [AnyNegFormula.in_side])
      rcases IH with ⟨Y, Y_in, v_Y⟩
      use Y
      simp_all only [List.empty_eq, List.nil_subperm, Option.instHasSubsetOption, and_self,
        and_true]
      use endNodesOf (next (L.diff Lcond ++ res, R, O) (by aesop))
      simp_all only [and_true]
      use (L.diff Lcond ++ res, R, O)
      simp_all only [exists_prop, and_true]
      use res
    case oneSidedR resNodes orule =>
      -- analogous to oneSidedL
      simp_all only [applyLocalRule, List.empty_eq, List.diff_nil, List.map_map, List.mem_map,
        Function.comp_apply, List.append_nil, Olf.change_none_none, modelCanSemImplyList,
        forall_exists_index, exists_exists_and_eq_and, endNodesOf.eq_1, List.mem_flatten,
        List.mem_attach, true_and, Subtype.exists] -- uses locRulTru
      rcases v_t with ⟨res, res_in, v_⟩
      specialize IH _ res ⟨res_in, rfl⟩ α v_α_w v_
        (by cases side <;> simp_all [AnyNegFormula.in_side])
      rcases IH with ⟨Y, Y_in, v_Y⟩
      use Y
      simp_all only [List.empty_eq, List.nil_subperm, Option.instHasSubsetOption, and_self,
        and_true]
      use endNodesOf (next (L, R.diff Rcond ++ res, O) (by aesop))
      simp_all only [and_true]
      use (L, R.diff Rcond ++ res, O)
      simp_all only [exists_prop, and_true]
      use res
    case LRnegL φ =>
      simp_all
    case LRnegR =>
      simp_all

    case loadedL outputs χ lrule =>
      -- Instead of localRuleTruth ...
      clear locRulTru
      -- here we use use `existsDiamondH` to imitate the relation v_α_w
      have from_H := @existsDiamondH W M α _ _ v_α_w
      rcases from_H with ⟨⟨F,δ⟩, _in_H, v_F, v_δ_w⟩
      simp at *
      cases lrule -- dia or dia' annoyance ;-)
      case dia α' χ' α'_not_atomic =>
        -- The rule application has its own α' that must be α, and χ' must be ξ.
        have ⟨χ_eq_ξ,α_same⟩ : α = α' ∧ χ' = ξ := by
          simp [AnyNegFormula.in_side] at negLoad_in
          have := precons.2.2
          simp at this
          rw [← this] at negLoad_in
          cases side <;> aesop
        subst α_same
        subst χ_eq_ξ
        -- Now we have that this F,δ pair is also used for one result in `B`:
        have claim : (L ++ F, R, some (Sum.inl (~'⌊⌊δ⌋⌋χ'))) ∈ B := by
          simp [applyLocalRule, unfoldDiamondLoaded, YsetLoad] at B_def_apply_r_LRO
          simp_all; use F, δ

        -- PROBLEM: Cannot apply IH to node where α is gone and replaced by its unfolding.
        -- Do we need an induction on δ here? And strengthen IH to work for other programs!
        refine ⟨?_Y, ⟨ ⟨_, ⟨(L ++ F, R, some (Sum.inl (~'⌊⌊δ⌋⌋χ'))), claim, rfl⟩ , ?_⟩ , ?_⟩⟩
        · sorry -- Do not know yet which end node to pick!
        · sorry
        · sorry

      case dia' α' φ α'_not_atomic => -- analogous to `dia` case?
        sorry

    case loadedR =>
      -- should be analogous to loadedL, but depending on `side`?
      sorry

  case sim X X_isBasic =>
    -- If `X` is simple then `α` must be atomic.
    have : α.isAtomic := by
      rw [Program.isAtomic_iff]
      rcases X with ⟨L,R,O⟩
      unfold AnyNegFormula.in_side at negLoad_in
      rcases O with _|⟨lf|lf⟩
      · cases side <;> simp_all [Program.isAtomic]
      all_goals
        unfold isBasic at *
        simp at X_isBasic
        specialize X_isBasic (~lf.1.unload)
        simp at X_isBasic
        cases side <;> simp [AnyFormula.unload] at negLoad_in
        subst negLoad_in
        cases ξ
        all_goals
          simp_all [LoadFormula.unload]
          cases α <;> simp_all
    rw [Program.isAtomic_iff] at this
    rcases this with ⟨a, α_def⟩
    subst α_def
    -- We can use X itself as the end node.
    refine ⟨X, ?_, v_t, Or.inr ⟨[], [·a], negLoad_in,  ?_,  ?_,  ?_⟩ ⟩ <;> simp_all [H]
    exact Sequent.without_loaded_in_side_isFree X (⌊·a⌋ξ) side negLoad_in

lemma Sequent.isLoaded_of_negAnyFormula_loaded {α ξ side} {X : Sequent}
    (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋ξ))).in_side side X)
    : X.isLoaded := by
  unfold AnyNegFormula.in_side at negLoad_in
  rcases X with ⟨L,R,O⟩
  rcases O with _|⟨lf|lf⟩
  · cases side <;> simp_all [Program.isAtomic]
  all_goals
    cases side <;> simp [AnyFormula.unload] at negLoad_in
    subst negLoad_in
    cases ξ
    all_goals
      simp_all [isLoaded]

-- Some helper lemmas about `List` and `Vector`, move elsewhere?

lemma List.nonempty_drop_sub_succ (δ_not_empty : δ ≠ []) (k : Fin δ.length) :
  (List.drop (k.val + 1) δ).length + 1 = δ.length.succ - (k.val + 1) :=
  by
  simp
  have : ∀ n, n ≠ 0 → (k.val < n) → n - (k.val + 1) + 1 = n - k.val := by
    intro n n_no_zero k_lt_n
    induction n <;> simp_all
    omega
  apply this <;> aesop

lemma Vector.my_cast_head (n m : Nat) (v : List.Vector α n.succ) (h : n = m) :
    (h ▸ v).head = v.head := by subst h; simp

lemma Vector.my_cast_eq_val_head (n m : Nat) (v : List.Vector α n.succ) (h : n = m) h2 :
    (h ▸ v).head = v.1.head h2 := by
  rcases v with ⟨l,l_prop⟩
  rw [Vector.my_cast_head]
  induction l <;> simp_all
  · exfalso; aesop
  · aesop

lemma Vector.my_cast_toList (n m : ℕ) (t : List α) ht (h : n = m) :
    t = List.Vector.toList (h ▸ (⟨t, ht⟩ : List.Vector α n)) := by subst h; simp

lemma aux_simplify_vector_type {α} {q p : ℕ} (t : List α) h :
    let help (n m : ℕ) : (n + 1 + 1 - (m + 1 + 1)) = n + 1 - (m + 1) := by omega
    (⟨t, h⟩ : List.Vector α (q + 1 + 1 - (p + 1 + 1)))
    = (help q p) ▸ ⟨t, by simp at h; simp; exact h⟩ := by
    apply List.Vector.eq
    simp
    apply Vector.my_cast_toList

lemma Vector.my_drop_succ_cons {α} {m n : ℕ} (x : α) (t : List α) h (hyp : m < n) :
    let help : (n + 1 - (m + 1)) = n - m := by omega
    List.Vector.drop (m + 1) (⟨x :: t, h⟩ : List.Vector α n.succ)
    = help ▸ List.Vector.drop m ⟨t, by simp at h; exact h⟩ := by
    induction m generalizing t n h x with
    | zero => simp [List.Vector.drop]
    | succ p ih =>
      cases t with
      | nil => simp at h; omega
      | cons head tail =>
        cases n with
        | zero => omega
        | succ q =>
        simp [List.Vector.drop] at ih
        simp [List.Vector.drop]
        rw [aux_simplify_vector_type]

lemma Vector.get_succ_eq_head_drop {v : List.Vector α n.succ} (k : Fin n) (j : Nat)
    (h : (n + 1 - (k.val + 1)) = j + 1) :
    v.get k.succ = (h ▸ v.drop (k.val + 1)).head
    := by
  rcases v with ⟨l, l_prop⟩
  induction l generalizing n
  · exfalso
    aesop
  case cons he ta IH =>
    simp only [Nat.succ_eq_add_one] at IH
    rw [← List.Vector.get_tail_succ]
    simp only [List.Vector.tail]
    cases n
    · exfalso
      cases k
      linarith
    case succ n =>
      cases k using Fin.cases
      · rw [Vector.my_drop_succ_cons]
        · simp [List.Vector.drop]
          convert rfl using 2 <;> simp_all
        · simp
      case succ k =>
        specialize @IH n k (by simp_all) (by simp_all)
        simp only [Nat.succ_eq_add_one, Nat.add_one_sub_one, Fin.val_succ]
        rw [IH]
        clear IH
        rw [Vector.my_drop_succ_cons]
        convert rfl
        simp only [eqRec_heq_iff_heq, heq_eq_eq]
        omega

/-- Generalized vesrion of `Vector.drop_get_eq_get_add`. -/
lemma Vector.drop_get_eq_get_add' (v : List.Vector α n) (l r : ℕ) {h : i = l + r} {hi hr} :
    v.get ⟨i, hi⟩ = (List.Vector.drop l v).get ⟨r, hr⟩ := by
  rcases v with ⟨t, t_prop⟩
  simp [List.Vector.get, List.Vector.drop, h]

/-- A Vector analogue of `List.getElem_drop`. -/
lemma Vector.drop_get_eq_get_add {n : Nat} (v : List.Vector α n) (k : Nat)
    (i : Fin (n - k))
    (still_lt : k + i.val < n) :
    (v.drop k).get i = v.get ⟨k + i.val, still_lt⟩ := by
  apply Eq.symm (Vector.drop_get_eq_get_add' ..)
  rfl

-- FIXME is this in mathlib?
lemma Fin.my_cast_val (n m : Nat) (h : n = m) (j_lt : j < n) :
    (h ▸ ( ⟨j, j_lt⟩ : Fin n)).val = j := by
  aesop

lemma Vector.drop_last_eq_last {v : List.Vector α n.succ} (k : Fin n) (j : Nat)
    (h : (n.succ - (k + 1)) = j.succ) :
    (h ▸ v.drop (k + 1)).last = v.last := by
  unfold List.Vector.last
  have := Vector.drop_get_eq_get_add v (k.val + 1) (h ▸ Fin.last j) (by omega)
  convert this using 2
  · linarith
  · simp
  · simp
  · ext
    unfold Fin.last
    rcases k with ⟨k, k_lt⟩
    simp only [Nat.succ_eq_add_one]
    simp only [Nat.succ_eq_add_one, Nat.reduceSubDiff] at h
    rw [Fin.my_cast_val (j + 1) (n + 1 - (k + 1)) (by linarith) (Nat.lt_succ_self j)]
    omega

lemma Vector.my_cast_heq (n m : Nat) (h : n = m) (v : List.Vector α n) :
    HEq (h ▸ v : List.Vector α m) v := by
  aesop

theorem boxes_true_at_k_of_Vector_rel {W : Type} {M : KripkeModel W} (ξ : AnyFormula)
    (δ : List Program) (h : ¬δ = [])
    (ws : List.Vector W δ.length.succ)
    (ws_rel : ∀ (i : Fin δ.length), relate M (δ.get i) (ws.get ↑↑i) (ws.get i.succ))
    (k : Fin δ.length) (w_nξ : (M, ws.last)⊨~''ξ) :
    (M, ws.get k.succ)⊨~''(AnyFormula.loadBoxes (List.drop (↑k.succ) δ) ξ) := by
  rw [SemImplyAnyNegFormula_loadBoxes_iff]
  refine ⟨ws.last, ?_, w_nξ⟩
  rw [relateSeq_iff_exists_Vector]
  simp only [Fin.val_succ, Nat.succ_eq_add_one, List.get_eq_getElem,
    List.getElem_drop, Fin.coe_eq_castSucc]
  -- need a vector of length `δ.length - (k+1) + 1`
  -- `ws` has length `δ.length + 1`
  -- Hence we use `ws.drop (k + 1)`
  have drop_len_eq : (List.drop (↑k + 1) δ).length + 1 = δ.length.succ - (↑k + 1) :=
    by apply List.nonempty_drop_sub_succ; aesop
  -- cool that List.Vector.drop exists!
  refine ⟨drop_len_eq ▸ ws.drop (k + 1), ?_, ?_, ?_⟩
  · simp_all only [modelCanSemImplyList, List.get_eq_getElem, Nat.succ_eq_add_one, Fin.coe_eq_castSucc,
      Fin.coe_castSucc, Fin.getElem_fin]
    apply Vector.get_succ_eq_head_drop
  · simp [Vector.drop_last_eq_last]
  · simp_all only [modelCanSemImplyList, List.get_eq_getElem, Nat.succ_eq_add_one,
    Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.getElem_fin]
    intro i
    -- It remains to use `ws_rel`. Just dealing with Vector and Fin issues now.
    have still_lt : ↑k + 1 + ↑i < δ.length := by
      rcases k with ⟨k_val, k_prop⟩
      rcases i with ⟨i_val, i_prop⟩
      simp at i_prop
      omega
    have still_rel := ws_rel ⟨↑k + 1 + ↑i, still_lt⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at still_rel
    convert still_rel using 1
    · have : (δ.drop (↑k + 1)).length + 1 = δ.length.succ - (↑k + 1) := by omega
      have := Vector.drop_get_eq_get_add ws (↑k + 1) (this ▸ i) (by omega)
      simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc] at this
      convert this using 1
      · rcases i with ⟨i_val, i_prop⟩ -- to remove casSucc
        simp only [Fin.castSucc_mk]
        congr!
        · simp
        · apply Eq.symm; apply Fin.my_cast_val
      · rcases i with ⟨i_val, i_prop⟩ -- to remove casSucc
        simp only [Fin.castSucc_mk]
        convert rfl using 4
        apply Fin.my_cast_val
    · -- analogous to previous thing?
      rw [Vector.drop_get_eq_get_add' ws (↑k + 1) (↑i + 1)] <;> try omega
      congr
      · apply Vector.my_cast_heq
      · congr!

/-- Soundness of loading and repeats: a tableau can immitate all moves in a model. -/
-- Note that we mix induction' tactic and recursive calls __O.o__
theorem loadedDiamondPaths (α : Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  {side : Side} -- NOT in notes but needed for partition
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side (nodeAt t))
  (v_α_w : relate M α v w)
  (w_nξ : (M,w) ⊨ ~''ξ)
  : ∃ s : PathIn tab, t ◃⁺ s ∧
    -- TODO: missing here: path from t to s is satisfiable!
    (   ( satisfiable (nodeAt s) ∧ ¬ (s ≡ᶜ t) )  -- FIXME: move satisfiable outside disjunction?
      ∨ ( ((~''ξ).in_side side (nodeAt s))
        ∧ (M,w) ⊨ (nodeAt s)
        ∧ ((nodeAt s).without (~''ξ)).isFree
        )
    ) := by

  -- outer induction on the program (do it with recursive calls!)

  -- inner induction is on the path (in Notes this is a separate Lemma , going from t to t')
  induction' t_def : t using PathIn.init_inductionOn
  case root =>
    subst t_def
    exfalso
    unfold AnyNegFormula.in_side at negLoad_in
    unfold Sequent.isFree Sequent.isLoaded at root_free
    rcases X with ⟨L,R,O⟩
    cases O <;> cases side <;> simp at *
  case step s IH t0 s_t0 => -- NOTE: not indenting from here.
  subst t_def

  -- Notes first take care of cases where rule is applied to non-loaded formula.
  -- For this, we need to distinguish what happens at `t`.
  rcases tabAt_t_def : tabAt t with ⟨Hist, Z, tZ⟩
  cases tZ
  -- applying a local or a pdl rule or being a repeat?
  case loc nbas ltZ nrep next =>
    clear IH -- not used here, that one is only for the repeats
    have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
    have locLD := localLoadedDiamond α ltZ v_α_w (this ▸ v_t) _ (this ▸ negLoad_in) w_nξ
    clear this
    rcases locLD with ⟨Y, Y_in, w_Y, free_or_newLoadform⟩
    -- We are given end node, now define path to it
    let t_to_s1 : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ PathIn.loc Y_in .nil)
    let s1 : PathIn tab := t.append t_to_s1
    have t_s : t ⋖_ s1 := by
      unfold s1 t_to_s1
      apply edge_append_loc_nil
      rw [tabAt_t_def]
    have tabAt_s_def : tabAt s1 = ⟨Z :: _, ⟨Y, next Y Y_in⟩⟩ := by
      unfold s1 t_to_s1
      rw [tabAt_append]
      have : (tabAt (PathIn.loc Y_in PathIn.nil : PathIn (Tableau.loc nrep nbas ltZ next)))
           = ⟨Z :: _, ⟨Y, next Y Y_in⟩⟩ := by simp_all
      convert this <;> try rw [tabAt_t_def]
      rw [eqRec_heq_iff_heq]
    have v_s1 : (M,v) ⊨ nodeAt s1 := by
      intro φ φ_in
      apply w_Y
      have : (tabAt s1).2.1 = Y := by rw [tabAt_s_def]
      simp_all
    -- Now distinguish the two cases coming from `localLoadedDiamond`:
    rcases free_or_newLoadform with Y_is_Free
                                  | ⟨F, δ, anf_in_Y, v_seq_w, v_F, Fδ_in_H, Y_almost_free⟩
    · -- Leaving the cluster, easy case.
      refine ⟨s1, ?_, Or.inl ⟨?_, ?_⟩⟩
      · apply Relation.TransGen.single
        left
        exact t_s
      · use W, M, v
      · -- using eProp2 here
        unfold cEquiv
        simp
        have := eProp2.d t s1 (Sequent.isLoaded_of_negAnyFormula_loaded negLoad_in) ?_ t_s
        · unfold before at this
          intro s1_t
          rw [Relation.ReflTransGen.cases_tail_iff] at s1_t
          rcases s1_t with t_def|⟨u,s1_u,u_t⟩
          · rw [t_def] at this
            exfalso
            tauto
          · exfalso
            absurd this.2
            exact Relation.TransGen.tail' s1_u u_t
        · convert Y_is_Free
          unfold nodeAt
          rw [tabAt_s_def]
    · -- Second case of `localLoadedDiamond`.
      -- If δ is empty then we have found the node we want.
      by_cases δ = []
      · subst_eqs
        simp_all only [modelCanSemImplyList, AnyFormula.boxes_nil, relateSeq_nil]
        subst_eqs
        refine ⟨s1, Relation.TransGen.single (Or.inl t_s), Or.inr ⟨?_, v_s1, ?_⟩⟩
        · convert anf_in_Y
          unfold nodeAt
          rw [tabAt_s_def]
        · convert Y_almost_free
          unfold nodeAt
          rw [tabAt_s_def]
      -- Now we have that δ is not empty.
      -- FIXME: indent rest or use wlog above?
      -- Here is the interesting case: not leaving the cluster.
      -- We get a sequence of worlds from the δ relation:
      rcases (relateSeq_iff_exists_Vector M δ v w).mp v_seq_w with ⟨ws, v_def, w_def, ws_rel⟩

      -- Claim for an inner induction on the list δ.
      have claim : ∀ k : Fin δ.length.succ, -- Note the succ here!
          ∃ sk, t ◃⁺ sk ∧ ( ( satisfiable (nodeAt sk) ∧ ¬(sk ≡ᶜ t) )
                          ∨ ( (~''(ξ.loadBoxes (δ.drop k.val))).in_side side (nodeAt sk)
                            ∧ (M, ws[k]) ⊨ nodeAt sk
                            ∧ ((nodeAt sk).without (~''(ξ.loadBoxes (δ.drop k.val)))).isFree)) := by
        intro k
        induction k using Fin.inductionOn
        case zero =>
          simp only [Nat.succ_eq_add_one, Fin.val_zero, List.drop_zero, Fin.getElem_fin]
          refine ⟨s1, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
          · exact Relation.TransGen.single (Or.inl t_s)
          · unfold nodeAt
            rw [tabAt_s_def]
            exact anf_in_Y
          · convert v_s1
            rw [v_def]
            rcases ws with ⟨ws, ws_len⟩
            have := List.exists_of_length_succ _ ws_len
            aesop
          · unfold nodeAt
            rw [tabAt_s_def]
            simp
            cases δ
            · simp_all
            case cons d δ =>
              simp
              apply Sequent.without_loaded_in_side_isFree
              convert anf_in_Y
        case succ k inner_IH =>
          -- Here we will need to apply the outer induction hypothesis. to δ[k] or k+1 ??
          -- NOTE: it is only applicable when α is not a star.
          -- For the star case we need another induction! On the length of `ws`? See notes.

          rcases inner_IH with ⟨sk, t_sk, IH_cases⟩

          rcases IH_cases with _ | ⟨_in_node_sk, wsk_sk, anf_in_sk⟩
          · refine ⟨sk, t_sk, ?_⟩
            left
            assumption
          ·
            -- Prepare using outer IH for the program δ[k] (that must be simpler than α)
            have _forTermination : lengthOfProgram δ[k] < lengthOfProgram α := by
              -- TODO: Show that length went down.
              -- ! Needs better `H_goes_down` similar to `P_goes_down`.
              -- ! Only true when α is a test, union or semicolon ==> need separate case for star!
              have := H_goes_down_prog α Fδ_in_H (by aesop : δ.get k ∈ δ)
              cases α
              all_goals
                simp [Program.isAtomic, Program.isStar, lengthOfProgram] at *
                try linarith
              case atom_prog =>
                rw [this]
                simp [Program.isAtomic, Program.isStar, lengthOfProgram] at *
                -- PROBLEM
                -- should length of atom be 0 or 1?
                -- OR
                -- can we argue here that k should not large? / reach a contradiction?
                -- OR
                -- do we want that `loc` or something else on the way to here should not be allowed for when α is atomic???
                sorry
              case star =>
                -- Here is the **star case** that needs an additional induction and minimality.
                -- See notes!
                sorry

            have outer_IH := @loadedDiamondPaths (δ.get k) _ tab root_free sk W M
              (ws.get k.castSucc) (ws.get k.succ) wsk_sk
              (ξ.loadBoxes (δ.drop k.succ)) -- This is the new ξ.
              side
              (by convert _in_node_sk; rw [←AnyFormula.loadBoxes_cons]; convert rfl using 2; simp)
              (by convert ws_rel k; simp)
              (by apply boxes_true_at_k_of_Vector_rel <;> simp_all)

            clear _forTermination

            rcases outer_IH with ⟨sk2, sk_c_sk2, sk2_property⟩
            rcases sk2_property with ⟨sk2_sat, sk2_nEquiv_sk⟩ | ⟨anf_in_sk2, u_sk2, sk2_almostFree⟩
            · refine ⟨sk2, ?_, Or.inl ⟨sk2_sat, ?_⟩⟩  -- leaving cluster, easy?
              · exact Relation.TransGen.trans t_sk sk_c_sk2
              · apply eProp2.f_tweak _ _ _ t_sk sk_c_sk2 sk2_nEquiv_sk
            · refine ⟨sk2, ?_, Or.inr ⟨anf_in_sk2, u_sk2, sk2_almostFree⟩⟩
              · exact Relation.TransGen.trans t_sk sk_c_sk2

      -- It remains to show that the claim suffices.
      specialize claim δ.length
      rcases claim with ⟨sk, t_sk, sk_prop⟩
      have := List.drop_length δ
      use sk
      simp_all only [modelCanSemImplyList, List.get_eq_getElem, Nat.succ_eq_add_one,
        Fin.coe_eq_castSucc, Fin.natCast_eq_last, Fin.val_last, AnyFormula.boxes_nil,
        Fin.getElem_fin, List.drop_length, true_and]
      convert sk_prop

  case pdl Y bas r nrep next =>
    cases r -- six PDL rules
    -- cannot apply (L+) because we already have a loaded formula
    case loadL =>
      exfalso
      simp only [nodeAt, AnyNegFormula.in_side] at negLoad_in
      rw [tabAt_t_def] at negLoad_in
      aesop
    case loadR =>
      exfalso
      simp only [nodeAt, AnyNegFormula.in_side] at negLoad_in
      rw [tabAt_t_def] at negLoad_in
      aesop
    case freeL L R δ β φ =>
      -- Leaving cluster, interesting that IH is not needed here.
      clear IH
      -- Define child node with path to to it:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      have tabAt_s_def : tabAt s = ⟨_, _, next⟩ := by
        unfold s t_to_s
        rw [tabAt_append]
        -- Only some HEq business left here.
        have : tabAt (.pdl .nil : PathIn (Tableau.pdl nrep bas PdlRule.freeL next))
             = ⟨ (L, R, some (Sum.inl (~'⌊⌊δ⌋⌋⌊β⌋AnyFormula.normal φ))) :: _
               , ⟨(List.insert (~⌈⌈δ⌉⌉⌈β⌉φ) L, R, none), next⟩⟩ := by
          unfold tabAt
          unfold tabAt
          rfl
        convert this <;> try rw [tabAt_t_def]
        simp
      refine ⟨s, ?_, Or.inl ⟨?_, ?_⟩ ⟩
      · apply Relation.TransGen.single
        left
        right
        unfold s t_to_s
        refine ⟨Hist, _, nrep, bas, _, PdlRule.freeL, next, ?_⟩
        simp [tabAt_t_def]
      · use W, M, v
        intro φ φ_in
        rw [tabAt_s_def] at φ_in
        apply v_t -- Let's use that t and s are equivalent if they only differ in loading
        rw [tabAt_t_def]
        aesop
      · apply not_cEquiv_of_free_loaded
        -- use lemma that load and free are never in same cluster
        · simp only [Sequent.isFree, Sequent.isLoaded, nodeAt, decide_false, decide_true,
          Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_true']
          rw [tabAt_s_def]
        · simp only [Sequent.isLoaded, nodeAt, decide_false, decide_true]
          rw [tabAt_t_def]

    case freeR L R δ β φ =>
      -- Leaving cluster, interesting that IH is not needed here.
      clear IH
      -- Define child node with path to to it:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      have tabAt_s_def : tabAt s = ⟨_, _, next⟩ := by
        unfold s t_to_s
        rw [tabAt_append]
        -- Only some HEq business left here.
        have : tabAt (.pdl .nil : PathIn (.pdl nrep bas .freeR next))
             = ⟨ (L, R, some (Sum.inr (~'⌊⌊δ⌋⌋⌊β⌋AnyFormula.normal φ))) :: _
               , ⟨L, (List.insert (~⌈⌈δ⌉⌉⌈β⌉φ) R), none⟩, next⟩ := by
          unfold tabAt
          unfold tabAt
          rfl
        convert this <;> try rw [tabAt_t_def]
        simp
      refine ⟨s, ?_, Or.inl ⟨?_, ?_⟩ ⟩
      · apply Relation.TransGen.single
        left
        right
        unfold s t_to_s
        refine ⟨Hist, _, nrep, bas, _, PdlRule.freeR, next, ?_⟩
        simp [tabAt_t_def]
      · use W, M, v
        intro φ φ_in
        rw [tabAt_s_def] at φ_in
        apply v_t -- Let's use that t and s are equivalent if they only differ in loading
        rw [tabAt_t_def]
        aesop
      · apply not_cEquiv_of_free_loaded
        -- use lemma that load and free are never in same cluster
        · simp only [Sequent.isFree, Sequent.isLoaded, nodeAt, decide_false, decide_true,
          Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_true']
          rw [tabAt_s_def]
        · simp only [Sequent.isLoaded, nodeAt, decide_false, decide_true]
          rw [tabAt_t_def]

    case modL L R a ξ' Z_def Z_isBasic =>
      clear IH -- not needed in this case, also not in notes.
      have : ξ' = ξ := by
        unfold nodeAt at negLoad_in
        rw [tabAt_t_def] at negLoad_in
        unfold AnyNegFormula.in_side at negLoad_in
        cases side <;> simp_all
      subst this
      -- modal rule, so α must actually be atomic!
      have α_is_a : α = (·a : Program) := by
        simp only [AnyNegFormula.in_side, nodeAt] at negLoad_in
        rw [tabAt_t_def] at negLoad_in
        subst Z_def
        cases side
        all_goals
          simp only at negLoad_in
          subst_eqs
        rfl
      subst α_is_a
      simp at v_α_w
      -- Let `s` be the unique child:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      -- used in multiple places below:
      have helper : (∃ φ, ξ' = .normal φ ∧ nodeAt s = ((~φ) :: projection a L, projection a R, none))
                  ∨ (∃ χ, ξ' = .loaded χ ∧ nodeAt s = (projection a L, projection a R, some (Sum.inl (~'χ)))) := by
        subst Z_def
        unfold nodeAt
        unfold s t_to_s
        rw [tabAt_append]
        -- remains to deal with HEq business
        let tclean : PathIn (.pdl nrep bas (.modL (Eq.refl _) Z_isBasic) next) := .pdl .nil
        cases ξ'
        case normal φ =>
          left
          use φ
          simp only [true_and]
          simp at next
          have : (tabAt tclean).2.1 = ((~φ) :: projection a L, projection a R, none) := by
            have : tabAt tclean = ⟨ _ :: _, ((~φ) :: projection a L, projection a R, none) , next⟩ := by unfold tabAt; rfl
            rw [this]
          convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
        case loaded χ =>
          right
          use χ
          simp only [true_and]
          simp at next
          have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inl (~'χ))) := by
            have : tabAt tclean = ⟨ _, (projection a L, projection a R, some (Sum.inl (~'χ))) , next⟩ := by unfold tabAt; rfl
            rw [this]
          convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
      -- ... it is then obvious that `s` satisfies the required properties:
      refine ⟨s, ?_, Or.inr ⟨?_a, ?_b, ?_c⟩⟩
      · constructor
        constructor
        right
        refine ⟨Hist, _, nrep, bas, _, (.modL Z_def Z_isBasic), next, tabAt_t_def, ?_⟩
        simp [s, t_to_s]
      · -- (a)
        subst Z_def
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        all_goals
          rw [nodeAt_s_def]
          unfold AnyNegFormula.in_side
          cases side
          case LL => simp_all
          case RR =>
            absurd negLoad_in
            unfold nodeAt
            rw [tabAt_t_def]
            unfold AnyNegFormula.in_side
            simp
      · -- (b)
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        · rw [nodeAt_s_def]
          intro f f_in
          simp at f_in
          rcases f_in with (f_in|f_in|f_in)
          · subst_eqs
            exact w_nξ
          all_goals
            have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
            apply this
            simp only [relate]
            exact v_α_w
        · rw [nodeAt_s_def]
          intro f f_in
          simp at f_in
          rcases f_in with ((f_in|f_in)|f_in)
          case inr.intro.intro.inr =>
            subst_eqs
            simp only [evaluate]
            exact w_nξ
          all_goals
            have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
            apply this
            simp only [relate]
            exact v_α_w
      · -- (c)
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        all_goals
          rw [nodeAt_s_def]
          simp_all [Sequent.isFree, Sequent.isLoaded, Sequent.without]

    case modR L R a ξ' Z_def Z_isBasic => -- COPY ADAPTATION from `modL`
      clear IH -- not needed in this case, also not in notes.
      have : ξ' = ξ := by
        unfold nodeAt at negLoad_in
        rw [tabAt_t_def] at negLoad_in
        unfold AnyNegFormula.in_side at negLoad_in
        cases side <;> simp_all
      subst this
      -- modal rule, so α must actually be atomic!
      have α_is_a : α = (·a : Program) := by
        simp only [AnyNegFormula.in_side, nodeAt] at negLoad_in
        rw [tabAt_t_def] at negLoad_in
        subst Z_def
        cases side
        all_goals
          simp only at negLoad_in
          subst_eqs
        rfl
      subst α_is_a
      simp at v_α_w
      -- Let `s` be the unique child:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      -- used in multiple places below:
      have helper : (∃ φ, ξ' = .normal φ ∧ nodeAt s = (projection a L, (~φ) :: projection a R, none))
                  ∨ (∃ χ, ξ' = .loaded χ ∧ nodeAt s = (projection a L, projection a R, some (Sum.inr (~'χ)))) := by
        subst Z_def
        unfold nodeAt
        unfold s t_to_s
        rw [tabAt_append]
        -- remains to deal with HEq business
        let tclean : PathIn (.pdl nrep bas (.modR (Eq.refl _) Z_isBasic) next) := .pdl .nil
        cases ξ'
        case normal φ =>
          left
          use φ
          simp only [true_and]
          simp at next
          have : (tabAt tclean).2.1 = (projection a L, (~φ) :: projection a R, none) := by
            have : tabAt tclean = ⟨ _ :: _, (projection a L, (~φ) :: projection a R, none) , next⟩ := by unfold tabAt; rfl
            rw [this]
          convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
        case loaded χ =>
          right
          use χ
          simp only [true_and]
          simp at next
          have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inr (~'χ))) := by
            have : tabAt tclean = ⟨ _, (projection a L, projection a R, some (Sum.inr (~'χ))) , next⟩ := by unfold tabAt; rfl
            rw [this]
          convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
      -- ... it is then obvious that `s` satisfies the required properties:
      refine ⟨s, ?_, Or.inr ⟨?_a', ?_b', ?_c'⟩⟩ -- annoying that ' are needed here?
      · constructor
        constructor
        right
        refine ⟨Hist, _, nrep, bas, _, (PdlRule.modR Z_def Z_isBasic), next, tabAt_t_def, ?_⟩
        simp [s, t_to_s]
      · -- (a)
        subst Z_def
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        all_goals
          rw [nodeAt_s_def]
          unfold AnyNegFormula.in_side
          cases side
          case RR => simp_all
          case LL =>
            absurd negLoad_in
            unfold nodeAt
            rw [tabAt_t_def]
            unfold AnyNegFormula.in_side
            simp
      · -- (b)
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        · rw [nodeAt_s_def]
          intro f f_in
          simp at f_in
          rcases f_in with (f_in|f_in|f_in)
          · have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
            apply this
            simp only [relate]
            exact v_α_w
          · subst_eqs
            simp_all
            exact w_nξ
          · have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
            apply this
            simp only [relate]
            exact v_α_w
        · rw [nodeAt_s_def]
          intro f f_in
          simp at f_in
          rcases f_in with ((f_in|f_in)|f_in)
          case inr.intro.intro.inr =>
            subst_eqs
            simp only [evaluate]
            exact w_nξ
          all_goals
            have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
            apply this
            simp only [relate]
            exact v_α_w
      · -- (c)
        rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
        all_goals
          rw [nodeAt_s_def]
          simp_all [Sequent.isFree, Sequent.isLoaded, Sequent.without]

  case rep lpr =>
    -- Here we need to go to the companion.
    -- IDEA: make a recursive call, and for termination note that the path becomes shorter?
    have h : (tabAt t).snd.snd = Tableau.rep (tabAt_t_def ▸ lpr) := by
      -- rw [tabAt_t_def] -- motive is not type correct ???
      sorry
    -- Let `u` be the companion.
    let u := companionOf t (tabAt_t_def ▸ lpr) h
    have t_comp_u : t ♥ u:= ⟨(tabAt_t_def ▸ lpr), h, rfl⟩
    -- Show that the companion fulfills the conditions:
    have u_eq_t := nodeAt_companionOf_setEq t (tabAt_t_def ▸ lpr) h
    have v_u : (M, v) ⊨ nodeAt u := by
      rw [vDash_setEqTo_iff u_eq_t]
      exact v_t
    have negLoad_in_u : (~''(AnyFormula.loaded (⌊α⌋ξ))).in_side side (nodeAt u) := by
      rw [AnyNegFormula.in_side_of_setEqTo u_eq_t]
      exact negLoad_in
    -- Now prepare and make the recursive call:
    have _forTermination : (companionOf t (tabAt_t_def ▸ lpr) h).length < t.length := by
      apply companionOf_length_lt_length
    have := loadedDiamondPaths α tab root_free u v_u ξ negLoad_in_u v_α_w w_nξ
    rcases this with ⟨s, u_s, (⟨s_sat, not_s_u⟩|reached)⟩
    all_goals
      refine ⟨s, ?_, ?_⟩
      exact Relation.TransGen.head (Or.inr ⟨tabAt_t_def ▸ lpr, h, rfl⟩) u_s
    · refine Or.inl ⟨s_sat, ?_⟩
      exact eProp2.f_tweak _ _ _ (Relation.TransGen.single (Or.inr t_comp_u)) u_s not_s_u
    · exact Or.inr reached

termination_by
  (⟨lengthOfProgram α, t.length⟩ : Nat ×ₗ Nat)
decreasing_by
  · exact Prod.Lex.left _ _ _forTermination
  · exact Prod.Lex.right (lengthOfProgram α) _forTermination

theorem simpler_equiv_simpler {u s t : PathIn tab} :
    s <ᶜ u → s ≡ᶜ t → t <ᶜ u := by
  intro u_simpler_s s_equiv_t
  rcases u_simpler_s with ⟨s_c_u, not_u_c_s⟩
  rcases s_equiv_t with ⟨_, t_s⟩
  constructor
  · exact Relation.TransGen.trans_right t_s s_c_u
  · intro u_c_t
    absurd not_u_c_s
    exact Relation.TransGen.trans_left u_c_t t_s

/-- Any node in a closed tableau with a free root is not satisfiable.
This is the main argument for soundness. -/
theorem tableauThenNotSat (tab : Tableau .nil Root) (Root_isFree : Root.isFree) (t : PathIn tab) :
    ¬satisfiable (nodeAt t) :=
  by
  -- by induction on the *converse* well-founded strict partial order <ᶜ called `before`.
  apply @WellFounded.induction _ (flip before) ((eProp tab).2.2 : _) _ t
  clear t
  intro t IH
  simp [flip] at IH
  by_cases (Sequent.isFree $ nodeAt t)
  case pos t_is_free =>
    -- "First assume that t is free.""
    cases t_def : (tabAt t).2.2 -- Now consider what the tableau does at `t`.
    case rep lpr => -- Then t cannot be a LPR.
      exfalso
      have := LoadedPathRepeat_rep_isLoaded lpr
      simp_all [Sequent.isFree, nodeAt]
    case loc nbas lt nrep next =>
      simp [nodeAt]
      rw [localTableauSat lt] -- using soundness of local tableaux here!
      simp
      intro Y Y_in
      -- We are given an end node, now need to define a path leading to it.
      let t_to_s : PathIn (Tableau.loc nrep nbas lt next) := (.loc Y_in .nil)
      let s : PathIn tab := t.append (t_def ▸ t_to_s)
      have t_s : t ⋖_ s := by
        unfold s t_to_s
        have := edge_append_loc_nil t next Y_in (by rw [← t_def])
        convert this
        rw [← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]
      have : Y = nodeAt s := by
        unfold s t_to_s
        simp
        apply Eq.symm
        convert nodeAt_loc_nil next Y_in
        simp
      rw [this]
      apply IH
      apply eProp2.c t _ t_is_free t_s
    case pdl Y bas r nrep next =>
      simp [nodeAt]
      intro hyp
      have := pdlRuleSat r hyp -- using soundness of pdl rules here!
      absurd this
      -- As in `loc` case, it now remains to define a path leading to `Y`.
      let t_to_s : PathIn (Tableau.pdl nrep bas r next) := (.pdl .nil)
      let s : PathIn tab := t.append (t_def ▸ t_to_s)
      have t_s : t ⋖_ s := by
        unfold s t_to_s
        exact edge_append_pdl_nil t_def
      have : Y = nodeAt s := by
        unfold s t_to_s
        simp only [nodeAt_append]
        apply Eq.symm
        convert nodeAt_pdl_nil next r
        simp
      rw [this]
      apply IH
      apply eProp2.c t _ t_is_free t_s
  -- "The interesting case is where t is loaded;"
  case neg not_free =>
    simp [Sequent.isFree] at not_free
    rcases O_def : (tabAt t).2.1.2.2 with _ | snlf
    · -- "none" case is impossible because t is not free:
      exfalso; simp_all [nodeAt, Sequent.isLoaded]; split at not_free <;> simp_all
    -- two goals remaining, but left and right case are almost the same :-)
    let _theSide := sideOf snlf -- Needed below in `all_goals` block.
    rcases snlf with (nlf | nlf)
    all_goals
    · clear not_free -- to clear up inner IH
      rcases nlf with ⟨lf⟩
      -- Now we take apart the loaded formula to get all loaded boxes from the front at once,
      -- so that we can do induction on δ for multiple `loadedDiamondPaths` applications.
      rcases LoadFormula.exists_loadMulti lf with ⟨δ, α, φ, lf_def⟩
      -- Start the induction before `rintro` so the inner IH is about satisfiability.
      induction δ generalizing lf t -- amazing that this does not give a wrong motive ;-)
      -- Note that here it is too late to generalize whether loaded formula was left/right.
      case nil =>
        simp only [loadMulti, List.foldr_nil] at lf_def
        have in_t : (~''(⌊α⌋φ)).in_side _theSide (nodeAt t) := by
          simp_all [nodeAt]; aesop
        -- Let C be the cluster to which `t` belongs.
        -- We claim that any ◃-path of satisfiable nodes starting at t must remain in C.
        have claim : ∀ s, t ◃⁺ s → satisfiable (nodeAt s) → s ≡ᶜ t := by
          intro s t_to_s s_sat
          rw [cEquiv.symm]
          by_contra hyp
          absurd s_sat
          -- use IH and Lemma (f) to show claim
          apply IH
          exact eProp2.f s t t_to_s hyp
        -- Now assume for contradiction, that Λ(t) is satisfiable.
        rintro ⟨W, M, v, v_⟩
        have := v_ (~(loadMulti [] α φ).unload) (by simp; right; aesop)
        rw [unload_loadMulti] at this
        simp only [Formula.boxes_nil, evaluate, not_forall, Classical.not_imp] at this
        rcases this with ⟨w, v_α_w, not_w_φ⟩
        have := loadedDiamondPaths α tab Root_isFree t v_ φ in_t v_α_w (not_w_φ)
        rcases this with ⟨s, t_to_s, (⟨s_sat, notequi⟩ | ⟨in_s, w_s, rest_s_free⟩)⟩
        · -- "Together wit the observation ..."
          absurd notequi
          apply claim _ t_to_s s_sat
        · -- We now claim that we have a contradiction with the outer IH as we left the cluster:
          absurd IH s ?_
          exact ⟨W, M, w, w_s⟩
          simp only [Sequent.without_normal_isFree_iff_isFree] at rest_s_free
          -- Remains to show that s is simpler than t. We use eProp2.
          constructor
          · exact t_to_s
          · have : (nodeAt t).isLoaded := by
              unfold Sequent.isLoaded
              simp [AnyNegFormula.in_side] at in_t
              aesop
            apply eProp2.d_help _ _ this rest_s_free t_to_s
      case cons β δ inner_IH =>
        rintro ⟨W,M,v,v_⟩
        have := v_ (~(loadMulti (β :: δ) α φ).unload) (by
          simp
          right
          rw [O_def]
          -- the following is needed because we are in "all_goals"
          try (left; use (~'loadMulti (β :: δ) α φ); simp_all; done)
          try (right; use (~'loadMulti (β :: δ) α φ); simp_all)
          )
        simp only [unload_loadMulti] at this
        rw [Formula.boxes_cons] at this
        simp only [evaluate, not_forall, Classical.not_imp] at this
        -- We make one step with `loadedDiamondPaths` for β.
        rcases this with ⟨w, v_β_w, not_w_δαφ⟩
        have in_t : (~''(⌊β⌋(⌊⌊δ⌋⌋⌊α⌋φ))).in_side _theSide (nodeAt t) := by
          simp_all only [nodeAt, loadMulti_cons]
          subst lf_def
          exact O_def
        have := loadedDiamondPaths β tab Root_isFree t v_ (⌊⌊δ⌋⌋⌊α⌋φ) in_t v_β_w
          (by simp_all [modelCanSemImplyAnyNegFormula, modelCanSemImplyAnyFormula])
        rcases this with ⟨s, t_to_s, s_property⟩
        rcases s_property with ⟨s_sat, notequi⟩ | ⟨not_af_in_s, w_s, rest_s_free⟩
        · -- We left the cluster, use outer IH to get contradiction.
          absurd IH s (eProp2.f s t t_to_s (by rw [cEquiv.symm]; exact notequi))
          -- need that `s` is satisfiable
          exact s_sat
        · -- Here is the case where s is still loaded and in the same cluster.
          -- We apply the *inner* IH to s and then the outer IH to get a contradiction
          have := inner_IH s ?_ (loadMulti δ α φ) ?_ rfl
          · absurd this
            use W, M, w, w_s
          · intro u ⟨u_to_s, not_s_to_u⟩
            apply IH
            constructor
            · exact Relation.TransGen.trans t_to_s u_to_s
            · intro hyp
              absurd not_s_to_u
              exact Relation.TransGen.trans hyp t_to_s
          · simp only [nodeAt] at not_af_in_s
            subst lf_def
            simp_all
            assumption

theorem correctness : ∀ LR : Sequent, LR.isFree → satisfiable LR → consistent LR := by
  intro LR LR_isFRee
  contrapose
  unfold consistent
  unfold inconsistent
  simp only [not_nonempty_iff, not_isEmpty_iff, Nonempty.forall]
  intro hyp
  apply tableauThenNotSat hyp LR_isFRee .nil

theorem soundTableau : ∀ φ, provable φ → ¬satisfiable ({~φ} : Finset Formula) := by
  intro φ prov
  rcases prov with ⟨tabl⟩|⟨tabl⟩
  exact tableauThenNotSat tabl (by simp) .nil
  exact tableauThenNotSat tabl (by simp) .nil

/-- All provable formulas are semantic tautologies.
See `tableauThenNotSat` for what the notes call soundness. -/
theorem soundness : ∀ φ, provable φ → tautology φ := by
  intro φ prov
  apply notsatisfnotThenTaut
  rw [← singletonSat_iff_sat]
  apply soundTableau
  exact prov
