import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Relation
import Mathlib.Tactic.DepRewrite

import Pdl.Tableau

/-! # Navigating through tableaux with PathIn

To define relations between nodes in a tableau we need to represent the whole
tableau and point to a specific node inside it. This is the `PathIn` type.
Its values say "go to this child, then to this child, ... stop here."
-/

/-- A path in a tableau. Three constructors for the empty path, a local step or a pdl step.
The `loc` and `pdl` steps correspond to two out of three constructors of `Tableau`.
A `PathIn` only goes downwards, it cannot use `LoadedPathRepeat`s. -/
inductive PathIn : ∀ {Hist X}, Tableau Hist X → Type
| nil : PathIn _
| loc {nrep nbas lt next Y} (Y_in : Y ∈ endNodesOf lt) (tail : PathIn (next Y Y_in))
    : PathIn (Tableau.loc nrep nbas lt next)
| pdl {nrep bas} {r : PdlRule X Y} {next} (tail : PathIn next)
    : PathIn (Tableau.pdl nrep bas r next)
deriving DecidableEq

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

/-- Relation `s ⋖_ t` says `t` is a child of `s`. Two cases, both defined via `append`. -/
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
    (tabAt_s_def : tabAt s = ⟨sHist, sX, Tableau.loc nrep nbas lt next⟩) :
    edge s (s.append (tabAt_s_def ▸ PathIn.loc Y_in .nil)) := by
  unfold edge
  left
  use sHist, sX, nrep, nbas, lt, next, (by assumption), Y_in
  constructor
  · rw [append_eq_iff_eq, ← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]
  · rw [← tabAt_s_def]

/-- Appending a one-step `pdl` path is also a ⋖_ child. -/
@[simp]
theorem edge_append_pdl_nil (h : (tabAt s).2.2 = Tableau.pdl nrep bas r next) :
    edge s (s.append (h ▸ PathIn.pdl .nil)) := by
  simp only [edge, append_eq_iff_eq]
  right
  use (tabAt s).1, (tabAt s).2.1, nrep, bas, (by assumption), r, next
  constructor
  · rw [← heq_iff_eq, heq_eqRec_iff_heq, eqRec_heq_iff_heq]
  · rw [← h]

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
      simp at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp at p_def
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
      simp at p_def
      rw [p_def]
      rfl
    · right
      use Hist, X, nrep, bas, Y, r, next, tab_def
      simp at p_def
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
    · subst_eqs; simp_all only [heq_eq_eq, eqRec_heq_iff_heq]
  · subst t_def
    rw [append_length, add_right_inj]
    have : 1 = (.pdl .nil : PathIn (Tableau.pdl nrep bas r' next')).length := by simp
    convert this
    · simp_all only [PathIn.length, zero_add]
    · rw [tabAt_s_def]
    · rw [tabAt_s_def]
    · subst_eqs; simp_all only [heq_eq_eq, eqRec_heq_iff_heq]

theorem edge_then_length_lt {s t : PathIn tab} (s_t : s ⋖_ t) : s.length < t.length := by
  have := length_succ_eq_length_of_edge s_t
  linarith

def edge_natLT_relHom {Hist X tab} : RelHom (@edge Hist X tab) Nat.lt :=
  ⟨PathIn.length, edge_then_length_lt⟩

/-- The `⋖_` relation in a tableau is well-founded.
Proven by lifting the relation to the length of histories.
That length goes up with `⋖_`, so because `<` is wellfounded on `Nat`
also `⋖_` is well-founded via `RelHomClass.wellFounded`. -/
theorem edge.wellFounded : WellFounded (@edge Hist X tab) := by
  apply @RelHomClass.wellFounded _ Nat (@edge Hist X tab) Nat.lt _ _ _ edge_natLT_relHom
  have := instWellFoundedLTNat
  rcases this with ⟨nat_wf⟩
  convert nat_wf

instance edge.isAsymm : @Std.Asymm (PathIn tab) edge := by
  constructor
  apply WellFounded.asymmetric edge.wellFounded

/-- Enable "<" notation for transitive closure of ⋖_. -/
instance : LT (PathIn tab) := ⟨Relation.TransGen edge⟩

/-- Enable "≤" notation for reflexive transitive closure of ⋖_ -/
instance : LE (PathIn tab) := ⟨Relation.ReflTransGen edge⟩

/-- The "<" in a tableau is antisymmetric. -/
instance edge.TransGen_isAsymm : @Std.Asymm (PathIn tab) (Relation.TransGen edge) :=
  ⟨WellFounded.asymmetric (WellFounded.transGen wellFounded)⟩

theorem not_path_nil {a : PathIn tab} : ¬(a < PathIn.nil) := by
  intro con
  cases con <;> simp_all [not_edge_nil]

theorem edge_is_strict_ordering {s t : PathIn tab} : s ⋖_ t → s ≠ t := by
  intro s_t set
  have := edge_then_length_lt s_t
  simp_all

theorem path_is_strict_ordering {s t : PathIn tab} : s < t → s ≠ t := by
intro s_t seqt
induction s_t
case single set =>
  absurd seqt
  exact edge_is_strict_ordering set
case tail k t s_k k_t ih =>
  apply edge.TransGen_isAsymm.1 s k s_k
  rw [seqt]
  apply Relation.TransGen.single k_t

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
  case lrep =>
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

/-! ## Path cast and append lemmas

Lemmas developed for `tabToIntAt`.
-/

@[simp]
lemma PathIn.cast_nil (h : tab = tab2) :
    (h ▸ (.nil : PathIn tab)) = (.nil : PathIn tab2) := by grind

@[simp]
lemma PathIn.tabAt_cast_nil (h : tab = tab2) :
    tabAt (h ▸ (PathIn.nil : PathIn tab)) = tabAt (.nil : PathIn tab2) := by
  convert @tabAt_nil; simp_all

@[simp]
lemma PathIn.tabAt_cast_loc (h : (Tableau.loc nrep nbas lt nexts) = tab2)
    (tail : PathIn (nexts Y Y_in)) :
    tabAt (h ▸ (PathIn.loc Y_in tail)) = tabAt tail := by
  convert tabAt_loc <;> simp_all

@[simp]
lemma PathIn.tabAt_cast_pdl (h : Tableau.pdl nrep bas r next = tab2) :
    tabAt (h ▸ PathIn.pdl tail) = tabAt tail := by
  convert @tabAt_pdl _ _ nrep bas _ r next tail <;> simp_all

@[simp]
lemma PathIn.tabAt_cast (p : PathIn tab) (h : tab = tab2) :
    tabAt (h ▸ p) = tabAt p := by
  cases p <;> simp_all [tabAt]

/-- (p ++ q) ++ r = p ++ (q ++ r) -/
lemma PathIn.append_append {tab : Tableau Hist X}
    (p : PathIn tab) (q : PathIn (tabAt p).2.2) (r : PathIn (tabAt (p.append q)).2.2)
    : (p.append q).append r = p.append (q.append (tabAt_append p q ▸ r)) := by
  induction p <;> simp_all [PathIn.append]

@[simp]
lemma PathIn.loc_append {X Hist} {nrep : ¬rep Hist X} {nbas : ¬X.basic} {lt : LocalTableau X}
    {nexts : (Y : Sequent) → Y ∈ endNodesOf lt → Tableau (X :: Hist) Y}
    {Y : Sequent} {Y_in : Y ∈ endNodesOf lt} {tail : PathIn _}
    (h : PathIn (nexts Y Y_in) = PathIn (tabAt (PathIn.loc Y_in .nil)).snd.snd)
    : (PathIn.loc Y_in .nil : PathIn (Tableau.loc nrep nbas lt nexts)).append tail
    = PathIn.loc Y_in (h ▸ tail) := by
  simp [append]

@[simp]
lemma PathIn.pdl_append {Hist X Y} {next : Tableau (X :: Hist) Y} {nrep : ¬rep Hist X}
    {bas : X.basic} {r : PdlRule X Y} {tail : PathIn (tabAt PathIn.nil.pdl).snd.snd}
    (h : PathIn next = PathIn (tabAt nil.pdl).snd.snd)
    : (PathIn.pdl .nil : PathIn (Tableau.pdl nrep bas r next)).append tail
    = PathIn.pdl (h ▸ tail) := by
  simp [append]

/-- Used for `tabToIntAt`. -/
lemma PathIn.lt_append_non_nil {Hist X pHist pX tabNew} {tab : Tableau Hist X}
  (p : PathIn tab) (h : tabAt p = ⟨pHist, ⟨pX, tabNew⟩⟩) (q : PathIn tabNew)
  : q ≠ .nil → p < p.append (h ▸ q) := by
  cases q
  case nil => simp
  case loc Y nbas lt Y_in nrep nexts tail =>
    simp
    have p_loc : p ⋖_ (p.append (h ▸ PathIn.loc Y_in .nil)) := edge_append_loc_nil _ _ _ h
    apply Relation.TransGen.head' p_loc
    by_cases tail_nil : tail = .nil
    · subst_eqs
      exact Relation.ReflTransGen.refl
    · apply Relation.TransGen.to_reflTransGen
      have IH := @PathIn.lt_append_non_nil Hist X _ _ (nexts Y Y_in) tab
      convert IH ?_ ?_ tail tail_nil using 1
      · rw [PathIn.append_append, append_eq_iff_eq]
        simp
        have := @PathIn.loc_append _ _ nrep nbas lt nexts Y Y_in tail rfl
        convert this <;> try rw [h]
        · simp_all
        · grind
      · simp
        rw! [h]
        simp
  case pdl Y bas r nrep next tail =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_const]
    have p_pdl : p ⋖_ (p.append (h ▸ nil.pdl)) := by
      have := @edge_append_pdl_nil Hist X tab p
      rw! (castMode := .all) [h] at this
      simp only [Tableau.pdl.injEq, forall_and_index] at this
      exact @this nrep bas Y r next rfl (by simp) (by simp)
    apply Relation.TransGen.head' p_pdl
    by_cases tail_nil : tail = .nil
    · subst_eqs
      exact Relation.ReflTransGen.refl
    · apply Relation.TransGen.to_reflTransGen
      have IH := @PathIn.lt_append_non_nil _ _ _ _ next tab
      convert IH ?_ ?_ tail tail_nil using 1
      · rw [PathIn.append_append, append_eq_iff_eq]
        simp
        have := @PathIn.pdl_append _ _ _ next nrep bas r tail rfl
        convert this <;> try rw [h]
        · simp_all
        · grind
      · simp
        rw! [h]
        simp
termination_by
  tabNew.size
decreasing_by
  · subst_eqs
    apply Tableau.size_next_lt_of_loc rfl
  · subst_eqs
    apply Tableau.size_next_lt_of_pdl rfl

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
    : (loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length
      = tail.toHistory.length + 1 := by
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
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList]
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toList, PathIn.prefix]
    case pdl rest Y Z r tab IH tail =>
      simp [PathIn.toList, PathIn.prefix]
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList]
  case lrep =>
    cases t
    simp_all [PathIn.toList, PathIn.prefix]

/-! ## Path Rewinding -/

/-- Rewinding a path, removing the last `k` steps. Cannot go into Hist.
Used to go to the companion of a repeat. Returns `.nil` when `k` is the length of the whole path.
We use +1 in the type because `rewind 0` is always possible, even with history `[]`.
Defined using Fin.lastCases.

Hint: when proving stuff about `rewind k`, avoid induction on k, because rewind does not decrease k.
-/
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
    -- TODO
    -- The rest here would be nice as a lemma, a variant of `Fin.lastCases_castSucc`
    -- and maybe it could be called `Fin.lastCases_castSucc_of_ne_last`.
    have : 0 ≠ Fin.last (.loc Y_in tail : PathIn (.loc nrep nbas lt next)).toHistory.length := by
      simp_all
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, loc.injEq, heq_eq_eq, true_and]
    convert IH
    cases k
    simp_all
  case pdl Y Z X0 nrep bas r next tail IH =>
    have : 0 ≠ Fin.last (.pdl tail : PathIn (.pdl nrep bas r next)).toHistory.length := by
      simp_all
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp [← kdef, Fin.lastCases_castSucc, Function.comp_apply, pdl.injEq]
    convert IH
    cases k
    simp_all

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
  case lrep =>
    cases t
    simp only [rewind]
    exact Relation.ReflTransGen.refl

/-- If we rewind by `k > 0` steps then the length goes down. -/
theorem PathIn.rewind_length_lt_length_of_gt_zero {Hist X} {tab : Tableau Hist X}
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

theorem PathIn.rewind_lt_of_gt_zero {Hist X} {tab : Tableau Hist X}
    (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) (k_gt_zero : k > 0) :
    (t.rewind k) < t := by
  have h : t.rewind k ≤ t := PathIn.rewind_le t k
  apply Relation.TransGen_of_ReflTransGen h
  intro con
  have length_lt : (t.rewind k).length < t.length :=
    PathIn.rewind_length_lt_length_of_gt_zero t k k_gt_zero
  have length_eq : (t.rewind k).length = t.length := by simp [con]
  simp_all

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
          Fin.lastCases_castSucc, Function.comp_apply, nodeAt_loc, Fin.val_cast, Fin.val_castSucc]
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
          Fin.val_cast, Fin.val_castSucc]
        rcases j with ⟨j,j_lt⟩
        rw [pdl_length_eq] at j_lt
        have := @List.getElem_append _ (nodeAt tail :: tail.toHistory) [Z] j ?_
        · simp only [List.cons_append, List.length_cons, List.getElem_singleton] at this
          rw [this]
          simp_all
        · simp only [List.cons_append, List.length_cons, List.length_append]
          exact Nat.lt_add_right 1 j_lt
  case lrep =>
    cases t
    simp_all [PathIn.toHistory, PathIn.rewind]

theorem nil_iff_length_zero {a : PathIn tab} :
    a = PathIn.nil ↔ a.toHistory = [] := by
constructor
· intro a_nil
  subst a_nil
  simp [PathIn.toHistory]
· cases a <;> simp [PathIn.toHistory]

lemma PathIn.loc_injective {Hist X nrep nbas lt next Y Y_in ta tb} :
    @PathIn.loc Hist X nrep nbas lt next Y Y_in ta = PathIn.loc Y_in tb → ta = tb := by
  simp

lemma PathIn.pdl_injective {Hist X Y nrep bas next} r ta tb :
    @PathIn.pdl Hist X Y nrep bas r next ta = PathIn.pdl tb → ta = tb := by
  simp

theorem edge_is_irreflexive {a : PathIn tab} : ¬(a ⋖_ a) := by
intro con
have := edge_then_length_lt con
simp_all

theorem path_then_length_lt {s t : PathIn tab} (s_t : s < t) : s.length < t.length := by
  induction s_t
  case single set => exact edge_then_length_lt set
  case tail h ih => have := edge_then_length_lt h
                    linarith

theorem path_is_irreflexive {a : PathIn tab} : ¬(Relation.TransGen edge a a) := by
  intro con
  have := path_then_length_lt con
  simp_all

theorem rewind_order_reversing {t : PathIn tab} {k k' : Fin (List.length t.toHistory + 1)}
    (h : k < k') : t.rewind k' ≤ t.rewind k := by -- We have to put ≤ to deal with nil.
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp [Fin.last]
          simp [PathIn.toHistory] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.loc_le_loc_of_le
          apply IH
          · simp_all
  case pdl => -- almost the same as `loc`, maybe change to `all_goals`?
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      exact Relation.ReflTransGen.refl
    case pdl rest Y Z r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp [Fin.last]
          simp [PathIn.toHistory] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          rw [Fin.lastCases_last]
          exact PathIn.nil_le_anything
        case cast j' =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.pdl_le_pdl_of_le
          apply IH
          · simp_all
  case lrep =>
    cases t
    simp only [PathIn.rewind]
    exact Relation.ReflTransGen.refl

theorem PathIn.loc_lt_loc_of_lt {Hist X Y nrep nbas lt next Z_in} {t1 t2} (h : t1 < t2) :
    @loc Hist X Y nrep nbas lt next Z_in t1 < @ loc Hist X Y nrep nbas lt next Z_in t2 :=
  Relation.TransGen_of_ReflTransGen (PathIn.loc_le_loc_of_le (Relation.TransGen.to_reflTransGen h))
  <| by
  simp_all
  intro con
  subst con
  exact path_is_irreflexive h

theorem PathIn.pdl_lt_pdl_of_lt {Hist X Y nrep bas r Z_in} {t1 t2} (h : t1 < t2) :
    @pdl Hist X Y nrep bas r Z_in t1 < @pdl Hist X Y nrep bas r Z_in t2 :=
  Relation.TransGen_of_ReflTransGen (PathIn.pdl_le_pdl_of_le (Relation.TransGen.to_reflTransGen h))
  <| by
  simp_all
  intro con
  subst con
  exact path_is_irreflexive h

-- needs a better name
theorem one_is_one_helper {h : k > 0} :
    (1 : ℕ) = (1 : Fin (k + 1)).1 := by
  simp
  induction k
  case zero => simp_all
  case succ n ih => simp

theorem rewind_of_edge_is_eq {a b : PathIn tab} (a_b : a ⋖_ b) : b.rewind 1 = a := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases b <;> simp_all only [PathIn.rewind]
    case nil => simp_all [not_edge_nil]
    case loc Z nbas' nrep' Z_in tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                          | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · simp [PathIn.append] at p_def
            apply PathIn.loc_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
          · exfalso
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        rfl
      case loc X nbas'' nrep'' X_in tail' =>
        have Z_X : Z = X := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩ )
          all_goals
          simp [PathIn.append] at p_def
          exact p_def.1
        have Z_in_X_in : HEq Z_in X_in := by simp_all
        subst Z_X Z_in_X_in
        simp at a_b
        specialize IH Z Z_in a_b
        have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
          have t_ne_nil : tail ≠ PathIn.nil := by
            intro con
            subst con
            exact not_edge_nil _ _ a_b
          simp
          by_contra con
          have t_nil := nil_iff_length_zero.2 con
          simp_all
        have hyp : 1 ≠ Fin.last (List.length (tail.toHistory ++ [Y])) := by
          simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
        rw [← Fin.exists_castSucc_eq] at hyp
        rcases hyp with ⟨k,kdef⟩
        simp [← kdef, Fin.lastCases_castSucc, Function.comp_apply]
        rw [← IH]
        convert rfl
        simp [Fin.ext_iff] at *
        rw [kdef, @Nat.one_mod_eq_one]
        aesop
  case pdl rest Y X nrep bas r tab IH =>
    cases b <;> simp_all only [PathIn.rewind]
    case nil => simp_all [not_edge_nil]
    case pdl Z bas' nrep' tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                          | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · exfalso
            unfold tabAt at tabAt_def
            aesop
          · simp [PathIn.append] at p_def
            apply PathIn.pdl_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        rfl
      case pdl bas'' nrep'' tail' =>
        simp at a_b
        specialize IH a_b
        have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
          have t_ne_nil : tail ≠ PathIn.nil := by
            intro con
            subst con
            exact not_edge_nil _ _ a_b
          simp
          by_contra con
          have t_nil := nil_iff_length_zero.2 con
          simp_all
        have hyp : 1 ≠ Fin.last (List.length (tail.toHistory ++ [Y])) := by
          simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
        rw [← Fin.exists_castSucc_eq] at hyp
        rcases hyp with ⟨k,kdef⟩
        simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, PathIn.pdl.injEq]
        rw [← IH]
        convert rfl
        simp [Fin.ext_iff] at *
        rw [kdef, @Nat.one_mod_eq_one]
        aesop
  case lrep => cases b ; simp [not_edge_nil] at a_b

theorem rewind_order_reversing_if_not_nil {t : PathIn tab}
    {k k' : Fin (List.length t.toHistory + 1)} (h : k < k') (h' : t ≠ PathIn.nil) :
    t.rewind k' < t.rewind k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      simp_all
    case loc Z nbas nrep Z_in tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          absurd h
          simp
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp [Fin.last]
          simp [PathIn.toHistory] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          apply Relation.TransGen_of_ReflTransGen (PathIn.nil_le_anything)
          simp
        case cast j' =>
          have ⟨j'_val, j'_pf⟩ := j'
          have ⟨j_val, j_pf⟩ := j
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.loc_lt_loc_of_lt
          apply IH
          · simp_all
          · intro con
            subst con
            simp [PathIn.toHistory] at j_pf
            simp [PathIn.toHistory] at j'_pf
            simp_all
  case pdl  => -- almost the same as `loc`, maybe change to `all_goals`?
    cases t <;> simp only [PathIn.rewind]
    case nil =>
      simp_all
    case pdl rest Y Z r tab IH bas nrep tail =>
      cases k using Fin.lastCases
      case last =>
        cases k' using Fin.lastCases
        case last =>
          absurd h
          simp
        case cast j' =>
          absurd h
          have ⟨j'_val, j'_pf⟩ := j'
          simp [Fin.last]
          simp [PathIn.toHistory] at j'_pf
          exact Nat.le_of_lt j'_pf
      case cast j =>
        cases k' using Fin.lastCases
        case last =>
          simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
          apply Relation.TransGen_of_ReflTransGen (PathIn.nil_le_anything)
          simp
        case cast j' =>
          have ⟨j'_val, j'_pf⟩ := j'
          have ⟨j_val, j_pf⟩ := j
          simp only [Fin.lastCases_castSucc, Function.comp_apply]
          apply PathIn.pdl_lt_pdl_of_lt
          apply IH
          · simp_all
          · intro con
            subst con
            simp [PathIn.toHistory] at j_pf
            simp [PathIn.toHistory] at j'_pf
            simp_all
  case lrep =>
    cases t
    simp only [PathIn.rewind]
    simp_all

theorem rewind_is_inj {t : PathIn tab} {k k'} (h1 : t.rewind k = t.rewind k') : k = k' := by
  cases eq_or_ne t PathIn.nil
  case inl t_eq_nil =>
    subst t_eq_nil
    have ⟨k_val, k_pf⟩ := k
    have ⟨k'_val, k'_pf⟩ := k'
    simp [PathIn.toHistory] at k_pf
    simp [PathIn.toHistory] at k'_pf
    simp_all
  case inr t_ne_nil =>
    apply Fin.le_antisymm
    all_goals
    by_contra hyp
    simp at hyp
    have := rewind_order_reversing_if_not_nil hyp t_ne_nil
    simp_all
    exact path_is_irreflexive this

theorem one_is_one_rewind_helper {b : PathIn tab} {k : Fin (List.length b.toHistory + 1)}
    (h : (b.rewind k) ⋖_ b) : k = (1 : Fin (List.length b.toHistory + 1)) := by
  have := rewind_of_edge_is_eq h
  exact Eq.symm (rewind_is_inj this)

lemma edge_leftInjective {tab : Tableau Hist X} (a b c : PathIn tab) :
    a ⋖_ c → b ⋖_ c → a = b := by
  intro a_c b_c
  apply rewind_of_edge_is_eq at a_c
  apply rewind_of_edge_is_eq at b_c
  simp_all

lemma edge_revEuclideanHelper (a b c : PathIn tab) : a ⋖_ c → b < c → b ≤ a := by
  intro a_c b_c
  cases b_c
  case single c b_c =>
    have a_eq_c := edge_leftInjective a b c a_c b_c
    simp_all
    exact Relation.ReflTransGen.refl
  case tail d b_d d_c =>
    have a_eq_d := edge_leftInjective a d c a_c d_c
    rw [a_eq_d]
    exact Relation.TransGen.to_reflTransGen b_d

lemma path_revEuclidean (a b c : PathIn tab) :
    a < c → b < c → (a < b ∨ b < a ∨ b = a) := by
  intro a_lt_c b_lt_c
  induction a_lt_c
  case single c a_ed_b =>
    have b_le_a := edge_revEuclideanHelper a b c a_ed_b b_lt_c
    cases eq_or_ne b a
    case inl b_eq_a => exact Or.inr (Or.inr b_eq_a)
    case inr b_ne_a => exact Or.inr (Or.inl (Relation.TransGen_of_ReflTransGen b_le_a b_ne_a))
  case tail d c a_d d_c ih =>
    have b_le_d : b ≤ d := edge_revEuclideanHelper d b c d_c b_lt_c
    cases eq_or_ne b d
    case inl b_eq_d =>
      rw [←b_eq_d] at a_d
      exact Or.inl a_d
    case inr b_ne_d => exact ih (Relation.TransGen_of_ReflTransGen b_le_d b_ne_d)

lemma path_revEuclidean' (a b c : PathIn tab) :
    a < c → b < c → (a ≤ b ∨ b ≤ a) := by
  intro a_c b_c
  rcases (path_revEuclidean a b c a_c b_c) with a_b | b_a | a_eq_b
  case inl => exact Or.inl (Relation.TransGen.to_reflTransGen a_b)
  case inr =>
    have a_a : a ≤ a := by exact Relation.ReflTransGen.refl
    left
    simp_all
  case inr.inl => exact Or.inr (Relation.TransGen.to_reflTransGen b_a)

theorem edge_inc_length_by_one {a b : PathIn tab} (a_b : edge a b) :
    List.length a.toHistory + 1 + 1 = List.length b.toHistory + 1 := by
  have a_is_b_re_1 := rewind_of_edge_is_eq a_b
  subst a_is_b_re_1
  induction b
  case nil => simp [not_edge_nil] at a_b
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    by_cases tail = PathIn.nil
    case pos tail_eq_nil =>
      subst tail_eq_nil
      rfl
    case neg tail_ne_nil =>
      have helper : 1 ≠ Fin.last (List.length (tail.toHistory ++ [X])) := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp only [Nat.right_eq_add, List.length_eq_zero_iff]
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp only [Nat.add_right_cancel_iff, PathIn.rewind, PathIn.loc_length_eq] at *
      -- similar to something above, should be same lemma?
      rw [← Fin.exists_castSucc_eq] at helper
      rcases helper with ⟨k, kdef⟩
      rw [← kdef] at a_b
      simp only [Fin.lastCases_castSucc, Function.comp_apply, loc_edge_loc_iff_edge] at a_b
      have := one_is_one_rewind_helper a_b
      simp_all [← kdef]
  case pdl Hist X Y nrep bas r next tail IH => -- exactly the same as loc case
    by_cases tail = PathIn.nil
    case pos tail_eq_nil =>
      subst tail_eq_nil
      rfl
    case neg tail_ne_nil =>
      have helper : 1 ≠ Fin.last (List.length (tail.toHistory ++ [X])) := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp only [Nat.right_eq_add, List.length_eq_zero_iff]
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp only [Nat.add_right_cancel_iff, PathIn.rewind, PathIn.pdl_length_eq] at *
      -- similar to something above, should be same lemma?
      rw [← Fin.exists_castSucc_eq] at helper
      rcases helper with ⟨k, kdef⟩
      rw [← kdef] at a_b
      simp only [Fin.lastCases_castSucc, Function.comp_apply, pdl_edge_pdl_iff_edge] at a_b
      have := one_is_one_rewind_helper a_b
      simp_all [← kdef]

theorem rewind_helper {a b : PathIn tab} {k : Fin (List.length a.toHistory + 1)} (a_b : a ⋖_ b) :
    b.rewind (Fin.cast (edge_inc_length_by_one a_b) (k.succ)) = a.rewind k := by
  induction tab
  case loc rest Y nrep nbas lt next IH =>
    cases b
    case nil => simp [not_edge_nil] at a_b
    case loc Z nbas' nrep' Z_in tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                        | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · simp [PathIn.append] at p_def
            apply PathIn.loc_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
          · exfalso
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        simp_all [PathIn.rewind, Fin.lastCases, PathIn.toHistory]
        have ⟨k_val, k_pf⟩ := k
        simp [PathIn.toHistory] at k_pf
        simp_all
        rfl
      case loc X nbas'' nrep'' X_in tail' =>
        have Z_X : Z = X := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩ )
          all_goals
          simp [PathIn.append] at p_def
          exact p_def.1
        have Z_in_X_in : HEq Z_in X_in := by simp_all
        subst Z_X
        subst Z_in_X_in
        have t'_t : tail' ⋖_ tail := by simp_all
        simp only [PathIn.rewind]
        cases k using Fin.lastCases
        case last => simp
        case cast i =>
          -- TODO same lemma?
          have h : (Fin.cast (Nat.succ.inj (edge_inc_length_by_one a_b)) i.castSucc).succ
                  ≠ Fin.last (List.length (PathIn.loc Z_in tail).toHistory) := by
            intro con
            have ⟨i_val, i_pf⟩ := i
            simp_all [Fin.last]
            simp [PathIn.toHistory] at i_pf
            have := edge_inc_length_by_one t'_t
            linarith
          rw [← Fin.exists_castSucc_eq] at h
          rcases h with ⟨k, kdef⟩
          simp [← kdef]
          have := @IH Z Z_in tail' tail (Fin.cast (PathIn.loc_length_eq Z_in tail') i) t'_t
          rcases k with ⟨k, k_lt⟩
          convert this
          simp at *
          cases kdef
          simp
  case pdl rest Y X nrep bas r tab IH =>
    cases b
    case nil => simp [not_edge_nil] at a_b
    case pdl Z bas' nrep' tail =>
      cases a
      case nil =>
        have t_nil : tail = PathIn.nil := by
          rcases a_b with ( ⟨_, _, _, _, _, _, _, _, tabAt_def, p_def⟩
                        | ⟨_, _, _, _, _, _, _, tabAt_def, p_def⟩ )
          · exfalso
            unfold tabAt at tabAt_def
            aesop
          · simp [PathIn.append] at p_def
            apply PathIn.pdl_injective
            rw [p_def]
            unfold tabAt at tabAt_def
            aesop
        subst t_nil
        simp_all [PathIn.rewind, PathIn.toHistory]
        have ⟨k_val, k_pf⟩ := k
        simp [PathIn.toHistory] at k_pf
        simp_all
        rfl
      case pdl bas'' nrep'' tail' =>
        have t'_t : tail' ⋖_ tail := by simp_all
        simp only [PathIn.rewind]
        cases k using Fin.lastCases
        case last => simp
        case cast i =>
          -- TODO same lemma?
          have h : (Fin.cast (Nat.succ.inj (edge_inc_length_by_one a_b)) i.castSucc).succ
                  ≠ Fin.last (List.length (PathIn.pdl tail).toHistory) := by
            intro con
            have ⟨i_val, i_pf⟩ := i
            simp_all [Fin.last]
            simp [PathIn.toHistory] at i_pf
            have := edge_inc_length_by_one t'_t
            linarith
          rw [← Fin.exists_castSucc_eq] at h
          rcases h with ⟨k, kdef⟩
          simp [← kdef]
          have := @IH tail' tail (Fin.cast (PathIn.pdl_length_eq tail') i) t'_t
          rcases k with ⟨k, k_lt⟩
          convert this
          simp at *
          cases kdef
          simp
  case lrep => cases b ; simp [not_edge_nil] at a_b

-- unique existence?
theorem exists_rewind_of_le {a b : PathIn tab} (h : a ≤ b) : ∃ k, b.rewind k = a := by
  induction h
  case refl b a_b =>
    use 0
    exact PathIn.rewind_zero
  case tail c b a_c c_b ih =>
    have ⟨k, c_re_k_is_a⟩ := ih
    use (Fin.cast (edge_inc_length_by_one c_b) (k.succ))
    have := (@rewind_helper _ _ _ c b k c_b)
    rw [c_re_k_is_a] at this
    exact this

theorem exists_rewinds_middle {a b c : PathIn tab} (h : a ≤ b) (h' : b ≤ c) :
    ∃ k k', c.rewind k = a ∧ c.rewind k' = b ∧ k' ≤ k := by
  have ⟨k, c_re_k_is_a⟩ := exists_rewind_of_le (Relation.ReflTransGen.trans h h')
  have ⟨k', c_re_k'_is_b⟩ := exists_rewind_of_le h'
  use k
  use k'
  have k_lt_k' : k' ≤ k := by
    cases eq_or_ne c PathIn.nil
    case inl c_eq_nil =>
      subst c_eq_nil
      simp_all [PathIn.toHistory]
    case inr c_ne_nil =>
    by_contra k_lt_k
    apply not_le.1 at k_lt_k
    have this := rewind_order_reversing_if_not_nil k_lt_k c_ne_nil
    simp_all only [ne_eq]
    apply edge.TransGen_isAsymm.1 a b ?_ this
    apply Relation.TransGen_of_ReflTransGen h
    intro con
    simp_all only
    exact path_is_irreflexive this
  simp_all

/-! ## Finiteness and Wellfoundedness -/

-- Why not in Mathlib?
-- See https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Union.20BigOperator/near/470044981
@[simp]
def Finset.join [DecidableEq α] (M : Finset (Finset α)) : Finset α := M.sup id

def allPaths : (tab : Tableau Hist X) → Finset (PathIn tab)
| .loc _ _ lt next => { .nil } ∪
    ((endNodesOf lt).attach.map
      (fun Y => (allPaths (next Y.1 Y.2)).image (fun p => PathIn.loc Y.2 p))
    ).toFinset.join
| .pdl _ _ _ next => { .nil } ∪ (allPaths next).image (fun p => PathIn.pdl p)
| .lrep _ => { .nil }

theorem allPaths_loc_cases (s : PathIn _) : s ∈ allPaths (.loc nrep nbas lt next) ↔
      s = PathIn.nil
    ∨ ∃ (Y : Sequent) (Y_in : Y ∈ endNodesOf lt) (t : allPaths (next Y Y_in)),
        s = PathIn.loc Y_in t := by
  unfold allPaths
  aesop

theorem PathIn.elem_allPaths {Hist X} {tab : Tableau Hist X} (p : PathIn tab) :
    p ∈ allPaths tab := by
  induction tab
  case loc Hist X lt nexts IH =>
    induction p using init_inductionOn
    case root =>
      simp_all [allPaths]
    case step t _ s t_s =>
      rw [allPaths_loc_cases]
      cases s
      · tauto
      case loc nrep nbas Y Y_in tail =>
        right
        simp_all
  case pdl nrep bas r next =>
    cases p <;> simp_all [allPaths]
  case lrep lpr =>
    cases p
    simp_all [allPaths]

/-- A Tableau is finite.
Should be useful to get *converse* well-foundedness of `edge` -/
instance PathIn.instFintype {tab : Tableau Hist X} : Fintype (PathIn tab) := by
  refine ⟨allPaths tab, PathIn.elem_allPaths⟩

-- mathlib?
theorem Finite.wellfounded_of_irrefl_TC {α : Type} [Finite α] (r : α → α → Prop)
    (h : Std.Irrefl (Relation.TransGen r)) : WellFounded r :=
  let wf := Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
  ⟨fun a => acc_transGen_iff.mp <| wf.apply a⟩

lemma nodeAt_mem_History_of_edge : p ⋖_ q → nodeAt p ∈ (tabAt q).1 := by
  rintro ( ⟨Hist, XX, nrep, nbas, lt, next, Y, Y_in, tab_def, q_def⟩
         | ⟨Hist, XX, nrep, bas, Y, r, next, tab_def, q_def⟩ )
  <;> induction p <;> (simp at tab_def; aesop)

lemma mem_History_of_edge : p ⋖_ q → x ∈ (tabAt p).1 → x ∈ (tabAt q).1 := by
  intro hedge hmemp
  rcases hedge with ( ⟨Hist, XX, nrep, nbas, lt, next, Y, Y_in, tab_def, q_def⟩
                    | ⟨Hist, XX, nrep, bas, Y, r, next, tab_def, q_def⟩ )
  <;> induction p <;> (simp at tab_def; aesop)

lemma mem_History_append : X ∈ (tabAt p).1 → X ∈ (tabAt (p.append q)).1 := by
  intro h
  induction q using PathIn.init_inductionOn <;> simp_all
  apply mem_History_of_edge <;> assumption

lemma edge_TransGen_then_mem_History :
    Relation.TransGen edge p q → nodeAt p ∈ (tabAt q).1 := by
  intro h
  induction h with
  | single h => apply (nodeAt_mem_History_of_edge h)
  | tail t h ih =>
    rcases h with ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩
    <;> subst p_def <;> apply (mem_History_append ih)

lemma PathIn.mem_history_multisetEqTo_then_lrep {tab : Tableau Hist X} (p : PathIn tab) :
    (∃ Y ∈ (tabAt p).1, Y.multisetEqTo (nodeAt p)) → (tabAt p).2.2.isLrep := by
  rintro ⟨Y, h1, h2⟩
  generalize h : tabAt p = tp
  rcases tp with ⟨H, Z, t⟩
  simp [nodeAt] at h2
  rw [h] at h2
  cases t
  case loc _ _   nrep _ => exact nrep ⟨Y, by have := Sequent.setEqTo_of_multisetEqTo; aesop⟩
  case pdl _ _ _ nrep _ => exact nrep ⟨Y, by have := Sequent.setEqTo_of_multisetEqTo; aesop⟩
  case lrep             => simp [Tableau.isLrep]

lemma single_of_transgen {α} {r} {a c : α} : Relation.TransGen r a c → ∃ b, r a b := by
  intro h
  induction h
  case single b e => use b
  case tail d e ih => assumption

instance flipEdge.instIsIrrefl : @Std.Irrefl (PathIn tab) (Relation.TransGen (flip edge)) := by
  constructor
  intro p p_p
  rw [Relation.transGen_swap] at p_p
  have p_in_Hist_p := edge_TransGen_then_mem_History p_p
  have := PathIn.mem_history_multisetEqTo_then_lrep p ⟨nodeAt p, by simpa⟩
  rcases (single_of_transgen p_p) with ⟨_,   ⟨_, _, _, _, _, _, _, _, h, _⟩
                                           | ⟨_, _, _, _, _, _, _, h, _⟩⟩
  <;> rw [h] at this <;> contradiction

/-- The `flip edge` relation in a tableau is well-founded. -/
theorem flipEdge.wellFounded :
  WellFounded (flip (@edge _ _ tab)) := by
  apply Finite.wellfounded_of_irrefl_TC _ flipEdge.instIsIrrefl

/-- Induction principle going from the leaves (= childless nodes) to the root.
Suppose whenever the `motive` holds at all children then it holds at the parent.
Then it holds at all nodes. -/
theorem PathIn.edge_upwards_inductionOn {Hist X} {tab : Tableau Hist X}
    {motive : PathIn tab → Prop}
    (up : ∀ {u}, (∀ {s}, (u_s : u ⋖_ s) → motive s) → motive u)
    (t : PathIn tab)
    : motive t := by
  -- Doing `induction tab` as in `init_inductionOn` is not what we want here.
  apply WellFounded.induction flipEdge.wellFounded t
  intro t IH
  rcases tabT_def : (tabAt t) with ⟨H,X,tabT⟩
  cases tabT
  case loc => exact up fun {s} t_s => IH s t_s
  case pdl => exact up fun {s} t_s => IH s t_s
  case lrep =>
    apply up
    rintro s t_s
    rcases t_s with ⟨_, _, _, _, _, _, _, _, tabAt_t_eq, _⟩
                  | ⟨_, _, _, _, _, _, _, tabAt_t_eq, _⟩
    · rw [tabT_def] at tabAt_t_eq
      cases tabAt_t_eq
    · rw [tabT_def] at tabAt_t_eq
      cases tabAt_t_eq

-- not in mathlib already?
lemma Relation.TransGen_flip_iff {r : α → α → Prop} :
    Relation.TransGen (flip r) s t ↔ Relation.TransGen r t s := by
  constructor
  all_goals
    intro t_s
    induction t_s
    case single t s_t =>
      exact TransGen.single s_t
    case tail b c _ c_b b_s =>
      simp only [flip] at c_b
      exact TransGen.trans (TransGen.single c_b) b_s

/-- Strong induction from the leaves (= childless nodes) to the root.
Suppose whenever the `motive` holds at all successors then it holds at the parent.
Then it holds at all nodes. -/
theorem PathIn.strong_upwards_inductionOn {Hist X} {tab : Tableau Hist X}
    {motive : PathIn tab → Prop}
    (ups : ∀ {u}, (∀ {s}, (u_s : u < s) → motive s) → motive u)
    (t0 : PathIn tab)
    : motive t0 := by
  have := @WellFounded.transGen _ _ (@flipEdge.wellFounded _ _ tab)
  apply WellFounded.induction this t0
  intro t IH
  rcases tabT_def : (tabAt t) with ⟨H,X,tabT⟩
  cases tabT
  case loc => exact ups fun {s} t_s => IH s (by rw [Relation.TransGen_flip_iff]; exact t_s)
  case pdl => exact ups fun {s} t_s => IH s (by rw [Relation.TransGen_flip_iff]; exact t_s)
  case lrep lpr =>
    apply ups
    rintro s t_s
    cases t_s
    case a.single t_s => -- easy case, like in non-strong induction
      rcases t_s with ⟨_, _, _, _, _, _, _, _, tabAt_t_eq, _⟩
                    | ⟨_, _, _, _, _, _, _, tabAt_t_eq, _⟩
      · rw [tabT_def] at tabAt_t_eq
        cases tabAt_t_eq
      · rw [tabT_def] at tabAt_t_eq
        cases tabAt_t_eq
    case a.tail b c t__b b_c =>
      apply IH
      rw [Relation.TransGen_flip_iff]
      exact Relation.TransGen.trans t__b (Relation.TransGen.single b_c)
