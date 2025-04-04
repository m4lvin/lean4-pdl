import Mathlib.Data.Finset.Lattice.Fold

import Pdl.Tableau
import Pdl.Vector

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

/-- The `⋖_` relation in a tableau is well-founded.
Proven by lifting the relation to the length of histories.
That length goes up with `⋖_`, so because `<` is wellfounded on `Nat`
also `⋖_` is well-founded via `RelHomClass.wellFounded`. -/
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
  case lrep =>
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
  case lrep =>
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
  case lrep =>
    cases t
    simp_all [PathIn.toHistory, PathIn.rewind]

/-- ## Finiteness and Wellfoundedness --/

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
    (h : IsIrrefl α (Relation.TransGen r)) : WellFounded r :=
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

lemma PathIn.mem_history_setEqTo_then_lrep {tab : Tableau Hist X} (p : PathIn tab) :
    (∃ Y ∈ (tabAt p).1, Y.setEqTo (nodeAt p)) → (tabAt p).2.2.isLrep := by
  rintro ⟨Y, h1, h2⟩
  generalize h : tabAt p = tp
  rcases tp with ⟨H, Z, t⟩
  simp [nodeAt] at h2
  rw [h] at h2
  cases t
  case loc _ _   nrep _ => exact nrep ⟨Y, by aesop⟩
  case pdl _ _ _ nrep _ => exact nrep ⟨Y, by aesop⟩
  case lrep             => simp [Tableau.isLrep]

lemma single_of_transgen {α} {r} {a c: α} : Relation.TransGen r a c → ∃ b, r a b := by
  intro h
  induction h
  case single b e => use b
  case tail d e ih => assumption

instance flipEdge.instIsIrrefl : IsIrrefl (PathIn tab) (Relation.TransGen (flip edge)) := by
  constructor
  intro p p_p
  rw [Relation.transGen_swap] at p_p
  have p_in_Hist_p := edge_TransGen_then_mem_History p_p
  have := PathIn.mem_history_setEqTo_then_lrep p ⟨nodeAt p, by simpa⟩
  rcases (single_of_transgen p_p)
  with ⟨_, ⟨_, _, _, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, _, h, _⟩⟩ <;> rw [h] at this <;> contradiction

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
