import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Vector.Defs
import Pdl.TableauPath

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
  case modL L R a χ X_def =>
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
  case modR L R a χ X_def =>
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

/-! ## Companion, cEdge, etc. -/

/-- To get the companion of a `LoadedPathRepeat` we rewind the path with the lpr value.
The `succ` is there because the lpr values are indices of the history starting with 0, but
`PathIn.rewind 0` would do nothing. -/
def companionOf {X} {tab : Tableau .nil X} (s : PathIn tab) lpr
  (_ : (tabAt s).2.2 = .lrep lpr) : PathIn tab :=
    s.rewind ((Fin.cast (tabAt_fst_length_eq_toHistory_length s) lpr.val).succ)

-- maybe use Fin.cast?

/-- `s ♥ t` means `s` is a `LoadedPathRepeat` and the `companionOf s` is `t`. -/
def companion {X} {tab : Tableau .nil X} (s t : PathIn tab) : Prop :=
  ∃ (lpr : _) (h : (tabAt s).2.2 = .lrep lpr), t = companionOf s lpr h

notation pa:arg " ♥ " pb:arg => companion pa pb

/-- The node at a companion is the same as the one in the history. -/
theorem nodeAt_companionOf_eq_toHistory_get_lpr_val (s : PathIn tab) lpr h :
    nodeAt (companionOf s lpr h)
    = s.toHistory.get (Fin.cast (tabAt_fst_length_eq_toHistory_length s) lpr.val) := by
  unfold companionOf
  rw [PathIn.nodeAt_rewind_eq_toHistory_get]
  simp

theorem nodeAt_companionOf_setEq {tab : Tableau .nil X} (s : PathIn tab) lpr
    (h : (tabAt s).2.2 = .lrep lpr)
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
  simp only [List.append_nil] at this
  convert lpr.2.2 lpr.val (by simp)
  exact (Fin.heq_ext_iff (congrArg List.length this)).mpr rfl

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

/-- The `<ᶜ` relation is irreflexive. -/
theorem before.irrefl :
    IsIrrefl _ (@before X tab) := by
  constructor
  intro p
  simp [before]

/-- The `<ᶜ` relation is transitive. -/
theorem before.trans :
    Transitive (@before X tab) := by
  intro p q r p_c_q q_c_r
  rcases p_c_q with ⟨p_q, not_q_p⟩
  rcases q_c_r with ⟨q_r, not_r_q⟩
  constructor
  · exact Relation.TransGen.trans p_q q_r
  · intro r_p
    absurd not_r_q
    exact Relation.TransGen.trans r_p p_q

/-- The transitive closure of `<ᶜ` (which in fact is the same as `<ᶜ`) is irreflexive. -/
theorem trans_before.irrefl {X tab} :
    IsIrrefl _ (Relation.TransGen (@before X tab)) := by
  rw [Relation.transGen_eq_self before.trans]
  exact before.irrefl

/-- The `before` relation in a tableau is well-founded. -/
theorem before.wellFounded :
    WellFounded (@before X tab) :=
  Finite.wellfounded_of_irrefl_TC _ trans_before.irrefl

/-- The converse of `<ᶜ` is irreflexive. -/
theorem flip_before.irrefl :
    IsIrrefl _ (flip (@before X tab)) := by
  constructor
  intro p
  simp [flip, before]

-- maybe already in mathlib?
lemma Relation.TransGen.flip_iff (α : Type) {r : α → α → Prop} {a b : α} :
    (Relation.TransGen (flip r)) a b ↔ (Relation.TransGen r) b a := by
  exact @Relation.transGen_swap α r a b

/-- The transtive closure of the converse of `<ᶜ` is irreflexive. -/
theorem trans_flip_before.irrefl :
    IsIrrefl _ (Relation.TransGen (flip (@before X tab))) := by
  constructor
  intro p
  rw [Relation.TransGen.flip_iff]
  exact (@trans_before.irrefl X tab).1 p

/-- The `before` relation in a tableau is converse well-founded. -/
theorem flip_before.wellFounded :
    WellFounded (flip (@before X tab)) :=
  Finite.wellfounded_of_irrefl_TC _ trans_flip_before.irrefl

/-- ≣ᶜ is an equivalence relation and <ᶜ is well-founded and converse well-founded.
The converse well-founded is what we really need for induction proofs. -/
theorem eProp {X} (tab : Tableau .nil X) :
    Equivalence (@cEquiv X tab)
    ∧
    WellFounded (@before X tab)
    ∧
    WellFounded (flip (@before X tab))
     := by
  refine ⟨?_, before.wellFounded, flip_before.wellFounded⟩
  constructor
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

-- Unused?
theorem ePropB.a {tab : Tableau .nil X} (s t : PathIn tab) :
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
theorem ePropB.b {tab : Tableau .nil X} (s t : PathIn tab) : s ♥ t → t ≡ᶜ s := by
  intro comp
  constructor
  · simp only [companion, companionOf, exists_prop] at comp
    rcases comp with ⟨lpr, _, t_def⟩
    subst t_def
    have := PathIn.rewind_le s ((Fin.cast (tabAt_fst_length_eq_toHistory_length s) lpr.val).succ)
    simp only [LE.le, instLEPathIn] at this
    exact Relation.ReflTransGen_or_left this
  · unfold cEdge
    apply Relation.ReflTransGen_or_right
    exact Relation.ReflTransGen.single comp

theorem vector_tail_head {α : Type} {n : ℕ} (ys : List.Vector α n.succ) : ys.head = ys.get 0 := by
rcases ys with ⟨l,l_len⟩
cases l <;> aesop

theorem vector_tail_get {α : Type} {n : ℕ} (k : Fin n) (ys : List.Vector α n.succ) : ys.tail.get k = ys.get (k+1)
:= match ys with
| ⟨[], h⟩ => by simp [List.Vector.tail, List.Vector.get]
                rfl'
| ⟨head :: v, h⟩ => by simp [List.Vector.tail, List.Vector.get]

theorem Vector.my_get_one_eq_tail_head (ys : List.Vector α (k + 1).succ) :
    ys.get 1 = ys.tail.head := by
  cases ys using List.Vector.inductionOn
  case cons y ys =>
    simp only [Nat.succ_eq_add_one, List.Vector.tail_cons]
    -- Remaining proof found by asking `rw?` three times ;-)
    rw [← @Fin.succ_zero_eq_one', @List.Vector.get_cons_succ, List.Vector.get_zero]

theorem Vector.last_eq_tail_last {k : Nat} (ys : List.Vector α (k + 1).succ) :
    ys.tail.last = ys.last := by
  cases ys using List.Vector.inductionOn
  case cons y ys => aesop

theorem TransGen.of_reflTransGen {α : Type} {r : α → α → Prop}
  {a b : α} (h : Relation.ReflTransGen r a b) (hne : a ≠ b) : Relation.TransGen r a b :=
  by induction h
     case refl => contradiction
     case tail c b a_c c_b ih => cases eq_or_ne a c with
      | inl a_eq_c => apply Relation.TransGen.single
                      simp_all
      | inr a_ne_c => apply Relation.TransGen.tail (ih a_ne_c) c_b

theorem length_append_greater_1 {b : PathIn tab} {a : PathIn (tabAt b).snd.snd} (h : b ≠ PathIn.nil) : List.length ((b.append a).toHistory) ≥ 1 := by
induction b <;> simp [PathIn.append]
case nil => contradiction

theorem nil_iff_length_zero {a : PathIn tab} : (a = PathIn.nil) ↔ (a.toHistory = []) := by
constructor
· intro a_nil
  subst a_nil
  simp [PathIn.toHistory]
· cases a <;> simp [PathIn.toHistory]

theorem one_is_one_helper {h : k > 0} : (1 : ℕ) = (1 : Fin (k + 1)).1 := by -- needs a better name
simp [Fin.eq_of_val_eq]
induction k
case zero => simp_all
case succ n ih => simp

lemma PathIn.loc_injective :
    @PathIn.loc Hist X nrep nbas lt next Y Y_in ta = PathIn.loc Y_in tb → ta = tb := by
  simp

lemma PathIn.pdl_injective r ta tb :
    @PathIn.pdl Hist X Y nrep bas r next ta = PathIn.pdl tb → ta = tb := by
  simp

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
      simp [Fin.lastCases, Fin.reverseInduction, PathIn.toHistory]
    case loc X nbas'' nrep'' X_in tail' =>
      have Z_X : Z = X := by
        rcases a_b with ( ⟨_, _, _, _, _, _, _, _, _, p_def⟩ | ⟨_, _, _, _, _, _, _, _, p_def⟩ )
        all_goals
        simp [PathIn.append] at p_def
        exact p_def.1
      have Z_in_X_in : HEq Z_in X_in := by simp_all
      subst Z_X
      subst Z_in_X_in
      simp at a_b
      have t_nil : tail ≠ PathIn.nil := by
        intro con
        subst con
        exact not_edge_nil _ _ a_b
      have := IH Z Z_in a_b
      simp [Fin.lastCases, Fin.reverseInduction, PathIn.toHistory]
      have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
        simp
        by_contra con
        have t_nil := nil_iff_length_zero.2 con
        simp_all
      have hyp : ¬ (1 = Fin.last (List.length (tail.toHistory ++ [Y]))) := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp_all
      convert this
      apply one_is_one_helper
      by_contra con
      simp_all
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
      simp [Fin.lastCases, Fin.reverseInduction, PathIn.toHistory]
    case pdl bas'' nrep'' tail' =>
      simp at a_b
      have t_nil : tail ≠ PathIn.nil := by
        intro con
        subst con
        exact not_edge_nil _ _ a_b
      have := IH a_b
      simp [Fin.lastCases, Fin.reverseInduction, PathIn.toHistory]
      have hyp' : List.length (tail.toHistory) + 1 ≠ 1 := by
        simp
        by_contra con
        have t_nil := nil_iff_length_zero.2 con
        simp_all
      have hyp : ¬ (1 = Fin.last (List.length (tail.toHistory ++ [Y]))) := by
        have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
          simp
          intro con
          have := nil_iff_length_zero.2 con
          simp_all
        intro con
        simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
      simp_all
      convert this
      apply one_is_one_helper
      by_contra con
      simp_all
case lrep => cases b
             simp_all [not_edge_nil]

lemma edge_leftInjective {tab : Tableau Hist X} (a b c : PathIn tab) : a ⋖_ c → b ⋖_ c → a = b := by
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
  case inr b_ne_a => exact Or.inr (Or.inl (TransGen.of_reflTransGen b_le_a b_ne_a))
case tail d c a_d d_c ih =>
  have b_le_d : b ≤ d := edge_revEuclideanHelper d b c d_c b_lt_c
  cases eq_or_ne b d
  case inl b_eq_d =>
    rw [←b_eq_d] at a_d
    exact Or.inl a_d
  case inr b_ne_d => exact ih (TransGen.of_reflTransGen b_le_d b_ne_d)

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

theorem PathIn.rewind_lt_of_gt_zero' {tab : Tableau Hist X} -- naming isnt good, see original PathIn.rewind_lt_of_gt_zero which has to do with length
  (t : PathIn tab) (k : Fin (t.toHistory.length + 1)) (k_gt_zero : k > 0)
  : (t.rewind k) < t := by
have h : t.rewind k ≤ t := PathIn.rewind_le t k
apply TransGen.of_reflTransGen h
intro con
have length_lt : (t.rewind k).length < t.length := PathIn.rewind_lt_of_gt_zero t k k_gt_zero
have length_eq : (t.rewind k).length = t.length := by simp [con]
simp_all

theorem lpr_is_lt {l c : PathIn tab} : l ♥ c → c < l := by
intro l_hearts_c
have ⟨lpr, tabAt_l_def, c_def⟩ := l_hearts_c
rw [c_def]
unfold companionOf
apply PathIn.rewind_lt_of_gt_zero' l _ _
simp

theorem rewind_helper {b : PathIn tab} (k : ℕ)
  (h : k + 1 < List.length b.toHistory + 1)
  (h' : k < List.length (b.rewind 1).toHistory + 1) :
  b.rewind (⟨k + 1, h⟩) = (b.rewind 1).rewind ⟨k, h'⟩ := by
induction tab
case loc rest Y nrep nbas lt next IH =>
  cases b <;> simp_all only [PathIn.rewind]
  case loc Z nbas nrep Z_in tail =>
    cases (⟨k + 1, h⟩ : Fin (List.length (PathIn.loc Z_in tail).toHistory + 1)) using Fin.lastCases
    sorry
    sorry
case pdl => sorry -- this will be same as loc case
case lrep =>
  cases b; simp only [PathIn.rewind]

theorem edge_inc_length_by_one {a b : PathIn tab} (a_b : edge a b) : List.length b.toHistory = List.length a.toHistory + 1 := by
have a_is_b_re_1 := rewind_of_edge_is_eq a_b
subst a_is_b_re_1
induction b
case nil => simp [not_edge_nil] at a_b
case loc Hist X nrep nbas lt next Y Y_in tail IH => -- replace with all_goals later maybe
  by_cases tail = PathIn.nil
  case pos tail_eq_nil =>
    subst tail_eq_nil
    simp [PathIn.toHistory, PathIn.rewind, Fin.lastCases, Fin.reverseInduction]
  case neg tail_ne_nil =>
    have helper : ¬ (1 = Fin.last (List.length (tail.toHistory ++ [X]))) := by
      have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
        simp
        intro con
        have := nil_iff_length_zero.2 con
        simp_all
      intro con
      simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
    simp_all [PathIn.toHistory, PathIn.rewind, Fin.lastCases, Fin.reverseInduction, PathIn.rewind]
    sorry  -- CASE: this is very solvable with IH because the ⟨1,...⟩ is not casting the 1 to zero because tail has length > 0, but how to get lean to understand this...
case pdl Hist X Y nrep bas r next tail IH => -- will be same as loc case
  by_cases tail = PathIn.nil
  case pos tail_eq_nil =>
    subst tail_eq_nil
    simp [PathIn.toHistory, PathIn.rewind, Fin.lastCases, Fin.reverseInduction]
  case neg tail_ne_nil =>
    have helper : ¬ (1 = Fin.last (List.length (tail.toHistory ++ [X]))) := by
      have hyp : ¬ (1 = (List.length tail.toHistory + 1)) := by
        simp
        intro con
        have := nil_iff_length_zero.2 con
        simp_all
      intro con
      simp_all [Fin.last, Fin.eq_mk_iff_val_eq]
    simp_all [PathIn.toHistory, PathIn.rewind, Fin.lastCases, Fin.reverseInduction, PathIn.rewind]
    sorry -- CASTING: same as loc case

-- unique existence?
theorem exists_rewind_of_le {a b : PathIn tab} (h : a ≤ b) : ∃ k, b.rewind k = a := by
induction h
case refl b a_b =>
  use 0
  exact PathIn.rewind_zero
case tail c b a_c c_b ih =>
  have ⟨⟨k_val, k_pf⟩, c_re_k_is_a⟩ := ih
  have k_pf' : k_val + 1 < List.length b.toHistory + 1 := by
    have := edge_inc_length_by_one c_b
    simp_all
  use ⟨k_val + 1, k_pf'⟩
  have b_re_1_is_c := rewind_of_edge_is_eq c_b
  have k_pf'' : k_val < List.length (b.rewind 1).toHistory + 1 := by
    have h : List.length (b.rewind 1).toHistory = List.length c.toHistory := by
      have := edge_inc_length_by_one c_b
      simp_all
    linarith
  have b_re_is_a : (b.rewind 1).rewind ⟨k_val, k_pf''⟩ = a := by
    subst b_re_1_is_c -- eq_of_heq was actually not necessary
    simp_all
  subst b_re_is_a
  exact (rewind_helper k_val k_pf' k_pf'')

theorem not_path_nil {a : PathIn tab} : ¬(a < PathIn.nil) := by
intro con
cases con <;> simp_all [not_edge_nil]

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
        simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
        apply PathIn.loc_le_loc_of_le
        apply IH
        · simp_all
case pdl => -- this is kind of just a copy of loc, maybe there is some all_goals simplification possible
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
        simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
        apply PathIn.pdl_le_pdl_of_le
        apply IH
        · simp_all
case lrep =>
  cases t
  simp only [PathIn.rewind]
  exact Relation.ReflTransGen.refl

theorem PathIn.loc_lt_loc_of_lt {t1 t2} (h : t1 < t2) :
  @loc Hist X Y nrep nbas lt next Z_in t1 < @ loc Hist X Y nrep nbas lt next Z_in t2 := by
apply TransGen.of_reflTransGen (PathIn.loc_le_loc_of_le (Relation.TransGen.to_reflTransGen h))
simp_all
intro con
subst con
exact path_is_irreflexive h

theorem PathIn.pdl_lt_pdl_of_lt {t1 t2} (h : t1 < t2) :
  @pdl Hist X Y nrep bas r Z_in t1 < @pdl Hist X Y nrep bas r Z_in t2 := by
apply TransGen.of_reflTransGen (PathIn.pdl_le_pdl_of_le (Relation.TransGen.to_reflTransGen h))
simp_all
intro con
subst con
exact path_is_irreflexive h

theorem rewind_order_reversing_if_not_nil {t : PathIn tab} {k k' : Fin (List.length t.toHistory + 1)}
  (h : k < k') (h' : t ≠ PathIn.nil) : t.rewind k' < t.rewind k := by
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
        apply TransGen.of_reflTransGen (PathIn.nil_le_anything)
        simp
      case cast j' =>
        have ⟨j'_val, j'_pf⟩ := j'
        have ⟨j_val, j_pf⟩ := j
        simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
        apply PathIn.loc_lt_loc_of_lt
        apply IH
        · simp_all
        · intro con
          subst con
          simp [PathIn.toHistory] at j_pf
          simp [PathIn.toHistory] at j'_pf
          simp_all
case pdl  => -- this is kind of just a copy of loc, maybe there is some all_goals simplification possible
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
        apply TransGen.of_reflTransGen (PathIn.nil_le_anything)
        simp
      case cast j' =>
        have ⟨j'_val, j'_pf⟩ := j'
        have ⟨j_val, j_pf⟩ := j
        simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last]
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

theorem rewind_is_inj {c t : PathIn tab} {k k'} (h1 : t.rewind k = c) (h2 : t.rewind k' = c) : k = k' := by
cases eq_or_ne t PathIn.nil
case inl t_eq_nil =>
  subst t_eq_nil
  have ⟨k'_val, k'_pf⟩ := k'
  have ⟨k_val, k_pf⟩ := k
  simp [PathIn.toHistory] at k'_pf
  simp [PathIn.toHistory] at k_pf
  simp_all
case inr t_ne_nil =>
  apply Fin.le_antisymm
  all_goals
  by_contra hyp
  simp at hyp
  have := rewind_order_reversing_if_not_nil hyp t_ne_nil
  simp_all
  exact path_is_irreflexive this

theorem exists_rewinds_middle {a b c : PathIn tab} (h : a ≤ b) (h' : b ≤ c)
: ∃ k k', c.rewind k = a ∧ c.rewind k' = b ∧ k' ≤ k := by
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
  simp_all
  apply edge.TransGen_isAsymm.1 a b
  apply TransGen.of_reflTransGen h
  intro con
  simp_all
  exact path_is_irreflexive this
  exact this
 simp_all

theorem companion_to_repeat_all_loaded -- NEXT MEET: rewrite using hearts notation?
{l c : PathIn tab}
(lpr : LoadedPathRepeat (tabAt l).fst (tabAt l).snd.fst)
(tabAt_l_def : (tabAt l).snd.snd = Tableau.lrep lpr)
(c_def : c = companionOf l lpr tabAt_l_def)
: ∀ (k : Fin (List.length l.toHistory + 1)), (k.1 ≤ lpr.1.1.succ) → (nodeAt (l.rewind k)).isLoaded := by
intro ⟨k, k_lt_l_len⟩ k_lt_lpr
simp only [PathIn.nodeAt_rewind_eq_toHistory_get]
cases k
case zero => exact (companion_loaded ⟨lpr, tabAt_l_def, c_def⟩).1
case succ k =>
  have hist_eq_path : l.toHistory = (tabAt l).fst := by
    have := PathIn.toHistory_eq_Hist l
    simp_all
  simp [hist_eq_path]
  have ⟨⟨lpr_len, lpr_len_pf⟩, ⟨eq_con, loaded_con⟩⟩ := lpr
  have h1 : k < List.length (tabAt l).fst := by
    simp [←hist_eq_path]
    exact Nat.lt_of_succ_lt_succ k_lt_l_len
  have h2 : k ≤ lpr_len := by
    simp [Fin.lt_def] at k_lt_lpr
    exact k_lt_lpr
  exact loaded_con ⟨k, h1⟩ h2

theorem c_claim {a : Sequent} {tab : Tableau [] a} (t l c : PathIn tab) :
  (nodeAt t).isFree → t < l → l ♥ c → t < c := by
intro t_free t_above_l l_hearts_c
have ⟨lpr, tabAt_l_def, c_def⟩ := l_hearts_c
by_contra hyp
have c_above_l : c < l := lpr_is_lt l_hearts_c
have comp_leq_t : c ≤ t := by
  rcases path_revEuclidean _ _ _ t_above_l c_above_l with h|h|h
  · exact False.elim (hyp h)
  · exact Relation.TransGen.to_reflTransGen h
  · rw [h]
    exact Relation.ReflTransGen.refl
have comp_lt_t : c < t := by
  apply TransGen.of_reflTransGen comp_leq_t
  intro c_eq_t
  have c_loaded := (companion_loaded l_hearts_c).2
  simp [Sequent.isFree] at t_free
  rw [←c_eq_t, c_loaded] at t_free
  contradiction
have ⟨k, k', def_c, def_t, k'_le_k⟩ := exists_rewinds_middle comp_leq_t (Relation.TransGen.to_reflTransGen t_above_l)
have t_loaded : (nodeAt t).isLoaded := by
  rw [←def_t]
  apply companion_to_repeat_all_loaded lpr tabAt_l_def c_def k'
  apply Fin.le_def.1 at k'_le_k
  have k_is_lpr_succ : k.1 = lpr.1.1.succ := by
    have ⟨k_val, k_def⟩ := k
    have ⟨⟨lpr_len, lpr_len_pf⟩, ⟨eq_con, loaded_con⟩⟩ := lpr
    unfold companionOf at c_def
    have := rewind_is_inj (Eq.symm c_def) (def_c)
    simp [Fin.cast] at this
    simp
    rw [←this]
  simp_all
simp [Sequent.isFree] at t_free
rw [t_loaded] at t_free
contradiction

theorem ePropB.c {X} {tab : Tableau .nil X} (s t : PathIn tab) : (nodeAt s).isFree → s < t → s <ᶜ t := by
intro s_free slt
constructor
· apply Relation.TransGen_or_left; exact slt
· intro con
  unfold cEdge at con
  induction con using Relation.TransGen.head_induction_on
  case right.base t hyp =>
    cases hyp
    case inl tes =>
      absurd slt
      exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
    case inr ths =>
      have con := (companion_loaded ths).2
      simp [Sequent.isFree] at s_free
      rw [con] at s_free
      contradiction
  case right.ih t k t_k k_s ih =>
    apply ih
    cases t_k
    case inl tes => exact (Relation.TransGen.trans slt (Relation.TransGen.single tes))
    case inr khs => exact c_claim s t k s_free slt khs

theorem free_or_loaded {a : Sequent} {tab : Tableau [] a} (s : PathIn tab) : (nodeAt s).isFree ∨ (nodeAt s).isLoaded := by
simp_all [Sequent.isFree]

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

theorem not_cEquiv_of_free_loaded (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded: (nodeAt t).isLoaded) :
    ¬ s ≡ᶜ t := by
rintro ⟨s_t, t_s⟩
unfold cEdge at s_t
induction s_t using Relation.ReflTransGen.head_induction_on
case intro.refl =>
  simp [Sequent.isFree] at s_free
  rw [s_free] at t_loaded
  contradiction
case intro.head s l s_l l_t ih =>
  cases free_or_loaded l
  case inl l_free => exact ih l_free (Relation.ReflTransGen.tail t_s s_l)
  case inr l_loaded =>
    cases s_l
    case inl sel =>
      have scl := ePropB.c s l s_free (Relation.TransGen.single sel)
      absurd scl.2
      have l_s : l ◃* s := Relation.ReflTransGen.trans l_t t_s
      cases eq_or_ne l s
      case inl les =>
        have := edge_is_strict_ordering sel
        simp_all
      case inr lnes => exact TransGen.of_reflTransGen l_s lnes
    case inr shl =>
      have con := (companion_loaded shl).1
      simp [Sequent.isFree] at s_free
      rw [con] at s_free
      contradiction

  theorem ePropB.d {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt t).isFree → s < t → s <ᶜ t := by
intro t_free
intro slt
constructor
· apply Relation.TransGen_or_left; exact slt
· intro con
  unfold cEdge at con
  induction con using Relation.TransGen.head_induction_on
  case right.base t hyp =>
    cases hyp
    case inl tes =>
      absurd slt
      exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
    case inr ths =>
      have con := (companion_loaded ths).1
      simp [Sequent.isFree] at t_free
      rw [con] at t_free
      contradiction
  case right.ih t k t_k k_s ih =>
    cases free_or_loaded k
    case inl k_free =>
      cases t_k
      case inl tek => exact ih k_free (Relation.TransGen.tail slt tek)
      case inr thk =>
        have con := (companion_loaded thk).1
        simp [Sequent.isFree] at t_free
        rw [con] at t_free
        contradiction
    case inr k_loaded =>
      apply not_cEquiv_of_free_loaded t k t_free k_loaded
      constructor
      · exact Relation.ReflTransGen.single t_k
      · exact Relation.ReflTransGen.trans (Relation.TransGen.to_reflTransGen k_s) (Relation.ReflTransGen_or_left (Relation.TransGen.to_reflTransGen slt))

-- do we still need this?
theorem ePropB.c_single {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s ⋖_ t → s <ᶜ t := by
  intro s_free t_childOf_s
  apply ePropB.c _ t s_free
  apply Relation.TransGen.single; exact t_childOf_s

-- Unused?
theorem ePropB.e {tab : Tableau .nil X} (s t : PathIn tab) :
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
theorem ePropB.e_help {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt t).isLoaded → (nodeAt s).isFree → t ◃⁺ s → ¬ (s ◃⁺ t) := by
  intro t_loaded s_free t_s
  intro s_t
  absurd not_cEquiv_of_free_loaded _ _ s_free t_loaded
  constructor <;> apply Relation.TransGen.to_reflTransGen <;> assumption

-- Unused?
/-- <ᶜ is transitive -/
theorem ePropB.f {tab : Tableau .nil X} (s u t : PathIn tab) :
    s <ᶜ u  →  u <ᶜ t  →  s <ᶜ t := by
  rintro ⟨s_u, _⟩ ⟨u_t, not_u_t⟩
  constructor
  · exact Relation.TransGen.trans s_u u_t
  · intro t_s
    absurd not_u_t
    apply Relation.TransGen.trans t_s s_u

theorem ePropB.g {tab : Tableau .nil X} (s t : PathIn tab) :
    t ◃⁺ s  →  ¬ t ≡ᶜ s  →  t <ᶜ s := by
  rintro s_c_t s_nequiv_t
  constructor
  · exact s_c_t
  · intro t_c_s
    absurd s_nequiv_t
    constructor
    · exact Relation.TransGen.to_reflTransGen s_c_t
    · exact Relation.TransGen.to_reflTransGen t_c_s

-- Not in notes
theorem ePropB.g_tweak {tab : Tableau .nil X} (s u t : PathIn tab) :
    s ◃⁺ u  →  u ◃⁺ t  →  ¬ t ≡ᶜ u → ¬ t ≡ᶜ s := by
  intro s_u u_t not_t_u
  intro t_s
  absurd not_t_u
  constructor
  · apply @Relation.ReflTransGen.trans _ _ _ _ _ t_s.1
    exact Relation.TransGen.to_reflTransGen s_u
  · exact Relation.TransGen.to_reflTransGen u_t

theorem ePropB.h {tab : Tableau .nil X} (s t : PathIn tab) :
    (s <ᶜ t → ¬ s ≡ᶜ t) := by
  intro s_lt_t
  rintro ⟨-, t_to_s⟩
  rcases s_lt_t with ⟨s_steps_t', not_t_steps_s⟩
  absurd not_t_steps_s
  by_cases s = t
  · simp_all
  · rw [@Relation.reflTransGen_iff_eq_or_transGen] at t_to_s
    simp_all

theorem ePropB.i {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s <ᶜ u  →  s ≡ᶜ t  →  t <ᶜ u) := by
  rintro s_c_y s_equiv_t
  rcases s_c_y with ⟨s_u, not_u_s⟩
  rcases s_equiv_t with ⟨-, t_to_s⟩
  constructor
  · exact Relation.TransGen.trans_right t_to_s s_u
  · intro u_to_t
    absurd not_u_s
    exact Relation.TransGen.trans_left u_to_t t_to_s

theorem ePropB {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s ⋖_ t → (s <ᶜ t) ∨ (t ≡ᶜ s)) -- a
  ∧ (s ♥ t → t ≡ᶜ s) -- b
  ∧ ((nodeAt s).isFree → s < t → s <ᶜ t) -- c
  ∧ ((nodeAt t).isFree → s < t → s <ᶜ t) -- d
  ∧ ((nodeAt s).isLoaded → (nodeAt t).isFree → s ⋖_ t → s <ᶜ t) -- e
  ∧ (s <ᶜ u → u <ᶜ t → s <ᶜ t) -- f
  ∧ (t ◃⁺ s  →  ¬ t ≡ᶜ s  →  t <ᶜ s) -- g
  ∧ (s <ᶜ t → ¬ s ≡ᶜ t) -- h
  ∧ (s <ᶜ u  →  s ≡ᶜ t  →  t <ᶜ u) -- i
  :=
  ⟨ ePropB.a s t, ePropB.b s t, ePropB.c s t
  , ePropB.d s t, ePropB.e s t, ePropB.f s u t
  , ePropB.g s t, ePropB.h s t, ePropB.i s u t⟩

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
        have := X_isBasic.1 (~lf.1.unload)
        simp at this
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
-- findme2

theorem loadedDiamondPathsM (α : Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  {side : Side} -- NOT in notes but needed for partition.
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side (nodeAt t)) -- M: why two '' after ~?
  (v_α_w : relate M α v w)
  (w_nξ : (M,w) ⊨ ~''ξ)
  : ∃ s : PathIn tab, t ◃⁺ s ∧ (satisfiable (nodeAt s)) ∧
    ( ¬ (s ≡ᶜ t)
      ∨ ( ((~''ξ).in_side side (nodeAt s))
        ∧ (M,w) ⊨ (nodeAt s)
        ∧ ((nodeAt s).without (~''ξ)).isFree
        )
    ) := by
  sorry

-- TODO: missing here: path from t to s is satisfiable!
-- FIXME: move satisfiable outside disjunction?

theorem loadedDiamondPaths (α : Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)       -- M: Why is this called PathIn tab? t is a node.
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  {side : Side} -- NOT in notes but needed for partition. M: What is this?
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side (nodeAt t)) -- M: why two '' after ~?
                                                     -- M: where do we say [α] loaded?
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

  -- inner induction is on the path (in Notes this is a separate Lemma , going from t to t') M: Lemma 5.2
  induction' t_def : t using PathIn.init_inductionOn -- MQuestion: I don't understand this induction
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
      · -- using ePropB here
        unfold cEquiv
        simp
        have := ePropB.e t s1 (Sequent.isLoaded_of_negAnyFormula_loaded negLoad_in) ?_ t_s
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

      -- Claim for an inner induction on the list δ. -- Extended Induction Hypothesis is herre

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
              -- ! Needs better `H_goes_down` similar to `PgoesDown`.
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
              · apply ePropB.g_tweak _ _ _ t_sk sk_c_sk2 sk2_nEquiv_sk
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

    case modL L R a ξ' Z_def =>
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
        let tclean : PathIn (.pdl nrep bas (.modL (Eq.refl _)) next) := .pdl .nil
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
        refine ⟨Hist, _, nrep, bas, _, (.modL Z_def), next, tabAt_t_def, ?_⟩
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

    case modR L R a ξ' Z_def => -- COPY ADAPTATION from `modL`
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
        let tclean : PathIn (.pdl nrep bas (.modR (Eq.refl _)) next) := .pdl .nil
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
        refine ⟨Hist, _, nrep, bas, _, (PdlRule.modR Z_def), next, tabAt_t_def, ?_⟩
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

  case lrep lpr =>
    -- Here we need to go to the companion.
    -- IDEA: make a recursive call, and for termination note that the path becomes shorter?
    have h : (tabAt t).snd.snd = .lrep (tabAt_t_def ▸ lpr) := by
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
      exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inr t_comp_u)) u_s not_s_u
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
    case lrep lpr => -- Then t cannot be a LPR.
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
      apply ePropB.c_single t _ t_is_free t_s
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
      apply ePropB.c_single t _ t_is_free t_s
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
          exact ePropB.g s t t_to_s hyp
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
          -- Remains to show that s is simpler than t. We use ePropB.
          constructor
          · exact t_to_s
          · have : (nodeAt t).isLoaded := by
              unfold Sequent.isLoaded
              simp [AnyNegFormula.in_side] at in_t
              aesop
            apply ePropB.e_help _ _ this rest_s_free t_to_s
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
          absurd IH s (ePropB.g s t t_to_s (by rw [cEquiv.symm]; exact notequi))
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
