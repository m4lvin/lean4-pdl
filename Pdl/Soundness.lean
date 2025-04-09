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
    s.rewind ((tabAt_fst_length_eq_toHistory_length s ▸ lpr.val).succ)

/-- `s ♥ t` means `s` is a `LoadedPathRepeat` and the `companionOf s` is `t`. -/
def companion {X} {tab : Tableau .nil X} (s t : PathIn tab) : Prop :=
  ∃ (lpr : _) (h : (tabAt s).2.2 = .lrep lpr), t = companionOf s lpr h

notation pa:arg " ♥ " pb:arg => companion pa pb

/-- The node at a companion is the same as the one in the history. -/
theorem nodeAt_companionOf_eq_toHistory_get_lpr_val (s : PathIn tab) lpr h :
    nodeAt (companionOf s lpr h)
    = s.toHistory.get (tabAt_fst_length_eq_toHistory_length s ▸ lpr.val) := by
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


-- MQuestion: why not use r-t closure like in notes?

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
    have := PathIn.rewind_le s ((tabAt_fst_length_eq_toHistory_length s ▸ lpr.val).succ)
    simp only [LE.le, instLEPathIn] at this
    exact Relation.ReflTransGen_or_left this
  · unfold cEdge
    apply Relation.ReflTransGen_or_right
    exact Relation.ReflTransGen.single comp

theorem vector_tail_head {α : Type} {n : ℕ} (ys : List.Vector α n.succ) : ys.head = ys.get 0 := by sorry

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

theorem oneStep_free_loaded_back_path_no {a : Sequent} {tab : Tableau [] a}
    (s t : PathIn tab)
    (s_free : (nodeAt s).isFree)
    (t_loaded : (nodeAt t).isLoaded)
    (m : ℕ)
    (single_rel : s ◃ t)
    (vs : List.Vector (PathIn tab) m.succ)
    (t_is_z0 : t = vs.head)
    (s_is_zn : s = vs.last)
    (v_rel : ∀ (i : Fin m), (vs.get i.castSucc) ◃ (vs.get i.succ))
    : False := by
    -- but is this easier to show now?!
    induction m generalizing t s
    · have : t = s := by
        rcases vs with ⟨_|⟨v,vs⟩, vs_h⟩
        · exfalso; cases vs_h
        · rcases vs with (_|_)
          · simp_all [List.Vector.head, List.Vector.last]
          · cases vs_h
      simp_all [Sequent.isFree]
    case succ m ih =>
      let l : PathIn tab := List.Vector.get vs 1
      let us : List.Vector (PathIn tab) m.succ := vs.tail
      have l_is_u0 : l = us.head := by apply Vector.my_get_one_eq_tail_head
      have s_is_uk : s = us.last := by unfold us; simp [s_is_zn, Vector.last_eq_tail_last]
      have u_rel : ∀ (i : Fin m), (us.get i.castSucc) ◃ (us.get i.succ) := by
        intro i
        unfold us
        simp [us, vector_tail_get]
        exact v_rel i.succ
      sorry

theorem not_cEquiv_of_free_loaded_helper {a : Sequent} {tab : Tableau [] a}
    (s t : PathIn tab)
    (s_free : (nodeAt s).isFree)
    (t_loaded : (nodeAt t).isLoaded)
    (n m : ℕ) :
    ∀
    (ys : List.Vector (PathIn tab) n.succ)
    (s_is_y0 : s = ys.head)
    (t_is_yn : t = ys.last)
    (y_rel : ∀ (i : Fin n), (ys.get i.castSucc) ◃ (ys.get i.succ))
    (zs : List.Vector (PathIn tab) m.succ)
    (t_is_z0 : t = zs.head)
    (s_is_zn : s = zs.last)
    (z_rel : ∀ (i : Fin m), (zs.get i.castSucc) ◃ (zs.get i.succ)),
    False := by
  -- Madeleine: We dont need induction just cases? since we use strong induction anyways.
  -- Malvin: Yes, rewritten with cases now, but also adding `n_def` to remember `n`.
  cases n_def : n
  <;> intro ys s_is_y0 t_is_yn y_rel zs t_is_z0 s_is_zn z_rel -- do it in both cases.
  case zero =>
    -- Madeleine: There has to be a shorter way of handling this case
    -- Malvin: shortened a bit, avoid calc
    have : ys.last = ys.head := by rw [List.Vector.last]; simp
    simp_all [Sequent.isLoaded, Sequent.isFree]
  case succ k =>
    let l : PathIn tab := List.Vector.get ys 1
    by_cases l_free : (nodeAt l).isFree
    · let us : List.Vector (PathIn tab) k.succ := ys.tail
      have l_is_u0 : l = us.head := by apply Vector.my_get_one_eq_tail_head
      have t_is_uk : t = us.last := by unfold us; simp [t_is_yn, Vector.last_eq_tail_last]
      have u_rel : ∀ (i : Fin k), (us.get i.castSucc) ◃ (us.get i.succ) := by
        intro i
        unfold us
        simp [us, vector_tail_get]
        exact y_rel i.succ
      let vs : List.Vector (PathIn tab) (m + 1).succ := List.Vector.append zs (List.Vector.cons l List.Vector.nil)
      have t_is_v0 : t = vs.head := by
        -- Malvin: here is a solution for one of the easy cases.
        -- This is "taking apart" the vector into a list and the proof of its length.
        rcases zs with ⟨_|_, h⟩; exfalso; cases h; aesop
      have l_is_vm1 : l = vs.last := by unfold vs --- same issue
                                        sorry
      have v_rel : ∀ (i : Fin (m + 1)), (vs.get i.castSucc) ◃ (vs.get i.succ) := by
        subst_eqs
        apply Fin.cases -- Malvin: does this help?
        · simp [vs]
          sorry
        · sorry
      -- Malvin: Instead of IH, make a recursive call here:
      -- Malvin: Crucial is that we go down from   n = k + 1  to  k  here.
      apply not_cEquiv_of_free_loaded_helper l t l_free t_loaded k (m + 1) us l_is_u0 t_is_uk u_rel vs t_is_v0 l_is_vm1 v_rel
    · --- same idea as inl, so skipping until I work out inl
      simp [Sequent.isFree] at l_free
      rename (nodeAt l).isLoaded = true => l_loaded
      have us : List.Vector (PathIn tab) 2 := by sorry
      have s_is_u0 : s = us.head := by sorry
      have l_is_uk : l = us.last := sorry
      have u_rel : ∀ (i : Fin 1), (us.get i.castSucc) ◃ (us.get i.succ) := by sorry
      have vs : List.Vector (PathIn tab) (m + k).succ := by sorry
      have l_is_v0 : l = vs.head := by sorry
      have s_is_vmk : s = vs.last := by sorry
      have v_rel : ∀ (i : Fin (m + k)), (vs.get i.castSucc) ◃ (vs.get i.succ) := by sorry
      -- Madeleine did convince Malvin: We want n=1 here.
      -- Appeal to separate lemma for this, not recursion.
      apply oneStep_free_loaded_back_path_no s l s_free l_loaded (m + k) ?_ vs l_is_v0 s_is_vmk v_rel
      rw [s_is_u0, l_is_uk]
      convert u_rel 0
      simp
-- no more termination hints needed then.

/-- A free node and a loaded node cannot be ≡ᶜ equivalent. -/
theorem not_cEquiv_of_free_loaded' (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded: (nodeAt t).isLoaded) :
    ¬ s ≡ᶜ t := by
rintro ⟨s_t, t_s⟩
rcases ReflTransGen.to_finitelyManySteps s_t with ⟨n,ys,y0,yn,y_rel⟩
rcases ReflTransGen.to_finitelyManySteps t_s with ⟨m,zs,z0,zn,z_rel⟩
exact not_cEquiv_of_free_loaded_helper s t s_free t_loaded n m ys y0 yn y_rel zs z0 zn z_rel

-- findme3

-- TODO IMPORTANT
theorem ePropB.c' {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s < t → s <ᶜ t := by
  intro s_free t_path_s
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


-- START HERE
lemma unique_paths {a : Sequent} {tab : Tableau [] a}
    (t l : PathIn tab) (h : t < l) :
    ∃! n, ∃! ys : List.Vector _ _,
      t = ys.head ∧ l = ys.last ∧ ∀ (i : Fin n), (ys.get i.castSucc) ⋖_ (ys.get i.succ)
      := by
  sorry

-- FIXME move to TableauPath.lean later
lemma edge_revEuclidean (a b c : PathIn tab) :
    a < c → b < c → (a < b ∨ b < a ∨ b = a) := by
  sorry
lemma edge_revEuclidean' (a b c : PathIn tab) :
    a < c → b < c → (a ≤ b ∨ b ≤ a) := by
  sorry

theorem lpr_is_lt {a : Sequent} {tab : Tableau [] a}
    (l c : PathIn tab)
    (lpr : LoadedPathRepeat ((tabAt l).1) ((tabAt l).2.1))
    (tabAt_l_def : (tabAt l).2.2 = Tableau.lrep lpr)
    (c_def : c = companionOf l lpr tabAt_l_def)
    : c < l := by
  rw [c_def]
  unfold companionOf
  have := @PathIn.rewind_lt_of_gt_zero -- need something like that but without length
  sorry

theorem c_claim {a : Sequent} {tab : Tableau [] a}
    (t l c : PathIn tab)
    (t_above_l : t < l)
    (t_free : (nodeAt t).isFree)
    (lpr : LoadedPathRepeat ((tabAt l).1) ((tabAt l).2.1))
    (tabAt_l_def : (tabAt l).2.2 = Tableau.lrep lpr)
    (c_def : c = companionOf l lpr tabAt_l_def)
    : t < c := by
  by_contra hyp
  have c_above_l : c < l := lpr_is_lt l c lpr _ c_def
  have comp_le_t : c ≤ t := by
    rcases edge_revEuclidean _ _ _ t_above_l c_above_l with h|h|h
    · exact False.elim (hyp h)
    · exact Relation.TransGen.to_reflTransGen h
    · rw [h]
      exact Relation.ReflTransGen.refl
  have := unique_paths _ _ c_above_l
  -- want to show: all elements of ys are loaded (because from lpr) -- needs better unique_paths
  -- want: t is inside ys
  sorry

theorem ePropB.c {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s < t → s <ᶜ t := by
    intro s_free slt
    constructor
    · apply Relation.TransGen_or_left; exact slt
    · intro con
      unfold cEdge at con
      induction con using Relation.TransGen.head_induction_on
      case right.base t hyp => cases hyp with
        | inl tes => absurd slt
                     exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
        | inr ths => have con := (companion_loaded ths).2
                     simp [Sequent.isFree] at s_free
                     rw [con] at s_free
                     contradiction
      case right.ih t k t_k k_s ih => cases t_k with
        | inl tes => apply ih
                     exact (Relation.TransGen.trans slt (Relation.TransGen.single tes))
        | inr khs => apply ih
                     unfold companion at khs
                     have ⟨lpr, h, kch⟩ := khs
                     apply c_claim s t k slt s_free
                     · sorry --- something in statement of c_claim is clashing here?
                     · exact lpr
                     · exact h

theorem free_or_loaded {a : Sequent} {tab : Tableau [] a} (s : PathIn tab) : (nodeAt s).isFree ∨ (nodeAt s).isLoaded
  :=  by simp_all [Sequent.isFree]


theorem TransGen.of_reflTransGen {α : Type} {r : α → α → Prop}
  (a b : α) (h : Relation.ReflTransGen r a b) (hne : a ≠ b) : Relation.TransGen r a b :=
  by
   induction h with
   | refl => contradiction
   | tail a_b b_c ih => sorry -- variable names are innaccessible??

theorem edge_is_strict_ordering {s t : PathIn tab} : s ⋖_ t → s ≠ t :=
by
  intro s_t set
  have := edge_then_length_lt s_t
  simp_all

  theorem path_is_strict_ordering {s t : PathIn tab} : s < t → s ≠ t :=
by
  intro s_t seqt
  induction s_t with
  | single set => absurd seqt
                  exact edge_is_strict_ordering set
  | tail a b ih => sorry -- same issue? variable names are innaccessible??

theorem not_cEquiv_of_free_loaded (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded: (nodeAt t).isLoaded) :
    ¬ s ≡ᶜ t := by
rintro ⟨s_t, t_s⟩
unfold cEdge at s_t
induction s_t using Relation.ReflTransGen.head_induction_on
case intro.refl => simp [Sequent.isFree] at s_free
                   rw [s_free] at t_loaded
                   contradiction
case intro.head s l s_l l_t ih => cases free_or_loaded l with
  | inl l_free => exact ih l_free (Relation.ReflTransGen.tail t_s s_l)
  | inr l_loaded => cases s_l with
                    | inl sel => have scl : s <ᶜ l := by exact ePropB.c s l s_free (Relation.TransGen.single sel)
                                 absurd scl.2
                                 have l_s : l ◃* s := Relation.ReflTransGen.trans l_t t_s
                                 cases eq_or_ne l s with
                                 | inl les => have := edge_is_strict_ordering sel
                                              simp_all
                                 | inr lnes => exact TransGen.of_reflTransGen l s l_s lnes
                    | inr shl => have con := (companion_loaded shl).1
                                 simp [Sequent.isFree] at s_free
                                 rw [con] at s_free
                                 contradiction

theorem ePropB.d {tab : Tableau .nil X} (s t : PathIn tab) : -- M
    (nodeAt t).isFree → s < t → s <ᶜ t := by
  intro t_free
  intro slt
  constructor
  · apply Relation.TransGen_or_left; exact slt
  · intro con
    have t_neq_s : t ≠ s := by have := path_is_strict_ordering slt
                               intro t_eq_s
                               simp_all
    have t_s : t ◃* s := Relation.TransGen.to_reflTransGen con
    rcases ReflTransGen.to_finitelyManySteps t_s with ⟨n,ys,ys0,ysn,ys_rel⟩
    have h : ∀ (i : Fin n), (ys.get i.castSucc) ⋖_ (ys.get i.succ) :=
      by intro i
         have y_y' := ys_rel i
         cases y_y' with
         | inl yey' => exact yey'
         | inr yhy' => sorry -- this is so doable since we have t free, y loaded and t ◃⁺ y and y ◃⁺ t, so not_cEquiv_of_free_loaded2 gives contradiction
    have t_patheq_s : t ≤ s := by apply ReflTransGen.from_finitelyManySteps edge t s ys ⟨ys0 ,⟨ysn, h⟩⟩
    have t_path_s : t < s := TransGen.of_reflTransGen t s t_patheq_s t_neq_s
    absurd slt
    exact edge.TransGen_isAsymm.1 t s t_path_s

-- END HERE

theorem ePropB.c_single {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s ⋖_ t → s <ᶜ t := by
  intro s_free t_childOf_s
  apply ePropB.c _ t s_free
  apply Relation.TransGen.single; exact t_childOf_s


theorem ePropB.d' {tab : Tableau .nil X} (s t : PathIn tab) : -- M
    (nodeAt t).isFree → s < t → s <ᶜ t := by
  intro t_free
  intro slt
  constructor
  · apply Relation.TransGen_or_left; exact slt
  · intro con
    unfold cEdge at con
    induction con using Relation.TransGen.head_induction_on
    case right.base t t_s => cases t_s with
      | inl tes => absurd slt
                   exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
      | inr ths => have con := (companion_loaded ths).1
                   simp [Sequent.isFree] at t_free
                   rw [con] at t_free
                   contradiction
    case right.ih t k t_k k_s ih => cases t_k with
      | inl kes => apply ih
                   · sorry
                   · exact (Relation.TransGen.trans slt (Relation.TransGen.single kes))
      | inr khs => have con := (companion_loaded khs).1
                   exfalso
                   simp [Sequent.isFree] at t_free
                   rw [con] at t_free
                   contradiction


theorem ePropB.d'' {tab : Tableau .nil X} (s t : PathIn tab) : -- M
    (nodeAt t).isFree → s < t → s <ᶜ t := by
  intro t_free
  intro slt
  constructor
  · apply Relation.TransGen_or_left; exact slt
  · intro con
    unfold cEdge at con
    induction con
    case single s t_s => cases t_s with
      | inl tes => absurd slt
                   exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
      | inr ths => have con := (companion_loaded ths).1
                   simp [Sequent.isFree] at t_free
                   rw [con] at t_free
                   contradiction
    case tail k s t_k k_s ih => cases k_s with
      | inl kes => apply ih
                   exact (Relation.TransGen.trans (Relation.TransGen.single kes) slt)
      | inr khs => sorry

-- theorem minduction
--   {α : Sort u} {r : α → α → Prop} {a b : α}
--   (P : ∀ b : α, Relation.TransGen r a b  → Prop)
--   (h : Relation.TransGen r a b)
--   (head : r a b → P b h)
--   (tail : ∀ c (hs : r a c) (ht : Relation.TransGen r c b), P b (Relation.TransGen.trans (Relation.TransGen.single hs) ht) → P b h) : P b h :=
-- by
--   induction h
--   case single b hyp =>
--       exact head hyp
--   case tail b c aRtb bRc ih =>
--       apply ih
--       · exact fun h ↦ tail h (single hbc) (base hbc)
--       · exact fun hab hbc ↦ ih hab _

-- theorem ePropB.dM {tab : Tableau .nil X} (s t : PathIn tab) : -- M
--     (nodeAt t).isFree → s < t → s <ᶜ t := by
--   intro t_free
--   intro slt
--   constructor
--   · apply Relation.TransGen_or_left; exact slt
--   · intro con
--     have := minduction (fun b aRb ↦ False) (con) (by
--       intro h1
--       cases h1 with
--         | inl tes => absurd slt
--                      exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
--         | inr ths => have con := (companion_loaded ths).1
--                      simp [Sequent.isFree] at t_free
--                      rw [con] at t_free
--                      contradiction
--     ) (by
--       intro k t_k k_s ih
--       cases t_k with
--       | inl tek => absurd ih
--                    exact Relation.TransGen.tail (slt) (tek)
--       | inr thk => have con := (companion_loaded thk).1
--                    simp [Sequent.isFree] at t_free
--                    rw [con] at t_free
--                    contradiction)
--     absurd slt
--     exact this



/-- A free node and a loaded node cannot be ≡ᶜ equivalent. -/
theorem not_cEquiv_of_free_loaded'' (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded: (nodeAt t).isLoaded) : ¬ s ≡ᶜ t := by
  rintro ⟨s_t, t_s⟩
  induction s_t using Relation.ReflTransGen.head_induction_on
  · simp [Sequent.isFree] at *
    simp_all
  case head u v u_v v_t IH =>
    cases u_v -- normal edge or companion edge?
    case inl u_v =>
      rcases ePropB.c_single u v s_free u_v with ⟨-, not_v_u⟩
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

-- MQuestion: π in notes
-- MQuestion: what is side:Side about?
-- M: Why is this called PathIn tab? t is a node.
-- MQuestion: formulation is wrong?
-- MQuestion: Where do we say [α] loaded?
-- MQuestion: We need to say that the entire path is satisfiable
-- MQuestion: Extended Induction Hypothesis

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
