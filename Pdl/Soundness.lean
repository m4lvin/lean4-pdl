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

theorem companion_lt {l c : PathIn tab} : l ♥ c → c < l := by
  intro l_hearts_c
  have ⟨lpr, tabAt_l_def, c_def⟩ := l_hearts_c
  rw [c_def]
  unfold companionOf
  apply PathIn.rewind_lt_of_gt_zero l _ _
  simp

/-- The node at a companion is the same as the one in the history. -/
theorem nodeAt_companionOf_eq_toHistory_get_lpr_val (s : PathIn tab) lpr h :
    nodeAt (companionOf s lpr h)
    = s.toHistory.get (Fin.cast (tabAt_fst_length_eq_toHistory_length s) lpr.val) := by
  unfold companionOf
  rw [PathIn.nodeAt_rewind_eq_toHistory_get]
  simp

theorem nodeAt_companionOf_multisetEq {tab : Tableau .nil X} (s : PathIn tab) lpr
    (h : (tabAt s).2.2 = .lrep lpr)
    : (nodeAt (companionOf s lpr h)).multisetEqTo (nodeAt s) := by
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
  apply PathIn.rewind_length_lt_length_of_gt_zero
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

theorem ePropB.b {tab : Tableau .nil X} (s t : PathIn tab) :
    s ♥ t → t ≡ᶜ s := by
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


/-- Not using ♥ here because we need to refer to the `lpr`. -/
theorem companion_to_repeat_all_loaded
    {l c : PathIn tab}
    (lpr : LoadedPathRepeat (tabAt l).fst (tabAt l).snd.fst)
    (tabAt_l_def : (tabAt l).snd.snd = Tableau.lrep lpr)
    (c_def : c = companionOf l lpr tabAt_l_def)
    : ∀ (k : Fin (List.length l.toHistory + 1)),
      (k.1 ≤ lpr.1.1.succ) → (nodeAt (l.rewind k)).isLoaded := by
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
have c_above_l : c < l := companion_lt l_hearts_c
have comp_leq_t : c ≤ t := by
  rcases path_revEuclidean _ _ _ t_above_l c_above_l with h|h|h
  · exact False.elim (hyp h)
  · exact Relation.TransGen.to_reflTransGen h
  · rw [h]
    exact Relation.ReflTransGen.refl
have comp_lt_t : c < t := by
  apply Relation.TransGen_of_ReflTransGen comp_leq_t
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
    rw [c_def] at def_c
    have := rewind_is_inj def_c
    simp [Fin.cast] at this
    exact this
  simp_all
simp [Sequent.isFree] at t_free
rw [t_loaded] at t_free
contradiction

theorem ePropB.c {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s < t → s <ᶜ t := by
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
        case inr lnes => exact Relation.TransGen_of_ReflTransGen l_s lnes
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

-- Other Lemma idea: if α is atomic, and ~''(⌊α⌋ξ) is in t, then if we make a local tableau for t, the loaded diamond must still be in all endNodesOf it.

theorem atomicLocalLoadedDiamond (α : Program) {X : Sequent}
  (ltab : LocalTableau X)
  (α_atom : α.isAtomic)
  (ξ : AnyFormula)
  {side : Side}
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side X)
  : ∀ Y ∈ endNodesOf ltab, (~''(⌊α⌋ξ)).in_side side Y := by
  intro Y Y_in
  induction ltab
  case byLocalRule X B lra next IH =>
    rcases X with ⟨L, R, O⟩
    rcases lra with ⟨Lcond, Rcond, Ocond, r, precons⟩
    rename_i resNodes B_def_apply_r_LRO
    cases r
    case oneSidedL resNodes orule =>
      simp_all
      have ⟨A, ⟨⟨Z, ⟨⟨Γ, ⟨Γ_in, Z_def⟩⟩, A_def⟩⟩, Y_in_A⟩⟩ := Y_in
      apply IH Z Γ ⟨Γ_in, Z_def⟩
      · subst Z_def
        cases side
        all_goals
        simp [AnyNegFormula.in_side] at *
        exact negLoad_in
      · simp [Y_in_A, A_def]
    case oneSidedR resNodes orule =>
      simp_all
      have ⟨A, ⟨⟨Z, ⟨⟨Γ, ⟨Γ_in, Z_def⟩⟩, A_def⟩⟩, Y_in_A⟩⟩ := Y_in
      apply IH Z Γ ⟨Γ_in, Z_def⟩
      · subst Z_def
        cases side
        all_goals
        simp [AnyNegFormula.in_side] at *
        exact negLoad_in
      · simp [Y_in_A, A_def]
    case LRnegL φ => simp_all
    case LRnegR φ => simp_all
    case loadedL outputs χ lrule =>
      simp_all
      have ⟨A, ⟨⟨Z, ⟨⟨Γ, ⟨Δ, ⟨cond, Z_def⟩⟩⟩, A_def⟩⟩, Y_in_A⟩⟩ := Y_in
      apply IH Z Γ Δ ⟨cond, Z_def⟩
      · subst Z_def
        cases side
        case LL =>
          simp only [AnyNegFormula.in_side] at *
          simp [negLoad_in] at precons
          subst precons
          cases lrule <;> simp_all
        case RR =>
          simp [AnyNegFormula.in_side] at *
          rw [negLoad_in]
          simp_all
      · simp [Y_in_A, A_def]
    case loadedR outputs χ lrule =>
      simp_all
      have ⟨A, ⟨⟨Z, ⟨⟨Γ, ⟨Δ, ⟨cond, Z_def⟩⟩⟩, A_def⟩⟩, Y_in_A⟩⟩ := Y_in
      apply IH Z Γ Δ ⟨cond, Z_def⟩
      · subst Z_def
        cases side
        case LL =>
          simp [AnyNegFormula.in_side] at *
          rw [negLoad_in]
          simp_all [Olf.change, Option.overwrite, Option.map, sdiff]
        case RR =>
          simp [AnyNegFormula.in_side]
          simp [AnyNegFormula.in_side] at negLoad_in
          simp [negLoad_in] at precons
          subst precons
          cases lrule <;> simp_all
      · simp [Y_in_A, A_def]
  case sim X X_isBasic =>
    simp [endNodesOf] at Y_in
    subst Y_in
    exact negLoad_in

-- TODO: move to UnfoldDia.lean later
def Hl : List Program → List (List Formula × List Program)
| [] => [([],[])]
| [α] => H α
| α :: rest => (H α).flatMap (fun ⟨F,δ⟩ => -- inspired by `;` case of `H`
            if δ = []
              then ((Hl rest).flatMap (fun ⟨G,δ'⟩ => [⟨F ∪ G, δ'⟩]))
              else [⟨F, δ ++ rest⟩])

@[simp]
lemma Hl_singleton : Hl [α] = H α := by simp [Hl]

@[simp]
lemma Hl_atomic_cons : Hl (·a :: αs) =  [ ([], ((·a : Program) :: αs)) ] := by
  unfold Hl
  cases αs <;> simp_all [H]

@[simp]
lemma next_exists_avoid_def_l {B : List Sequent} (next : (Y : Sequent) → Y ∈ B → LocalTableau Y) :
    (∃ l, (∃ a, ∃ (h : a ∈ B), endNodesOf (next a h) = l) ∧ Y ∈ l)
    ↔ ∃ Z, ∃ Z_in : Z ∈ B, Y ∈ endNodesOf (next Z Z_in) := by
  aesop

lemma lra_preserves_free (lra : LocalRuleApp X B) (Z_in : Z ∈ B) (X_free : X.isFree) :
    Z.isFree := by
  -- We distinguish which rule was applied.
  rcases X with ⟨L,R,O⟩
  rcases lra with ⟨Lcond, Rcond, Ocond, r, precons⟩
  rename_i resNodes B_def_apply_r_LRO
  unfold Sequent.isFree Sequent.isLoaded
  rcases Z with ⟨ZL, ZR, _|(nlf|nlf)⟩ <;> rcases O with (_|(nlf|nlf)) <;> simp_all
  all_goals
    cases r
    case oneSidedR resNodes orule =>
      cases orule <;> simp_all <;> subst_eqs
      · cases Z_in <;> rename_i h <;> cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
    case oneSidedL resNodes orule =>
      cases orule <;> simp_all <;> subst_eqs
      · cases Z_in <;> rename_i h <;> cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
      · rcases Z_in with ⟨q, _, h⟩; cases h
    all_goals
      simp_all

lemma endNodesOf_free_are_free {X Y} (ltX : LocalTableau X) (h : X.isFree)
    (Y_in : Y ∈ endNodesOf ltX) : Y.isFree := by
  induction ltX
  case byLocalRule X B lra next IH =>
    rcases X with ⟨L,R,O⟩
    simp_all
    rcases Y_in with ⟨Z, Z_in_B, Y_in⟩
    apply IH Z Z_in_B ?_ Y_in
    -- remains to show that Z is free
    apply lra_preserves_free lra Z_in_B h
  case sim =>
    simp_all

-- TODO find better home
@[simp]
lemma whatever :
      (~(⌊α⌋  AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)
    = (~ ⌈α⌉((AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)) := by
  cases αs <;> simp_all [AnyFormula.loadBoxes, AnyFormula.unload]

-- TODO find better home
lemma loaded_eq_to_unload_eq χ αs φ
    (h : AnyFormula.loaded χ = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : χ.unload = ⌈⌈αs⌉⌉φ
    := by
  cases αs
  · simp_all
  case cons α1 αs =>
    cases αs
    · simp_all
    case cons α2 αs =>
      simp only [Formula.boxes_cons]
      rcases χ with  ⟨β, af⟩
      simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq, LoadFormula.box.injEq] at h
      rcases h with ⟨β_eq_α1, af_def⟩
      have := loaded_eq_to_unload_eq ((⌊α2⌋AnyFormula.loadBoxes αs (.normal φ))) (α2 :: αs) _ rfl
      aesop

lemma any_loaded_helper
    (h : AnyFormula.loaded χ' = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : (⌊d⌋AnyFormula.loadBoxes (δ ++ αs) (AnyFormula.normal φ)) = ⌊⌊d :: δ⌋⌋χ' := by
  cases αs
  · exfalso
    simp_all
  case cons α αs =>
    simp at h
    subst h
    rw [LoadFormula.boxes_cons]
    rw [AnyFormula.loadBoxes_append]
    rw [AnyFormula.loadBoxes_cons]
    simp -- d gone
    apply AnyFormula.loadBoxes_loaded_eq_loaded_boxes

lemma Sequent.without_loadBoxes_isFree_of_eq_inl {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inl (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [any_loaded_helper]
  exact h

lemma Sequent.without_loadBoxes_isFree_of_eq_inr {L R δs} {χ : LoadFormula} {φ : Formula}
    (h : χ = AnyFormula.loadBoxes αs φ)
    : (Sequent.without (L, R, some (Sum.inr (~'⌊⌊d :: δs⌋⌋χ)))
      (~''(AnyFormula.loadBoxes (d :: (δs ++ αs)) (AnyFormula.normal φ)))).isFree := by
  unfold Sequent.without
  simp
  suffices (⌊⌊d :: δs⌋⌋χ) = ⌊d⌋AnyFormula.loadBoxes (δs ++ αs) (AnyFormula.normal φ) by simp_all
  rw [any_loaded_helper]
  exact h

lemma splitLast_undo_of_some (h : splitLast αs = some βs_b) :
    βs_b.1 ++ [βs_b.2] = αs := by
  rcases αs with _ |⟨α,αs⟩
  · exfalso
    simp_all
  have := @splitLast_cons_eq_some _ α αs
  rw [h] at this
  simp at this
  subst this
  simp
  apply List.dropLast_append_getLast_eq_cons

lemma loadMulti_eq_of_some (h : δ.head? = some d) :
    loadMulti δ β φ = ⌊d⌋AnyFormula.loaded (loadMulti δ.tail β φ) := by
  cases δ
  <;> simp_all

lemma splitLast_inj (h : splitLast αs = splitLast βs) :
    αs = βs := by
  induction αs using List.reverseRecOn <;> induction βs using List.reverseRecOn
  · rfl
  · exfalso
    simp_all
  · exfalso
    simp_all
  aesop

lemma loadMulti_of_splitLast_cons {α αs βs β φ} (h : splitLast (α :: αs) = some ⟨βs, β⟩) :
    loadMulti βs β φ = ⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ) := by
  have : (α :: αs) = βs ++ [β] := by
    rw [← @splitLast_append_singleton] at h
    exact splitLast_inj h
  cases αs
  · unfold splitLast at h
    simp at h
    cases h
    subst_eqs
    simp at *
  case cons α2 αs =>
    have ⟨δβ2, new_h⟩ : ∃ δ2_β2, splitLast (α2 :: αs) = some δ2_β2 := by simp [splitLast]
    rw [AnyFormula.loadBoxes_cons]
    have IH := @loadMulti_of_splitLast_cons α2 αs _ _ φ new_h
    rw [← IH]; clear IH
    cases βs
    · exfalso
      unfold splitLast at h
      simp at h
      cases h
    case cons β2 βs =>
      simp_all
      subst new_h
      simp_all

lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inl {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inl (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]

lemma Sequent.without_loadMulti_isFree_of_splitLast_cons_inr {L R δs} {φ : Formula}
    (h : splitLast (d :: δs) = some δ_β)
    : (Sequent.without (L, R, some (Sum.inr (~'loadMulti δ_β.1 δ_β.2 φ)))
      (~''(AnyFormula.loadBoxes (d :: δs) (AnyFormula.normal φ)))).isFree := by
  rw [@loadMulti_of_splitLast_cons _ _ _ _ φ h]
  simp [Sequent.without]

set_option maxHeartbeats 1000000 in
/-- NEW ATTEMPT. Helper to deal with local tableau in `loadedDiamondPaths`.
Takes a *list* of programs and φ, i.e. we want access to all loaded boxes. -/
theorem localLoadedDiamondList (αs : List Program) {X : Sequent}
  (ltab : LocalTableau X)
  {W} {M : KripkeModel W} {v w : W}
  (v_αs_w : relateSeq M αs v w)
  (v_t : (M,v) ⊨ X)
  (φ : Formula) -- must not be loaded
  {side : Side}
  (negLoad_in : (~''(AnyFormula.loadBoxes αs φ)).in_side side X)
  (no_other_loading : (X.without (~''(AnyFormula.loadBoxes αs φ))).isFree)
  (w_nξ : (M,w) ⊨ ~''φ)
  : ∃ Y ∈ endNodesOf ltab, (M,v) ⊨ Y ∧
    (   Y.isFree -- means we left cluster
      ∨ ( ∃ (F : List Formula) (γ : List Program),
            ( (~''(AnyFormula.loadBoxes γ φ)).in_side side Y
            ∧ relateSeq M γ v w
            ∧ (M,v) ⊨ F
            ∧ (F,γ) ∈ Hl αs -- "F,γ is a result from unfolding the αs"
            ∧ (Y.without (~''(AnyFormula.loadBoxes γ φ))).isFree
            )
        )
    ) := by

  cases αs

  case nil => -- We can pick any end node.
    simp_all
    rcases (localTableauTruth ltab M w).1 v_t with ⟨Y, Y_in, w_Y⟩
    refine ⟨Y, Y_in, w_Y, Or.inl ?_⟩
    apply endNodesOf_free_are_free ltab no_other_loading Y_in

  case cons α αs =>

    induction ltab generalizing α αs v w
    -- the generalizing `αs` here makes things really slow. use recursion instead?

    case byLocalRule X B lra next IH =>
      rcases X with ⟨L,R,O⟩

      -- Soundness and invertibility of the local rule:
      have locRulTru := @localRuleTruth (L,R,O) _ lra W M

      -- We distinguish which rule was applied.
      rcases lra with ⟨Lcond, Rcond, Ocond, r, precons⟩
      rename_i resNodes B_def_apply_r_LRO
      cases r

      -- Rules not affecting the loaded formula are easy by using the IH.
      case oneSidedL resNodes orule =>
        simp_all [applyLocalRule] -- uses locRulTru
        rcases v_t with ⟨res, res_in, v_⟩
        specialize IH _ res ⟨res_in, rfl⟩ v_ w_nξ _ _ v_αs_w
          (by cases side <;> simp_all [AnyNegFormula.in_side])
          (by apply Sequent.without_loaded_in_side_isFree _ _ side; clear IH
              cases side
              all_goals
                simp [AnyNegFormula.in_side]
                simp [AnyNegFormula.in_side] at negLoad_in
                exact negLoad_in)
        rcases IH with ⟨Y, Y_in, v_Y⟩
        use Y
        simp_all only [List.empty_eq, List.nil_subperm, Option.instHasSubsetOption, and_self, and_true]
        use endNodesOf (next (L.diff Lcond ++ res, R, O) (by aesop))
        simp_all only [and_true]
        use (L.diff Lcond ++ res, R, O)
        simp_all only [exists_prop, and_true]
        use res
      case oneSidedR resNodes orule => -- analogous to oneSidedL
        simp_all [applyLocalRule] -- uses locRulTru
        rcases v_t with ⟨res, res_in, v_⟩
        specialize IH _ res ⟨res_in, rfl⟩ v_ w_nξ _ _ v_αs_w
          (by cases side <;> simp_all [AnyNegFormula.in_side])
          (by apply Sequent.without_loaded_in_side_isFree _ _ side; clear IH
              cases side
              all_goals
                simp [AnyNegFormula.in_side]
                simp [AnyNegFormula.in_side] at negLoad_in
                exact negLoad_in)
        rcases IH with ⟨Y, Y_in, v_Y⟩
        use Y
        simp_all only [List.empty_eq, List.nil_subperm, Option.instHasSubsetOption, and_self, and_true]
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
        rw [@relateSeq_cons] at v_αs_w
        rcases v_αs_w with ⟨u, v_α_u, u_αs_w⟩
        -- ... here we use use `existsDiamondH` to imitate the relation v_α_u
        have from_H := @existsDiamondH W M α _ _ v_α_u
        rcases from_H with ⟨⟨F,δ⟩, _in_H, v_F, v_δ_u⟩
        simp at v_δ_u
        cases lrule -- dia or dia' annoyance ;-)
        case dia α' χ' α'_not_atomic =>
          -- The rule application has its own α' that must be α, and χ' must be ⌊αs⌋φ.
          have ⟨α_same, χ_def⟩ : α = α' ∧ χ' = (AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
            simp [AnyNegFormula.in_side] at negLoad_in
            have := precons.2.2
            simp at this
            rw [← this] at negLoad_in
            cases side <;> aesop
          subst α_same -- But cannot do `subst χ_def`.
          -- This F,δ pair is also used for one result in `B`:
          have in_B : (L ++ F, R, some (Sum.inl (~'⌊⌊δ⌋⌋χ'))) ∈ B := by
            simp [applyLocalRule, unfoldDiamondLoaded, YsetLoad] at B_def_apply_r_LRO
            rw [B_def_apply_r_LRO]
            simp
            use F, δ
          simp
          cases δ
          case nil => -- δ is empty, is this the easy or the hard case? ;-)
            simp at v_δ_u v_F -- Here we have v = u.
            subst v_δ_u
            cases αs
            · exfalso; simp_all [χ_def]
            case cons new_α new_αs =>
              -- Let's prepare the IH application now.
              specialize @IH _ in_B v w ?_ w_nξ new_α new_αs u_αs_w ?_ ?_
              · intro f f_in; clear IH
                simp only [Option.map_some', Sum.elim_inl, negUnload, unload_boxes,
                  Formula.boxes_nil, Option.toList_some, List.mem_union_iff, List.mem_append,
                  List.mem_cons, List.not_mem_nil, or_false] at f_in
                rcases f_in with (((f_in|f_in)|f_in)|f_def)
                · apply v_t; simp_all
                · exact v_F _ f_in
                · apply v_t; simp_all
                · subst f_def
                  rw [loaded_eq_to_unload_eq χ' _ _ χ_def]
                  simp only [evaluate, Formula.boxes_cons, not_forall, Classical.not_imp]
                  rcases u_αs_w with ⟨x, v_α_x, bla⟩
                  use x, v_α_x; rw [evalBoxes]
                  push_neg; use w; tauto
              · rw [← χ_def]; cases side <;> simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
              · rw [← χ_def]; simp_all [Sequent.without, LoadFormula.boxes]
              -- Now actually get the IH result.
              rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                            | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
              · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
              · -- Not fully sure here.
                refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
                refine ⟨F ∪ G, γs, in_Y, v_γs_w, ?_, ?_, Y_almost_free⟩
                · intro f f_in
                  simp at f_in; cases f_in
                  · apply v_F; assumption
                  · apply v_G; assumption
                simp [Hl]
                refine ⟨_, _, _in_H, ?_⟩
                simp
                refine ⟨G, in_Hl, rfl⟩
          case cons d δs =>
            -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
            -- Again we prepare to use IH, but now for `d` and `δs ++ αs` instead.
            specialize @IH _ in_B v w ?_ w_nξ d (δs ++ αs) ?_ ?_ ?_
            · intro f f_in
              simp only [Option.map_some', Sum.elim_inl, negUnload, unload_boxes,
                Formula.boxes_cons, Option.toList_some, List.mem_union_iff, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at f_in
              rcases f_in with (((f_in|f_in)|f_in)|f_def)
              · apply v_t; simp_all
              · exact v_F _ f_in
              · apply v_t; simp_all
              · subst f_def
                simp only [evaluate, evalBoxes, not_forall, Classical.not_imp]
                rw [@relateSeq_cons] at v_δ_u
                rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
                refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
                rw [loaded_eq_to_unload_eq χ' _ _ χ_def, evalBoxes]
                push_neg; use w; tauto
            · simp_rw [relateSeq_cons, relateSeq_append]
              rw [relateSeq_cons] at v_δ_u
              rcases v_δ_u with ⟨x, v_d_x, x_δ_u⟩
              refine ⟨x, v_d_x, ⟨u, x_δ_u, u_αs_w⟩⟩
            · cases side
              · simp only [AnyFormula.loadBoxes_cons, AnyNegFormula.in_side]
                convert rfl
                apply any_loaded_helper χ_def
              · exfalso
                simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
            · exact Sequent.without_loadBoxes_isFree_of_eq_inl χ_def
            -- Now actually get the IH result.
            rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                          | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
              refine ⟨F, _, in_Y, v_γs_w, v_F, ?_, Y_almost_free⟩
              have αs_nonEmpty : αs ≠ [] := by cases αs <;> simp_all [χ_def]
              simp only [Hl, List.mem_flatMap, Prod.exists] -- uses `αs_nonEmpty`
              refine ⟨F, d :: δs, _in_H, ?_⟩
              simp
              -- Now show that `d` is atomic, because it resulted from `H α`.
              have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
                have := H_mem_sequence α _in_H
                rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
                · exfalso ; simp_all
                · refine ⟨a, by simp_all⟩
              subst d_atom
              -- Hence `Hl (d :: ...)` does not actually unfold anything.
              simp [Hl] at in_Hl
              exact in_Hl.2
        case dia' α' φ' α'_not_atomic => -- only *somewhat* analogous to `dia` case.
          -- The rule application has its own α' that must be α,
          -- also has its own φ' that must be φ, (this is new/easier here)
          -- and αs must be [], there is no more χ.
          have ⟨α_same, φ_same, αs_empty⟩ : α = α' ∧ φ = φ' ∧ αs = [] := by
            simp [AnyNegFormula.in_side] at negLoad_in
            have := precons.2.2
            simp at this
            rw [← this] at negLoad_in
            cases side
            · simp at *
              rcases negLoad_in with ⟨α_same, φ_def⟩
              cases αs <;> simp_all
            · subst B_def_apply_r_LRO this
              simp_all only [modelCanSemImplyList, Option.some.injEq, reduceCtorEq]
          -- It seems this is actually easier than the `dia` case, we can `subst` more here.
          subst α_same
          subst φ_same
          subst αs_empty
          simp [relateSeq] at u_αs_w
          subst u_αs_w -- We now have u = w.
          -- Note: we now do `in_B` *after* distinguishing whether δ = [].
          simp
          cases δ
          case nil => -- δ is empty, so we should have a free result?
            simp at v_δ_u v_F -- Here we have v = u.
            subst v_δ_u
            -- This F,δ pair is also used for one result in `B`:
            have in_B : (L ++ (F ∪ [~φ]), R, none) ∈ B := by
              simp [applyLocalRule, unfoldDiamondLoaded', YsetLoad'] at B_def_apply_r_LRO
              rw [B_def_apply_r_LRO]
              simp
              refine ⟨F, [], _in_H, ?_, ?_⟩
              · simp
              · clear IH
                cases O <;> cases side
                all_goals
                  simp [splitLast, Olf.change, Option.insHasSdiff, AnyNegFormula.in_side] at *
                · exact negLoad_in
                · exfalso; aesop
            -- No IH needed because we reach a free node.
            clear IH
            -- We do not know `Y` yet because ltab may continue after `(L ++ F ++ [~φ], R, none)`.
            -- So let's use localTableauTruth to find a free end node, similar to αs = [] case.
            have v_Z : (M, v) ⊨ ((L ++ (F ∪ [~φ]), R, none) : Sequent) := by intro f f_in; aesop
            rcases (localTableauTruth (next _ in_B) M v).1 v_Z with ⟨Y, Y_in, v_Y⟩
            refine ⟨Y, ⟨(L ++ (F ∪ [~φ]), R, none), in_B, Y_in⟩, ⟨v_Y, Or.inl ?Y_free⟩⟩
            apply endNodesOf_free_are_free (next _ in_B) ?_ Y_in
            simp
          case cons d δs =>
            rw [@relateSeq_cons] at v_δ_u
            rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
            let δ_β := match h : splitLast (d :: δs) with
              | some this => this
              | none => by exfalso; simp_all [splitLast]
            have split_def : splitLast (d :: δs) = some δ_β := by rfl
            -- This F,δ pair is also used for one result in `B`:
            have in_B : (L ++ F, R, some (Sum.inl (~'loadMulti δ_β.1 δ_β.2 φ))) ∈ B := by
              simp [applyLocalRule, unfoldDiamondLoaded', YsetLoad'] at B_def_apply_r_LRO
              rw [B_def_apply_r_LRO]
              simp
              use F, (d :: δs), _in_H
              rw [split_def]
              simp
            -- Rest based on non-empty δ case in `dia` above; changed to work with `loadMulti`.
            -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
            -- Again we prepare to use IH, but now for `d` and `δs` instead.
            specialize @IH _ in_B v u ?_ w_nξ d δs ?_ ?_ ?_
            · intro f f_in
              simp only [Option.map_some', Sum.elim_inl, negUnload, unload_loadMulti,
                Option.toList_some, List.mem_union_iff, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false] at f_in
              rcases f_in with (((f_in|f_in)|f_in)|f_def)
              · apply v_t; simp_all
              · exact v_F _ f_in
              · apply v_t; simp_all
              · subst f_def
                rw [← @boxes_last, splitLast_undo_of_some split_def]
                simp only [evaluate, Formula.boxes_cons, evalBoxes, not_forall, Classical.not_imp]
                refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
                exact w_nξ
            · simp_rw [relateSeq_cons]
              exact ⟨x, v_d_x, x_δs_u⟩
            · cases side
              · simp [AnyFormula.loadBoxes_cons, AnyNegFormula.in_side]
                exact loadMulti_of_splitLast_cons split_def
              · exfalso
                simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
            · exact Sequent.without_loadMulti_isFree_of_splitLast_cons_inl split_def
            -- Now actually get the IH result.
            rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                          | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
              refine ⟨F, _, in_Y, v_γs_w, v_F, ?_, Y_almost_free⟩
              -- Now show that `d` is atomic, because it resulted from `H α`.
              have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
                have := H_mem_sequence α _in_H
                rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
                · exfalso ; simp_all
                · refine ⟨a, by simp_all⟩
              subst d_atom
              -- Hence `Hl (d :: ...)` does not actually unfold anything.
              simp [Hl] at in_Hl
              rw [in_Hl.2]
              exact _in_H

      case loadedR outputs χ lrule => -- COPY-PASTA from loadedL, modulo the value of `side`
        -- Instead of localRuleTruth ...
        clear locRulTru
        rw [@relateSeq_cons] at v_αs_w
        rcases v_αs_w with ⟨u, v_α_u, u_αs_w⟩
        -- ... here we use use `existsDiamondH` to imitate the relation v_α_u
        have from_H := @existsDiamondH W M α _ _ v_α_u
        rcases from_H with ⟨⟨F,δ⟩, _in_H, v_F, v_δ_u⟩
        simp at v_δ_u
        cases lrule -- dia or dia' annoyance ;-)
        case dia α' χ' α'_not_atomic =>
          -- The rule application has its own α' that must be α, and χ' must be ⌊αs⌋φ.
          have ⟨α_same, χ_def⟩ : α = α' ∧ χ' = (AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
            simp [AnyNegFormula.in_side] at negLoad_in
            have := precons.2.2
            simp at this
            rw [← this] at negLoad_in
            cases side <;> aesop
          subst α_same -- But cannot do `subst χ_def`.
          -- This F,δ pair is also used for one result in `B`:
          have in_B : (L, R ++ F, some (Sum.inr (~'⌊⌊δ⌋⌋χ'))) ∈ B := by
            simp [applyLocalRule, unfoldDiamondLoaded, YsetLoad] at B_def_apply_r_LRO
            rw [B_def_apply_r_LRO]
            simp
            use F, δ
          simp
          cases δ
          case nil => -- δ is empty, is this the easy or the hard case? ;-)
            simp at v_δ_u v_F -- Here we have v = u.
            subst v_δ_u
            cases αs
            · exfalso; simp_all [χ_def]
            case cons new_α new_αs =>
              -- Let's prepare the IH application now.
              specialize @IH _ in_B v w ?_ w_nξ new_α new_αs u_αs_w ?_ ?_
              · intro f f_in; clear IH
                simp only [LoadFormula.boxes_nil, Option.map_some', Sum.elim_inr, negUnload,
                  Option.toList_some, List.mem_union_iff, List.mem_append, List.mem_cons,
                  List.not_mem_nil, or_false] at f_in
                rcases f_in with ((f_in|(f_in|f_in))|f_def)
                · apply v_t; simp_all
                · apply v_t; simp_all
                · exact v_F _ f_in
                · subst f_def
                  rw [loaded_eq_to_unload_eq χ' _ _ χ_def]
                  simp only [evaluate, Formula.boxes_cons, not_forall, Classical.not_imp]
                  rcases u_αs_w with ⟨x, v_α_x, bla⟩
                  use x, v_α_x; rw [evalBoxes]
                  push_neg; use w; tauto
              · rw [← χ_def]; cases side <;> simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
              · rw [← χ_def]; simp_all [Sequent.without, LoadFormula.boxes]
              -- Now actually get the IH result.
              rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                            | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
              · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
              · -- Not fully sure here.
                refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
                refine ⟨F ∪ G, γs, in_Y, v_γs_w, ?_, ?_, Y_almost_free⟩
                · intro f f_in
                  simp at f_in; cases f_in
                  · apply v_F; assumption
                  · apply v_G; assumption
                simp [Hl]
                refine ⟨_, _, _in_H, ?_⟩
                simp
                refine ⟨G, in_Hl, rfl⟩
          case cons d δs =>
            -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
            -- Again we prepare to use IH, but now for `d` and `δs ++ αs` instead.
            specialize @IH _ in_B v w ?_ w_nξ d (δs ++ αs) ?_ ?_ ?_
            · intro f f_in
              simp only [Option.map_some', Sum.elim_inr, negUnload, unload_boxes,
                Formula.boxes_cons, Option.toList_some, List.mem_union_iff, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at f_in
              rcases f_in with ((f_in|(f_in|f_in))|f_def)
              · apply v_t; simp_all
              · apply v_t; simp_all
              · exact v_F _ f_in
              · subst f_def
                simp only [evaluate, evalBoxes, not_forall, Classical.not_imp]
                rw [@relateSeq_cons] at v_δ_u
                rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
                refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
                rw [loaded_eq_to_unload_eq χ' _ _ χ_def, evalBoxes]
                push_neg; use w; tauto
            · simp_rw [relateSeq_cons, relateSeq_append]
              rw [relateSeq_cons] at v_δ_u
              rcases v_δ_u with ⟨x, v_d_x, x_δ_u⟩
              refine ⟨x, v_d_x, ⟨u, x_δ_u, u_αs_w⟩⟩
            · cases side
              · exfalso
                simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
              · simp only [AnyFormula.loadBoxes_cons, AnyNegFormula.in_side]
                convert rfl
                apply any_loaded_helper χ_def
            · exact Sequent.without_loadBoxes_isFree_of_eq_inr χ_def
            -- Now actually get the IH result.
            rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                          | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
              refine ⟨F, _, in_Y, v_γs_w, v_F, ?_, Y_almost_free⟩
              have αs_nonEmpty : αs ≠ [] := by cases αs <;> simp_all [χ_def]
              simp only [Hl, List.mem_flatMap, Prod.exists] -- uses `αs_nonEmpty`
              refine ⟨F, d :: δs, _in_H, ?_⟩
              simp
              -- Now show that `d` is atomic, because it resulted from `H α`.
              have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
                have := H_mem_sequence α _in_H
                rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
                · exfalso ; simp_all
                · refine ⟨a, by simp_all⟩
              subst d_atom
              -- Hence `Hl (d :: ...)` does not actually unfold anything.
              simp [Hl] at in_Hl
              exact in_Hl.2
        case dia' α' φ' α'_not_atomic => -- only *somewhat* analogous to `dia` case.
          -- The rule application has its own α' that must be α,
          -- also has its own φ' that must be φ, (this is new/easier here)
          -- and αs must be [], there is no more χ.
          have ⟨α_same, φ_same, αs_empty⟩ : α = α' ∧ φ = φ' ∧ αs = [] := by
            simp [AnyNegFormula.in_side] at negLoad_in
            have := precons.2.2
            simp at this
            rw [← this] at negLoad_in
            cases side
            · subst this
              simp_all only [modelCanSemImplyList, Option.some.injEq, reduceCtorEq]
            · simp at negLoad_in
              rcases negLoad_in with ⟨α_same, φ_def⟩
              cases αs <;> simp_all
          -- It seems this is actually easier than the `dia` case, we can `subst` more here.
          subst α_same
          subst φ_same
          subst αs_empty
          simp [relateSeq] at u_αs_w
          subst u_αs_w -- We now have u = w.
          -- Note: we now do `in_B` *after* distinguishing whether δ = [].
          simp
          cases δ
          case nil => -- δ is empty, so we should have a free result?
            simp at v_δ_u v_F -- Here we have v = u.
            subst v_δ_u
            -- This F,δ pair is also used for one result in `B`:
            have in_B : (L, R ++ (F ∪ [~φ]), none) ∈ B := by
              simp [applyLocalRule, unfoldDiamondLoaded', YsetLoad'] at B_def_apply_r_LRO
              rw [B_def_apply_r_LRO]
              simp
              refine ⟨F, [], _in_H, ?_, ?_⟩
              · simp
              · clear IH
                cases O <;> cases side
                all_goals
                  simp [splitLast, Olf.change, Option.insHasSdiff, AnyNegFormula.in_side] at *
                · exfalso; simp_all only [reduceCtorEq]
                · exact negLoad_in
            -- No IH needed because we reach a free node.
            clear IH
            -- We do not know `Y` yet because ltab may continue after `(L ++ F ++ [~φ], R, none)`.
            -- So let's use localTableauTruth to find a free end node, similar to αs = [] case.
            have v_Z : (M, v) ⊨ ((L, R ++ (F ∪ [~φ]), none) : Sequent) := by intro f f_in; aesop
            rcases (localTableauTruth (next _ in_B) M v).1 v_Z with ⟨Y, Y_in, v_Y⟩
            refine ⟨Y, ⟨(L, R ++ (F ∪ [~φ]), none), in_B, Y_in⟩, ⟨v_Y, Or.inl ?_⟩⟩
            apply endNodesOf_free_are_free (next _ in_B) ?_ Y_in
            simp
          case cons d δs =>
            rw [@relateSeq_cons] at v_δ_u
            rcases v_δ_u with ⟨x, v_d_x, x_δs_u⟩
            let δ_β := match h : splitLast (d :: δs) with
              | some this => this
              | none => by exfalso; simp_all [splitLast]
            have split_def : splitLast (d :: δs) = some δ_β := by rfl
            -- This F,δ pair is also used for one result in `B`:
            have in_B : (L, R ++ F, some (Sum.inr (~'loadMulti δ_β.1 δ_β.2 φ))) ∈ B := by
              simp [applyLocalRule, unfoldDiamondLoaded', YsetLoad'] at B_def_apply_r_LRO
              rw [B_def_apply_r_LRO]
              simp
              use F, (d :: δs), _in_H
              rw [split_def]
              simp
            -- Rest based on non-empty δ case in `dia` above; changed to work with `loadMulti`.
            -- A non-empty δ came from α, so we have not actually made the step to `u` yet.
            -- Again we prepare to use IH, but now for `d` and `δs` instead.
            specialize @IH _ in_B v u ?_ w_nξ d δs ?_ ?_ ?_
            · intro f f_in
              simp only [Option.map_some', Sum.elim_inr, negUnload, unload_loadMulti,
                Option.toList_some, List.mem_union_iff, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false] at f_in
              clear IH
              rcases f_in with ((f_in|(f_in|f_in))|f_def)
              · apply v_t; simp_all
              · apply v_t; simp_all
              · exact v_F _ f_in
              · subst f_def
                rw [← @boxes_last, splitLast_undo_of_some split_def]
                simp only [evaluate, Formula.boxes_cons, evalBoxes, not_forall, Classical.not_imp]
                refine ⟨x, v_d_x, ⟨u, x_δs_u, ?_⟩⟩
                exact w_nξ
            · simp_rw [relateSeq_cons]
              exact ⟨x, v_d_x, x_δs_u⟩
            · cases side
              · exfalso
                simp_all [AnyNegFormula.in_side, LoadFormula.boxes]
              · simp [AnyFormula.loadBoxes_cons, AnyNegFormula.in_side]
                exact loadMulti_of_splitLast_cons split_def
            · exact Sequent.without_loadMulti_isFree_of_splitLast_cons_inr split_def
            -- Now actually get the IH result.
            rcases IH with ⟨Y, Y_in, v_Y, ( Y_free
                                          | ⟨G, γs, in_Y, v_γs_w, v_G, in_Hl, Y_almost_free⟩ )⟩
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inl Y_free⟩⟩ -- free'n'easy
            · refine ⟨Y, ⟨_, in_B, Y_in⟩ , ⟨v_Y, Or.inr ?_⟩⟩
              refine ⟨F, _, in_Y, v_γs_w, v_F, ?_, Y_almost_free⟩
              -- Now show that `d` is atomic, because it resulted from `H α`.
              have ⟨a, d_atom⟩ : ∃ a, d = ((·a) : Program) := by
                have := H_mem_sequence α _in_H
                rcases this with inl | ⟨a, ⟨δ, list_prop⟩⟩
                · exfalso ; simp_all
                · refine ⟨a, by simp_all⟩
              subst d_atom
              -- Hence `Hl (d :: ...)` does not actually unfold anything.
              simp [Hl] at in_Hl
              rw [in_Hl.2]
              exact _in_H

    case sim X X_isBasic =>
      clear no_other_loading
      -- If `X` is basic then `α` must be atomic.
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
          all_goals
            cases α <;> simp_all
      rw [Program.isAtomic_iff] at this
      rcases this with ⟨a, α_def⟩
      subst α_def
      -- We can use X itself as the end node.
      refine ⟨X, ?_, v_t, Or.inr ⟨[], ·a :: αs, negLoad_in,  ?_,  ?_,  ?_⟩ ⟩ <;> simp_all [H]
      exact Sequent.without_loaded_in_side_isFree X _ side negLoad_in

lemma localLoadedDiamondSingleton
  (ltab : LocalTableau X)
  {W} {M : KripkeModel W} {v w : W}
  (v_α_w : relate M α v w)
  (v_t : (M,v) ⊨ X)
  (φ : Formula) -- must not be loaded
  {side : Side}
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋(AnyFormula.normal φ)))).in_side side X)
  (w_nφ : (M,w) ⊨ ~''φ)
  : ∃ Y ∈ endNodesOf ltab, (M,v) ⊨ Y ∧
    (   Y.isFree -- means we left cluster
      ∨ ( ∃ (F : List Formula) (γ : List Program),
            ( (~''(AnyFormula.loadBoxes γ φ)).in_side side Y
            ∧ relateSeq M γ v w
            ∧ (M,v) ⊨ F
            ∧ (F,γ) ∈ Hl [α] -- "F,γ is a result from unfolding α"
            ∧ (Y.without (~''(AnyFormula.loadBoxes γ φ))).isFree
            )
        )
    ) := by
  refine localLoadedDiamondList [α] ltab ⟨w, ⟨v_α_w, by simp⟩⟩ v_t φ negLoad_in ?_ w_nφ
  · rcases X with ⟨L,R,O⟩
    simp [AnyFormula.loadBoxes, Sequent.without]
    cases side <;> simp [AnyNegFormula.in_side] at negLoad_in
    all_goals
    simp [negLoad_in]

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

lemma not_edge_and_heart {b : PathIn tab} : ¬ (a ⋖_ b ∧ b ♥ a) := by
  intro ⟨aeb, bha⟩
  have node_eq : Sequent.multisetEqTo (nodeAt a) (nodeAt b) := by
    have ⟨lpr, ⟨tabAt_b_22, comp⟩⟩ := bha
    unfold companionOf at comp
    subst comp
    apply nodeAt_companionOf_multisetEq
    exact tabAt_b_22
  have node_ne : ¬ (Sequent.multisetEqTo (nodeAt a) (nodeAt b)) := by
    have a_loaded : (nodeAt a).isLoaded := by exact (companion_loaded bha).2
    have b_loaded : (nodeAt b).isLoaded := by exact (companion_loaded bha).1
    rcases aeb with ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tabAt_a_def, b_def⟩ | ⟨Hist, X, nrep, bas, Y, r, next, tabAt_a_def, b_def⟩
    · have nodeAt_a_def : X = nodeAt a := by unfold nodeAt; rw [tabAt_a_def]
      have nodeAt_b_def : Y = nodeAt b := by
        let a_to_b : PathIn (tabAt a).2.2 := (tabAt_a_def ▸ PathIn.loc Y_in PathIn.nil)
        have tabAt_b_def : tabAt b = ⟨_, _, next Y Y_in⟩ := by
          subst b_def
          rw [tabAt_append]
          have : tabAt (.loc Y_in .nil : PathIn (Tableau.loc nrep nbas lt next))
              = ⟨ X :: _
                , Y, next Y Y_in⟩ := by
            unfold tabAt
            unfold tabAt
            rfl
          convert this <;> try rw [tabAt_a_def]
          simp_all
        unfold nodeAt at *; rw [tabAt_b_def]
      subst nodeAt_a_def
      subst nodeAt_b_def
      rw [Sequent.multisetEqTo_symm]
      exact non_multisetEqTo_of_ltSequent (@endNodesOf_nonbasic_lt_Sequent (nodeAt a) (nodeAt b) lt nbas Y_in)
    · intro con
      rcases X with ⟨LX, RX, OX⟩
      let a_to_b : PathIn (tabAt a).2.2 := (tabAt_a_def ▸ PathIn.pdl PathIn.nil)
      have tabAt_b_def : tabAt b = ⟨_, _, next⟩ := by
        subst b_def
        rw [tabAt_append]
        have : tabAt (.pdl .nil : PathIn (.pdl nrep bas r next))
             = ⟨ (LX, RX, OX) :: _
               , Y, next⟩ := by
          unfold tabAt
          unfold tabAt
          rfl
        convert this <;> try rw [tabAt_a_def]
        simp
      unfold nodeAt at *
      have nodeAt_a_def : (tabAt a).snd.fst = (LX,RX,OX) := by rw [tabAt_a_def]
      simp [nodeAt_a_def] at *
      simp [Sequent.multisetEqTo] at con
      cases r
      case loadL => simp [Sequent.isLoaded] at a_loaded
      case loadR => simp [Sequent.isLoaded] at a_loaded
      case freeL δ α φ =>
        have help : (tabAt b).snd.fst = (List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) LX, RX, none) := by rw [tabAt_b_def]
        simp only [help] at con
        simp_all
      case freeR δ α φ =>
        have help : (tabAt b).snd.fst = (LX, List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) RX, none) := by rw [tabAt_b_def]
        simp only [help] at con
        simp_all
      case modL LX' RX' n ξ X_def =>
        rw [X_def] at con
        cases ξ
        case normal φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = ((~φ) :: projection n LX', projection n RX', none) := by rw [tabAt_b_def]
          simp only [help] at con
          simp_all
        case loaded φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = (projection n LX', projection n RX', some (Sum.inl (~'φ))) := by rw [tabAt_b_def]
          simp only [help] at con
          have := con.2.2
          simp at this
          cases this
      case modR LX' RX' n ξ X_def =>  -- same as modL
        rw [X_def] at con
        cases ξ
        case normal φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = (projection n LX', (~φ) :: projection n RX', none) := by rw [tabAt_b_def]
          simp only [help] at con
          simp_all
        case loaded φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = (projection n LX', projection n RX', some (Sum.inr (~'φ))) := by rw [tabAt_b_def]
          simp only [help] at con
          have := con.2.2
          simp at this
          cases this
  exact node_ne node_eq

/- Soundness of loading and repeats: a tableau can immitate all moves in a model. -/
-- Note that we mix induction' tactic and recursive calls __O.o__
-- TODO: missing here: path from t to s is satisfiable!
-- FIXME: move satisfiable outside disjunction?
set_option maxHeartbeats 10000000

-- TODO adapt to list
lemma loadedDiamondPathsPDL
  (α : Program)
  (αs : List Program)
  (X : Sequent)
  (tab : Tableau [] X)
  (t : PathIn tab)
  {W}
  {M : KripkeModel W}
  {v w : W}
  (v_t : (M, v)⊨nodeAt t)
  (φ : Formula)
  {side : Side}
  (negLoad_in : (~''(⌊α⌋AnyFormula.loadBoxes αs φ)).in_side side (nodeAt t))
  (v_α_w : relateSeq M (α :: αs) v w) -- FIXME rename
  (w_nξ : (M,w) ⊨ (~φ)) -- FIXME rename
  {Hist : History}
  {Z Y : Sequent}
  (bas : Z.basic)
  (r : PdlRule Z Y)
  (nrep : ¬rep Hist Z)
  (next : Tableau (Z :: Hist) Y)
  (tabAt_t_def : tabAt t = ⟨Hist, ⟨Z, Tableau.pdl nrep bas r next⟩⟩) :
  ∃ s, t ◃⁺ s ∧
        (satisfiable (nodeAt s) ∧ ¬s ≡ᶜ t ∨
        (~''(AnyFormula.normal φ)).in_side side (nodeAt s) ∧ (M, w) ⊨ nodeAt s ∧ ((nodeAt s).isFree)) := by
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
    have : ξ' = AnyFormula.loadBoxes αs φ := by
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
    cases αs
    case nil =>
      simp [relateSeq] at v_α_w
      -- Let `s` be the unique child:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      -- used in multiple places below:

      have nodeAt_s_def : nodeAt s = ((~φ) :: projection a L, projection a R, none) := by
        subst Z_def
        unfold nodeAt
        unfold s t_to_s
        rw [tabAt_append]
        -- remains to deal with HEq business
        let tclean : PathIn (.pdl nrep bas (.modL (Eq.refl _)) next) := .pdl .nil
        have : (tabAt tclean).2.1 = ((~φ) :: projection a L, projection a R, none) := by
          have : tabAt tclean = ⟨ _ :: _, ((~φ) :: projection a L, projection a R, none) , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]

      -- ... it is then obvious that `s` satisfies the required properties:
      use s-- refine ⟨s , ?_, Or.inr ⟨?_a, ?_b, ?_c⟩⟩ -- FIXME: change back to refine if possible, see other cases
      constructor
      · constructor
        constructor
        right
        refine ⟨Hist, _, nrep, bas, _, (.modL Z_def), next, tabAt_t_def, ?_⟩
        simp [s, t_to_s]
      · apply Or.inr -- (a)
        constructor
        · subst Z_def
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
        · constructor
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
            simp_all [Sequent.isFree, Sequent.isLoaded, Sequent.without]

    case cons α αs =>
      -- Let `s` be the unique child:
      let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
      let s : PathIn tab := t.append t_to_s
      -- used in multiple places below:
      have nodeAt_s_def : nodeAt s = (projection a L, projection a R, some (Sum.inl (~'(⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ))))) := by
        subst Z_def
        unfold nodeAt
        unfold s t_to_s
        rw [tabAt_append]
        -- remains to deal with HEq business
        let tclean : PathIn (.pdl nrep bas (.modL (Eq.refl _)) next) := .pdl .nil
        have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inl (~'(⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ))))) := by
          have : tabAt tclean = ⟨ _, (projection a L, projection a R, some (Sum.inl (~'(⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ))))) , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
      have t_s : t ⋖_ s := by
        right
        refine ⟨Hist, _, nrep, bas, _, (.modL Z_def), next, tabAt_t_def, ?_⟩
        simp [s, t_to_s]
      unfold relateSeq at v_α_w
      have ⟨u, v_a_u, u_α_w⟩ := v_α_w
      -- look at the tab here, it must still be pdl because more loaded formulas ???
      have u_s : (M, u) ⊨ nodeAt s := by
        rw [nodeAt_s_def]
        intro f f_in
        simp at f_in
        rcases f_in with (f_in | f_in) | f_eq
        · have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
          apply this
          simp only [relate]
          exact v_a_u
        · have : (M,v) ⊨ (⌈·a⌉f) := by apply v_t; rw [tabAt_t_def] ;simp_all
          apply this
          simp only [relate]
          exact v_a_u
        · subst_eqs
          simp
          have ⟨o, u_α_o, o_αs_w⟩ := u_α_w
          refine ⟨o, u_α_o, ?_⟩
          sorry -- DOABLE: just need a helper for this

      have in_s : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))).in_side side (nodeAt s) := by
        rw [nodeAt_s_def]
        unfold nodeAt at negLoad_in
        rw [tabAt_t_def] at negLoad_in
        simp [AnyNegFormula.in_side] at *
        cases side <;> simp_all
      rw [AnyFormula.loadBoxes_cons] at next
      simp at next
      cases next
      case loc nbas lt nrep next =>  -- ISSUE: is there some way to ensure that we do not go into a local tableau
        sorry


      case pdl Y bas r nrep next =>
        have tabAt_s_def : tabAt s = ⟨Z :: Hist, ⟨(projection a L, projection a R, some (Sum.inl (~'⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ)))), Tableau.pdl nrep bas r next⟩⟩ := by sorry
        have ⟨s1, s_s1, s1_cases⟩ := @loadedDiamondPathsPDL α αs X tab s W M u w u_s φ side in_s (u_α_w) w_nξ (Z :: Hist) ((projection a L, projection a R, some (Sum.inl (~'⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ))))) Y bas r nrep next tabAt_s_def
        rcases s1_cases with ⟨sat_con, eq_con⟩ | inr
        · refine ⟨s1, ?_, Or.inl ⟨sat_con, ?_⟩⟩
          · exact Relation.TransGen.head (Or.inl t_s) s_s1
          · exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inl t_s)) s_s1 eq_con
        · refine ⟨s1, ?_, Or.inr inr⟩
          · exact Relation.TransGen.head (Or.inl t_s) s_s1

      case lrep => sorry -- ISSUE: is there some way to ensure that we do not repeat

  case modR L R a ξ' Z_def => -- COPY ADAPTATION from `modL`
    sorry -- just copy modL when done


lemma list_drop_eq_get :
    List.drop k.val xs = (xs.get k) :: (List.drop (k.val + 1) xs) := by
  induction xs
  case nil => exfalso; have ⟨k, k_pf⟩ := k; simp_all
  case cons => induction k using Fin.inductionOn <;> simp

-- List version now
theorem loadedDiamondPaths (α : Program) (αs : List Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (φ : Formula)
  {side : Side} -- not in notes but needed for partition
  (negLoad_in : (~''(⌊α⌋AnyFormula.loadBoxes αs φ)).in_side side (nodeAt t))
  (v_α_w : relateSeq M (α :: αs) v w) -- FIXME rename
  (w_nξ : (M,w) ⊨ (~φ)) -- FIXME rename
  : ∃ s : PathIn tab, t ◃⁺ s ∧
    -- maybe TODO: missing here: path from t to s is satisfiable!
    (   ( satisfiable (nodeAt s) ∧ ¬ (s ≡ᶜ t) )  -- maybe: move satisfiable outside disjunction?
      ∨ ( ((~''(AnyFormula.normal φ)).in_side side (nodeAt s))
        ∧ (M,w) ⊨ (nodeAt s)
        ∧ (nodeAt s).isFree -- hmm
        )
    ) := by

  -- outer induction (do it with recursive calls!)
  -- - lenght of list
  -- - the first program in the list

  -- We do not really need induction, but use `PathIn.init_inductionOn`
  -- to first distinguish whether we are the rooot, and in the step case
  -- we look at what happens at the *end* of the path.
  -- (This is similar to the separate Lemma 5.2, going from t to t'.)
  cases t using PathIn.init_inductionOn
  case root =>
    exfalso
    unfold AnyNegFormula.in_side at negLoad_in
    unfold Sequent.isFree Sequent.isLoaded at root_free
    rcases X with ⟨L,R,O⟩
    cases O <;> cases side <;> simp at *
  case step t0 IH s_t0 => -- NOTE: not indenting from here. why do we get this IH???

  -- Notes first take care of cases where rule is applied to non-loaded formula.
  -- For this, we need to distinguish what happens at `t`.
  rcases tabAt_t_def : tabAt t with ⟨Hist, Z, tZ⟩
  cases tZ
  -- applying a local or a pdl rule or being a repeat?
  case loc nbas ltZ nrep next =>
    cases α_def : α
    case atom_prog a =>
      subst α_def
      have α_atom : (·a : Program).isAtomic := by simp [Program.isAtomic]
      have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
      -- No recursive call or IH needed, just use localTableauTruth to get any end node.
      rcases (localTableauTruth ltZ M v).1 (this ▸ v_t) with ⟨Y, Y_in, w_Y⟩
      have alocLD := atomicLocalLoadedDiamond (·a) ltZ α_atom (AnyFormula.loadBoxes αs φ) (this ▸ negLoad_in) Y Y_in
      clear this
      let t_to_s1 : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .loc Y_in .nil)
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
      have negLoad_in_s : (~''(AnyFormula.loaded (⌊·a⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt s1) := by
        unfold nodeAt ; rw [tabAt_s_def]
        simp_all
      -- NOW: do cases on s1, s1 can NOT be a local tableau,
      cases next_def : (next Y Y_in)
      case loc nbas' _ _ _ =>
        exfalso
        exact nbas' (endNodesOf_basic Y_in)

      case pdl Y' bas' r' nrep' next' =>
        -- first adapt loadedDiamondPathsPDL to list
        simp only [relateSeq] at v_α_w
        have ⟨u, u_prop⟩ := v_α_w
        have ⟨s, s1_s, s1_cases⟩ := @loadedDiamondPathsPDL (·a) αs X tab s1 W M v w (by sorry) φ side (negLoad_in_s) (by sorry) (by sorry) (Z :: Hist) _ _ bas' r' nrep' next' (next_def ▸ tabAt_s_def)
        rcases s1_cases with inl | inr
        · refine ⟨s, ⟨Relation.TransGen.head (Or.inl t_s) s1_s, Or.inl ⟨inl.1, ?_⟩⟩⟩
          · exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inl t_s)) s1_s inl.2
        · refine ⟨s, ⟨Relation.TransGen.head (Or.inl t_s) s1_s, Or.inr inr⟩⟩

      -- Here we need to go to the companion.
      -- IDEA: make a recursive call, and for termination note that the path becomes shorter?
      case lrep lpr =>
        rename' tabAt_t_def => tabAt_t'_def
        rename' t => t'
        rename' t_s => t'_s
        rename' s1 => t
        rename' tabAt_s_def => tabAt_t_def
        rename' negLoad_in => negLoad_in_t
        rename' negLoad_in_s => negLoad_in
        rename' v_s1 => v_t
        have h : (tabAt t).snd.snd = .lrep (tabAt_t_def ▸ next_def ▸ lpr) := by
          -- rw [tabAt_t_def] -- motive is not type correct :-(
          rw [← heq_iff_eq]
          -- The trick here still is to use extensionality for Σ types, twice.
          have tabAt_t_snd_def : (tabAt t).snd = ⟨Y, tabAt_t_def ▸ Tableau.lrep lpr⟩ := by
            ext
            · simp
              rw [tabAt_t_def]
            · simp
              rw [tabAt_t_def]
              simp
              exact next_def
          have := (Sigma.ext_iff.1 tabAt_t_snd_def).2
          simp at this
          convert this <;> simp_all
        -- Let `u` be the companion.
        let u := companionOf t (tabAt_t_def ▸ next_def ▸ lpr) h
        have t_comp_u : t ♥ u := ⟨(tabAt_t_def ▸ next_def ▸ lpr), h, rfl⟩
        -- Show that the companion fulfills the conditions:
        have u_eq_t := nodeAt_companionOf_multisetEq t (tabAt_t_def ▸ next_def ▸ lpr) h
        have v_u : (M, v) ⊨ nodeAt u := by
          rw [vDash_multisetEqTo_iff u_eq_t]
          exact v_t
        have negLoad_in_u : (~''(AnyFormula.loaded (⌊·a⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt u) := by
          rw [AnyNegFormula.in_side_of_multisetEqTo u_eq_t]
          exact negLoad_in
        -- Now prepare and make the recursive call:
        have _forTermination : (companionOf t (tabAt_t_def ▸ next_def ▸ lpr) h).length < t'.length := by -- findme
          apply path_then_length_lt
          apply Relation.TransGen_of_ReflTransGen
          · apply edge_revEuclideanHelper t' u t t'_s (companion_lt t_comp_u)
          · intro con
            unfold u at t_comp_u
            rw [con] at t_comp_u
            exact not_edge_and_heart (And.intro t'_s t_comp_u)
        have := loadedDiamondPaths (·a) αs tab root_free u v_u φ negLoad_in_u v_α_w w_nξ
        rcases this with ⟨s, u_s, (⟨s_sat, not_s_u⟩|reached)⟩
        all_goals
          refine ⟨s, ?_, ?_⟩ -- write a have statement for below line
          exact Relation.TransGen.trans (Relation.TransGen.trans (Relation.TransGen_or_left (Relation.TransGen.single t'_s)) (Relation.TransGen_or_right (Relation.TransGen.single t_comp_u))) u_s
        · refine Or.inl ⟨s_sat, ?_⟩
          refine ePropB.g_tweak t' u s ?_ u_s not_s_u -- ePropB stuf??? exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inr t_comp_u)) u_s not_s_u
          · exact Relation.TransGen.trans (Relation.TransGen_or_left (Relation.TransGen.single t'_s)) (Relation.TransGen_or_right (Relation.TransGen.single t_comp_u))
        · exact Or.inr reached

    -- STAR CASE
    case star β =>
      clear IH
      subst α_def
      have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
      sorry
      /-
    -- needs attention : rewrite to localLoadedDiamondSingleton OR don't use localLoadedDiamond at all ?
      have locLD := localLoadedDiamond (∗β) ltZ v_α_w (this ▸ v_t) _ (this ▸ negLoad_in) w_nξ
      clear this
      rcases locLD with ⟨Y, Y_in, w_Y, free_or_newLoadform⟩
      -- We are given end node by locLD, now define path to it
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
      rcases free_or_newLoadform with Y_is_Free
                                    | ⟨F, δ, anf_in_Y, v_seq_w, v_F, Fδ_in_H, Y_almost_free⟩
      · -- Leaving the cluster, easy case.
        refine ⟨s1, ?_, Or.inl ⟨?_, ?_⟩⟩
        · apply Relation.TransGen.single
          left
          exact t_s
        · use W, M, v
        · unfold cEquiv
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
      by_cases δ = []
      case pos δ_em =>
        subst δ_em
        simp_all
        refine ⟨s1, Relation.TransGen.single (Or.inl t_s), Or.inr ⟨?_, v_s1, ?_⟩⟩
        · convert anf_in_Y
          unfold nodeAt ; rw [tabAt_s_def]
        · convert Y_almost_free
          unfold nodeAt ; rw [tabAt_s_def]
      case neg δ_ne =>
        unfold relate at v_α_w
        have ⟨n, ⟨ws, ⟨v_head, ⟨w_tail, rel⟩⟩⟩⟩ := ReflTransGen.to_finitelyManySteps v_α_w

        -- This is (sort of... see comments below) the minimality claim made in the notes

        have claim : ∀ k : Fin n.succ, -- Note the succ here!
            ∃ sk, t ◃⁺ sk ∧ ( ( satisfiable (nodeAt sk) ∧ ¬(sk ≡ᶜ t) )
                            ∨ ((~''(AnyFormula.loaded (⌊∗β⌋ξ))).in_side side (nodeAt sk)
                                ∧ (M, ws[k]) ⊨ nodeAt sk
                                ∧ ((nodeAt sk).without (~''(AnyFormula.loaded (⌊∗β⌋ξ)))).isFree
                                ∧ True )) := by -- this (True) needs to be replaced with something saying ⌊∗β⌋ξ is principal at sk

          intro k
          induction k using Fin.inductionOn
          case zero =>
            have βstar_last : List.getLast δ δ_ne = (∗β) := by  -- move me to a helper
              unfold H at Fδ_in_H
              rcases List.mem_union_iff.1 Fδ_in_H with inl | inr
              · simp at inl ; exfalso ; exact δ_ne inl.2
              · induction Hβ_def : H β
                case nil =>
                  rw [Hβ_def] at inr
                  simp at inr
                case cons x xs ih =>
                  rw [Hβ_def] at inr
                  simp at inr
                  rcases inr with h | h
                  · have δ_def := h.2.2
                    subst δ_def
                    simp
                  · have ⟨l, ⟨⟨a, ⟨b, ⟨ab_in, pr⟩⟩⟩, Fδ_in⟩⟩ := h
                    by_cases b = []
                    · simp_all
                    · simp_all
                      rw [←pr] at Fδ_in
                      simp at Fδ_in
                      have δ_def := Fδ_in.2
                      subst δ_def
                      simp
            let γ := List.take (δ.length - 1) δ
            have δ_def : δ = γ ++ [∗β] := by unfold γ; rw [←βstar_last] ; simp
            have help : AnyFormula.loaded (⌊⌊γ⌋⌋⌊∗β⌋ξ) = AnyFormula.loadBoxes δ ξ := by -- this can also become a helper, dont know if we will use
              rw [δ_def]
              simp [AnyFormula.loadBoxes, LoadFormula.boxes]
              induction γ <;> simp_all

            rw [δ_def] at v_seq_w
            -- unfold vDash.SemImplies at w_Y
            -- rcases Y with ⟨L, R, O⟩
            -- simp [modelCanSemImplySequent] at w_Y
            -- cases side <;> simp [AnyNegFormula.in_side] at anf_in_Y

            have ⟨u, ⟨M_v_γ_u, M_u_β_v⟩⟩ := relateSeq_append.1 v_seq_w
            rcases (relateSeq_iff_exists_Vector M γ v u).mp M_v_γ_u with ⟨ws', v_def, u_def, ws'_rel⟩

            have claim : ∀ k : Fin γ.length.succ, -- Note the succ here!
              ∃ sk, t ◃⁺ sk ∧ ( ( satisfiable (nodeAt sk) ∧ ¬(sk ≡ᶜ t) )
                              ∨ ( (~''(⌊⌊γ.drop k.val⌋⌋⌊∗β⌋ξ)).in_side side (nodeAt sk) -- ⌊⌊γ.drop k.val⌋⌋⌊∗β⌋ξ
                                ∧ (M, ws'[k]) ⊨ nodeAt sk
                                ∧ ((nodeAt sk).without (~''(⌊⌊γ.drop k.val⌋⌋⌊∗β⌋ξ))).isFree)) := by
              intro k
              induction k using Fin.inductionOn
              case zero =>
                simp only [Nat.succ_eq_add_one, Fin.val_zero, List.drop_zero, Fin.getElem_fin]
                refine ⟨s1, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
                · exact Relation.TransGen.single (Or.inl t_s)
                · unfold nodeAt
                  rw [tabAt_s_def]
                  convert anf_in_Y
                · convert v_s1
                  rw [v_def]
                  rcases ws with ⟨ws, ws_len⟩
                  exact List.Vector.get_zero _
                · unfold nodeAt
                  rw [tabAt_s_def]
                  convert Y_almost_free

              case succ k inner_IH =>

                rcases inner_IH with ⟨sk, t_sk, IH_cases⟩

                rcases IH_cases with _ | ⟨_in_node_sk, wsk'_sk, anf_in_sk⟩
                · refine ⟨sk, t_sk, ?_⟩
                  left
                  assumption
                ·
                  -- Prepare using outer IH for the program δ[k] (that must be simpler than α)
                  have _forTermination : lengthOfProgram γ[k] < lengthOfProgram (∗β) := by sorry         -- TALK TO MALVIN ABOUT THIS, I THINK MIGHT BE TRUE
                    -- TODO: Show that length went down.
                    -- ! Needs better `H_goes_down` similar to `PgoesDown`.
                    -- ! Only true when α is a test, union or semicolon ==> need separate case for star!
                    -- have := H_goes_down_prog (∗β) Fδ_in_H (by aesop : γ.get k ∈ δ)
                    -- cases α
                    -- all_goals
                    --   simp [Program.isAtomic, Program.isStar, lengthOfProgram] at *
                    --   try linarith

                  have γ_ne : γ ≠ [] := by
                    intro con
                    rw [con] at k
                    have ⟨k_val, k_pf⟩ := k
                    simp at k_pf

                  have u_nβξ : (M, u)⊨~''(AnyFormula.loaded (⌊∗β⌋ξ)) := by sorry

                  have in_side_con : (~''(AnyFormula.loaded (⌊γ.get k⌋AnyFormula.loaded (⌊⌊List.drop (↑k.succ) γ⌋⌋⌊∗β⌋ξ)))).in_side side (nodeAt sk) := by
                    convert _in_node_sk
                    have helper : List.drop k.castSucc γ = (γ.get k) :: (List.drop (k.succ) γ) := by
                      exact @list_drop_eq_get _ γ k
                    rw [helper]
                    simp only [LoadFormula.boxes, List.foldr_cons]

                  have sat_con : (M, ws'.get k.succ)⊨~''(AnyFormula.loaded (⌊⌊List.drop (↑k.succ) γ⌋⌋⌊∗β⌋ξ)) := by
                    have := @boxes_true_at_k_of_Vector_rel W M (⌊∗β⌋ξ) γ (by simp [γ_ne]) ws' ws'_rel k (by convert u_nβξ; simp [u_def])
                    convert this
                    simp [AnyFormula.loadBoxes_loaded_eq_loaded_boxes]

                  have outer_IH := @loadedDiamondPaths (γ.get k) _ tab root_free sk W M
                    (ws'.get k.castSucc) (ws'.get k.succ) wsk'_sk
                    ((⌊⌊γ.drop k.succ.val⌋⌋⌊∗β⌋ξ)) -- This is the new ξ.
                    side
                    (in_side_con)
                    (by convert ws'_rel k; simp)
                    (sat_con)

                  clear _forTermination

                  rcases outer_IH with ⟨sk2, sk_c_sk2, sk2_property⟩
                  rcases sk2_property with ⟨sk2_sat, sk2_nEquiv_sk⟩ | ⟨anf_in_sk2, u_sk2, sk2_almostFree⟩
                  · refine ⟨sk2, ?_, Or.inl ⟨sk2_sat, ?_⟩⟩  -- leaving cluster, easy?
                    · exact Relation.TransGen.trans t_sk sk_c_sk2
                    · apply ePropB.g_tweak _ _ _ t_sk sk_c_sk2 sk2_nEquiv_sk
                  · refine ⟨sk2, ?_, Or.inr ⟨anf_in_sk2, u_sk2, sk2_almostFree⟩⟩
                    · exact Relation.TransGen.trans t_sk sk_c_sk2

            have h : ws'[Fin.last γ.length] = u := by rw [u_def] ; unfold List.Vector.last ; exact Eq.refl _
            have ⟨sn, ⟨t_sn, sn_hyp⟩⟩ := claim (Fin.last γ.length)
            rw [h] at *
            simp [List.drop_length] at sn_hyp
            rcases sn_hyp with left | ⟨loaded_con, ⟨w_sn, without_con⟩⟩
            · refine ⟨sn, ⟨t_sn, Or.inl left⟩⟩
            · refine ⟨sn, ⟨t_sn, Or.inr ⟨loaded_con , ?_, without_con, ?_⟩⟩⟩
              · sorry -- ahhhh
              · simp -- this is the principal con

          case succ k ih =>
            by_cases ws[k.castSucc] = ws[k.succ]
            case pos eq => rw [eq] at ih; exact ih
            case neg ne => -- we need this distinction to show δ ≠ ε (see notes)
              have ⟨sk, t_sk, sk_hyp⟩ := ih
              rcases sk_hyp with ⟨sk_sat, sk_ne_t⟩ | ⟨γ, inside_con, wk_sk, loaded_con, principal_con⟩
              · exact ⟨sk, ⟨t_sk, Or.inl ⟨sk_sat, sk_ne_t⟩⟩⟩
              · have ⟨⟨F,δ⟩, ⟨Fδ_in, ⟨wk_F, wk_δ_wk1⟩⟩⟩:= @existsDiamondH W M β ws[k.castSucc] ws[k.succ] (rel k)
                have δ_ne : δ ≠ [] := by
                  intro δ_em
                  simp [δ_em] at wk_δ_wk1
                  exact ne wk_δ_wk1
                have Hβstar_prop : (F, δ ++ [∗β]) ∈ H (∗β) := by  -- this may be wrong? see triple on bottom of page 43
                  simp [H]
                  refine ⟨[(F, δ ++ [∗β])], ⟨⟨F, ⟨δ, ⟨Fδ_in, by simp [δ_ne]⟩⟩⟩, by simp⟩⟩
                -- PRINCIPAL: since ⌊∗β⌋ξ is principal, there must be a succesor with desired properties

                -- IDEA: we now need to sort through the `γ` list to find a succesor with deired properties.. so we use the inner induction from below?
                sorry

        have h : ws[Fin.last n] = w := by rw [w_tail] ; unfold List.Vector.last ; exact Eq.refl _
        have ⟨sn, ⟨t_sn, sn_hyp⟩⟩ := claim (Fin.last n)
        rw [h] at *
        rcases sn_hyp with left | ⟨loaded_con, ⟨w_sn, without_con⟩⟩
        · refine ⟨sn, ⟨t_sn, Or.inl left⟩⟩

        -- PRINCIPAL: because ⌊∗β⌋ξ is principal at sn, we can find child s with desired properties
        · have α_natom : ¬(∗β).isAtomic := by simp [Program.isAtomic]
          sorry
    -/

    all_goals -- all other cases for α!
        have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]

        have Z_free := Z.without_loaded_in_side_isFree (⌊α⌋AnyFormula.loadBoxes αs φ) side (this ▸ negLoad_in)
        have locLD := localLoadedDiamondList (α :: αs) ltZ v_α_w (this ▸ v_t) φ (this ▸ negLoad_in) Z_free
          w_nξ
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
        -- Now distinguish the two cases coming from `localLoadedDiamondList`:
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
        · -- Second case of `localLoadedDiamondList`.
          -- If δ is empty then we have found the node we want.
          by_cases δ = []
          · subst_eqs
            simp_all only [modelCanSemImplyList, AnyFormula.boxes_nil, relateSeq_nil,
              Sequent.without_normal_isFree_iff_isFree]
            subst_eqs
            refine ⟨s1, Relation.TransGen.single (Or.inl t_s), Or.inr ⟨?_, v_s1, ?_⟩⟩
            · convert anf_in_Y
              unfold nodeAt
              rw [tabAt_s_def]
            · unfold nodeAt
              convert Y_almost_free
              rw [tabAt_s_def]
          -- Now we have that δ is not empty.
          -- FIXME: indent rest or use wlog above?
          -- Here is the interesting case: not leaving the cluster.
          -- We get a sequence of worlds from the δ relation:
          rcases (relateSeq_iff_exists_Vector M δ v w).mp v_seq_w with ⟨ws, v_def, w_def, ws_rel⟩

          -- Claim for an inner induction on the list δ. -- Extended Induction Hypothesis is herre

          -- NEW: tempting here to just not do this claim / the inner induction,
          -- but then we would need a different termination argument that compares whole lists?!
          -- For now I will keep the induction and try to repair the old proof.

          let ξ : AnyFormula := AnyFormula.normal φ -- no αs here?!

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
                simp only
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
                have _forTermination_all : lengthOfProgram δ[k] < lengthOfProgram α := by
                  -- Here we show that the length goes down to get the outer_IH.
                  -- For this we use `H_goes_down_prog` that is similar to `PgoesDown`.
                  -- ! Only true when α is a test, union or semicolon ==> need separate case for star!
                  -- NEW: maybe here we need something like `Hl_goes_down_prog`?
                  -- simp [Hl] at Fδ_in_H
                  -- have := H_goes_down_prog α Fδ_in_H (by aesop : δ.get k ∈ δ)
                  cases α
                  all_goals
                    simp [Program.isAtomic, Program.isStar, lengthOfProgram] at *
                    try linarith
                  all_goals
                    sorry

                have outer_IH := @loadedDiamondPaths (δ.get k) (δ.drop k.succ) _ tab root_free sk W M
                  (ws.get k.castSucc) (ws.get k.succ) wsk_sk
                  φ -- Still the same φ here!
                  side
                  (by convert _in_node_sk; rw [←AnyFormula.loadBoxes_cons]; convert rfl using 2; simp)
                  (by sorry /- convert ws_rel k; simp -/)
                  (by sorry /- apply boxes_true_at_k_of_Vector_rel <;> simp_all -/)

                clear _forTermination_all

                rcases outer_IH with ⟨sk2, sk_c_sk2, sk2_property⟩
                rcases sk2_property with ⟨sk2_sat, sk2_nEquiv_sk⟩ | ⟨anf_in_sk2, u_sk2, sk2_almostFree⟩
                · refine ⟨sk2, ?_, Or.inl ⟨sk2_sat, ?_⟩⟩  -- leaving cluster, easy?
                  · exact Relation.TransGen.trans t_sk sk_c_sk2
                  · apply ePropB.g_tweak _ _ _ t_sk sk_c_sk2 sk2_nEquiv_sk
                · refine ⟨sk2, ?_, Or.inr ⟨?_, u_sk2, ?_⟩⟩
                  · exact Relation.TransGen.trans t_sk sk_c_sk2
                  · -- PROBLEM HERE?!
                    -- anf_in_sk2
                    sorry
                  · apply Sequent.isFree_then_without_isFree _ sk2_almostFree

          -- It remains to show that the claim suffices.
          specialize claim δ.length
          rcases claim with ⟨sk, t_sk, sk_prop⟩
          use sk
          simp_all [modelCanSemImplyList, List.get_eq_getElem, Nat.succ_eq_add_one,
            Fin.coe_eq_castSucc, Fin.natCast_eq_last, Fin.val_last, AnyFormula.boxes_nil,
            Fin.getElem_fin, List.drop_length, true_and]
          -- UNSURE here
          convert sk_prop using 3
          sorry

  case pdl Y bas r nrep next => -- handled by helper
    exact loadedDiamondPathsPDL α αs X tab t v_t φ negLoad_in v_α_w w_nξ bas r nrep next tabAt_t_def

  case lrep lpr =>
    -- Here we need to go to the companion.
    -- IDEA: make a recursive call, and for termination note that the path becomes shorter?
    have h : (tabAt t).snd.snd = .lrep (tabAt_t_def ▸ lpr) := by
      clear IH
      -- rw [tabAt_t_def] -- motive is not type correct :-(
      rw [← heq_iff_eq]
      -- The trick here is to use extensionality for Σ types, twice.
      have tabAt_t_snd_def : (tabAt t).snd = ⟨Z, tabAt_t_def ▸ Tableau.lrep lpr⟩ := by
        ext <;> (simp ; rw [tabAt_t_def])
      have := (Sigma.ext_iff.1 tabAt_t_snd_def).2
      simp at this
      convert this <;> simp_all
    -- Let `u` be the companion.
    let u := companionOf t (tabAt_t_def ▸ lpr) h
    have t_comp_u : t ♥ u:= ⟨(tabAt_t_def ▸ lpr), h, rfl⟩
    -- Show that the companion fulfills the conditions:
    have u_eq_t := nodeAt_companionOf_multisetEq t (tabAt_t_def ▸ lpr) h
    have v_u : (M, v) ⊨ nodeAt u := by
      rw [vDash_multisetEqTo_iff u_eq_t]
      exact v_t
    have negLoad_in_u : (~''(AnyFormula.loaded (⌊α⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt u) := by
      rw [AnyNegFormula.in_side_of_multisetEqTo u_eq_t]
      exact negLoad_in
    -- Now prepare and make the recursive call:
    have _forTermination_lrep : (companionOf t (tabAt_t_def ▸ lpr) h).length < t.length := by
      apply companionOf_length_lt_length
    have := loadedDiamondPaths α αs tab root_free u v_u φ negLoad_in_u v_α_w w_nξ
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
      · subst α_def
        apply Prod.Lex.right (lengthOfProgram _) _forTermination
      /-
      · subst α_def
        apply Prod.Lex.left _ _ _forTermination
      -/
      · exact Prod.Lex.left _ _ _forTermination_all
      · exact Prod.Lex.left _ _ _forTermination_all
      · exact Prod.Lex.left _ _ _forTermination_all
      · exact Prod.Lex.right (lengthOfProgram α) _forTermination_lrep


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
      cases δ
      -- Start the induction before `rintro` so the inner IH is about satisfiability.
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
        simp [Formula.boxes_nil, evaluate, not_forall, Classical.not_imp] at this
        rcases this with ⟨w, v_α_w, not_w_φ⟩
        have := loadedDiamondPaths α [] tab Root_isFree t v_ φ in_t
          (by simp; exact v_α_w) (not_w_φ)
        rcases this with ⟨s, t_to_s, (⟨s_sat, notequi⟩ | ⟨in_s, w_s, rest_s_free⟩)⟩
        · -- "Together wit the observation ..."
          absurd notequi
          apply claim _ t_to_s s_sat
        · -- We now claim that we have a contradiction with the outer IH as we left the cluster:
          absurd IH s ?_
          exact ⟨W, M, w, w_s⟩
          -- simp only [Sequent.without_normal_isFree_iff_isFree] at rest_s_free
          -- Remains to show that s is simpler than t. We use ePropB.
          constructor
          · exact t_to_s
          · have : (nodeAt t).isLoaded := by
              unfold Sequent.isLoaded
              simp [AnyNegFormula.in_side] at in_t
              aesop
            apply ePropB.e_help _ _ this rest_s_free t_to_s
      case cons β δ =>
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
        simp [evaluate, not_forall, Classical.not_imp] at this
        rw [← @boxes_last] at this
        simp_rw [evalBoxes] at this
        push_neg at this
        rcases this with ⟨w, v_β_w, u, w_δα_u, u_not_φ⟩
        have v_βδα_u : relateSeq M (β :: (δ ++ [α])) v u := by
          -- use v_β_w, u, w_δα_u
          sorry -- should be easy
        -- We make all the steps with `loadedDiamondPaths` now (not just for β as before).
        have in_t : (~''(AnyFormula.loaded (⌊β⌋AnyFormula.loadBoxes (δ ++ [α]) (AnyFormula.normal φ)))).in_side _theSide (nodeAt t) := by
          simp_all only [nodeAt, loadMulti_cons]
          subst lf_def
          sorry -- exact O_def
        have := loadedDiamondPaths β (δ ++ [α]) tab Root_isFree t v_ φ in_t v_βδα_u u_not_φ
        rcases this with ⟨s, t_to_s, s_property⟩
        rcases s_property with ⟨s_sat, notequi⟩ | ⟨not_af_in_s, w_s, rest_s_free⟩
        · -- We left the cluster, use outer IH to get contradiction.
          absurd IH s (ePropB.g s t t_to_s (by rw [cEquiv.symm]; exact notequi))
          -- need that `s` is satisfiable
          exact s_sat
        · -- Here is the case where s is still loaded and in the same cluster.
          absurd IH s ?_
          exact ⟨W, M, u, w_s⟩
          -- simp only [Sequent.without_normal_isFree_iff_isFree] at rest_s_free
          -- Remains to show that s is simpler than t. We use ePropB.
          constructor
          · exact t_to_s
          · have : (nodeAt t).isLoaded := by
              unfold Sequent.isLoaded
              simp [AnyNegFormula.in_side] at in_t
              aesop
            apply ePropB.e_help _ _ this rest_s_free t_to_s

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
