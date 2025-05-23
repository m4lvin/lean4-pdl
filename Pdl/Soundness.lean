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
        -- Do we need an induction on δ here?
        -- Note: already strengthened IH to work for other programs.
        refine ⟨?_Y, ⟨ ⟨_, ⟨(L ++ F, R, some (Sum.inl (~'⌊⌊δ⌋⌋χ'))), claim, rfl⟩ , ?_⟩ , ?_⟩⟩
        ·
          sorry -- Do not know yet which end node to pick!
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

theorem loadedDiamondPaths (α : Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M,v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  {side : Side} -- not in notes but needed for partition
  (negLoad_in : (~''(⌊α⌋ξ)).in_side side (nodeAt t))
  (v_α_w : relate M α v w)
  (w_nξ : (M,w) ⊨ ~''ξ)
  : ∃ s : PathIn tab, t ◃⁺ s ∧
    -- maybe TODO: missing here: path from t to s is satisfiable!
    (   ( satisfiable (nodeAt s) ∧ ¬ (s ≡ᶜ t) )  -- maybe: move satisfiable outside disjunction?
      ∨ ( ((~''ξ).in_side side (nodeAt s))
        ∧ (M,w) ⊨ (nodeAt s)
        ∧ ((nodeAt s).without (~''ξ)).isFree
        )
    ) := by

  -- outer induction on the program (do it with recursive calls!)

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
      have locLD := localLoadedDiamond (·a) ltZ v_α_w (this ▸ v_t) _ (this ▸ negLoad_in) w_nξ
      rcases locLD with ⟨Y, Y_in, w_Y, free_or_newLoadform⟩
      have alocLD := atomicLocalLoadedDiamond (·a) ltZ α_atom ξ (this ▸ negLoad_in) Y Y_in
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
      have negLoad_in_s : (~''(AnyFormula.loaded (⌊·a⌋ξ))).in_side side (nodeAt s1) := by
        unfold nodeAt ; rw [tabAt_s_def]
        simp_all
      -- NOW: do cases on s1, s1 can NOT be a local tableau,
      cases next_def : (next Y Y_in)
      case loc nbas' _ _ _ =>
        exfalso
        exact nbas' (endNodesOf_basic Y_in)
      case pdl Y' bas' r' nrep' next' =>
        rename' tabAt_t_def => tabAt_t'_def
        rename' t => t'
        rename' t_s => t'_s
        rename' s1 => t
        rename' tabAt_s_def => tabAt_t_def
        rename' negLoad_in => negLoad_in_t
        rename' negLoad_in_s => negLoad_in
        rename' v_s1 => v_t
        rename' Y' => Y
        rename' bas' => bas
        rename' r' => r
        rename' nrep' => nrep
        rename' next => next_prev
        rename' next' => next

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
          let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ next_def ▸ PathIn.pdl PathIn.nil)
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
            convert this <;> try rw [tabAt_t_def, next_def]
            simp_all [eqRec_heq_iff_heq]
          refine ⟨s, ?_, Or.inl ⟨?_, ?_⟩ ⟩
          · apply Relation.TransGen.tail (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
            left
            right
            unfold s t_to_s
            refine ⟨Z :: Hist, _, ?_, bas, _, PdlRule.freeL, next, ?_⟩
            · simp_all [tabAt_t_def]
            · rw [next_def] at tabAt_t_def
              use tabAt_t_def
              convert rfl
              simp_all [eqRec_heq_iff_heq]
          · use W, M, v
            intro φ φ_in
            rw [tabAt_s_def] at φ_in
            apply v_t -- Let's use that t and s are equivalent if they only differ in loading
            rw [tabAt_t_def]
            aesop
          · apply ePropB.g_tweak t' t s (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
            · have t_s : t ⋖_ s := by
                right
                refine ⟨Z :: Hist, _, nrep, bas, _, PdlRule.freeL, next, next_def ▸ tabAt_t_def, ?_⟩
                simp [s, t_to_s]
                convert rfl
                simp_all [eqRec_heq_iff_heq]
              exact Relation.TransGen_or_left (Relation.TransGen.single t_s)
            · apply not_cEquiv_of_free_loaded
              · simp only [Sequent.isFree, Sequent.isLoaded, nodeAt, decide_false, decide_true,
                           Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_true']
                rw [tabAt_s_def]
              · simp only [Sequent.isLoaded, nodeAt, decide_false, decide_true]
                rw [tabAt_t_def]
        case freeR L R δ β φ =>  -- copy in freeL
          let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ next_def ▸ PathIn.pdl PathIn.nil)
          let s : PathIn tab := t.append t_to_s
          have tabAt_s_def : tabAt s = ⟨_, _, next⟩ := by
            unfold s t_to_s
            rw [tabAt_append]
         --   Only some HEq business left here.
            have : tabAt (.pdl .nil : PathIn (.pdl nrep bas .freeR next))
                   = ⟨ (L, R, some (Sum.inr (~'⌊⌊δ⌋⌋⌊β⌋AnyFormula.normal φ))) :: _
                   , ⟨L, (List.insert (~⌈⌈δ⌉⌉⌈β⌉φ) R), none⟩, next⟩ := by
              unfold tabAt
              unfold tabAt
              rfl
            convert this <;> try rw [tabAt_t_def, next_def]
            simp_all [eqRec_heq_iff_heq]
          refine ⟨s, ?_, Or.inl ⟨?_, ?_⟩ ⟩
          · apply Relation.TransGen.tail (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
            left
            right
            unfold s t_to_s
            refine ⟨Z :: Hist, _, ?_, bas, _, PdlRule.freeR, next, ?_⟩
            · simp_all [tabAt_t_def]
            · rw [next_def] at tabAt_t_def
              use tabAt_t_def
              convert rfl
              simp_all [eqRec_heq_iff_heq]
          · use W, M, v
            intro φ φ_in
            rw [tabAt_s_def] at φ_in
            apply v_t -- Let's use that t and s are equivalent if they only differ in loading
            rw [tabAt_t_def]
            aesop
          · apply ePropB.g_tweak t' t s (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
            · have t_s : t ⋖_ s := by
                right
                refine ⟨Z :: Hist, _, nrep, bas, _, PdlRule.freeR, next, next_def ▸ tabAt_t_def, ?_⟩
                simp [s, t_to_s]
                convert rfl
                simp_all [eqRec_heq_iff_heq]
              exact Relation.TransGen_or_left (Relation.TransGen.single t_s)
            · apply not_cEquiv_of_free_loaded
              · simp only [Sequent.isFree, Sequent.isLoaded, nodeAt, decide_false, decide_true,
                           Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_true']
                rw [tabAt_s_def]
              · simp only [Sequent.isLoaded, nodeAt, decide_false, decide_true]
                rw [tabAt_t_def]
        case modL L R a' ξ' Z_def =>
          have : ξ' = ξ := by
            unfold nodeAt at negLoad_in
            rw [tabAt_t_def] at negLoad_in
            unfold AnyNegFormula.in_side at negLoad_in
            cases side <;> simp_all
          subst this
        --  modal rule, so α must actually be atomic!
          have a_is_a' : a = a' := by
            simp only [AnyNegFormula.in_side, nodeAt] at negLoad_in
            rw [tabAt_t_def] at negLoad_in
            subst Z_def
            cases side
            all_goals
              simp only at negLoad_in
              subst_eqs
            rfl
          subst a_is_a'
          simp at v_α_w
          -- Let `s` be the unique child:
          let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ next_def ▸ PathIn.pdl PathIn.nil)
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
              convert this <;> (try rw [tabAt_t_def, next_def]) <;> simp [tclean]
            case loaded χ =>
              right
              use χ
              simp only [true_and]
              simp at next
              have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inl (~'χ))) := by
                have : tabAt tclean = ⟨ _, (projection a L, projection a R, some (Sum.inl (~'χ))) , next⟩ := by unfold tabAt; rfl
                rw [this]
              convert this <;> (try rw [tabAt_t_def, next_def]) <;> simp [tclean]
          -- ... it is then obvious that `s` satisfies the required properties:
          refine ⟨s, ?_, Or.inr ⟨?_a, ?_b, ?_c⟩⟩
          · have t_s : t ⋖_ s := by
              right
              refine ⟨Z :: Hist, _, nrep, bas, _, (.modL Z_def), next, next_def ▸ tabAt_t_def, ?_⟩
              simp [s, t_to_s]
              convert rfl
              simp_all [eqRec_heq_iff_heq]
            exact Relation.TransGen.trans (Relation.TransGen_or_left (Relation.TransGen.single t'_s)) (Relation.TransGen_or_left (Relation.TransGen.single t_s)) -- theres a shorter way
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
        case modR L R a' ξ' Z_def => -- COPY ADAPTATION from `modL`
          have : ξ' = ξ := by
            unfold nodeAt at negLoad_in
            rw [tabAt_t_def] at negLoad_in
            unfold AnyNegFormula.in_side at negLoad_in
            cases side <;> simp_all
          subst this
          -- modal rule, so α must actually be atomic!
          have a_is_a' : a = a' := by
            simp only [AnyNegFormula.in_side, nodeAt] at negLoad_in
            rw [tabAt_t_def] at negLoad_in
            subst Z_def
            cases side
            all_goals
              simp only at negLoad_in
              subst_eqs
            rfl
          subst a_is_a'
          simp at v_α_w
          -- Let `s` be the unique child:
          let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ next_def ▸ .pdl .nil)
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
              convert this <;> (try rw [tabAt_t_def, next_def]) <;> simp [tclean]
            case loaded χ =>
              right
              use χ
              simp only [true_and]
              simp at next
              have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inr (~'χ))) := by
                have : tabAt tclean = ⟨ _, (projection a L, projection a R, some (Sum.inr (~'χ))) , next⟩ := by unfold tabAt; rfl
                rw [this]
              convert this <;> (try rw [tabAt_t_def, next_def]) <;> simp [tclean]
          -- ... it is then obvious that `s` satisfies the required properties:
          refine ⟨s, ?_, Or.inr ⟨?_a', ?_b', ?_c'⟩⟩ -- annoying that ' are needed here?
          · have t_s : t ⋖_ s := by
              right
              refine ⟨Z :: Hist, _, nrep, bas, _, (.modR Z_def), next, next_def ▸ tabAt_t_def, ?_⟩
              simp [s, t_to_s]
              convert rfl
              simp_all [eqRec_heq_iff_heq]
            exact Relation.TransGen.trans (Relation.TransGen_or_left (Relation.TransGen.single t'_s)) (Relation.TransGen_or_left (Relation.TransGen.single t_s)) -- theres a shorter way
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
        have negLoad_in_u : (~''(AnyFormula.loaded (⌊·a⌋ξ))).in_side side (nodeAt u) := by
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
        have := loadedDiamondPaths (·a) tab root_free u v_u ξ negLoad_in_u v_α_w w_nξ
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
      unfold relate at v_α_w
      have ⟨n, ⟨ws, ⟨v_head, ⟨w_tail, rel⟩⟩⟩⟩:= ReflTransGen.to_finitelyManySteps v_α_w
      have claim : ∀ k : Fin n.succ, -- Note the succ here!
          ∃ sk, t ◃⁺ sk ∧ ( ( satisfiable (nodeAt sk) ∧ ¬(sk ≡ᶜ t) )
                          ∨ ( (~''(AnyFormula.loaded (⌊∗β⌋ξ))).in_side side (nodeAt sk)
                            ∧ (M, ws[k]) ⊨ nodeAt sk
                            ∧ ((nodeAt sk).without (~''(AnyFormula.loaded (⌊∗β⌋ξ)))).isFree
                            ∧ True )) := by -- this needs to be replaced with something saying ⌊∗β⌋ξ is principal at sk
        intro k
        induction k using Fin.inductionOn
        case zero =>
          have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
          have locLD := localLoadedDiamond (∗β) ltZ v_α_w (this ▸ v_t) _ (this ▸ negLoad_in) w_nξ
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
          · have h : (∗β) ∈ δ := by sorry
            refine ⟨s1, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
            · apply Relation.TransGen.single
              left
              exact t_s
            · convert anf_in_Y
              · sorry
              · unfold nodeAt ; rw [tabAt_s_def]
            · sorry -- some sort of invertibility in loc??
            · convert Y_almost_free
              · unfold nodeAt ; rw [tabAt_s_def]
              · sorry
            · simp -- ⌊∗β⌋ξ is principal at sk
        case succ k ih =>
          by_cases ws[k.castSucc] = ws[k.succ]
          case pos eq => rw [eq] at ih; exact ih
          case neg ne => -- we need this distinction to show δ ≠ ε (see notes)
            have ⟨sk, t_sk, sk_hyp⟩ := ih
            rcases sk_hyp with ⟨sk_sat, sk_ne_t⟩ | _
            · exact ⟨sk, ⟨t_sk, Or.inl ⟨sk_sat, sk_ne_t⟩⟩⟩
            · have claim : ∀ j : Fin k.succ, ∃ sk, t ◃⁺ sk  -- this claim is in notes (see if needed)
                          ∧ (( (~''(AnyFormula.loaded (⌊∗β⌋ξ))).in_side side (nodeAt sk)
                          ∧ (M, ws[k]) ⊨ nodeAt sk
                          ∧ ((nodeAt sk).without (~''(AnyFormula.loaded (⌊∗β⌋ξ)))).isFree)) := by sorry -- this should be provable with some strong induction and some ePropB stuff, but lets see if needed first
              have ⟨⟨F,δ⟩, ⟨Fδ_in, ⟨wk_F, wk_δ_wk1⟩⟩⟩:= @existsDiamondH W M β ws[k.castSucc] ws[k.succ] (rel k)
              have δ_ne : δ ≠ [] := by
                intro δ_em
                simp [δ_em] at wk_δ_wk1
                exact ne wk_δ_wk1
              have Hβstar_prop : (F, δ ++ [∗β]) ∈ H (∗β) := by  -- this may be wrong? see triple on bottom of page 43
                simp [H]
                refine ⟨[(F, δ ++ [∗β])], ⟨⟨F, ⟨δ, ⟨Fδ_in, by simp [δ_ne]⟩⟩⟩, by simp⟩⟩
              -- PRINCIPAL: since ⌊∗β⌋ξ is principal, there must be a succesor with desired properties
              sorry

      have h : ws[Fin.last n] = w := by rw [w_tail] ; unfold List.Vector.last ; exact Eq.refl _
      have ⟨sn, ⟨t_sn, sn_hyp⟩⟩ := claim (Fin.last n)
      rw [h] at sn_hyp
      -- PRINCIPAL: because ⌊∗β⌋ξ is principal at sn, we can find child s with desired properties
      sorry

    all_goals -- all other cases for α!
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
        · constructor
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
      use s --refine ⟨s, ?_, Or.inr ⟨?_a', ?_b', ?_c'⟩⟩ -- annoying that ' are needed here? FIXME? refine is suddenly not working here?
      constructor
      · constructor
        constructor
        right
        refine ⟨Hist, _, nrep, bas, _, (PdlRule.modR Z_def), next, tabAt_t_def, ?_⟩
        simp [s, t_to_s]
      · right
        constructor
        · subst Z_def
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
        · constructor
          · rcases helper with (⟨φ, ξ'_def, nodeAt_s_def⟩|⟨χ, ξ'_def, nodeAt_s_def⟩)
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
    have negLoad_in_u : (~''(AnyFormula.loaded (⌊α⌋ξ))).in_side side (nodeAt u) := by
      rw [AnyNegFormula.in_side_of_multisetEqTo u_eq_t]
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
      · subst α_def
        apply Prod.Lex.right (lengthOfProgram _) _forTermination
      · exact Prod.Lex.left _ _ _forTermination
      · exact Prod.Lex.left _ _ _forTermination
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
