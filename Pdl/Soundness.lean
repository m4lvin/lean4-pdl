import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Vector.Defs
import Pdl.TableauPath
import Mathlib.Data.ENat.Defs

import Pdl.LocalSoundness

/-! # Soundness (Section 6) -/

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
  case modL L R a χ X_def Y_def =>
    subst X_def Y_def
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
  case modR L R a χ X_def Y_def =>
    subst X_def Y_def
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
      simp at k_lt_lpr
      exact k_lt_lpr
    exact loaded_con ⟨k, h1⟩ h2

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
    rcases aeb with ⟨Hist, X, nrep, nbas, lt, next, Y, Y_in, tabAt_a_def, b_def⟩
                  | ⟨Hist, X, nrep, bas, Y, r, next, tabAt_a_def, b_def⟩
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
      exact non_multisetEqTo_of_ltSequent
        (@endNodesOf_nonbasic_lt_Sequent (nodeAt a) (nodeAt b) lt nbas Y_in)
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
      case freeL δ α φ X_def Y_def =>
        cases X_def
        subst Y_def
        have help : (tabAt b).snd.fst = (List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) LX, RX, none) := by
          rw [tabAt_b_def]
        simp only [help] at con
        simp_all
      case freeR δ α φ X_def Y_def =>
        cases X_def
        subst Y_def
        have help : (tabAt b).snd.fst = (LX, List.insert (~⌈⌈δ⌉⌉⌈α⌉φ) RX, none) := by
          rw [tabAt_b_def]
        simp only [help] at con
        simp_all
      case modL LX' RX' n ξ X_def Y_def =>
        subst Y_def
        rw [X_def] at con
        cases ξ
        case normal φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = ((~φ) :: projection n LX', projection n RX', none) := by
            rw [tabAt_b_def]
          simp only [help] at con
          simp_all
        case loaded φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = ( projection n LX'
                                          , projection n RX'
                                          , some (Sum.inl (~'φ))) := by rw [tabAt_b_def]
          simp only [help] at con
          have := con.2.2
          simp at this
          cases this
      case modR LX' RX' n ξ X_def Y_def =>  -- same as modL
        subst Y_def
        rw [X_def] at con
        cases ξ
        case normal φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = ( projection n LX'
                                          , (~φ) :: projection n RX'
                                          , none) := by rw [tabAt_b_def]
          simp only [help] at con
          simp_all
        case loaded φ =>
          simp at tabAt_b_def
          have help : (tabAt b).snd.fst = ( projection n LX'
                                          , projection n RX'
                                          , some (Sum.inr (~'φ))) := by rw [tabAt_b_def]
          simp only [help] at con
          have := con.2.2
          simp at this
          cases this
  exact node_ne node_eq

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

/-- Given a tableau node, return its cluster as an element in the `cEquiv` quotient.
Suffices for Soundness, but for Interpolation we need something "more constructive". -/
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
    Std.Irrefl (@before X tab) := by
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
    Std.Irrefl (Relation.TransGen (@before X tab)) := by
  rw [Relation.transGen_eq_self before.trans]
  exact before.irrefl

/-- The `before` relation in a tableau is well-founded. -/
theorem before.wellFounded :
    WellFounded (@before X tab) :=
  Finite.wellfounded_of_irrefl_TC _ trans_before.irrefl

/-- The converse of `<ᶜ` is irreflexive. -/
theorem flip_before.irrefl :
    Std.Irrefl (flip (@before X tab)) := by
  constructor
  intro p
  simp [flip, before]

/-- The transtive closure of the converse of `<ᶜ` is irreflexive. -/
theorem trans_flip_before.irrefl :
    Std.Irrefl (Relation.TransGen (flip (@before X tab))) := by
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
  simp_all only [edge, cEquiv, before]
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
    simp only [LE.le] at this
    exact Relation.ReflTransGen_or_left this
  · unfold cEdge
    apply Relation.ReflTransGen_or_right
    exact Relation.ReflTransGen.single comp

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
  have ⟨k, k', def_c, def_t, k'_le_k⟩ :=
    exists_rewinds_middle comp_leq_t (Relation.TransGen.to_reflTransGen t_above_l)
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
  cases t_free

theorem ePropB.c {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt s).isFree → s < t → s <ᶜ t := by
  intro s_free slt
  constructor
  · apply Relation.TransGen_or_left; exact slt
  · intro con
    unfold cEdge at con
    induction con using Relation.TransGen.head_induction_on
    case right.single t hyp =>
      cases hyp
      case inl tes =>
        absurd slt
        exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
      case inr ths =>
        have con := (companion_loaded ths).2
        simp [Sequent.isFree] at s_free
        rw [con] at s_free
        contradiction
    case right.head t k t_k k_s ih =>
      apply ih
      cases t_k
      case inl tes => exact (Relation.TransGen.trans slt (Relation.TransGen.single tes))
      case inr khs => exact c_claim s t k s_free slt khs

theorem not_cEquiv_of_free_loaded (s t : PathIn tab)
    (s_free : (nodeAt s).isFree) (t_loaded : (nodeAt t).isLoaded) :
    ¬ s ≡ᶜ t := by
  rintro ⟨s_t, t_s⟩
  unfold cEdge at s_t
  induction s_t using Relation.ReflTransGen.head_induction_on
  case refl =>
    simp [Sequent.isFree] at s_free
    rw [s_free] at t_loaded
    contradiction
  case head s l s_l l_t ih =>
    by_cases (nodeAt l).isFree
    case pos l_free => exact ih l_free (Relation.ReflTransGen.tail t_s s_l)
    case neg l_loaded =>
      cases s_l
      case inl sel =>
        have scl := ePropB.c s l s_free (Relation.TransGen.single sel)
        absurd scl.2
        have l_s : l ◃* s := Relation.ReflTransGen.trans l_t t_s
        cases eq_or_ne l s
        case inl les =>
          simp_all
        case inr lnes => exact Relation.TransGen_of_ReflTransGen l_s lnes
      case inr shl =>
        have con := (companion_loaded shl).1
        simp [Sequent.isFree] at s_free
        rw [con] at s_free
        contradiction

theorem ePropB.d {tab : Tableau .nil X} (s t : PathIn tab) :
    (nodeAt t).isFree → s < t → s <ᶜ t := by
intro t_free slt
constructor
· apply Relation.TransGen_or_left; exact slt
· intro con
  unfold cEdge at con
  induction con using Relation.TransGen.head_induction_on
  case right.single t hyp =>
    cases hyp
    case inl tes =>
      absurd slt
      exact edge.TransGen_isAsymm.1 t s (Relation.TransGen.single tes)
    case inr ths =>
      have con := (companion_loaded ths).1
      simp [Sequent.isFree] at t_free
      rw [con] at t_free
      contradiction
  case right.head t k t_k k_s ih =>
    by_cases (nodeAt k).isFree
    case pos k_free =>
      cases t_k
      case inl tek => exact ih k_free (Relation.TransGen.tail slt tek)
      case inr thk =>
        have con := (companion_loaded thk).1
        simp [Sequent.isFree] at t_free
        rw [con] at t_free
        contradiction
    case neg k_loaded =>
      simp [Sequent.isFree] at k_loaded
      apply not_cEquiv_of_free_loaded t k t_free k_loaded
      constructor
      · exact Relation.ReflTransGen.single t_k
      · exact Relation.ReflTransGen.trans
          (Relation.TransGen.to_reflTransGen k_s)
          (Relation.ReflTransGen_or_left (Relation.TransGen.to_reflTransGen slt))

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
  intro t_loaded s_free t_s s_t
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
  intro s_u u_t not_t_u t_s
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

/-- Previously called `simpler_equiv_simpler`. -/
theorem ePropB.i {tab : Tableau .nil X} (s u t : PathIn tab) :
    (s <ᶜ u  →  s ≡ᶜ t  →  t <ᶜ u) := by
  intro u_simpler_s s_equiv_t
  rcases u_simpler_s with ⟨s_c_u, not_u_c_s⟩
  rcases s_equiv_t with ⟨_, t_s⟩
  constructor
  · exact Relation.TransGen.trans_right t_s s_c_u
  · intro u_c_t
    absurd not_u_c_s
    exact Relation.TransGen.trans_left u_c_t t_s

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

set_option maxHeartbeats 10000000 in -- for simp and aesop timeouts
/-! Specific case of `loadedDiamondPaths` for `Tableau.pdl`. -/
lemma loadedDiamondPathsPDL
  (α : Program)
  (X : Sequent)
  (tab : Tableau [] X)
  (t : PathIn tab)
  {W}
  {M : KripkeModel W}
  {v w : W}
  (v_t : (M, v) ⊨ nodeAt t)
  (ξ : AnyFormula)
  {side : Side}
  (negLoad_in : (~''(AnyFormula.loaded (⌊α⌋ξ))).in_side side (nodeAt t))
  (v_α_w : relate M α v w)
  (w_nξ : (M, w) ⊨ ~''ξ)
  {Hist : History}
  {Z Y : Sequent}
  (bas : Z.basic)
  (r : PdlRule Z Y)
  (nrep : ¬rep Hist Z)
  (next : Tableau (Z :: Hist) Y)
  (tabAt_t_def : tabAt t = ⟨Hist, ⟨Z, Tableau.pdl nrep bas r next⟩⟩) :
  ∃ s, t ◃⁺ s ∧
        ( satisfiable (nodeAt s) ∧ ¬s ≡ᶜ t
        ∨   (~''ξ).in_side side (nodeAt s)
          ∧ (M, w) ⊨ nodeAt s
          ∧ ((nodeAt s).without (~''ξ)).isFree) := by
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
  case freeL L R δ β φ Z_def Y_def =>
    subst Z_def Y_def
    -- Leaving cluster, interesting that IH is not needed here.
    -- Define child node with path to to it:
    let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
    let s : PathIn tab := t.append t_to_s
    have tabAt_s_def : tabAt s = ⟨_, _, next⟩ := by
      unfold s t_to_s
      rw [tabAt_append]
      -- Only some HEq business left here.
      have : tabAt (.pdl .nil : PathIn (Tableau.pdl nrep bas (PdlRule.freeL rfl rfl) next))
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
      refine ⟨Hist, _, nrep, bas, _, (PdlRule.freeL rfl rfl), next, ?_⟩
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
  case freeR L R δ β φ Z_def Y_def =>
    subst Z_def Y_def
    -- Leaving cluster, interesting that IH is not needed here.
    -- Define child node with path to to it:
    let t_to_s : PathIn (tabAt t).2.2 := (tabAt_t_def ▸ .pdl .nil)
    let s : PathIn tab := t.append t_to_s
    have tabAt_s_def : tabAt s = ⟨_, _, next⟩ := by
      unfold s t_to_s
      rw [tabAt_append]
      -- Only some HEq business left here.
      have : tabAt (.pdl .nil : PathIn (.pdl nrep bas (.freeR rfl rfl) next))
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
      refine ⟨Hist, _, nrep, bas, _, (.freeR rfl rfl), next, ?_⟩
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
  case modL L R a ξ' Z_def Y_def =>
    subst Y_def
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
    have helper : (∃ φ, ξ' = .normal φ
                    ∧ nodeAt s = ((~φ) :: projection a L, projection a R, none))
                ∨ (∃ χ, ξ' = .loaded χ
                    ∧ nodeAt s = (projection a L, projection a R, some (Sum.inl (~'χ)))) := by
      subst Z_def
      unfold nodeAt
      unfold s t_to_s
      rw [tabAt_append]
      -- remains to deal with HEq business
      let tclean : PathIn (.pdl nrep bas (.modL (Eq.refl _) rfl) next) := .pdl .nil
      cases ξ'
      case normal φ =>
        left
        use φ
        simp only [true_and]
        simp at next
        have : (tabAt tclean).2.1 = ((~φ) :: projection a L, projection a R, none) := by
          have : tabAt tclean = ⟨ _ :: _, (_, _, none) , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
      case loaded χ =>
        right
        use χ
        simp only [true_and]
        simp at next
        have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inl (~'χ))) := by
          have : tabAt tclean = ⟨ _, (_, _, some (Sum.inl (~'χ))) , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
    -- ... it is then obvious that `s` satisfies the required properties:
    use s -- was: refine ⟨s , ?_, Or.inr ⟨?_a, ?_b, ?_c⟩⟩ -- FIXME: change back? see other cases
    constructor
    · constructor
      constructor
      right
      refine ⟨Hist, _, nrep, bas, _, (.modL Z_def rfl), next, tabAt_t_def, ?_⟩
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
            case inr.inr =>
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
  case modR L R a ξ' Z_def Y_def => -- COPY ADAPTATION from `modL`
    subst Y_def
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
    have helper : (∃ φ, ξ' = .normal φ
                    ∧ nodeAt s = (projection a L, (~φ) :: projection a R, none))
                ∨ (∃ χ, ξ' = .loaded χ
                    ∧ nodeAt s = (projection a L, projection a R, some (Sum.inr (~'χ)))) := by
      subst Z_def
      unfold nodeAt
      unfold s t_to_s
      rw [tabAt_append]
      -- remains to deal with HEq business
      let tclean : PathIn (.pdl nrep bas (.modR (Eq.refl _) rfl) next) := .pdl .nil
      cases ξ'
      case normal φ =>
        left
        use φ
        simp only [true_and]
        simp at next
        have : (tabAt tclean).2.1 = (projection a L, (~φ) :: projection a R, none) := by
          have : tabAt tclean = ⟨ _ :: _, _ , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
      case loaded χ =>
        right
        use χ
        simp only [true_and]
        simp at next
        have : (tabAt tclean).2.1 = (projection a L, projection a R, some (Sum.inr (~'χ))) := by
          have : tabAt tclean = ⟨_, (_, _, some (Sum.inr (~'χ))) , next⟩ := by unfold tabAt; rfl
          rw [this]
        convert this <;> (try rw [tabAt_t_def]) <;> simp [tclean]
    -- ... it is then obvious that `s` satisfies the required properties:
    -- refine ⟨s, ?_, Or.inr ⟨?_a', ?_b', ?_c'⟩⟩ -- annoying that ' are needed here?
    -- FIXME? refine is suddenly not working here?
    use s
    constructor
    · constructor
      constructor
      right
      refine ⟨Hist, _, nrep, bas, _, (PdlRule.modR Z_def rfl), next, tabAt_t_def, ?_⟩
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
            case inr.inr =>
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

lemma SemImply_loadedNormal_ofSeqAndNormal {M u}
  (w_nφ : (M, w) ⊨ (~φ))
  (u_αs_w : relateSeq M αs u w) :
    (M, u)⊨~''(AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
  induction αs generalizing u w
  case nil => simp_all; exact w_nφ
  case cons β βs ih =>
    have ⟨v, ⟨u_β_v, v_βs_w⟩⟩ := u_αs_w
    simp [vDash.SemImplies] at *
    refine ⟨v, ⟨u_β_v, ?_⟩⟩
    have := ih w_nφ v_βs_w
    cases f_def : AnyFormula.loadBoxes βs (AnyFormula.normal φ)
    <;> rw [f_def] at this <;> simp_all [AnyFormula.unload]

lemma firstBox_isAtomic_of_basic (Y_bas : Y.basic)
    (anf_in_Y : (~''(AnyFormula.loadBoxes (β :: βs) (AnyFormula.normal φ))).in_side side Y) :
    β.isAtomic := by
  rcases Y with ⟨L,R,O⟩
  cases side
  all_goals
    unfold Sequent.basic at Y_bas
    simp at Y_bas
    have := fun h => Y_bas.1 (~⌈β⌉⌈⌈βs⌉⌉φ) (Or.inr (Or.inr h))
    unfold AnyNegFormula.in_side at anf_in_Y
    simp at *
    subst anf_in_Y
    simp [AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload] at *
    specialize this ?_
    · exact AnyFormula.loadBoxes_unload_eq_boxes
    cases β <;> simp_all [Program.isAtomic]

/-- Key helper lemma to show the soundness of loading and repeats.
Intutively, it says that a tableau starting with a loaded diamond can immitate all
possible ways in which a Kripke model can satisfy that diamond.

The lemma statement differs slightly from the paper version:

- Our paths cannot stop "inside" a `LocalTableau` and they may take apart more than one loaded box,
  hence we need access to *all* of the boxes `αs` in front of the normal formula `φ`.
- We do _not_ say that the path from `t` to `s` has to be satisfiable.
- We only demand `s` to be satisfiable in the free case. For the other disjunct this is implied.

The paper proof uses three nested induction levels, one of them only in the star case.
Instead of that here we use recursive calls and show that they terminate via the lexicographic order
on the `ℕ∞ × Nat × Nat` triple `⟨distance_list M v w (α :: αs), lengthOfProgram α, t.length⟩`.
The star case is then actually handled just like the other connectives.
-/
theorem loadedDiamondPaths (α : Program) (αs : List Program) {X : Sequent}
  (tab : Tableau .nil X) -- .nil to prevent repeats from "above"
  (root_free : X.isFree) -- ADDED / not/implicit in Notes?
  (t : PathIn tab)
  {W}
  {M : KripkeModel W} {v w : W}
  (v_t : (M, v) ⊨ nodeAt t)
  (φ : Formula)
  {side : Side} -- not in notes but needed for partition
  (negLoad_in : (~''(⌊α⌋AnyFormula.loadBoxes αs φ)).in_side side (nodeAt t))
  (v_α_αs_w : relateSeq M (α :: αs) v w)
  (w_nφ : (M, w) ⊨ (~φ))
  : ∃ s : PathIn tab, t ◃⁺ s ∧
    -- Paper also says here: path from t to s is satisfiable.
    (   ( satisfiable (nodeAt s) ∧ ¬ (s ≡ᶜ t) )  -- Paper has satisfiable outside disjunction.
      ∨ ( ((~''(AnyFormula.normal φ)).in_side side (nodeAt s))
        ∧ (M,w) ⊨ (nodeAt s)
        ∧ (nodeAt s).isFree
        )
    ) := by
  -- We do not need induction, but use `PathIn.init_inductionOn` to first distinguish whether we
  -- are the rooot, and in the step case we look at what happens at the *end* of the path.
  cases t using PathIn.init_inductionOn
  case root =>
    exfalso
    unfold AnyNegFormula.in_side at negLoad_in
    unfold Sequent.isFree Sequent.isLoaded at root_free
    rcases X with ⟨L,R,O⟩
    cases O <;> cases side <;> simp at *
  case step t0 IH s_t0 => -- NOTE: not indenting from here.
  clear IH -- Not needed, came from `PathIn.init_inductionOn`.
  -- Notes first take care of cases where rule is applied to non-loaded formula.
  -- For this, we need to distinguish what happens at `t`.
  rcases tabAt_t_def : tabAt t with ⟨Hist, Z, tZ⟩
  cases tZ
  -- applying a local or a pdl rule or being a repeat?
  case loc nbas ltZ nrep next =>
    rcases α_def : α with a | ⟨α₁, α₂⟩ | ⟨α₁, α₂⟩ | β | τ
    · subst α_def
      have α_atom : (·a : Program).isAtomic := by simp [Program.isAtomic]
      have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
      -- No recursive call or IH needed, just use localTableauTruth to get any end node.
      rcases (localTableauTruth ltZ M v).1 (this ▸ v_t) with ⟨Y, Y_in, w_Y⟩
      have alocLD := atomicLocalLoadedDiamond (·a) ltZ α_atom (AnyFormula.loadBoxes αs φ)
                      (this ▸ negLoad_in) Y Y_in
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
      have negLoad_in_s : (~''((⌊·a⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt s1) := by
        unfold nodeAt ; rw [tabAt_s_def]
        simp_all
      -- NOW: do cases on s1, s1 can NOT be a local tableau,
      cases next_def : (next Y Y_in)
      case loc nbas' _ _ _ =>
        exfalso
        exact nbas' (endNodesOf_basic Y_in)
      case pdl Y' bas' r' nrep' next' =>
        -- first adapt loadedDiamondPathsPDL to list
        have := exists_same_distance_of_relateSeq_cons v_α_αs_w
        rcases this with ⟨u, ⟨v_α_u, u_αs_w, u_minimal⟩⟩
        have u_nαsφ : (M, u)⊨~''(AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
          apply SemImply_loadedNormal_ofSeqAndNormal w_nφ u_αs_w
        have lDPDL := loadedDiamondPathsPDL (·a) X tab s1 v_s1 (AnyFormula.loadBoxes αs φ)
                        negLoad_in_s v_α_u u_nαsφ bas' r' nrep' next' (next_def ▸ tabAt_s_def)
        cases αs_def : αs
        case nil => -- if αs = [] we are done via the s1 we found
          simp_all
          have ⟨s, ⟨s1_s, s_props⟩⟩ := lDPDL
          rcases s_props with ⟨sat_con, eq_con⟩ | inr
          · refine ⟨s, ⟨?_, Or.inl ⟨sat_con, ?_⟩⟩⟩
            · exact Relation.TransGen.head (Or.inl t_s) s1_s
            · exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inl t_s)) s1_s eq_con
          · refine ⟨s, ⟨?_, Or.inr inr⟩⟩
            · exact Relation.TransGen.head (Or.inl t_s) s1_s
        case cons β βs => -- if αs = β :: βs then we do a recursive call
          have ⟨s, ⟨s1_s, s_props⟩⟩ := lDPDL
          rcases s_props with ⟨sat_con, eq_con⟩ | ⟨in_con, u_s, free_con⟩
          · refine ⟨s, ⟨?_, Or.inl ⟨sat_con, ?_⟩⟩⟩
            · exact Relation.TransGen.head (Or.inl t_s) s1_s
            · exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inl t_s)) s1_s eq_con
          · have _forTermination_loc_atom_pdl :
                distance_list M u w (β :: βs) < distance_list M v w (·a :: αs) := by
              rw [← αs_def]
              rw [u_minimal]
              simp_all [relate, distance]
              have := distance_list_iff_relate_Seq.2 u_αs_w
              cases dist_list_def : (distance_list M u w (β :: βs))
              · exfalso ; exact this dist_list_def
              · have := ENat.coe_one
                rw [←this]
                simp only [←ENat.coe_add, ENat.coe_lt_coe, lt_add_iff_pos_left, Nat.lt_one_iff]
            have ⟨k, ⟨s_k, k_props⟩⟩ :=
              loadedDiamondPaths β βs tab root_free s u_s φ (αs_def ▸ in_con) (αs_def ▸ u_αs_w) w_nφ
            clear _forTermination_loc_atom_pdl
            rcases k_props with ⟨sat_con, eq_con⟩ | inr
            · refine ⟨k, ⟨?_, Or.inl ⟨sat_con, ?_⟩⟩⟩
              · exact Relation.TransGen.head (Or.inl t_s) (Relation.TransGen.trans s1_s s_k)
              · apply ePropB.g_tweak _ _ _ (Relation.TransGen.head (Or.inl t_s) s1_s) s_k eq_con
            · refine ⟨k, ⟨?_, Or.inr inr⟩⟩
              · exact Relation.TransGen.head (Or.inl t_s) (Relation.TransGen.trans s1_s s_k)
      -- Here we need to go to the companion.
      -- We will make a recursive call, and for termination note that the path becomes shorter.
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
        have negLoad_in_u : (~''((⌊·a⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt u) := by
          rw [AnyNegFormula.in_side_of_multisetEqTo u_eq_t]
          exact negLoad_in
        -- Now prepare and make the recursive call:
        have _forTermination :
            (companionOf t (tabAt_t_def ▸ next_def ▸ lpr) h).length < t'.length := by
          apply path_then_length_lt
          apply Relation.TransGen_of_ReflTransGen
          · apply edge_revEuclideanHelper t' u t t'_s (companion_lt t_comp_u)
          · intro con
            unfold u at t_comp_u
            rw [con] at t_comp_u
            exact not_edge_and_heart (And.intro t'_s t_comp_u)
        have := loadedDiamondPaths (·a) αs tab root_free u v_u φ negLoad_in_u v_α_αs_w w_nφ
        rcases this with ⟨s, u_s, (⟨s_sat, not_s_u⟩|reached)⟩
        all_goals
          refine ⟨s, ?_, ?_⟩
          exact Relation.TransGen.trans (Relation.TransGen.trans
            (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
            (Relation.TransGen_or_right (Relation.TransGen.single t_comp_u))) u_s
        · refine Or.inl ⟨s_sat, ?_⟩
          refine ePropB.g_tweak t' u s ?_ u_s not_s_u
          · exact Relation.TransGen.trans
              (Relation.TransGen_or_left (Relation.TransGen.single t'_s))
              (Relation.TransGen_or_right (Relation.TransGen.single t_comp_u))
        · exact Or.inr reached
    all_goals -- all other cases for α! (even including ∗, other than in paper)
        have : nodeAt t = Z := by unfold nodeAt; rw [tabAt_t_def]
        have Z_free := Z.without_loaded_in_side_isFree (⌊α⌋AnyFormula.loadBoxes αs φ)
                         side (this ▸ negLoad_in)
        have locLD := localLoadedDiamondList (α :: αs) ltZ v_α_αs_w
                        (this ▸ v_t) φ (this ▸ negLoad_in) Z_free w_nφ
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
        rcases free_or_newLoadform
          with  Y_is_Free
              | ⟨F, δ, anf_in_Y, v_seq_w, dist_eq, v_F, Fδ_in_H, Y_almost_free⟩
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
          cases δ
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
          -- Here is the interesting case: not leaving the cluster.
          -- We get a sequence of worlds from the δ relation:
          case cons β βs =>
            have anf_in_s1 : (~''((⌊β⌋AnyFormula.loadBoxes βs φ))).in_side side (nodeAt s1) := by
              convert anf_in_Y
              unfold nodeAt
              rw [tabAt_s_def]
            have _for_termination_all : lengthOfProgram β < lengthOfProgram α := by
              have := endNodesOf_basic Y_in
              have : β.isAtomic := firstBox_isAtomic_of_basic this anf_in_Y
              rw [Program.isAtomic_iff] at this
              rcases this with ⟨b, β_def⟩
              subst α_def β_def
              have := lengthOfProgram_gt_zero
              simp only [lengthOfProgram]
              try rw [add_assoc]
              try simp only [lt_add_iff_pos_right]
              simp [this]
              try omega
            have ⟨s, s1_s, s_cons⟩ :=
              loadedDiamondPaths β βs tab root_free s1 v_s1 φ anf_in_s1 v_seq_w w_nφ
            rcases s_cons with ⟨sat_con, ne_con⟩ | inr
            · refine ⟨s, ?_, Or.inl ⟨sat_con, ?_⟩⟩
              · exact Relation.TransGen.head (Or.inl t_s) s1_s
              · exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inl t_s)) s1_s ne_con
            · refine ⟨s, ?_, Or.inr inr⟩
              · exact Relation.TransGen.head (Or.inl t_s) s1_s
  case pdl Y bas r nrep next => -- handled mainly by helper
    have := exists_same_distance_of_relateSeq_cons v_α_αs_w
    rcases this with ⟨u, ⟨v_α_u, u_αs_w, u_minimal⟩⟩
    have u_nαsφ : (M, u)⊨~''(AnyFormula.loadBoxes αs (AnyFormula.normal φ)) := by
      apply SemImply_loadedNormal_ofSeqAndNormal w_nφ u_αs_w
    have lDPDL := loadedDiamondPathsPDL α X tab t v_t (AnyFormula.loadBoxes αs φ)
                    negLoad_in v_α_u u_nαsφ bas r nrep next tabAt_t_def
    cases αs_def : αs
    case nil => -- if αs = [] we are done via the s we found
      simp_all
    case cons β βs => -- if αs = β :: βs then we do a recursive call
      have ⟨s1, ⟨t_s1, s1_props⟩⟩ := lDPDL
      rcases s1_props with inl | ⟨in_con, u_s1, free_con⟩
      · refine ⟨s1, ⟨t_s1, Or.inl inl⟩⟩
      · have _forTermination_pdl :
            distance_list M u w (β :: βs) < distance_list M v w (α :: αs) := by
          have : α.isAtomic := by
            apply firstBox_isAtomic_of_basic bas
            convert negLoad_in
            · unfold nodeAt
              rw [tabAt_t_def]
          rw [Program.isAtomic_iff] at this
          rcases this with ⟨a, α_def⟩
          subst α_def
          rw [u_minimal]
          simp_all only [relate]
          have := distance_list_iff_relate_Seq.2 u_αs_w
          cases dist_list_def : (distance_list M u w (β :: βs))
          · exfalso ; exact this dist_list_def
          · simp [distance, v_α_u]
            have := ENat.coe_one
            rw [←this]
            simp only [←ENat.coe_add, ENat.coe_lt_coe, lt_add_iff_pos_left, Nat.lt_one_iff]
        have ⟨s, ⟨s1_s, s_props⟩⟩ :=
          loadedDiamondPaths β βs tab root_free s1 u_s1 φ (αs_def ▸ in_con) (αs_def ▸ u_αs_w) w_nφ
        clear _forTermination_pdl
        rcases s_props with ⟨sat_con, eq_con⟩ | inr
        · refine ⟨s, ⟨?_, Or.inl ⟨sat_con, ?_⟩⟩⟩
          · exact Relation.TransGen.trans t_s1 s1_s
          · exact ePropB.g_tweak _ _ _ t_s1 s1_s eq_con
        · refine ⟨s, ⟨?_, Or.inr inr⟩⟩
          · exact Relation.TransGen.trans t_s1 s1_s
  case lrep lpr =>
    -- Here we need to go to the companion.
    -- We will make a recursive call, and for termination note that the path becomes shorter.
    have h : (tabAt t).snd.snd = .lrep (tabAt_t_def ▸ lpr) := by
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
    have negLoad_in_u : (~''((⌊α⌋AnyFormula.loadBoxes αs φ))).in_side side (nodeAt u) := by
      rw [AnyNegFormula.in_side_of_multisetEqTo u_eq_t]
      exact negLoad_in
    -- Now prepare and make the recursive call:
    have _forTermination_lrep : (companionOf t (tabAt_t_def ▸ lpr) h).length < t.length := by
      apply companionOf_length_lt_length
    have := loadedDiamondPaths α αs tab root_free u v_u φ negLoad_in_u v_α_αs_w w_nφ
    rcases this with ⟨s, u_s, (⟨s_sat, not_s_u⟩|reached)⟩
    all_goals
      refine ⟨s, ?_, ?_⟩
      exact Relation.TransGen.head (Or.inr ⟨tabAt_t_def ▸ lpr, h, rfl⟩) u_s
    · refine Or.inl ⟨s_sat, ?_⟩
      exact ePropB.g_tweak _ _ _ (Relation.TransGen.single (Or.inr t_comp_u)) u_s not_s_u
    · exact Or.inr reached
    termination_by
      (⟨distance_list M v w (α :: αs), lengthOfProgram α, t.length⟩ : ℕ∞ × Nat × Nat)
    decreasing_by
      · subst α_def
        exact Prod.Lex.left _ _ _forTermination_loc_atom_pdl
      · subst α_def
        exact Prod.Lex.right _ (Prod.Lex.right _ _forTermination)
      · rw [dist_eq]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ _for_termination_all)
      · rw [dist_eq]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ _for_termination_all)
      · rw [dist_eq]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ _for_termination_all)
      · rw [dist_eq]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ _for_termination_all)
      · exact Prod.Lex.left _ _ _forTermination_pdl
      · exact Prod.Lex.right _ (Prod.Lex.right _ _forTermination_lrep)

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
  by_cases Sequent.isFree (nodeAt t)
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
          apply Classical.by_contradiction
          intro hyp
          absurd s_sat
          -- use IH and Lemma to show claim
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
          rw [@relateSeq_cons]
          use w
        -- We make all the steps with `loadedDiamondPaths` now (not just for β as before).
        have in_t : (~''((⌊β⌋AnyFormula.loadBoxes (δ ++ [α]) φ))).in_side _theSide (nodeAt t) := by
          unfold _theSide
          try apply LoadFormula.in_side_of_lf_inl
          try apply LoadFormula.in_side_of_lf_inr
          simp_all [nodeAt, loadMulti_cons]
          apply loadMulti_eq_loadBoxes
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
  · exact tableauThenNotSat tabl (by simp) .nil
  · exact tableauThenNotSat tabl (by simp) .nil

/-- All provable formulas are semantic tautologies.
See `tableauThenNotSat` for what the notes call soundness. -/
theorem soundness : ∀ φ, provable φ → tautology φ := by
  intro φ prov
  apply notsatisfnotThenTaut
  rw [← singletonSat_iff_sat]
  apply soundTableau
  exact prov
