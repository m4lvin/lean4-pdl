import Mathlib.Data.Finset.Basic

import Pdl.TableauPath

/-! # Interpolants for Partitions (big part of Section 7) -/

open HasSat

def Olf.L : Olf → List Formula
| none => []
| some (Sum.inl ⟨lf⟩) => [~ lf.unload]
| some (Sum.inr _) => []

@[simp]
lemma Olf.L_none : Olf.L none = [] := by rfl
@[simp]
lemma Olf.L_inr : Olf.L (some (Sum.inr lf)) = [] := by rfl

def Olf.R : Olf → List Formula
| none => []
| some (Sum.inl _) => []
| some (Sum.inr ⟨lf⟩) => [~ lf.unload]

@[simp]
lemma Olf.R_none : Olf.R none = [] := by rfl
@[simp]
lemma Olf.R_inl : Olf.R (some (Sum.inl lf)) = [] := by rfl

@[simp]
def Sequent.left (X : Sequent) : List Formula := X.L ++ X.O.L
@[simp]
def Sequent.right (X : Sequent) : List Formula := X.R ++ X.O.R

/-- Joint vocabulary of all parts of a `Sequent`. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).fvoc ∩ (X.right).fvoc

def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ((~θ) :: X.left) ∧ ¬ satisfiable (θ :: X.right))

def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

/-- This is like `Olf.voc` but without the ⊕ inside. -/
def onlfvoc : Option NegLoadFormula → Vocab
| none => ∅
| some nlf => NegLoadFormula.voc nlf

def lfovoc (L : List (List Formula × Option NegLoadFormula)) : Vocab :=
  L.toFinset.sup (fun ⟨fs,o⟩ => fs.fvoc ∪ (onlfvoc o))

lemma LoadRule_voc (lr : LoadRule (~'χ) ress) : lfovoc ress ⊆ χ.voc := by
  intro x x_in
  unfold lfovoc at x_in
  simp at x_in
  rcases x_in with ⟨fs, onlf, in_ress, x_in_V⟩
  cases lr
  case dia α χ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α χ.unload
    rw [← unfoldDiamondLoaded_eq α χ] at unfvoc
    specialize @unfvoc (pairUnload (fs, onlf)) (by simp only [List.mem_map]; use (fs,onlf))
    rcases onlf with _ | ⟨⟨lf⟩⟩  <;> simp [onlfvoc] at *
    · rcases x_in_V with ⟨f, f_in_fs, x_in⟩
      specialize unfvoc f_in_fs
      aesop
    · simp [pairUnload] at unfvoc
      rcases x_in_V with ⟨f, f_in_fs, x_in⟩|_ <;> aesop
  case dia' α φ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α φ
    rw [← unfoldDiamondLoaded'_eq α φ] at unfvoc
    specialize @unfvoc (pairUnload (fs, onlf)) (by simp only [List.mem_map]; use (fs,onlf))
    rcases onlf with _ | ⟨⟨lf⟩⟩  <;> simp [onlfvoc] at *
    · rcases x_in_V with ⟨f, f_in_fs, x_in⟩
      specialize unfvoc f_in_fs
      aesop
    · simp [pairUnload] at unfvoc
      rcases x_in_V with ⟨f, f_in_fs, x_in⟩|_ <;> aesop

theorem localRule_does_not_increase_vocab_L {Cond B}
    (rule : LocalRule Cond B) :
    ∀ res ∈ B, res.left.fvoc ⊆ Cond.left.fvoc := by
  rcases Cond with ⟨Lcond, Rcond, Ocond⟩
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedL ress orule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp at *
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedL ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    simp only [List.fvoc, Vocab.fromList, Sequent.left, Sequent.L, Sequent.O, List.map_append,
      List.toFinset_append, Finset.mem_sup, Finset.mem_union, List.mem_toFinset, List.mem_map,
      id_eq, List.empty_eq, List.nil_append, exists_exists_and_eq_and] at *
    rcases x_in_res with ⟨φvoc, ⟨φ, φ_in_L, def_φvoc⟩|⟨φ, φ_in_OlfL, def_φvoc⟩, x_in_φvoc⟩
    all_goals
      subst def_φvoc
      simp only [Olf.L, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, Formula.voc]
      have := LoadRule_voc lrule
      simp only [lfovoc, List.fvoc, Vocab.fromList, LoadFormula.voc] at this
      apply this; clear this
      simp [onlfvoc]
      refine ⟨L, lnf, in_ress, ?_⟩
    · left
      use φ
    · right
      cases lnf <;> simp [Olf.L] at *
      subst φ_in_OlfL
      exact x_in_φvoc
  case loadedR B_def =>
    simp [List.fvoc, Olf.L] at *
    subst_eqs
    rcases x_in_res with ⟨φ, φ_in_Olf, x_in_φvoc⟩
    absurd x_in_φvoc
    aesop
  -- other cases are all trivial (as in Bml)
  all_goals
    simp at *
  · aesop

theorem localRule_does_not_increase_vocab_R (rule : LocalRule Cond B) :
    ∀ res ∈ B, res.right.fvoc ⊆ Cond.right.fvoc := by
  rcases Cond with ⟨Lcond, Rcond, Ocond⟩
  intro res res_in_B x x_in_res
  cases rule
  case oneSidedR ress orule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, L_in, def_res⟩
    subst def_res
    simp at *
    rcases x_in_res with ⟨ψ, ψ_in, x_in_voc_ψ⟩
    cases orule
    case nCo => aesop
    case box α φ α_notAt => have := unfoldBox_voc L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedR ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    simp only [List.fvoc, Vocab.fromList, Sequent.right, Sequent.R, Sequent.O, List.map_append,
      List.toFinset_append, Finset.mem_sup, Finset.mem_union, List.mem_toFinset, List.mem_map,
      id_eq, List.empty_eq, List.nil_append, exists_exists_and_eq_and] at *
    rcases x_in_res with ⟨φvoc, ⟨φ, φ_in_L, def_φvoc⟩|⟨φ, φ_in_OlfR, def_φvoc⟩, x_in_φvoc⟩
    all_goals
      subst def_φvoc
      simp only [Olf.R, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left, Formula.voc]
      have := LoadRule_voc lrule
      simp only [lfovoc, List.fvoc, Vocab.fromList, LoadFormula.voc] at this
      apply this; clear this
      simp [onlfvoc]
      refine ⟨L, lnf, in_ress, ?_⟩
    · left
      use φ
    · right
      cases lnf <;> simp [Olf.R] at *
      subst φ_in_OlfR
      exact x_in_φvoc
  case loadedL B_def =>
    simp [List.fvoc, Olf.R] at *
    subst_eqs
    rcases x_in_res with ⟨φ, φ_in_Olf, x_in_φvoc⟩
    absurd x_in_φvoc
    aesop
  -- other cases are all trivial (as in Bml)
  all_goals
    simp at *
  · aesop

lemma jvoc_sub_of_voc_sub {Y X : Sequent}
    (hl : Y.left.fvoc ⊆ X.left.fvoc)
    (hr : Y.right.fvoc ⊆ X.right.fvoc)
    : jvoc Y ⊆ jvoc X := by
  intro x x_in_jY
  simp only [jvoc, Finset.mem_inter] at x_in_jY
  specialize @hl x x_in_jY.1
  specialize @hr x x_in_jY.2
  simp only [jvoc, Finset.mem_inter]
  tauto

theorem localRuleApp_does_not_increase_jvoc (ruleA : LocalRuleApp X C) :
    ∀ Y ∈ C, jvoc Y ⊆ jvoc X := by
  match ruleA with
  | @LocalRuleApp.mk L R C ress O Lcond Rcond Ocond lrule hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp [applyLocalRule] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩ , res_in, cLRO_def⟩
    simp at cLRO_def
    cases cLRO_def
    apply jvoc_sub_of_voc_sub -- hhmmm?
    · intro x x_in
      simp at * -- only
      rcases x_in with ⟨φvoc, ⟨φ, φ_nocon, d_φvoc⟩|⟨φ, φ_L, d_φvoc⟩|⟨φ, φ_O, d_φvoc⟩, x_in_φvoc⟩
      all_goals subst d_φvoc
      · refine ⟨φ.voc, Or.inl ?_, x_in_φvoc⟩
        exact ⟨φ, List.diff_subset L Lcond φ_nocon, rfl⟩
      all_goals
        have Lsub := @localRule_does_not_increase_vocab_L _ _ lrule _ res_in x
        simp at Lsub
      · specialize Lsub φ.voc (Or.inl ⟨_, φ_L, rfl⟩) x_in_φvoc
        rcases Lsub with ⟨ψvoc, h_ψvoc, x_in_ψvoc⟩
        refine ⟨ψvoc, ?_, x_in_ψvoc⟩
        rcases h_ψvoc with (⟨ψ, ψ_in_Lcond, d_ψvoc⟩ | ⟨ψ, ψ_in_Ocond, d_ψvoc⟩) <;> subst d_ψvoc
        · exact Or.inl ⟨ψ, preconditionProof.1.subset ψ_in_Lcond, rfl⟩
        · refine Or.inr ⟨ψ, ?_, rfl⟩; aesop
      · -- whether to use φ.voc depends on whether the localRuleApp changes the O here.
        rcases O with _|χ <;> rcases Ocond with _|cχ <;> rcases Ores with _|resχ
        all_goals
          simp [Olf.change] at * -- already treats 3 cases
        · specialize Lsub φ.voc (Or.inr ⟨φ, φ_O, rfl⟩) x_in_φvoc
          rcases Lsub with ⟨ψ, ψ_in_Lcond, x_in_φvoc⟩
          exact ⟨ψ, preconditionProof.1.subset ψ_in_Lcond, x_in_φvoc⟩
        · rcases χ with ⟨⟨χ⟩⟩|⟨χ⟩ <;> simp [Olf.L] at *
          subst φ_O
          aesop
        · rcases resχ with ⟨⟨resχ⟩⟩|⟨⟨resχ⟩⟩ <;> simp [Olf.L] at φ_O Lsub
          subst φ_O
          simp at x_in_φvoc
          specialize Lsub (resχ.unload).voc (Or.inr rfl) x_in_φvoc
          rcases Lsub with ⟨ψ, ψ_in_Lcond, x_in_φvoc⟩
          exact ⟨ψ.voc, Or.inl ⟨ψ, preconditionProof.1.subset ψ_in_Lcond, rfl⟩, x_in_φvoc⟩
        · rcases preconditionProof with ⟨Lin, Rin, same_form⟩
          subst same_form
          simp at φ_O
        · specialize Lsub φ.voc (Or.inr ⟨φ, φ_O, rfl⟩) x_in_φvoc
          rcases Lsub with ⟨ψvoc, ψ_defs, x_in_ψvoc⟩
          rcases ψ_defs with ⟨ψ, ψ_in, ψvoc_def⟩|⟨ψ, ψ_in, ψvoc_def⟩ <;> subst ψvoc_def
          · exact ⟨ψ.voc, Or.inl ⟨ψ, preconditionProof.1.subset ψ_in, rfl⟩, x_in_ψvoc⟩
          · refine ⟨ψ.voc, Or.inr ⟨ψ, ?_, rfl⟩, x_in_ψvoc⟩
            simp_all
    · -- analogous to L side, but quite some modifications
      intro x x_in
      simp at * -- only
      rcases x_in with ⟨φvoc, ⟨φ, φ_nocon, d_φvoc⟩|⟨φ, φ_L, d_φvoc⟩|⟨φ, φ_O, d_φvoc⟩, x_in_φvoc⟩
      all_goals subst d_φvoc
      · refine ⟨φ.voc, Or.inl ?_, x_in_φvoc⟩
        exact ⟨φ, List.diff_subset R Rcond φ_nocon, rfl⟩
      all_goals
        have Rsub := @localRule_does_not_increase_vocab_R _ _ lrule _ res_in x
        simp at Rsub
      · specialize Rsub φ.voc (Or.inl ⟨_, φ_L, rfl⟩) x_in_φvoc
        rcases Rsub with ⟨ψvoc, h_ψvoc, x_in_ψvoc⟩
        refine ⟨ψvoc, ?_, x_in_ψvoc⟩
        rcases h_ψvoc with (⟨ψ, ψ_in_Rcond, d_ψvoc⟩ | ⟨ψ, ψ_in_Ocond, d_ψvoc⟩) <;> subst d_ψvoc
        · exact Or.inl ⟨ψ, preconditionProof.2.1.subset ψ_in_Rcond, rfl⟩
        · refine Or.inr ⟨ψ, ?_, rfl⟩; aesop
      · -- whether to use φ.voc depends on whether the localRuleApp changes the O here.
        rcases O with _|χ <;> rcases Ocond with _|cχ <;> rcases Ores with _|resχ
        all_goals
          simp [Olf.change] at * -- already treats 3 cases
        · specialize Rsub φ.voc (Or.inr ⟨φ, φ_O, rfl⟩) x_in_φvoc
          rcases Rsub with ⟨ψ, ψ_in_Rcond, x_in_φvoc⟩
          exact ⟨ψ, preconditionProof.2.subset ψ_in_Rcond, x_in_φvoc⟩
        · rcases χ with ⟨⟨χ⟩⟩|⟨χ⟩ <;> simp [Olf.R] at *
          subst φ_O
          aesop
        · rcases resχ with ⟨⟨resχ⟩⟩|⟨⟨resχ⟩⟩ <;> simp [Olf.R] at φ_O Rsub
          subst φ_O
          simp at x_in_φvoc
          specialize Rsub (resχ.unload).voc (Or.inr rfl) x_in_φvoc
          rcases Rsub with ⟨ψ, ψ_in_Rcond, x_in_φvoc⟩
          exact ⟨ψ.voc, Or.inl ⟨ψ, preconditionProof.2.subset ψ_in_Rcond, rfl⟩, x_in_φvoc⟩
        · rcases preconditionProof with ⟨Lin, Rin, same_form⟩
          subst same_form
          simp at φ_O
        · specialize Rsub φ.voc (Or.inr ⟨φ, φ_O, rfl⟩) x_in_φvoc
          rcases Rsub with ⟨ψvoc, ψ_defs, x_in_ψvoc⟩
          rcases ψ_defs with ⟨ψ, ψ_in, ψvoc_def⟩|⟨ψ, ψ_in, ψvoc_def⟩ <;> subst ψvoc_def
          · refine ⟨ψ.voc, Or.inl ⟨ψ, preconditionProof.2.1.subset ψ_in, rfl⟩, x_in_ψvoc⟩
          · refine ⟨ψ.voc, Or.inr ⟨ψ, ?_, rfl⟩, x_in_ψvoc⟩
            simp_all

/-- Maehara's method for local rule applications.
This is `itpLeaves` for singleton clusters in the notes, but not only. -/
def localInterpolantStep (L R : List Formula) (o) (ruleA : LocalRuleApp (L,R,o) C)
    (subθs : Π c ∈ C, PartInterpolant c)
    : PartInterpolant (L,R,o) := by
  -- UNPACKING TERMS
  rcases def_ruleA : ruleA with @⟨L, R, C, ress, O, Lcond, Rcond, Ocond, rule, hc, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use dis interList
    constructor
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · have locSound := @localRuleTruth _ _ ruleA
      constructor
      all_goals
        rintro ⟨W,M,w,w_⟩
        specialize locSound M w
      ·
        sorry -- See Bml?
      ·
        sorry -- See Bml?
  case oneSidedR orule =>
    let interList :=  (C.attach).map $ λ⟨c, cinC⟩ => (subθs c cinC).1
    use Con interList
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp [interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · intro L_and_nθ_sat
      sorry -- See Bml?
    · intro R_and_θ_sat
      sorry -- See Bml?

  case LRnegL φ =>
    use φ
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      aesop
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 φ
      simp_all
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp] at *
      subst_eqs
      absurd w_.1
      have := w_.2 (~φ)
      simp_all [evaluate]

  case LRnegR φ =>
    use ~φ
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      aesop
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 (~φ)
      simp_all [evaluate]
    · rintro ⟨W, M, w, w_⟩
      simp only [List.empty_eq, List.mem_cons, forall_eq_or_imp, evaluate] at *
      subst_eqs
      absurd w_.1
      have := w_.2 φ
      simp_all

  case loadedL =>
    -- keep interpolant the same
    sorry
  case loadedR =>
    -- keep interpolant the same
    sorry


/-- The exits of a cluster: (C \ C+). -/
-- IDEA: similar to endNodesOf?
def exitsOf : (tab : Tableau Hist (L, R, some nlf)) → List (PathIn tab)
| .lrep lpr => [] -- a repeat is never an exit
| .loc _ _ lt next => sorry -- TODO: can the exit be "inside" lt? Or can we filter `endNodesOf lt`?
| .pdl _ _ _ next => sorry -- TODO: if (L-) then root of next is exit, also if (M) removes loading etc?

-- TODO move to Soundness.lean ?
def PathIn.children : (p : PathIn tab) → List (PathIn tab) := sorry

/-- C+ -/
def plus_exits {X} {tab : Tableau .nil X} (C : List (PathIn tab)) : List (PathIn tab) :=
  C ++ (C.map (fun p => p.children)).flatten

/-- W.l.o.g version of `clusterInterpolation`. -/
def clusterInterpolation_right {Hist L R nlf}
    (tab : Tableau Hist (L, R, some (Sum.inr nlf)))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some (Sum.inr nlf)) := by
  sorry

/-- Given a tableau where the root is loaded, and exit interpolants, interpolate the root. -/
def clusterInterpolation {Hist L R snlf}
    (tab : Tableau Hist (L, R, some snlf))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some snlf) := by
  cases snlf
  case inl nlf =>
    -- TODO: "flip" the left/right sides of `tab` so we can apply the wlog version.
    sorry
  case inr nlf =>
    exact @clusterInterpolation_right _ _ _ nlf tab exitIPs

def tabToInt {X : Sequent} (tab : Tableau .nil X) :
    PartInterpolant X := by
  sorry
