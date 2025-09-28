import Mathlib.Data.Finset.Basic

import Pdl.Soundness

/-! # Interpolants for Partitions (big part of Section 7)

Note that we can skip much of subsection 7.3 because we worked already with split tableaux anyway.
-/

open HasSat

/-! ## Joint vocabulary -/

/-- The joint vocabulary occurring on both the left and the right side. -/
@[simp]
def jvoc (X : Sequent) : Vocab := (X.left).fvoc ∩ (X.right).fvoc

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

/-! ## Partition Interpolants -/

def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ((~θ) :: X.left) ∧ ¬ satisfiable (θ :: X.right))

def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

/-- Like `Olf.voc` but without the ⊕ inside. -/
def onlfvoc : Option NegLoadFormula → Vocab
| none => ∅
| some nlf => NegLoadFormula.voc nlf

def lfovoc (L : List (List Formula × Option NegLoadFormula)) : Vocab :=
  L.toFinset.sup (fun ⟨fs,o⟩ => fs.fvoc ∪ (onlfvoc o))

/-! ## Interpolants for local rules -/

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

/-- Maehara's method for single-step *local* rule applications.
This covers easy cases without any loaded path repeats.
We do *not* use `localRuleTruth` to prove this,
but the more specific lemmas `oneSidedL_sat_down` and `oneSidedL_sat_down`. -/
def localInterpolantStep L R o C (ruleA : LocalRuleApp (L,R,o) C)
    (subθs : ∀ c ∈ C, PartInterpolant c)
    : PartInterpolant (L,R,o) := by
  -- UNPACKING TERMS
  rcases def_ruleA : ruleA with @⟨L, R, C, YS, O, Lcond, Rcond, Ocond, rule, hc, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL ress orule YS_def => -- rule applied in first component L
    let interList := C.attach.map $ fun c => (subθs c.1 c.2).1
    refine ⟨dis interList, ?_, ?_, ?_⟩ -- disjunction here
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro nInter_L_sat
      have LI_sat : satisfiable (Sequent.left (L, R, o) ∪ (interList.map Formula.neg)) := by
        rcases nInter_L_sat with ⟨W, M, w, w_nInter_L⟩
        use W, M, w
        simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_cons, List.mem_append,
          forall_eq_or_imp, evaluate, disEval, not_exists, not_and] at w_nInter_L
        simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_union_iff, List.mem_append,
          List.mem_map]
        rintro φ (φ_in | ⟨θi,θi_in, φ_def⟩)
        · apply w_nInter_L.2; assumption
        · subst φ_def; apply w_nInter_L.1; assumption
      have := oneSidedL_sat_down ⟨L,R,o⟩ precondProof.1.subset orule YS_def LI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      refine (subθs ⟨L', R', o'⟩ (hc ▸ def_rule ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in; simp at φ_in
      apply w_; simp [interList]; grind
    · rintro ⟨W, M, w, w_⟩
      simp only [Sequent.right, Sequent.R, Sequent.O, List.mem_cons, List.mem_append,
        forall_eq_or_imp, disEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
        interList] at w_
      rcases w_ with ⟨⟨θi, ⟨c, c_in, def_θi⟩, w_θi⟩, w_R⟩
      refine (subθs c (hc ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      have same_R : c.right = Sequent.right (L,R,o) :=
        @oneSidedL_preserves_right (L,R,o) _ precondProof.1.subset _ orule _ YS_def c (hc ▸ c_in)
      rw [same_R]; simp; grind
  case oneSidedR ress orule YS_def => -- rule applied in second component R
    -- Only somewhat analogous to oneSidedR. Part 2 and 3 are flipped around in a way.
    let interList := C.attach.map $ fun c => (subθs c.1 c.2).1
    refine ⟨Con interList, ?_, ?_, ?_⟩ -- using conjunction here
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro ⟨W, M, w, w_⟩
      simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_cons, List.mem_append,
        forall_eq_or_imp, evaluate, conEval, not_forall] at w_
      rcases w_ with ⟨⟨θi, θi_in, w_nθi⟩, w_L⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at θi_in
      rcases θi_in with ⟨⟨L', R', o'⟩, c_in, def_θi⟩
      have same_L : Sequent.left ⟨L', R', o'⟩ = Sequent.left (L,R,o) :=
        @oneSidedR_preserves_left (L,R,o) _ precondProof.2.1.subset _ orule _ YS_def _ (hc ▸ c_in)
      refine (subθs ⟨L', R', o'⟩ (hc ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩
      rw [same_L]; simp; grind
    · rintro inter_R_sat
      have RI_sat : satisfiable (Sequent.right (L, R, o) ∪ (interList)) := by
        rcases inter_R_sat with ⟨W, M, w, w_Inter_R⟩
        use W, M, w; simp [conEval] at *; grind
      have := oneSidedR_sat_down ⟨L,R,o⟩ precondProof.2.1.subset orule YS_def RI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      refine (subθs ⟨L', R', o'⟩ (hc ▸ def_rule ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in; simp at φ_in
      simp [interList] at *
      grind
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
  case loadedL ress χ lrule YS_def =>
    -- similar to oneSidedL case
    simp at YS_def
    let interList := C.attach.map $ fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inl (~'χ)) := by
        have := precondProof.2.2; simp at this; simp; exact this.symm
    refine ⟨dis interList, ?_, ?_, ?_⟩ -- disjunction here
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro nInter_L_sat
      have LI_sat : satisfiable (Sequent.left (L, R, o) ∪ (interList.map Formula.neg)) := by
        rcases nInter_L_sat with ⟨W, M, w, w_nInter_L⟩
        use W, M, w
        simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_cons, List.mem_append,
          forall_eq_or_imp, evaluate, disEval, not_exists, not_and] at w_nInter_L
        simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_union_iff, List.mem_append,
          List.mem_map]
        rintro φ (φ_in | ⟨θi,θi_in, φ_def⟩)
        · apply w_nInter_L.2; assumption
        · subst φ_def; apply w_nInter_L.1; assumption
      have := loadedL_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def LI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      refine (subθs ⟨L', R', o'⟩ (hc ▸ def_rule ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in; simp at φ_in
      apply w_; simp [interList]; grind
    · rintro ⟨W, M, w, w_⟩
      simp only [Sequent.right, Sequent.R, Sequent.O, List.mem_cons, List.mem_append,
        forall_eq_or_imp, disEval, List.mem_map, List.mem_attach, true_and, Subtype.exists,
        interList] at w_
      rcases w_ with ⟨⟨θi, ⟨c, c_in, def_θi⟩, w_θi⟩, w_R⟩
      refine (subθs c (hc ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      have same_R : c.right = Sequent.right (L,R,o) :=
        @loadedL_preserves_right ⟨L,R,o⟩ χ O_is_some ress lrule YS YS_def c (hc ▸ c_in)
      rw [same_R]; simp; grind
  case loadedR ress χ lrule YS_def =>
    -- based on oneSidedR case
    let interList := C.attach.map $ fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inr (~'χ)) := by
      have := precondProof.2.2; simp at this; simp; exact this.symm
    refine ⟨Con interList, ?_, ?_, ?_⟩ -- using conjunction here
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc ruleA Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro ⟨W, M, w, w_⟩
      simp only [Sequent.left, Sequent.L, Sequent.O, List.mem_cons, List.mem_append,
        forall_eq_or_imp, evaluate, conEval, not_forall] at w_
      rcases w_ with ⟨⟨θi, θi_in, w_nθi⟩, w_L⟩
      simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, interList] at θi_in
      rcases θi_in with ⟨⟨L', R', o'⟩, c_in, def_θi⟩
      have same_L : Sequent.left ⟨L', R', o'⟩ = Sequent.left (L,R,o) :=
        @loadedR_preserves_left (L,R,o) _ O_is_some _ lrule _ YS_def _ (hc ▸ c_in)
      refine (subθs ⟨L', R', o'⟩ (hc ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩
      rw [same_L]; simp; grind
    · rintro inter_R_sat
      have RI_sat : satisfiable (Sequent.right (L, R, o) ∪ (interList)) := by
        rcases inter_R_sat with ⟨W, M, w, w_Inter_R⟩
        use W, M, w; simp [conEval] at *; grind
      have := loadedR_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def RI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      refine (subθs ⟨L', R', o'⟩ (hc ▸ def_rule ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in; simp at φ_in
      simp [interList] at *
      grind

/-! ## Cluster tools -/

def repeatsOf {tab : Tableau .nil X} (s : PathIn tab) : List (PathIn tab) :=
  sorry

def all_cEdge {X} {tab : Tableau .nil X} (s : PathIn tab) : List (PathIn tab) :=
  sorry

lemma all_cEdge_spec {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    t ∈ all_cEdge s ↔ ((s ⋖_ t) ∨ s ♥ t) := by
  sorry

def all_cEdge_rev {X} {tab : Tableau .nil X} (t : PathIn tab) : List (PathIn tab) :=
  sorry

lemma all_cEdge_rev_spec {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    s ∈ all_cEdge_rev t ↔ ((s ⋖_ t) ∨ s ♥ t) := by
  sorry

/-- Loaded nodes "below" the given one, also allowing ♥ steps. -/
def loadedBelow : PathIn tab → List (PathIn tab) := sorry

/-- Loaded nodes "above" the given one, also allowing *backwards* ♥ steps. -/
def loadedAbove : PathIn tab → List (PathIn tab) := sorry

/-- List of all other nodes in the same cluster, essentially a constructive version of `clusterOf`.
Computed as the intersection of `loadedAbove` and `loadedBelow`. -/
def clusterListOf (p : PathIn tab) : List (PathIn tab) := loadedBelow p  ∩  loadedBelow p

lemma clusterListOf_spec (p : PathIn tab) :
    q ∈ clusterListOf p  ↔  p ≡ᶜ q := by
  sorry

-- TODO: how to convert `clusterListOf` result back to a tree?
-- Essentially, this would incorporate Lemma 7.22 (a).

def rootOf : List (PathIn tab) → PathIn tab := sorry -- just take the shortest?

-- Or would it be better to already construct (partial) trees instead of lists directly?

-- OR just assume are given the root of a cluster and use the tableau as it is to define `Q`?

/-- Lemma 7.22 (b) for left side -/
lemma cluster_all_left_loaded {p : PathIn tab} (h : (nodeAt p).2.2.isLeft) :
    ∀ q ∈ clusterListOf p, (nodeAt q).2.2.isLeft := by
  sorry

/-- Lemma 7.22 (b) for right side -/
lemma cluster_all_right_loaded {p : PathIn tab} (h : (nodeAt p).2.2.isRight) :
    ∀ q ∈ clusterListOf p, (nodeAt q).2.2.isRight := by
  sorry

def isExitIn : Sequent → List Sequent → Prop := sorry

instance : Decidable (isExitIn X C) := sorry

/-! ## Quasi-Tableaux -/

-- Alternative idea for def 7.31:
-- Instead of labelling nodes in Q with finite sequents, label them with the path to where
-- that sequent comes from in `Λ₂[C⁺]`?

inductive Typ | one | two | three -- lower case because these are not `Type`s.
open Typ

/-- Simple tree data type for `Q`. -/
inductive QuasiTab : Type | QNode : Typ → Sequent → List QuasiTab → QuasiTab
open QuasiTab

-- TODO add invariant?!

def Qchildren (C : List Sequent) : (t : Typ) → (Hist : List Sequent) → (X : Sequent) → List QuasiTab
| .one, Hist, X => -- case k(x)=1
    if X ∈ Hist ∨ isExitIn X C
      then [ ] -- then x is a leaf
      else [ QNode .two X (Qchildren C .two (X :: Hist) X) ]
| .two, Hist, X => -- case k(x)=2
    [ QNode .three X (Qchildren C .three (X :: Hist) X) ]
| .three, Hist, X => -- case k(x)=3
    if X.basic
    then
      -- unique child with .one and result of PDL rule application
      sorry
    else
      -- create children based on local rule
      sorry
termination_by
  1 -- O.o ... see remark after Def 7.31 ;-)
decreasing_by
  · sorry
  · sorry

/-- Quasi-Tableau from Def 7.31.
No names for the nodes as we use an inductive type, so we just write `X` for `Δₓ` -/
def Q {r : PathIn tab} : QuasiTab :=
  let X := nodeAt r -- FIXME wlog we only want the right sequent. But `.R` is not enogh !?!?!?!?!?
  QNode .one X (Qchildren ((clusterListOf r).map nodeAt) .one [] X)

/-! ## Interpolants for proper clusters -/

/-- The exits of a cluster: (C \ C+). -/
-- IDEA: similar to endNodesOf?
def exitsOf : (tab : Tableau Hist (L, R, some nlf)) → List (PathIn tab)
| .lrep lpr => [] -- a repeat is never an exit
| .loc _ _ lt next => sorry -- TODO: can the exit be "inside" lt? Or can we filter `endNodesOf lt`?
| .pdl _ _ _ next => sorry -- TODO: if (L-) then root of next is exit, also if (M) removes loading etc?

-- move to TableauPath.lean later
def PathIn.children : (p : PathIn tab) → List (PathIn tab) := sorry

/-- Exits from a given list of nodes. Something like this should get us from `C` to `C+`. -/
def plus_exits {X} {tab : Tableau .nil X} (C : List (PathIn tab)) : List (PathIn tab) :=
  C ++ (C.map (fun p => p.children)).flatten

/-- W.l.o.g version of `clusterInterpolation` where loaded formula is on the right side. -/
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
