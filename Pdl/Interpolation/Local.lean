import Pdl.Local.Tableau

open HasSat

/-! ## Finset helper lemmas

All lemmas and definitions in this section are not specific to interpolation.
They are only here because during the `List` to `Finset` refactoring we should
not yet touch the other files.  See the `FIXME` comments for where they belong. -/

/-- FIXME: This should be moved to `Pdl/Vocab.lean`, next to `Finset.fvoc`. -/
@[simp]
lemma Finset.mem_fvoc {X : Finset Formula} {x} : x ∈ X.fvoc ↔ ∃ φ ∈ X, x ∈ φ.voc := by
  simp [Finset.fvoc, Vocab.fromFinset, Finset.mem_sup]

/-- FIXME: This should be moved to `Pdl/Vocab.lean`, next to `Finset.fvoc`. -/
@[simp]
lemma Finset.fvoc_union {X Y : Finset Formula} : (X ∪ Y).fvoc = X.fvoc ∪ Y.fvoc := by
  simp [Finset.fvoc, Vocab.fromFinset, Finset.image_union, Finset.sup_union]

/-- FIXME: This should be moved to `Pdl/Vocab.lean`, next to `Finset.fvoc`. -/
lemma Finset.fvoc_mono {X Y : Finset Formula} (h : X ⊆ Y) : X.fvoc ⊆ Y.fvoc := by
  intro x x_in
  rw [Finset.mem_fvoc] at *
  rcases x_in with ⟨φ, φ_in, x_in⟩
  exact ⟨φ, h φ_in, x_in⟩

/-- FIXME: This should be moved to `Pdl/Sequent.lean`, next to `Olf.L`. -/
lemma Olf.L_subset_of_subset {O1 O2 : Olf} (h : O1 ⊆ O2) : O1.L ⊆ O2.L := by
  rcases O1 with _|χ <;> rcases O2 with _|χ' <;> simp_all [Olf.L]

/-- FIXME: This should be moved to `Pdl/Sequent.lean`, next to `Olf.R`. -/
lemma Olf.R_subset_of_subset {O1 O2 : Olf} (h : O1 ⊆ O2) : O1.R ⊆ O2.R := by
  rcases O1 with _|χ <;> rcases O2 with _|χ' <;> simp_all [Olf.R]

/-- FIXME: This should be moved to `Pdl/Sequent.lean`, next to `Olf.L`. -/
lemma Olf.L_sdiff_subset {O Ocond : Olf} : (O \ Ocond).L ⊆ O.L := by
  rcases O with _|χ
  · simp
  rcases Ocond with _|χ'
  · simp
  by_cases h : χ = χ' <;> simp_all [Option.insHasSdiff, Olf.L]

/-- FIXME: This should be moved to `Pdl/Sequent.lean`, next to `Olf.R`. -/
lemma Olf.R_sdiff_subset {O Ocond : Olf} : (O \ Ocond).R ⊆ O.R := by
  rcases O with _|χ
  · simp
  rcases Ocond with _|χ'
  · simp
  by_cases h : χ = χ' <;> simp_all [Option.insHasSdiff, Olf.R]

/-- `Finset` version of `unfoldBox_voc`.
FIXME: This should be moved to `Pdl/Local/UnfoldBox.lean`. -/
theorem unfoldBox_voc_fin {x α φ} {X : Finset Formula} (X_in : X ∈ (unfoldBox α φ).toFinFin)
    {ψ} (ψ_in : ψ ∈ X) (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp only [List.toFinFin, List.mem_toFinset, List.mem_map] at X_in
  rcases X_in with ⟨L, L_in, rfl⟩
  exact unfoldBox_voc L_in (List.mem_toFinset.mp ψ_in) x_in_voc_ψ

/-- `Finset` version of `unfoldDiamond_voc`.
FIXME: This should be moved to `Pdl/Local/UnfoldDia.lean`. -/
theorem unfoldDiamond_voc_fin {x α φ} {X : Finset Formula}
    (X_in : X ∈ (unfoldDiamond α φ).toFinFin)
    {ψ} (ψ_in : ψ ∈ X) (x_in_voc_ψ : x ∈ ψ.voc) : x ∈ α.voc ∨ x ∈ φ.voc := by
  simp only [List.toFinFin, List.mem_toFinset, List.mem_map] at X_in
  rcases X_in with ⟨L, L_in, rfl⟩
  exact unfoldDiamond_voc L_in (List.mem_toFinset.mp ψ_in) x_in_voc_ψ

/-- `Finset` version of `lfovoc`.
FIXME: This should be moved to `Pdl/Sequent.lean`, next to `lfovoc`. -/
def lfovocFin (L : Finset (Finset Formula × Option NegLoadFormula)) : Vocab :=
  L.sup (fun ⟨fs,o⟩ => fs.fvoc ∪ (onlfvoc o))

/-! ## Partition Interpolants -/

def isPartInterpolant (X : Sequent) (θ : Formula) :=
  θ.voc ⊆ jvoc X ∧ (¬ satisfiable ({~θ} ∪ X.left) ∧ ¬ satisfiable ({θ} ∪ X.right))

def PartInterpolant (N : Sequent) := Subtype <| isPartInterpolant N

/-! ## Interpolants for local rules -/

lemma LoadRule.voc (lr : LoadRule (~'χ) ress) : lfovocFin ress ⊆ χ.voc := by
  intro x x_in
  unfold lfovocFin at x_in
  simp only [Finset.mem_sup, Finset.mem_union, Prod.exists] at x_in
  rcases x_in with ⟨fs, onlf, in_ress, x_in_V⟩
  cases lr
  case dia α χ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α χ.unload
    rw [← unfoldDiamondLoaded_eq α χ] at unfvoc
    simp only [List.toFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq,
      Prod.exists] at in_ress
    rcases in_ress with ⟨gs, o, in_ress, def_fs, def_onlf⟩
    subst def_fs def_onlf
    specialize @unfvoc (pairUnload (gs, o)) (by simp only [List.mem_map]; use (gs,o))
    rcases o with _ | ⟨⟨lf⟩⟩  <;> simp [onlfvoc] at *
    · rcases x_in_V with ⟨f, f_in_fs, x_in⟩
      specialize unfvoc f_in_fs
      aesop
    · simp [pairUnload] at unfvoc
      rcases x_in_V with ⟨f, f_in_fs, x_in⟩|_ <;> aesop
  case dia' α φ notAtom =>
    have unfvoc := @unfoldDiamond_voc x α φ
    rw [← unfoldDiamondLoaded'_eq α φ] at unfvoc
    simp only [List.toFinFinOpt, List.mem_toFinset, List.mem_map, Prod.mk.injEq,
      Prod.exists] at in_ress
    rcases in_ress with ⟨gs, o, in_ress, def_fs, def_onlf⟩
    subst def_fs def_onlf
    specialize @unfvoc (pairUnload (gs, o)) (by simp only [List.mem_map]; use (gs,o))
    rcases o with _ | ⟨⟨lf⟩⟩  <;> simp [onlfvoc] at *
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
    case box α φ α_notAt => have := unfoldBox_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedL ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    have hsub := lrule.voc
    have goal_iff : x ∈ (Sequent.left (∅, ∅, some (Sum.inl (~'χ)))).fvoc ↔ x ∈ χ.voc := by
      simp [Sequent.left, Olf.L]
    rw [goal_iff]
    apply hsub
    unfold lfovocFin
    simp only [Finset.mem_sup, Finset.mem_union, Prod.exists]
    refine ⟨L, lnf, in_ress, ?_⟩
    simp only [Sequent.left_eq, Finset.fvoc_union, Finset.mem_union] at x_in_res
    rcases x_in_res with h | h
    · exact Or.inl h
    · right
      rcases lnf with _ | ⟨lf⟩
      · simp [Olf.L] at h
      · simpa [Olf.L, onlfvoc] using h
  -- other cases are all trivial (as in Bml)
  all_goals
    aesop

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
    case box α φ α_notAt => have := unfoldBox_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    case dia => have := unfoldDiamond_voc_fin L_in ψ_in x_in_voc_ψ; simp_all
    all_goals aesop
  case loadedR ress χ lrule B_def =>
    subst B_def
    simp at res_in_B
    rcases res_in_B with ⟨L, lnf, in_ress, def_res⟩
    subst def_res
    have hsub := lrule.voc
    have goal_iff : x ∈ (Sequent.right (∅, ∅, some (Sum.inr (~'χ)))).fvoc ↔ x ∈ χ.voc := by
      simp [Sequent.right, Olf.R]
    rw [goal_iff]
    apply hsub
    unfold lfovocFin
    simp only [Finset.mem_sup, Finset.mem_union, Prod.exists]
    refine ⟨L, lnf, in_ress, ?_⟩
    simp only [Sequent.right_eq, Finset.fvoc_union, Finset.mem_union] at x_in_res
    rcases x_in_res with h | h
    · exact Or.inl h
    · right
      rcases lnf with _ | ⟨lf⟩
      · simp [Olf.R] at h
      · simpa [Olf.R, onlfvoc] using h
  -- other cases are all trivial (as in Bml)
  all_goals
    aesop

theorem localRuleApp_does_not_increase_jvoc (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, jvoc Y ⊆ jvoc lra.X := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Lsub := localRule_does_not_increase_vocab_L lrule _ res_in
    have Rsub := localRule_does_not_increase_vocab_R lrule _ res_in
    simp only [Sequent.left_eq, Sequent.right_eq] at Lsub Rsub
    apply jvoc_sub_of_voc_sub
    · -- left
      have hcond : ∀ y ∈ (Lcond ∪ Ocond.L).fvoc, y ∈ L.fvoc ∨ y ∈ O.L.fvoc := by
        intro y hy
        rw [Finset.fvoc_union, Finset.mem_union] at hy
        rcases hy with h | h
        · exact Or.inl (Finset.fvoc_mono preconditionProof.1 h)
        · exact Or.inr (Finset.fvoc_mono (Olf.L_subset_of_subset preconditionProof.2.2) h)
      have hres : ∀ y ∈ (Lres ∪ Ores.L).fvoc, y ∈ L.fvoc ∨ y ∈ O.L.fvoc :=
        fun y hy => hcond y (Lsub hy)
      intro x x_in
      simp only [LocalRuleApp.X, Sequent.left_eq, Finset.fvoc_union,
        Finset.mem_union] at x_in ⊢
      rcases x_in with (h | h) | h
      · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
      · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
      · rcases Ores with _ | z
        · refine Or.inr (Finset.fvoc_mono ?_ h)
          simpa only [Olf.change, Option.overwrite] using Olf.L_sdiff_subset
        · rw [Olf.change_some] at h
          exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)
    · -- right, analogous to the left
      have hcond : ∀ y ∈ (Rcond ∪ Ocond.R).fvoc, y ∈ R.fvoc ∨ y ∈ O.R.fvoc := by
        intro y hy
        rw [Finset.fvoc_union, Finset.mem_union] at hy
        rcases hy with h | h
        · exact Or.inl (Finset.fvoc_mono preconditionProof.2.1 h)
        · exact Or.inr (Finset.fvoc_mono (Olf.R_subset_of_subset preconditionProof.2.2) h)
      have hres : ∀ y ∈ (Rres ∪ Ores.R).fvoc, y ∈ R.fvoc ∨ y ∈ O.R.fvoc :=
        fun y hy => hcond y (Rsub hy)
      intro x x_in
      simp only [LocalRuleApp.X, Sequent.right_eq, Finset.fvoc_union,
        Finset.mem_union] at x_in ⊢
      rcases x_in with (h | h) | h
      · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
      · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
      · rcases Ores with _ | z
        · refine Or.inr (Finset.fvoc_mono ?_ h)
          simpa only [Olf.change, Option.overwrite] using Olf.R_sdiff_subset
        · rw [Olf.change_some] at h
          exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- Maehara's method for single-step *local* rule applications.
This covers easy cases without any loaded path repeats.
We do *not* use `localRuleTruth` to prove this,
but the more specific lemmas `oneSidedL_sat_down` and `oneSidedL_sat_down`. -/
def localInterpolantStep (lra : LocalRuleApp)
    (subθs : ∀ c ∈ lra.C, PartInterpolant c)
    : PartInterpolant lra.X := by
  -- UNPACKING TERMS
  rcases lra with ⟨L, R, o, Lcond, Rcond, Ocond, ress, rule, C, hC, precondProof⟩
  -- DISTINCTION ON LOCALRULE USED
  cases def_rule : rule
  case oneSidedL ress orule YS_def => -- rule applied in first component L
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    refine ⟨dis interSet.fsort, ?_, ?_, ?_⟩ -- disjunction here
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      rw [Formula.mem_fsort] at φ_in
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, interSet] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc _ Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro nInter_L_sat
      have LI_sat : satisfiable (Sequent.left (L, R, o) ∪ interSet.image Formula.neg) := by
        rcases nInter_L_sat with ⟨W, M, w, w_nInter_L⟩
        refine ⟨W, M, w, ?_⟩
        have w_ndis : ¬ evaluate M w (dis interSet.fsort) :=
          w_nInter_L (~ dis interSet.fsort) (by simp)
        rw [disEval] at w_ndis
        push_neg at w_ndis
        intro φ φ_in
        rcases Finset.mem_union.mp φ_in with h | h
        · exact w_nInter_L φ (Finset.mem_union_right _ h)
        · rcases Finset.mem_image.mp h with ⟨θ, θ_in, def_φ⟩
          subst def_φ
          exact w_ndis θ (Formula.mem_fsort.mpr θ_in)
      have := oneSidedL_sat_down ⟨L,R,o⟩ precondProof.1 orule YS_def LI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
      refine (subθs ⟨L', R', o'⟩ c_in').2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        refine w_ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩))
        simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        exact ⟨(L', R', o'), c_in', rfl⟩
      · exact w_ φ (Finset.mem_union_left _ h)
    · rintro ⟨W, M, w, w_⟩
      have w_dis : evaluate M w (dis interSet.fsort) := w_ _ (by simp)
      rw [disEval] at w_dis
      rcases w_dis with ⟨θi, θi_in, w_θi⟩
      rw [Formula.mem_fsort] at θi_in
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at θi_in
      rcases θi_in with ⟨c, c_in, def_θi⟩
      have same_R : c.right = Sequent.right (L,R,o) :=
        @oneSidedL_preserves_right (L,R,o) _ precondProof.1 _ orule _ YS_def c (hC ▸ c_in)
      refine (subθs c (hC ▸ c_in)).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        rw [def_θi]
        exact w_θi
      · rw [same_R] at h
        exact w_ φ (Finset.mem_union_right _ h)
  case oneSidedR ress orule YS_def => -- rule applied in second component R
    -- Only somewhat analogous to oneSidedL. Part 2 and 3 are flipped around in a way.
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    refine ⟨con interSet.fsort, ?_, ?_, ?_⟩ -- using conjunction here
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      rw [Formula.mem_fsort] at φ_in
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, interSet] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc _ Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro ⟨W, M, w, w_⟩
      have w_ncon : ¬ evaluate M w (con interSet.fsort) :=
        w_ (~ con interSet.fsort) (by simp)
      rw [conEval] at w_ncon
      push_neg at w_ncon
      rcases w_ncon with ⟨θi, θi_in, w_nθi⟩
      rw [Formula.mem_fsort] at θi_in
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at θi_in
      rcases θi_in with ⟨c, c_in, def_θi⟩
      have same_L : c.left = Sequent.left (L,R,o) :=
        @oneSidedR_preserves_left (L,R,o) _ precondProof.2.1 _ orule _ YS_def c (hC ▸ c_in)
      refine (subθs c (hC ▸ c_in)).2.2.1 ⟨W, M, w, ?_⟩
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        rw [def_θi]
        exact w_nθi
      · rw [same_L] at h
        exact w_ φ (Finset.mem_union_right _ h)
    · rintro inter_R_sat
      have RI_sat : satisfiable (Sequent.right (L, R, o) ∪ interSet) := by
        rcases inter_R_sat with ⟨W, M, w, w_Inter_R⟩
        refine ⟨W, M, w, ?_⟩
        have w_con : evaluate M w (con interSet.fsort) := w_Inter_R _ (by simp)
        rw [conEval] at w_con
        intro φ φ_in
        rcases Finset.mem_union.mp φ_in with h | h
        · exact w_Inter_R φ (Finset.mem_union_right _ h)
        · exact w_con φ (Formula.mem_fsort.mpr h)
      have := oneSidedR_sat_down ⟨L,R,o⟩ precondProof.2.1 orule YS_def RI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
      refine (subθs ⟨L', R', o'⟩ c_in').2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        refine w_ _ (Finset.mem_union_right _ ?_)
        simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        exact ⟨(L', R', o'), c_in', rfl⟩
      · exact w_ φ (Finset.mem_union_left _ h)
  case LRnegL φ =>
    use φ
    simp only [LocalRuleApp.X]
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_fvoc.mpr
          ⟨φ, Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self φ)), n_in_φ⟩
      · exact Finset.mem_fvoc.mpr
          ⟨~φ, Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self _)), n_in_φ⟩
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w φ :=
        w_ φ (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self φ))))
      simp only [evaluate] at h1
      exact h1 h2
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w φ :=
        w_ φ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self _))))
      simp only [evaluate] at h2
      exact h2 h1
  case LRnegR φ =>
    use ~φ
    simp only [LocalRuleApp.X]
    refine ⟨?_, ?_, ?_⟩
    · intro n n_in_φ
      simp only [Formula.voc] at n_in_φ
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_fvoc.mpr
          ⟨~φ, Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self _)), n_in_φ⟩
      · exact Finset.mem_fvoc.mpr
          ⟨φ, Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self φ)), n_in_φ⟩
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~~φ) :=
        w_ (~~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.1 (Finset.mem_singleton_self _))))
      simp only [evaluate] at h1 h2
      exact h1 h2
    · rintro ⟨W, M, w, w_⟩
      have h1 : evaluate M w (~φ) :=
        w_ (~φ) (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have h2 : evaluate M w φ :=
        w_ φ (Finset.mem_union_right _
          (Finset.mem_union_left _ (precondProof.2.1 (Finset.mem_singleton_self φ))))
      simp only [evaluate] at h1
      exact h1 h2
  case loadedL ress χ lrule YS_def =>
    -- similar to oneSidedL case
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inl (~'χ)) := by
        have := precondProof.2.2; simp at this; simp; exact this.symm
    refine ⟨dis interSet.fsort, ?_, ?_, ?_⟩ -- disjunction here
    · intro n n_in_inter
      rw [in_voc_dis] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      rw [Formula.mem_fsort] at φ_in
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, interSet] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc _ Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro nInter_L_sat
      have LI_sat : satisfiable (Sequent.left (L, R, o) ∪ interSet.image Formula.neg) := by
        rcases nInter_L_sat with ⟨W, M, w, w_nInter_L⟩
        refine ⟨W, M, w, ?_⟩
        have w_ndis : ¬ evaluate M w (dis interSet.fsort) :=
          w_nInter_L (~ dis interSet.fsort) (by simp)
        rw [disEval] at w_ndis
        push_neg at w_ndis
        intro φ φ_in
        rcases Finset.mem_union.mp φ_in with h | h
        · exact w_nInter_L φ (Finset.mem_union_right _ h)
        · rcases Finset.mem_image.mp h with ⟨θ, θ_in, def_φ⟩
          subst def_φ
          exact w_ndis θ (Formula.mem_fsort.mpr θ_in)
      have := loadedL_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def LI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
      refine (subθs ⟨L', R', o'⟩ c_in').2.2.1 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        refine w_ _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, ?_, rfl⟩))
        simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        exact ⟨(L', R', o'), c_in', rfl⟩
      · exact w_ φ (Finset.mem_union_left _ h)
    · rintro ⟨W, M, w, w_⟩
      have w_dis : evaluate M w (dis interSet.fsort) := w_ _ (by simp)
      rw [disEval] at w_dis
      rcases w_dis with ⟨θi, θi_in, w_θi⟩
      rw [Formula.mem_fsort] at θi_in
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at θi_in
      rcases θi_in with ⟨c, c_in, def_θi⟩
      have same_R : c.right = Sequent.right (L,R,o) :=
        @loadedL_preserves_right ⟨L,R,o⟩ χ O_is_some ress lrule _ YS_def c (hC ▸ c_in)
      refine (subθs c c_in).2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        rw [def_θi]
        exact w_θi
      · rw [same_R] at h
        exact w_ φ (Finset.mem_union_right _ h)
  case loadedR ress χ lrule YS_def =>
    -- based on oneSidedR case
    let interSet : Finset Formula := C.attach.image <| fun c => (subθs c.1 c.2).1
    have O_is_some : Sequent.O (L, R, o) = some (Sum.inr (~'χ)) := by
      have := precondProof.2.2; simp at this; simp; exact this.symm
    refine ⟨con interSet.fsort, ?_, ?_, ?_⟩ -- using conjunction here
    · intro n n_in_inter
      rw [in_voc_con] at n_in_inter
      rcases n_in_inter with ⟨φ, φ_in, n_in_voc_φ⟩
      rw [Formula.mem_fsort] at φ_in
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, interSet] at φ_in
      rcases φ_in with ⟨Y, Y_in, def_φ⟩
      apply localRuleApp_does_not_increase_jvoc _ Y Y_in
      subst def_φ
      exact (subθs Y Y_in).prop.1 n_in_voc_φ
    · rintro ⟨W, M, w, w_⟩
      have w_ncon : ¬ evaluate M w (con interSet.fsort) :=
        w_ (~ con interSet.fsort) (by simp)
      rw [conEval] at w_ncon
      push_neg at w_ncon
      rcases w_ncon with ⟨θi, θi_in, w_nθi⟩
      rw [Formula.mem_fsort] at θi_in
      simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at θi_in
      rcases θi_in with ⟨c, c_in, def_θi⟩
      have same_L : c.left = Sequent.left (L,R,o) :=
        @loadedR_preserves_left (L,R,o) χ O_is_some ress lrule _ YS_def c (hC ▸ c_in)
      refine (subθs c c_in).2.2.1 ⟨W, M, w, ?_⟩
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        rw [def_θi]
        exact w_nθi
      · rw [same_L] at h
        exact w_ φ (Finset.mem_union_right _ h)
    · rintro inter_R_sat
      have RI_sat : satisfiable (Sequent.right (L, R, o) ∪ interSet) := by
        rcases inter_R_sat with ⟨W, M, w, w_Inter_R⟩
        refine ⟨W, M, w, ?_⟩
        have w_con : evaluate M w (con interSet.fsort) := w_Inter_R _ (by simp)
        rw [conEval] at w_con
        intro φ φ_in
        rcases Finset.mem_union.mp φ_in with h | h
        · exact w_Inter_R φ (Finset.mem_union_right _ h)
        · exact w_con φ (Formula.mem_fsort.mpr h)
      have := loadedR_sat_down ⟨L,R,o⟩ χ O_is_some lrule YS_def RI_sat
      rcases this with ⟨⟨L', R', o'⟩, c_in, W, M, w, w_⟩
      have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in
      refine (subθs ⟨L', R', o'⟩ c_in').2.2.2 ⟨W, M, w, ?_⟩ -- given IP property
      intro φ φ_in
      rcases Finset.mem_union.mp φ_in with h | h
      · rw [Finset.mem_singleton] at h
        subst h
        refine w_ _ (Finset.mem_union_right _ ?_)
        simp only [interSet, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
        exact ⟨(L', R', o'), c_in', rfl⟩
      · exact w_ φ (Finset.mem_union_left _ h)

/-! ## Interpolants for Local Tableau -/

def LocalTableau.interpolant (ltX : LocalTableau X)
    (endθs : ∀ Y ∈ endNodesOf ltX, PartInterpolant Y)
    : PartInterpolant X := by
  cases ltX
  case byLocalRule lra nexts X_def =>
    subst X_def
    apply localInterpolantStep lra
    intro Y Y_in
    have IH := LocalTableau.interpolant (nexts Y Y_in)
    exact IH (fun Z Z_in_end => endθs _ (endNodeOfChild_to_endNode lra nexts rfl Y_in Z_in_end))
  case sim Xbas =>
    apply endθs X
    simp [endNodesOf]
