import Pdl.FischerLadner
import Pdl.Tableau

/-! # Staying inside the Fischer-Ladner closure

Here we define what it means for a `Sequent` to be inside the `FL` closure of another, and then
prove several helper lemmas to show that all rules of our tableau system stay in the closure.

Intuitively, we want to say that each step from (L,R,O) in a tableau to (L',R',O') stays in the
FL of (L,R,O). To be precise, each side left/right stays within its own FL closure.
However, this does *not* mean that `L'` must be in the FL of `L`, because the `O` may also
contribute to the left part. This makes `Sequent.subseteq_FL` tricky to define.

-/

/-- Sequent `Y` is a component-wise subset of the FL-closure of `X`.
Note that by component we mean left and right (and not L, R, O).

WORRY: Is using Sequent.O.L here a problem because it might not be injective?
(Because it calls `unload` where both ⌊a⌋⌊b⌋p and ⌊a⌋⌈b⌉p become ⌈a⌉⌈b⌉p.)
-/
def Sequent.subseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
      X.L   ⊆ FLL (Y.L ++ Y.O.L)
    ∧ X.O.L ⊆ FLL (Y.L ++ Y.O.L)
    ∧ X.R   ⊆ FLL (Y.R ++ Y.O.R)
    ∧ X.O.R ⊆ FLL (Y.R ++ Y.O.R)

@[simp]
lemma Sequent.subseteq_FL_refl (X : Sequent) : X.subseteq_FL X := by
  rcases X with ⟨L,R,O⟩
  simp [Sequent.subseteq_FL, FLL_append_eq]

@[simp]
lemma Sequent.subseteq_FL_trans (X Y Z : Sequent) :
    X.subseteq_FL Y → Y.subseteq_FL Z → X.subseteq_FL Z := by
  intro X_Y Y_Z
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [Sequent.subseteq_FL] at *
  have := @FLL_sub_FLL_iff_sub_FLL
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro φ φ_in
  · have : (L' ++ O'.L) ⊆ FLL (L'' ++ O''.L) := by grind
    grind
  · have : (L' ++ O'.L) ⊆ FLL (L'' ++ O''.L) := by grind
    grind
  · have : (R' ++ O'.R) ⊆ FLL (R'' ++ O''.R) := by grind
    grind
  · have : (R' ++ O'.R) ⊆ FLL (R'' ++ O''.R) := by grind
    grind

lemma Sequent.subseteq_FL_of_setEq_right (h : X.setEqTo Y) {Z : Sequent} :
    Z.subseteq_FL X → Z.subseteq_FL Y := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [setEqTo] at h
  rcases h with ⟨L_same, R_same, O_same⟩
  subst O_same
  rintro ⟨hL, hR, hOL, hOR⟩
  simp at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  all_goals
    rw [FLL_append_eq, List.toFinset.ext_iff] at *
    have := FLL_ext L_same
    have := FLL_ext R_same
    grind

lemma Sequent.subseteq_FL_of_setEq_left {X Y : Sequent} (h : X.setEqTo Y) {Z : Sequent} :
    X.subseteq_FL Z → Y.subseteq_FL Z := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [setEqTo] at h
  rcases h with ⟨L_same, R_same, O_same⟩
  subst O_same
  rintro ⟨hL, hR, hOL, hOR⟩
  simp at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  all_goals
    rw [FLL_append_eq, List.toFinset.ext_iff] at *
    have := FLL_ext L_same
    have := FLL_ext R_same
    grind

lemma testsOfProgram_in_FLb {φ α} (φ_in : φ ∈ testsOfProgram α) ψ : φ ∈ FLb α ψ := by
  cases α <;> simp [testsOfProgram] at *
  case sequence α β =>
    simp [FLb]
    right
    right
    rcases φ_in with h|h <;> have IH := testsOfProgram_in_FLb h <;> grind
  case union α β =>
    simp [FLb]
    right
    right
    rcases φ_in with h|h <;> have IH := testsOfProgram_in_FLb h <;> grind
  case star α =>
    have IH := testsOfProgram_in_FLb φ_in (⌈∗α⌉ψ)
    grind [FLb]
  case test τ =>
    simp_all [FLb]

lemma H_tests_in_FL α F δ (in_H : (F, δ) ∈ H α) ψ : F ⊆ FLb α ψ := by
  cases α <;> simp [H] at *
  case atom_prog =>
    grind
  case sequence α β =>
    rcases in_H with ⟨l, ⟨G, γ, in_H, def_l⟩, in_l⟩
    subst def_l
    by_cases γ = []
    · subst_eqs
      simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at in_l
      rcases in_l with ⟨l, ⟨F', δ', in_H', def_l⟩ , in_l⟩
      subst def_l
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at *
      cases in_l ; subst_eqs
      have IHα := H_tests_in_FL _ _ _ in_H
      have IHβ := H_tests_in_FL _ _ _ in_H'
      grind [FLb]
    · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      cases in_l ; subst_eqs
      have IH := H_tests_in_FL α F γ in_H (⌈β⌉ψ)
      grind [FLb]
  case union α β =>
    rcases in_H with in_H|in_H
    all_goals
      have IHα := H_tests_in_FL _ _ _ in_H ψ
      grind [FLb]
  case star α =>
    rcases in_H with ⟨⟨_⟩,⟨_⟩⟩|in_H
    · simp
    · rcases in_H with ⟨l, ⟨G, γ, in_H, def_l⟩, in_l⟩
      subst def_l
      by_cases γ = []
      · subst_eqs
        simp_all
      · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
        cases in_l ; subst_eqs
        have IH := H_tests_in_FL α F γ in_H (⌈∗α⌉ψ)
        grind [FLb]
  case test =>
    cases in_H
    subst_eqs
    simp [FLb]

lemma H_progs_in_FL F δ α (in_H : (F, δ) ∈ H α) ψ : δ ≠ [] → (~⌈⌈δ⌉⌉ψ) ∈ FLb α ψ := by
  cases α <;> simp [H, FLb] at *
  · cases in_H
    subst_eqs
    simp
  case sequence α β =>
    rcases in_H with ⟨l, ⟨G, γ, in_H, def_l⟩, in_l⟩
    subst def_l
    by_cases γ = []
    · subst_eqs
      simp only [↓reduceIte, List.mem_flatten, List.mem_map, Prod.exists] at in_l
      rcases in_l with ⟨l, ⟨F', δ', in_H', def_l⟩ , in_l⟩
      subst def_l
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at *
      cases in_l ; subst_eqs
      have IHα := H_progs_in_FL _ _ _ in_H
      have IHβ := H_progs_in_FL _ _ _ in_H'
      grind [FLb]
    · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
      cases in_l ; subst_eqs
      have IH := H_progs_in_FL _ _ _ in_H (⌈β⌉ψ)
      rw [boxes_append]
      grind
  case union α β =>
    rcases in_H with in_H|in_H
    all_goals
      have IHα := H_progs_in_FL _ _ _ in_H ψ
      grind [FLb]
  case star α =>
    rcases in_H with ⟨⟨_⟩,⟨_⟩⟩|in_H
    · simp
    · rcases in_H with ⟨l, ⟨G, γ, in_H, def_l⟩, in_l⟩
      subst def_l
      by_cases γ = []
      · subst_eqs
        simp_all
      · simp_all only [↓reduceIte, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
        cases in_l ; subst_eqs
        have IH := H_progs_in_FL _ _ _ in_H (⌈∗α⌉ψ)
        rw [boxes_append]
        grind [FLb]
  case test τ =>
    cases in_H
    subst_eqs
    simp

lemma unfoldDiamond_in_FL (α : Program) (ψ : Formula) (X : List Formula) :
    X ∈ unfoldDiamond α ψ → ∀ φ ∈ X, φ ∈ FL (⌈α⌉ψ) := by
  intro X_in φ φ_in
  rcases unfoldDiamondContent α ψ X X_in φ φ_in with φ_def|h|h
  · simp_all [FL]
  · rcases h with ⟨τ, τ_from_α, φ_def⟩
    subst φ_def
    simp only [FL, List.cons_append, List.nil_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (testsOfProgram_in_FLb τ_from_α ψ)))
  · rcases h with ⟨a, δ, φ_def⟩
    subst φ_def
    rcases α with ⟨a⟩|⟨α,β⟩|⟨α,β⟩|⟨α⟩|⟨τ⟩
    case atom_prog =>
      simp [unfoldDiamond, Yset, H] at X_in
      subst X_in
      simp_all only [List.mem_cons, Formula.neg.injEq, Formula.box.injEq, Program.atom_prog.injEq,
        List.not_mem_nil, or_false]
      rcases φ_in with ⟨h1,h2⟩
      subst h1
      exact FL_single_neg_closed fun a => a
    case test =>
      simp only [unfoldDiamond, Yset, H, List.map_cons, Formula.boxes_nil, List.cons_union,
        List.nil_union, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at X_in
      subst X_in
      simp at *
      rcases φ_in with h|h
      · subst h
        simp [FL, FLb]
      · absurd h
        apply Formula.boxes_cons_neq_self
    all_goals -- sequence, union and star case work the same :-)
      simp [unfoldDiamond, Yset] at X_in
      rcases X_in with ⟨F, δ, in_H, def_X⟩
      subst def_X
      simp at φ_in
      rcases φ_in with φ_in|φ_def
      · simp only [FL, List.cons_append, List.nil_append, List.mem_cons, Formula.neg.injEq,
        Formula.box.injEq, reduceCtorEq, false_and, List.mem_append, false_or]
        right
        left
        exact H_tests_in_FL _ _ _ in_H ψ φ_in
      · rw [φ_def]
        simp only [FL, List.cons_append, List.nil_append, List.mem_cons, Formula.neg.injEq,
          List.mem_append]
        right
        right
        left
        apply H_progs_in_FL _ _ _ in_H ψ ?_
        intro hyp
        subst hyp
        rw [Formula.boxes_nil] at φ_def
        absurd φ_def
        apply Formula.boxes_cons_neq_self

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL_left {χ ress} (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteq_FL (Y.1, ∅, Y.2.map Sum.inl) (∅, ∅, some (Sum.inl (~'χ))) := by
  simp only [List.empty_eq, Prod.forall]
  intro F oχ in_ress
  cases lr
  case dia α χ notAt =>
    simp only [Sequent.subseteq_FL, Sequent.L_eq, Sequent.O_eq, Olf.L_inl, LoadFormula.unload,
      List.nil_append, FLL_singelton, Sequent.R_eq, Olf.R_inl, List.append_nil, FLL_nil,
      List.Subset.refl, Olf.R_map_inl, and_self, and_true]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α χ.unload := by
      have := unfoldDiamondLoaded_eq α χ
      grind
    cases oχ <;> grind [FL, pairUnload, unfoldDiamond_in_FL]
  case dia' α φ notAt =>
    simp only [Sequent.subseteq_FL, Sequent.L_eq, Sequent.O_eq, Olf.L_inl, LoadFormula.unload,
      List.nil_append, FLL_singelton, Sequent.R_eq, Olf.R_inl, List.append_nil, FLL_nil,
      List.Subset.refl, Olf.R_map_inl, and_self, and_true]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α φ := by
      have := (unfoldDiamondLoaded'_eq α φ)
      grind
    cases oχ <;> grind [FL, pairUnload, unfoldDiamond_in_FL]

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL_right (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteq_FL (∅, Y.1, Y.2.map Sum.inr) (∅, ∅, some (Sum.inr (~'χ))) := by
  -- copy-pasta based on LoadRule.stays_in_FL_left
  simp only [List.empty_eq, Prod.forall]
  intro F oχ in_ress
  cases lr
  case dia α χ notAt =>
    simp only [Sequent.subseteq_FL, Sequent.L_eq, Sequent.O_eq, Olf.L_inr, List.append_nil, FLL_nil,
      List.Subset.refl, Olf.L_map_inr, Sequent.R_eq, Olf.R_inr, LoadFormula.unload, List.nil_append,
      FLL_singelton, true_and]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α χ.unload := by
      have := unfoldDiamondLoaded_eq α χ
      grind
    cases oχ <;> grind [FL, pairUnload, unfoldDiamond_in_FL]
  case dia' α φ notAt =>
    simp only [Sequent.subseteq_FL, Sequent.L_eq, Sequent.O_eq, Olf.L_inr, List.append_nil, FLL_nil,
      List.Subset.refl, Olf.L_map_inr, Sequent.R_eq, Olf.R_inr, LoadFormula.unload, List.nil_append,
      FLL_singelton, true_and]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α φ := by
      have := (unfoldDiamondLoaded'_eq α φ)
      grind
    cases oχ <;> grind [FL, pairUnload, unfoldDiamond_in_FL]

lemma unfoldBox_in_FL (α : Program) (ψ : Formula) (X : List Formula) :
    X ∈ unfoldBox α ψ → ∀ φ ∈ X, φ ∈ FL (⌈α⌉ψ) := by
  intro X_in
  simp [unfoldBox] at X_in
  rcases X_in with ⟨ℓ, ℓ_in, def_X⟩
  subst def_X
  intro φ φ_in
  cases α
  · simp_all [Xset, F, P, FL, allTP]
  · simp_all only [allTP, List.mem_map, List.mem_sublists, Xset, F, P, List.mem_append,
    List.mem_union_iff, List.mem_filter, bne_iff_ne, ne_eq, List.mem_ite_nil_right, FL,
    List.cons_append, List.nil_append, List.mem_cons]
    sorry
  · simp_all [Xset, F, P, FL, allTP]
    sorry
  · simp_all [Xset, F, P, FL, allTP]
    sorry
  · simp_all [Xset, F, P, FL, allTP]
    sorry

/-- Helper for `LocalRule.stays_in_FL` -/
theorem OneSidedLocalRule.stays_in_FL
    (rule : OneSidedLocalRule precond ress) :
    ∀ res ∈ ress, res ⊆ FLL precond := by
  intro res res_in
  cases rule <;> simp [FL] at *
  all_goals
    subst_eqs
    try simp
  case nCo φ1 φ2 =>
    -- NOTE: Here it matters that FL is closed under (single) negation.
    cases res_in <;> subst_eqs <;> simp at *
  case box α φ notAt =>
    exact unfoldBox_in_FL _ _ _ res_in -- a bit funny that `exact` works here!
  case dia =>
    have := unfoldDiamond_in_FL _ _ _ res_in
    grind

/-- Helper for `LocalTableau.stays_in_FL` -/
theorem LocalRule.stays_in_FL {X B}
    (rule : LocalRule X B) :
    ∀ Y ∈ B, Y.subseteq_FL X := by
  intro Y Y_in_B
  cases rule
  case oneSidedL precond ress orule B_def =>
    subst B_def
    simp at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp [Sequent.subseteq_FL]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case oneSidedR precond ress orule B_def =>
    subst B_def
    simp at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp [Sequent.subseteq_FL]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case LRnegL =>
    absurd Y_in_B
    tauto
  case LRnegR =>
    absurd Y_in_B
    tauto
  case loadedL ress χ lorule B_def =>
    subst B_def
    simp [List.empty_eq, List.mem_map, Prod.exists] at *
    rcases Y_in_B with ⟨l, o, in_ress, def_Y⟩
    have := LoadRule.stays_in_FL_left lorule (l, o) in_ress
    simp_all
  case loadedR ress χ lorule B_def =>
    subst B_def
    simp only [List.empty_eq, List.mem_map, Prod.exists] at *
    rcases Y_in_B with ⟨l, o, in_ress, def_Y⟩
    have := LoadRule.stays_in_FL_right lorule (l, o) in_ress
    simp_all

/-- LocalTableau helper for `move_inside_FL` -/
theorem LocalTableau.stays_in_FL {X}
    (ltX : LocalTableau X) :
    ∀ Y ∈ endNodesOf ltX, Y.subseteq_FL X := by
  intro Y Y_in_B
  cases ltX
  case byLocalRule B next lra =>
    have _forTermination := localRuleApp.decreases_DM lra
    rcases lra with @⟨L, R, _, ress, O, Lcond, Rcond, Ocond, lr, B_def, ⟨Lconp,Rconp,Oconp⟩⟩
    subst B_def
    have lr_lemma := LocalRule.stays_in_FL lr
    simp [endNodesOf] at Y_in_B
    rcases Y_in_B with ⟨l, ⟨W, W_in, def_l⟩ , Y_in⟩
    subst def_l
    rcases W_in with ⟨re, re_in_ress, def_W⟩
    have IH := LocalTableau.stays_in_FL _ Y Y_in
    clear _forTermination -- to avoid simplifying it
    subst def_W
    specialize lr_lemma re re_in_ress
    rcases re with ⟨Lnew, Rnew, Onew⟩
    simp at *
    clear Y_in next
    simp [Sequent.subseteq_FL, FLL_append_eq] at IH lr_lemma ⊢
    obtain ⟨IHL, IHLO, IHR, IHRO⟩ := IH
    obtain ⟨lemL, lemLO, lemR, lemRO⟩ := lr_lemma
    refine ⟨?_, ?_ , ?_ , ?_⟩ <;> intro x x_in
    · specialize IHL x_in
      simp at *
      rcases IHL with h|h|h
      · left
        have := @FLL_diff_sub L Lcond
        grind
      · have := FLL_sub lemL h
        simp [FLL_append_eq] at this
        rcases this with in_Lcond|inOcondL
        · left
          apply @FLL_sub Lcond L (List.Subperm.subset Lconp) _ in_Lcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · left
          apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · rcases lemLO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Lconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
    · specialize IHLO x_in
      simp at *
      rcases IHLO with h|h|h
      · left
        have := @FLL_diff_sub L Lcond
        grind
      · have := FLL_sub lemL h
        simp [FLL_append_eq] at this
        rcases this with in_Lcond|inOcondR
        · left
          apply @FLL_sub Lcond L (List.Subperm.subset Lconp) _ in_Lcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemLO h
        · left
          apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · rcases lemLO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Lconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
    · specialize IHR x_in
      simp at *
      rcases IHR with h|h|h
      · left
        have := @FLL_diff_sub R Rcond
        grind
      · have := FLL_sub lemR h
        simp [FLL_append_eq] at this
        rcases this with in_Rcond|inOcondR
        · left
          apply @FLL_sub Rcond R (List.Subperm.subset Rconp) _ in_Rcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · left
          apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · rcases lemRO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Rconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
    · specialize IHRO x_in
      simp at *
      rcases IHRO with h|h|h
      · left
        have := @FLL_diff_sub R Rcond
        grind
      · have := FLL_sub lemR h
        simp [FLL_append_eq] at this
        rcases this with in_Rcond|inOcondR
        · left
          apply @FLL_sub Rcond R (List.Subperm.subset Rconp) _ in_Rcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · left
          apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · rcases lemRO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Rconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
  case sim => simp_all [endNodesOf]
termination_by
  X
decreasing_by
  simp_wf
  subst_eqs
  simp at *
  apply _forTermination re re_in_ress

lemma projection_sub_FLL {a L} : projection a L ⊆ FLL L := by
  intro φ φ_in
  rw [proj] at φ_in
  simp only [FLL, List.mem_flatMap]
  use ⌈·a⌉φ, φ_in
  simp [FL]

/-- PdlRule helper for `move_inside_FL` -/
theorem PdlRule.stays_in_FL {X Y} (rule : PdlRule X Y) :
    Y.subseteq_FL X := by
  cases rule
  case loadL L δ α φ R in_L Y_def =>
    subst Y_def
    simp [Sequent.subseteq_FL]
    constructor
    · exact List.Subset.trans List.erase_subset FLL_refl_sub
    · exact FLL_refl_sub in_L
  case loadR L δ α φ R in_L Y_def =>
    subst Y_def
    simp [Sequent.subseteq_FL]
    constructor
    · exact List.Subset.trans List.erase_subset FLL_refl_sub
    · exact FLL_refl_sub in_L
  case freeL L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteq_FL]
    intro x x_in
    simp at x_in
    apply FLL_refl_sub
    simp
    tauto
  case freeR L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteq_FL]
    intro x x_in
    simp at x_in
    apply FLL_refl_sub
    simp
    tauto
  case modL L R a ξ X_def Y_def =>
    subst X_def
    subst Y_def
    cases ξ <;> simp [Sequent.subseteq_FL]
    case normal φ =>
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · have := @projection_sub_FLL a L
        grind [FLL_append_eq]
      · apply projection_sub_FLL
    case loaded χ =>
      refine ⟨?_, ?_, ?_⟩
      · have := @projection_sub_FLL a L
        grind [FLL_append_eq]
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · apply projection_sub_FLL
  case modR L R a ξ X_def Y_def => -- analogous to `modL` case
    subst X_def
    subst Y_def
    cases ξ <;> simp [Sequent.subseteq_FL]
    case normal φ =>
      refine ⟨?_, ?_, ?_⟩
      · apply @projection_sub_FLL a L
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · have := @projection_sub_FLL a R
        grind [FLL_append_eq]
    case loaded χ =>
      refine ⟨?_, ?_, ?_⟩
      · apply projection_sub_FLL
      · have := @projection_sub_FLL a R
        grind [FLL_append_eq]
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
