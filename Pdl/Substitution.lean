import Pdl.Discon

/-!
# Substitution and Helper Lemmas

The lemmas here are mostly from Sections 2.1 and 2.2.
-/

/-! ## Single-step replacing -/

mutual
  /-- Replace atomic proposition `x` by `ψ` in a formula. -/
  @[simp]
  def repl_in_F (x : Nat) (ψ : Formula) : Formula → Formula
    | ⊥ => ⊥
    | ·c => if c == x then ψ else ·c
    | ~φ => ~(repl_in_F x ψ φ)
    | φ1⋀φ2 => (repl_in_F x ψ) φ1 ⋀ (repl_in_F x ψ) φ2
    | ⌈α⌉ φ => ⌈repl_in_P x ψ α⌉ (repl_in_F x ψ φ)
  /-- Replace atomic proposition `x` by `ψ` in a program. -/
  @[simp]
  def repl_in_P (x : Nat) (ψ : Formula) : Program → Program
    | ·c => ·c
    | α;'β  => (repl_in_P x ψ α) ;' (repl_in_P x ψ β)
    | α⋓β  => (repl_in_P x ψ α) ⋓ (repl_in_P x ψ β)
    | ∗α  => ∗(repl_in_P x ψ α)
    | ?'φ  => ?' (repl_in_F x ψ φ)
end

theorem repl_in_Con : repl_in_F x ψ (Con l) = Con (l.map (repl_in_F x ψ)) := by
  cases l
  · simp
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp [Con]
      apply repl_in_Con

@[simp]
theorem repl_in_or : repl_in_F x ψ (φ1 ⋁ φ2) = repl_in_F x ψ φ1 ⋁ repl_in_F x ψ φ2 := by
  simp

theorem repl_in_dis : repl_in_F x ψ (dis l) = dis (l.map (repl_in_F x ψ)) := by
  cases l
  · simp
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp [dis]
      apply repl_in_dis

mutual
theorem repl_in_F_non_occ_eq {x φ ρ} :
    (Sum.inl x) ∉ φ.voc → repl_in_F x ρ φ = φ := by
  intro x_notin_phi
  cases φ
  case bottom => simp
  case atom_prop c =>
    simp only [repl_in_F, beq_iff_eq, ite_eq_right_iff]
    intro c_is_x; simp [Formula.voc] at *; subst_eqs; tauto
  case neg φ0 =>
    simp [Formula.voc] at *
    apply repl_in_F_non_occ_eq; tauto
  case and φ1 φ2 =>
    simp [Formula.voc] at *
    constructor <;> (apply repl_in_F_non_occ_eq ; tauto)
  case box α φ0 =>
    simp [Formula.voc] at *
    constructor
    · apply repl_in_P_non_occ_eq; tauto
    · apply repl_in_F_non_occ_eq; tauto

theorem repl_in_P_non_occ_eq {x α ρ} :
    (Sum.inl x) ∉ α.voc → repl_in_P x ρ α = α := by
  intro x_notin_alpha
  cases α
  all_goals simp [Program.voc] at *
  case sequence β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case union β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case star β =>
    apply repl_in_P_non_occ_eq ; tauto
  case test φ =>
    apply repl_in_F_non_occ_eq; tauto
end

theorem repl_in_boxes_non_occ_eq_neg (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → repl_in_F x ψ (⌈⌈δ⌉⌉~·x) = ⌈⌈δ⌉⌉~ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, repl_in_F, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Program.voc, Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Program.voc, Vocab.fromList]

theorem repl_in_boxes_non_occ_eq_pos (δ : List Program) :
    (Sum.inl x) ∉ Vocab.fromList (δ.map Program.voc) → repl_in_F x ψ (⌈⌈δ⌉⌉·x) = ⌈⌈δ⌉⌉ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, List.foldr_cons, repl_in_F, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp_all [Program.voc, Vocab.fromList]
    · apply IH
      clear IH
      simp_all [Program.voc, Vocab.fromList]

theorem repl_in_list_non_occ_eq (F : List Formula) :
     (Sum.inl x) ∉ Vocab.fromList (F.map Formula.voc) → F.map (repl_in_F x ρ) = F := by
  intro nonOcc
  induction F
  · simp
  case cons φ F IH =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply repl_in_F_non_occ_eq
      simp [Program.voc, Vocab.fromList] at *
      exact nonOcc.left
    · apply IH
      clear IH
      simp_all [Program.voc, Vocab.fromList]

set_option maxHeartbeats 2000000 in
mutual
lemma repl_in_F_voc_def p φ ψ :
    (repl_in_F p φ ψ).voc = (ψ.voc \ {Sum.inl p}) ∪ (if Sum.inl p ∈ ψ.voc then φ.voc else {}) := by
  cases ψ <;> simp
  case atom_prop q => by_cases q = p <;> aesop
  case neg => apply repl_in_F_voc_def
  case and ψ1 ψ2 =>
    ext x
    have := repl_in_F_voc_def p φ ψ1
    have := repl_in_F_voc_def p φ ψ2
    aesop
  case box α ψ =>
    ext x
    have := repl_in_F_voc_def p φ ψ
    have := repl_in_P_voc_def p φ α
    aesop

lemma repl_in_P_voc_def p φ α :
    (repl_in_P p φ α).voc = (α.voc \ {Sum.inl p}) ∪ (if Sum.inl p ∈ α.voc then φ.voc else {}) := by
  cases α <;> simp
  case sequence α β =>
    ext x
    have := repl_in_P_voc_def p φ α
    have := repl_in_P_voc_def p φ β
    aesop
  case union α β =>
    ext x
    have := repl_in_P_voc_def p φ α
    have := repl_in_P_voc_def p φ β
    aesop
  case test τ =>
    ext x
    have := repl_in_F_voc_def p φ τ
    simp_all
  case star α =>
    ext x
    have := repl_in_P_voc_def p φ α
    simp_all
end

/-- Overwrite the valuation of `x` with the current value of `ψ` in a model. -/
def repl_in_model (x : Nat) (ψ : Formula) : KripkeModel W → KripkeModel W
| M@⟨V,R⟩ => ⟨fun w c => if c == x then (M,w) ⊨ ψ else V w c,R⟩

mutual
theorem repl_in_model_sat_iff x ψ φ {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ repl_in_F x ψ φ ↔ (repl_in_model x ψ M, w) ⊨ φ := by
  cases φ
  case bottom =>
    simp [evaluatePoint, modelCanSemImplyForm]
  case atom_prop c =>
    simp [evaluatePoint, modelCanSemImplyForm, evaluate, repl_in_model]
    aesop
  case neg φ =>
    have IH := repl_in_model_sat_iff x ψ φ M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    tauto
  case and φ1 φ2 =>
    have IH1 := repl_in_model_sat_iff x ψ φ1 M w
    have IH2 := repl_in_model_sat_iff x ψ φ2 M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    rw [IH1, IH2]
  case box α φ =>
    have IHα := repl_in_model_rel_iff x ψ α M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    constructor
    all_goals
      intro hyp v rel
      have IHφ := repl_in_model_sat_iff x ψ φ M v
      specialize IHα v
      specialize hyp v
      tauto

theorem repl_in_model_rel_iff x ψ α {W} (M : KripkeModel W) (w v : W) :
    relate M (repl_in_P x ψ α) w v ↔ relate (repl_in_model x ψ M) α w v := by
  cases α
  case atom_prog a =>
    simp [repl_in_model]
  case sequence α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [repl_in_P, relate]
  case union α β =>
    have IHα := repl_in_model_rel_iff x ψ α M
    have IHβ := repl_in_model_rel_iff x ψ β M
    simp_all only [repl_in_P, relate]
  case star α =>
    have IHα := repl_in_model_rel_iff x ψ α M
    simp_all only [repl_in_P, relate]
    constructor
    all_goals
      apply Relation.ReflTransGen.mono
      intro w v
      rw [IHα w v]
      tauto
  case test φ =>
    have IHφ := repl_in_model_sat_iff x ψ φ M v
    simp only [repl_in_P, relate, and_congr_right_iff, evaluatePoint, modelCanSemImplyForm] at *
    intro w_is_v
    subst w_is_v
    exact IHφ
end

theorem repl_in_F_equiv x ψ :
    (φ1 ≡ φ2) → (repl_in_F x ψ φ1) ≡ (repl_in_F x ψ φ2) := by
  intro hyp
  intro W M w
  have claim1 := repl_in_model_sat_iff x ψ φ1 M w
  have claim2 := repl_in_model_sat_iff x ψ φ2 M w
  simp only [evaluatePoint, modelCanSemImplyForm] at *
  rw [claim1]
  rw [claim2]
  have := @equiv_iff φ1 φ2 hyp W (repl_in_model x ψ M) w
  simp only [evaluatePoint, modelCanSemImplyForm] at *
  exact this

theorem repl_in_P_equiv x ψ :
    (α1 ≡ᵣ α2) → (repl_in_P x ψ α1) ≡ᵣ (repl_in_P x ψ α2) := by
  intro hyp
  intro W M w v
  have claim1 := repl_in_model_rel_iff x ψ α1 M w v
  have claim2 := repl_in_model_rel_iff x ψ α2 M w v
  rw [claim1]
  rw [claim2]
  apply hyp

theorem repl_in_disMap x ρ (L : List α) (p : α → Prop) (f : α → Formula) [DecidablePred p] :
    repl_in_F x ρ (dis (L.map (fun Fδ => if p Fδ then Formula.bottom else f Fδ))) =
    dis (L.map (fun Fδ => if p Fδ then Formula.bottom else repl_in_F x ρ (f Fδ))) := by
  rw [repl_in_dis, listEq_to_disEq]
  simp only [List.map_map]
  aesop

/-! ## Cancellation of replacements -/

mutual
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same formula. -/
@[simp]
lemma repl_in_F_cancel_via_non_occ φ p q : Sum.inl q ∉ φ.voc →
    repl_in_F q (·p) (repl_in_F p (·q) φ) = φ := by
  intro q_not_in_ψ
  cases φ <;> simp_all
  case atom_prop q =>
    by_cases q = p <;> aesop
  case neg φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    aesop
  case and φ1 φ2 =>
    have := repl_in_F_cancel_via_non_occ φ1 p q
    have := repl_in_F_cancel_via_non_occ φ2 p q
    aesop
  case box α φ =>
    have := repl_in_F_cancel_via_non_occ φ p q
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the same program. -/
lemma repl_in_P_cancel_via_non_occ α p q : Sum.inl q ∉ α.voc →
    repl_in_P q (·p) (repl_in_P p (·q) α) = α := by
  intro q_not_in_α
  cases α <;> simp_all
  case sequence α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case union α1 α2 =>
    have := repl_in_P_cancel_via_non_occ α1 p q
    have := repl_in_P_cancel_via_non_occ α2 p q
    aesop
  case test τ =>
    have := repl_in_F_cancel_via_non_occ τ p q
    aesop
  case star α =>
    have := repl_in_P_cancel_via_non_occ α p q
    aesop
end

/-! ## Replacement of atoms in tautologies -/

/-- Replacing an atom in a tautology results in a tautology. -/
lemma taut_repl φ p q :
    tautology φ → tautology (repl_in_F p (·q) φ) := by
  intro taut_φ
  intro W M w
  have := repl_in_model_sat_iff p (·q) φ M w
  simp [vDash, vDash.SemImplies] at this
  rw [this]
  apply taut_φ

/-- A special case of `taut_repl` for the proof of `beth`. -/
lemma non_occ_taut_then_taut_repl_in_imp (φ ψ : Formula) (p q : ℕ) :
    Sum.inl p ∉ ψ.voc → Sum.inl q ∉ ψ.voc →
    tautology (φ ↣ ψ) → tautology (repl_in_F p (·q) φ ↣ ψ) := by
  intro p_not_in_ψ q_not_in_ψ taut_imp
  intro W M w; simp only [evaluate, not_and, not_not]; intro w_φ
  have := taut_repl _ p q taut_imp W M w
  clear taut_imp
  simp only [repl_in_F, evaluate, not_and, not_not] at this
  specialize this w_φ
  clear w_φ
  rw [repl_in_F_non_occ_eq] at this <;> assumption

/-- Another special case of `taut_repl` for the proof of `beth`. -/
lemma non_occ_taut_then_taut_imp_repl_in (φ ψ : Formula) (p q : ℕ) :
    Sum.inl p ∉ ψ.voc → Sum.inl q ∉ ψ.voc →
    tautology (ψ ↣ φ) → tautology (ψ ↣ repl_in_F p (·q) φ) := by
  intro p_not_in_ψ q_not_in_ψ taut_imp
  intro W M w; simp only [evaluate, not_and, not_not]; intro w_ψ
  have := taut_repl _ p q taut_imp W M w
  clear taut_imp
  simp [repl_in_F, evaluate, not_and, not_not] at this
  apply this
  rw [repl_in_F_non_occ_eq] <;> assumption

/-! ## Simultaneous Substitutions -/

abbrev Substitution := Nat → Formula

mutual
  /-- Apply substitution `σ` to formula `φ`. -/
  @[simp]
  def subst_in_F (σ : Substitution) : (φ : Formula) → Formula
    | ⊥ => ⊥
    | ·c => σ c
    | ~φ => ~(subst_in_F σ φ)
    | φ1⋀φ2 => (subst_in_F σ) φ1 ⋀ (subst_in_F σ) φ2
    | ⌈α⌉ φ => ⌈subst_in_P σ α⌉ (subst_in_F σ φ)
  /-- Apply substitution `σ` to program `α`. -/
  @[simp]
  def subst_in_P (σ : Substitution) : (α : Program) → Program
    | ·c => ·c
    | α;'β  => (subst_in_P σ α) ;' (subst_in_P σ β)
    | α⋓β  => (subst_in_P σ α) ⋓ (subst_in_P σ β)
    | ∗α  => ∗(subst_in_P σ α)
    | ?'φ  => ?' (subst_in_F σ φ)
end

/-- Overwrite the valuation in `M` with the substitution `σ`. -/
def subst_in_model (σ : Substitution) : (M : KripkeModel W) → KripkeModel W
| M@⟨_, R⟩ => ⟨fun w c => (M,w) ⊨ σ c, R⟩

mutual
theorem substitutionLemma σ φ {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ subst_in_F σ φ ↔ (subst_in_model σ M, w) ⊨ φ := by
  cases φ
  case bottom =>
    simp [evaluatePoint, modelCanSemImplyForm]
  case atom_prop c =>
    simp [evaluatePoint, modelCanSemImplyForm, evaluate, subst_in_model]
  case neg φ =>
    have IH := substitutionLemma σ φ M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    tauto
  case and φ1 φ2 =>
    have IH1 := substitutionLemma σ φ1 M w
    have IH2 := substitutionLemma σ φ2 M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    rw [IH1, IH2]
  case box α φ =>
    have IHα := substitutionLemmaRel σ α M w
    simp [evaluatePoint, modelCanSemImplyForm] at *
    constructor
    all_goals
      intro hyp v rel
      have IHφ := substitutionLemma σ φ M v
      specialize IHα v
      specialize hyp v
      tauto

theorem substitutionLemmaRel (σ : Substitution) α {W} (M : KripkeModel W) (w v : W) :
    relate M (subst_in_P σ α) w v ↔ relate (subst_in_model σ M) α w v := by
  cases α
  case atom_prog a =>
    simp [subst_in_model]
  case sequence α β =>
    have IHα := substitutionLemmaRel σ α M
    have IHβ := substitutionLemmaRel σ β M
    simp_all only [subst_in_P, relate]
  case union α β =>
    have IHα := substitutionLemmaRel σ α M
    have IHβ := substitutionLemmaRel σ β M
    simp_all only [subst_in_P, relate]
  case star α =>
    have IHα := substitutionLemmaRel σ α M
    simp_all only [subst_in_P, relate]
    constructor
    all_goals
      apply Relation.ReflTransGen.mono
      intro w v
      rw [IHα w v]
      tauto
  case test φ =>
    have IHφ := substitutionLemma σ φ M v
    simp only [subst_in_P, relate, and_congr_right_iff, evaluatePoint, modelCanSemImplyForm] at *
    intro w_is_v
    subst w_is_v
    exact IHφ
end

/-! ## Semantic Equivalents -/

/-
-- This is *not* true because `frm` might be sneaky.
theorem wrong_equiv_repl φ1 φ2 (h : φ1 ≡ φ2) (frm : Formula → Formula) :
    frm φ1 ≡ frm φ2 := by
  sorry
-/

/-- A true instance of `wrong_equiv_repl`, here we replaced `frm` with a special case. -/
theorem equiv_con {φ1 φ2} (h : φ1 ≡ φ2) ψ :
    φ1 ⋀ ψ ≡ φ2 ⋀ ψ := by
  intro W M w
  specialize h W M w
  simp_all
