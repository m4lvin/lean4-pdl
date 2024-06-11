
import Pdl.Semantics
import Pdl.Vocab
import Pdl.Discon

-- ## Single-step replacing
-- For simultaneous substition, see below!

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

theorem repl_in_dis : repl_in_F x ψ (dis l) = dis (l.map (repl_in_F x ψ)) := by
  cases l
  · simp
  case cons φ1 l =>
    cases l
    · simp
    case cons φ2 l =>
      simp [dis]
      apply repl_in_dis

open HasVocabulary

mutual
theorem repl_in_F_non_occ_eq {x φ ρ} :
    x ∉ voc φ → repl_in_F x ρ φ = φ := by
  intro x_notin_phi
  cases φ
  case bottom => simp
  case atom_prop c =>
    simp only [repl_in_F, beq_iff_eq, ite_eq_right_iff]
    intro c_is_x; simp [voc,vocabOfFormula] at *; tauto
  case neg φ0 =>
    simp [voc,vocabOfFormula] at *
    apply repl_in_F_non_occ_eq; tauto
  case and φ1 φ2 =>
    simp [voc,vocabOfFormula] at *
    constructor <;> (apply repl_in_F_non_occ_eq ; tauto)
  case box α φ0 =>
    simp [voc,vocabOfFormula] at *
    constructor
    · apply repl_in_P_non_occ_eq; tauto
    · apply repl_in_F_non_occ_eq; tauto
theorem repl_in_P_non_occ_eq {x α ρ} :
    x ∉ voc α → repl_in_P x ρ α = α := by
  intro x_notin_alpha
  cases α
  all_goals simp [voc,vocabOfProgram] at *
  case sequence β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case union β γ =>
    constructor <;> (apply repl_in_P_non_occ_eq; tauto)
  case star β =>
    apply repl_in_P_non_occ_eq ; tauto
  case test φ =>
    apply repl_in_F_non_occ_eq; tauto
end

theorem repl_in_boxes_non_occ_eq (δ : List Program) :
    x ∉ voc δ → repl_in_F x ψ (⌈⌈δ⌉⌉~·x) = ⌈⌈δ⌉⌉~ψ := by
  intro nonOcc
  induction δ
  · simp
  case cons α δ IH =>
    simp only [Formula.boxes, repl_in_F, Formula.box.injEq]
    constructor
    · apply repl_in_P_non_occ_eq
      simp [voc,vocabOfProgram,vocabOfListProgram] at *
      intro _
      simp_all
    · apply IH
      clear IH
      simp [voc,vocabOfProgram,vocabOfListProgram] at *
      intro d d_in
      simp_all

theorem repl_in_list_non_occ_eq (F : List Formula) :
     x ∉ voc F → F.map (repl_in_F x ρ) = F := by
  intro nonOcc
  induction F
  · simp
  case cons φ F IH =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · apply repl_in_F_non_occ_eq
      simp [voc,vocabOfProgram,vocabOfListFormula] at *
      exact nonOcc.left
    · apply IH
      clear IH
      simp [voc,vocabOfProgram,vocabOfListFormula] at *
      intro d d_in
      simp_all

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

-- ## Substitutions
-- Simultaneous

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
