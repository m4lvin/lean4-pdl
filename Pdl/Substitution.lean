
import Pdl.Semantics
import Pdl.Vocab

mutual
  /-- Replace atomic proposition `x` by `ψ` in a formula. -/
  @[simp]
  def repl_in_F (x : Char) (ψ : Formula) : Formula → Formula
    | ⊥ => ⊥
    | ·c => if c == x then ψ else ·c
    | ~φ => ~(repl_in_F x ψ φ)
    | φ1⋀φ2 => (repl_in_F x ψ) φ1 ⋀ (repl_in_F x ψ) φ2
    | ⌈α⌉ φ => ⌈repl_in_P x ψ α⌉ (repl_in_F x ψ φ)
  /-- Replace atomic proposition `x` by `ψ` in a program. -/
  @[simp]
  def repl_in_P (x : Char) (ψ : Formula) : Program → Program
    | ·c => ·c
    | α;'β  => (repl_in_P x ψ α) ;' (repl_in_P x ψ β)
    | α⋓β  => (repl_in_P x ψ α) ⋓ (repl_in_P x ψ β)
    | ∗α  => ∗(repl_in_P x ψ α)
    | ?'φ  => ?' (repl_in_F x ψ φ)
end

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

/-- Overwrite the valuation of `x` with the current value of `ψ` in a model. -/
def repl_in_model (x : Char) (ψ : Formula) : KripkeModel W → KripkeModel W
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