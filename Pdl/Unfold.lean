-- UNFOLD

import Pdl.Semantics
import Pdl.Vocab
import Pdl.Discon

-- TODO: move to Syntax.lean
mutual
  @[simp]
  def repl_in_F (x : Char) (ψ : Formula) : Formula → Formula
    | ⊥ => ⊥
    | ·c => if c == x then ψ else ·c
    | ~φ => ~(repl_in_F x ψ φ)
    | φ1⋀φ2 => (repl_in_F x ψ) φ1 ⋀ (repl_in_F x ψ) φ2
    | ⌈α⌉ φ => ⌈repl_in_P x ψ α⌉ (repl_in_F x ψ φ)
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

-- TODO: move to Semantics?

mutual
theorem repl_in_F_equiv x ψ :
    (φ1 ≡ φ2) → (repl_in_F x ψ φ1) ≡ (repl_in_F x ψ φ2) := sorry -- TODO easy?

theorem repl_in_P_equiv x ψ :
    (α1 ≡ᵣ α2) → (repl_in_P x ψ α1) ≡ᵣ (repl_in_P x ψ α2) := sorry -- TODO easy?
end


-- ### Test Profiles

def allFunToBool : (L : List α) → List (Subtype (fun β => β ∈ L) → Bool)
| [] => [fun x => by exfalso; cases x; tauto]
| (x::xs) => (allFunToBool xs).map sorry -- extend the function somehow?

def TestProfile (α : Program) : Type := Subtype (fun β => β ∈ testsOfProgram α) → Bool

/-- List of all test profiles for a given program. -/
def TP (α : Program) : List (TestProfile α) := allFunToBool (testsOfProgram α)

/-- σ^ℓ -/
def signature (ℓ : TestProfile α) : Formula :=
  Con $ (testsOfProgram α).attach.map (fun ⟨τ,h⟩ => if ℓ ⟨τ,h⟩ then τ else ~ τ)

-- Now come the three facts about test profiles and signatures.

theorem top_equiv_disj_TP : ⊤ ≡ dis ((TP α).map signature) := by
  intro W M w
  sorry

theorem signature_conbot_iff_neq : ℓ ⋀ ℓ' ≡ ⊥  ↔  ℓ ≠ ℓ' := by
  sorry

theorem equiv_iff_TPequiv : φ ≡ ψ  ↔  ∀ ℓ ∈ TP α, φ ⋀ signature ℓ ≡ ψ ⋀ signature ℓ := by
  sorry

-- Coercion of TestProfiles to subprograms
-- These are needed to re-use `l` in the recursive calls of `F`.
instance : CoeOut (TestProfile (α ⋓ β)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inl f_in⟩⟩
instance : CoeOut (TestProfile (α ⋓ β)) (TestProfile β) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inr f_in⟩⟩

instance : CoeOut (TestProfile (α ;' β)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inl f_in⟩⟩
instance : CoeOut (TestProfile (α ;' β)) (TestProfile β) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram, List.mem_union_iff]; exact Or.inr f_in⟩⟩

instance : CoeOut (TestProfile (∗α)) (TestProfile α) :=
  ⟨fun l ⟨f,f_in⟩ => l ⟨f, by simp only [testsOfProgram]; exact f_in⟩⟩

-- ### F, P, X and the Φ_□ set

-- NOTE: In P and Xset
-- We use lists here because we eventually want to make formulas.

def F : (Σ α, TestProfile α) → List Formula
| ⟨·_, _⟩ => ∅
| ⟨?' τ, l⟩ => if l ⟨τ, by simp [TestProfile,testsOfProgram] at *⟩ then ∅ else {~τ}
| ⟨α ⋓ β, l⟩ => F ⟨α, l⟩ ∪ F ⟨β, l⟩
| ⟨α;'β, l⟩ => F ⟨α, l⟩ ∪ F ⟨β, l⟩
| ⟨∗α, l⟩ => F ⟨α, l⟩

def ε : List Program := [] -- ugly way to define the empty program?

def P : (Σ α, TestProfile α) → List (List Program)
| ⟨·a, _⟩ => [ [(·a : Program)] ]
| ⟨?' τ, l⟩ => if l ⟨τ, by simp [TestProfile,testsOfProgram] at *⟩ then ∅ else [ [] ]
| ⟨α ⋓ β, l⟩ => P ⟨α, l⟩ ∪ P ⟨β, l⟩ -- ∪ or ++ here ??
| ⟨α;'β, l⟩ => (P ⟨α,l⟩ \ [ε]).map (fun as => as ++ [β])
             ∪ (if ε ∈ P ⟨α,l⟩ then (P ⟨β,l⟩ \ [ε]) else [])
| ⟨∗α, l⟩ => [ ε ] ∪ (P (⟨α, l⟩) \ [ε]).map (fun as => as ++ [∗α])

def Xset (α) (l : TestProfile α) (ψ : Formula) : List Formula :=
  F ⟨α, l⟩ ++ (P ⟨α, l⟩).map (fun as => Formula.boxes as ψ)

/-- Φ_□(αs,ψ) -/
-- *Not* the same as `Formula.boxes`.
def PhiSet α ψ := { Xset α l ψ | l ∈ TP α }

-- TODO Lemma 21 with parts 1) and 2)

-- TODO Lemma 22 with parts 1) and 2) and 3)

theorem guardToStar (x : Char)
    (x_notin_beta : x ∉ HasVocabulary.voc β)
    (beta_equiv : (⌈β⌉·x) ≡ (((·x) ⋀ χ0) ⋁ χ1))
    (rho_imp_repl : ρ ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1))
    (rho_imp_psi : ρ ⊨ ψ)
  : ρ ⊨ ⌈(∗β)⌉ψ := by
  -- The key observation in this proof is the following:
  have fortysix :
       ∀ W M (w v : W), (M,w) ⊨ ρ → relate M β w v → (M,v) ⊨ ρ := by
    intro W M w v w_rho w_β_v
    have : (M,w) ⊨ ⌈β⌉ρ := by
      have by_ass : (M,w) ⊨ (repl_in_F x ρ) (χ0 ⋁ χ1) := by apply rho_imp_repl; simp; exact w_rho; simp
      have obvious : (M,w) ⊨ (repl_in_F x ρ) (·x) := by simp; exact w_rho
      have : (M,w) ⊨ (repl_in_F x ρ) (((·x) ⋀ χ0) ⋁ χ1) := by
        simp [evaluate,relate,modelCanSemImplyForm] at *
        tauto
      -- Now we want to "rewrite" with beta_equiv.
      have := repl_in_F_equiv x ρ beta_equiv
      simp only [repl_in_F, beq_self_eq_true, reduceIte, Formula.or] at this
      have nox : repl_in_P x ρ β = β := repl_in_P_non_occ_eq x_notin_beta
      rw [nox] at this
      rw [equiv_iff _ _ this]
      simp_all
    -- It is then immediate...
    simp [evaluate,relate,modelCanSemImplyForm] at this
    exact this v w_β_v -- This finishes the proof of (46).
  -- To see how the Lemma follows from this...
  intro W M w
  simp only [List.mem_singleton, forall_eq, evaluate, relate]
  intro w_rho v w_bS_v
  induction w_bS_v using Relation.ReflTransGen.head_induction_on
  · apply rho_imp_psi; simp; assumption; simp
  case head u1 u2 u1_b_u2 _ IH =>
    apply IH
    exact fortysix W M u1 u2 w_rho u1_b_u2

/-- Induction claim for `localBoxTruth`. -/
theorem localBoxTruth' γ ψ ℓ : (⌈γ⌉ψ) ⋀ signature ℓ ≡ Con (Xset γ ℓ ψ) ⋀ signature ℓ := by
  cases γ
  case atom_prog =>
    sorry
  case test =>
    sorry
  case union =>
    sorry
  case sequence =>
    sorry
  case star =>

    -- use guardToStar
    sorry

theorem localBoxTruth : (⌈γ⌉ψ) ≡ dis ( (TP γ).map (fun ℓ => Con (Xset γ ℓ ψ)) ) := by
  have := localBoxTruth' γ ψ
  -- clearly this suffices to prove the theorem ;-)
  sorry
