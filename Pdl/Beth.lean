import Pdl.Interpolation

/-! # Beth Definability (Sections 2.3 and 7) -/

open vDash HasSat

def Formula.implicitlyDefines (φ : Formula) (p : Nat) : Prop :=
  ∀ p0 p1, repl_in_F p (·p0) φ ⋀ repl_in_F p (·p1) φ ⊨ (·p0) ⟷ (·p1)

def Formula.explicitlyDefines (ψ : Formula) (p : Nat) (φ : Formula) : Prop :=
  ψ.voc ⊆ φ.voc \ {Sum.inl p} ∧ φ ⊨ (·p) ⟷ ψ

/-- Replacing an atom in a tautology results in a tautology. -/
lemma taut_repl φ p q :
    tautology φ → tautology (repl_in_F p (·q) φ) := by
  intro taut_φ
  intro W M w
  have := repl_in_model_sat_iff p (·q) φ M w
  simp [vDash,SemImplies] at this
  rw [this]
  apply taut_φ

/-- Replacing `p` with a fresh `q` and then replacing `q` by `p` results in the original. -/
@[simp]
lemma repl_repl_cancel_via_non_occ φ p q : Sum.inl q ∉ φ.voc →
    repl_in_F q (·p) (repl_in_F p (·q) φ) = φ := by
  sorry

-- move to `Substitution.lean` after proving and using it
lemma non_occ_taut_then_repl_in_taut (φ ψ : Formula) (p q : ℕ) :
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

theorem beth (φ : Formula) (h : φ.implicitlyDefines p) :
    ∃ (ψ : Formula), ψ.explicitlyDefines p φ := by
  -- Let p0 and p1 be fresh variables not in φ:
  let p0 := freshVarForm φ
  have p0_not_in_φ : Sum.inl p0 ∉ φ.voc := freshVarForm_is_fresh φ
  let p1 := freshVarForm (φ ⋀ ·p0)
  have p1_not_in_φ : Sum.inl p1 ∉ φ.voc := by
    have : Sum.inl p1 ∉ _ := freshVarForm_is_fresh (φ ⋀ ·p0)
    simp_all
  have p0_neq_p1 : p0 ≠ p1 := by
    have p1_fresh : Sum.inl p1 ∉ _ := freshVarForm_is_fresh (φ ⋀ ·p0)
    simp at *
    tauto
  -- Now prepare the tautology that we want to interpolate:
  have : tautology
      ((repl_in_F p (·p0) φ ⋀ ·p0) ↣ (repl_in_F p (·p1) φ ↣ ·p1)) := by
    intro W M w
    simp
    specialize h p0 p1 W M w
    simp at h
    intro w_φp0 w_p0
    specialize h w_φp0
    aesop
  rcases interpolation this with ⟨ψ, ip_voc, ip_one, ip_two⟩
  clear this
  use ψ
  unfold Formula.explicitlyDefines
  constructor
  · clear ip_one ip_two h
    -- show the vocabulary condition:
    intro x x_in
    specialize ip_voc x_in
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    simp only [Formula.voc, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton] at ip_voc
    rcases ip_voc with ⟨ip_voc0, ip_voc1⟩
    rw [repl_in_F_voc_def p (·p0) φ] at ip_voc0
    rw [repl_in_F_voc_def p (·p1) φ] at ip_voc1
    simp only [Formula.voc, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at *
    by_cases Sum.inl p ∈ φ.voc
    all_goals
      simp_all only [ite_true, Finset.mem_singleton, or_self_right]
      by_contra hyp
      simp [hyp] at *
      absurd p0_neq_p1
      rw[ip_voc0] at ip_voc1; injection ip_voc1
  · -- show the semantic condition:
    have ip_one_p : tautology ((φ ⋀ ·p) ↣ ψ) := by
      clear ip_two
      have := non_occ_taut_then_repl_in_taut ((repl_in_F p (·p0) φ⋀·p0)) ψ p0 p
      simp only [repl_in_F, beq_self_eq_true, ↓reduceIte] at this
      rw [repl_repl_cancel_via_non_occ _ p p0 ?_] at this
      apply this
      · intro p0_in_ψ
        specialize ip_voc p0_in_ψ
        simp [p0_neq_p1] at ip_voc
        rw [repl_in_F_voc_def] at ip_voc
        aesop
      · intro p_in_ψ
        specialize ip_voc p_in_ψ
        simp at ip_voc
        by_cases Sum.inl p ∈ φ.voc <;> simp_all [repl_in_F_voc_def]
        aesop
      · assumption
      · assumption
    have ip_two_p : tautology (ψ ↣ (φ ↣ ·p)) := by
      clear ip_one
      -- idea: apply something like `non_occ_taut_then_repl_in_taut` to ip_two
      sorry
    intro W M w w_φ
    simp at w_φ
    specialize ip_one_p W M w
    specialize ip_two_p W M w
    simp_all
