import Pdl.Interpolation

/-! # Beth Definability (Sections 2.3 and 7) -/

open vDash HasSat

def Formula.implicitlyDefines (φ : Formula) (p : Nat) : Prop :=
  ∀ p0 p1, repl_in_F p (·p0) φ ⋀ repl_in_F p (·p1) φ ⊨ (·p0) ⟷ (·p1)

def Formula.explicitlyDefines (ψ : Formula) (p : Nat) (φ : Formula) : Prop :=
  ψ.voc ⊆ φ.voc \ {Sum.inl p} ∧ φ ⊨ (·p) ⟷ ψ

theorem beth (φ : Formula) (h : φ.implicitlyDefines p) :
    ∃ (ψ : Formula), ψ.explicitlyDefines p φ := by
  -- Let p0 and p1 be fresh variables not in φ:
  let p0 := freshVarForm φ
  let p1 := freshVarForm (φ ⋀ ·p0)
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
      have : p0 = p1 := by rw[ip_voc0] at ip_voc1; injection ip_voc1
      have p1_fresh : Sum.inl p1 ∉ _ := freshVarForm_is_fresh (φ ⋀ ·p0)
      simp at p1_fresh
      tauto
  · clear ip_voc
    -- show the semantic condition:
    intro W M w w_φ
    simp at w_φ
    specialize ip_one W M w
    specialize ip_two W M w
    simp at *
    -- still need to use fresh variables here? do that in separate lemma?
    sorry
