
import Pdl.Vocab

mutual
  /-- Get a fresh atom `x` not occuring in `ψ`. -/
  def freshVarForm : Formula → Nat
    | ⊥ => 0
    | ·c => c + 1
    | ~φ => freshVarForm φ
    | φ1⋀φ2 => max (freshVarForm φ1) (freshVarForm φ2)
    | ⌈α⌉ φ => max (freshVarProg α) (freshVarForm φ)
  /-- Get a fresh atom `x` not occuring in `α`. -/
  def freshVarProg : Program → Nat
    | ·c => c + 1
    | α;'β  => max (freshVarProg α) (freshVarProg β)
    | α⋓β  =>  max (freshVarProg α) (freshVarProg β)
    | ∗α  => freshVarProg α
    | ?'φ  => freshVarForm φ
end

open HasVocabulary

mutual
theorem freshVarForm_is_larger (φ) : ∀ n ∈ voc φ, n < freshVarForm φ := by
  cases φ
  all_goals simp [freshVarForm, voc, vocabOfFormula, not_or, instMembershipNatVocab]
  case neg φ =>
    apply freshVarForm_is_larger
  case and φ1 φ2 =>
    have IH1 := freshVarForm_is_larger φ1
    have IH2 := freshVarForm_is_larger φ2
    simp_all [instMembershipNatVocab]
    aesop
  case box α φ =>
    have IHφ := freshVarForm_is_larger φ
    have IHα := freshVarProg_is_larger α
    simp_all [instMembershipNatVocab]
    aesop

theorem freshVarProg_is_larger (α) : ∀ n ∈ voc α, n < freshVarProg α := by
  cases α
  all_goals simp [freshVarProg, voc, vocabOfProgram, instMembershipNatVocab]
  case union α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp_all [instMembershipNatVocab]
    aesop
  case sequence α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp_all [instMembershipNatVocab]
    aesop
  case star α =>
    have IHα := freshVarProg_is_larger α
    simp_all [instMembershipNatVocab]
    aesop
  case test φ =>
    have IHφ := freshVarForm_is_larger φ
    simp_all [instMembershipNatVocab]
    aesop
end

theorem freshVarForm_is_fresh (φ) : freshVarForm φ ∉ voc φ := by
  have := freshVarForm_is_larger φ
  simp [freshVarForm, voc, vocabOfFormula] at *
  by_contra hyp
  specialize this (freshVarForm φ)
  have := Nat.lt_irrefl (freshVarForm φ)
  tauto

theorem freshVarProg_is_fresh (α) : freshVarProg α ∉ HasVocabulary.voc α := by
  have := freshVarProg_is_larger α
  simp [freshVarProg, voc, vocabOfFormula] at *
  by_contra hyp
  specialize this (freshVarProg α)
  have := Nat.lt_irrefl (freshVarProg α)
  tauto
