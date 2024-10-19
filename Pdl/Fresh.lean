
import Pdl.Vocab

mutual
  /-- Get a fresh atomic proposition `x` not occuring in `ψ`. -/
  def freshVarForm : Formula → Nat
    | ⊥ => 0
    | ·c => c + 1
    | ~φ => freshVarForm φ
    | φ1⋀φ2 => max (freshVarForm φ1) (freshVarForm φ2)
    | ⌈α⌉ φ => max (freshVarProg α) (freshVarForm φ)
  /-- Get a fresh atomic proposition `x` not occuring in `α`. -/
  def freshVarProg : Program → Nat
    | ·_ => 0 -- don't care!
    | α;'β  => max (freshVarProg α) (freshVarProg β)
    | α⋓β  =>  max (freshVarProg α) (freshVarProg β)
    | ∗α  => freshVarProg α
    | ?'φ  => freshVarForm φ
end

mutual
theorem freshVarForm_is_larger (φ) : ∀ n ∈ φ.voc.atomProps, n < freshVarForm φ := by
  cases φ
  all_goals simp [freshVarForm, Formula.voc, not_or, Vocab.atomProps]
  case neg φ =>
    have IH := freshVarForm_is_larger φ
    simp [Vocab.atomProps] at *
    assumption
  case and φ1 φ2 =>
    have IH1 := freshVarForm_is_larger φ1
    have IH2 := freshVarForm_is_larger φ2
    simp [Vocab.atomProps] at *
    aesop
  case box α φ =>
    have IHφ := freshVarForm_is_larger φ
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop

theorem freshVarProg_is_larger (α) : ∀ n ∈ α.voc.atomProps, n < freshVarProg α := by
  cases α
  all_goals simp [freshVarProg, Program.voc, Vocab.atomProps]
  case union α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case sequence α β =>
    have IHα := freshVarProg_is_larger α
    have IHβ := freshVarProg_is_larger β
    simp [Vocab.atomProps] at *
    aesop
  case star α =>
    have IHα := freshVarProg_is_larger α
    simp [Vocab.atomProps] at *
    aesop
  case test φ =>
    have IHφ := freshVarForm_is_larger φ
    simp [Vocab.atomProps] at *
    aesop
end

theorem freshVarForm_is_fresh (φ) : Sum.inl (freshVarForm φ) ∉ φ.voc := by
  have := freshVarForm_is_larger φ
  simp [freshVarForm, Formula.voc, Vocab.atomProps] at *
  by_contra hyp
  specialize this (freshVarForm φ)
  have := Nat.lt_irrefl (freshVarForm φ)
  tauto

theorem freshVarProg_is_fresh (α) : Sum.inl (freshVarProg α) ∉ α.voc := by
  have := freshVarProg_is_larger α
  simp [freshVarProg, Formula.voc, Vocab.atomProps] at *
  by_contra hyp
  specialize this (freshVarProg α)
  have := Nat.lt_irrefl (freshVarProg α)
  tauto
