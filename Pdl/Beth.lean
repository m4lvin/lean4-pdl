import Pdl.Interpolation

/-! # Beth Definability (Sections 2.3 and 7) -/

open vDash HasSat

-- Question: is this a good way to represent formulas with one free variable?
def OpenFormula : Type := Nat → Formula

-- Still missing in the defs below: additionally fixed vocabulary `ps`?

def implicitlyDefines (φ_ : OpenFormula) : Prop :=
  ∀ q q', φ_ q ⋀ φ_ q' ⊨ (·q) ⟷ (·q')

def explicitlyDefines (ψ : Formula) (φ_ : OpenFormula) : Prop :=
  ∀ q, φ_ q ⊨ (·q) ⟷ ψ

theorem beth φ_ :
    implicitlyDefines φ_ → ∃ ψ, explicitlyDefines ψ φ_ := by
  intro impDef

  -- have : deduction [] φ ψ -- ???
  sorry
