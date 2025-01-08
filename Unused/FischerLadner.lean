import Mathlib.Data.Finset.Basic
import Mathlib.Order.FixedPoints

import Pdl.Syntax

/-!
# Fischer-Ladner Closure

NOTE: This file is currently unused!
-/

/-- Single step to close a single formula under:
-- - single-negations,
-- - subformulas, and
-- - unraveling PDL programs. -/
def flOf : Formula → Finset Formula
| ⊥ => {}
| ·_ => {}
| φ⋀ψ => {~(φ⋀ψ), φ, ψ}
| ⌈·a⌉φ => { ~⌈·a⌉φ, φ }
| ⌈α;'β⌉φ => { ~⌈α;'β⌉φ, ⌈α⌉⌈β⌉φ }
| ⌈α⋓β⌉φ => { ~⌈α⋓β⌉φ, ⌈α⌉φ, ⌈β⌉φ }
| ⌈∗α⌉φ => { ~⌈∗α⌉φ, φ, ⌈α⌉⌈∗α⌉φ }
| ⌈?'τ⌉φ => { ~⌈?'τ⌉φ, τ, φ }
| ~~φ => { ~φ }
| ~⊥ => { ⊥ }
| ~(·p) => { (·p : Formula) }
| ~(φ⋀ψ) => { φ⋀ψ }
| ~⌈·a⌉φ => { ⌈·a⌉φ, ~φ }
| ~⌈α;'β⌉φ => { ⌈α;'β⌉φ, ~⌈α⌉⌈β⌉φ }
| ~⌈α⋓β⌉φ => { ⌈α⋓β⌉φ, ~⌈α⌉φ, ~⌈β⌉φ }
| ~⌈∗α⌉φ => { ⌈∗α⌉φ, ~φ, ~⌈α⌉⌈∗α⌉φ }
| ~⌈?'τ⌉φ => { ⌈?'τ⌉φ, ~τ, ~φ }

/-- Single step for the closure of a set of formulas. -/
def flStep : Set Formula  → Set Formula
| X => X ∪ (⋃ φ ∈ X, flOf φ)

theorem flStep_isMonotone : Monotone flStep := by -- Thanks Andrés!
  intro X Y h
  simp_all only [Set.le_eq_subset, flStep]
  intro x hx
  cases hx <;> aesop

def flHom : OrderHom (Set Formula) (Set Formula) := ⟨flStep, flStep_isMonotone⟩

theorem le_flHom : X ≤ flHom X := by
  intro f f_in
  simp [flHom, flStep]
  left
  assumption

/-- The Fischer-Ladner closure defined as a fixed point of `flStep`.
Note that we use `nextFixed` and not `lfp`. -/
def fischerLadner (X : Set Formula) : Set Formula := OrderHom.nextFixed flHom X le_flHom

-- theorem fischerLadner_finite : (fischerLadner X).Finite := by
--   sorry
