import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
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

theorem fischerLadner_finite : (fischerLadner X).Finite := by
  sorry

/-! ## Alternative approach with `Finset` -/

def flStep_Finset : Finset Formula  → Finset Formula
| X => X ∪ Finset.biUnion X flOf

theorem flStep_Finset_isMonotone : Monotone flStep_Finset := by -- same proof
  intro X Y h
  simp_all only [Set.le_eq_subset, flStep_Finset]
  intro x hx
  simp at hx
  cases hx <;> aesop

def flHom_Finset : OrderHom (Finset Formula) (Finset Formula) := ⟨flStep_Finset, flStep_Finset_isMonotone⟩

theorem le_flHom_Finset : X ≤ flHom_Finset X := by
  intro f f_in
  simp [flHom_Finset, flStep_Finset]
  left
  assumption

def fischerLadner_Finset (X : Finset Formula) : Set Formula :=
  -- OrderHom.nextFixed flHom_Finset X le_flHom
  -- NOPE, because `Finset` is not a `CompleteLattice`
  sorry
