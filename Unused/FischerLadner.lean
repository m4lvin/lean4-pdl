import Mathlib.Order.FixedPoints

import Pdl.Syntax

/-!
# Fischer-Ladner Closure

NOTE: This file is currently unused!
-/

def fischerLadnerOf : Formula → Set Formula
| ⊥ => {}
| ·a => {}
| φ⋀ψ => {~(φ⋀ψ), φ, ψ}
| ⌈·_⌉φ => {φ}
| ⌈α;'β⌉φ => { ⌈α⌉⌈β⌉φ }
| ⌈α⋓β⌉φ => { ⌈α⌉φ, ⌈β⌉φ }
| ⌈∗α⌉φ => { φ, ⌈α⌉⌈∗α⌉φ }
| ⌈?'τ⌉φ => { τ, φ }
| ~~φ => {~φ}
| ~⊥ => {}
| ~(·_) => {}
| ~(φ⋀ψ) => {φ⋀ψ}
| ~⌈·_⌉φ => {~φ}
| ~⌈α;'β⌉φ => { ~⌈α⌉⌈β⌉φ }
| ~⌈α⋓β⌉φ => { ~⌈α⌉φ, ~⌈β⌉φ }
| ~⌈∗α⌉φ => { ~φ, ~⌈α⌉⌈∗α⌉φ }
| ~⌈?'τ⌉φ => { ~τ, ~φ }

def fischerLadnerStep : Set Formula  → Set Formula
| X => X ∪ (⋃ φ ∈ X, fischerLadnerOf φ)

theorem flS_isMonotone : Monotone fischerLadnerStep := by
  sorry

def flHom : OrderHom (Set Formula) (Set Formula) := ⟨fischerLadnerStep, flS_isMonotone⟩

-- I think `lfp` is not what I want, because it does not ask me for a strarting value.
-- Probably the lfp of flHom in general is just {} ;-)
def fischerLadner_NOPE : Set Formula := OrderHom.lfp flHom

theorem X_le_flX : X ≤ flHom X := by
  intro f f_in
  simp [flHom, fischerLadnerStep]
  left
  assumption

-- Apparently I want `nextFixed` instead of `lfp`?
def fischerLadner (X : Set Formula) : Set Formula := OrderHom.nextFixed flHom X X_le_flX
