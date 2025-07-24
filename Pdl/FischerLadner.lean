import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.FixedPoints

import Pdl.Syntax

/-! # Fischer-Ladner Closure

Main result TODO here: Fischer-Ladner closure of a finite set is finite.
This is exercise 4.8.2 in [BRV] ;-)
-/

/-! ## Single closure step -/

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

/-! ## Fischer-Ladner closure in `Finset` using `partial_fixpoint` -/

def flStep : Finset Formula  → Finset Formula
| X => X ∪ Finset.biUnion X flOf

theorem flStep_isMonotone : Monotone flStep := by -- same proof
  intro X Y h
  simp_all only [Finset.le_eq_subset, flStep]
  intro x hx
  simp at hx
  cases hx <;> aesop

def flHom_Finset : OrderHom (Finset Formula) (Finset Formula) := ⟨flStep, flStep_isMonotone⟩

theorem le_flHom_Finset : X ≤ flHom_Finset X := by
  intro f f_in
  simp [flHom_Finset, flStep]
  left
  assumption

/-- Fischer-Ladner closure, defined using if-then-else and partial_fixpoint.
(We cannot use `OrderHom.nextFixed flHom_Finset X le_flHom` because `Finset` is not a `CompleteLattice`.) -/
def fischerLadner (X : Finset Formula) : Finset Formula :=
  if X = flStep X then X else fischerLadner (flStep X)
partial_fixpoint

/-- Question: Is this definition useful? The following example workds, but we need more probably? -/
lemma example_fl_top : fischerLadner { ⊤ } = { ⊤, ⊥ } := by
  unfold fischerLadner
  simp [flStep, flOf]
  unfold fischerLadner
  decide

/-! ## Alternative Fischer-Ladner Closure in `Set` using `OrderHom.nextFixed` -/

namespace FLSet

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

/-! Question: is the above def computable? It seems we can just not print it?
-- #eval ⊤ ∈ fischerLadner { ⊤ }
-/

/-- TODO ?? A single `flStep` preserves finiteness. -/
lemma flStep_finite {X : Set Formula} : X.Finite → (flStep X).Finite := by
  rintro @⟨n, X_is_Fin_n⟩
  induction n using Nat.strong_induction_on
  next n IH =>
    -- is this even provable?
    sorry

/-- TODO ?? -/
theorem fischerLadner_finite : (fischerLadner X).Finite := by
  unfold fischerLadner
  have := @flStep_finite
  sorry

end FLSet
