import Pdl.Syntax

-- NOTE: This file is currently unused!

/-! ## Fischer-Ladner Closure -/

def fischerLadnerStep : Formula → List Formula
| ⊥ => []
| ·_ => []
| φ⋀ψ => [~(φ⋀ψ), φ, ψ]
| ⌈·_⌉φ => [φ]
| ⌈α;'β⌉φ => [ ⌈α⌉⌈β⌉φ ]
| ⌈α⋓β⌉φ => [ ⌈α⌉φ, ⌈β⌉φ ]
| ⌈∗α⌉φ => [ φ, ⌈α⌉⌈∗α⌉φ ]
| ⌈?'τ⌉φ => [ τ, φ ]
| ~~φ => [~φ]
| ~⊥ => []
| ~(·_) => []
| ~(φ⋀ψ) => [φ⋀ψ]
| ~⌈·_⌉φ => [~φ]
| ~⌈α;'β⌉φ => [ ~⌈α⌉⌈β⌉φ ]
| ~⌈α⋓β⌉φ => [ ~⌈α⌉φ, ~⌈β⌉φ ]
| ~⌈∗α⌉φ => [ ~φ, ~⌈α⌉⌈∗α⌉φ ]
| ~⌈?'τ⌉φ => [ ~τ, ~φ ]

/-
def fischerLadner : List Formula → List Formula
| X => let Y := X ∪ (X.map fischerLadnerStep).join
       if Y ⊆ X then Y else fischerLadner Y
decreasing_by sorry -- hmm??
-/

-- Examples:
-- #eval fischerLadner [~~((·1) : Formula)]
-- #eval fischerLadner [ ((⌈(·1) ⋓ (·2)⌉(·3)) ⟷ ((⌈(·1)⌉(·3)) ⋀ (⌈(·2)⌉(·3)))) ]
