
import Bml.Syntax
import Bml.Semantics
import Bml.Modelgraphs
import Bml.Tableau

open LocalTableau

-- Maximal paths in a local tableau, from root to end node, as sets of sets.
-- pathsOf (X with children B) := { X ∪ rest | c <- B, rest <- pathsOf c }
def pathsOf {X} : LocalTableau X → Finset (Finset Formula)
  | @byLocalRule _ B lr next => B.attach.biUnion
      (λ ⟨Y,h⟩ => have : lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h
                  (pathsOf (next Y h)).image (λ fs => fs ∪ X))
  | sim _ => { X }


theorem consThenOpenTab : Consistent X → ∃ (t : Tableau X), isOpen t :=
  by
  have ⟨tX⟩ := existsTableauFor X
  -- should be easy now
  sorry


theorem modelExistence {X} : Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (w : WS), (M.val, w) ⊨ X :=
  by
  intro consX
  have := consThenOpenTab consX
  -- now define the model in one go, using pathsOf
  sorry
