
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
  contrapose
  simp[not_exists, Consistent, Inconsistent]
  intro h
  specialize h tX
  refine Nonempty.intro ?val
  have : isClosed tX := by
    have h2 : ¬ isOpen tX ↔ ¬ ¬ isClosed tX := Iff.symm (Iff.not (Iff.symm open_iff_notClosed))
    simp_all only [not_not, not_true_eq_false, not_false_eq_true, iff_true]
  exact (isClosed_then_ClosedTab this)


theorem modelExistence {X} : Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (w : WS), (M.val, w) ⊨ X :=
  by
  intro consX
  have := consThenOpenTab consX
  -- now define the model in one go, using pathsOf
  rcases this with ⟨tX, open_tX⟩
  induction tX

  case loc X tX next IH  =>
  {
    use pathsOf tX
    sorry
            }

  case atm X α h₀ simpleX t_proj IH =>
  {
    use pathsOf (LocalTableau.sim simpleX)
    sorry
            }

  case opn X simpleX notClosable  =>
  {
    use pathsOf (LocalTableau.sim simpleX)
    sorry
            }
