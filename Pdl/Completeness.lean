-- COMPLETENESS

import Pdl.Soundness
import Pdl.Modelgraphs

open HasSat

theorem freeSuccExists : sorry := sorry

theorem modelExistence: Consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.toFinset ⊆ W :=
  by
  sorry

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    rcases X with ⟨L, R, O⟩
    have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
    use WS, M.val, w
    simp [modelCanSemImplyTNode, TNode.toFinset] at *
    intro f f_in
    apply truthLemma M w f
    apply h
    aesop
  -- use Theorem 2:
  · exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent ([φ],[],none) ↔ Satisfiable φ :=
  by
  intro φ
  have := completeness ⟨[φ], [], none⟩
  simp [this,tNodeHasSat,modelCanSemImplyTNode]
