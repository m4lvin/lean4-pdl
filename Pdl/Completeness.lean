-- COMPLETENESS

import Pdl.Soundness
import Pdl.Modelgraphs

open HasSat

theorem freeSuccExists : sorry := sorry

theorem freeConsSuccExists : sorry := sorry

-- MB page 34
-- TODO: the type below is not correct, this may also be within / across a local tableau!?
def relInTableau {H X} {ctX : ClosedTableau H X} : PathIn ctX → PathIn ctX → Prop := sorry -- TODO

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
