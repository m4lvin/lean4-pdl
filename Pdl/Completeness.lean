-- COMPLETENESS

import Pdl.Soundness
import Pdl.TableauGame
import Pdl.Modelgraphs

open HasSat

-- MB page 34
-- TODO: the type below is not correct, this may also be within / across a local tableau!?
def relInTableau {H X} {ctX : Tableau H X} : PathIn ctX → PathIn ctX → Prop := sorry -- TODO

theorem modelExistence: consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.toFinset ⊆ W :=
  by
  sorry

theorem completeness : ∀ X, consistent X → satisfiable X :=
  by
  intro X
  intro X_is_consistent
  rcases X with ⟨L, R, O⟩
  have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
  use WS, M.val, w
  simp [modelCanSemImplyTNode, TNode.toFinset] at *
  intro f f_in
  apply truthLemma M w f
  apply h
  aesop

theorem consIffSat : ∀ X, consistent X ↔ satisfiable X :=
  fun X => ⟨completeness X, correctness X⟩

theorem singletonConsIffSat : ∀ φ, consistent ([φ],[],none) ↔ satisfiable φ :=
  by
  intro φ
  have := consIffSat ⟨[φ], [], none⟩
  simp [this,tNodeHasSat,modelCanSemImplyTNode]
