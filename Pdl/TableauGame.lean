import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Defining the Tableau Game (Section 6.2) -/

def Rule : Type := Sum (Σ X B, LocalRuleApp X B) (Σ X Y, PdlRule X Y)
  -- TODO deriving DecidableEq, Repr -- nice to have

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

structure builderPos where
  Γ : Sequent
  φ : Formula
  R : Rule

  φ_nin_Γ : φ ∉ Γ
  R_app : True := trivial
  φ_principle : True := trivial

def tableauPos := Sequent ⊕ builderPos

def tableauGame : Game where
  Pos := tableauPos ×  List tableauPos

  turn
  | ⟨.inl _, _⟩ => Prover
  | ⟨.inr _, _⟩ => Builder

  moves := sorry

  bound := sorry
  bound_h := sorry

-- TODO def strategy trees (or adjust already in `Game.lean`?)

-- TODO def pre-state

-- TODO cp1a

-- TODO cp3

-- TODO cp1

-- TODO cp2

-- TODO cp4

-- TODO cp5

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (Sum.inl X, [])) :
    Nonempty (Tableau [] X) := by
  sorry

/-! ## From winning strategies to model graphs (Section 6.3) -/

/-- If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (Sum.inl X, [])) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), X.toFinset ∈ WS := by
  sorry
