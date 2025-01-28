import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Defining the Tableau Game (Section 6.2) -/

def RuleApp (X : Sequent) : Type :=
  Sum (Σ B, LocalRuleApp X B) (Σ Y, PdlRule X Y)

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

/-- A *position* in the tableau game is either a sequent
or a pair of a sequent and a rule application on it. -/
def TGPos := Sum Sequent (Σ X: Sequent, RuleApp X)

-- QUESTION:
-- Suppose Prover chooses a LocalRuleApp and thereby starts a `.loc`
-- with a `LocalTableau`. How to ensure then that the next choice may
-- only be a `PdlRule` iff we have reached an end node of the local
-- tableau already?
-- Just replace `LocalRuleApp` in `RuleApp` with `LocalTableau`?
-- No, we probably also need the steps inside the `LocalTableau`
-- to eventually build the countermodel!?

/-- A history of TG positions, needed to check for repeats. -/
def TGHist := List TGPos

def tableauGame : Game where
  Pos := TGPos × List TGPos
  turn tgp := match tgp with
    | (Sum.inl _, _) => Prover
    | (Sum.inr _, _) => Builder
  moves := sorry
  bound := sorry -- PROBLEM: how to define the bound?
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
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning (Sum.inl X, []) s) :
    Nonempty (Tableau [] X) := by
  sorry

/-! ## From winning strategies to model graphs (Section 6.3) -/

/-- If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning (Sum.inl X, []) s) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), X.toFinset ∈ WS := by
  sorry
