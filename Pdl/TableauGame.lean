import Pdl.Game
import Pdl.Tableau

/-! # The Tableau Game (Section 6.2) -/

def Rule : Type := sorry

-- Renaming the players for the tableau game:
def Prover : Player := Player.A
def Builder : Player := Player.B

def tableauGame : Game where
  Pos := Sum TNode (TNode × Formula × Rule) -- probably not enough, also need history to check for repeats?
  turn := sorry
  moves := sorry
  bound := sorry
  bound_h := sorry

/- ToDo list:

- define "match"

- translate winning strategy of Prover to Tableau

- translate winning strategy of Builder to Kripke model

-/
