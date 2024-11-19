-- Section 6.2: Tableau Game

import Mathlib.SetTheory.Game.State

import Pdl.Tableau

/-! # Two-player games (in general) -/

/-- Two players, `A` and `B`. In the tableau game they will be "Prover" and "Builder". -/
inductive Player : Type
| A : Player
| B : Player
deriving DecidableEq

open Player

@[simp]
theorem Player.ne_A_iff_eq_B : p ≠ A ↔ p = B := by cases p <;> simp

@[simp]
theorem Player.ne_B_iff_eq_A : p ≠ B ↔ p = A := by cases p <;> simp

@[simp]
def other : Player → Player
| A => B
| B => A

/-- Two-player game with
- perfect information
- alternating moves
- finitely many moves at each step
- TODO: a bound on the number of remaining steps / a well-founded order on positions?
-/
class Game where
  Pos : Type -- positions in the game
  turn : Position → Player -- whose turn is it?
  moves : Position → Finset Position -- what are the available moves?
  wins : Position → Option Player
  -- bound : Position → Nat

/-- A strategy in game `g` for player `i` chooses a move whenever it is `i`'s turn. -/
def Strategy (g : Game) (i : Player) : Type := ∀ p : g.Pos, g.turn p = i → g.moves p

/-- Winner of a game, if the strategies `sI` and `sJ` are used. -/
partial -- because of termination!
def winner {g : Game} (sI : Strategy g i) (sJ : Strategy g (other i)) (p : g.Pos) : Player :=
  match g.wins p with
  | some i => i
  | none => if h : g.turn p = i
              then winner sI sJ (sI p h)
              else winner sI sJ (sJ p (by cases i <;> simp_all))

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (p : g.Pos) (sI : Strategy g i) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-- Zermelo's Theorem
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) (p : g.Pos) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := by
  sorry

/-! # The Tableau Game -/

def Rule : Type := sorry

def tableauGame : Game where
  Pos := Sum TNode (TNode × Formula × Rule)
  turn := sorry
  moves := sorry
  wins := sorry

/-

/-! # Abandoned ideas and references -/

structure TabGameState where
  Γ : TNode -- starting sequent
  cur : Sum TNode (TNode × Formula × Rule) -- current state

instance : SetTheory.PGame.State TabGameState where
  turnBound := sorry
  l := sorry
  r := sorry
  left_bound := sorry
  right_bound := sorry


-/
