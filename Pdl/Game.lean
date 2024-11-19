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

theorem Player.eq_A_or_eq_B : p = A ∨ p = B := by cases p <;> simp

/-- Two-player game with
- perfect information
- sequential moves (i.e. only one player moves at each position)
- finitely many moves at each step
- a decreasing bound on the number of remaining steps
-/
class Game where
  Pos : Type -- positions in the game
  turn : Position → Player -- whose turn is it?
  moves : Position → Finset Position -- what are the available moves?
  bound : Position → Nat
  bound_h : ∀ p next : Position, next ∈ moves p → bound next < bound p

/-- A strategy in `g` for `i`, whenever it is `i`'s turn, chooses a move, if there are any. -/
def Strategy (g : Game) (i : Player) : Type := ∀ p : g.Pos, g.turn p = i ∧ g.moves p ≠ ∅ → g.moves p

/-- There is always some strategy. -/
instance Strategy.instNonempty : Nonempty (Strategy g i) := by
  constructor
  rintro p ⟨-, moves_ne_empty⟩
  simp at moves_ne_empty
  rw [@Finset.eq_empty_iff_forall_not_mem] at moves_ne_empty
  apply Classical.choice
  aesop

/-- Winner of a game, if the given strategies are used.
A player loses iff it is their turn and there are no moves.
A player wins if the opponent loses. -/
def winner {g : Game} (sI : Strategy g i) (sJ : Strategy g (other i)) (p : g.Pos) : Player :=
  if h1 : (g.moves p).Nonempty
    then if h2 : g.turn p = i --
      then winner sI sJ (sI p (by aesop))
      else winner sI sJ (sJ p (by aesop))
    else other (g.turn p) -- no more moves, the other player wins
termination_by
  g.bound p
decreasing_by
  all_goals
    apply g.bound_h; simp

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (p : g.Pos) (sI : Strategy g i) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-- Generalized version of `gamedet` for the proof by induction on `g.bound p`. -/
theorem gamedet' (g : Game) (p : g.Pos) n (h : n = g.bound p) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := by
  induction n using Nat.caseStrongRecOn generalizing p
  case zero =>
    have : g.moves p = ∅ := by
      by_contra hyp
      rw [@Finset.eq_empty_iff_forall_not_mem] at hyp
      simp only [not_forall, not_not] at hyp
      rcases hyp with ⟨next, next_in⟩
      have := g.bound_h p next next_in
      omega
    unfold winning
    unfold winner
    simp_all
    apply Player.eq_A_or_eq_B
  case ind n IH =>
    by_cases haveMoves : (g.moves p).Nonempty
    · have := haveMoves.to_subtype
      have := Classical.choice this
      -- TODO:
      -- - "map" IH over `g.moves p`
      -- - if there is any next state where `g.turn p` has a winning strategy, use that,
      ---  otherwise we have a winning strategy for the other player.
      sorry
    · unfold winning
      unfold winner
      simp_all
      apply Player.eq_A_or_eq_B

/-- Zermelo's Theorem
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) (p : g.Pos) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := gamedet' g p _ rfl

/-! # The Tableau Game -/

def Rule : Type := sorry

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
