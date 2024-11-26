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

theorem Player.eq_A_or_eq_B : p = A ∨ p = B := by cases p <;> simp

def other : Player → Player
| A => B
| B => A

@[simp]
theorem other_A_eq_B : other A = B := by simp [other]

@[simp]
theorem other_B_eq_A : other B = A := by simp [other]

@[simp]
theorem other_other : other (other i) = i := by
  cases i <;> simp [other]

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
def Strategy (g : Game) (i : Player) : Type := ∀ p : g.Pos, g.turn p = i → g.moves p ≠ ∅ → g.moves p

/-- There is always some strategy. -/
instance Strategy.instNonempty : Nonempty (Strategy g i) := by
  constructor
  intro p _ moves_ne_empty
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
      then winner sI sJ (sI p (by cases i <;> simp_all) (Finset.nonempty_iff_ne_empty.mp h1))
      else winner sI sJ (sJ p (by cases i <;> simp_all) (Finset.nonempty_iff_ne_empty.mp h1))
    else other (g.turn p) -- no more moves, the other player wins
termination_by
  g.bound p
decreasing_by
  all_goals
    apply g.bound_h; simp

/-- If there are no moves left, then the winner is the other player. -/
-- unused?
lemma winner_of_no_moves (g : Game) (p : g.Pos) (no_moves : g.moves p = ∅) :
    ∀ i (sI : Strategy g i) sJ, winner sI sJ p = other (g.turn p) := by
  unfold winner
  simp_all

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (p : g.Pos) (sI : Strategy g i) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-- If there are no moves left, then any strategy of the other player is winning. -/
-- unused?
lemma winning_of_no_moves (g : Game) (p : g.Pos) (no_moves : g.moves p = ∅) :
    ∀ sI : Strategy g (other (g.turn p)), winning p sI := by
  intro sI
  unfold winning
  unfold winner
  simp_all

-- unused?
lemma exists_other_winning_strategy_of_no_moves (g : Game) (p : g.Pos) (no_moves : g.moves p = ∅) :
    ∃ s : Strategy g (other (g.turn p)), winning p s := by
  have := winner_of_no_moves g p no_moves
  refine ⟨Classical.choice Strategy.instNonempty, ?_⟩
  unfold winning
  apply this

/-- A _play_ is a list of positions connected by moves. Aka "match". -/
def Game.Play (g : Game) : Type :=
  { L // List.Chain' (fun p q => q ∈ g.moves p) (L : List g.Pos) }

lemma Game.Play.decreasing {g : Game} (L : List g.Pos)
    (h_L : List.Chain' (fun p q => q ∈ g.moves p) (L : List g.Pos)) :
    List.Chain' (fun p q => g.bound q < g.bound p) L := by
  induction L
  · simp_all
  case cons p rest IH =>
    apply List.Chain'.cons'
    · apply IH
      have := List.Chain'.tail h_L
      simp_all
    · cases rest
      · simp
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq']
        apply g.bound_h
        simp_all

-- Mathlib this?
theorem List.Chain'.not_map_lt_of_mem {α: Type} (f : α → Nat)
    {x : α} {rest : List α} (h : x ∈ rest)
    : ¬ (List.Chain' (fun p q => f q < f p) (x :: rest)) := by
  induction rest <;> simp_all only [mem_cons, chain'_cons, not_and, not_mem_nil]
  intro fy_lt_fx
  case cons y rest IH =>
    rcases h with h|h
    · subst_eqs; simp_all
    · specialize IH h
      rw [List.chain'_cons']
      cases rest <;> simp_all
      case cons z rest =>
        cases h
        · subst_eqs
          intro fy_lt_fx
          linarith
        · intro fz_lt_fy
          exact IH (Nat.lt_trans fz_lt_fy fy_lt_fx)

/-- A play cannot have repeating states. -/
lemma Game.Play.nodup {g : Game} (pl : g.Play) : pl.val.Nodup := by
  by_contra hasDup
  push_neg at hasDup
  rcases pl with ⟨pl, pl_h⟩
  induction pl
  case nil =>
    absurd hasDup
    simp
  case cons p rest IH =>
    simp at IH
    specialize IH (by apply List.Chain'.tail pl_h)
    simp only [List.nodup_cons, not_and] at hasDup
    suffices p ∉ rest by simp_all
    clear hasDup IH
    intro p_in_rest
    exact List.Chain'.not_map_lt_of_mem g.bound p_in_rest (Game.Play.decreasing _ pl_h)

/-- Two strategies agree on all later states. -/
def same_from_here {g : Game} (sI sI' : Strategy g i) (p : g.Pos) :=
  ∀ (q : g.Pos), g.bound q ≤ g.bound p → sI q = sI' q

/-- applying any strategy leads to a position with a lower bound. -/
lemma bound_strat_lt {g : Game} {sI : Strategy g i} p ha hb :
    g.bound (sI p ha hb).val < g.bound p := g.bound_h _ _ (sI p ha hb).prop

lemma winner_eq_of_strategy_eq_from_here {g : Game} {sI sI' : Strategy g i}
    (p : g.Pos) (h : same_from_here sI sI' p) (sJ : Strategy g (other i))
    : winner sI sJ p = winner sI' sJ p := by
  induction' def_n : g.bound p using Nat.strongRecOn generalizing p
  case ind n IH =>
    subst def_n
    unfold winner
    by_cases h1 : (Game.moves p).Nonempty <;> simp_all
    unfold same_from_here at h
    by_cases whose_turn : g.turn p = i <;> simp_all
    all_goals
    · apply IH (g.bound _) _ _ _ rfl
      · apply bound_strat_lt
      · intro q q_le
        apply h
        apply Nat.le_trans q_le
        apply le_of_lt
        apply bound_strat_lt

lemma winning_strategy_of_next_when_my_turn (g : Game) [DecidableEq g.Pos]
    (p : g.Pos) (whose_turn : g.turn p = i)
    (nextPos : g.moves p) (s : Strategy g i) (s_wins_next : winning nextPos s)
    : ∃ s' : Strategy g i, winning p s' := by
  -- Now we overwrite what s chooses at the current place.
  let s' : Strategy g i :=
    (fun pos turn_i has_moves => if h : pos = p then h ▸ nextPos else s pos turn_i has_moves)
  use s'
  unfold winning winner
  intro sJ
  specialize s_wins_next (whose_turn ▸ sJ)
  have : (Game.moves p).Nonempty := ⟨nextPos, nextPos.prop⟩
  simp_all only [ne_eq, dite_eq_ite, ite_true, dite_true]
  have : winner s sJ nextPos = winner s' sJ nextPos := by
    apply winner_eq_of_strategy_eq_from_here
    intro q q_lt_p
    unfold s'
    have : q ≠ p := by
      by_contra q_eq_p
      subst_eqs
      have : g.bound nextPos.val < g.bound p := by apply g.bound_h _ _ nextPos.2
      linarith
    simp_all
  unfold_let s'
  subst whose_turn
  simp_all

/-- Generalized version of `gamedet` for the proof by induction on `g.bound p`. -/
theorem gamedet' (g : Game) [DecidableEq g.Pos] (p : g.Pos) n (h : n = g.bound p) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := by
  induction n using Nat.caseStrongRecOn generalizing p
  case zero =>
    -- When the bound is zero then there are no moves available.
    have : g.moves p = ∅ := by
      by_contra hyp
      rw [@Finset.eq_empty_iff_forall_not_mem] at hyp
      simp only [not_forall, not_not] at hyp
      rcases hyp with ⟨next, next_in⟩
      have := g.bound_h p next next_in
      omega
    -- Because there are no moves we have a winner by definition.
    unfold winning
    unfold winner
    simp_all
    apply Player.eq_A_or_eq_B
  case ind n IH =>
    -- Proof idea:
    -- - "map" IH over `g.moves p`
    -- - if there is any next state where `g.turn p` has a winning strategy, use that,
    ---  otherwise we have a winning strategy for the other player.
    --
    -- If the bound still allows moves, distinguish cases if there are any.
    by_cases haveMoves : (g.moves p).Nonempty
    · -- By IH, at all next states one of the players must have a winning strategy:
      have claim : ∀ pNext ∈ g.moves p, (∃ (s : Strategy g A), winning pNext s)
                                      ∨ ∃ (s : Strategy g B), winning pNext s := by
        intro pNext pNext_in_moves_p
        let m := g.bound pNext
        have : m ≤ n := by apply Nat.le_of_lt_succ; rw [h]; exact g.bound_h _ _ pNext_in_moves_p
        exact IH _ this pNext rfl
      -- Is there a next state where the current player has a winning strategy?
      by_cases ∃ pNext ∈ g.moves p, ∃ (s : Strategy g (g.turn p)), winning pNext s
      case pos hyp =>
        rcases hyp with ⟨pNext, pNext_in, s, s_winning⟩
        -- Whose turn is it? That player has a winning strategy!
        cases whose_turn : g.turn p
        case A =>
          left
          apply winning_strategy_of_next_when_my_turn g p whose_turn ⟨pNext, _⟩ (whose_turn ▸ s)
          convert s_winning
          · simp_all
          · exact eqRec_heq whose_turn s
          · exact pNext_in
        case B =>
          right
          -- Analogous to `case A`.
          apply winning_strategy_of_next_when_my_turn g p whose_turn ⟨pNext, _⟩ (whose_turn ▸ s)
          convert s_winning
          · simp_all
          · exact eqRec_heq whose_turn s
          · exact pNext_in
      case neg hyp =>
        push_neg at hyp
        -- Whose turn is it? The other player should have a winning strategy.
        cases whose_turn : g.turn p
        case A =>
          right
          rcases Classical.choice haveMoves.to_subtype with ⟨pNext, pNext_in⟩
          -- Situation:
          -- it is the turn of A
          specialize hyp pNext pNext_in -- all A strategies here are NOT winning
          specialize claim pNext pNext_in -- in the next position someone has a winning strategy
          -- TODO:
          -- claim that B has a winning strategy
          -- show that the move by A does not matter
          -- also use `winning_strategy_of_next_when_my_turn` here?
          sorry
        case B =>
          left
          -- should be analogous to `case A`.
          sorry
    · -- No moves left, we have a winner by definition.
      unfold winning
      unfold winner
      simp_all
      apply Player.eq_A_or_eq_B

/-- Zermelo's Theorem
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) [DecidableEq g.Pos] (p : g.Pos) :
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