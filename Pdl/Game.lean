import Mathlib.SetTheory.Game.State

/-! # A General Theory for Determined Two-player Games

Nothing here is specific about PDL, but we give a general
definition of games and show that one of the two players
must have a winning strategy: `gamedet` at the end.

-/

/-- Two players, `A` and `B`. -/
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
theorem Player.not_eq_iff_eq_other : (¬ p = A) ↔ p = B := by cases p <;> simp

@[simp]
theorem Player.not_eq_B_iff_eq_A : (¬ p = B) ↔ p = A := by cases p <;> simp

theorem Player.eq_A_or_eq_B : p = A ∨ p = B := by cases p <;> simp

def other : Player → Player
| A => B
| B => A

@[simp]
theorem other_A_eq_B : other A = B := by simp [other]

@[simp]
theorem other_B_eq_A : other B = A := by simp [other]

@[simp]
theorem Player.not_eq_i_eq_other : (¬ p = i) ↔ p = other i := by cases p <;> cases i <;> simp

@[simp]
theorem Player.not_eq_other_eq_i : (¬ p = other i) ↔ p = i := by cases p <;> cases i <;> simp

@[simp]
theorem Player.not_i_eq_other : ¬ i = other i := by cases i <;> simp

@[simp]
theorem Player.not_other_i_eq_i : ¬ other i = i := by cases i <;> simp

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
  turn : Pos → Player -- whose turn is it?
  moves : Pos → Finset Pos -- what are the available moves?
  bound : Pos → Nat
  bound_h : ∀ (p next : Pos), next ∈ moves p → bound next < bound p

/-- Allow notation `p.moves` for `g.moves p`. -/
abbrev Game.Pos.moves {g : Game} : g.Pos → Finset g.Pos := Game.moves

/-- If the bound bound is zero then there are no more moves. -/
lemma Game.no_moves_of_bound_zero {g : Game} {p : g.Pos}
    (bound_zero : g.bound p = 0) : g.moves p = ∅ := by
  suffices ¬ (g.moves p).Nonempty by simp_all
  by_contra hyp
  rcases Finset.Nonempty.exists_mem hyp with ⟨q, q_in⟩
  have := g.bound_h _ q q_in
  linarith

instance {g : Game} : LT g.Pos := ⟨fun p q => g.bound p < g.bound q⟩

/-- A strategy in `g` for `i`, whenever it is `i`'s turn, chooses a move, if there are any. -/
def Strategy (g : Game) (i : Player) : Type := ∀ p : g.Pos, g.turn p = i → p.moves.Nonempty → p.moves

noncomputable def choose_move {g : Game} {p : g.Pos} : p.moves.Nonempty → p.moves :=
  Classical.choice ∘ Set.Nonempty.to_subtype

/-- There is always some strategy. -/
instance Strategy.instNonempty : Nonempty (Strategy g i) := ⟨fun _ _ => choose_move⟩

/-- Winner of a game, if the given strategies are used.
A player loses iff it is their turn and there are no moves.
A player wins if the opponent loses. -/
def winner {g : Game} (sI : Strategy g i) (sJ : Strategy g (other i)) (p : g.Pos) : Player :=
  if h1 : (g.moves p).Nonempty
    then if h2 : g.turn p = i --
      then winner sI sJ (sI p h2 h1)
      else winner sI sJ (sJ p (by cases i <;> simp_all) h1)
    else other (g.turn p) -- no more moves, the other player wins
termination_by
  g.bound p
decreasing_by
  all_goals
    apply g.bound_h; simp

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (p : g.Pos) (sI : Strategy g i) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

/-- The cone of all positions reachable from `p` assuming that `i` plays `sI`. -/
inductive inMyCone {g : Game} (sI : Strategy g i) (p : g.Pos) : g.Pos → Prop
| nil : inMyCone sI p p
| myStep : inMyCone sI p q → (has_moves : q.moves.Nonempty) → (h : g.turn q = i) → inMyCone sI p (sI q h has_moves)
| oStep : inMyCone sI p q → g.turn q = other i → r ∈ g.moves q → inMyCone sI p r

/-- Strategy for specific height -/
def NStrategy (g : Game) (n : ℕ) (i : Player) : Type :=
  ∀ p, g.bound p = n → g.turn p = i → p.moves.Nonempty → p.moves

noncomputable def good {g : Game} (i : Player) (p : g.Pos) : Prop :=
    (g.turn p = i       ∧ ∃ (q : g.Pos) (_ : q ∈ p.moves), good i q)
  ∨ (g.turn p = other i ∧ ∀ (q : g.Pos) (_ : q ∈ p.moves), good i q)
termination_by g.bound p
decreasing_by all_goals apply g.bound_h _ _; assumption

theorem good_or_other {g : Game} (p : g.Pos) : good (g.turn p) p ∨ good (other (g.turn p)) p :=
  Nat.strongRecMeasure (g.bound) (fun p ind =>
    (exists_or_forall_not (fun q => ∃ (h : q ∈ p.moves), good _ q)).elim
    (fun E => .inl <| by unfold good; apply Or.inl; exact ⟨rfl, E⟩)
    (fun A => .inr <| by
      unfold good; apply Or.inr; apply And.intro
      . exact other_other.symm
      . intro q h
        have det := ind q (g.bound_h _ _ h)
        have := A q
        by_cases g.turn p = g.turn q <;> simp_all
    )
  ) p

theorem good_A_or_B {g : Game} (p : g.Pos) : good A p ∨ good B p := by
  have det := good_or_other p
  cases i : g.turn p <;> cases det <;> simp_all

noncomputable def good_strat (i : Player): Strategy g i := fun p turn nempty =>
  have := Classical.dec
  if W : good i p
    then by
      unfold good at W
      have E := And.right <| W.resolve_right (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)
      exact ⟨E.choose, E.choose_spec.choose⟩
    else choose_move nempty

theorem sub_lt_sub_left' : ∀ {a b c : Nat}, b < c → c <= a → a - c < a - b := fun h₁ h₂ =>
  Nat.sub_lt_sub_left (trans h₁ h₂) h₁

theorem bound_le_in_cone {s : Strategy g i} : inMyCone s p q → g.bound q <= g.bound p := fun h =>
  by induction h with
  | nil => rfl
  | myStep _ _ _ ih => exact le_of_lt (lt_of_lt_of_le (g.bound_h _ _ <| Subtype.mem _) ih)
  | oStep _ _ h ih => exact le_of_lt (lt_of_lt_of_le (g.bound_h _ _ h) ih)

theorem good_cone {g : Game} {p r : g.Pos} (W : good i p) (h : inMyCone (good_strat i) p r) : good i r := by
  induction h with
  | nil => exact W
  | oStep _ turn h ih =>
    unfold good at ih
    exact (ih.resolve_left (not_and_of_not_left _ <| not_eq_i_eq_other.mpr turn)).right _ h
  | @myStep q a nempty turn ih =>
    unfold good_strat
    if good i q
      then
        let E := good_strat.proof_1 i q turn ih
        simp only [ih, ↓reduceDIte]
        exact (good_strat.proof_1 i q turn (of_eq_true (eq_true ih))).choose_spec.choose_spec
      else contradiction

theorem good_is_surviving {g : Game} {p : g.Pos} : good i p → g.turn p = i → p.moves.Nonempty := by
  intro W turn
  unfold good at W
  apply (Or.resolve_right . (not_and_of_not_left _ <| not_eq_other_eq_i.mpr turn)) at W
  match W with | ⟨_, ⟨q, ⟨h, _⟩⟩⟩ => exact ⟨q,h⟩

theorem cone_trans {p q r : g.Pos} {s : Strategy g i} : inMyCone s p q → inMyCone s q r → inMyCone s p r :=
  fun a b => by induction b with
  | nil => assumption
  | myStep _ _ _ ih => exact .myStep ih ..
  | oStep a turn h ih => exact .oStep ih turn h

theorem surviving_is_winning {sI : Strategy g i} (surv : ∀ q, inMyCone sI p q → g.turn q = i → q.moves.Nonempty)
    : winning p sI :=
  fun sJ => by
    unfold winner
    split
    case isFalse empty =>
      by_contra turn
      apply (not_eq_other_eq_i.mp ∘ Ne.symm) at turn
      exact empty (surv _ .nil turn.symm)
    split
    . exact surviving_is_winning (surv . ∘ cone_trans (.myStep .nil _ _)) _
    next _ turn =>
      exact surviving_is_winning (surv . ∘ cone_trans (.oStep .nil (not_eq_i_eq_other.mp turn) <| Subtype.mem _)) _
termination_by g.bound p
decreasing_by all_goals apply g.bound_h; exact Subtype.mem _

theorem good_strat_winning (W : good i p) : winning p (good_strat i) :=
  surviving_is_winning fun _ => good_is_surviving ∘ (good_cone W)

/-- Zermelo's Theorem: In every `Game` posiiton one of the two players has a winning strategy.
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) [DecidableEq g.Pos] (p : g.Pos) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := Or.imp
    (⟨good_strat A, good_strat_winning .⟩)
    (⟨good_strat B, good_strat_winning .⟩)
    <| good_A_or_B p
