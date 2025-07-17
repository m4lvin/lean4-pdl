import Mathlib.SetTheory.Game.State
import Mathlib.Tactic.Linarith

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
  /-- Positions in the game. -/
  Pos : Type
  /-- Whose turn is it? -/
  turn : Pos → Player
  /-- What are the available moves? -/
  moves : Pos → Finset Pos
  /-- A wellfounded relation on positions. -/
  wf : WellFoundedRelation Pos
  /-- Every move goes a step down in the relation. -/
  move_rel : ∀ (p next : Pos), next ∈ moves p → wf.rel next p

/-- This seems a bit hacky, but makes `termination_by (p : g.Pos)` work in `winner` and elsewhere.
If the instance causes trouble, change to `termination_by g.wf.2.wrap p` via `WellFounded.wrap`. -/
instance {g : Game} : WellFoundedRelation Game.Pos := g.wf

/-- Allow notation `p.moves` for `g.moves p`. -/
abbrev Game.Pos.moves {g : Game} : g.Pos → Finset g.Pos := Game.moves

/-- If the bound bound is zero then there are no more moves. -/
lemma Game.no_moves_of_no_rel {g : Game} {p : g.Pos}
    (no_rel : ∀ q, ¬ g.wf.rel q p) : g.moves p = ∅ := by
  suffices ¬ (g.moves p).Nonempty by simp_all
  by_contra hyp
  rcases Finset.Nonempty.exists_mem hyp with ⟨q, q_in⟩
  have := g.move_rel _ q q_in
  simp_all

instance {g : Game} : LT g.Pos := ⟨fun p q => g.wf.rel q p⟩

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
  p
decreasing_by
  all_goals
    apply g.move_rel; simp

/-- A strategy is winning at `p` if it wins against all strategies of the other player. -/
def winning {g : Game} {i : Player} (sI : Strategy g i) (p : g.Pos) : Prop :=
  ∀ sJ : Strategy g (other i), winner sI sJ p = i

lemma winning_has_moves {g : Game} {i : Player} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    (g.moves p).Nonempty := by
  specialize sI_wins_p (Classical.choice Strategy.instNonempty)
  unfold winner at sI_wins_p
  by_contra hyp
  simp_all

lemma winning_of_winning_move {g : Game} {i : Player} {sI : Strategy g i} {p : g.Pos}
    (h : g.turn p = i) (sI_wins_p : winning sI p) :
    winning sI (sI p h (winning_has_moves h sI_wins_p)).val := by
  intro sJ
  have := winning_has_moves h sI_wins_p
  specialize sI_wins_p sJ
  unfold winner at sI_wins_p
  simp_all

/-- The cone of all positions reachable from `p` assuming that `i` plays `sI`. -/
inductive inMyCone {g : Game} (sI : Strategy g i) (p : g.Pos) : g.Pos → Prop
| nil : inMyCone sI p p
| myStep : inMyCone sI p q → (has_moves : q.moves.Nonempty) → (h : g.turn q = i) → inMyCone sI p (sI q h has_moves)
| oStep : inMyCone sI p q → g.turn q = other i → r ∈ g.moves q → inMyCone sI p r

def good {g : Game} (i : Player) (p : g.Pos) : Prop :=
    (g.turn p = i       ∧ ∃ (q : g.Pos) (_ : q ∈ p.moves), good i q)
  ∨ (g.turn p = other i ∧ ∀ (q : g.Pos) (_ : q ∈ p.moves), good i q)
termination_by p
decreasing_by all_goals apply g.move_rel _ _; assumption

theorem good_or_other {g : Game} (p : g.Pos) : good (g.turn p) p ∨ good (other (g.turn p)) p := by
  apply WellFounded.induction g.wf.2 p
  intro r IH
  by_cases ∃ q ∈ r.moves, good (g.turn r) q
  case pos E =>
    apply Or.inl
    unfold good
    apply Or.inl
    simp only [exists_prop, true_and]
    exact E
  case neg A =>
    apply Or.inr
    unfold good
    refine Or.inr (And.intro other_other.symm ?_)
    intro q h
    specialize IH q (g.move_rel _ _ h)
    by_cases g.turn r = g.turn q <;> simp_all

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

-- To find the magic `_proof_XXX` below, uncomment this:
-- set_option pp.proofs true
-- #print good_strat
-- (With Lean 4.19.0 it changed from `proof_1` to `_proof_20`.)
-- With Lean 4.20.1 it became `_proof_21`.
-- With Lean 4.22.0-rc2 it became `_proof_1`.

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
        simp only [ih, ↓reduceDIte]
        exact (good_strat._proof_1 i q turn (of_eq_true (eq_true ih))).choose_spec.choose_spec
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
    : winning sI p :=
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
termination_by p
decreasing_by all_goals apply g.move_rel; exact Subtype.mem _

theorem good_strat_winning (W : good i p) : winning (good_strat i) p :=
  surviving_is_winning fun _ => good_is_surviving ∘ (good_cone W)

/-- Zermelo's Theorem: In every `Game` posiiton one of the two players has a winning strategy.
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) (p : g.Pos) :
    (∃ s : Strategy g A, winning s p) ∨ (∃ s : Strategy g B, winning s p) := Or.imp
    (⟨good_strat A, good_strat_winning .⟩)
    (⟨good_strat B, good_strat_winning .⟩)
    <| good_A_or_B p
