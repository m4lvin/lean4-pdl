import Mathlib.SetTheory.Game.State

/-! # A General Theory for Determined Two-playerGames -/

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
  bound_h : ∀ p next : Pos, next ∈ moves p → bound next < bound p

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

/-- Induction on the bound of game positions. -/
theorem Game.Pos.inductionOnLT {g : Game} (p : g.Pos) {motive : g.Pos → Prop}
    (ind : (p : Pos) → (∀ q, q < p → motive q) → motive p) : motive p := by
  induction' gb_def : g.bound p using Nat.strongRecOn generalizing p
  case ind k IH =>
    apply ind
    intro q q_lt_p
    apply IH (g.bound q) (by aesop) _ rfl

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

lemma winner_of_winning {g : Game} {i : Player} (p : g.Pos) (sI : Strategy g i) (h : winning p sI) :
    ∀ sJ, winner sI sJ p = i := by
  intro sJ
  exact h sJ

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
    (h_L : List.Chain' (fun p q => q ∈ p.moves) (L : List g.Pos)) :
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

/-- First helper for `gamedet'`. -/
lemma winning_strategy_of_one_next_when_my_turn (g : Game) [DecidableEq g.Pos]
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

/-- Variant of `winning_strategy_of_one_next_when_my_turn` not about winning
but winner against specific other strategy. -/
lemma winner_of_next_when_my_turn (g : Game) [DecidableEq g.Pos]
    (p : g.Pos)
    (whose_turn : g.turn p = i)
    (nextPos : g.moves p)
    (sI : Strategy g i)
    (sJ : Strategy g (other i))
    (s_wins_next : winner sI sJ nextPos = i)
    : ∃ s' : Strategy g i, winner s' sJ p = i := by
  -- Now we overwrite what s chooses at the current place.
  let s' : Strategy g i :=
    (fun pos turn_i has_moves => if h : pos = p then h ▸ nextPos else sI pos turn_i has_moves)
  use s'
  have : (Game.moves p).Nonempty := ⟨nextPos, nextPos.prop⟩
  unfold winner
  simp_all only [dite_true]
  have : winner sI sJ nextPos = winner s' sJ nextPos := by
    apply winner_eq_of_strategy_eq_from_here
    intro q q_lt_p
    unfold s'
    have : q ≠ p := by
      by_contra q_eq_p
      subst_eqs
      have : g.bound nextPos.val < g.bound p := by apply g.bound_h _ _ nextPos.2
      linarith
    simp_all
  unfold s'
  simp_all

/-- DUAL COPY -/
lemma winner_eq_of_strategy_eq_from_here_otherDual {g : Game} {sJ sJ' : Strategy g (other i)}
    (p : g.Pos) (h : same_from_here sJ sJ' p) (sI : Strategy g i)
    : winner sI sJ p = winner sI sJ' p := by
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

/-- DUAL COPY -/
lemma winner_of_next_when_my_turn_otherDual (g : Game) [DecidableEq g.Pos]
    (p : g.Pos)
    (whose_turn : g.turn p = other i)
    (nextPos : g.moves p)
    (sI : Strategy g i)
    (sJ : Strategy g (other i))
    (s_wins_next : winner sI sJ nextPos = other i)
    : ∃ s' : Strategy g (other i), winner sI s' p = other i := by
  -- Now we overwrite what sJ chooses at the current place.
  let s' : Strategy g (other i) :=
    (fun pos turn_i has_moves => if h : pos = p then h ▸ nextPos else sJ pos turn_i has_moves)
  use s'
  have : (Game.moves p).Nonempty := ⟨nextPos, nextPos.prop⟩
  unfold winner
  simp_all only [dite_true]
  have : winner sI sJ nextPos = winner sI s' nextPos := by
    apply winner_eq_of_strategy_eq_from_here_otherDual
    intro q q_lt_p
    unfold s'
    have : q ≠ p := by
      by_contra q_eq_p
      subst_eqs
      have : g.bound nextPos.val < g.bound p := by apply g.bound_h _ _ nextPos.2
      linarith
    simp_all
  unfold s'
  simp_all

/-- The cone of all positions reachable from `p`. -/
inductive inCone {g : Game} (p : g.Pos) : g.Pos → Prop
| nil : inCone p p
| step : inCone p q → r ∈ g.moves q → inCone p r

-- FIXME everywhere: change `≠ ∅` to `.Nonempty`

/-- The cone of all positions reachable from `p` assuming that `i` plays `sI`. -/
inductive inMyCone {g : Game} (sI : Strategy g i) (p : g.Pos) : g.Pos → Prop
| nil : inMyCone sI p p
| myStep : inMyCone sI p q → (has_moves : g.moves q ≠ ∅) → (h : g.turn q = i) → inMyCone sI p (sI q h has_moves)
| oStep : inMyCone sI p q → g.turn q = other i → r ∈ g.moves q → inMyCone sI p r

-- USED !
lemma winning_here_then_winning_inMyCone {g : Game} [DecidableEq g.Pos] (sI : Strategy g i) (p : g.Pos)
    (win_at_p : winning p sI) (q : g.Pos) (q_inMyCone : inMyCone sI p q)
    : winning q sI := by
  induction q_inMyCone
  · assumption
  case myStep r _ has_moves turn_i IH =>
    intro sJ
    specialize IH sJ
    unfold winner at IH
    have := Finset.nonempty_iff_ne_empty.mpr has_moves
    simp_all
  case oStep q r _ turn_other_i r_in IH =>
    -- Suppose sI is not winning at r.
    by_contra hyp
    unfold winning at hyp
    push_neg at hyp
    rcases hyp with ⟨sJ, win_r_j⟩
    -- Hence there is a strategy sJ winning against sI at r.
    simp at win_r_j
    -- Then there must be a strategy sJ' beating sI at q.
    have := @winner_of_next_when_my_turn_otherDual
      i g _ q turn_other_i ⟨r, r_in⟩ sI sJ win_r_j
    rcases this with ⟨sJ', win_q_j⟩
    -- But this means sI cannot be winning at q
    absurd IH sJ'
    simp
    exact win_q_j

/-- In its cone from here, `sI` does what one of `sIset` would do. -/
def subset_from_here {g : Game} [DecidableEq g.Pos]
    (sI : Strategy g i) (sIset : Finset (Strategy g i)) (p : g.Pos) :=
  ∀ (q : g.Pos), inMyCone sI p q
    → (i_turn : Game.turn q = i)
    → (has_moves : Game.moves q ≠ ∅)
    → sI q i_turn has_moves ∈ sIset.image (fun sI' => sI' q i_turn has_moves)

-- Need something like a multi-strategy version of `winning_here_then_winning_inMyCone`?
-- ?? If all those strategies are winning here, then they are winning in each others cone ??

/-- If a strategy always (in its own cone) imitates winning strategies, then it is winning. -/
lemma winning_if_imitating_some_winning {g : Game} (p : g.Pos) (s : Strategy g i)
    (imitates_winning : ∀ x, inMyCone s p x → g.turn x = i → ∃ s', s x = s' x ∧ winning x s')
    : winning p s := by
  suffices claim : ∀ x, inMyCone s p x → winning x s by exact claim _ inMyCone.nil
  intro x x_in
  induction' bound_def : g.bound x using Nat.strongRecOn generalizing x
  case ind k IH =>
    unfold winning
    intro sJ
    unfold winner
    -- Four cases: there are (no) moves × it is (not) my turn
    by_cases (Game.moves x).Nonempty <;> by_cases g.turn x = i <;> simp_all
    case pos has_moves turn_i =>
      let nexts := s x turn_i (by aesop)
      have := IH _ (by rw [← bound_def]; apply g.bound_h; simp) nexts ?_ rfl
      · specialize this sJ
        exact this
      · unfold nexts
        apply inMyCone.myStep x_in
    case neg _ turn_other =>
      simp_all
      let nexts := sJ x turn_other (by aesop)
      have := IH _ (by rw [← bound_def]; apply g.bound_h; simp) nexts ?_ rfl
      · specialize this sJ
        exact this
      · unfold nexts
        apply inMyCone.oStep x_in turn_other
        simp
    case pos no_moves turn_i =>
      rcases imitates_winning x x_in turn_i with ⟨s', _, s'_winning⟩
      specialize s'_winning sJ
      simp_all [winner]

/-
-- UNUSED
/-- Version of `winner_eq_of_strategy_eq_from_here` generalized to a set of strategies. -/
lemma winner_mem_of_subset_from_here {g : Game} [DecidableEq g.Pos]
    (p : g.Pos)
    {i} {sI : Strategy g i} {sIset : Finset (Strategy g i)}
    (h : subset_from_here sI sIset p)
    (sJ : Strategy g (other i))
    : winner sI sJ p ∈ sIset.image (fun sI' => winner sI' sJ p) := by
  induction' def_n : g.bound p using Nat.strongRecOn generalizing p
  case ind n IH =>
    subst def_n
    unfold winner
    by_cases h1 : (Game.moves p).Nonempty <;> simp_all
    unfold subset_from_here at h
    by_cases whose_turn : g.turn p = i <;> simp_all
    all_goals
      sorry
-/

noncomputable def Exists.subtype {p : α → Prop} (h : ∃ x, p x) : { x // p x } := by
  use (Classical.choose h)
  apply Exists.choose_spec

noncomputable def Exists.subtype_pair {motive : α → Prop} {p : (x : α) → motive x → Prop}
    (h : ∃ x, ∃ mx : motive x, p x mx) : { xmx : { x // motive x } // p xmx.1 xmx.2 } := by
  let x := Exists.choose h
  let px := Exists.choose_spec h
  let mx := Exists.choose px
  let xmx : { x // motive x } := ⟨x, mx⟩
  have := Exists.choose_spec px
  use xmx

/-- Second helper for `gamedet'`. -/
theorem winning_strategy_of_all_next_when_others_turn (g : Game) [DecidableEq g.Pos]
    (p : g.Pos) (whose_turn : g.turn p = other i)
    (win_all_next : ∀ pNext ∈ Game.moves p, ∃ (s : Strategy g i), winning pNext s)
    : ∃ (s : Strategy g i), winning p s := by
  wlog has_moves : (Game.moves p).Nonempty
  · unfold winning winner
    simp_all
  -- We "stitch together" the (possibly overlapping) strategies given by `win_all_next`.
  -- This needs a lot of choice.
  have := Classical.dec -- needed to decide `is_relevant`.
  let stratFor (pNext : g.moves p) : { sI' : Strategy g i // winning pNext sI' } :=
    Exists.subtype (win_all_next pNext.val pNext.prop)
  let s : Strategy g i :=
    (fun pos turn_i has_moves =>
      if is_relevant : ∃ pNext : g.moves p, inMyCone (stratFor pNext).val pNext pos
      then
        let ⟨pNext, pos_inCone⟩ := Exists.subtype is_relevant
        (stratFor pNext).val pos turn_i has_moves
      else
        Classical.choice Strategy.instNonempty pos turn_i has_moves -- should never be used
    )
  use s
  -- Need to show that s is winning at p.
  unfold winning winner
  have : ¬ (Game.turn p = i) := by rw [whose_turn]; cases i <;> simp
  simp_all
  intro sJ
  let nextP := sJ p (by cases i <;> simp_all) (by aesop)
  change winner s sJ nextP.val = i
  -- Now suffices to show that `s'` is winning at `nextP` chosen by `sJ`.
  suffices claim : ∀ n, ∀ nextP : g.moves p, ∀ p,
                inMyCone (stratFor nextP).val nextP p → g.bound p = n → winner s sJ p = i by
    exact claim _ nextP nextP inMyCone.nil rfl
  clear nextP
  -- Remains to show the claim.
  intro n
  induction n using Nat.strongRecOn
  case ind n IH =>
    intro nextP q q_inMyCone def_n
    unfold winner
    -- Want to use `apply IH`, but not on `q`, only later!
    -- Four cases:
    by_cases has_moves : (Game.moves q).Nonempty <;> by_cases turn_i : Game.turn q = i <;> simp_all
    · let nextQ := s q ?_ ?_
      change winner s sJ nextQ = i
      apply IH (g.bound nextQ) ?_ nextP.val ?_ nextQ ?_ rfl
      · rw [← def_n]
        exact g.bound_h q nextQ.val nextQ.prop
      · simp
      · -- Use `myStep` because it is the turn of `i`.
        have := inMyCone.myStep q_inMyCone (Finset.nonempty_iff_ne_empty.mp has_moves) turn_i
        unfold_let nextQ
        convert this using 1
        -- PROBLEM
        -- Need that `s` does the same as `stratFor nextP` at `q`.
        unfold_let s
        -- unfold stratFor
        simp only
        -- simp -- times out, but `simp only` works a bit?
        have : ∃ pNext : g.moves p, inMyCone (stratFor pNext).val pNext q := by
          use nextP
        split
        · unfold stratFor
          convert rfl
          -- PROBLEM: need nextP = Exists.subtype.val ??? Avoid choice to repair this.
          sorry
        · exfalso
          tauto
    · let nextQ := sJ q ?_ ?_ -- sJ, not s here
      change winner s sJ nextQ = i
      apply IH (g.bound nextQ) ?_ nextP.val ?_ nextQ ?_ rfl
      · rw [← def_n]
        exact g.bound_h q nextQ.val nextQ.prop
      · simp
      · apply inMyCone.oStep q_inMyCone ?_ nextQ.prop
        cases i <;> simp_all
    · -- no moves and our turn, cannot be.
      exfalso
      have := winning_here_then_winning_inMyCone
        (stratFor nextP).val nextP (stratFor nextP).prop q q_inMyCone
      unfold winning winner at this
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
    · -- There is a move. Is there a next state where the current player has a winning strategy?
      by_cases ∃ pNext ∈ g.moves p, ∃ (s : Strategy g (g.turn p)), winning pNext s
      case pos hyp =>
        rcases hyp with ⟨pNext, pNext_in, s, s_winning⟩
        -- Whose turn is it? That player has a winning strategy!
        cases whose_turn : g.turn p
        -- GOLF: merge/shorten?
        case A =>
          left
          apply winning_strategy_of_one_next_when_my_turn g p whose_turn ⟨pNext, _⟩ (whose_turn ▸ s)
          convert s_winning
          · simp_all
          · exact eqRec_heq whose_turn s
          · exact pNext_in
        case B =>
          right
          apply winning_strategy_of_one_next_when_my_turn g p whose_turn ⟨pNext, _⟩ (whose_turn ▸ s)
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
          apply winning_strategy_of_all_next_when_others_turn _ _ (by simp_all)
          -- By IH and `hyp` at all next states B must have a winning strategy:
          intro pNext pNext_in_moves_p
          let m := g.bound pNext
          have : m ≤ n := by apply Nat.le_of_lt_succ; rw [h]; exact g.bound_h _ _ pNext_in_moves_p
          have Awin_or_Bwin := IH _ this pNext rfl
          have := hyp pNext pNext_in_moves_p
          suffices ¬ (∃ (s : Strategy g _), winning pNext s) by tauto
          push_neg
          intro s
          rw [whose_turn] at this
          exact this s
        case B =>
          left
          apply winning_strategy_of_all_next_when_others_turn _ _ (by simp_all)
          -- By IH and `hyp` at all next states B must have a winning strategy:
          intro pNext pNext_in_moves_p
          let m := g.bound pNext
          have : m ≤ n := by apply Nat.le_of_lt_succ; rw [h]; exact g.bound_h _ _ pNext_in_moves_p
          have Awin_or_Bwin := IH _ this pNext rfl
          have := hyp pNext pNext_in_moves_p
          suffices ¬ (∃ (s : Strategy g _), winning pNext s) by tauto
          push_neg
          intro s
          rw [whose_turn] at this
          exact this s
    · -- No moves left, we have a winner by definition.
      unfold winning
      unfold winner
      simp_all
      apply Player.eq_A_or_eq_B

/-- Zermelo's Theorem: In every `Game` posiiton one of the two players has a winning strategy.
https://en.wikipedia.org/wiki/Zermelo%27s_theorem_(game_theory)
-/
theorem gamedet (g : Game) [DecidableEq g.Pos] (p : g.Pos) :
    (∃ s : Strategy g A, winning p s) ∨ (∃ s : Strategy g B, winning p s) := gamedet' g p _ rfl
