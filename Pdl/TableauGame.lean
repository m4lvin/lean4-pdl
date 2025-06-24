import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Defining the Tableau Game (Section 6.2) -/

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

inductive ProverPos (H : History) (X : Sequent) : Type where
  | nlpRep : ¬ Nonempty (LoadedPathRepeat H X) → rep H X → ProverPos H X -- Prover loses
  | bas : ¬ rep H x → X.basic → ProverPos H X -- Prover must make a local LocalTableau
  | nbas : ¬ rep H x → ¬ X.basic → ProverPos H X -- Prover must apply a PDL rule
-- FIXME maye merge bas and nbas?

def BuilderPos (H : History) (X : Sequent) : Type :=
  LoadedPathRepeat H X -- no moves, Prover wins.
  ⊕
  LocalTableau X -- Builder must pick from endNodesOf

def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
instance : DecidableEq GamePos := sorry

-- TODO
instance {H X} : Decidable (rep H X) := sorry
instance {H X} : Decidable (Nonempty (LoadedPathRepeat H X)) := sorry
instance {X : Sequent} : Decidable (X.basic) := sorry

-- FIXME can we avoid Nonempty and choice here?
-- `LoadedPathRepeat H X` should be computable, intuitively.

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if nlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.inl sorry) -- FIXME choice?! -- BuilderPos with no moves to let Prover win at lpr
  else
    if rep : rep H X
    then .inl (.nlpRep nlp rep) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas rep bas) -- actual ProverPos to make LocalTab
      else .inl (.nbas rep bas) -- actual ProverPos to choose a PDL rule

def tableauGame : Game where
  Pos := GamePos
  turn
  | ⟨_, _, .inl _⟩ => Prover
  | ⟨_, _, .inr _⟩ => Builder
  moves
  -- ProverPos:
  | ⟨H, X, .inl (.nlpRep _ _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ _)⟩  =>
      -- need to choose PDL rule application
      -- (L+) if X is not loaded  << choice of formula
      -- (L-) if X is loaded (deterministic)
      -- (M) if loaded (deterministic)
      sorry
  | ⟨H, X, .inl (.nbas _ _)⟩ =>
      -- pick an `ltab : LocalTableau x`, then map `posOf` over `endNodesOf ltab`
      sorry
  -- BuilderPos:
  | ⟨H, X, .inr (.inl lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.inr ltab)⟩ =>
      ((endNodesOf ltab).map (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩)).toFinset

  bound := sorry
  bound_h := sorry


-- TODO Definition 6.9 Strategy Tree fro Prover (or adjust already in `Game.lean`?)

-- TODO Definition 6.13 initial, pre-state

-- TODO Lemma 6.14

-- TODO Lemma 6.15

-- TODO Lemma 6.16 pre-states are locally consistent and saturated, last node basic.

-- TODO Definition 6.18 to get model graph from strategy tree.

-- TODO Lemma 6.18

-- TODO Lemma 6.19

-- TODO Lemma 6.20

def startPos (X : Sequent) : GamePos := ⟨[], X, posOf [] X⟩

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    Nonempty (Tableau [] X) := by
  sorry

/-! ## From winning strategies to model graphs (Section 6.3) -/

/-- If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), X.toFinset ∈ WS := by
  sorry
