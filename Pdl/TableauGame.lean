import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Decidability Helpers -- FIXME move elsewhere -/

-- FIXME move
instance {H X} : Decidable (Nonempty (LoadedPathRepeat H X)) := by
  by_cases ∃ k, (H.get k).multisetEqTo X ∧ ∀ m ≤ k, (H.get m).isLoaded
  case pos h =>
    apply isTrue
    rcases h with ⟨k, same, all_le_loaded⟩
    exact ⟨k, same, all_le_loaded⟩
  case neg h =>
    apply isFalse
    simp only [not_nonempty_iff]
    constructor
    rintro ⟨k, same, all_le_loaded⟩
    push_neg at h
    specialize h k same
    aesop

-- FIXME move
instance {φ : Formula} {X :Sequent} : Decidable (φ ∈ X) := by
  rcases X with ⟨L,R,o⟩
  simp
  infer_instance

/-- Easy, but this is only for a list `L`, we want this for some Sequent `X`. -/
example {p : α → Prop} [DecidablePred p] {L : List α} : Decidable (∃ x ∈ L, p x) := by infer_instance

/-- A variant of `Fintype.decidableExistsFintype`. -/
instance Fintype.decidableExistsImpliesFintype {α : Type u_1} {p q : α → Prop} [DecidablePred p] [DecidablePred q] [Fintype (Subtype p)] : Decidable (∃ (a : α), p a ∧ q a) := by
  by_cases ∃ x : Subtype p, q x -- This uses the Fintype instance.
  · apply isTrue
    aesop
  · apply isFalse
    aesop

instance instFintypeSubtypeMemSequent {X : Sequent} : Fintype (Subtype (fun x => x ∈ X)) := by
  rcases X with ⟨L,R,o⟩
  simp only [instMembershipFormulaSequent, Sequent.L, Sequent.R]
  apply Fintype.subtype (L.toFinset ∪ R.toFinset)
  aesop

instance {X : Sequent} : Decidable (X.closed) := by
  unfold Sequent.closed
  by_cases ⊥ ∈ X
  · apply isTrue
    tauto
  · have := @Fintype.decidableExistsImpliesFintype _ (· ∈ X) (fun f => (~f) ∈ X) _ _ instFintypeSubtypeMemSequent
    by_cases ∃ f, f ∈ X ∧ (~f) ∈ X
    · apply isTrue
      aesop
    · apply isFalse
      aesop

instance {X : Sequent} : Decidable (X.basic) := by
  by_cases X.closed
  · apply isFalse
    rcases X with ⟨L,R,o⟩
    unfold Sequent.basic
    aesop
  case neg h =>
    rcases X with ⟨L,R,o⟩
    unfold Sequent.basic
    simp only [h, not_false_eq_true, and_true]
    by_cases ∃ f ∈ L ++ R ++ (Option.map (Sum.elim negUnload negUnload) o).toList, f.basic ≠ true
    · apply isFalse
      push_neg
      assumption
    · apply isTrue
      push_neg at *
      assumption

/-! ## Defining the Tableau Game (Section 6.2) -/

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

inductive ProverPos (H : History) (X : Sequent) : Type where
  | nlpRep : ¬ Nonempty (LoadedPathRepeat H X) → rep H X → ProverPos H X -- Prover loses
  | bas : ¬ rep H x → X.basic → ProverPos H X -- Prover must make a local LocalTableau
  | nbas : ¬ rep H x → ¬ X.basic → ProverPos H X -- Prover must apply a PDL rule
  -- FIXME maye merge bas and nbas?
  deriving DecidableEq

instance {H X} : DecidableEq (LoadedPathRepeat H X) := by
  intro lpr1 lpr2
  rcases lpr1 with ⟨k1, same1, load1⟩
  rcases lpr2 with ⟨k2, same2, load2⟩
  by_cases k1 = k2
  · apply isTrue
    aesop
  · apply isFalse
    -- Actually, this case should be impossible, but that would be harder to show!
    rw [Subtype.ext_iff]
    simp
    assumption

def BuilderPos (H : History) (X : Sequent) : Type :=
  LoadedPathRepeat H X -- no moves, Prover wins.
  ⊕
  LocalTableau X -- Builder must pick from endNodesOf

instance {H X} : DecidableEq (BuilderPos H X) := by
  rintro (_|_) (_|_) <;> try (simp; exact instDecidableFalse)
  · rename_i lr1 lr2
    by_cases lr1 = lr2
    · apply isTrue
      aesop
    · apply isFalse
      intro hyp
      cases hyp
      aesop
  · rename_i lt1 lt2
    by_cases lt1 = lt2
    · apply isTrue
      aesop
    · apply isFalse
      intro hyp
      cases hyp
      aesop

def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
  deriving DecidableEq

-- There's probably a more elegant way to fully avoid Nonempty and choice here?
-- Something like: def isLPR (H : History) (X : Sequent) : Prop := sorry

def LoadedPathRepeat.choice {H X} (ne : Nonempty (LoadedPathRepeat H X)) : LoadedPathRepeat H X := by
  let somek := @Fin.find (H.length)
    (fun k => (H.get k).multisetEqTo X ∧ ∀ m ≤ k, (H.get m).isLoaded = true) _
  rcases find_def : somek with _|⟨k⟩
  · exfalso
    rw [Fin.find_eq_none_iff] at find_def
    rcases ne with ⟨⟨k,bla⟩⟩
    specialize find_def k
    aesop
  · refine ⟨k, ?_⟩
    rw [Fin.find_eq_some_iff] at find_def
    aesop

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if neNlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.inl (.choice neNlp)) -- BuilderPos with no moves to let Prover win at lpr
  else
    if rep : rep H X
    then .inl (.nlpRep neNlp rep) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas rep bas) -- actual ProverPos to make LocalTab
      else .inl (.nbas rep bas) -- actual ProverPos to choose a PDL rule

def LocalRuleApp.all X : List (Σ B, LocalRuleApp X B) := sorry

lemma LocalRuleApp.all_spec X B lra : ⟨B, lra⟩ ∈ LocalRuleApp.all X := by
  sorry

instance LocalRuleApp.fintype {X} : Fintype (LocalRuleApp X B) := by
  refine ⟨((LocalRuleApp.all X).filterMap
    (fun Zlra => if h : Zlra.1 = B then some (h ▸ Zlra.2) else none)).toFinset, ?_⟩
  intro lra
  rw [List.mem_toFinset]
  simp only [List.mem_filterMap, Option.dite_none_right_eq_some, Option.some.injEq, Sigma.exists]
  use B
  simp only [exists_const, exists_eq_right]
  apply LocalRuleApp.all_spec

-- def comobo : (List (List α)) → (List (List α)) -- hmm

def LocalTableau.all : (X : Sequent) → List (LocalTableau X) := fun X =>
  if bas : X.basic
  then [ .sim bas ]
  else do
    let ⟨B, (lra : LocalRuleApp X B)⟩ <- LocalRuleApp.all X
    let tabsFor (Y : Sequent) (h : Y ∈ B) : List (LocalTableau Y) := sorry -- LocalTableau.all Y
    let nexts : List ((Y : Sequent) → Y ∈ B → LocalTableau Y) := by
      sorry
    let next <- nexts
    return @byLocalRule X B lra next

lemma LocalTableau.all_spec : ltX ∈ LocalTableau.all X := by
  sorry

instance LocalTableau.fintype {X} : Fintype (LocalTableau X) := by
  refine ⟨(LocalTableau.all X).toFinset, ?_⟩
  intro ltX
  rw [List.mem_toFinset]
  exact LocalTableau.all_spec


def tableauGame : Game where
  Pos := GamePos
  turn
  | ⟨_, _, .inl _⟩ => Prover
  | ⟨_, _, .inr _⟩ => Builder
  moves
  -- ProverPos:
  | ⟨H, X, .inl (.nlpRep _ _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ Xbasic)⟩ =>
      -- need to choose PDL rule application:
      match X with
      | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
            (L.map (fun φ => match boxesOf φ with -- need ALL the boxes.
              | (δ@h:(_::_), ψ) =>
                [ ⟨_,_,posOf (X::H) (L.erase (~⌈⌈δ⌉⌉φ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊δ.getLast (by subst h; simp)⌋φ))))⟩ ]
              | ([],_) => [] ) ).flatten.toFinset
            ∪
            (R.map (fun φ => match boxesOf φ with -- need ALL the boxes.
              | (δ@h:(_::_), ψ) =>
                [ ⟨_,_,posOf (X::H) (L, R.erase (~⌈⌈δ⌉⌉φ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊δ.getLast (by subst h; simp)⌋φ))))⟩ ]
              | ([],_) => [] ) ).flatten.toFinset
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ => (
              -- (M) rule, deterministic:
              ( match ξ with
              | .normal φ => [⟨_,_,posOf (X::H) ⟨(~φ) :: projection a L, projection a R, none⟩⟩]
              | .loaded χ => [⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inl (~'χ))⟩⟩] )
              ++
              -- (L-) rule, deterministic:
              [⟨_, _, posOf (X::H) ((L.insert (⌊·a⌋ξ).unload, R, none))⟩]
          ).toFinset -- can we avoid the list, make Finset directly?
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ => (
              -- (M) rule, deterministic:
              ( match ξ with
              | .normal φ => [⟨_,_,posOf (X::H) ⟨projection a L, (~φ) :: projection a R, none⟩⟩]
              | .loaded χ => [⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inr (~'χ))⟩⟩] )
              ++
              -- (L-) rule, deterministic:
              [⟨_, _, posOf (X::H) ((L, R.insert (⌊·a⌋ξ).unload, none))⟩]
          ).toFinset -- can we avoid the list, make Finset directly?

      -- Somewhat repetitive here. Is there pattern matching with "did not match before" proofs?
      | ⟨L, R, some (.inl (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *

  | ⟨H, X, .inl (.nbas _ _)⟩ =>
      -- If not basic, let prover pick any `ltab : LocalTableau X` as new position.
      LocalTableau.fintype.1.image (fun ltab => ⟨H, X, .inr (.inr ltab)⟩)
  -- BuilderPos:
  | ⟨H, X, .inr (.inl lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.inr ltab)⟩ =>
      ((endNodesOf ltab).map (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩)).toFinset

  -- QUESTION: What is a wellfounded relation that goes down at each game step?
  wf := ⟨fun p q => sorry, by sorry⟩
  move_rel := by
    intro p next next_in
    simp_wf
    sorry

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
