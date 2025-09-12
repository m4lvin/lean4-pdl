import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs
import Pdl.LocalAll

import Pdl.TransFinWF
import Pdl.FischerLadner

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Prover and Builder positions -/

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

inductive ProverPos (H : History) (X : Sequent) : Type where
  | nlpRep : ¬ Nonempty (LoadedPathRepeat H X) → ProverPos H X -- Prover loses
  | bas : ¬ rep H X → X.basic → ProverPos H X -- Prover must apply a PDL rule
  | nbas : ¬ rep H X → ¬ X.basic → ProverPos H X -- Prover must make a local LocalTableau
  deriving DecidableEq

inductive BuilderPos (H : History) (X : Sequent) : Type where
  | lpr : LoadedPathRepeat H X → BuilderPos H X -- no moves, Prover wins.
  | ltab : ¬ rep H X → ¬ X.basic → LocalTableau X → BuilderPos H X -- Builder must pick endNodesOf
  deriving DecidableEq

def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
  deriving DecidableEq

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if neNlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.lpr (.choice neNlp)) -- BuilderPos with no moves to let Prover win at lpr
  else
    if rep : rep H X
    then .inl (.nlpRep neNlp) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas rep bas) -- actual ProverPos to choose a PDL rule
      else .inl (.nbas rep bas) -- actual ProverPos to make LocalTab

/-! ## Moves -/

/-- The moves for the `tableauGame`. -/
@[simp]
def theMoves : GamePos → Finset GamePos
  -- ProverPos:
  | ⟨H, X, .inl (.nlpRep _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ Xbasic)⟩ =>
      -- need to choose PDL rule application:
      match X with
      | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
            -- We want to catch a negation and all boxes (≥ 1) after it to be loaded.
            (L.map (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              [ ⟨_,_,posOf (X::H) (L.erase (~φ), R, some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by subst h; simp)⌋ψ))))⟩ ]
                            | ([],_) => []
                        | _ => [] )).flatten.toFinset
            ∪
            (R.map (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              [ ⟨_,_,posOf (X::H) (L, R.erase (~φ), some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by subst h; simp)⌋ψ))))⟩ ]
                            | ([],_) => []
                        | _ => [] )).flatten.toFinset
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨(~φ) :: projection a L, projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inl (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L.insert (~(⌊·a⌋ξ).unload), R, none)⟩ }
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨projection a L, (~φ) :: projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inr (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L, R.insert (~(⌊·a⌋ξ).unload), none)⟩ }
      -- Somewhat repetitive. Is there pattern matching with "did not match before" proofs?
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
  | ⟨H, X, .inl (.nbas nrep nbas)⟩ =>
      -- If not basic, let prover pick any `ltab : LocalTableau X` as new position.
      LocalTableau.fintype.1.image (fun ltab => ⟨H, X, .inr (.ltab nrep nbas ltab)⟩)
  -- BuilderPos:
  | ⟨H, X, .inr (.lpr lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.ltab _ _ ltab)⟩ =>
      ((endNodesOf ltab).map (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩)).toFinset

def move (next p : GamePos) := next ∈ theMoves p

lemma no_moves_of_rep {Hist X pos} (h : rep Hist X) :
    theMoves ⟨Hist, X, pos⟩ = ∅ := by
  by_contra hyp
  rw [Finset.eq_empty_iff_forall_notMem] at hyp
  push_neg at hyp
  rcases hyp with ⟨p, p_in⟩
  unfold theMoves at p_in
  rcases X with ⟨L,R,_|o⟩ <;> rcases pos with (_|_|_)|(_|_) <;> aesop

lemma move_then_no_rep {next} {p : (ProverPos Hist X ⊕ BuilderPos Hist X)} :
    move next ⟨Hist, X, p⟩ → ¬ rep Hist X := by
  intro next_p hyp
  have := @no_moves_of_rep _ _ p hyp
  unfold move at next_p
  aesop

lemma move.hist (mov : move next ⟨Hist, X, pos⟩) :
      (∃ newPos, next = ⟨Hist, X, newPos⟩) -- this is an annoying case ;-)
    ∨ (∃ Y newPos, next = ⟨X :: Hist, Y, newPos⟩)  := by
  unfold move theMoves at mov
  simp at mov
  rcases X with ⟨L,R,_|o⟩ <;> rcases pos with (_|_|_)|(_|_) <;> simp at mov
  all_goals
    grind

/-! ## Termination -/

-- Quick reminder how ≤ and ⊆ work on multisets.
example : ¬ {2,2,1} ≤ ({1,2} : Multiset Nat) := by decide -- cares about multiplicity
example :   {2,2,1} ⊆ ({1,2} : Multiset Nat) := by simp_all -- set-like / only cares about support

/-- `X` is a component-wise *multi*subset of the FL-closure of `Y`.
This implies `Sequent.subseteq_FL` but not vice versa, because infinitely
many multisets yield the same set.
!!! TODO also need to take into account X.O and Y.O on both sides each !! -/
def Sequent.multisubseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
    Multiset.ofList X.R < Multiset.ofList (FLL Y.R)
  ∧ Multiset.ofList X.L < Multiset.ofList (FLL Y.L)

/-- Sequent `X` is a component-wise subset of the FL-closure of `Y`.
!!! TODO also need to take into account X.O and Y.O on both sides each !! -/
def Sequent.subseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
    X.R ⊆ FLL Y.R  ∧  X.L ⊆ FLL Y.L  ∧  true

@[simp]
lemma Sequent.subseteq_FL_refl (X : Sequent) : X.subseteq_FL X := by sorry

@[simp]
lemma Sequent.subseteq_FL_trans (X Y Z: Sequent) :
    X.subseteq_FL Y → Y.subseteq_FL Z → X.subseteq_FL Z := by
  sorry

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, (Y.1) ⊆ FL (~ χ.unload) := by -- PROBLEM: also need to cover Y.2
  sorry

/-- Helper for `move_inside_FL` -/
theorem LocalRule.stays_in_FL {Lcond Rcond Ocond B}
    (rule : LocalRule (Lcond, Rcond, Ocond) B) :
    ∀ Y ∈ B, Y.subseteq_FL ⟨Lcond, Rcond, Ocond⟩ := by
  -- intro res res_in_B x x_in_res
  cases rule
  <;> sorry


lemma move_inside_FL : move next p → next.2.1.subseteq_FL p.2.1 := by
  -- This will be many case distinctions and extra lemmas.
  sorry

-- QUESTION: Given (X : Sequent) how to say
-- "there are only finitely many "sequents modulo `setEq`" that are subseteq_FL Y X
-- ???

/-- Lemma 6.10, sort of. Because the move relation is wellfounded, all matches must be finite.
Note that the paper does not prove this, only says it is similar to the proof that PDL-tableaux
are finite, i.e. Lemma 4.10 which uses the Fischer-Ladner closure. -/
lemma move.wf : WellFounded move := by
  -- If it's not wellfounded, then there must be an infinite sequence of moves.
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra hyp
  simp at hyp
  rcases hyp with ⟨f, f_rel⟩

  have all_moves_inside : ∀ n, ((f n).2.1).subseteq_FL (f 0).2.1 := by
    intro k
    induction k
    · simp
    case succ k IH =>
      apply Sequent.subseteq_FL_trans _ _ _ ?_ IH
      apply move_inside_FL (f_rel k)

  -- TODO: state that the history of all `f k` must be shared, proven via `move.hist`?

  -- IDEA from here onwards: the Hist and X stays inside FL, but they also must all be different?!
  -- Well, almost all must be different. Single steps that keep `Hist` and `X` are sometimes
  -- allowed, in the annyong case in `move.hist`.

  have no_repeats : ∀ n, ¬ rep (f n).1 (f n).2.1 := fun k => move_then_no_rep (f_rel k)

  unfold rep at *

  sorry

  /- OLD IDEA for `move.wf`
  apply @wf_of_finTransInvImage_of_transIrrefl
  · -- To show: only finitely many moves are reachable
    -- Use `move_inside_flc` for this.
    sorry
  · -- To show: (TransGen move) is irreflexive, i.e. no repeats.
    -- Use `no_moves_of_rep` here maybe?
    sorry
  -/

/-! ## Actual Game Definition -/

/-- The game defined in Section 6.2.-/
def tableauGame : Game where
  Pos := GamePos
  turn | ⟨_, _, .inl _⟩ => Prover
       | ⟨_, _, .inr _⟩ => Builder
  moves := theMoves
  wf := ⟨move, move.wf⟩
  move_rel := by simp [move]

@[simp]
lemma tableauGame_turn_Prover {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inl lpr⟩ = Prover := by
  unfold Game.turn
  unfold tableauGame
  simp

@[simp]
lemma tableauGame_turn_Builder {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inr lpr⟩ = Builder := by
  unfold Game.turn tableauGame
  simp

@[simp]
lemma tableauGame_winner_nlpRep_eq_Builder :
    @winner i tableauGame sI sJ ⟨Hist, X, .inl (.nlpRep h1)⟩ = Builder := by
  simp [winner, tableauGame]

@[simp]
lemma tableauGame_winner_lpr_eq_Prover :
    @winner i tableauGame sI sJ ⟨Hist, X, .inr (.lpr lpr)⟩ = Prover := by
  simp [winner, tableauGame]


lemma def_of_boxesOf_def (h : boxesOf φ = (αs, ψ)) : φ = ⌈⌈αs⌉⌉ψ := by
  induction αs generalizing φ
  · unfold boxesOf at h
    cases φ <;> simp_all
  case cons α αs IH =>
    simp
    cases φ <;> simp_all [boxesOf]
    case box β φ =>
      apply IH
      grind

/-! ## From Prover winning strategies to tableau -/

/-- After history `Hist`, if Prover has a winning strategy then there is a closed tableau.
Note: we skip Definition 6.9 (Strategy Tree for Prover) and just use the `Strategy` type.
This is the induction loading for `gameP`. -/
theorem gameP_general Hist (X : Sequent) (sP : Strategy tableauGame Prover) (pos : _)
    (h : winning sP ⟨Hist, X, pos⟩)
    : Nonempty (Tableau Hist X) := by
  rcases pos_def : pos with proPos|builPos
  -- ProverPos:
  · cases proPos
    · -- free repeat, but then Prover loses, which contradicts h.
      absurd h
      simp [pos_def,winning]
    case bas nrep Xbas =>
      -- basic, Prover should choose PDL rule
      rw [pos_def] at h
      have P_turn : tableauGame.turn ⟨Hist, ⟨X, pos⟩⟩ = Prover := by
        rw [pos_def]
        simp
      -- Ask `sP` say which move to make / what rule to apply.
      let the_move := sP ⟨_ ,_, pos⟩ ?_ ?_
      case refine_1 => rw [pos_def]; unfold Game.turn tableauGame; simp
      case refine_2 => by_contra hyp; exfalso; unfold winning winner at h; simp_all
      -- Using lemma that if sP is winning here then sP is still winning after sP moves.
      have still_winning : winning sP the_move := winning_of_winning_move P_turn (pos_def ▸ h)
      -- Now use IH to get the remaining tableau.
      have IH := gameP_general _ _ sP _ still_winning -- okay ??
      rcases IH with ⟨new_tab_from_IH⟩
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp at new_tab_from_IH
      simp only [tableauGame, Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      rcases X with ⟨L,R,_|(⟨⟨χ⟩⟩|⟨⟨χ⟩⟩)⟩ <;> simp at *
      · -- no loaded formula yet, the only PDL rule we can apply is (L+)
        rcases nextPosIn with ⟨χ, χ_in⟩|⟨χ, χ_in⟩
        · cases χ
          case neg φ =>
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, List.mem_cons, List.not_mem_nil, or_false]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              constructor -- leaving Prop
              apply Tableau.pdl nrep Xbas
                (@PdlRule.loadL _ ((δ :: αs).dropLast) ((δ :: αs).getLast (by simp)) ψ _ _ ?_ ?_)
                new_tab_from_IH
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
                simp_all only [Formula.boxes_cons]
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
          all_goals -- other formulas, cannot have empty boxesOf
            exfalso
            simp at χ_in
        -- COPY-PASTA only changed loadL to loadR
        · cases χ
          case neg φ =>
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, List.mem_cons, List.not_mem_nil, or_false]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              constructor -- leaving Prop
              apply Tableau.pdl nrep Xbas
                (@PdlRule.loadR _ ((δ :: αs).dropLast) ((δ :: αs).getLast (by simp)) ψ _ _ _ _)
                new_tab_from_IH
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
                simp_all only [Formula.boxes_cons]
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
          all_goals -- other formulas, cannot have empty boxesOf
            exfalso
            simp at χ_in
      · -- already have loaded formula in left, PDL rule must be (M) or (L-)
        rcases χ with ⟨α, (ψ : AnyFormula)⟩
        cases α
        case atom_prog a in_moves =>
          simp_all only [tableauGame_turn_Prover, Finset.mem_insert]
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (L-)
            cases nextPosIn
            cases ψ
            case normal φ0 =>
              constructor
              apply Tableau.pdl nrep Xbas ?_ new_tab_from_IH
              apply @PdlRule.freeL _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              constructor
              apply Tableau.pdl nrep Xbas ?_ new_tab_from_IH
              apply @PdlRule.freeL _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact ⟨Tableau.pdl nrep Xbas (PdlRule.modL rfl rfl) new_tab_from_IH⟩
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
      · -- COPY PASTA only changed L to R
        rcases χ with ⟨α, (ψ : AnyFormula)⟩
        cases α
        case atom_prog a in_moves =>
          simp_all only [tableauGame_turn_Prover, Finset.mem_insert]
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (L-)
            cases nextPosIn
            cases ψ
            case normal φ0 =>
              constructor
              apply Tableau.pdl nrep Xbas ?_ new_tab_from_IH
              apply @PdlRule.freeR _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              constructor
              apply Tableau.pdl nrep Xbas ?_ new_tab_from_IH
              apply @PdlRule.freeR _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact ⟨Tableau.pdl nrep Xbas (by apply PdlRule.modR <;> rfl) new_tab_from_IH⟩
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
    case nbas nrep X_nbas =>
      -- not basic, Prover should make a local tableau
      -- COPY PASTA from bas case ...
      rw [pos_def] at h
      have P_turn : tableauGame.turn ⟨Hist, ⟨X, pos⟩⟩ = Prover := by
        rw [pos_def]
        simp
      -- Ask `sP` say which move to make / what rule to apply.
      let the_move := sP ⟨_ ,_, pos⟩ ?_ ?_
      case refine_1 => rw [pos_def]; unfold Game.turn tableauGame; simp
      case refine_2 => by_contra hyp; exfalso; unfold winning winner at h; simp_all
      -- Using lemma that if sP is winning here then sP is still winning after sP moves.
      have still_winning : winning sP the_move := winning_of_winning_move P_turn (pos_def ▸ h)
      -- Now use IH to get the remaining tableau.
      have IH := gameP_general _ _ sP _ still_winning -- okay ??
      rcases IH with ⟨new_tab_from_IH⟩
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp at new_tab_from_IH
      simp only [tableauGame, Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      --- ... until here
      -- No need to look into `lt` here, we just use the IH for the `BuilderPos` case!
      simp at nextPosIn
      rcases nextPosIn with ⟨lt, lt_in, same⟩
      cases same
      constructor
      exact new_tab_from_IH
  -- BuilderPos:
  · rcases builPos with ⟨lpr⟩|⟨nrep, nbas, ltX⟩
    · use Tableau.lrep lpr
    · -- We have a local tableau and it is the turn of Builder.
      -- Now each `Y : endNodesOf lt` is a possible move.
      -- Because `sP` wins against all moves by Builder we can use `sP` to define `next`.
      -- Note that all is non-constructive here via Nonempty.
      have next' : ∀ (Y : Sequent) (Y_in : Y ∈ endNodesOf ltX), Nonempty (Tableau (X :: Hist) Y) := by
        intro Y Y_in
        apply gameP_general (X :: Hist) Y sP (by apply posOf) -- the IH
        subst pos_def
        -- The main work is done by the following lemma
        have := winning_of_whatever_other_move (by simp) h
        simp [tableauGame, Game.moves] at this
        exact this _ Y_in
      have next := fun Y Y_in => Classical.choice (next' Y Y_in)
      use Tableau.loc nrep nbas ltX next
termination_by
  tableauGame.wf.2.wrap ⟨Hist, X, pos⟩ -- note `pos`, not `posOf` here.
decreasing_by
  all_goals
    apply tableauGame.move_rel
    simp [WellFounded.wrap]
  · subst pos_def
    simp [tableauGame, Game.moves]
    use Y

/-- The starting position for the given sequent.
With an empty history and using `posOf` to determine the first `GamePos`. -/
def startPos (X : Sequent) : GamePos := ⟨[], X, posOf [] X⟩

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    Nonempty (Tableau [] X) := gameP_general [] X s _ h

/-! ## From Builder winning strategies to model graphs (Section 6.3) -/

-- See also Bml/CompletenessViaPaths.lean for the things needed here.

-- TODO Definition 6.13 initial, pre-state

-- TODO Lemma 6.14: how to collect formulas in a pre-state

-- TODO Lemma 6.15

-- TODO Lemma 6.16 pre-states are locally consistent and saturated, last node basic.

-- TODO Definition 6.18 to get model graph from strategy tree.

-- TODO Lemma 6.18

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded

-- TODO Lemma 6.20: diamond existence lemma for pre-states

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), X.toFinset ∈ WS := by
  sorry
