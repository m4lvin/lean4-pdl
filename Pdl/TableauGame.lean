import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs
import Pdl.LocalAll

/-! # The Tableau Game (Section 6.2 and 6.3) -/

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
  · rename_i lt1 _ _ lt2
    by_cases lt1 = lt2
    · apply isTrue
      aesop
    · apply isFalse
      intro hyp
      cases hyp
      aesop

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

/-- The game defined in Section 6.2.
Still TODO: Lemma 6.10 should be built-in as `tableauGame.wf` and `tableauGame.move_rel`: because
the wellfounded relation holds at every move, all matches must be finite. Note that the paper does
not prove Lemma 6.10 but says it is similar to Lemma 4.10 which uses the Fischer-Ladner closure. -/
def tableauGame : Game where
  Pos := GamePos
  turn
  | ⟨_, _, .inl _⟩ => Prover
  | ⟨_, _, .inr _⟩ => Builder
  moves
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

  -- QUESTION: What is a wellfounded relation that holds for each game step?
  wf := ⟨fun p q => sorry, by sorry⟩
  move_rel := by
    rintro ⟨H, ⟨L,R,_|olf⟩, ProvPo|BuildPo⟩ nextP nextP_in <;> simp_wf
    -- `none` cases without loaded formula in X:
    · cases ProvPo <;> simp at *
      · sorry
      · sorry
    · cases BuildPo
      · exfalso; simp at * -- cannot have an lpr when not loaded
      · simp at *
        sorry
    -- `some olf` cases with loaded formula in X:
    · sorry
    · sorry

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

/-- After history `Hist`, if Prover has a winning strategy then there is a closed tableau.
Note: we skip Definition 6.9 (Strategy Tree for Prover) and just use the `Strategy` type.
This is the induction loading for `gameP`. -/
theorem gameP_general Hist (X : Sequent) (sP : Strategy tableauGame Prover)
  (pos : _)
  (h : winning sP ⟨Hist, X, pos⟩) :
    Nonempty (Tableau Hist X) := by
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
        cases α <;> simp_all
        case atom_prog a in_moves =>
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact ⟨Tableau.pdl nrep Xbas (by apply PdlRule.modL <;> rfl) new_tab_from_IH⟩
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
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
      · -- COPY PASTA only changed L to R
        rcases χ with ⟨α, (ψ : AnyFormula)⟩
        cases α <;> simp_all
        case atom_prog a in_moves =>
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact ⟨Tableau.pdl nrep Xbas (by apply PdlRule.modR <;> rfl) new_tab_from_IH⟩
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
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind

    case nbas nrep X_nbas =>
      -- not basic, Prover should make a local tableau
      constructor
      apply Tableau.loc nrep X_nbas
      -- IDEA: now `sJ` should give us `lt`
      -- and applying an IH should give us `next` ???
      all_goals
        sorry

  -- BuilderPos:
  · rcases builPos with ⟨lpr⟩|⟨nrep, nbas, ltX⟩
    · use Tableau.lrep lpr
    · -- We have a local tableau and it is the turn of Builder.
      -- IDEA: for each `Y : endNodesOf lt` there is an `sB : Strategy _ Prover` that picks `Y`.
      -- Because `sP` wins against all those `sB`, we can use `sP` to define `next`.
      -- For now we do this non-constructively via Nonempty.
      have next' : ∀ (Y : Sequent) (Y_in : Y ∈ endNodesOf ltX), Nonempty (Tableau (X :: Hist) Y) := by
        intro Y Y_in
        -- Now we get an IH.
        apply gameP_general (X :: Hist) Y sP (by apply posOf)
        -- use `h`
        unfold winning at h
        -- NOTE: maybe external lemma like "winning of winning at next step chosen by other" ..
        -- Is there something like this in `Game.lean` already?
        let sJ : Strategy tableauGame Builder := sorry -- some strategy that chooses `Y` ???
        specialize h sJ
        unfold winner at h
        rw [pos_def] at h
        simp at h
        -- Hmmmmm
        unfold winning
        sorry
      have next := fun Y Y_in => Classical.choice (next' Y Y_in)
      use Tableau.loc nrep nbas ltX next
termination_by
  tableauGame.wf.2.wrap ⟨Hist, X, posOf Hist X⟩
decreasing_by
  all_goals
    apply tableauGame.move_rel
    simp [WellFounded.wrap]
  -- Need to show that a valid move was made
  · -- hmm?
    sorry
  · -- hmm?
    sorry

def startPos (X : Sequent) : GamePos := ⟨[], X, posOf [] X⟩

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    Nonempty (Tableau [] X) := gameP_general [] X s _ h

/-! ## From winning strategies to model graphs (Section 6.3) -/

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
