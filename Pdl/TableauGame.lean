import Mathlib.Data.Quot

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

/-- The relation `move old next` says that we can move from `old` to `next`.
There are three kinds of moves. -/
-- @[grind] -- FIXME
inductive move : (old : GamePos) → (new : GamePos) → Prop
/-- When the sequent is basic and no repeat, let prover apply a PDL rule. -/
| prPdl {Y Hist nrep Xbasic} : PdlRule X Y →
    move ⟨Hist, X, .inl (.bas nrep Xbasic)⟩ ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩
/-- If not basic, let prover pick any `ltab : LocalTableau X` as new position. -/
| prLocTab {Hist X nrep nbas ltab} : move ⟨Hist, X, .inl (.nbas nrep nbas)⟩
                                          ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩
/-- Let Builder pick an end node of `ltab` -/
| buEnd {X ltab Y Hist nrep nbas} : Y ∈ endNodesOf (ltab : LocalTableau X) →
    move ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩ ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩

lemma move_then_no_rep {Hist X next} {p : (ProverPos Hist X ⊕ BuilderPos Hist X)} :
    move ⟨Hist, X, p⟩ next → ¬ rep Hist X := by
  intro next_p hyp
  cases next_p <;> grind

/-- The finite set of moves, given as a function instead of a relation.
In `theMoves_mem_iff_move` below we prove that this agrees with `move`. -/
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
                              [ ⟨ _, _, posOf (X::H) (L.erase (~φ), R
                                , some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ ]
                            | ([],_) => []
                        | _ => [] )).flatten.toFinset
            ∪
            (R.map (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              [ ⟨ _, _, posOf (X::H) (L, R.erase (~φ)
                                , some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ ]
                            | ([],_) => []
                        | _ => [] )).flatten.toFinset
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨(~φ) :: projection a L, projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ projection a L, projection a R
                                                 , some (Sum.inl (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L.insert (~(⌊·a⌋ξ).unload), R, none)⟩ }
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨projection a L, (~φ) :: projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ projection a L, projection a R
                                                 , some (Sum.inr (~'χ))⟩⟩ } )
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
      -- Let Builder pick an end node of `ltab`:
      ((endNodesOf ltab).map (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩)).toFinset

set_option maxHeartbeats 2000000 in -- for simp_all timeouts
/-- Characterization of `theMoves`. -/
lemma theMoves_iff {H X} {p : ProverPos H X ⊕ BuilderPos H X} {next : GamePos} :
    next ∈ theMoves ⟨H, X, p⟩
    ↔
    -- ProverPos:
    ( ∃ nrep Xbasic, p = .inl (.bas nrep Xbasic)
      ∧ ∃ L R, ( -- need to choose PDL rule application:
        ( X = ⟨L, R, none⟩ -- (L+) rule, choosing formula to load
          ∧ ( ( ∃ δs δ ψ, ¬ ψ.isBox ∧ (~⌈⌈δs⌉⌉⌈δ⌉ψ) ∈ L
                ∧ next = ⟨_, _, posOf (X::H) ( L.erase (~⌈⌈δs⌉⌉⌈δ⌉ψ), R
                                             , some (Sum.inl (~'(⌊⌊δs⌋⌋⌊δ⌋ψ))))⟩)
              ∨
              ( ∃ δs δ ψ, ¬ ψ.isBox ∧ (~⌈⌈δs⌉⌉⌈δ⌉ψ) ∈ R
                ∧ next = ⟨_, _, posOf (X::H) ( L, R.erase (~⌈⌈δs⌉⌉⌈δ⌉ψ)
                                             , some (Sum.inr (~'(⌊⌊δs⌋⌋⌊δ⌋ψ))))⟩)
            )
        )
        ∨
        ( ∃ a ξ, X = ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩
          ∧ ( ( ∃ φ, ξ = .normal φ -- (M) rule, deterministic
                ∧ next = ⟨_,_,posOf (X::H) ⟨(~φ) :: projection a L, projection a R, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inl (~'χ))⟩⟩ )
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L.insert (~(⌊·a⌋ξ).unload), R, none)⟩ )
            )
        )
        ∨
        ( ∃ a ξ, X = ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩
          ∧ ( ( ∃ φ, ξ = .normal φ -- (M) rule, deterministic
                ∧ next = ⟨_,_,posOf (X::H) ⟨projection a L, (~φ) :: projection a R, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inr (~'χ))⟩⟩)
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L, R.insert (~(⌊·a⌋ξ).unload), none)⟩
              )
            )
        )
      )
    )
    ∨
    ( ∃ nrep nbas, p = .inl (.nbas nrep nbas) -- not basic, prover picks ltab
      ∧ ∃ ltab : LocalTableau X, next = ⟨H, X, .inr (.ltab nrep nbas ltab)⟩
    )
    ∨
    -- BuilderPos:
    ( ∃ nrep nbas ltab, p = .inr (.ltab nrep nbas ltab) -- builds picks end node
      ∧ ∃ Y ∈ endNodesOf ltab, next = ⟨(X :: H), Y, posOf (X :: H) Y⟩) := by
  constructor
  · intro mv
    unfold move theMoves at mv
    rcases p with (_|_|_) | (_|_) <;> rcases X with ⟨L,R,_|χ⟩
    · simp at *
    · simp at *
    · simp_all -- bas none case
      -- use L, R
      rcases mv with ⟨ψ, ψ_in, next_in⟩ | ⟨ψ, ψ_in, next_in⟩ -- FIXME
      · cases ψ -- L
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp [bxs_def, List.mem_cons, List.not_mem_nil, or_false] at next_in
            refine ⟨L, R, Or.inl ⟨ rfl, Or.inl ⟨(head :: tail).dropLast
                                 , (head :: tail).getLast (by simp), ψ, ?_⟩⟩⟩
            rw [← boxes_last, List.dropLast_append_getLast]
            have := def_of_boxesOf_def bxs_def; grind
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
      · cases ψ -- R, analogous
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp [bxs_def, List.mem_cons, List.not_mem_nil, or_false] at next_in
            refine ⟨L, R, Or.inl ⟨ rfl, Or.inr ⟨(head :: tail).dropLast
                                 , (head :: tail).getLast (by simp), ψ, ?_⟩⟩⟩
            rw [← boxes_last, List.dropLast_append_getLast]
            have := def_of_boxesOf_def bxs_def; grind
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
    · -- Here we have a loaded formula in X already, and are basic.
      -- So the only applicable rules are (M) and (L-).
      rcases χ with (⟨⟨χ⟩⟩|⟨⟨χ⟩⟩) <;> rcases χ with ⟨δ,φ|χ⟩ <;> cases δ <;> simp_all
      all_goals
        try grind
      case inl.normal.atom_prog a nrep bas =>
        exact ⟨L, R, Or.inr (Or.inl ⟨a, .normal φ, by aesop⟩)⟩
      case inl.loaded.atom_prog a nrep bas =>
        exact ⟨L, R, Or.inr (Or.inl ⟨a, .loaded χ, by aesop⟩)⟩
      case inr.normal.atom_prog a nrep bas =>
        exact ⟨L, R, Or.inr (Or.inr ⟨a, .normal φ, by aesop⟩)⟩
      case inr.loaded.atom_prog a nrep bas =>
        exact ⟨L, R, Or.inr (Or.inr ⟨a, .loaded χ, by aesop⟩)⟩
    all_goals
      simp at *
      try grind
  · unfold theMoves
    rintro (⟨_, _, p_def, hyp⟩ | ⟨_, _, p_def, hyp⟩ | ⟨_, _, lt, p_def, hyp⟩) <;> subst p_def
    · rcases hyp with ⟨L, R, (⟨X_def, hyp⟩ | _ | _) ⟩
      · subst X_def
        simp
        rcases hyp with ⟨δs, δ, ψ, ψ_noBox, _in_L, next_def⟩
                      | ⟨δs, δ, ψ, ψ_noBox, _in_R, next_def⟩
        · left
          use (~⌈⌈δs⌉⌉⌈δ⌉ψ)
          have := @boxesOf_def_of_def_of_nonBox _ (δs ++ [δ]) ψ rfl ψ_noBox
          rw [boxes_last] at this
          simp_all
          cases δs <;> simp
          grind
        · right
          use (~⌈⌈δs⌉⌉⌈δ⌉ψ)
          have := @boxesOf_def_of_def_of_nonBox _ (δs ++ [δ]) ψ rfl ψ_noBox
          rw [boxes_last] at this
          simp_all
          cases δs <;> simp
          grind
      · grind
      · grind
    · simp
      rcases hyp with ⟨ltab, next_def⟩
      subst next_def
      use ltab
      simp [LocalTableau.fintype.complete]
    · simp
      grind

lemma no_moves_of_rep {Hist X pos} (h : rep Hist X) :
    theMoves ⟨Hist, X, pos⟩ = ∅ := by
  by_contra hyp
  rw [Finset.eq_empty_iff_forall_notMem] at hyp
  push_neg at hyp
  rcases hyp with ⟨p, p_in⟩
  unfold theMoves at p_in
  rcases X with ⟨L,R,_|o⟩ <;> rcases pos with (_|_|_)|(_|_) <;> aesop

/-- The finite set given by `theMoves` indeed agrees with the relation `move`.
(Other direction should hold too, but for now seems to not be needed.) -/
lemma move_of_mem_theMoves :
    next ∈ theMoves p → move p next := by
  rcases p with ⟨Hist, X, pos⟩
  -- FIXME: un-indent
  · intro mv
    unfold theMoves at mv
    rcases pos with (_|_|_) | (_|_) <;> rcases X with ⟨L,R,_|χ⟩ <;> simp_all
    case inl.bas.none =>
      rcases mv with ⟨ψ, ψ_in, next_in⟩ | ⟨ψ, ψ_in, next_in⟩
      · cases ψ -- L
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp [bxs_def, List.mem_cons, List.not_mem_nil, or_false] at next_in
            subst next
            have : ∀ h, φ = ⌈⌈(head :: tail).dropLast⌉⌉⌈(head :: tail).getLast h⌉ψ := by
              simp [def_of_boxesOf_def bxs_def]
              rw [← boxes_last, List.dropLast_append_getLast, Formula.boxes_cons]
            rw [this (by simp)]
            apply move.prPdl
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
            subst this
            exact PdlRule.loadL ψ_in rfl
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
      · cases ψ -- R, analogous
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp [bxs_def, List.mem_cons, List.not_mem_nil, or_false] at next_in
            subst next
            have : ∀ h, φ = ⌈⌈(head :: tail).dropLast⌉⌉⌈(head :: tail).getLast h⌉ψ := by
              simp [def_of_boxesOf_def bxs_def]
              rw [← boxes_last, List.dropLast_append_getLast, Formula.boxes_cons]
            rw [this (by simp)]
            apply move.prPdl
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
            subst this
            exact PdlRule.loadR ψ_in rfl
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
    · -- Here we have a loaded formula in X already, and are basic.
      -- So the only applicable rules are (M) and (L-).
      rcases χ with (⟨⟨χ⟩⟩|⟨⟨χ⟩⟩) <;> rcases χ with ⟨δ,φ|χ⟩ <;> cases δ <;> simp_all
      case inl.bas.some.inl.normal.atom_prog a nrep bas =>
        cases mv <;> subst_eqs
        · apply move.prPdl; apply @PdlRule.freeL _ L R [] (·a) φ _ rfl; simp
        · apply move.prPdl; apply PdlRule.modL rfl rfl
      case inl.bas.some.inl.loaded.atom_prog a nrep bas =>
        cases mv <;> subst_eqs
        · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
          subst χ
          rw [unload_loadMulti]
          apply move.prPdl;
          convert @PdlRule.freeL _ L R (·a :: δ) α φ _ rfl rfl using 1
        · apply move.prPdl; apply PdlRule.modL rfl rfl
      case inl.bas.some.inr.normal.atom_prog a nrep bas =>
        cases mv <;> subst_eqs
        · apply move.prPdl; apply @PdlRule.freeR _ L R [] (·a) φ _ rfl; simp
        · apply move.prPdl; apply PdlRule.modR rfl rfl
      case inl.bas.some.inr.loaded.atom_prog a nrep bas =>
        cases mv <;> subst_eqs
        · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
          subst χ
          rw [unload_loadMulti]
          apply move.prPdl;
          convert @PdlRule.freeR _ L R (·a :: δ) α φ _ rfl rfl using 1
        · apply move.prPdl; apply PdlRule.modR rfl rfl
      all_goals
        grind
    · rcases mv with ⟨lt, lt_in, def_next⟩
      subst def_next
      apply move.prLocTab
    · rcases mv with ⟨lt, lt_in, def_next⟩
      subst def_next
      apply move.prLocTab
    · rcases mv with ⟨lt, lt_in, def_next⟩
      subst def_next
      apply move.buEnd lt_in
    · rcases mv with ⟨lt, lt_in, def_next⟩
      subst def_next
      apply move.buEnd lt_in

lemma move.hist (mov : move ⟨Hist, X, pos⟩ next) :
      (∃ newPos, next = ⟨Hist, X, newPos⟩) -- this is an annoying case ;-)
    ∨ (∃ Y newPos, next = ⟨X :: Hist, Y, newPos⟩)  := by
  cases mov <;> grind

lemma move.hist_suffix (mov : move ⟨Hist, X, pos⟩ next) : Hist <:+ next.1 := by
  have := move.hist mov
  grind

lemma move.trans_hist_suffix (mov : Relation.TransGen move pX pZ) :
    pX.1 <:+ pZ.1 := by
  induction mov
  case single hm => exact move.hist_suffix hm
  case tail steps hm IH =>
    have := move.hist_suffix hm
    apply List.IsSuffix.trans IH this

/-- After two moves we must reach a different sequent.
Is this useful for termination? -/
lemma move_twice_neq {A B C : GamePos} (A_B : move A B) (B_C : move B C) :
    A.2.1 ≠ C.2.1 := by
  rcases A with ⟨HA, A, pA⟩
  rcases B with ⟨HB, B, pB⟩
  rcases C with ⟨HC, C, pC⟩
  simp
  -- have := @no_moves_of_rep -- useful or useless here?
  -- Now that `move` is an inductive we can do `cases B_C` here.
  cases A_B -- <;>
  case prPdl Xbasic nrep r =>
    -- cases B_C -- Dependent elimination failed: Failed to solve equation.
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C
    case prPdl basicB nrepB r' =>
      intro A_C
      subst A_C
      -- ?? PdlRule from A to B but also from B to A --- only possible by loading + freeing
      -- PROBLEM: how do we prevent (L+) right after (L-) and vice versa?
      sorry
    case prLocTab nbasB ltB nrep' =>
      intro A_eq_B
      subst A_eq_B
      exfalso
      tauto
    case buEnd ltB nbasB nrepB C_in =>
      intro A_eq_C
      subst A_eq_C
      -- ??? -- LocalTableau from B to A but also PdlRule form A to B -- should be impossible?
      sorry
  case prLocTab ltA nrep =>
    cases B_C -- must be buEnd :-)
    case buEnd nbas nrep' C_in =>
      have := @endNodesOf_nonbasic_non_eq _ C ltA nbas C_in
      grind
  case buEnd ltA nbas nrep B_in =>
    -- cases B_C -- Dependent elimination failed: Failed to solve equation.
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C
    case prPdl basicB nrepB r =>
      intro A_C
      subst A_C
      -- ??? -- LocalTableau from A to B but also PdlRule form B to A -- should be impossible?
      sorry
    case prLocTab nbasB ltB nrep' =>
      have := @endNodesOf_nonbasic_non_eq _ B ltA nbas B_in
      tauto
    case buEnd ltB nbasB nrepB C_in =>
      exfalso
      have := endNodesOf_basic B_in
      tauto

/-! ## Termination via finite FL closure

Intuitively, we want to say that each step from (L,R,O) in a tableau to (L',R',O') stays in the
FL of (L,R,O). Moreover, each side left/right stays within its own FL closure.
This does *not* mean that `L'` must be in the FL of `L`, because the `O` may also contribute to
the left part. This makes `Sequent.subseteq_FL` tricky to define.

Moreover, we are working with lists (or, by ignoring their order, multisets) and thus staying in
the FL closure does not imply that there are only finitely many sequents reachable: by repeating
the same formulas the length of the list may increase.
To tackle this we want to use that `rep` is defined with `setEqTo` that ignores multiplicity, so
that even if there are infinitely many different lists and thus sequents in principle reachable,
we still cannot have an infinite chain because that would mean we must have a "set-repeat" that
is not allowed.

-/

-- Quick reminder how ≤ and ⊆ work on multisets.
example : ¬ {2,2,1} ≤ ({1,2} : Multiset Nat) := by decide -- cares about multiplicity
example :   {2,2,1} ⊆ ({1,2} : Multiset Nat) := by simp_all -- set-like / only cares about support

/-- `X` is a component-wise *multi*subset of the FL-closure of `Y`.
Implies `Sequent.subseteq_FL` but not vice versa, as infinitely many multisets yield the same set.

BROKEN - does not take into account X.O and Y.O on both sides.
Hopefully we will never need this anyway. Use `Sequent.subseteq_FL` instead. -/
def Sequent.multisubseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
    Multiset.ofList X.R < Multiset.ofList (FLL Y.R)
  ∧ Multiset.ofList X.L < Multiset.ofList (FLL Y.L)

/-- Sequent `Y` is a component-wise subset of the FL-closure of `X`.
Note that by component we mean left and right (and not L, R, O).

WORRY: Is using Sequent.O.L here a problem because it might not be injective?
(Because it calls `unload` where both ⌊a⌋⌊b⌋p and ⌊a⌋⌈b⌉p become ⌈a⌉⌈b⌉p.)
-/
def Sequent.subseteq_FL (X : Sequent) (Y : Sequent) : Prop :=
      X.L   ⊆ FLL (Y.L ++ Y.O.L)
    ∧ X.O.L ⊆ FLL (Y.L ++ Y.O.L)
    ∧ X.R   ⊆ FLL (Y.R ++ Y.O.R)
    ∧ X.O.R ⊆ FLL (Y.R ++ Y.O.R)

@[simp]
lemma Sequent.subseteq_FL_refl (X : Sequent) : X.subseteq_FL X := by
  rcases X with ⟨L,R,O⟩
  simp [Sequent.subseteq_FL, FLL_append_eq]

@[simp]
lemma Sequent.subseteq_FL_trans (X Y Z : Sequent) :
    X.subseteq_FL Y → Y.subseteq_FL Z → X.subseteq_FL Z := by
  intro X_Y Y_Z
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [Sequent.subseteq_FL] at *
  have := @FLL_sub_FLL_iff_sub_FLL
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro φ φ_in
  · have : (L' ++ O'.L) ⊆ FLL (L'' ++ O''.L) := by grind
    grind
  · have : (L' ++ O'.L) ⊆ FLL (L'' ++ O''.L) := by grind
    grind
  · have : (R' ++ O'.R) ⊆ FLL (R'' ++ O''.R) := by grind
    grind
  · have : (R' ++ O'.R) ⊆ FLL (R'' ++ O''.R) := by grind
    grind

lemma Sequent.subseteq_FL_of_setEq_right (h : X.setEqTo Y) {Z : Sequent} :
    Z.subseteq_FL X → Z.subseteq_FL Y := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [setEqTo] at h
  rcases h with ⟨L_same, R_same, O_same⟩
  subst O_same
  rintro ⟨hL, hR, hOL, hOR⟩
  simp at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  all_goals
    rw [FLL_append_eq, List.toFinset.ext_iff] at *
    have := FLL_ext L_same
    have := FLL_ext R_same
    grind

lemma Sequent.subseteq_FL_of_setEq_left {X Y : Sequent} (h : X.setEqTo Y) {Z : Sequent} :
    X.subseteq_FL Z → Y.subseteq_FL Z := by
  rcases X with ⟨L,R,O⟩
  rcases Y with ⟨L',R',O'⟩
  rcases Z with ⟨L'',R'',O''⟩
  simp [setEqTo] at h
  rcases h with ⟨L_same, R_same, O_same⟩
  subst O_same
  rintro ⟨hL, hR, hOL, hOR⟩
  simp at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  all_goals
    rw [FLL_append_eq, List.toFinset.ext_iff] at *
    have := FLL_ext L_same
    have := FLL_ext R_same
    grind

-- TODO: is this the right/useful statement?
lemma unfoldDiamond_in_FL (α : Program) (ψ : Formula) (X : List Formula) :
    X ∈ unfoldDiamond α ψ → ∀ φ ∈ X, φ ∈ FL (⌈α⌉φ) := by
  intro X_in φ φ_in
  rcases unfoldDiamondContent α ψ X X_in φ φ_in with φ_def|h|h
  · simp_all [FL]
  · rcases h with ⟨τ, τ_from_φ, φ_def⟩
    subst φ_def
    cases α <;> simp [FL]
  · rcases h with ⟨a, δ, φ_def⟩
    subst φ_def
    cases α <;> simp [FL]

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL_left {χ ress} (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteq_FL (Y.1, ∅, Y.2.map Sum.inl) (∅, ∅, some (Sum.inl (~'χ))) := by
  simp
  intro F oχ in_ress
  cases lr
  -- Need or already have somwhere a lemma that unfoldDiamond(loaded)' stays in FL closure?
  case dia α χ notAt =>
    simp [Sequent.subseteq_FL]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α χ.unload := by
      have := (unfoldDiamondLoaded_eq α χ)
      grind
    -- hmm
    have := unfoldDiamond_in_FL α χ.unload _ this
    cases oχ <;> simp [pairUnload] at *
    · sorry
    · sorry
  case dia' α φ notAt =>
    simp [Sequent.subseteq_FL]
    have : pairUnload (F, oχ) ∈ unfoldDiamond α φ := by
      have := (unfoldDiamondLoaded'_eq α φ)
      grind
    -- hmm
    have := unfoldDiamond_in_FL α φ _ this
    cases oχ <;> simp [pairUnload] at *
    · sorry
    · sorry

/-- Helper for `LocalRule.stays_in_FL` -/
lemma LoadRule.stays_in_FL_right (lr : LoadRule (~'χ) ress) :
    ∀ Y ∈ ress, Sequent.subseteq_FL (∅, Y.1, Y.2.map Sum.inr) (∅, ∅, some (Sum.inr (~'χ))) := by
  -- TODO, analogous to `LoadRule.stays_in_FL_left`?
  sorry

/-- Helper for `LocalRule.stays_in_FL` -/
theorem OneSidedLocalRule.stays_in_FL
    (rule : OneSidedLocalRule precond ress) :
    ∀ res ∈ ress, res ⊆ FLL precond := by
  intro res res_in
  cases rule <;> simp [FL] at *
  all_goals
    subst_eqs
    try simp
  case nCo φ1 φ2 =>
    -- NOTE: Here it matters that FL is closed under (single) negation.
    cases res_in <;> subst_eqs <;> simp at *
  case box =>
    -- need lemma that `unfoldBox` stays in FL here?
    sorry
  case dia =>
    -- finish `LoadRule.stays_in_FL_left` before this here.
    sorry

/-- Helper for `LocalTableau.stays_in_FL` -/
theorem LocalRule.stays_in_FL {X B}
    (rule : LocalRule X B) :
    ∀ Y ∈ B, Y.subseteq_FL X := by
  intro Y Y_in_B
  cases rule
  case oneSidedL precond ress orule B_def =>
    subst B_def
    simp at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp [Sequent.subseteq_FL]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case oneSidedR precond ress orule B_def =>
    subst B_def
    simp at *
    rcases Y_in_B with ⟨res, res_in, def_Y⟩
    subst def_Y
    simp [Sequent.subseteq_FL]
    apply OneSidedLocalRule.stays_in_FL orule _ res_in
  case LRnegL =>
    absurd Y_in_B
    tauto
  case LRnegR =>
    absurd Y_in_B
    tauto
  case loadedL ress χ lorule B_def =>
    subst B_def
    simp [List.empty_eq, List.mem_map, Prod.exists] at *
    rcases Y_in_B with ⟨l, o, in_ress, def_Y⟩
    have := LoadRule.stays_in_FL_left lorule (l, o) in_ress
    simp_all
  case loadedR ress χ lorule B_def =>
    subst B_def
    simp only [List.empty_eq, List.mem_map, Prod.exists] at *
    rcases Y_in_B with ⟨l, o, in_ress, def_Y⟩
    have := LoadRule.stays_in_FL_right lorule (l, o) in_ress
    simp_all

/-- LocalTableau helper for `move_inside_FL` -/
theorem LocalTableau.stays_in_FL {X}
    (ltX : LocalTableau X) :
    ∀ Y ∈ endNodesOf ltX, Y.subseteq_FL X := by
  intro Y Y_in_B
  cases ltX
  case byLocalRule B next lra =>
    have _forTermination := localRuleApp.decreases_DM lra
    rcases lra with @⟨L, R, _, ress, O, Lcond, Rcond, Ocond, lr, B_def, ⟨Lconp,Rconp,Oconp⟩⟩
    subst B_def
    have lr_lemma := LocalRule.stays_in_FL lr
    simp [endNodesOf] at Y_in_B
    rcases Y_in_B with ⟨l, ⟨W, W_in, def_l⟩ , Y_in⟩
    subst def_l
    rcases W_in with ⟨re, re_in_ress, def_W⟩
    have IH := LocalTableau.stays_in_FL _ Y Y_in
    clear _forTermination -- to avoid simplifying it
    subst def_W
    specialize lr_lemma re re_in_ress
    rcases re with ⟨Lnew, Rnew, Onew⟩
    simp at *
    clear Y_in next
    simp [Sequent.subseteq_FL, FLL_append_eq] at IH lr_lemma ⊢
    obtain ⟨IHL, IHLO, IHR, IHRO⟩ := IH
    obtain ⟨lemL, lemLO, lemR, lemRO⟩ := lr_lemma
    refine ⟨?_, ?_ , ?_ , ?_⟩ <;> intro x x_in
    · specialize IHL x_in
      simp at *
      rcases IHL with h|h|h
      · left
        have := @FLL_diff_sub L Lcond
        grind
      · have := FLL_sub lemL h
        simp [FLL_append_eq] at this
        rcases this with in_Lcond|inOcondL
        · left
          apply @FLL_sub Lcond L (List.Subperm.subset Lconp) _ in_Lcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · left
          apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · rcases lemLO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Lconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
    · specialize IHLO x_in
      simp at *
      rcases IHLO with h|h|h
      · left
        have := @FLL_diff_sub L Lcond
        grind
      · have := FLL_sub lemL h
        simp [FLL_append_eq] at this
        rcases this with in_Lcond|inOcondR
        · left
          apply @FLL_sub Lcond L (List.Subperm.subset Lconp) _ in_Lcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemLO h
        · left
          apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
        · rcases lemLO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Lconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
        · apply FLL_sub (List.Subperm.subset Lconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemLO h
    · specialize IHR x_in
      simp at *
      rcases IHR with h|h|h
      · left
        have := @FLL_diff_sub R Rcond
        grind
      · have := FLL_sub lemR h
        simp [FLL_append_eq] at this
        rcases this with in_Rcond|inOcondR
        · left
          apply @FLL_sub Rcond R (List.Subperm.subset Rconp) _ in_Rcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · left
          apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · rcases lemRO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Rconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
    · specialize IHRO x_in
      simp at *
      rcases IHRO with h|h|h
      · left
        have := @FLL_diff_sub R Rcond
        grind
      · have := FLL_sub lemR h
        simp [FLL_append_eq] at this
        rcases this with in_Rcond|inOcondR
        · left
          apply @FLL_sub Rcond R (List.Subperm.subset Rconp) _ in_Rcond
        · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> simp_all
      · cases Ocond <;> rcases O with _|⟨χ|χ⟩ <;> rcases Onew with _|⟨χnew|χnew⟩ <;> simp_all
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          apply List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · left
          apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · apply FLL_sub (List.Subperm.subset Rconp)
          rw [← FLL_idem_ext]
          exact List.mem_flatMap_of_mem lemRO h
        · rcases lemRO with lemH|lemH
          · left
            apply FLL_sub (List.Subperm.subset Rconp)
            rw [← FLL_idem_ext]
            exact List.mem_flatMap_of_mem lemH h
          · right
            exact FL_trans lemH h
  case sim => simp_all [endNodesOf]
termination_by
  X
decreasing_by
  simp_wf
  subst_eqs
  simp at *
  apply _forTermination re re_in_ress

lemma projection_sub_FLL {a L} : projection a L ⊆ FLL L := by
  intro φ φ_in
  rw [proj] at φ_in
  simp only [FLL, List.mem_flatMap]
  use ⌈·a⌉φ, φ_in
  simp [FL]

/-- PdlRule helper for `move_inside_FL` -/
theorem PdlRule.stays_in_FL {X Y} (rule : PdlRule X Y) :
    Y.subseteq_FL X := by
  cases rule
  case loadL L δ α φ R in_L Y_def =>
    subst Y_def
    simp [Sequent.subseteq_FL]
    constructor
    · exact List.Subset.trans List.erase_subset FLL_refl_sub
    · exact FLL_refl_sub in_L
  case loadR L δ α φ R in_L Y_def =>
    subst Y_def
    simp [Sequent.subseteq_FL]
    constructor
    · exact List.Subset.trans List.erase_subset FLL_refl_sub
    · exact FLL_refl_sub in_L
  case freeL L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteq_FL]
    intro x x_in
    simp at x_in
    apply FLL_refl_sub
    simp
    tauto
  case freeR L R δ α φ X_def Y_def =>
    subst X_def
    subst Y_def
    simp [Sequent.subseteq_FL]
    intro x x_in
    simp at x_in
    apply FLL_refl_sub
    simp
    tauto
  case modL L R a ξ X_def Y_def =>
    subst X_def
    subst Y_def
    cases ξ <;> simp [Sequent.subseteq_FL]
    case normal φ =>
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · have := @projection_sub_FLL a L
        grind [FLL_append_eq]
      · apply projection_sub_FLL
    case loaded χ =>
      refine ⟨?_, ?_, ?_⟩
      · have := @projection_sub_FLL a L
        grind [FLL_append_eq]
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · apply projection_sub_FLL
  case modR L R a ξ X_def Y_def => -- analogous to `modL` case
    subst X_def
    subst Y_def
    cases ξ <;> simp [Sequent.subseteq_FL]
    case normal φ =>
      refine ⟨?_, ?_, ?_⟩
      · apply @projection_sub_FLL a L
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]
      · have := @projection_sub_FLL a R
        grind [FLL_append_eq]
    case loaded χ =>
      refine ⟨?_, ?_, ?_⟩
      · apply projection_sub_FLL
      · have := @projection_sub_FLL a R
        grind [FLL_append_eq]
      · simp [FLL_append_eq]
        right
        -- Note: here the closure under single negation matters.
        simp [FL, FLb]

lemma move_inside_FL (mov : move p next) : next.2.1.subseteq_FL p.2.1 := by
  cases mov
  case prPdl r => apply PdlRule.stays_in_FL r
  case buEnd ltX _ _ _ _ Y_in => simp; apply LocalTableau.stays_in_FL ltX _ Y_in
  case prLocTab => simp

/-- A list of sequents that are all FL-subsequents of the given sequent.
The list defined here is not complete because there are infinitely many such other sequents.
But the list is exhaustive modulo `setEqTo`, as will be shown later via the `Seqt` quotient.
Defined using `List.instMonad`.
-/
def Sequent.all_subseteq_FL (Y : Sequent) : List { X : Sequent // Sequent.subseteq_FL X Y } := do
  -- QUESTION: any way to do sublist and permutation in one go?
  -- Never mind, removed `.flatMap List.permutations` again which really should not be needed.
  -- Trying out different orders `.sublists.attach` and `.attach.sublists` here.
  let XL  ← (FLL (Y.L ++ Y.O.L)).sublists.attach
  let XOL ← (FLL (Y.L ++ Y.O.L)).sublists.attach
  let XR  ← (FLL (Y.R ++ Y.O.R)).sublists.attach
  let XOR ← (FLL (Y.R ++ Y.O.R)).sublists.attach
  -- TODO: We need to generate all possible `XO : Olf` from `XOL` and `XOR` here.
  let X : Sequent := ⟨XL.1, XR.1, none⟩
  have h : X.subseteq_FL Y := by
    unfold X
    rcases Y with ⟨L',R',O'⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp
    · have := XL.2
      simp at this
      exact List.Sublist.subset this
    · have := XR.2
      simp at this
      exact List.Sublist.subset this
    -- · sorry -- TODO for O later
  return ⟨X, h⟩

/-! NOTE

The following do NOT hold / do NOT exist because there are in fact infinitely many FL-subsequents
of a given sequent, so the list returned by `all_subseteq_FL` can never contain all.

```
def Sequent.all_subseteq_FL_complete (X Y : Sequent) (h : Y.subseteq_FL X) :
    ⟨Y,h⟩ ∈ Sequent.all_subseteq_FL X := sorry

instance Sequent.subseteq_FL_fintype {X : Sequent} :
    Fintype { Y // Sequent.subseteq_FL Y X } := sorry
```

Hence, we now define the Quotient modulo `Sequent.setEqTo` within which there are only finitely
many FL-subsequents.

TODO move `Seqt` to Sequent.lean and `Sequent.subseteq_FL_congr` to FischerLadner.lean later?
-/

instance instEquivalenceSequentSetEqTo : Equivalence Sequent.setEqTo where
  refl := by rintro ⟨L,R,O⟩; simp [Sequent.setEqTo]
  symm := by rintro ⟨L,R,O⟩ ⟨L',R',O'⟩; simp [Sequent.setEqTo]; grind
  trans := by rintro ⟨L,R,O⟩ ⟨L',R',O'⟩ ⟨L'',R'',O''⟩; simp [Sequent.setEqTo]; grind

instance instSetoidSequent : Setoid Sequent := ⟨Sequent.setEqTo, instEquivalenceSequentSetEqTo⟩

/-- Yes, it's a pun. A `Sequent` modulo `Sequent.setEqTo`. -/
abbrev Seqt := Quotient instSetoidSequent

/-- Needed to make `List.toFinset` work for `List Seqt`.
Strange that this is not inferred from `instDecidableRelSequentSetEqTo` automatically. -/
instance instDecidableEqSeqt : DecidableEq Seqt := by
  have := instDecidableRelSequentSetEqTo
  apply Quotient.decidableEq

/-- Congruence for `Sequent.subseteq_FL`, used to make `Seqt.subseteq_FL` well-defined. -/
lemma Sequent.subseteq_FL_congr (a₁ b₁ a₂ b₂ : Sequent) :
    a₁ ≈ a₂ → b₁ ≈ b₂ → (a₁.subseteq_FL b₁ = a₂.subseteq_FL b₂) := by
  rintro ⟨a_L, a_R, a_O⟩ ⟨b_L, b_R, b_O⟩
  rw [eq_iff_iff]
  rcases a₁ with ⟨La1,Ra1,Oa1⟩
  rcases a₂ with ⟨La2,Ra2,Oa2⟩
  rcases b₁ with ⟨Lb1,Rb1,Ob1⟩
  rcases b₂ with ⟨Lb2,Rb2,Ob2⟩
  rw [List.toFinset.ext_iff] at a_L a_R b_L b_R
  subst a_O b_O
  unfold subseteq_FL
  simp only [Sequent.L, Sequent.O, Sequent.R]
  constructor <;> rintro ⟨hL,hOL,hR,hOR⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro φ φ_in
    rw [FLL_append_eq, List.mem_append]
    simp only at *
  · rw [← a_L] at φ_in
    specialize hL φ_in
    rw [FLL_append_eq, List.mem_append] at hL
    have := FLL_ext b_L φ
    aesop
  · specialize hOL φ_in
    rw [FLL_append_eq, List.mem_append] at hOL
    have := FLL_ext b_L φ
    tauto
  · rw [← a_R] at φ_in
    specialize hR φ_in
    rw [FLL_append_eq, List.mem_append] at hR
    have := FLL_ext b_R φ
    tauto
  · specialize hOR φ_in
    rw [FLL_append_eq, List.mem_append] at hOR
    have := FLL_ext b_R φ
    tauto
  · rw [a_L] at φ_in
    specialize hL φ_in
    rw [FLL_append_eq, List.mem_append] at hL
    have := FLL_ext b_L φ
    tauto
  · specialize hOL φ_in
    rw [FLL_append_eq, List.mem_append] at hOL
    have := FLL_ext b_L φ
    tauto
  · rw [a_R] at φ_in
    specialize hR φ_in
    rw [FLL_append_eq, List.mem_append] at hR
    have := FLL_ext b_R φ
    tauto
  · specialize hOR φ_in
    rw [FLL_append_eq, List.mem_append] at hOR
    have := FLL_ext b_R φ
    tauto

def Seqt.subseteq_FL (X : Seqt) (Y : Seqt) : Prop :=
  Quotient.lift₂ Sequent.subseteq_FL Sequent.subseteq_FL_congr X Y

/-- In the quotient the moves keep us inside the FL. UNUSED, delete this? -/
lemma Seqt.subseteq_FL_of_move (hm : move p next) :
    Seqt.subseteq_FL (Quotient.mk' next.2.1) (Quotient.mk' p.2.1) := by
  unfold Seqt.subseteq_FL
  exact move_inside_FL hm

def Sequent.allSeqt_subseteq_FL (X : Sequent) : Finset Seqt :=
  (X.all_subseteq_FL.map (fun x => ⟦x.1⟧)).toFinset

lemma Sequent.allSeqt_subseteq_FL_spec (X : Sequent) :
    ∀ Y, ⟦Y⟧ ∈ X.allSeqt_subseteq_FL → Y.subseteq_FL X := by
  intro Y Ys_in
  simp [Sequent.allSeqt_subseteq_FL, instSetoidSequent] at *
  rcases Ys_in with ⟨Z, ⟨Z_sub_X, Z_in_all⟩, Z_equiv_Y⟩
  exact Sequent.subseteq_FL_of_setEq_left Z_equiv_Y Z_sub_X

lemma Sequent.allSeqt_subseteq_FL_complete (X : Sequent) :
    ∀ Y, Y.subseteq_FL X → ⟦Y⟧ ∈ X.allSeqt_subseteq_FL := by
  intro Y Y_in
  simp [Sequent.allSeqt_subseteq_FL, instSetoidSequent]
  -- Here the above NOTE matters.
  -- We need to work around that there is no `Sequent.all_subseteq_FL_complete`.
  -- use Y -- this might not work because `Y` might not be in `all_subseteq_FL`.
  -- How to find a sequent that is an element of `all_subseteq_FL` ???
  sorry

lemma Sequent.allSeqt_subseteq_FL_congr (X Y : Sequent) (h : X ≈ Y) :
    Sequent.allSeqt_subseteq_FL X = Sequent.allSeqt_subseteq_FL Y := by
  ext Ys
  simp only [allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset, List.mem_map,
    List.mem_unattach]
  simp [instHasEquivOfSetoid, instSetoidSequent] at h
  constructor
  · rintro ⟨Z, ⟨Z_sub_X, Z_in_sub_X⟩, def_YS⟩
    have Z_sub_Y := (Sequent.subseteq_FL_congr Z X Z Y (Setoid.refl _) h).mp Z_sub_X
    have := Y.allSeqt_subseteq_FL_complete Z Z_sub_Y
    simp only [allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset, List.mem_map,
      List.mem_unattach, Quotient.eq] at this
    aesop
  · rintro ⟨Z, ⟨Z_sub_Y, Z_in_sub_Y⟩, def_YS⟩
    have Z_sub_Y := (Sequent.subseteq_FL_congr Z Y Z X (Setoid.refl _) (Setoid.symm h)).mp Z_sub_Y
    have := X.allSeqt_subseteq_FL_complete Z Z_sub_Y
    simp only [allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset, List.mem_map,
      List.mem_unattach, Quotient.eq] at this
    aesop

def Seqt.all_subseteq_FL (Xs : Seqt) : Finset Seqt  :=
  Quotient.lift Sequent.allSeqt_subseteq_FL Sequent.allSeqt_subseteq_FL_congr Xs

lemma Seqt.all_subseteq_FL_spec {Ys : Seqt} (Ys_in : Ys ∈ Xs.all_subseteq_FL) :
    Ys.subseteq_FL Xs := by
  sorry

lemma Seqt.all_subseteq_FL_complete {Ys : Seqt} (Ys_in : Ys.subseteq_FL Xs) :
    Ys ∈ Xs.all_subseteq_FL := by
  sorry

def Seqt.all_subseteq_FL_attached (Xs : Seqt) : Finset { Ys :Seqt // Ys.subseteq_FL Xs } :=
  Xs.all_subseteq_FL.attach.map
    ⟨fun ⟨Ys,Ys_in⟩ => ⟨Ys, Seqt.all_subseteq_FL_spec Ys_in⟩, by rintro ⟨Ys1,_⟩ ⟨Ys2,_⟩ h; aesop⟩

def Seqt.all_subseteq_FL_attached_complete (Xs : Seqt) :
    ∀ (x : { Ys : Seqt // Ys.subseteq_FL Xs }), x ∈ Xs.all_subseteq_FL_attached := by
  rintro ⟨Ys,Ys_in⟩
  simp only [all_subseteq_FL_attached, Finset.mem_map, Finset.mem_attach,
    Function.Embedding.coeFn_mk, Subtype.mk.injEq, true_and, Subtype.exists, exists_prop,
    exists_eq_right]
  apply Seqt.all_subseteq_FL_complete Ys_in

instance Seqt.subseteq_FL_instFintype {Xs : Seqt} : Fintype { Ys // Seqt.subseteq_FL Ys Xs } :=
  ⟨ Xs.all_subseteq_FL_attached, Xs.all_subseteq_FL_attached_complete ⟩

/-- In the quotient for `setEqTo` there are only finitely many FL-subsets for a given Seqt.
This means "there are only finitely many "sequents modulo `setEq`" that are subseteq_FL Y. -/
lemma Seqt.subseteq_FL_finite {Xs : Seqt} : Finite { Ys // Seqt.subseteq_FL Ys Xs } :=
  @Finite.of_fintype { Ys // Seqt.subseteq_FL Ys Xs } Seqt.subseteq_FL_instFintype

/-- General helper lemma: If we have an enumeration of infinitely many values, and all of them
have a certain property, but we also know that there are only finitely many values with that
property, then there must be identical values in the enuemration. -/
lemma help {α : Type} {f : ℕ → α} {p : α → Prop}
    (h_p : ∀ n, p (f n)) (h_fin : Finite {x // p x})
    : ∃ k1 k2, k1 ≠ k2 ∧ f k1 = f k2 := by
  -- Because {x // p x} is finite, also Set.range f is finite.
  have range_finite : Finite (Set.range f) := by
    apply Set.Finite.subset h_fin
    intro x ⟨n, def_x⟩
    convert h_p n
    rw [def_x]
  -- ℕ is infinite, so f cannot be injective
  have not_injective : ¬Function.Injective f := by
    intro hinj
    -- If f were injective, then Set.range f would be infinite (bijective with ℕ)
    have : Infinite (Set.range f) := by
      rw [@Set.infinite_coe_iff]
      have := Infinite.of_injective f hinj
      exact Set.infinite_range_of_injective hinj
    exact this.not_finite range_finite
  -- Non-injective means there exist distinct inputs with same output
  rw [Function.Injective] at not_injective
  push_neg at not_injective
  tauto

/-- Lemma 6.10, sort of. Because the move relation is wellfounded, all matches must be finite.
Note that the paper does not prove this, only says it is similar to the proof that PDL-tableaux
are finite, i.e. Lemma 4.10 which uses the Fischer-Ladner closure. -/
lemma move.converse_wf : WellFounded (Function.swap move) := by
  -- If it's not wellfounded, then there must be an infinite sequence of moves.
  rw [wellFounded_iff_isEmpty_descending_chain]
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

  -- Elements along the chain are related by the transitive closure of `move.swap`.
  have trans_rel : ∀ k1 k2, k1 < k2 → Relation.TransGen (Function.swap move) (f k2) (f k1) := by
    intro k1 k2 k_lt
    rw [lt_iff_exists_add] at k_lt
    rcases k_lt with ⟨m, m_pos, k2_def⟩; subst k2_def
    induction m
    · exfalso; cases m_pos
    case succ m IH =>
      cases m
      · exact Relation.TransGen.single (f_rel k1)
      case succ m =>
        simp at IH
        exact Relation.TransGen.head (f_rel (k1 + m + 1)) IH

  -- IDEA from here onwards: the Hist and X stays inside FL, but must be different / no repeats.
  -- Well, almost all X must be different. Single steps that keep `Hist` and `X` are sometimes
  -- allowed, in the annyong case in `move.hist`. Still, we can never repeat an `X` in `Hist`.
  have no_repeats : ∀ n, ¬ rep (f n).1 (f n).2.1 := fun k => move_then_no_rep (f_rel k)

  -- The histories along the chain extend each other.
  have hist_suffixes : ∀ k1 k2, k1 < k2 → (f k1).1 <:+ (f k2).1 := by
    intro k1 k2 k_lt
    specialize trans_rel k1 k2 k_lt
    exact @move.trans_hist_suffix _ _ (Relation.TransGen.swap trans_rel)

  -- There are only finitely many setEqTo-different sequents in the FL closure of the chain start.
  have FL_fin := @Seqt.subseteq_FL_finite (Quotient.mk' (f 0).2.1)

  -- Now we apply the general helper lemma from above. A tricky thing here is that we want to
  -- go from "only finitely many sequents" to "finitely many GamePos" values.
  have := @help _ (fun n => ⟦(f n).2.1⟧) (fun Xs => Seqt.subseteq_FL Xs ⟦(f 0).2.1⟧) ?_ FL_fin
  · rcases this with ⟨k1, k2, k_diff, same⟩
    simp [rep, instSetoidSequent] at same no_repeats
    rw [Nat.ne_iff_lt_or_gt] at k_diff
    absurd same
    rcases k_diff with k1_lt_k2 | k2_lt_k1
    · -- k1 < k2 case
      -- here use the history extension
      apply no_repeats k2 (f k1).2.1

      -- Remains to show that `f k1` is in the history of `f k2`.
      -- We have that the k2 history extends the k1 history,
      specialize hist_suffixes k1 k2 k1_lt_k2
      -- but also need that history *actually grows* at some point.
      -- Make lemma for this?
      -- Can we use `move_twice_neq` here?
      -- How do we know that k2 - k1 is at least 2 and not 1 ???

      sorry

    · -- analogous case for k2 < k1
      rw [Sequent.setEqTo_symm]
      apply no_repeats k1 (f k2).2.1

      sorry
  · intro n
    specialize all_moves_inside n
    simp [Seqt.subseteq_FL]
    assumption

-- and THEN argue that same in quotient means we have no `move` successor before quotienting?!

  /- OLD IDEA for `move.wf`
  apply `wf_of_finTransInvImage_of_transIrrefl` - no longer needed at all now?
  · -- To show: only finitely many moves are reachable
    -- Use `move_inside_flc` for this.
    sorry
  · -- To show: (TransGen move) is irreflexive, i.e. no repeats.
    -- Use `no_moves_of_rep` here maybe?
    sorry
  -/

/-! ## Actual Game Definition -/

/-- The game defined in Section 6.2. -/
def tableauGame : Game where
  Pos := GamePos
  turn | ⟨_, _, .inl _⟩ => Prover
       | ⟨_, _, .inr _⟩ => Builder
  moves := theMoves
  wf := ⟨fun x y => move y x, move.converse_wf⟩
  move_rel := by grind [move_of_mem_theMoves]

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
      have next' : ∀ Y (Y_in : Y ∈ endNodesOf ltX), Nonempty (Tableau (X :: Hist) Y) := by
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

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- Tree data type to keep track of choices made by Builder. Might still need to be tweaked.
TODO: choices should be labelled with the choices made by prover??
-/
inductive BuildTree : Sequent → Type
  | Leaf {X} : BuildTree X
  | Step {X} : List (Σ Y, BuildTree Y) → BuildTree X

/-- The generated strategy tree for Builder -/
def buildTree (s : Strategy tableauGame Builder) {H X} p (h : winning s ⟨H, X, p⟩) : BuildTree X :=
  match p with
  -- Prover positions:
  | Sum.inl (.nlpRep _) => .Leaf -- Builder wins :-)
  | Sum.inl (.bas nrep bas) => sorry -- prover must apply PDL rule
  | Sum.inl (.nbas nrep nbas) => -- prover must choose local rule / a whole local tableau
      -- Note: not using the Fintype instance because we want a List, not Finset
      let prMoves := (LocalTableau.all X).map
        (fun ltab => (⟨H, X, .inr (.ltab nrep nbas ltab)⟩ : GamePos))
      have stillWin : ∀ newPos ∈ prMoves, winning s newPos := by sorry
      .Step <|
      prMoves.attach.map <| fun pos => ⟨_, buildTree s p (stillWin _ sorry)⟩ -- p ≠ pos MISMATCH ?!
  -- Builder positions:
  | Sum.inr (.lpr _) => by exfalso; simp [winning] at h -- prover wins, cannot happen
  | Sum.inr (.ltab nrep nbas ltX) =>
      if ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty
      then
        -- use `s` to choose `Y ∈ endNodeOf ltX`
        let Y := (s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne)
        have new_h : winning s Y.1 := winning_of_winning_move _ h
        have forTermination : move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ Y.1 := by
          have := Y.2
          simp only [Game.Pos.moves, Game.moves, tableauGame, theMoves] at this
          simp [-Finset.coe_mem] at this
          have := fun Y => @move.buEnd X ltX Y H nrep nbas
          grind
        .Step [ ⟨_, buildTree s _ new_h⟩ ]
      else by
        exfalso
        unfold winning winner at h
        simp_all
termination_by
  tableauGame.wf.2.wrap (⟨H, X, p⟩ : GamePos)
decreasing_by
  · simp_wf
    simp [WellFoundedRelation.rel, Game.wf, tableauGame]
    -- show that it's a move
    sorry
  · simp_wf
    simp [WellFoundedRelation.rel, Game.wf, tableauGame]
    -- show that it's a move
    exact forTermination

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
