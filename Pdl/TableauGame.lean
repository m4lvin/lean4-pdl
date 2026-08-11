import Pdl.Game
import Pdl.AllLocalTab
import Pdl.Modelgraphs
import Pdl.StayingInFL

/-! # The Tableau Game (Section 6.2) -/

/-! ## Prover and Builder positions -/

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

/-- Prover should make a move. -/
inductive ProverPos (H : History) (X : Sequent) : Type where
  | frep : (rep H X ∧ X.isFree) → ProverPos H X -- Prover loses at free repeats.
  | bas : ¬ flprep H X → X.basic → ProverPos H X -- Prover must apply a PDL rule
  | nbas : ¬ flprep H X → ¬ X.basic → ProverPos H X -- Prover must make a local LocalTableau
  deriving DecidableEq

/-- Builder should make a move. -/
inductive BuilderPos (H : History) (X : Sequent) : Type where
  | lpr : LoadedPathRepeat H X → BuilderPos H X -- no moves, Prover wins.
  | ltab : ¬ flprep H X → ¬ X.basic → LocalTableau X → BuilderPos H X -- Builder picks endNodesOf
  deriving DecidableEq

/-- Game position where either Prover (`isLeft`) or Builder (`isRight`) should make a move. -/
def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
  deriving DecidableEq

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if h_neNlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.lpr (.choice h_neNlp)) -- BuilderPos with no moves to let Prover win at lpr
  else
    if h_frep : rep H X ∧ X.isFree
    then .inl (.frep h_frep) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas (by grind) bas) -- actual ProverPos to choose a PDL rule
      else .inl (.nbas (by grind) bas) -- actual ProverPos to make LocalTab

lemma posOf_eq_inr_then_lpr {H X p} :
    posOf H X = Sum.inr p → ∃ lpr, p = .lpr lpr := by
  unfold posOf
  grind

/-! ## Moves -/

/-- The relation `Move old next` says that we can move from `old` to `next`.
There are three kinds of moves. -/
inductive Move : (old : GamePos) → (new : GamePos) → Type
/-- When the sequent is basic and no repeat, let prover apply a PDL rule. -/
| prPdl {X Y Hist nrep Xbasic} : PdlRule X Y →
    Move ⟨Hist, X, .inl (.bas nrep Xbasic)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩
/-- If not basic, let prover pick any `ltab : LocalTableau X` as new position. -/
| prLocTab {Hist X nrep nbas ltab} :
    Move ⟨Hist, X, .inl (.nbas nrep nbas)⟩
         ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩
/-- Let Builder pick an end node of `ltab` -/
| buEnd {X ltab Y Hist nrep nbas} : Y ∈ endNodesOf (ltab : LocalTableau X) →
    Move ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩

def Move.isModal {pos newPos : GamePos} : Move pos newPos → Prop
| .prPdl r => r.isModal
| .prLocTab => False
| .buEnd _ => False

def move (old : GamePos) (new : GamePos) : Prop := Nonempty (Move old new)

lemma move_then_no_frep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ (rep H X ∧ X.isFree) := by
  simp only [move, Nonempty.forall]
  intro next_p hyp
  cases next_p <;> grind

/-- The finite set of moves, given as a function instead of a relation.
With `move_of_mem_theMoves` and `mem_theMoves_of_move` this agrees with `move`. -/
@[simp]
def theMoves : GamePos → Finset GamePos
  -- ProverPos:
  | ⟨H, X, .inl (.frep _)⟩ => ∅ -- no moves ⇒ Builder wins
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
      rcases mv with ⟨ψ, ψ_in, next_in⟩ | ⟨ψ, ψ_in, next_in⟩
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

attribute [local simp] flprep in
lemma no_moves_of_rep {H X pos} (h : rep H X ∧ X.isFree) :
    theMoves ⟨H, X, pos⟩ = ∅ := by
  by_contra hyp
  rw [Finset.eq_empty_iff_forall_notMem] at hyp
  push_neg at hyp
  rcases hyp with ⟨p, p_in⟩
  unfold theMoves at p_in
  rcases X with ⟨L,R,_|o⟩ <;> rcases pos with (_|_|_)|(_|_) <;> aesop

/-- The finite set given by `theMoves` indeed agrees with the relation `move`.
Other direction is `mem_theMoves_of_move`. -/
lemma move_of_mem_theMoves {pos next} :
    next ∈ theMoves pos → move pos next := by
  rcases pos with ⟨Hist, X, p⟩
  intro mv
  unfold theMoves at mv
  rcases p with (_|_|_) | (_|_) <;> rcases X with ⟨L,R,_|χ⟩ <;> simp_all
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
          simp only [move]
          constructor
          apply Move.prPdl
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
          subst this
          exact PdlRule.loadL ψ_in ψ_nonBox rfl
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
          simp only [move]
          constructor
          apply Move.prPdl
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
          subst this
          exact PdlRule.loadR ψ_in ψ_nonBox rfl
        · exfalso
          cases φ <;> simp_all [boxesOf]
      all_goals
        exfalso; simp at *
  · -- Here we have a loaded formula in X already, and are basic.
    -- So the only applicable rules are (M) and (L-).
    rcases χ with (⟨⟨χ⟩⟩|⟨⟨χ⟩⟩) <;> rcases χ with ⟨δ,φ|χ⟩ <;> cases δ <;> simp_all
    case inl.bas.some.inl.normal.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · constructor; apply Move.prPdl; apply @PdlRule.freeL _ L R [] (·a) φ _ rfl; simp
      · constructor; apply Move.prPdl; apply PdlRule.modL rfl rfl
    case inl.bas.some.inl.loaded.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
        subst χ
        rw [unload_loadMulti]
        constructor; apply Move.prPdl;
        convert @PdlRule.freeL _ L R (·a :: δ) α φ _ rfl rfl using 1
      · constructor; apply Move.prPdl (PdlRule.modL rfl rfl)
    case inl.bas.some.inr.normal.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · constructor; apply Move.prPdl; apply @PdlRule.freeR _ L R [] (·a) φ _ rfl; simp
      · constructor; apply Move.prPdl (PdlRule.modR rfl rfl)
    case inl.bas.some.inr.loaded.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
        subst χ
        rw [unload_loadMulti]
        constructor; apply Move.prPdl;
        convert @PdlRule.freeR _ L R (·a :: δ) α φ _ rfl rfl using 1
      · constructor; apply Move.prPdl; apply PdlRule.modR rfl rfl
    all_goals
      grind
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.prLocTab
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.prLocTab
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.buEnd lt_in
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.buEnd lt_in

lemma mem_theMoves_of_move {pos next} :
    move pos next → next ∈ theMoves pos := by
  intro mov
  rcases pos with ⟨H, X, p⟩
  rw [theMoves_iff]
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl Y bas r nrep =>
    simp_all only [true_and, exists_const, not_false_eq_true, Sum.inl.injEq, reduceCtorEq,
      false_and, not_true_eq_false, IsEmpty.exists_iff, exists_false, or_self, or_false]
    use X.1, X.2.1
    rcases X with ⟨L,R,_|χ⟩ <;> cases r <;> try subst_eqs
    case none.loadL δs δ ψ notBox in_L =>
      simp_all only [true_and]
      left; left
      use δs, δ, ψ
    case none.loadR δs δ ψ notBox in_L =>
      simp_all only [true_and]
      left; right
      use δs, δ, ψ
    case some.freeL δs δ ψ  =>
      simp_all only
      right
      left -- L
      cases δs
      · simp_all only [LoadFormula.boxes_nil]
        cases δ
        case atom_prog a =>
          use a, AnyFormula.normal ψ
          simp only [AnyFormula.normal.injEq, exists_eq_left', reduceCtorEq, false_and,
            exists_false, LoadFormula.unload, false_or, true_and]
          aesop
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Option.map_some, Sum.elim_inl, negUnload, LoadFormula.unload,
            Option.toList_some, List.append_assoc, List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false, Formula.basic, decide_false, decide_true] at bas
          specialize bas _ (Or.inr (Or.inr rfl))
          simp at bas
      case cons α δs =>
        cases α
        case atom_prog a =>
          use a
          use ⌊⌊δs⌋⌋⌊δ⌋AnyFormula.normal ψ
          simp only [LoadFormula.boxes_cons, reduceCtorEq, false_and, exists_const,
            AnyFormula.loaded.injEq, exists_eq_left', LoadFormula.unload, false_or, true_and]
          right
          convert rfl using 5
          simp
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Option.map_some, Sum.elim_inl, negUnload, unload_boxes, LoadFormula.unload,
            Formula.boxes_cons, Option.toList_some, List.append_assoc, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, Formula.basic, decide_false,
            decide_true] at bas
          specialize bas _ (Or.inr (Or.inr rfl))
          simp at bas
    case some.freeR δs δ ψ =>
      right
      right -- R, this is the only change here!
      cases δs
      · simp_all only [LoadFormula.boxes_nil]
        cases δ
        case atom_prog a =>
          use a, AnyFormula.normal ψ
          simp only [AnyFormula.normal.injEq, exists_eq_left', reduceCtorEq, false_and,
            exists_false, LoadFormula.unload, false_or, true_and]
          aesop
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Option.map_some, Sum.elim_inr, negUnload, LoadFormula.unload,
            Option.toList_some, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false, Formula.basic, decide_false, decide_true] at bas
          specialize bas _ (Or.inr (Or.inr rfl))
          simp at bas
      case cons α δs =>
        cases α
        case atom_prog a =>
          use a
          use ⌊⌊δs⌋⌋⌊δ⌋AnyFormula.normal ψ
          simp only [LoadFormula.boxes_cons, reduceCtorEq, false_and, exists_const,
            AnyFormula.loaded.injEq, exists_eq_left', LoadFormula.unload, false_or, true_and]
          right
          convert rfl using 5
          simp
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Option.map_some, Option.toList_some, List.append_assoc, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, Formula.basic, decide_false,
            decide_true] at bas
          specialize bas _ (Or.inr (Or.inr rfl))
          simp at bas
    case some.modL a ξ =>
      right
      left
      use a, ξ
      simp only [true_and]
      cases ξ <;> grind
    case some.modR =>
    · grind -- sus that this works but did not in `modL` case?!
  case prLocTab nbas ltX nrep =>
    grind
  case buEnd Y ltX nbas Y_in nrep =>
    grind

lemma move.hist (mov : move ⟨Hist, X, pos⟩ next) :
      (∃ newPos, next = ⟨Hist, X, newPos⟩) -- this is for the annoying `prLocTab` case ;-)
    ∨ (∃ Y newPos, next = ⟨X :: Hist, Y, newPos⟩)  := by
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl => right; grind
  case prLocTab => left; grind
  case buEnd => right; grind

lemma move.hist_suffix (mov : move ⟨Hist, X, pos⟩ next) : Hist <:+ next.1 := by
  have := move.hist mov
  grind

lemma move.trans_hist_suffix (movt : Relation.TransGen move pX pZ) :
    pX.1 <:+ pZ.1 := by
  induction movt
  case single hm => exact move.hist_suffix hm
  case tail steps hm IH =>
    have := move.hist_suffix hm
    apply List.IsSuffix.trans IH this

/-- Along the transitive closure of `move` either the history stays the same or the old
sequent and history form a prefix of the new history
(where "prefix" is actually "suffix" because the history has the newest element first). -/
lemma move.trans_hist {pX pY} (movt : Relation.TransGen move pX pY) :
      (pX.1 = pY.1 ∧ pX.2.1 = pY.2.1)
    ∨ ((pX.2.1 :: pX.1) <:+ pY.1) := by
  induction movt -- would like induction here
  case single hm =>
    rcases hm.hist  with ⟨newP, HXP_eq⟩ | ⟨Z, newP, Y_def⟩
    · left
      cases HXP_eq
      simp
    · grind
  case tail pW pZ steps hm IH =>
    rcases IH with ⟨IH_same_H, IH_same_X⟩ | IH_change
      <;> rcases hm.hist  with ⟨newP, HXP_eq⟩ | ⟨Z, newP, Y_def⟩
    · left
      cases HXP_eq
      simp_all
    · cases Y_def
      simp
      aesop
    · cases HXP_eq
      simp at *
      aesop
    · cases Y_def
      simp at *
      rcases pX with ⟨X, H, p⟩
      rcases pW with ⟨Y', H', p'⟩
      simp at *
      grind

/-! ## Lemmas about double moves -/

/-- After two moves the history must grow. -/
lemma move_twice_hist_length {A B C : GamePos} (A_B : move A B) (B_C : move B C) :
    A.1.length < C.1.length := by
  rcases A with ⟨HA, A, pA⟩
  rcases B with ⟨HB, B, pB⟩
  rcases C with ⟨HC, C, pC⟩
  simp only
  rcases A_B with ⟨A_B⟩
  rcases B_C with ⟨B_C⟩
  cases A_B
  case prPdl Xbasic nrep r =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all <;> linarith
  case prLocTab ltA nrep =>
    cases B_C -- must be buEnd :-)
    case buEnd nbas nrep' C_in =>
      have := @endNodesOf_nonbasic_non_eq _ C ltA nbas C_in
      grind
  case buEnd ltA nbas nrep B_in =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all <;> linarith

/-- Insert obligatory "We like to move it move it" joke here. -/
abbrev movemove := Relation.Comp move move

lemma movemove.hist {A B C : GamePos} (A_B : move A B) (B_C : move B C) :
    ((A.2.1 :: A.1) <:+ C.1)  := by
  rcases A with ⟨HA, A, pA⟩
  rcases B with ⟨HB, B, pB⟩
  rcases C with ⟨HC, C, pC⟩
  simp only
  rcases A_B with ⟨A_B⟩
  rcases B_C with ⟨B_C⟩
  cases A_B
  case prPdl Xbasic nrep r =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all
  case prLocTab ltA nrep =>
    cases B_C -- must be buEnd :-)
    case buEnd nbas nrep' C_in =>
      have := @endNodesOf_nonbasic_non_eq _ C ltA nbas C_in
      grind
  case buEnd ltA nbas nrep B_in =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all

/-- After any number of double moves the history gets extended. -/
lemma movemove_trans_hist {A B : GamePos} (A_B : Relation.TransGen movemove A B) :
    ((A.2.1 :: A.1) <:+ B.1)  := by
  induction A_B
  case single C mvmv =>
    rcases mvmv with ⟨B, A_B, B_C⟩
    exact movemove.hist A_B B_C
  case tail B C A__B B_C IH =>
    rcases B_C with ⟨X, B_X, X_C⟩
    have := movemove.hist B_X X_C
    cases IH
    cases this
    grind

/-! ## Termination via finite FL closure

See also `StayingInFL.lean` where`Sequent.subseteq_FL` is defined.

We are working with lists (or, by ignoring their order, multisets) and thus staying in
the FL closure does not imply that there are only finitely many sequents reachable: by repeating
the same formulas the length of the list may increase.
To tackle this we want to use that `rep` is defined with `setEqTo` that ignores multiplicity, so
that even if there are infinitely many different lists and thus sequents in principle reachable,
we still cannot have an infinite chain because that would mean we must have a "set-repeat" that
is not allowed.

-/

lemma move_inside_FL {p next} (mov : move p next) : next.2.1.subseteq_FL p.2.1 := by
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl r => apply PdlRule.stays_in_FL r
  case buEnd ltX _ _ _ _ Y_in => simp; apply LocalTableau.stays_in_FL ltX _ Y_in
  case prLocTab => simp

/-- Given `~⌈α₁⌉…⌈αₙ⌉φ`, return the list of `~⌊α₁⌋…⌊αₖ⌋⌈αₖ₊₁⌉…⌈αₙ⌉φ` for all k. -/
def Formula.allNegLoads : Formula → List NegLoadFormula
| ~φ => match boxesOf φ with
    | ([], _) => []
    | (α :: αs, ψ) => do
        let k ← (List.range' 1 (α :: αs).length).attach
        have : (α :: αs).take k ≠ [] := by aesop
        return ~'(loadMulti_nonEmpty ((α :: αs).take k) this (⌈⌈(α :: αs).drop k⌉⌉ψ))
| _ => []

lemma Formula.allNegLoads_spec {nχ φ} : nχ ∈ φ.allNegLoads → negUnload nχ = φ := by
  cases φ <;> try (simp [allNegLoads]; done)
  case neg χ =>
  cases χ <;> try (simp [allNegLoads,boxesOf]; done)
  case box α φ =>
    rcases nχ with ⟨χ⟩
    simp only [allNegLoads, List.length_cons, List.pure_def, List.bind_eq_flatMap, negUnload,
      neg.injEq]
    split
    next h => exfalso; cases h
    next β βs ψ h =>
      simp only [List.mem_flatMap, List.mem_attach, List.mem_cons, NegLoadFormula.neg.injEq,
        List.not_mem_nil, or_false, true_and, Subtype.exists, List.mem_range'_1,
        forall_exists_index, forall_and_index]
      intro k one_le_k k_lt χ_def
      have := def_of_boxesOf_def h
      rw [this]; clear this
      subst χ_def
      simp only [loadMulti_nonEmpty_unload, boxes_cons]
      rw [← @boxes_append]
      rw [@List.take_append_drop]
      rfl

lemma Formula.allNegLoads_complete {nχ φ} : negUnload nχ = φ → nχ ∈ φ.allNegLoads := by
  rcases nχ with ⟨χ⟩
  simp only [negUnload]
  intro def_φ
  subst def_φ
  have := LoadFormula.exists_loadMulti χ
  rcases this with ⟨αs, α, φ, def_χ⟩
  have := @loadMulti_nonEmpty_eq_loadMulti αs α (by simp) φ
  rw [← this] at def_χ; clear this
  rw [def_χ]; clear def_χ
  simp only [allNegLoads, loadMulti_nonEmpty_unload, List.length_cons, List.pure_def,
    List.bind_eq_flatMap]
  split
  · exfalso
    cases αs <;> simp_all [boxesOf]
  next β βs ψ boxes_def =>
    simp only [List.mem_flatMap, List.mem_attach, List.mem_cons, NegLoadFormula.neg.injEq,
      List.not_mem_nil, or_false, true_and, Subtype.exists, List.mem_range'_1]
    use (αs ++ [α]).length
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add, List.take_succ_cons,
      List.drop_succ_cons, le_add_iff_nonneg_left, zero_le, true_and]
    have := Formula.boxesOf_boxes_prefix (αs ++ [α]) φ
    rcases this with ⟨γs, αs_α_γs_eq_boxes⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append, boxes_def] at αs_α_γs_eq_boxes
    refine ⟨?_, ?_⟩
    · have : (αs ++ α :: γs).length = (β :: βs).length := by simp_all
      simp only [List.length_append, List.length_cons] at this
      omega
    · -- This was tricky.
      rw [@loadMulti_nonEmpty_eq_loadMulti]
      have := def_of_boxesOf_def boxes_def
      cases αs
      · simp_all
      case cons β αs =>
      simp only [loadMulti_cons, List.length_cons]
      simp only [List.cons_append, boxes_cons, box.injEq] at this
      rcases this with ⟨β_, this⟩
      subst β_
      simp only [List.cons_append, List.cons.injEq, true_and] at αs_α_γs_eq_boxes
      subst αs_α_γs_eq_boxes
      simp only [List.drop_length_add_append, List.drop_succ_cons, List.drop_zero, ne_eq,
        List.take_eq_nil_iff, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false,
        List.append_eq_nil_iff, reduceCtorEq, or_self, not_false_eq_true, loadMulti_nonEmpty_box,
        LoadFormula.box.injEq, AnyFormula.loaded.injEq, true_and]
      -- Doable from here.
      simp only [boxes_append, boxes_cons, boxes_nil, boxes_injective, box.injEq, true_and] at this
      rw [this]
      apply LoadFormula.split_eq_loadMulti_nonEmpty (loadMulti αs α (⌈⌈γs⌉⌉ψ))
      rw [loadMulti_split]
      simp [List.take_length_add_append]

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
  -- Now we still need to generate all possible `XO : Olf` from `XOL` and `XOR`.
  let OLs : List Olf:= XOL.1.flatMap (fun φ => φ.allNegLoads.map (some ∘ Sum.inl))
  let ORs : List Olf:= XOR.1.flatMap (fun φ => φ.allNegLoads.map (some ∘ Sum.inr))
  let XO ← ((none : Olf) :: OLs ++ ORs).attach
  let X : Sequent := ⟨XL.1, XR.1, XO.1⟩
  have h : X.subseteq_FL Y := by
    unfold X
    rcases Y with ⟨L',R',O'⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
    · have := XL.2
      simp at this
      exact List.Sublist.subset this
    · simp only [Olf.L]
      rcases XO with ⟨none|⟨(nχ|_)⟩, XO_in⟩ <;> try simp_all
      simp only [List.cons_append, List.mem_cons, reduceCtorEq, List.mem_append, List.mem_flatMap,
        List.mem_map, Function.comp_apply, Option.some.injEq, Sum.inl.injEq, exists_eq_right,
        and_false, exists_false, or_false, false_or, OLs, ORs] at XO_in
      rcases XO_in with ⟨φ, φ_in, nχ_in⟩
      have := Formula.allNegLoads_spec nχ_in
      simp only [negUnload] at this
      rw [this]
      suffices φ ∈ (FLL (L' ++ O'.L)) by aesop
      have := XOL.2
      simp only [L_eq, O_eq, List.mem_sublists] at this
      exact List.Sublist.mem φ_in this
    · have := XR.2
      simp only [R_eq, O_eq, List.mem_sublists] at this
      exact List.Sublist.subset this
    · simp only [Olf.R]
      rcases XO with ⟨none|⟨(nχ|_)⟩, XO_in⟩ <;> try simp_all
      simp only [List.cons_append, List.mem_cons, reduceCtorEq, List.mem_append, List.mem_flatMap,
        List.mem_map, Function.comp_apply, Option.some.injEq, and_false, exists_false,
        Sum.inr.injEq, exists_eq_right, false_or, OLs, ORs] at XO_in
      rcases XO_in with ⟨φ, φ_in, nχ_in⟩
      have := Formula.allNegLoads_spec nχ_in
      simp only [negUnload] at this
      rw [this]
      suffices φ ∈ (FLL (R' ++ O'.R)) by aesop
      have := XOR.2
      simp only [R_eq, O_eq, List.mem_sublists] at this
      exact List.Sublist.mem φ_in this
  return ⟨X, h⟩

/-! NOTE

The following do NOT hold / do NOT exist because there are in fact infinitely many FL-subsequents
of a given sequent, so the list returned by `all_subseteq_FL` can never contain all.

```
def Sequent.all_subseteq_FL_complete (X Y : Sequent) (h : Y.subseteq_FL X) :
    ⟨Y,h⟩ ∈ Sequent.all_subseteq_FL X := ...

instance Sequent.subseteq_FL_fintype {X : Sequent} :
    Fintype { Y // Sequent.subseteq_FL Y X } := ...
```

Hence, we now use the `Seqt` (which is the quotient from `Sequent.setEqTo`)
within which there are only finitely many FL-subsequents.
-/

/-- In the quotient the moves keep us inside the FL. Unused but nice to have. -/
lemma Seqt.subseteq_FL_of_move (hm : move p next) :
    Seqt.subseteq_FL (Quotient.mk' next.2.1) (Quotient.mk' p.2.1) := by
  unfold Seqt.subseteq_FL
  exact move_inside_FL hm

def Sequent.allSeqt_subseteq_FL (X : Sequent) : Finset Seqt :=
  (X.all_subseteq_FL.map (fun x => ⟦x.1⟧)).toFinset

lemma Sequent.allSeqt_subseteq_FL_spec (X : Sequent) :
    ∀ Y, ⟦Y⟧ ∈ X.allSeqt_subseteq_FL → Y.subseteq_FL X := by
  intro Y Ys_in
  simp [Sequent.allSeqt_subseteq_FL, instSetoidSequent, Quotient.eq] at *
  rcases Ys_in with ⟨Z, ⟨Z_sub_X, Z_in_all⟩, Z_equiv_Y⟩
  exact Sequent.subseteq_FL_of_setEq_left Z_equiv_Y Z_sub_X

/-- Small helper function. Mathlib this? -/
lemma exists_mem_sublists_toFinsetEq_of_Subset [DecidableEq α] {A B : List α} :
    A ⊆ B → ∃ C ∈ B.sublists, C.toFinset = A.toFinset := by
  intro A_sub_B
  use (List.filter (fun x => decide (x ∈ A)) B)
  simp only [List.mem_sublists, List.filter_sublist, List.toFinset_filter, decide_eq_true_eq,
    true_and]
  aesop

lemma Sequent.allSeqt_subseteq_FL_complete (X : Sequent) :
    ∀ Y, Y.subseteq_FL X → ⟦Y⟧ ∈ X.allSeqt_subseteq_FL := by
  intro Y Y_in
  simp only [instSetoidSequent, allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset,
    List.mem_map, List.mem_unattach, Quotient.eq]
  -- Here the above NOTE matters.
  -- We need to work around that there is no `Sequent.all_subseteq_FL_complete`.
  -- `use Y` would not work because `Y` might not be in `all_subseteq_FL`.
  -- Instead, we find something that is `setEqTo Y` but also an element of `all_subseteq_FL`.
  unfold subseteq_FL at Y_in
  rcases Y_in with ⟨Lh, OLh, Rh, ORh⟩
  -- Now use the lemma that for any subset of a list gives us a sublist, four times.
  rcases exists_mem_sublists_toFinsetEq_of_Subset Lh  with ⟨L' , L'_in , L'_same ⟩
  rcases exists_mem_sublists_toFinsetEq_of_Subset OLh with ⟨OL', OL'_in, OL'_same⟩
  rcases exists_mem_sublists_toFinsetEq_of_Subset Rh  with ⟨R' , R'_in , R'_same ⟩
  rcases exists_mem_sublists_toFinsetEq_of_Subset ORh with ⟨OR', OR'_in, OR'_same⟩
  -- Now we need to reconstruct (a subOption of ???) `Y.O` from OL' and R' here ??
  -- Or could we just use Y.O itself ?!?!
  refine ⟨⟨L', R', Y.O⟩, ⟨?_, ?_⟩ , L'_same, R'_same, rfl⟩
  · unfold subseteq_FL
    simp only [L_eq, O_eq, R_eq]
    simp_all [FLL_append_eq]
    constructor
    · exact List.Sublist.subset L'_in
    · exact List.Sublist.subset R'_in
  · rcases Y with ⟨YL, YR, YO⟩
    rcases X with ⟨XL, XR, XO⟩
    -- now we hope that the above procedure imitates the `all_subseteq_FL` def :-)
    simp only [all_subseteq_FL, L, R, O]
    simp only [List.cons_append, List.attach_cons, List.attach_append, List.map_append,
      List.map_map, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_append,
      List.nil_append, List.mem_flatMap, List.mem_attach, List.mem_cons, Subtype.mk.injEq,
      List.mem_append, List.mem_map, Function.comp_apply, true_and, Subtype.exists,
      List.not_mem_nil, or_false, exists_prop, exists_eq_right, List.mem_sublists]
    refine ⟨L', List.mem_sublists.mp L'_in, ?_⟩
    refine ⟨OL', List.mem_sublists.mp OL'_in, ?_⟩
    refine ⟨R', List.mem_sublists.mp R'_in, ?_⟩
    refine ⟨OR', List.mem_sublists.mp OR'_in, ?_⟩
    rcases YO with none|⟨nχ|nχ⟩
    · left; rfl
    · right; left
      have nχ_in : negUnload nχ ∈ OL' := by
        simp only [O_eq, Olf.L_inl, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, negUnload] at *
        rw [← List.mem_toFinset, OL'_same]
        simp
      refine ⟨some (Sum.inl nχ), ?_, ⟨?_, rfl⟩⟩
      · right; left
        exact ⟨negUnload nχ, nχ_in, ⟨nχ, Formula.allNegLoads_complete rfl, rfl⟩⟩
      · exact ⟨negUnload nχ, nχ_in, ⟨nχ, Formula.allNegLoads_complete rfl, rfl⟩⟩
    · right; right
      have nχ_in : negUnload nχ ∈ OR' := by
        simp only [L_eq, O_eq, List.mem_sublists, R_eq, Olf.L_inr, List.toFinset_nil,
          List.toFinset_eq_empty_iff, Olf.R_inr, List.toFinset_cons, insert_empty_eq,
          List.nil_subset, List.cons_subset, and_true, negUnload] at *
        rw [← List.mem_toFinset, OR'_same]
        simp
      refine ⟨some (Sum.inr nχ), ?_, ⟨?_, rfl⟩⟩
      · right; right
        exact ⟨negUnload nχ, nχ_in, ⟨nχ, Formula.allNegLoads_complete rfl, rfl⟩⟩
      · exact ⟨negUnload nχ, nχ_in, ⟨nχ, Formula.allNegLoads_complete rfl, rfl⟩⟩

lemma Sequent.allSeqt_subseteq_FL_congr (X Y : Sequent) (h : X ≈ Y) :
    Sequent.allSeqt_subseteq_FL X = Sequent.allSeqt_subseteq_FL Y := by
  ext Ys
  simp only [allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset, List.mem_map,
    List.mem_unattach]
  simp [instHasEquivOfSetoid, instSetoidSequent] at h
  constructor
  · rintro ⟨Z, ⟨Z_sub_X, Z_in_sub_X⟩, def_YS⟩
    subst def_YS
    have Z_sub_Y := (Sequent.subseteq_FL_congr Z X Z Y (Setoid.refl _) h).mp Z_sub_X
    have := Y.allSeqt_subseteq_FL_complete Z Z_sub_Y
    simp only [instSetoidSequent, allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset,
      List.mem_map, List.mem_unattach, Quotient.eq] at this
    rcases this with ⟨W, ⟨W_eq_Y, _⟩, W_eq_Z⟩
    use W
    simp_all
    exact Quotient.sound W_eq_Z
  · rintro ⟨Z, ⟨Z_sub_Y, Z_in_sub_Y⟩, def_YS⟩
    subst def_YS
    have Z_sub_Y := (Sequent.subseteq_FL_congr Z Y Z X (Setoid.refl _) (Setoid.symm h)).mp Z_sub_Y
    have := X.allSeqt_subseteq_FL_complete Z Z_sub_Y
    simp only [allSeqt_subseteq_FL, List.map_subtype, List.mem_toFinset, List.mem_map,
      List.mem_unattach, Quotient.eq] at this
    rcases this with ⟨W, ⟨W_eq_Y, _⟩, W_eq_Z⟩
    use W
    simp_all
    exact Quotient.sound W_eq_Z

def Seqt.all_subseteq_FL (Xs : Seqt) : Finset Seqt  :=
  Quotient.lift Sequent.allSeqt_subseteq_FL Sequent.allSeqt_subseteq_FL_congr Xs

lemma Seqt.all_subseteq_FL_spec {Ys : Seqt} (Ys_in : Ys ∈ Xs.all_subseteq_FL) :
    Ys.subseteq_FL Xs := by
  rcases Ys with ⟨Y⟩
  rcases Xs with ⟨x⟩
  unfold Seqt.all_subseteq_FL at Ys_in
  unfold Seqt.subseteq_FL
  simp [instSetoidSequent] at *
  exact Sequent.allSeqt_subseteq_FL_spec x Y Ys_in

lemma Seqt.all_subseteq_FL_complete {Ys : Seqt} (Ys_in : Ys.subseteq_FL Xs) :
    Ys ∈ Xs.all_subseteq_FL := by
  rcases Ys with ⟨Y⟩
  rcases Xs with ⟨X⟩
  exact Sequent.allSeqt_subseteq_FL_complete X Y Ys_in

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

/-- Helper lemma for `matchesFinite`: If we have enumerate infinitely many values, and all of them
have a certain property, but we also know that there are only finitely many values with that
property, then there must be identical values in the enumeration. -/
lemma exist_duplicates_of_infinite_among_fintype {α : Type} {f : ℕ → α} {p : α → Prop}
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

/-! ### Infinite chains of moves

Towards `matchesFinite` we here collect facts about an infinite chain `g : ℕ → GamePos` with
`move (g n) (g (n+1))` for all `n`, following the proof idea for the `matchesFinite` lemma:

- at each position of the chain a move is possible, hence there is no forbidden repeat,
  i.e. `¬ flprep` (see `moveChain_not_flprep`);
- all sequents along the chain stay inside the FL closure of the first one
  (see `moveChain_inside_FL`), of which there are only finitely many modulo `setEqTo`
  (see `Seqt.subseteq_FL_finite`);
- the history at a later position contains the sequents of all earlier positions
  (see `moveChain_hist_accum` and `moveChain_hist_split`);
- hence a sequent that is `setEqTo` an earlier one must be loaded, because a free repeat
  would have ended the match (see `moveChain_setEq_isLoaded`), and thus from some point
  onwards *all* sequents in the chain are loaded (see `moveChain_eventually_loaded`);
- a repeat in this loaded part gives a loaded-path repeat, which also ends the match
  (see `moveChain_hist_index` and `moveChain_multisetEq_absurd`).

This section is from aristotle.harmonic.fun -/

/-- If a move from `⟨H, X, p⟩` is possible, then `X` is neither a free repeat nor a
loaded-path repeat in `H`. Note this is stronger than `move_then_no_frep`. -/
lemma move_then_not_flprep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ flprep H X := by
  simp only [move, Nonempty.forall]
  intro next_p hyp
  cases next_p <;> grind

/-- Helper lemma for `matchesFinite`: if a property of natural numbers holds arbitrarily late,
then we can enumerate witnesses for it with gaps of at least two. -/
lemma exists_spread_subsequence {P : ℕ → Prop} (hS : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ e : ℕ → ℕ, (∀ k, P (e k)) ∧ ∀ k1 k2, k1 < k2 → e k1 + 2 ≤ e k2 := by
  classical
  let e : ℕ → ℕ := fun k => Nat.rec (Classical.choose (hS 0))
    (fun _ prev => Classical.choose (hS (prev + 2))) k
  have e_succ : ∀ k, e (k + 1) = Classical.choose (hS (e k + 2)) := fun _ => rfl
  have hP : ∀ k, P (e k) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hS 0)).2
    | succ k => rw [e_succ]; exact (Classical.choose_spec (hS (e k + 2))).2
  have step : ∀ k, e k + 2 ≤ e (k + 1) := by
    intro k
    rw [e_succ]
    exact (Classical.choose_spec (hS (e k + 2))).1
  refine ⟨e, hP, ?_⟩
  intro k1 k2 hk
  induction k2 with
  | zero => omega
  | succ k IH =>
    rcases Nat.lt_or_ge k1 k with h | h
    · have := IH h
      have := step k
      omega
    · have : k1 = k := by omega
      subst this
      exact step k1

section MoveChain

variable {g : ℕ → GamePos} (g_rel : ∀ n, move (g n) (g (n + 1)))
include g_rel

/-- Because a move is possible, no position in the chain is a forbidden repeat. -/
lemma moveChain_not_flprep (n : ℕ) : ¬ flprep (g n).1 (g n).2.1 := by
  have h := g_rel n
  rcases hn : g n with ⟨H, X, p⟩
  rw [hn] at h
  exact move_then_not_flprep h

/-- One step in the chain either keeps history and sequent (the `prLocTab` case)
or adds the current sequent to the history. -/
lemma moveChain_hist_step (n : ℕ) :
    ((g (n + 1)).1 = (g n).1 ∧ (g (n + 1)).2.1 = (g n).2.1)
    ∨ (g (n + 1)).1 = (g n).2.1 :: (g n).1 := by
  have h := g_rel n
  rcases hn : g n with ⟨H, X, p⟩
  rw [hn] at h
  rcases move.hist h with ⟨newPos, h'⟩ | ⟨Y, newPos, h'⟩
  · left; rw [h']; simp
  · right; rw [h']

/-- The history only grows, and everything added to it are sequents from the chain. -/
lemma moveChain_hist_accum (m : ℕ) :
    ∀ n, m ≤ n → ∃ pre : List Sequent, (g n).1 = pre ++ (g m).1
      ∧ ∀ Y ∈ pre, ∃ j, m ≤ j ∧ j < n ∧ Y = (g j).2.1 := by
  intro n
  induction n with
  | zero =>
    intro h
    have : m = 0 := by omega
    subst this
    exact ⟨[], by simp, by simp⟩
  | succ k IH =>
    intro h
    by_cases hmk : m ≤ k
    · obtain ⟨pre, hpre, hall⟩ := IH hmk
      rcases moveChain_hist_step g_rel k with ⟨h1, _⟩ | h1
      · refine ⟨pre, by rw [h1, hpre], fun Y hY => ?_⟩
        obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
        exact ⟨j, hj1, by omega, hj3⟩
      · refine ⟨(g k).2.1 :: pre, ?_, ?_⟩
        · rw [h1, List.cons_append]
          exact congrArg (fun l => (g k).2.1 :: l) hpre
        · rintro Y hY
          rcases List.mem_cons.mp hY with rfl | hY
          · exact ⟨k, hmk, by omega, rfl⟩
          · obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
            exact ⟨j, hj1, by omega, hj3⟩
    · have : m = k + 1 := by omega
      subst this
      exact ⟨[], by simp, by simp⟩

/-- After at least two moves the sequent of the earlier position is in the later history,
and all newer entries of that history are sequents from strictly in between. -/
lemma moveChain_hist_split {m n : ℕ} (h : m + 2 ≤ n) :
    ∃ pre : List Sequent, (g n).1 = pre ++ ((g m).2.1 :: (g m).1)
      ∧ ∀ Y ∈ pre, ∃ j, m < j ∧ j < n ∧ Y = (g j).2.1 := by
  rcases moveChain_hist_step g_rel m with ⟨h1, hX1⟩ | h1
  · -- The step from `m` did not change the history, hence the next one must do so.
    have h2 : (g (m + 2)).1 = (g m).2.1 :: (g m).1 := by
      rcases moveChain_hist_step g_rel (m + 1) with ⟨h2, _⟩ | h2
      · exfalso
        have := move_twice_hist_length (g_rel m) (g_rel (m + 1))
        rw [show m + 1 + 1 = m + 2 from rfl] at h2
        rw [h2, h1] at this
        omega
      · rw [show m + 2 = m + 1 + 1 from rfl, h2]
        exact congrArg₂ (· :: ·) hX1 h1
    obtain ⟨pre, hpre, hall⟩ := moveChain_hist_accum g_rel (m + 2) n (by omega)
    refine ⟨pre, by rw [hpre, h2], fun Y hY => ?_⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
    exact ⟨j, by omega, hj2, hj3⟩
  · obtain ⟨pre, hpre, hall⟩ := moveChain_hist_accum g_rel (m + 1) n (by omega)
    refine ⟨pre, by rw [hpre, h1], fun Y hY => ?_⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
    exact ⟨j, by omega, hj2, hj3⟩

/-- All sequents in the chain stay inside the FL closure of the first sequent. -/
lemma moveChain_inside_FL (n : ℕ) : Seqt.subseteq_FL ⟦(g n).2.1⟧ ⟦(g 0).2.1⟧ := by
  simp only [Seqt.subseteq_FL, Quotient.lift_mk]
  induction n
  · simp
  case succ k IH =>
    apply Sequent.subseteq_FL_trans _ _ _ ?_ IH
    apply move_inside_FL (g_rel k)

/-- A sequent in the chain that is `setEqTo` an earlier one must be loaded,
because otherwise we would have a free repeat and the match would have ended. -/
lemma moveChain_setEq_isLoaded {m n : ℕ} (h : m + 2 ≤ n) (hs : (g m).2.1.setEqTo (g n).2.1) :
    (g n).2.1.isLoaded := by
  obtain ⟨pre, hpre, _⟩ := moveChain_hist_split g_rel h
  have h_rep : rep (g n).1 (g n).2.1 := by
    refine ⟨(g m).2.1, ?_, hs⟩
    rw [hpre]
    simp
  by_contra hfree
  exact moveChain_not_flprep g_rel n (Or.inl ⟨h_rep, by simp [Sequent.isFree, hfree]⟩)

/-- Because there are only finitely many sequents modulo `setEqTo` inside the FL closure,
arbitrarily late in the chain we find two positions with `setEqTo` sequents. -/
lemma moveChain_exists_setEq_late (N : ℕ) :
    ∃ m n, N ≤ m ∧ m + 2 ≤ n ∧ (g m).2.1.setEqTo (g n).2.1 := by
  obtain ⟨e, hP, hgap⟩ := exists_spread_subsequence (P := fun n => N ≤ n)
    (fun M => ⟨max M N, le_max_left _ _, le_max_right _ _⟩)
  obtain ⟨k1, k2, hne, hsame⟩ := @exist_duplicates_of_infinite_among_fintype _
    (fun k => (⟦(g (e k)).2.1⟧ : Seqt)) (Seqt.subseteq_FL · ⟦(g 0).2.1⟧)
    (fun k => moveChain_inside_FL g_rel (e k)) Seqt.subseteq_FL_finite
  simp only [Quotient.eq] at hsame
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · exact ⟨e k1, e k2, hP k1, hgap k1 k2 hlt, hsame⟩
  · exact ⟨e k2, e k1, hP k2, hgap k2 k1 (by omega), (Sequent.setEqTo_symm _ _).mp hsame⟩

/-- From some point onwards all sequents in the chain are loaded: there are only finitely
many sequents modulo `setEqTo`, and free ones can never come back. -/
lemma moveChain_eventually_loaded : ∃ N, ∀ n, N ≤ n → (g n).2.1.isLoaded := by
  by_contra hyp
  push_neg at hyp
  obtain ⟨e, hP, hgap⟩ := exists_spread_subsequence hyp
  obtain ⟨k1, k2, hne, hsame⟩ := @exist_duplicates_of_infinite_among_fintype _
    (fun k => (⟦(g (e k)).2.1⟧ : Seqt)) (Seqt.subseteq_FL · ⟦(g 0).2.1⟧)
    (fun k => moveChain_inside_FL g_rel (e k)) Seqt.subseteq_FL_finite
  simp only [Quotient.eq] at hsame
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · exact absurd (moveChain_setEq_isLoaded g_rel (hgap k1 k2 hlt) hsame) (hP k2)
  · exact absurd (moveChain_setEq_isLoaded g_rel (hgap k2 k1 (by omega))
      ((Sequent.setEqTo_symm _ _).mp hsame)) (hP k1)

/-- If all sequents from `N` onwards are loaded and `N ≤ m` with `m + 2 ≤ n`, then the sequent
of position `m` occurs in the history of position `n` at an index such that all entries up to
and including that index are loaded. This is what is needed for a loaded-path repeat. -/
lemma moveChain_hist_index {N m n : ℕ} (hN : ∀ j, N ≤ j → (g j).2.1.isLoaded)
    (hm : N ≤ m) (h : m + 2 ≤ n) :
    ∃ k : Fin (g n).1.length,
      (g n).1.get k = (g m).2.1 ∧ ∀ i ≤ k, ((g n).1.get i).isLoaded := by
  obtain ⟨pre, hpre, hall⟩ := moveChain_hist_split g_rel h
  have hlen : pre.length < (g n).1.length := by
    rw [hpre]; simp
  refine ⟨⟨pre.length, hlen⟩, ?_, ?_⟩
  · simp only [List.get_eq_getElem]
    rw [List.getElem_of_eq hpre, List.getElem_append_right (by omega)]
    simp
  · rintro ⟨i, hi⟩ hik
    simp only [List.get_eq_getElem, Fin.mk_le_mk] at *
    rcases Nat.lt_or_ge i pre.length with hlt | hge
    · have hmem : (g n).1[i] ∈ pre := by
        rw [List.getElem_of_eq hpre, List.getElem_append_left hlt]
        exact List.getElem_mem hlt
      obtain ⟨j, hj1, hj2, hj3⟩ := hall _ hmem
      rw [hj3]
      exact hN j (by omega)
    · have hieq : i = pre.length := by omega
      have : (g n).1[i] = (g m).2.1 := by
        rw [List.getElem_of_eq hpre, List.getElem_append_right (by omega)]
        simp [hieq]
      rw [this]
      exact hN m hm

/-- A `setEqTo` repeat in the loaded part of the chain is impossible:
it would be a loaded-path repeat, at which the match ends. -/
lemma moveChain_setEq_absurd {N m n : ℕ} (hN : ∀ j, N ≤ j → (g j).2.1.isLoaded)
    (hm : N ≤ m) (h : m + 2 ≤ n) (hs : (g m).2.1.setEqTo (g n).2.1) : False := by
  obtain ⟨k, hk1, hk2⟩ := moveChain_hist_index g_rel hN hm h
  exact moveChain_not_flprep g_rel n (Or.inr ⟨⟨k, by rw [hk1]; exact hs, hk2⟩⟩)

end MoveChain

/-- Lemma 6.11. The move relation is converse wellfounded (and thus all matches must be finite).
This is similar to the proof that PDL-tableaux are finite (Lemma 4.10), relying on the finiteness
of the Fischer-Ladner closure.
In Lean we never needed to say 4.10 because values of the inductive type `Tableau` are always
finite by constriction. But we do need a proof here, as this lemma is about `move`, not `Match`.

The whole argument is done in the `MoveChain` section above. -/
lemma matchesFinite : WellFounded (Function.swap move) := by
  -- If it's not wellfounded, then there must be an infinite sequence of moves.
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hyp
  simp at hyp
  rcases hyp with ⟨g, g_rel⟩
  simp only [Function.swap] at g_rel
  -- From some point `N` onwards all sequents in the chain are loaded.
  obtain ⟨N, hN⟩ := moveChain_eventually_loaded g_rel
  -- In this loaded part we find a repeat, which is a loaded-path repeat, ending the match.
  obtain ⟨m, n, hm, hmn, hs⟩ := moveChain_exists_setEq_late g_rel N
  exact moveChain_setEq_absurd g_rel hN hm hmn hs

/-! ## Actual Game Definition -/

/-- The game defined in Section 6.2. -/
def tableauGame : Game where
  Pos := GamePos
  turn | ⟨_, _, .inl _⟩ => Prover
       | ⟨_, _, .inr _⟩ => Builder
  moves := theMoves
  wf := ⟨fun x y => move y x, matchesFinite⟩
  move_rel := by grind [move_of_mem_theMoves]

/-- This helps to pick up the derived instance `DecidableEq GamePos` above. -/
instance instDecidableEqPos : DecidableEq tableauGame.Pos := by
  simp only [Game.Pos, tableauGame]
  exact instDecidableEqOfLawfulBEq

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
    @winner i tableauGame sI sJ ⟨Hist, X, .inl (.frep h)⟩ = Builder := by
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
            have notBox : ¬ (boxesOf φ).2.isBox := boxesOf_output_not_isBox
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, List.mem_cons, List.not_mem_nil, or_false]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              constructor -- leaving Prop
              apply Tableau.pdl nrep Xbas
                (@PdlRule.loadL _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_)
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
            have notBox : ¬ (boxesOf φ).2.isBox := boxesOf_output_not_isBox
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, List.mem_cons, List.not_mem_nil, or_false]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              constructor -- leaving Prop
              apply Tableau.pdl nrep Xbas
                (@PdlRule.loadR _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_)
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

/-- We start with a prover position, because when the history is empty we can't have any repeat. -/
lemma posOf_for_startPos (X : Sequent) : ∃ proPos, posOf [] X = Sum.inl proPos := by
  unfold posOf
  by_cases Nonempty (LoadedPathRepeat [] X)
  case pos h => rcases h with ⟨⟨_⟩⟩; grind
  case neg h =>
    simp only [h, ↓reduceDIte, not_rep_empty]
    by_cases X.basic <;> simp_all

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    Nonempty (Tableau [] X) := gameP_general [] X s _ h
