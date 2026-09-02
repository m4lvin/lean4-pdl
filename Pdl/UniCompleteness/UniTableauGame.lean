import Pdl.Completeness.TableauGame
import Pdl.Interpolation.Uniformity

/-! # The Tableau Game with uniform local tableaux

This is a variant of `Pdl.Completeness.TableauGame` in which Prover is no longer free to
choose *any* local tableau: at a non-basic sequent `X` the only move available is the one
to the canonical local tableau `uniLocalTab X` defined in `Pdl.Interpolation.Uniformity`.

Everything here lives in the namespace `UniGame`, so the names below shadow, but do not
clash with, those of the original game. Notions that do not mention `Move` — such as
`ProverPos`, `BuilderPos`, `GamePos` and `posOf`, and the finiteness lemmas about the
Fischer-Ladner closure — are reused from `Pdl.Completeness.TableauGame`.

The gain is in `gameP_general`: a winning strategy for Prover now yields a tableau that is
*uniform* in the sense of `Tableau.IsUni` (and hence `Tableau.isUniform` for the empty
history), because at every `loc` step the canonical local tableau is used.

The remaining results about the original game are redone for this game in
`Pdl.Completeness.UniBuildTree`, `Pdl.Completeness.UniBuildTreeModel`,
`Pdl.Completeness.UniBuildTreeExistence` and `Pdl.Completeness.UniTheorem`, which repeat the
completeness proof and conclude with `UniGame.satisfiable_or_exists_uniform_tableau`.
The converse direction, from a tableau to a winning strategy for Prover, is not needed for
that and has not been redone here. -/

namespace UniGame

/-! ## Moves -/

/-- The relation `Move old next` says that we can move from `old` to `next`.
There are three kinds of moves.

Unlike in `Pdl.Completeness.TableauGame`, in the `prLocTab` move Prover has no choice:
the local tableau must be the canonical uniform one, `uniLocalTab X`. -/
inductive Move : (old : GamePos) → (new : GamePos) → Type
/-- When the sequent is basic and no repeat, let prover apply a PDL rule. -/
| prPdl {X Y Hist nrep Xbasic} : PdlRule X Y →
    Move ⟨Hist, X, .inl (.bas nrep Xbasic)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩
/-- If not basic, Prover must move to the uniform local tableau `uniLocalTab X`. -/
| prLocTab {Hist X nrep nbas} :
    Move ⟨Hist, X, .inl (.nbas nrep nbas)⟩
         ⟨Hist, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩
/-- Let Builder pick an end node of `ltab` -/
| buEnd {X ltab Y Hist nrep nbas} : Y ∈ endNodesOf (ltab : LocalTableau X) →
    Move ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩

def Move.isModal {pos newPos : GamePos} : Move pos newPos → Prop
| .prPdl r => r.isModal
| .prLocTab => False
| .buEnd _ => False

def move (old : GamePos) (new : GamePos) : Prop := Nonempty (Move old new)

/-- Any move of the uniform game is also a move of the original game. -/
noncomputable def Move.toRoot {pos newPos : GamePos} : Move pos newPos → _root_.Move pos newPos
| .prPdl r => .prPdl r
| .prLocTab => .prLocTab
| .buEnd Y_in => .buEnd Y_in

lemma move.toRoot {pos newPos : GamePos} (h : move pos newPos) : _root_.move pos newPos :=
  h.elim (fun m => ⟨m.toRoot⟩)

lemma move_then_no_frep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ (rep H X ∧ X.isFree) :=
  fun h => _root_.move_then_no_frep h.toRoot

@[simp]
noncomputable def theMoves : GamePos → Finset GamePos
  -- ProverPos:
  | ⟨H, X, .inl (.frep _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ Xbasic)⟩ =>
      -- need to choose PDL rule application:
      match X with
      | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
            -- We want to catch a negation and all boxes (≥ 1) after it to be loaded.
            (L.sup (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              { ⟨ _, _, posOf (X::H) (L.erase (~φ), R
                                , some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ }
                            | ([],_) => {}
                        | _ => {} ))
            ∪
            (R.sup (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              { ⟨ _, _, posOf (X::H) (L, R.erase (~φ)
                                , some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ }
                            | ([],_) => {}
                        | _ => {} ))
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨{~φ} ∪ L.projection a, R.projection a, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ L.projection a, R.projection a
                                                 , some (Sum.inl (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L ∪ {~(⌊·a⌋ξ).unload}, R, none)⟩ }
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨L.projection a, {~φ} ∪ R.projection a, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ L.projection a, R.projection a
                                                 , some (Sum.inr (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L, R ∪ {~(⌊·a⌋ξ).unload}, none)⟩ }
      -- Somewhat repetitive. Is there pattern matching with "did not match before" proofs?
      | ⟨L, R, some (.inl (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
  | ⟨H, X, .inl (.nbas nrep nbas)⟩ =>
      -- If not basic, Prover must move to the uniform local tableau `uniLocalTab X`.
      { ⟨H, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩ }
  -- BuilderPos:
  | ⟨H, X, .inr (.lpr lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.ltab _ _ ltab)⟩ =>
      -- Let Builder pick an end node of `ltab`:
      ((endNodesOf ltab).image (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩))
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
                ∧ next = ⟨_,_,posOf (X::H) ⟨{~φ} ∪ L.projection a, R.projection a, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.projection a, R.projection a, some (Sum.inl (~'χ))⟩⟩ )
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L ∪ {~(⌊·a⌋ξ).unload}, R, none)⟩ )
            )
        )
        ∨
        ( ∃ a ξ, X = ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩
          ∧ ( ( ∃ φ, ξ = .normal φ -- (M) rule, deterministic
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.projection a, {~φ} ∪ R.projection a, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.projection a, R.projection a, some (Sum.inr (~'χ))⟩⟩)
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L, R ∪ {~(⌊·a⌋ξ).unload}, none)⟩
              )
            )
        )
      )
    )
    ∨
    ( ∃ nrep nbas, p = .inl (.nbas nrep nbas) -- not basic, prover must take `uniLocalTab X`
      ∧ next = ⟨H, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩
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
            simp only [bxs_def, Finset.mem_singleton] at next_in
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
            simp only [bxs_def, Finset.mem_singleton] at next_in
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
    · simp [hyp]
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
          simp only [bxs_def, Finset.mem_singleton] at next_in
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
          simp only [bxs_def, Finset.mem_singleton] at next_in
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
  · subst mv
    exact ⟨Move.prLocTab⟩
  · subst mv
    exact ⟨Move.prLocTab⟩
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
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inl, negUnload, LoadFormula.unload,
            Option.toFinset_some, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
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
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inl, negUnload, unload_boxes,
            LoadFormula.unload, Formula.boxes_cons, Option.toFinset_some, Finset.union_singleton,
            Finset.mem_insert, Finset.mem_union, Formula.basic, decide_false, decide_true,
            forall_eq_or_imp, Bool.false_eq_true, false_and] at bas
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
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inr, negUnload, LoadFormula.unload,
            Option.toFinset_some, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
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
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inr, negUnload, unload_boxes,
            LoadFormula.unload, Formula.boxes_cons, Option.toFinset_some,
            Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
    case some.modL a ξ =>
      right
      left
      use a, ξ
      simp only [true_and]
      cases ξ <;> grind
    case some.modR =>
    · grind -- sus that this works but did not in `modL` case?!
  case prLocTab nbas nrep =>
    grind
  case buEnd Y ltX nbas Y_in nrep =>
    grind

/-! ## Termination

Every move of the uniform game is also a move of the original game, hence the converse
wellfoundedness of `move` is inherited from `matchesFinite` in `Pdl.Completeness.TableauGame`,
and so are the lemmas about how the history changes. -/

lemma move.hist {Hist X pos next} (mov : move ⟨Hist, X, pos⟩ next) :
      (∃ newPos, next = ⟨Hist, X, newPos⟩)
    ∨ (∃ Y newPos, next = ⟨X :: Hist, Y, newPos⟩) := _root_.move.hist mov.toRoot

lemma move.hist_suffix {Hist X pos next} (mov : move ⟨Hist, X, pos⟩ next) : Hist <:+ next.1 :=
  _root_.move.hist_suffix mov.toRoot

lemma move_inside_FL {p next} (mov : move p next) : next.2.1.subseteq_FL p.2.1 :=
  _root_.move_inside_FL mov.toRoot

lemma move_then_not_flprep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ flprep H X :=
  fun h => _root_.move_then_not_flprep h.toRoot

/-- Lemma 6.11 for the uniform game: the move relation is converse wellfounded
(and thus all matches must be finite). -/
lemma matchesFinite : WellFounded (Function.swap move) :=
  Subrelation.wf (fun h => move.toRoot h) _root_.matchesFinite


/-- The game defined in Section 6.2. -/
noncomputable def tableauGame : Game where
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
/-! ## Uniform positions

A `BuilderPos` in general still carries an arbitrary local tableau, but the only such
positions that can be reached in the uniform game are those with `uniLocalTab`. -/

/-- A game position is *uniform* if any local tableau in it is the canonical one. -/
def GamePos.IsUni : GamePos → Prop
  | ⟨_, X, .inr (.ltab _ _ lt)⟩ => lt = uniLocalTab X
  | _ => True

/-- Positions given by `posOf` are uniform: they are never `ltab` positions. -/
lemma posOf_isUni (H : History) (X : Sequent) : GamePos.IsUni ⟨H, X, posOf H X⟩ := by
  unfold posOf
  split
  · trivial
  · split
    · trivial
    · split <;> trivial

/-- All moves lead to uniform positions. -/
lemma theMoves_isUni {p next : GamePos} (h : next ∈ theMoves p) : GamePos.IsUni next := by
  rcases move_of_mem_theMoves h with ⟨mov⟩
  cases mov
  case prPdl => exact posOf_isUni _ _
  case prLocTab => rfl
  case buEnd => exact posOf_isUni _ _

/-! ## From Prover winning strategies to uniform tableaux -/

/-- Helper for `gameP_general`: prefixing a uniform tableau with a PDL rule keeps it uniform. -/
lemma exists_isUni_of_pdl {Hist X Y} (nrep : ¬ flprep Hist X) (bas : X.basic) (r : PdlRule X Y)
    {next : Tableau (X :: Hist) Y} (h : next.IsUni) : ∃ tab : Tableau Hist X, tab.IsUni :=
  ⟨.pdl nrep bas r next, h⟩

/-- After history `Hist`, if Prover has a winning strategy then there is a closed tableau,
and moreover that tableau is uniform in the sense of `Tableau.IsUni`, because in this game
Prover has to play the canonical local tableau `uniLocalTab`.
Note: we skip Definition 6.9 (Strategy Tree for Prover) and just use the `Strategy` type.
This is the induction loading for `gameP`. -/
theorem gameP_general Hist (X : Sequent) (sP : Strategy tableauGame Prover) (pos : _)
    (pos_uni : GamePos.IsUni ⟨Hist, X, pos⟩)
    (h : winning sP ⟨Hist, X, pos⟩)
    : ∃ tab : Tableau Hist X, tab.IsUni := by
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
      have IH := gameP_general _ _ sP _ (theMoves_isUni the_move.2) still_winning -- okay ??
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp only at IH
      obtain ⟨new_tab_from_IH, new_uni⟩ := IH
      simp only [tableauGame, Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      rcases X with ⟨L,R,_|(⟨⟨χ⟩⟩|⟨⟨χ⟩⟩)⟩ <;> simp at *
      · -- no loaded formula yet, the only PDL rule we can apply is (L+)
        rcases nextPosIn with ⟨χ, χ_in⟩|⟨χ, χ_in⟩
        · cases χ
          case neg φ =>
            have notBox : ¬ (boxesOf φ).2.isBox := boxesOf_output_not_isBox
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, Finset.mem_singleton]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              refine exists_isUni_of_pdl nrep Xbas
                (@PdlRule.loadL _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_) new_uni
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
            · simp_all only [tableauGame_turn_Prover, Finset.mem_singleton]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              refine exists_isUni_of_pdl nrep Xbas
                (@PdlRule.loadR _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_) new_uni
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
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeL _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeL _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact exists_isUni_of_pdl nrep Xbas (PdlRule.modL rfl rfl) new_uni
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
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeR _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeR _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp at nextPosIn <;> cases nextPosIn
            all_goals
              exact exists_isUni_of_pdl nrep Xbas (by apply PdlRule.modR <;> rfl) new_uni
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
    case nbas nrep X_nbas =>
      -- not basic, Prover must move to the uniform local tableau
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
      have IH := gameP_general _ _ sP _ (theMoves_isUni the_move.2) still_winning -- okay ??
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp only at IH
      simp only [tableauGame, Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      --- ... until here
      -- No need to look into the local tableau here, we use the IH for the `BuilderPos` case!
      simp only [theMoves, Finset.mem_singleton] at nextPosIn
      obtain ⟨rfl, rfl, -⟩ := nextPosIn
      exact IH
  -- BuilderPos:
  · rw [pos_def] at pos_uni
    rcases builPos with ⟨lpr⟩|⟨nrep, nbas, ltX⟩
    · exact ⟨Tableau.lrep lpr, trivial⟩
    · -- We have a local tableau and it is the turn of Builder.
      -- Now each `Y : endNodesOf lt` is a possible move.
      -- Because `sP` wins against all moves by Builder we can use `sP` to define `next`.
      -- Note that all is non-constructive here via choice.
      have ltX_def : ltX = uniLocalTab X := pos_uni
      subst ltX_def
      have next' : ∀ Y (_ : Y ∈ endNodesOf (uniLocalTab X)),
          ∃ t : Tableau (X :: Hist) Y, t.IsUni := by
        intro Y Y_in
        apply gameP_general (X :: Hist) Y sP (posOf (X :: Hist) Y) (posOf_isUni _ _) -- the IH
        subst pos_def
        -- The main work is done by the following lemma
        have := winning_of_whatever_other_move (by simp) h
        simp [tableauGame, Game.moves] at this
        exact this _ Y_in
      choose next next_uni using next'
      exact ⟨Tableau.loc nrep nbas (uniLocalTab X) next, uniLocalTab_isUni X, next_uni⟩
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

/-- If Prover has a winning strategy then there is a closed tableau, and it is uniform. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    ∃ tab : Tableau [] X, tab.IsUni := gameP_general [] X s _ (posOf_isUni _ _) h

/-- If Prover has a winning strategy then there is a *uniform* closed tableau,
i.e. one satisfying the conditions U1 and U2. -/
theorem gameP_isUniform (X : Sequent) (s : Strategy tableauGame Prover)
    (h : winning s (startPos X)) : ∃ tab : Tableau [] X, tab.isUniform := by
  obtain ⟨tab, tab_uni⟩ := gameP X s h
  exact ⟨tab, tab_uni.isUniform⟩

end UniGame
