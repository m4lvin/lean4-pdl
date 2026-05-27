import Pdl.TableauGame
import Pdl.AllPdlRule

/-! # From winning strategies to model graphs (Section 6.3)

Lessons learned while working on this file:

- Not all leafs in the BuildTree are backpointers.
  We want open leafs (where builder wins the game) to actually build worlds :-)
  Moreover, free repeats also let builder win.

-/

namespace Simpler

/-! ## BuildTree -/

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

mutual
/-- Winning Strategy Tree for Builder.
At each step, we consider
- ALL rules R that prover may choose, followed immediately by
- ONE of the children then chosen by Builder

The type is actually similar to `Tableau`, but has no history (???) and does allow an open leaf.
There is no .lpr constructor here because we only make a `RuleTree` when Builder wins and
thus we can never reach an lpr (where Prover would win).
For choosing a local tableau end node the mutual `RuleChoice` is needed to avoid the error
"nested inductive datatypes parameters cannot contain local variables". -/
inductive BuildTree : Sequent → Type
  -- Prover chooses local tab, we pick one end node:
  | loc {X} (nbas : ¬ X.basic)
            (next : (lt : LocalTableau X) → BuildChoice (endNodesOf lt))
            : BuildTree X
  /-- Prover chooses PDL rule, never branches, so continue with unique child. -/
  | pdl {X} (bas : X.basic)
            (next : ∀ Y, ∀ _r : PdlRule X Y, BuildTree Y) : BuildTree X
  /-- A leaf / end of the game where we win. -/ -- TODO: add conditions?
  -- free repeat OR basic and no rule applicable -- but what about (L+)?
  | openLeaf {X} : BuildTree X

inductive BuildChoice : List Sequent → Type
  | pick {YS Y} : Y ∈ YS → BuildTree Y → BuildChoice YS
end

/-- Given a winning Builder strategy, compute its `RuleTree`.
TODO: add NEW here: we must start from a Prover position, i.e.
- not allowing BuilderPos.lpr here (easy, was forbidden already anyway as prover wins there.)
- not allowing BuilderPos.ltab because we cannot use BuildTree.loc for a single fixed local tab. -/
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, p⟩) :
    BuildTree X :=
  match p_def : p with
  -- Prover positions:
  | Sum.inl (.nlpRep rp noLpRep) => .openLeaf -- Builder wins rep. ?? maybe we do want history?
  | Sum.inl (.bas nrep bas) => -- prover chooses PDL rule
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.bas nrep bas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      .pdl bas
        (fun newSeq r => buildTree s (stillWin _ (.prPdl r)))
  | Sum.inl (.nbas nrep nbas) => -- prover chooses a local tableau
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.nbas nrep nbas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      .loc nbas <| fun ltX => by
        have ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty
          := by by_contra hyp; sorry -- ??
        -- IDEA: use strategy `s` to choose move `mY` that picks the `Y ∈ endNodeOf ltX`:
        let mY := s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne
        -- We continue the BuildTree with the chosen `Y`:
        refine (@BuildChoice.pick _ mY.val.2.1 ?in_endNodesOf_ltX ?subtree_for_mY)
        · have := mY.prop
          unfold Game.Pos.moves Game.moves tableauGame at this
          simp only at this
          rw [theMoves_iff] at this
          simp at this
          rcases this with ⟨_,_,⟨Y',Y'_in,mY_def⟩⟩
          rw [mY_def]
          simp
          exact Y'_in
        · -- now still need to make a `Move` so we can recursively call `buildTree`.
          have Mov : Move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ mY.1 := by
            have := mY.2
            simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at this
            simp [List.mem_map] at this
            let oY := List.find? -- No more choice thanks to this!
              (fun Y => @decide (⟨_, ⟨_, posOf (X :: H) Y⟩⟩ = mY.val) (instDecidableEqPos _ _))
              (endNodesOf ltX)
            cases oY_def : oY
            · exfalso
              have := List.find?_eq_none.mp oY_def
              grind
            case some Y =>
              unfold oY at oY_def
              have def_mY := List.find?_some oY_def
              simp only [decide_eq_true_eq] at def_mY
              have Y_in := List.mem_of_find?_eq_some oY_def
              have := @Move.buEnd X ltX Y H nrep nbas Y_in
              rw [← def_mY]
              exact this
          -- make recursive call, remains to show that `s` still wins.
          refine @buildTree s _ _ mY.val.2.2 ?_
          -- Note that *two* moves have happened now, one by prover and one by us.
          apply winning_of_winning_move
          exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩ Move.prLocTab
  -- Builder positions:
  | Sum.inr (.lpr _) => by exfalso; simp [winning] at h -- lpr means prover wins, so cannot happen.
  | Sum.inr (.ltab nrep nbas ltX) => by
      -- Seems a bit weird to still have this case. Is it redundant with `(.nbas nrep nbas)` above?
      have ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty := by
        by_contra hyp
        simp_all only [winning, winner, ↓reduceDIte, tableauGame_turn_Builder, other_B_eq_A,
          reduceCtorEq, forall_const]

      -- Builder can use `s` to choose some `Y ∈ endNodeOf ltX`.
      let sY := s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne
      have Mov : Move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ sY.1 := by
        have := sY.2
        simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at this
        simp [List.mem_map] at this
        let oY := List.find? -- No more choice thanks to this!
          (fun Y => @decide (⟨X :: H, ⟨Y, posOf (X :: H) Y⟩⟩ = sY.val) (instDecidableEqPos _ _))
          (endNodesOf ltX)
        cases oY_def : oY
        · exfalso
          have := List.find?_eq_none.mp oY_def
          grind
        case some Y =>
          unfold oY at oY_def
          have def_sY := List.find?_some oY_def
          simp only [decide_eq_true_eq] at def_sY
          have Y_in := List.mem_of_find?_eq_some oY_def
          have := @Move.buEnd X ltX Y H nrep nbas Y_in
          rw [← def_sY]
          exact this
      have stillWin : winning s sY.1 := winning_of_winning_move _ h
      have forTermination : move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ sY.1 := ⟨Mov⟩ -- needed?
      -- No construction here, jsut recursion!?!
      have := buildTree s stillWin
      sorry
      -- .loc nbas ltX
      -- sorry -- BuildTree.BuStep (by simp) Mov (buildTree s stillWin)

termination_by
  tableauGame.wf.2.wrap (⟨H, X, p⟩ : GamePos)
decreasing_by -- show that it's a move
  all_goals sorry

  -- · simp_wf
  --   simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
  --   exact ⟨mov⟩
  -- · simp_wf
  --   simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
  --   exact ⟨mov⟩
  -- · simp_wf
  --   simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
  --   exact forTermination

end Simpler
