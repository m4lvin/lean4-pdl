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
NEW: note the `Sum.inl p` here. This ensure we start tree building from a Prover position, i.e.
- not allowing BuilderPos.lpr here (easy, was forbidden already anyway as prover wins there.)
- not allowing BuilderPos.ltab because we cannot use BuildTree.loc for a single fixed local tab. -/
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, Sum.inl p⟩) :
    BuildTree X :=
  match p_def : p with
  -- Prover positions:
  | (.nlpRep rp noLpRep) => .openLeaf -- Builder wins rep. ?? maybe we do want history?
  | (.bas nrep bas) => -- prover chooses PDL rule
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.bas nrep bas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      .pdl bas <| fun newSeq r => by
        -- deal with the result of `posOf` here already because we can only make a
        -- recursive call if we again have a ProverPos.
        cases newPos_def : posOf (X :: H) newSeq
        case inl newP =>
          refine @buildTree s (X :: H) newSeq newP (stillWin ⟨_, _, Sum.inl newP⟩ ?_)
          rw [← newPos_def]
          exact @Move.prPdl _ _ H nrep bas r
        case inr newBP =>
          exfalso
          -- IDEA: The only BuilderPos resulting from `posOf` is an lpr ...
          rcases posOf_eq_inr_then_lpr newPos_def with ⟨lpr, newBP_def⟩
          have := stillWin ⟨_, _, posOf (X :: H) newSeq⟩ (Move.prPdl r)
          rw [newPos_def, newBP_def] at this
          -- .. where prover would win, so that cannot happen here.
          simp [winning] at this
  | (.nbas nrep nbas) => -- prover chooses a local tableau
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
          -- NEW: also need case distinction here to ensure mY.val.2.2 is a ProverPos for recursion?
          match mY_def : mY.val.2.2 with
          | .inl myP =>
            -- make recursive call, remains to show that `s` still wins.
            refine @buildTree s _ _ myP ?_
            rw [← mY_def]
            -- Note that *two* moves have happened now, one by prover and one by us.
            apply winning_of_winning_move
            exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩ Move.prLocTab
          | .inr mY_BP =>
              exfalso -- fingers crossed ;-)
              -- (This is different than above, cannot use `posOf_eq_inr_then_lpr` immediately.)
              -- IDEA: mY is result of Move.buEnd, so if mY is a BuilderPos then it is an lpr.
              rcases mY with ⟨mY, mY_in⟩ -- PROBLEM: here we also lose the def of mY :-/
              rcases mY with ⟨newH, Y, posY⟩
              cases Mov -- also clears newH and posY // only possible after the rcases?
              case buEnd nbas' nrep' Y_in =>
              simp at *
              -- Now we can use it, but should we?
              rcases posOf_eq_inr_then_lpr mY_def with ⟨lpr, mY_BP_def⟩
              subst mY_BP_def
              -- Want to use stillWin now, but we are in the setting where two moves happened!?
              have := stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩ Move.prLocTab
              -- ... ?
              apply winning_of_winning_move (by simp) at this
              -- Here we need the lost information that mY is a winning choice made by `s`.
              -- simp [winning] at this
              sorry

termination_by
  tableauGame.wf.2.wrap (⟨H, X, Sum.inl p⟩ : GamePos)
decreasing_by -- show that it's a move
  -- TODO but now it might be 2 moves! Use transitive closure? (it still must be wellfounded)
  all_goals
    simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    try exact forTermination
  all_goals
    sorry

end Simpler
