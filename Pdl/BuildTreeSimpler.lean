import Pdl.TableauGame
import Pdl.AllPdlRule

/-! # From winning strategies to model graphs (Section 6.3)

Lessons learned while working on this file:

- Not all leafs in the BuildTree are backpointers.
  We want open leafs (where builder wins the game) to actually build worlds :-)
  Moreover, free repeats also let builder win.

-/

namespace Simpler -- delete me when replacing BuildTree.lean with this file

/-! ## BuildTree -/

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- A free repeat is a non-loaded sequent that occured before. -/
def FreeRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k).multisetEqTo X ∧ ¬ X.isLoaded)

mutual
/-- Winning Strategy Tree for Builder.
At each step, we consider
- ALL rules R that prover may choose, followed immediately by
- ONE of the children then chosen by Builder

The type is actually similar to `Tableau`, as it also uses a history, but it does allow open leaves.
For choosing a local tableau end node the mutual `RuleChoice` is needed to avoid the error
"nested inductive datatypes parameters cannot contain local variables".
Instead of the .lpr constructor here we have .fpr because we only make a `RuleTree` when Builder
wins and thus we can never reach an lpr where Prover would win, but do allow free repeats.
As in `Tableau` note that the history is stored in reverse. -/
inductive BuildTree : History → Sequent → Type
  /-- Prover chooses local tab, we pick one end node. -/
  | loc {H X} (nbas : ¬ X.basic)
            (next : (lt : LocalTableau X) → BuildChoice H X (endNodesOf lt))
            : BuildTree H X
  /-- Prover chooses PDL rule, never branches, so continue with unique child. -/
  | pdl {H X} (bas : X.basic)
            (next : ∀ Y, ∀ _r : PdlRule X Y, BuildTree (X :: H) Y) : BuildTree H X
  /-- A leaf / end of the game where we win. -/ -- TODO: add conditions?
  -- free repeat OR basic and no rule applicable -- but what about (L+)?
  -- NOTE:for free repeats we might need to get their "companion", so maybe we do need history?!
  | freeRepeat {H X} : FreeRepeat H X → BuildTree H X
  | openLeaf {H X} : BuildTree H X

inductive BuildChoice : History → Sequent → List Sequent → Type
  | pick {H X YS Y} : Y ∈ YS → BuildTree (X :: H) Y → BuildChoice H X YS
end

/-- Given a winning Builder strategy, compute its `RuleTree`.
NEW: note the `Sum.inl p` here. This ensure we start tree building from a Prover position, i.e.
- not allowing BuilderPos.lpr here (easy, was forbidden already anyway as prover wins there.)
- not allowing BuilderPos.ltab because we cannot use BuildTree.loc for a single fixed local tab. -/
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, Sum.inl p⟩) :
    BuildTree H X :=
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
          have _forTermination : Relation.TransGen tableauGame.wf.1 ⟨_,_, .inl newP⟩ ⟨_,_, .inl p⟩
            := by rw [p_def, ← newPos_def]; exact Relation.TransGen.single ⟨Move.prPdl r⟩
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
        have ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty :=
          winning_has_moves (by simp) <|
            stillWin ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩ Move.prLocTab
        -- IDEA: use strategy `s` to choose move `mY` that picks the `Y ∈ endNodeOf ltX`:
        -- We want to define mY and then do rcases, but keep the information how it was defined.
        let mY_raw := s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne
        have mY_def : mY_raw.1 = s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne := rfl
        rcases mY_raw with ⟨mY, mY_prop⟩
        simp at mY_def
        -- We continue the BuildTree with the chosen `Y`:
        refine (@BuildChoice.pick _ _ _ mY.2.1 ?in_endNodesOf_ltX ?subtree_for_mY)
        · have := mY_prop
          unfold Game.Pos.moves Game.moves tableauGame at this
          simp only at this
          rw [theMoves_iff] at this
          simp at this
          rcases this with ⟨_,_,⟨Y',Y'_in,mY_def⟩⟩
          rw [mY_def]
          simp
          exact Y'_in
        · -- now still need to make a `Move` so we can recursively call `buildTree`.
          have Mov : Move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ mY := by
            simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at mY_prop
            simp [List.mem_map] at mY_prop
            let oY := List.find? -- No more choice thanks to this!
              (fun Y => @decide (⟨_, ⟨_, posOf (X :: H) Y⟩⟩ = mY) (instDecidableEqPos _ _))
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
          rcases mY with ⟨H', Y, newP⟩ -- Happy because this does not lose mY_def.
          have H'_def : H' = X :: H := by
            simp [Game.Pos.moves, tableauGame, Game.moves] at mY_prop
            grind
          -- Case distinction here to ensure newP from mY is a ProverPos for recursion.
          match newP with
          | .inl myP =>
            simp only
            -- Make recursive call:
            have _forTermination : Relation.TransGen tableauGame.wf.1 ⟨_,_, .inl myP⟩ ⟨_,_, .inl p⟩
              :=  by
                unfold WellFoundedRelation.rel Game.wf tableauGame
                simp
                apply @Relation.TransGen.trans _ _ _
                  ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩
                · exact Relation.TransGen.single ⟨Mov⟩
                · rw [p_def]; exact Relation.TransGen.single ⟨Move.prLocTab⟩
            refine H'_def ▸ @buildTree s H' Y myP ?_
            -- (Remaining goal is nicer after doing `H'_def ▸` on the outside and not on `myP`.)
            rw [mY_def]
            -- Note that *two* moves have happened now, one by prover and one by Builder using `s`.
            -- Remains to show that `s` still wins.
            apply winning_of_winning_move
            exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩ Move.prLocTab
          | .inr mY_BP =>
              exfalso -- fingers crossed ;-)
              subst H'_def
              -- (This is different than above, cannot use `posOf_eq_inr_then_lpr` immediately.)
              -- OLD IDEA: mY is result of Move.buEnd, so if mY is a BuilderPos then it is an lpr.
              -- cannot do `cases Mov` -- Dependent elimination failed: Failed to solve equation
              -- `Mov` goes from a BuilderPos.ltab to `mY_BP`, so `mY_BP` must be a `posOf` result.
              -- Distinguish cases what the BP we reach can be.
              cases mY_BP
              case lpr lr => -- possible
                suffices winning s ⟨X :: H, ⟨Y, Sum.inr (BuilderPos.lpr lr)⟩⟩ by
                  simp [winning] at this
                rw [mY_def]
                apply @winning_of_winning_move _ _ s
                exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩ Move.prLocTab
              case ltab => -- impossible
                clear mY_def mY_prop newP
                have := mem_theMoves_of_move (⟨Mov⟩)
                absurd this
                simp [theMoves]
                intro Z Z_in
                have := endNodesOf_basic Z_in
                grind
termination_by
  -- Might need 2 moves, so we use the transitive closure (which is still wellfounded)
  tableauGame.wf.2.transGen.wrap (⟨H, X, Sum.inl p⟩ : GamePos)
decreasing_by
  all_goals
    simp_wf
    rw [← p_def]
    exact _forTermination

/-! ## Matches -/

/-- A match is a path inside a `BuildTree`. Analogous to `PathIn` for `Tableau`. In Game Theory
this could be called a "rollout", but note that it stays within the given Builder strategy tree
and it is not tracking all intermediate game positions. -/
inductive Match : ∀ {H : History} {X : Sequent}, BuildTree H X → Type
  | nil {bt} : Match bt
  | loc {nbas next lt} : Match (next lt).6 → Match (BuildTree.loc nbas next)
  | pdl {bas next Y r} : Match (next Y r) → Match (BuildTree.pdl bas next)

/-
-- TODO, but NOW do not use `LocalAll` and `AllPdlRule` for this probably.
-- Wait, where are these actually used at the moment or will they be needed later?

def BuildTree.all_Match (bt : BuildTree X) : List (Match bt) := sorry

theorem BuildTree.all_Match_spec (bt : BuildTree X) :
    ∀ m, m ∈ bt.all_Match := by
  sorry
-/

/-- Inspired by `PathIn.length`. Note that this only counts prover steps.
OLD worry here that was `prLocTab` gets counted but did not make `pos.1` longer. Now OKAY maybe? -/
@[simp]
def Match.length {H : History} {X : Sequent} {bt : BuildTree H X} : Match bt → Nat
  | .nil => 0
  | .loc tail => tail.length + 1
  | .pdl tail => tail.length + 1

def Match.btAt {H X} {bt : BuildTree H X} : Match bt → Σ H' Y, BuildTree H' Y
| .nil => ⟨_, _, bt⟩
| .loc tail => btAt tail
| .pdl tail => btAt tail

-- TODO lemmas like those about `tabAt` and `nodeAt`?

def Match.append {H X} {bt : BuildTree H X} :
    (m1 : Match bt) → (m2 : Match (btAt m1).2.2) → Match bt
| .nil, m2 => m2
| .loc tail, m2 => .loc (append tail m2)
| .pdl tail, m2 => .pdl (append tail m2)

-- TODO lemmas like those about `PathIn.append`?

@[grind]
structure Match.locEdge (m n : Match bt) where
  H : History
  mY : Sequent
  nbas : _
  next : (lt : LocalTableau mY) → BuildChoice H mY (endNodesOf lt)
  lt : LocalTableau mY
  btAt_m_def : btAt m = ⟨H, mY, @BuildTree.loc _ mY nbas next⟩
  btAt_n_def : btAt n = ⟨(next lt).2 :: (next lt).1, (next lt).4, (next lt).6⟩

@[grind]
structure Match.pdlEdge (m n : Match bt) where
  H : History
  mX : Sequent
  nY : Sequent
  bas : mX.basic
  next : ∀ Y, ∀ _r : PdlRule mX Y, BuildTree (mX :: H) Y
  r : PdlRule mX nY
  btAt_m_def : btAt m = ⟨_, mX, @BuildTree.pdl H mX bas next⟩
  btAt_n_def : btAt n = ⟨_, _, next nY r⟩

/-- The parent-child relation ⋖_𝕋 in a Builder strategy tree. -/
def Match.Edge (m n : Match bt) : Type := Match.locEdge m n ⊕ Match.pdlEdge m n

/-- This edge between matches is a modal step.
To even say this `BuildTree` must contain the rule data. -/
def Match.Edge.isModal {H pos} {bt : BuildTree H pos} {m n : Match bt} : Match.Edge m n → Prop
  | Sum.inl _ => False -- local edges are never modal steps.
  | Sum.inr ⟨_, _, _, _, _, r, _, _⟩ =>  PdlRule.isModal r

def Match.isLeaf {H pos} {bt : BuildTree H pos} {m : Match bt} : Prop :=
  match (btAt m) with | ⟨_, _, .openLeaf⟩ => True | _ => False

/-- If `m` ends at a leaf, then it cannot have an edge to any `n`. -/
lemma Match.isLeaf_no_edge {H pos} {bt : BuildTree H pos} (m : Match bt) (h : m.isLeaf) :
    ∀ n, ¬ Nonempty (Match.Edge m n) := by -- EASY as expected :)
  intro n
  unfold Match.isLeaf at h
  rintro ⟨m_n⟩
  cases m_n <;> grind

-- QUESTION: Do we need to be able to roll back to repeats in a `BuildTree`??

-- Maybe Match.toHistory is not actually needed?

/-- Rewind a `Match`, i.e. go back up inside `bt` by `k` steps. -/
def Match.rewind {H pos} {bt : BuildTree H pos} :
    (m : Match bt) → (k : Fin (m.length + 1)) → Match bt
| .nil, 0 => .nil
| .nil, ⟨k+1,k_h⟩ => by exfalso; simp at k_h
| .loc tail, k => Fin.lastCases (.nil) (Match.loc ∘ tail.rewind) k
| .pdl tail, k => Fin.lastCases (.nil) (Match.pdl ∘ tail.rewind) k


end Simpler -- delete me when replacing BuildTree.lean with this file
