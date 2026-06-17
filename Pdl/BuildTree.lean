import Pdl.TableauGame
import Pdl.AllPdlRule
import Pdl.Syntax

/-! # From winning strategies to model graphs (Section 6.3)

Lessons learned while working on this file:

- Not all leafs in the BuildTree are backpointers.
  We want open leafs (where builder wins the game) to actually build worlds :-)
  Moreover, free repeats also let builder win.

-/

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
  -- TODO: add that there must be at least one applicable PdlRule?
  | pdl {H X} (bas : X.basic)
            (next : ∀ Y, ∀ _r : PdlRule X Y, BuildTree (X :: H) Y) : BuildTree H X
  /-- Free repeat means builder wins. -/
  | freeRepeat {H X} : FreeRepeat H X → BuildTree H X
  /-- Leaf that is (might be?!) not a repeat, but no rules can be applied. -/
  | openLeaf {H X} : BuildTree H X
  -- TODO: add `(bas : X.basic)` for "no local rules" and somehow say "no PDL rules"?
  -- small worry but what about (L+) (L-), one of which is always applicable?
  -- Well, then it would lead to a free repeat!?

inductive BuildChoice : History → Sequent → List Sequent → Type
  | pick {H X YS Y} : Y ∈ YS → BuildTree (X :: H) Y → BuildChoice H X YS
end

mutual
/-- Manual replacement for `sizeOf (bt : BuildTree)` so we also count the `next` parts. -/
def BuildTree.size : BuildTree H X → Nat
  | .loc _ next => 1 + ((LocalTableau.all X).map (fun lt => (next lt).size)).sum
  | .pdl _ next => 1 + ((PdlRule.all X).map (fun ⟨Y,r⟩ => (next Y r).size)).sum
  | .freeRepeat _ => 1
  | .openLeaf => 1

def BuildChoice.size : BuildChoice H X YS → Nat
  | .pick _ bt_Y => bt_Y.size
end

@[simp]
lemma BuildChoice.fst_eq_H {H X YS} {bc : BuildChoice H X YS} : bc.1 = H := by
  cases bc
  rfl

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

/-- Inspired by `PathIn.length`. Counting the steps made by a `Match` in a `BuildTree`.
Note that such a step may be combinations of a prover and a builder move. -/
@[simp]
def Match.length {H : History} {X : Sequent} {bt : BuildTree H X} : Match bt → Nat
  | .nil => 0
  | .loc tail => tail.length + 1
  | .pdl tail => tail.length + 1

def Match.btAt {H X} {bt : BuildTree H X} : Match bt → Σ H' Y, BuildTree H' Y
| .nil => ⟨_, _, bt⟩
| .loc tail => btAt tail
| .pdl tail => btAt tail

/- All possible Matches in a given BuildTree. -/
def Match.all {H X} : (bt : BuildTree H X) → List (Match bt)
  | .loc nbas next =>
      Match.nil ::
      (LocalTableau.all X >>= fun ltX => return Match.loc (← Match.all (next ltX).6))
  | .pdl bas next =>
      Match.nil ::
      (PdlRule.all X >>= fun ⟨Y,r⟩ => return Match.pdl (← (Match.all (next Y r))))
  | .freeRepeat fr => [ .nil ]
  | .openLeaf => [ .nil ]
termination_by
  bt => bt.size
decreasing_by
  · simp [BuildTree.size]
    have : (next ltX).6.size ∈ ((LocalTableau.all X).map (fun lt => (next lt).6.size)) := by
      simp only [List.mem_map]
      use ltX, LocalTableau.all_spec
    have := List.le_sum_of_mem this
    have : ∀ lt, (next lt).size = (next lt).6.size := fun lt => by
      cases next lt; simp [BuildChoice.size]
    simp_rw [this]
    grind
  · simp only [BuildTree.size]
    have : (next Y r).size ∈ ((PdlRule.all X).map (fun ⟨Y,r⟩ => (next Y r).size)) := by
      simp only [List.mem_map, Sigma.exists]
      use Y, r, PdlRule.all_spec bas _
    have := List.le_sum_of_mem this
    grind

theorem Match.all_spec {H X} (bt : BuildTree H X) m :
    m ∈ Match.all bt := match m with
  | nil => by cases bt <;> grind [Match.all]
  | @loc _ _ nbas next lt tail => by
    have IH := Match.all_spec _ tail
    rw [Match.all]
    simp
    refine ⟨lt, ?_⟩
    -- something like a is an instance of ltX b/c LocalTableau.all_spec
    -- something like lt is in Match.all (next a).6 and therefore an instance of __do_lift
    -- something like bc lt is an instance of __do_lift, lt.loc is an instance of __do_lift.loc
    sorry
  | @pdl _ _ bas next Y r tail => by
    have IH := Match.all_spec _ tail
    rw [Match.all]
    simp
    refine ⟨_, r, PdlRule.all_spec bas r, ?_⟩
    refine ⟨tail, IH, rfl, ?_⟩ -- heterogeneous equality left here
    simp

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

lemma Match.Edge.wf {H X} {bt : BuildTree H X} :
    WellFounded (fun (m n : Match bt) => Nonempty (Match.Edge m n)) := by
  -- IDEA: similar to `matchesFinite`, but maybe easier?
  -- Still use these things:
  -- - `Match` is a finite type
  -- - the transitive closure of `Match.Edge` is irreflexive
  sorry

/-- This edge between matches is a modal step.
To even say this `BuildTree` must contain the rule data. -/
def Match.Edge.isModal {H X} {bt : BuildTree H X} {m n : Match bt} : Match.Edge m n → Prop
  | Sum.inl _ => False -- local edges are never modal steps.
  | Sum.inr ⟨_, _, _, _, _, r, _, _⟩ =>  PdlRule.isModal r

instance instDecidableMatchEdgeIsModal {e : Match.Edge m n} : Decidable (e.isModal) :=
  match e with
  | Sum.inl _ => by apply isFalse; simp [Match.Edge.isModal]
  | Sum.inr ⟨_, _, _, _, _, r, _, _⟩ => by
      simp [Match.Edge.isModal]; exact instDecidablePdlRuleIsModal

def Match.isOpenLeaf {H X} {bt : BuildTree H X} {m : Match bt} : Prop :=
  match (btAt m) with | ⟨_, _, .openLeaf⟩ => True | _ => False

def Match.isFreeRepeat {H X} {bt : BuildTree H X} (m : Match bt) : Prop :=
  match (btAt m) with | ⟨_, _, .freeRepeat _⟩ => True | _ => False

/-- If `m` ends at an open leaf, then it cannot have an edge to any `n`. -/
lemma Match.isOpenLeaf_no_edge {H X} {bt : BuildTree H X} (m : Match bt) (h : m.isOpenLeaf) :
    ∀ n, ¬ Nonempty (Match.Edge m n) := by -- EASY as expected :)
  intro n
  unfold Match.isOpenLeaf at h
  rintro ⟨m_n⟩
  cases m_n <;> grind

-- Maybe Match.toHistory is not actually needed? Skipping it for now.

/-- Rewind a `Match`, i.e. go back up inside `bt` by `k` steps.
The + 1 is there because going back 0 steps does nothing. -/
def Match.rewind {H X} {bt : BuildTree H X} : (m : Match bt) → (k : Fin (m.length + 1)) → Match bt
| .nil, 0 => .nil
| .nil, ⟨k+1,k_h⟩ => by exfalso; simp at k_h
| .loc tail, k => Fin.lastCases (.nil) (Match.loc ∘ tail.rewind) k
| .pdl tail, k => Fin.lastCases (.nil) (Match.pdl ∘ tail.rewind) k

-- move up later?
def BuildTree.isFreeRepeat {H X} : BuildTree H X → Prop
  | BuildTree.freeRepeat _ => True
  | _ => False

def BuildTree.getFreeRepeat {H X} {bt : BuildTree H X}
    (h : bt.isFreeRepeat) : FreeRepeat H X := by
  unfold isFreeRepeat at h
  cases bt <;> simp at *
  case freeRepeat fr => exact fr

lemma Match.btAt_newHist_length_eq_length_plus_oldHist {H X} {bt : BuildTree H X} (m : Match bt) :
    m.btAt.1.length = m.length + H.length :=
  match m with
  | nil => by simp [btAt]
  | @loc _ _ _ next lt tail => by
    have IH := Match.btAt_newHist_length_eq_length_plus_oldHist tail
    unfold btAt
    rw [IH]
    simp
    grind
  | pdl tail => by
    have IH := Match.btAt_newHist_length_eq_length_plus_oldHist tail
    simp
    unfold btAt
    rw [IH]
    simp
    omega
termination_by
  m.length

lemma Match.isFreeRepeat_iff {H X} {bt : BuildTree H X} {m : Match bt} :
    m.isFreeRepeat ↔ (btAt m).2.2.isFreeRepeat := by
  unfold BuildTree.isFreeRepeat Match.isFreeRepeat
  grind

/-- Roll back to the companion. Only possibe if we started with H=[] so we know the root. -/
def Match.companionOf {X} {bt : BuildTree [] X} (m : Match bt)
  (h : m.isFreeRepeat) : Match bt :=
    match BuildTree.getFreeRepeat (Match.isFreeRepeat_iff.eq ▸ h) with
    -- The free repeat says "go k steps back" where k < length of history at `m`.
    | ⟨⟨k, k_lt⟩ , same_and_free⟩ =>
      -- But to rewind m we need a k < length of m itself plus 1
      m.rewind ⟨k, by grind [Match.btAt_newHist_length_eq_length_plus_oldHist]⟩

/-- The repeat ♥ companion relation on `Match`. -/
def Match.companion {X} {bt : BuildTree [] X} (m n : Match bt) : Prop :=
  ∃ (h : m.isFreeRepeat), n = Match.companionOf m h

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

/-! ## Pre-states (Def 6.13)

As possible worlds for the model graph we want to define *maximal* paths inside the build tree
that do not contain `(M)` steps.

In the paper pre-states are allowed to be of the form π;π' when π ends at a repeat and π' is a
maximal prefix of the path from the companion to that repeat. Here in `PreState` and `PreStateP`
we only store the π part of such pre-states, because the π' is then uniquely determined by π.
-/

/-- A pre-state-part starting at `m` is any path in `bt : BuildTree` consisting of non-(M) `edge`s
and stopping at a leaf or at an (M) application. (No `Match.companion` steps here, see note above.)
-/
inductive PreStatePart {H X} (bt : BuildTree H X) : (m : Match bt) → Type
| edge {m n} : (e : Match.Edge m n) → ¬ e.isModal → PreStatePart bt n → PreStatePart bt m
| stopAtM {m n} : (e : Match.Edge m n) → e.isModal → PreStatePart bt m
| stopAtOpenLeaf {m} : m.isOpenLeaf → PreStatePart bt m
| stopAtFreeRepeat {m} : (h : m.isFreeRepeat) → PreStatePart bt m
 -- IDEA: PreStatePart bt (Match.companionOf m h) →

/-- Collect all `PreStateP`s from a given `m` onwards. -/
def BuildTree.allPreStateParts {H X0} (bt : BuildTree H X0) (m : Match bt) :
    List (PreStatePart bt m) :=
  match m_def : m.btAt with
  | ⟨H', X, .loc nbas next⟩ => do
      let ltX ←  @LocalTableau.all X
      -- IDEA: `map next` but the result type is dependent.
      have := next ltX
      -- After that make recursive call. But better do `.pdl` case below first, hopefully easier?
      sorry
  | ⟨H', X, .pdl bas next⟩ => do
      let ⟨Y,r⟩ ← @PdlRule.all X
      let := next Y r
      -- Now wrap up each `r` into a `Match.Edge`:
      let n : Match bt := m.append sorry -- use `append` here or better something else?
      have e : Match.Edge m n := .inr sorry
      if isMo : e.isModal then
        return PreStatePart.stopAtM e isMo
      else
        -- If we have a non-modal step, use recursion to get tail and then use PreStatePart.edge.
        let tail ← BuildTree.allPreStateParts bt n
        return PreStatePart.edge e isMo tail
  | ⟨H', X, .freeRepeat fr⟩ => [ .stopAtFreeRepeat (by simp [Match.isFreeRepeat]; grind) ]
  | ⟨H', X, .openLeaf⟩ => [ .stopAtOpenLeaf (by simp [Match.isOpenLeaf]; grind) ]
termination_by
  Match.Edge.wf.wrap m
decreasing_by
  sorry

lemma BuildTree.allPreStateParts_spec {H X} {bt : BuildTree H X} {m : Match bt}
    {π : PreStatePart bt m} : π ∈ bt.allPreStateParts m := by
  sorry

/-- A pre-state is a maximal pre-state-part, i.e. starting at the root or just after (M).

WORRY: should `fromRoot` also have a condition about `H` being empty, i.e. the start of the game?
-/
inductive PreState {H X} (bt : BuildTree H X) : Type
| fromRoot : PreStatePart bt .nil → PreState bt
| fromMod {o m} : (e : Match.Edge o m) → e.isModal → PreStatePart bt m → PreState bt

/-- Collect all `PreState`s for a given `BuildTree`. -/
def BuildTree.allPreStates {H X} (bt : BuildTree H X) : List (PreState bt) :=
  -- IDEAS: use `Match.all`, then filter by "is root or is just after modal", then
  -- apply  BuildTree.allPreStateParts.
  -- (Match.all bt).filter (fun m => m = .nil ∨ )
  -- ... (bt.allPreStateParts .nil).map .fromRoot
  sorry

lemma BuildTree.allPreStates_spec {H X} {bt : BuildTree H X} :
    ∀ π : PreState bt, π ∈ bt.allPreStates := by
  unfold allPreStates
  intro π
  have := @BuildTree.allPreStateParts_spec
  -- should be easy once `BuildTree.allPreStates` is done?
  sorry

-- Notes:
-- - PreStatePart.forms
-- - change output type to AnyFormula
-- - Sequent.anyForms to collect


/-- - Given a `PreStatePart` ending at a repeat, go to companion,
then return the PreStatePart from there staying in the same Match. -/
def PreStartPart.companionPart {m : Match bt} (h : m.isFreeRepeat) (π : PreStatePart bt m) :
    π = PreStatePart.stopAtFreeRepeat h →
    PreStatePart bt (Match.companionOf m h) :=
  sorry

/-- Collect formulas in a pre-state. The non-loaded part of Λ(π) in paper.

TODO: If the pre-state ends in a repeat, also include formulas in the path from companion to (M).

QUESTION: Can we collect loaded formulas here by unloading them?
Or would that make the loaded case of `PreState.pdlFormCase` unsayable?
-/
def PreState.forms {bt : BuildTree H X} : PreState bt → List Formula := by
  intro π
  cases π
  case fromRoot π' =>
    cases π'
    case edge n tail e notModal =>
      have := Match.btAt n
      -- IDEA: have rest := PreStatePart.forms tail
      sorry
    case stopAtFreeRepeat =>
      have := @PreStartPart.companionPart -- also collect forms from there!
      sorry
    all_goals
      sorry
  case fromMod =>
    sorry

/-- Collect formulas in a pre-state. The loaded part of Λ(π) in paper. -/
def PreState.lforms : PreState bt → List NegLoadFormula := sorry

def PreState.last : PreState bt → Sequent := sorry

def principalFormulaForLocalRule :  LocalRule X YS -> AnyFormula
  | .oneSidedL orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ =>  (φ ⋀ ψ)
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _ => ~⌈α⌉φ
        | .box α φ _ => ⌈α⌉φ
  | .oneSidedR orule _ =>
      match orule with
        | .bot      => Formula.bottom
        | .con φ ψ => φ ⋀ ψ
        | .not φ => φ
        | .neg φ => ~~φ
        | .nCo φ ψ => ~(Formula.and φ ψ)
        | .dia α φ _  => ~⌈α⌉φ
        | .box α φ _   => ⌈α⌉φ
  | .LRnegL φ => φ
  | .LRnegR φ => φ
  | .loadedL φ _ _ => φ
  | .loadedR φ _ _ => φ



/-- TODO Lemma 6.14 -/
lemma PreState.formsCases {π : PreState bt} : φ ∈ π.forms →
      (φ.basic ∧ φ ∈ π.last) -- NOTE: the `∈` is not dealing with loaded formulas here!
    ∨ (sorry) := by -- TODO how to say `φ is principal later?`
    -- Or can we say something else / phrase it as closure condition about π.forms directly?
  sorry

/-- WIP Lemma 6.15 *un*loaded case -/
lemma PreState.pdlFormCase {H X} {bt : BuildTree H X} {π : PreState bt} {α φ} :
    ¬ α.isAtomic → (~⌈α⌉φ) ∈ π.forms →
      ∃ Xδ ∈ Hset α, Xδ.1 ∪ [~ Formula.boxes Xδ.2 φ] ⊆ π.forms := by
  sorry

/-
TODO: This needs a case distinction for the AnyFormular, similar to `YsetLoad` and `YsetLoad'`.
/-- WIP Lemma 6.15 *loaded* case -/
lemma PreState.loadedFormCase {H X} {bt : BuildTree H X} {π : PreState bt} {α φ} :
    ¬ α.isAtomic → (~'⌊α⌋φ) ∈ π.lforms →
      ∃ Xδ ∈ Hset α, Xδ.1 ∪ [~ LoadFormula.boxes Xδ.2 φ] ⊆ π.forms := by
  sorry
-/

/-- WIP Lemma 6.16: pre-states are saturated and locally consistent, their last node is basic. -/
lemma PreState.locConsSatBas {H X} {bt : BuildTree H X} (π : PreState bt) :
    saturated (π.forms).toFinset
    ∧ locallyConsistent (π.forms).toFinset
    ∧ π.last.basic := by
  -- define `PreState.forms` first.
  sorry

/-- Definition 6.17 to get model graph from strategy tree. -/
@[simp]
def BuildTree.toModel {H X} (bt : BuildTree H X) :
    (Σ W : Finset (Finset Formula), KripkeModel W) :=
  ⟨ ((bt.allPreStates).map (List.toFinset ∘ PreState.forms)).toFinset -- W
  , { val := fun X p => Formula.atom_prop p ∈ X.1 -- valuation V(p)
    , Rel := fun a X Y => -- relation Rₐ
        ∃ φ, (~⌈·a⌉φ) ∈ X.1 ∧ (projection a X.1.toList).toFinset ∪ {~φ} ⊆ Y.1 }⟩

/-- WIP Lemma 6.18

QUESTION: which `R` can we use here in order to use `Modelgraphs.Q`?
-/
lemma PreState.diamondExistence {φ : AnyFormula} {π : PreState bt} : (~'⌊α⌋φ) ∈ π.lforms →
    -- QUESTION: what to say about `π` here and what to say about node `t` lying on `π`?
    ∃ t : Match bt,
        AnyNegFormula.mem_Sequent (t.btAt).2.1 (~''φ)
      ∧ ∃ ρ : PreState bt, ∃ u : Match bt,
        -- TODO: t < u
        -- TODO: missing loaded formulas below
        @Modelgraphs.Q sorry sorry α ⟨π.forms.toFinset, sorry⟩ ⟨ρ.forms.toFinset, sorry⟩ := by
  sorry

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded

-- TODO Lemma 6.20: diamond existence lemma for pre-states

/-! ## Model graph of pre-states -/

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph.
Uses `BuildTree.toModel`. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), ∃ Z ∈ WS, X.toFinset ⊆ Z := by
  unfold startPos at h
  rcases posOf_for_startPos X with ⟨proPos, posOf_def⟩
  let bt := buildTree s (posOf_def ▸ h)
  let WS := bt.toModel.1
  let M := bt.toModel.2
  refine ⟨WS, ⟨M, ⟨?a, ?b, ?c, ?d⟩⟩, ?X_in⟩
  -- show the model graph properties
  case a =>
    rintro ⟨X, X_in⟩
    unfold WS at X_in
    simp at X_in
    rcases X_in with ⟨π, in_all, def_X⟩
    have := PreState.locConsSatBas π-- using Lemma 6.16 for (i)
    simp_all
  -- "(b, c) will follow immediately from the definition"
  case b =>
    simp_all [M]
  case c =>
    intro X Y a φ X_a_Y aφ_in_X -- pick any ⌈a⌉φ
    simp only [M] at X_a_Y
    rcases X_a_Y with ⟨ψ, in_X, sub_Y⟩ -- relation was witnessed by ⌈a⌉ψ
    apply sub_Y -- show that φ is in projection
    simp_all
  case d =>
    simp
    intro w w_in α φ in_w
    -- "The main challenge" :-)
    -- Need Lemmas 6.18 to 6.19 about pre-states here.
    sorry
  case X_in =>
    unfold WS
    simp
    -- need actual def for `BuildTree.allPreStates` first
    -- use the .fromRoot pre-state
    sorry
