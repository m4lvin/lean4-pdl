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

/-
-- TODO, but NOW do not use `LocalAll` and `AllPdlRule` for this probably.
-- Wait, where are these actually used at the moment or will they be needed later?

def BuildTree.all_Match (bt : BuildTree X) : List (Match bt) := sorry

theorem BuildTree.all_Match_spec (bt : BuildTree X) :
    ∀ m, m ∈ bt.all_Match := by
  sorry
-/

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
def Match.Edge.isModal {H X} {bt : BuildTree H X} {m n : Match bt} : Match.Edge m n → Prop
  | Sum.inl _ => False -- local edges are never modal steps.
  | Sum.inr ⟨_, _, _, _, _, r, _, _⟩ =>  PdlRule.isModal r

def Match.isLeaf {H X} {bt : BuildTree H X} {m : Match bt} : Prop :=
  match (btAt m) with | ⟨_, _, .openLeaf⟩ => True | _ => False

/-- If `m` ends at a leaf, then it cannot have an edge to any `n`. -/
lemma Match.isLeaf_no_edge {H X} {bt : BuildTree H X} (m : Match bt) (h : m.isLeaf) :
    ∀ n, ¬ Nonempty (Match.Edge m n) := by -- EASY as expected :)
  intro n
  unfold Match.isLeaf at h
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

lemma Match.btAt_hist_length_eq_length_succ {H X} {bt : BuildTree H X} (m : Match bt) :
    m.btAt.1.length = m.length + H.length := by
  rcases m_def : m
  case nil =>
    simp [btAt]
  case loc nbas ltX next tail =>
    have _forTermination : tail.length < m.length := by subst m_def; simp
    have IH := @Match.btAt_hist_length_eq_length_succ _ _ (next ltX).6 tail
    unfold btAt
    rw [IH]
    simp
    grind
  case pdl Y bas r next tail =>
    have _forTermination : tail.length < m.length := by subst m_def; simp
    have IH := @Match.btAt_hist_length_eq_length_succ _ _ _ tail
    simp
    unfold btAt
    rw [IH]
    simp
    omega
termination_by
  m.length
decreasing_by
  all_goals
    simp_wf
    convert _forTermination
    subst_eqs
    simp
    -- annoying HEq business, maybe restate lemma with m.btAt = ... instead of using .1 field?
    sorry

/-- Roll back to the companion. Only possibe if we started with H=[] so we know the root. -/
def Match.companionOf {X} {bt : BuildTree [] X} (m : Match bt)
  (h : (btAt m).2.2.isFreeRepeat) : Match bt :=
    match BuildTree.getFreeRepeat h with
    -- The free repeat says "go k steps back" where k < length of history at `m`.
    | ⟨⟨k, k_lt⟩ , same_and_free⟩ =>
      -- But to rewind m we need a k < length of m itself plus 1
      m.rewind ⟨k, by grind [Match.btAt_hist_length_eq_length_succ]⟩

/-- The repeat ♥ companion relation on `Match`. -/
def Match.companion {X} {bt : BuildTree [] X} (m n : Match bt) : Prop :=
  ∃ (h : (btAt m).2.2.isFreeRepeat), n = Match.companionOf m h

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
inductive PreStateP {H X} (bt : BuildTree H X) : (m : Match bt) → Type
| edge {m n} : (e : Match.Edge m n) → ¬ e.isModal → PreStateP bt n → PreStateP bt m
| stopLeaf {m} : m.isLeaf → PreStateP bt m
| stopAtM {m n} : (e : Match.Edge m n) → e.isModal → PreStateP bt m

/-- Collect all `PreStateP`s from a given `m` onwards. -/
-- Maybe define `Match.all` first and then filter it here?
-- Or better do it inductively?
def BuildTree.allPreStatePs {H X} : (bt : BuildTree H X) → (m : Match bt) → List (PreStateP bt m)
| .loc nbas next, m => sorry
| .pdl bas next, _ => sorry
| .freeRepeat fr, m => sorry
| .openLeaf, m => sorry

lemma BuildTree.allPreStatePs_spec {H X} {bt : BuildTree H X} {m : Match bt} :
    ∀ π : PreStateP bt m, π ∈ bt.allPreStatePs m := by
  sorry

/-- A pre-state is a maximal pre-state-part, i.e. starting at the root or just after (M).

WORRY: should `fromRoot` also have a condition about `H` being empty, i.e. the start of the game?
-/
inductive PreState {H X} (bt : BuildTree H X) : Type
| fromRoot : PreStateP bt .nil → PreState bt
| fromMod {o m} : (e : Match.Edge o m) → e.isModal → PreStateP bt m → PreState bt

/-- Collect all `PreState`s for a given `BuildTree`. -/
def BuildTree.allPreStates {H X} (bt : BuildTree H X) : List (PreState bt) :=
  (bt.allPreStatePs .nil).map .fromRoot

lemma BuildTree.allPreStates_spec {H X} {bt : BuildTree H X} :
    ∀ π : PreState bt, π ∈ bt.allPreStates := by
  -- should be easy, use BuildTree.allPreStatePs_spec
  sorry

/-- Collect formulas in a pre-state. The non-loaded part of Λ(π) in paper.

TODO: If the pre-state ends in a repeat, also include formulas in the path from companion to (M).

QUESTION: Can we collect loaded formulas here by unloading them?
Or would that make the loaded case of `PreState.pdlFormCase` unsayable?
-/
def PreState.forms : PreState bt → List Formula := sorry

/-- Collect formulas in a pre-state. The loaded part of Λ(π) in paper. -/
def PreState.lforms : PreState bt → List NegLoadFormula := sorry

def PreState.last : PreState bt → Sequent := sorry

/-- TODO Lemma 6.14 -/
lemma PreState.formsCases {π : PreState bt} : φ ∈ π.forms →
      (φ.basic ∧ φ ∈ π.last) -- NOTE: the `∈` is not dealing with loaded formulas here!
    ∨ (sorry) := by -- TODO how to say `φ is principal later?`
    -- Or can we say something else / phrase it as closure condition about π.forms directly?
  sorry

/-- WIP Lemma 6.15 (unloaded case only) -/
lemma PreState.pdlFormCase {π : PreState bt} : ¬ α.isAtomic → (~⌈α⌉φ) ∈ π.forms →
    ∃ Xδ ∈ H α, Xδ.1 ∪ [~ Formula.boxes δ φ] ⊆ π.forms := by
  sorry

/-- WIP Lemma 6.16: pre-states are saturated and locally consistent, their last node is basic. -/
lemma PreState.locConsSatBas (π : PreState bt) :
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


end Simpler -- delete me when replacing BuildTree.lean with this file
