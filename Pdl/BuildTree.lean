import Pdl.TableauGame
import Pdl.AllPdlRule

/-! # From winning strategies to model graphs (Section 6.3) -/

/-! ## BuildTree -/

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- Tree data type to keep track of choices made by Builder. Might still need to be tweaked.
- Choices should be labelled with the choices made by prover?
  TODO: Do we need to keep track of which rule is used?
-/
inductive BuildTree : GamePos → Type
  | Leaf {pos} (rp : rep pos.1 pos.2.1) : BuildTree pos
  | Step {pos} (YS : List GamePos)
      (YS_Moves : ∀ newPos ∈ YS, Move pos newPos)
      (next : ∀ newPos ∈ YS, BuildTree newPos) : BuildTree pos

-- QUESTION: are actually all leafs in the BuildTree backpointers?

/-- The tree generated from a winning Builder strategy -/
noncomputable -- :-(
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, p⟩) :
    BuildTree ⟨H, X, p⟩ :=
  match p with
  -- Prover positions:
  | Sum.inl (.nlpRep rp noLpRep) => .Leaf rp -- Builder wins with back-pointer :-)
  | Sum.inl (.bas nrep bas) => -- prover chooses PDL rule
      let prMoves := (PdlRule.all X).map
        (fun ⟨Y, r⟩ => (⟨(X :: H), Y, posOf (X :: H) Y⟩ : GamePos))
      have stillWin : ∀ newPos ∈ prMoves, winning s newPos := by
        -- FIXME some redundancy between here and the termination proof
        intro newPos newPos_in
        refine @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, ?_⟩
        simp only [List.mem_map, Sigma.exists, exists_and_right, prMoves] at newPos_in
        rcases newPos_in with ⟨Y, ⟨r, r_in⟩, def_newPos⟩
        simp only [tableauGame]
        apply mem_theMoves_of_move
        subst newPos
        exact ⟨Move.prPdl r⟩
      -- TODO: what if `prMoves` here is empty? Make a leaf then?
      .Step prMoves
        (by intro nP nP_in; unfold prMoves at nP_in; simp at nP_in
            choose Y hr def_nP using nP_in
            choose r Yr_in using hr
            rw [<- def_nP]; exact Move.prPdl r)
        <| fun Y Y_in => buildTree s (stillWin _ Y_in)
  | Sum.inl (.nbas nrep nbas) => -- prover chooses a local tableau
      -- Note: not using the Fintype instance because we want a List, not Finset
      let prMoves := (LocalTableau.all X).map
        (fun ltab => (⟨H, X, .inr (.ltab nrep nbas ltab)⟩ : GamePos))
      have stillWin : ∀ newPos ∈ prMoves, winning s newPos := by
        intro newPos newPos_in
        refine @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, ?_⟩
        simp only [tableauGame, List.mem_map, theMoves, Finset.mem_image, prMoves] at *
        rcases newPos_in with ⟨ltX, ltX_in, def_newPos⟩
        refine ⟨ltX, ?_, def_newPos⟩
        simp_all [Fintype.elems]
      -- TODO: check that `prMoves` here can never be empty? Or can it?
      .Step prMoves
        (by intro nP nP_in; unfold prMoves at nP_in; simp at nP_in
            choose lt lt_in def_nP using nP_in
            rw [<- def_nP]; exact Move.prLocTab)
        <| fun Y Y_in => buildTree s (stillWin _ Y_in)
  -- Builder positions:
  | Sum.inr (.lpr _) => by exfalso; simp [winning] at h -- prover wins, cannot happen
  | Sum.inr (.ltab nrep nbas ltX) =>
      if ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty
      then
        -- use `s` to choose `Y ∈ endNodeOf ltX`
        let Y := (s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne)
        have stillWin : winning s Y.1 := winning_of_winning_move _ h
        have Mov : Move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ Y.1 := by
          have := Y.2
          simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at this
          simp [List.mem_map] at this
          choose Y Y_in def_Y using this
          have := @Move.buEnd X ltX Y H nrep nbas Y_in
          rw [← def_Y]
          exact this
        have forTermination : move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ Y.1 := ⟨Mov⟩
        .Step [ Y.1 ]
          (by intro nP nP_in; simp_all; subst nP_in; exact Mov)
          <| fun Y Y_in => by simp at Y_in; subst Y_in; exact buildTree s stillWin
      else by
        exfalso
        simp_all [winning, winner]
termination_by
  tableauGame.wf.2.wrap (⟨H, X, p⟩ : GamePos)
decreasing_by
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    -- PDL rule case
    simp only [List.mem_map, Sigma.exists, exists_and_right, prMoves] at Y_in
    rcases Y_in with ⟨Y, ⟨r, _⟩, def_newPos⟩
    subst def_newPos
    exact ⟨Move.prPdl r⟩
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    -- show that it's a move
    unfold prMoves at Y_in
    simp only [List.mem_map] at Y_in
    rcases Y_in with ⟨ltX, _, def_pos⟩
    subst def_pos
    exact ⟨@Move.prLocTab H X nrep nbas _⟩
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    -- show that it's a move
    exact forTermination

/-! ## Matches

WORRY: Where in the below is it okay/safe to work with the `BuildTree` type and
where should we insist on the (more specific) `buildTree` result value?
-/

/-- Path inside a `BuildTree`. Analogous to `PathIn` for `Tableau`. -/
inductive Match : ∀ {pos : GamePos}, BuildTree pos → Type
| stop {bt} : Match bt
| mov {YS Y mvs next} Y_in (tail : Match (next Y Y_in)) : Match (BuildTree.Step YS mvs next)

def Match.btAt {pos} {bt : BuildTree pos} : Match bt → Σ newPos, BuildTree newPos
| stop => ⟨_, bt⟩
| mov _ tail => btAt tail

-- TODO lemmas like those about `tabAt` and `nodeAt`?

def Match.append : (m1 : Match bt) → (m2 : Match (btAt m1).2) → Match bt
| stop, m2 => m2
| mov Y_in tail, m2 => mov Y_in (append tail m2)

-- TODO lemmas like those about `PathIn.append`?

/-- The parent-child relation ⋖_𝕋 in a Builder strategy tree. Similar to `edge` but data. -/
structure Match.edge (m n : Match bt) where
  YS : List GamePos
  next : (newPos : GamePos) → newPos ∈ YS → BuildTree newPos
  mPos : GamePos
  nPos : GamePos
  nPos_in : nPos ∈ YS
  mvs : ∀ newPos ∈ YS, Move mPos newPos
  h : btAt m = ⟨mPos, BuildTree.Step YS mvs next⟩
  def_n : n = m.append (h ▸ @mov mPos YS nPos mvs next nPos_in stop)

/-- If `m` ends at a leaf, then it cannot have an edge to any `n`. -/
lemma Match.leaf_no_edge {bt : BuildTree pos} (m : Match bt) rp (h : (btAt m).2 = .Leaf rp) :
    ∀ n, ¬ Nonempty (Match.edge m n) := by
  intro n
  by_contra hyp
  rcases hyp with ⟨m_n⟩
  rcases m_n with ⟨YS, next, mPos, nPos, nPos_in, mvs, h, def_n⟩
  grind

/-- Go back up inside `bt` by `k` steps.
FIXME: instead of `Nat`, use `Fin` like we do in `PathIn.rewind`. -/
def Match.rewind : Match bt → (k : Nat) → Match bt
| stop, _ => stop
| mov Y_in tail, 0 => mov Y_in tail
| mov Y_in tail, (k + 1) => (mov Y_in tail).rewind k

-- ... lots of stuff needed here?

def Match.companionOf {bt : BuildTree pos} (m : Match bt) rp
  (_ : btAt m = ⟨mPos, BuildTree.Leaf rp⟩) : Match bt := m.rewind (theRep rp)

def Match.companion (m n : Match bt) : Prop :=
  ∃ (mPos :_) (rp : _) (h : btAt m = ⟨mPos, BuildTree.Leaf rp⟩),
    n = Match.companionOf m rp h

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

/-! ## Pre-states (Def 6.13)

As possible worlds for the model graph we want to define *maximal* paths inside the build tree
that do not contain `(M)` steps.

In the paper pre-states are allowed to be of the form π;π' when π ends at a repeat and π' is a
maximal prefix of the path from the companion to that repeat. Here we only store the π part of
such pre-states, because the π' is then uniquely determined by π. -/

/-- This edge between matches is a modal step.
To even say this we adjusted `BuildTree` to contain data which rule was used. -/
def Match.edge.isModal {pos} {bt : BuildTree pos} {m n : Match bt} : Match.edge m n → Prop := by
  rcases btAt_m_def : btAt m with ⟨pos, m_bt⟩
  rcases pos with ⟨Hist, X, _⟩
  intro m_n
  cases m_bt
  case Leaf p rp =>
    exfalso
    simp at rp
    -- lemma that leafs have no edges?
    have := @Match.leaf_no_edge _ _ m
    rw [btAt_m_def] at this
    simp at this
    apply (this rp n).1 m_n
  case Step p YS next YS_moves =>
    -- `cases edge` broken here, solved by turning `edge` into data
    rcases m_n with ⟨YS, next, mPos, nPos, nPos_in, mvs, h, def_n⟩
    specialize mvs nPos nPos_in
    -- Here we use that we have a `Move` that is data (and we not just have `move`).
    cases mvs
    case prPdl r => exact r.isModal
    case prLocTab => exact False
    case buEnd => exact False

def Match.isLeaf {pos} {bt : BuildTree pos} {m : Match bt} : Prop :=
    ∃ m_pos rep, m.btAt = ⟨m_pos, .Leaf rep⟩

/-- A pre-state-part starting at `m` is any path in `bt : BuildTree` consisting of non-(M) `edge`s
and stopping at a leaf or at an (M) application. (No `Match.companion` steps here, see note above.)

PROBLEM / QUESTION: do we also need leafs given by empty `prMoves`??? -/
inductive PreStateP {pos} (bt : BuildTree pos) : (m : Match bt) → Type
| edge {m n} : (e : Match.edge m n) → ¬ e.isModal → PreStateP bt n → PreStateP bt m
| stopLeaf {m} : m.isLeaf → PreStateP bt m
| stopAtM {m n} : (e : Match.edge m n) → e.isModal → PreStateP bt m

/-- Collect all `PreStateP`s from a given `m` onwards. -/
def BuildTree.allPreStatePs {pos} : (bt : BuildTree pos) → (m : Match bt) → List (PreStateP bt m)
  -- Maybe define `Match.all` first and then filter it here?
  -- Or better do it inductively?
| .Leaf rp, m => [ .stopLeaf (by unfold Match.isLeaf; cases m; simp_all [Match.btAt]) ]
| .Step YS YS_Moves next, _ => sorry

lemma BuildTree.allPreStatePs_spec {pos} {bt : BuildTree pos} {m : Match bt} :
    ∀ π : PreStateP bt m, π ∈ bt.allPreStatePs m := by
  sorry

/-- A pre-state is a maximal pre-state-part, i.e. starting at the root or just after (M).

WORRY: should `fromRoot` also have a condition about `pos` being the start of the game?
-/
inductive PreState {pos} (bt : BuildTree pos) : Type
| fromRoot : PreStateP bt .stop → PreState bt
| fromMod {o m} : (e : Match.edge o m) → e.isModal → PreStateP bt m → PreState bt

/-- Collect all `PreState`s for a given `BuildTree`. -/
def BuildTree.allPreStates {pos} (bt : BuildTree pos) : List (PreState bt) :=
  (bt.allPreStatePs .stop).map .fromRoot

lemma BuildTree.allPreStates_spec {pos} {bt : BuildTree pos} :
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
def BuildTree.toModel (bt : BuildTree Pos) : (Σ W : Finset (Finset Formula), KripkeModel W) :=
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
        AnyNegFormula.mem_Sequent (t.btAt).1.2.1 (~''φ)
      ∧ ∃ ρ : PreState bt, ∃ u : Match bt,
        -- TODO: t < u
        -- TODO: missing loaded formulas below
        @Modelgraphs.Q sorry sorry α ⟨π.forms.toFinset, sorry⟩ ⟨ρ.forms.toFinset, sorry⟩ := by
  sorry

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded

-- TODO Lemma 6.20: diamond existence lemma for pre-states

/-! ## Model graph of pre-states -/

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), ∃ Z ∈ WS, X.toFinset ⊆ Z := by
  let bt := buildTree s h
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
    -- need actual def for `PreState.all` first
    -- use the .fromRoot pre-state
    sorry
