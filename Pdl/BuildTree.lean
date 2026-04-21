import Pdl.TableauGame
import Pdl.AllPdlRule

/-! # From winning strategies to model graphs (Section 6.3)

Lessons learned while working on this file:

- Are actually all leafs in the BuildTree backpointers?
  No, we also want all other leafs where builder wins the game to actually build some model :-)

-/

/-! ## BuildTree -/

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- Winning Strategy Tree for Builder.
At a `BuStep` it is the turn of `Builder` and we have a single child for the `Move` they make.
At a `PrStep` it is the turn of `Prover`, and we have children for all possible `Move`.

In the paper "a leaf is either labeled with a sequent to which no rule is applicable, or it is a
(free) repeat". Here we make leafs with `PrStep` because at such a position it is the turn of Prover
but there are no moves so Prover loses.

GOAL: The `BuildTree` type should carry all information we need, so later we should not care
about how a specific strategy tree for builder gets made/computer, but just that there is one.
-/
inductive BuildTree : GamePos → Type
  | BuStep {pos newPos}
      (hturn : tableauGame.turn pos = Builder)
      (m : Move pos newPos)
      (next : BuildTree newPos) -- single child
      : BuildTree pos
  | PrStep {pos}
      (hturn : tableauGame.turn pos = Prover)
      (next : ∀ newPos, ∀ _m : Move pos newPos, BuildTree newPos) -- all children
      : BuildTree pos
      -- side note: we no longer have a `List` here, so may need `Finset.sort (theMoves pos)`??

def BuildTree.isLeaf {pos} : BuildTree pos → Prop
  | BuildTree.BuStep .. => false
  | BuildTree.PrStep .. => theMoves pos = ∅

-- TODO: `BuildTree.isLeaf` implies that either we have a free repeat or we have a
-- basic sequence to which no rule can be applied (and that is easily satisfiable?)

def BuildTree.isFreeRepLeaf {pos} : BuildTree pos → Prop
  | BuildTree.BuStep .. => false
  | @BuildTree.PrStep _ hturn _ =>
      match pos with
      | ⟨H, X, p⟩ =>
        match p with
        | .inl proPos =>
          match proPos with
            | .nlpRep _ _ => True -- free repeat!
            | .bas _ _ => False -- might still be a Leaf, but not a repeat leaf
            | .nbas _ _ => False -- not a leaf because prover can apply a local rule/tableau
        | .inr _ => by exfalso; simp at hturn

theorem BuildTree.rep_of_isFreeRepLeaf {pos : GamePos} {bt : BuildTree pos} :
    bt.isFreeRepLeaf → rep pos.1 pos.2.1 := by
  intro h
  unfold isFreeRepLeaf at h
  rcases pos with ⟨H, X, p⟩
  cases bt <;> simp at *
  case PrStep hturn next =>
    cases p <;> simp at *
    case inl proPos =>
      cases proPos <;> simp at *
      case nlpRep theRep lpr => exact theRep
    · exfalso; grind

/-- Given a winning Builder strategy, compute its `BuildTree`. -/
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, p⟩) :
    BuildTree ⟨H, X, p⟩ :=
  match p_def : p with
  -- Prover positions:
  | Sum.inl (.nlpRep rp noLpRep) => .PrStep (by simp) (by intro _ m; cases m) -- Builder wins rep.
  | Sum.inl (.bas nrep bas) => -- prover chooses PDL rule
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.bas nrep bas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      @BuildTree.PrStep ⟨_,_,Sum.inl (.bas nrep bas)⟩ (by simp_all)
        (fun newPos mov => buildTree s (stillWin newPos mov))
  | Sum.inl (.nbas nrep nbas) => -- prover chooses a local tableau
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.nbas nrep nbas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      @BuildTree.PrStep ⟨_,_,Sum.inl (.nbas nrep nbas)⟩ (by simp_all)
        (fun newPos mov => buildTree s (stillWin newPos mov))
  -- Builder positions:
  | Sum.inr (.lpr _) => by exfalso; simp [winning] at h -- prover wins, cannot happen
  | Sum.inr (.ltab nrep nbas ltX) =>
      if ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty
      then
        -- Builder can use `s` to choose some `Y ∈ endNodeOf ltX`.
        let sY := (s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne)
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
        BuildTree.BuStep (by simp) Mov (buildTree s stillWin)
      else by
        exfalso
        simp_all [winning, winner]
termination_by
  tableauGame.wf.2.wrap (⟨H, X, p⟩ : GamePos)
decreasing_by -- show that it's a move
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    exact ⟨mov⟩
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    exact ⟨mov⟩
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    exact forTermination

/-! ## Matches -/

/-- Path inside a `BuildTree`. Analogous to `PathIn` for `Tableau`. -/
inductive Match : ∀ {pos : GamePos}, BuildTree pos → Type
  | nil {bt} : Match bt
  | bu : Match next → Match (BuildTree.BuStep hturn m next)
  | pr newPos :
      (mov : Move pos newPos)
      → Match (next newPos mov) → Match (@BuildTree.PrStep pos hturn next)

/-
-- TODO, use `LocalAll` and `AllPdlRule`
-- Wait, where are these actually used at the moment or will they be needed later?

def BuildTree.all_Match (bt : BuildTree pos) : List (Match bt) := sorry

theorem BuildTree.all_Match_spec (bt : BuildTree pos) :
    ∀ m, m ∈ bt.all_Match := by
  sorry
-/

/-- Inspired by `PathIn.length`.
Note that this counts all steps, even the `prLocTab` ones where `pos.1` does not get longer. -/
@[simp]
def Match.length {pos : GamePos} {bt : BuildTree pos} : Match bt → Nat
  | .nil => 0
  | .bu tail => tail.length + 1
  | .pr _ _ tail => tail.length + 1

def Match.btAt {pos} {bt : BuildTree pos} : Match bt → Σ newPos, BuildTree newPos
| .nil => ⟨_, bt⟩
| .bu tail => btAt tail
| .pr _ _ tail => btAt tail

-- TODO lemmas like those about `tabAt` and `nodeAt`?

def Match.append : (m1 : Match bt) → (m2 : Match (btAt m1).2) → Match bt
| .nil, m2 => m2
| .bu tail, m2 => .bu (append tail m2)
| .pr _ _ tail, m2 => .pr _ _ (append tail m2)

-- TODO lemmas like those about `PathIn.append`?

structure Match.BuEdge (m n : Match bt) where
  mPos : GamePos
  hturn : tableauGame.turn mPos = Builder
  mov : Move mPos n.btAt.1
  h : btAt m = ⟨mPos, @BuildTree.BuStep _ _ hturn mov (btAt n).2⟩

structure Match.PrEdge (m n : Match bt) where
  mPos : GamePos
  hturn : tableauGame.turn mPos = Prover
  mov : Move mPos n.btAt.1
  next : _
  btAt_m_def : btAt m = ⟨mPos, @BuildTree.PrStep _ hturn next⟩
  next_n_def : next (btAt n).1 n_in = (btAt n).2

/-- The parent-child relation ⋖_𝕋 in a Builder strategy tree. -/
def Match.Edge (m n : Match bt) : Type := Match.BuEdge m n ⊕ Match.PrEdge m n

/-- This edge between matches is a modal step.
To even say this `BuildTree` must contain `Move` and thus rule data. -/
def Match.Edge.isModal {pos} {bt : BuildTree pos} {m n : Match bt} : Match.Edge m n → Prop :=
  match btAt_m_def : btAt m with
  | ⟨⟨Hist, X, p⟩, m_bt⟩ =>
    fun m_n =>
      match m_bt with
      | @BuildTree.BuStep _ p YS next YS_moves => False -- Builder moves are never modal steps.
      | .PrStep hturn next =>
        match m_n with
        | .inl m_bu_n => by exfalso; grind [BuEdge]
        | .inr m_pr_n => m_pr_n.mov.isModal

def Match.isLeaf {pos} {bt : BuildTree pos} {m : Match bt} : Prop := (btAt m).2.isLeaf

/-- If `m` ends at a leaf, then it cannot have an edge to any `n`. -/
lemma Match.isLeaf_no_edge {bt : BuildTree pos} (m : Match bt) (h : m.isLeaf) :
    ∀ n, ¬ Nonempty (Match.Edge m n) := by
  intro n
  unfold Match.isLeaf at h
  by_contra hyp
  rcases hyp with ⟨m_bu_n|m_pr_n⟩
  · grind [BuildTree.isLeaf, Match.BuEdge]
  · simp only [BuildTree.isLeaf, Bool.false_eq_true] at h
    rcases m_pr_n with ⟨mPos, hturn, mov, next, btAt_m_def, next_n_def⟩
    have := @mem_theMoves_of_move mPos n.btAt.1 ⟨mov⟩
    grind

/-- Convert a `Match` to a `History`. Inspired by `PathIn.toHistory`.
Does not include the last node.
The history of `.nil` is `[]` because this will not go into `pos.1`. -/
def Match.toHistory {bt : BuildTree pos} : (m : Match bt) → History
| .nil => []
| .bu tail => tail.toHistory ++ [pos.2.1]
| .pr _ _ tail => tail.toHistory ++ [pos.2.1]

/-- Rewind a `Match`, i.e. go back up inside `bt` by `k` steps.
This used to use `Nat` but now we take a `Fin` like in `PathIn.rewind`, and
for that we needed to define `Match.length` first.
IDEA: also use `Match.toHistory` here? -/
def Match.rewind : (m : Match bt) → (k : Fin (m.length + 1)) → Match bt
| .nil, _ => .nil
| .bu tail, k => Fin.lastCases (.nil) (Match.bu ∘ tail.rewind) k
| .pr _ _ tail, k => Fin.lastCases (.nil) (Match.pr _ _ ∘ tail.rewind) k

-- ... lots of stuff needed here?

/-- Given a `rep H X`, determine the index of the companion in `H` using `List.findIdx?`.
Note that we do *not* care about loading here. -/
def rep.toFin {H X} (rp : rep H X) : Fin (H.length) :=
  match h : List.findIdx? (fun Y => decide (Y.setEqTo X)) H with
  | none => by
      exfalso
      have : ∃ Y ∈ H, decide (Y.setEqTo X) = true := by aesop
      have := @List.findIdx?_eq_some_of_exists Sequent H (fun Y => Y.setEqTo X) this
      simp_all
  | some k => ⟨k, by
    have : k = @List.findIdx Sequent (fun Y => Y.setEqTo X) H := by grind
    rw [this, List.findIdx_lt_length]
    rw [List.findIdx?_eq_some_iff_findIdx_eq] at h
    grind⟩

/-- The extra condition that it is the turn of Builder is needed because otherwise
the `prLocTab` case would falsify. -/
theorem Move.fst_length_succ {H X p} (mov : Move ⟨H, ⟨X, p⟩⟩ newPos) :
    tableauGame.turn ⟨H, ⟨X, p⟩⟩ = Builder →
    newPos.1.length = H.length + 1 := by
  cases mov <;> simp

/-- This is NOT TRUE, because history only records different steps and will
*not* count `Move.prLocTab` steps, though these are steps in the `Match`.

WAIT, but `Match.toHistory` DOES count all steps, so the length statement here should be true. ??

?? are we sure about this one ??
Note that the history from `pos` needs to be added on the right side.

?? Or better restrict `pos` to be a *starting* position of the game!?!?
(Analogous to how many things in TableauPath are only the `Hist = []` case.) -/
theorem Match.btAt_fst_fst_length_eq_length {bt : BuildTree pos} {m : Match bt} :
    m.btAt.1.1.length = m.length + pos.1.length := by
  induction bt
  case BuStep pos newPos hturn mov next IH =>
    cases m
    case nil =>
      rcases pos with ⟨H, X, p⟩
      simp [Match.btAt]
    case bu hturn tail =>
      -- FIXME: change defs above to avoid duplicate `hturn` here?!
      rcases pos with ⟨H, X, p⟩
      simp [Match.btAt]
      specialize @IH tail
      rw [add_assoc]
      convert IH using 2
      grind [Move.fst_length_succ mov]
  case PrStep pos hturn next IH =>
    cases m
    case nil =>
      rcases pos with ⟨H, X, p⟩
      simp [Match.btAt]
    case pr newPos hturn mov tail =>
      rcases pos with ⟨H, X, p⟩
      simp [Match.btAt]
      specialize @IH _ mov tail
      rw [add_assoc]
      convert IH using 2
      -- NOT provable here because `newPos.1` is a history not counting `prLocTab` steps,
      -- whereas the H list coming from `Match.toHistory` does count them.
      sorry

def Match.companionOf {bt : BuildTree pos} (m : Match bt)
  (h : (btAt m).2.isFreeRepLeaf) : Match bt :=
    -- WAS: m.rewind (theRep ((btAt m).2.rep_of_isFreeRepLeaf h))
    -- WANT: m.rewind (rep.toFin ((btAt m).2.rep_of_isFreeRepLeaf h))
    sorry

/-- The repeat ♥ companion relation on `Match`. -/
def Match.companion (m n : Match bt) : Prop :=
  ∃ (h : (btAt m).2.isFreeRepLeaf), n = Match.companionOf m h

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

/-! ## Pre-states (Def 6.13)

As possible worlds for the model graph we want to define *maximal* paths inside the build tree
that do not contain `(M)` steps.

In the paper pre-states are allowed to be of the form π;π' when π ends at a repeat and π' is a
maximal prefix of the path from the companion to that repeat. Here we only store the π part of
such pre-states, because the π' is then uniquely determined by π.
-/

/-- A pre-state-part starting at `m` is any path in `bt : BuildTree` consisting of non-(M) `edge`s
and stopping at a leaf or at an (M) application. (No `Match.companion` steps here, see note above.)

PROBLEM / QUESTION: do we also need leafs given by empty `prMoves`??? -/
inductive PreStateP {pos} (bt : BuildTree pos) : (m : Match bt) → Type
| edge {m n} : (e : Match.Edge m n) → ¬ e.isModal → PreStateP bt n → PreStateP bt m
| stopLeaf {m} : m.isLeaf → PreStateP bt m
| stopAtM {m n} : (e : Match.Edge m n) → e.isModal → PreStateP bt m

/-- Collect all `PreStateP`s from a given `m` onwards. -/
def BuildTree.allPreStatePs {pos} : (bt : BuildTree pos) → (m : Match bt) → List (PreStateP bt m)
  -- Maybe define `Match.all` first and then filter it here?
  -- Or better do it inductively?
| .PrStep hturn next, m => sorry
    -- [ .stopLeaf (by unfold Match.isLeaf; cases m; simp_all [Match.btAt]) ]
| .BuStep hturn mov next, _ => sorry

lemma BuildTree.allPreStatePs_spec {pos} {bt : BuildTree pos} {m : Match bt} :
    ∀ π : PreStateP bt m, π ∈ bt.allPreStatePs m := by
  sorry

/-- A pre-state is a maximal pre-state-part, i.e. starting at the root or just after (M).

WORRY: should `fromRoot` also have a condition about `pos` being the start of the game?
-/
inductive PreState {pos} (bt : BuildTree pos) : Type
| fromRoot : PreStateP bt .nil → PreState bt
| fromMod {o m} : (e : Match.Edge o m) → e.isModal → PreStateP bt m → PreState bt

/-- Collect all `PreState`s for a given `BuildTree`. -/
def BuildTree.allPreStates {pos} (bt : BuildTree pos) : List (PreState bt) :=
  (bt.allPreStatePs .nil).map .fromRoot

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
