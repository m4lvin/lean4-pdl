import Pdl.TableauGame
import Pdl.AllPdlRule

/-! # From winning strategies to model graphs (Section 6.3)

Lessons learned while working on this file:

- Not all leafs in the BuildTree are backpointers.
  We want open leafs (where builder wins the game) to actually build worlds :-)
  Moreover, free repeats also let builder win.

-/

/-! ## Helper Lemmas -/

/-- Any basic sequent is also saturated. -/
lemma Sequent.basic_then_saturated {X : Sequent} : X.basic → saturated X.toFinset := by
  intro Xbas
  rcases X with ⟨L,R,O⟩
  unfold saturated
  intro Fs φ ψ α
  refine ⟨?_, ?_, ?_, ?box, ?dia⟩
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  · simp_all [basic, Fs, toFinset]
    grind
  case box =>
    intro _in_F
    simp_all [basic, Fs, toFinset]
    cases α
    case atom_prog =>
      simp [TP, testsOfProgram,Bset,P,F]
      exact _in_F
    all_goals
      simp [TP, testsOfProgram,Bset,P,F]
      grind
  case dia =>
    intro _in_F
    simp_all [basic, Fs, toFinset]
    cases α
    case atom_prog =>
      simp [Dset,Yset]
      exact _in_F
    all_goals
      simp [Dset,Yset]
      grind

/-! ## BuildTree -/

-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- A free repeat is a non-loaded sequent that occured before. Values of this type are pairs:
the number of steps to go back in the history and a proof that we then find the same set.

Note: this now uses `setEqTo` instead of `multisetEqTo` to agree with `rep`.

IDEA: move this to `Tableau.lean` near `rep` and turn `flprep` into data? -/
def FreeRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k).setEqTo X ∧ ¬ X.isLoaded)

lemma FreeRepeat_nil_impossible : FreeRepeat [] X → False := by
  rintro ⟨n, n_h⟩
  grind

/-- An open local tableau has at least one end node. -/
def OpenLocalTableau (X : Sequent) : Type := {lt : LocalTableau X // endNodesOf lt ≠ []}
deriving DecidableEq

def OpenLocalTableau.all (X : Sequent) : List (OpenLocalTableau X) :=
  ((LocalTableau.all X).filter (endNodesOf · ≠ [])).attach.map (fun ⟨lt,h⟩ => ⟨lt, by simp_all⟩)

lemma OpenLocalTableau.all_spec {X : Sequent} {ltX : OpenLocalTableau X} :
    ltX ∈ OpenLocalTableau.all X := by
  rcases ltX with ⟨lt, lt_has_ends⟩
  unfold all
  simp_all only [ne_eq, List.mem_map, List.mem_attach, true_and, Subtype.exists, decide_not,
    List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  use lt
  have := lt.all_spec
  grind

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
  /-- Prover chooses local tab, we pick an end node (which must exist as otherwise prover wins). -/
  | loc {H X} (nbas : ¬ X.basic) (someLT : OpenLocalTableau.all X ≠ [])
            (next : (lt : OpenLocalTableau X) → BuildChoice H X (endNodesOf lt.1))
            : BuildTree H X
  /-- Prover chooses PDL rule, never branches, so continue with unique child. -/
  | pdl {H X} (bas : X.basic) (someR : PdlRule.all X ≠ [])
            (next : ∀ Y, ∀ _r : PdlRule X Y, BuildTree (X :: H) Y) : BuildTree H X
  /-- Free repeat means builder wins. -/
  -- QUESTION: do we insist on free repeat or is any not-loaded-path repeat a builder win?
  | freeRepeat {H X} : FreeRepeat H X → BuildTree H X
  /-- Leaf that is (might be?!) not a repeat, but no rules can be applied. -/
  | openLeaf {H X} (bas : X.basic) (noRule : PdlRule.all X = []) : BuildTree H X
  -- small worry but what about (L+) (L-), one of which is always applicable?
  -- No. L- and L+ are not applicable when there is no diamond formula left.
  -- (And even when there is, they would lead to a free repeat..)
  -- Also, we do not add a condition to be locally consistent, because
  -- already basic implies not closed and that implies locally consistent.

inductive BuildChoice : History → Sequent → List Sequent → Type
  | pick {H X YS Y} : Y ∈ YS → BuildTree (X :: H) Y → BuildChoice H X YS
end

mutual
/-- Manual replacement for `sizeOf (bt : BuildTree)` so we also count the `next` parts. -/
def BuildTree.size : BuildTree H X → Nat
  | .loc _ _ next => 1 + ((OpenLocalTableau.all X).map (fun lt => (next lt).size)).sum
  | .pdl _ _ next => 1 + ((PdlRule.all X).map (fun ⟨Y,r⟩ => (next Y r).size)).sum
  | .freeRepeat _ => 1
  | .openLeaf _ _ => 1

def BuildChoice.size : BuildChoice H X YS → Nat
  | .pick _ bt_Y => bt_Y.size
end

lemma BuildTree.size_lt_loc (H : History) (X : Sequent) (nbas : ¬X.basic)
    (next : (lt : OpenLocalTableau X) → BuildChoice H X (endNodesOf lt.1))
    (ltX : OpenLocalTableau X) someLT :
    (next ltX).6.size < (BuildTree.loc nbas someLT next).size := by
  simp [BuildTree.size]
  have : (next ltX).6.size ∈ ((OpenLocalTableau.all X).map (fun lt => (next lt).6.size)) := by
    simp only [List.mem_map]
    use ltX, OpenLocalTableau.all_spec
  have := List.le_sum_of_mem this
  have : ∀ lt, (next lt).size = (next lt).6.size := fun lt => by
    cases next lt; simp [BuildChoice.size]
  simp_rw [this]
  grind

lemma BuildTree.size_lt_pdl (H : History) (X : Sequent) (bas : X.basic)
    (someR : PdlRule.all X ≠ [])
    (next : (Y : Sequent) → PdlRule X Y → BuildTree (X :: H) Y) (Y : Sequent) (r : PdlRule X Y) :
    (next Y r).size < (BuildTree.pdl bas someR next).size := by
  simp only [BuildTree.size]
  have : (next Y r).size ∈ ((PdlRule.all X).map (fun ⟨Y,r⟩ => (next Y r).size)) := by
    simp only [List.mem_map, Sigma.exists]
    use Y, r, PdlRule.all_spec bas _
  have := List.le_sum_of_mem this
  grind

@[simp]
lemma BuildChoice.fst_eq {H X YS} {bc : BuildChoice H X YS} : bc.1 = H := by cases bc; rfl

@[simp]
lemma BuildChoice.snd_eq {H X YS} {bc : BuildChoice H X YS} : bc.2 = X := by cases bc; rfl

@[simp]
lemma BuildChoice.thrd_eq {H X YS} {bc : BuildChoice H X YS} : bc.3 = YS := by cases bc; rfl

def BuildTree.isFreeRepeat {H X} : BuildTree H X → Prop
  | BuildTree.freeRepeat _ => True
  | _ => False

instance instDecidableIsFreeRepeat {H X} {bt : BuildTree H X} : Decidable bt.isFreeRepeat := by
  cases bt <;> simp [BuildTree.isFreeRepeat] <;> try exact instDecidableFalse
  exact instDecidableTrue

def BuildTree.getFreeRepeat {H X} {bt : BuildTree H X}
    (h : bt.isFreeRepeat) : FreeRepeat H X := by
  unfold isFreeRepeat at h
  cases bt <;> simp at *
  case freeRepeat fr => exact fr

/-- Given the proof `rep H X` and that `X` is free, find a `FreeRepeat` value / data.

(Previously here we tried to go from `rep H X` and `¬Nonempty (LoadedPathRepeat H X)`
to `FreeRepeat` which does not work as there might still be loaded non-lpr repeats.) -/
def FreeRepeat.of_rep_free {X : Sequent} (rp : rep H X)
    (free : ¬ X.isLoaded) : FreeRepeat H X := by
  refine ⟨rp.toFin, ?_⟩
  have := rp.toFin_agrees
  simp_all

/-- Given a winning Builder strategy, compute its `BuildTree`.
NEW: note the `Sum.inl p` here. This ensure we start tree building from a Prover position, i.e.
- not allowing BuilderPos.lpr here (easy, was forbidden already anyway as prover wins there.)
- not allowing BuilderPos.ltab because we cannot use BuildTree.loc for a single fixed local tab. -/
def buildTree (s : Strategy tableauGame Builder) {H X p} (h : winning s ⟨H, X, Sum.inl p⟩) :
    BuildTree H X :=
  match p_def : p with
  -- Prover positions:
  | (ProverPos.frep rp) => -- Builder wins free rep.
    .freeRepeat (.of_rep_free rp.1 (by grind [Sequent.isFree]))
  | (.bas nrep bas) =>
    if someR : PdlRule.all X ≠ []
    then -- prover chooses PDL rule if there is one
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.bas nrep bas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      .pdl bas someR <| fun newSeq r => by
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
    else -- no rule, prover loses and we recordt his with an open leaf.
      (.openLeaf bas (by rw [ne_eq, Decidable.not_not] at someR; exact someR))
  | (.nbas nrep nbas) => -- prover chooses a local tableau
      have stillWin : ∀ newP, ∀ _ : Move ⟨_,_,Sum.inl (.nbas nrep nbas)⟩ newP, winning s newP :=
        fun newPos mov =>
          @winning_of_whatever_other_move _ _ s _ (by simp) h ⟨newPos, mem_theMoves_of_move ⟨mov⟩⟩
      have someLT : OpenLocalTableau.all X ≠ [] := by
        -- We show that there is no lt without end nodes because prover could use it to win.
        rcases List.exists_mem_of_ne_nil _ (LocalTableau.all_nonempty X) with ⟨lt, lt_in⟩
        apply List.ne_nil_of_mem (@OpenLocalTableau.all_spec X ⟨lt, ?_⟩)
        intro lt_no_ends
        have := stillWin ⟨H, ⟨X, Sum.inr (.ltab nrep nbas lt)⟩⟩ Move.prLocTab
        have has_moves := winning_has_moves (by simp) this
        simp only [tableauGame, Game.moves, theMoves, List.toFinset_nonempty_iff, ne_eq,
          List.map_eq_nil_iff] at has_moves
        exact has_moves lt_no_ends
      .loc nbas someLT <| fun ltX => by
        have ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (.ltab nrep nbas ltX.1)⟩⟩).Nonempty :=
          winning_has_moves (by simp) <|
            stillWin ⟨H, ⟨X, Sum.inr (.ltab nrep nbas ltX.1)⟩⟩ Move.prLocTab
        -- IDEA: use strategy `s` to choose move `mY` that picks the `Y ∈ endNodeOf ltX`:
        -- We want to define mY and then do rcases, but keep the information how it was defined.
        let mY_raw := s ⟨H, X, Sum.inr (.ltab nrep nbas ltX.1)⟩ (by simp) ne
        have mY_def : mY_raw.1 = s ⟨H, X, Sum.inr (.ltab nrep nbas ltX.1)⟩ (by simp) ne := rfl
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
          have Mov : Move ⟨H, X, Sum.inr (.ltab nrep nbas ltX.1)⟩ mY := by
            simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at mY_prop
            simp [List.mem_map] at mY_prop
            let oY := List.find? -- No more choice thanks to this!
              (fun Y => @decide (⟨_, ⟨_, posOf (X :: H) Y⟩⟩ = mY) (instDecidableEqPos _ _))
              (endNodesOf ltX.1)
            cases oY_def : oY
            · exfalso
              have := List.find?_eq_none.mp oY_def
              grind
            case some Y =>
              unfold oY at oY_def
              have def_mY := List.find?_some oY_def
              simp only [decide_eq_true_eq] at def_mY
              have Y_in := List.mem_of_find?_eq_some oY_def
              have := @Move.buEnd X ltX.1 Y H nrep nbas Y_in
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
                  ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX.1)⟩⟩
                · exact Relation.TransGen.single ⟨Mov⟩
                · rw [p_def]; exact Relation.TransGen.single ⟨Move.prLocTab⟩
            refine H'_def ▸ @buildTree s H' Y myP ?_
            -- (Remaining goal is nicer after doing `H'_def ▸` on the outside and not on `myP`.)
            rw [mY_def]
            -- Note that *two* moves have happened now, one by prover and one by Builder using `s`.
            -- Remains to show that `s` still wins.
            apply winning_of_winning_move
            exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX.1)⟩ Move.prLocTab
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
                exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX.1)⟩ Move.prLocTab
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
  | loc {nbas someLT next lt} : Match (next lt).6 → Match (BuildTree.loc nbas someLT next)
  | pdl {bas someR next Y r} : Match (next Y r) → Match (BuildTree.pdl bas someR next)
deriving DecidableEq

/-- Inspired by `PathIn.length`. Counting the steps made by a `Match` in a `BuildTree`.
Note that such a step is a combination of a prover and a builder move. -/
@[simp]
def Match.length {H : History} {X : Sequent} {bt : BuildTree H X} : Match bt → Nat
  | .nil => 0
  | .loc tail => tail.length + 1
  | .pdl tail => tail.length + 1

def Match.btAt {H X} {bt : BuildTree H X} : Match bt → Σ H' Y, BuildTree H' Y
| .nil => ⟨_, _, bt⟩
| .loc tail => btAt tail
| .pdl tail => btAt tail

/-- The sequent reached at the end of a match. -/
def Match.endSeq {bt : BuildTree H X} (m : Match bt) : Sequent := m.btAt.2.1

/- All possible Matches in a given BuildTree. -/
def Match.all {H X} : (bt : BuildTree H X) → List (Match bt)
  | .loc nbas someLT next =>
      Match.nil ::
      (OpenLocalTableau.all X >>= fun ltX => return Match.loc (← Match.all (next ltX).6))
  | .pdl bas someRule next =>
      Match.nil ::
      (PdlRule.all X >>= fun ⟨Y,r⟩ => return Match.pdl (← (Match.all (next Y r))))
  | .freeRepeat fr => [ .nil ]
  | .openLeaf _ _ => [ .nil ]
termination_by
  bt => bt.size
decreasing_by
  · apply BuildTree.size_lt_loc
  · apply BuildTree.size_lt_pdl

theorem Match.all_spec {H X} {bt : BuildTree H X} {m} :
    m ∈ Match.all bt := match m with
  | nil => by cases bt <;> grind [Match.all]
  | @loc _ _ bas someLT next lt tail => by
    have IH:= @Match.all_spec _ _ _ tail
    rw[Match.all]
    simp
    refine ⟨lt,?_ ⟩
    refine ⟨ OpenLocalTableau.all_spec ,tail,IH,?_⟩
    simp
  | @pdl _ _ bas someR next Y r tail => by
    have IH := @Match.all_spec _ _ _ tail
    rw [Match.all]
    simp
    refine ⟨_, r, PdlRule.all_spec bas r, ?_⟩
    refine ⟨tail, IH, rfl, ?_⟩ -- heterogeneous equality left here
    simp

def Match.isOpenLeaf {H X} {bt : BuildTree H X} {m : Match bt} : Prop :=
  match (btAt m) with | ⟨_, _, .openLeaf _ _⟩ => True | _ => False

instance instDecidableIsOpenLeaf {m : Match bt} : Decidable m.isOpenLeaf := by
  unfold Match.isOpenLeaf
  rcases m.btAt with ⟨_, _, bt⟩
  cases bt <;>
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse

def Match.isFreeRepeat {H X} {bt : BuildTree H X} (m : Match bt) : Prop :=
  match (btAt m) with | ⟨_, _, .freeRepeat _⟩ => True | _ => False

instance instMatchDecidableIsFreeRepeat {H X} {bt : BuildTree H X} {m : Match bt} :
    Decidable m.isFreeRepeat := by
  unfold Match.isFreeRepeat
  rcases m.btAt with ⟨_, _, bt⟩
  cases bt <;> simp_all
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse

lemma Match.isFreeRepeat_iff {H X} {bt : BuildTree H X} {m : Match bt} :
    m.isFreeRepeat ↔ (btAt m).2.2.isFreeRepeat := by
  unfold BuildTree.isFreeRepeat Match.isFreeRepeat
  grind

/-- Get the `FreeRepeat` (rewind-index and same-sequent proof) of a `Match`. -/
def Match.getFreeRepeat {X} {bt : BuildTree [] X} (m : Match bt)
  (h : m.isFreeRepeat) : FreeRepeat m.btAt.1 m.btAt.2.1 :=
    BuildTree.getFreeRepeat (Match.isFreeRepeat_iff.eq ▸ h)

-- needed / ever used?
def Match.append {H X} {bt : BuildTree H X} :
    (m1 : Match bt) → (m2 : Match (btAt m1).2.2) → Match bt
| .nil, m2 => m2
| .loc tail, m2 => .loc (append tail m2)
| .pdl tail, m2 => .pdl (append tail m2)

-- Maybe Match.toHistory is not actually needed? Skipping it for now.

/-- Rewind a `Match`, i.e. go back up inside `bt` by `k` steps.
The + 1 is there because going back 0 steps does nothing. -/
def Match.rewind {H X} {bt : BuildTree H X} : (m : Match bt) → (k : Fin (m.length + 1)) → Match bt
| .nil, _ => .nil
| .loc tail, k => Fin.lastCases (.nil) (Match.loc ∘ tail.rewind) k
| .pdl tail, k => Fin.lastCases (.nil) (Match.pdl ∘ tail.rewind) k

/-- Rewinding 0 steps does nothing. -/
@[simp]
lemma Match.rewind_zero {H X} {bt : BuildTree H X} (m : Match bt) : m.rewind 0 = m := by
  induction m <;> simp only [rewind]
  case loc H X nbas someLT next lt tail IH => -- idea from PathIn.rewind_zero
    have : 0 ≠ Fin.last (@loc H X nbas someLT next lt tail).length := by
      simp_all [Fin.last]
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp only [← kdef, Fin.lastCases_castSucc, Function.comp_apply, loc.injEq, heq_eq_eq, true_and]
    convert IH
    cases k
    simp_all
  case pdl H X bas someR next Y r tail IH =>
    have : 0 ≠ Fin.last (@pdl H X bas someR next Y r tail).length := by
      simp_all [Fin.last]
    rw [← Fin.exists_castSucc_eq] at this
    rcases this with ⟨k,kdef⟩
    simp [← kdef, Fin.lastCases_castSucc, Function.comp_apply, pdl.injEq]
    convert IH
    cases k
    simp_all

/-- Inspired by `PathIn.rewind_length_lt_length_of_gt_zero`. -/
lemma Match.rewind_length_lt_length_of_pos {H X} {bt : BuildTree H X} (m : Match bt)
    (k : Fin (m.length + 1)) (k_pos : 0 < k)
    : (m.rewind k).length < m.length := by
  induction m
  · exfalso
    rcases k with ⟨k, k_prop⟩
    simp only [length, zero_add, Nat.lt_one_iff] at k_prop
    subst k_prop
    simp_all
  case loc H X nbas next lt tail IH =>
    cases k using Fin.lastCases
    case last => simp [Match.rewind] at *
    case cast j =>
      simp only [rewind, length, Fin.lastCases_castSucc, Function.comp_apply, add_lt_add_iff_right]
      exact IH _ k_pos
  case pdl Z Y H next r tail IH =>
    cases k using Fin.lastCases
    case last => simp [Match.rewind] at *
    case cast j =>
      simp only [rewind, length, Fin.lastCases_castSucc, Function.comp_apply, add_lt_add_iff_right]
      exact IH _ k_pos

lemma Match.btAt_newHist_length_eq_length_plus_oldHist {H X} {bt : BuildTree H X} (m : Match bt) :
    m.btAt.1.length = m.length + H.length :=
  match m with
  | nil => by simp [btAt]
  | @loc _ _ _ _ next lt tail => by
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

/-- Roll back to the companion. Only possibe if we started with H=[] so we know the root. -/
def Match.companionOf {X} {bt : BuildTree [] X} (m : Match bt)
  (h : m.isFreeRepeat) : Match bt :=
    match m.getFreeRepeat h with
    -- The free repeat says "go k steps back" where k < length of history at `m`.
    | ⟨⟨k, k_lt⟩ , same_and_free⟩ =>
      -- But to rewind m we need a k < length of m itself plus 1
      m.rewind ⟨k, by grind [Match.btAt_newHist_length_eq_length_plus_oldHist]⟩

/-- The repeat ♥ companion relation on `Match`. -/
def Match.companion {X} {bt : BuildTree [] X} (m n : Match bt) : Prop :=
  ∃ (h : m.isFreeRepeat), n = Match.companionOf m h

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

lemma Match.companionOf_setEqTo_sequent (m : Match bt) h :
    (m.companionOf h).btAt.2.1.setEqTo m.btAt.2.1 := by
  unfold isFreeRepeat at h
  unfold companionOf Match.getFreeRepeat
  split
  simp_all
  -- need lemma that rewind+btAt.snd.fst gives same as going back in history
  sorry

/-! ## move to Syntax.lean and Sequent.lean later -/

/-- Unfortunately our `AnyFormula` type does not include *negated* loaded formulas, so this is yet
another type to describe "whatever formula" can be in a sequent, without losing information. -/
inductive WhateverFormula : Type
  | any : AnyFormula → WhateverFormula
  | negLoad : NegLoadFormula → WhateverFormula
  deriving Repr, DecidableEq

instance : Coe Formula WhateverFormula := ⟨.any ∘ .normal⟩
instance : Coe LoadFormula WhateverFormula := ⟨.any ∘ .loaded⟩
instance : Coe NegLoadFormula WhateverFormula := ⟨WhateverFormula.negLoad⟩

def Olf.wForms : Olf → List WhateverFormula
  | none => []
  | some (.inl (nφ)) => [.negLoad nφ]
  | some (.inr (nφ)) => [.negLoad nφ]

def Sequent.wForms : Sequent → List WhateverFormula
  | ⟨L,R,O⟩ => L.map Coe.coe ++ R.map Coe.coe ++ O.wForms

lemma Sequent.mem_bothSides_iff (φ : Formula) (X : Sequent) :
    φ ∈ X.bothSides ↔
      ((.any (.normal φ) : WhateverFormula) ∈ X.wForms
      ∨ (∃ χ, χ.unload = φ ∧ (.any (.loaded χ) ∈ X.wForms))
      ∨ (∃ ψ, negUnload ψ = φ ∧ (.negLoad ψ ∈ X.wForms))) := by
  rcases X with ⟨L, R, O⟩
  rcases O with _ | (ψ | ψ) <;>
    simp [Sequent.bothSides, Sequent.left, Sequent.right, Sequent.wForms, Olf.wForms,
      Olf.L, Olf.R, instCoeFormulaWhateverFormula] <;> tauto

/-! ## Collect paths of sequents within a LocalTableau (move to LocalTableau.lean later?)

This may be useful for the pre-states used in the completeness proof. -/

-- TODO golf/shorten this
/-- LocalRuleApp preserves saturatedness backwards. -/
lemma LocalRuleApp.preserve_saturated_up (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, ∀ (rest : List Sequent) ,
      Y ∈ rest →
      saturated (rest.map Sequent.bothSides).flatten.toFinset
        → saturated (((lra.X :: rest).map Sequent.bothSides).flatten.toFinset) := by
  intro Y hY rest hYr hs
  simp only [saturated] at hs ⊢
  intro φ ψ α
  have old_or_rest (f : Formula) :
      f ∈ ((lra.X :: rest).map Sequent.bothSides).flatten.toFinset →
      f ∈ lra.X.bothSides ∨ f ∈ (rest.map Sequent.bothSides).flatten.toFinset := by
    simp only [List.map_cons, List.flatten_cons, List.mem_toFinset, List.mem_append]
    exact id
  have child_in_rest (f : Formula) (hf : f ∈ Y.bothSides) :
      f ∈ (rest.map Sequent.bothSides).flatten.toFinset := by
    simp only [List.mem_toFinset, List.mem_flatten, List.mem_map]
    exact ⟨Y.bothSides, ⟨Y, hYr, rfl⟩, hf⟩
  have lift_rest (f : Formula) :
      f ∈ (rest.map Sequent.bothSides).flatten.toFinset →
      f ∈ ((lra.X :: rest).map Sequent.bothSides).flatten.toFinset := by simp_all
  have source_closure := lra.formula_preserved_or_expanded hY
  rcases hs φ ψ α with ⟨hneg, hcon, hncon, hbox, hdia⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact lift_rest _ (hneg (child_in_rest _ hkeep))
      · exact lift_rest _ (child_in_rest _ ((hexpand φ ψ α).1 rfl))
    · exact lift_rest _ (hneg hrest)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hcon (child_in_rest _ hkeep) with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
      · rcases (hexpand φ ψ α).2.1 rfl with ⟨hφ, hψ⟩
        exact ⟨lift_rest _ (child_in_rest _ hφ), lift_rest _ (child_in_rest _ hψ)⟩
    · rcases hcon hrest with ⟨hφ, hψ⟩
      exact ⟨lift_rest _ hφ, lift_rest _ hψ⟩
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · exact (hncon (child_in_rest _ hkeep)).imp (lift_rest _) (lift_rest _)
      · rcases (hexpand φ ψ α).2.2.1 rfl with hφ | hψ
        · exact Or.inl (lift_rest _ (child_in_rest _ hφ))
        · exact Or.inr (lift_rest _ (child_in_rest _ hψ))
    · exact (hncon hrest).imp (lift_rest _) (lift_rest _)
  constructor
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hbox (child_in_rest _ hkeep) with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.1 rfl with ⟨l, hl⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hl
        exact ⟨l, by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hl f hf))⟩
    · rcases hbox hrest with ⟨l, hl⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hl
      exact ⟨l, by simpa using fun f hf => lift_rest _ (by simpa using hl f hf)⟩
  · intro h
    rcases old_or_rest _ h with hsrc | hrest
    · rcases source_closure _ hsrc with hkeep | hexpand
      · rcases hdia (child_in_rest _ hkeep) with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩
      · rcases (hexpand φ ψ α).2.2.2.2 rfl with ⟨Fδ, hD, hF⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hF
        exact ⟨ Fδ, hD
              , by simpa using fun f hf => lift_rest _ (child_in_rest _ (by simpa using hF f hf))⟩
    · rcases hdia hrest with ⟨Fδ, hD, hF⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hF
      exact ⟨Fδ, hD, by simpa using fun f hf => lift_rest _ (by simpa using hF f hf)⟩

def LocalTableau.paths : {X : _} → LocalTableau X → List (List Sequent)
  | .(_), (@byLocalRule X lra _ next) =>
      (lra.C.attach.flatMap (fun ⟨Y, h⟩ => (next Y h).paths)).map (X :: ·)
  | .(_), (@sim X _) => [[X]]
termination_by
  X => X -- pick up instance WellFoundedRelation Sequent from above!
decreasing_by
  subst_eqs
  apply localRuleApp.decreases_DM lra Y h

lemma LocalTableau.paths_mem_nonempty {X} (lt : LocalTableau X) :
    ∀ L ∈ lt.paths, L ≠ [] := by
  intro L L_in; cases lt <;> grind [paths]

lemma LocalTableau.pathsHead_eq_self {X} {lt : LocalTableau X} :
    ∀ {L}, (h : L ∈ lt.paths) → L.head (LocalTableau.paths_mem_nonempty lt _ h) = X := by
  cases lt <;> simp_all [paths]
  case byLocalRule lra next X_def =>
    intro L1 Y Z Z_in Y_in def_L1
    subst def_L1
    simp

lemma LocalTableau.pathsLast_eq_endNodes {X} {lt : LocalTableau X} :
    lt.paths.attach.map
      (fun ⟨L,h⟩ => L.getLast (LocalTableau.paths_mem_nonempty lt L h)) = endNodesOf lt := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    -- this case is from aristotle.harmonic.fun
    have map_attach_last (ls : List (List Sequent)) (hne : ∀ L ∈ ls, L ≠ []) :
        ls.attach.map (fun ⟨L, h⟩ => (fun x => some x) (L.getLast (hne L h))) =
          ls.map List.getLast? := by
      induction ls with
      | nil => simp
      | cons L ls ih =>
        simp only [List.attach_cons, List.map_cons, List.cons.injEq]
        constructor
        · exact (List.getLast?_eq_some_getLast (hne L (by simp))).symm
        · simpa only [List.map_map] using
            ih (fun K h => hne K (by simp [h]))
    apply (Option.some_injective Sequent).list_map
    simp only [List.map_map]
    change (LocalTableau.byLocalRule lra X_def next).paths.attach.map
      (fun ⟨L, h⟩ => some (L.getLast (LocalTableau.paths_mem_nonempty _ L h))) = _
    rw [map_attach_last (LocalTableau.byLocalRule lra X_def next).paths
      (LocalTableau.paths_mem_nonempty _)]
    simp only [paths, endNodesOf, List.map_flatMap]
    have map_flatten (xss : List (List Sequent)) :
        List.map some xss.flatten = (xss.map (List.map some)).flatten := by
      induction xss <;> simp_all
    rw [map_flatten]
    apply congrArg List.flatten
    simp only [List.map_map]
    apply List.map_inj_left.mpr
    intro Yh Yh_in
    rcases Yh with ⟨Y, Y_in⟩
    rw [show List.map (List.getLast? ∘ List.cons X) (next Y Y_in).paths =
      List.map List.getLast? (next Y Y_in).paths by
        apply List.map_inj_left.mpr
        intro L L_in
        have hne := LocalTableau.paths_mem_nonempty (next Y Y_in) L L_in
        change (X :: L).getLast? = L.getLast?
        rw [List.getLast?_eq_some_getLast hne,
          List.getLast?_eq_some_getLast (List.cons_ne_nil X L)]
        exact congrArg some (List.getLast_cons hne)]
    have hIH := congrArg (List.map some) (IH Y Y_in)
    simp only [List.map_map] at hIH
    change (next Y Y_in).paths.attach.map
      (fun ⟨L, h⟩ => some (L.getLast (LocalTableau.paths_mem_nonempty _ L h))) = _ at hIH
    rw [map_attach_last (next Y Y_in).paths
      (LocalTableau.paths_mem_nonempty (next Y Y_in))] at hIH
    exact hIH
  case sim bas =>
    simp_all [paths]
    ext
    simp [paths]
    grind

/-- Any open local tableau has at least one path (from root to some end node).
Does not hold for `LocalTableau` which might end with "contradiction/closing" rule applications. -/
lemma OpenLocalTableau.paths_nonempty {X} (lt : OpenLocalTableau X) :
    lt.1.paths ≠ [] := by
  rcases lt with ⟨lt, lt_has_ends⟩
  have := @LocalTableau.pathsLast_eq_endNodes X lt
  grind

lemma LocalTableau.paths_last_basic {X} {lt : LocalTableau X} :
    ∀ L, (h : L ∈ lt.paths) → (L.getLast (LocalTableau.paths_mem_nonempty lt L h)).basic := by
  intro L L_in
  apply (@endNodesOf_basic _ _ lt)
  rw [← @LocalTableau.pathsLast_eq_endNodes _ lt]
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  grind

@[simp]
lemma Sequent.bothSides_toFinset_eq_toFinset {X : Sequent} :
    X.bothSides.toFinset = X.toFinset := by
  rcases X with ⟨L,R,O⟩
  unfold Sequent.bothSides Sequent.toFinset
  simp
  rcases O with _|(_|_) <;> simp

lemma LocalTableau.paths_saturated {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths,
      saturated (List.map Sequent.bothSides L).flatten.toFinset := by
  cases lt
  case byLocalRule lra next X_def =>
    intro L L_in
    simp [paths] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, def_L⟩
    have IH := LocalTableau.paths_saturated _ L'_in
    subst def_L
    subst X_def
    -- use separate lemma "LocalRuleApp preserves saturatedness backwards" here.
    apply @lra.preserve_saturated_up Y Y_in _ ?_ IH
    -- because L' is a path from `next y : LocalTableau Y` it must start with Y.
    have := LocalTableau.pathsHead_eq_self L'_in
    grind
  case sim Xbas =>
    simp [paths]
    have := X.basic_then_saturated
    exact Sequent.basic_then_saturated Xbas
termination_by
  X -- using DM ordering on `X` here
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-- An atomic formula anywhere in a local tableau path still occurs at the end of the path. -/
lemma LocalTableau.paths_local_atom_mem_last {X} {lt : LocalTableau X} {L} (L_in : L ∈ lt.paths) f :
    (f = ⊥ ∨ ∃ p : Nat, f = (Formula.atom_prop p) ∨ f = (~(Formula.atom_prop p))) →
      f ∈ (List.map Sequent.bothSides L).flatten →
        f ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).bothSides := by
  cases lt
  case byLocalRule lra next X_def =>
    intro f_kind f_in
    simp [paths] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have L'_ne := LocalTableau.paths_mem_nonempty (next Y Y_in) L' L'_in
    rw [List.getLast_cons L'_ne]
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at f_in
    apply LocalTableau.paths_local_atom_mem_last L'_in f f_kind
    rcases f_in with f_in_X | f_in_tail
    · have f_in_Y := lra.preserve_local_atom_down Y Y_in f f_kind (by simpa [X_def] using f_in_X)
      have head_eq := LocalTableau.pathsHead_eq_self L'_in
      rcases L' with _ | ⟨Z, L''⟩
      · contradiction
      · simp only [List.map_cons, List.flatten_cons, List.mem_append]
        left
        simp only [List.head_cons] at head_eq
        subst Y
        exact f_in_Y
    · exact f_in_tail
  case sim bas =>
    intro f_kind f_in
    simp [paths] at L_in
    subst L
    simpa using f_in
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-! ## Collecting Sequents for Pre-states

As possible worlds for the model graph we want to define *maximal* paths inside the build tree
that do not contain (M), (L+) or (L-) steps.

We collect the sequents along such paths directly by induction on the `BuildTree`. -/

/-- Collect pre-states in the whole BuildTree.
The local pre-states come from paths in a local tableau,
and PDL pre-states each consist of just a single node. -/
def BuildTree.collect {H X} : (bt : BuildTree H X) → List (List Sequent)
  | .loc _ _ next => (OpenLocalTableau.all X).flatMap fun lt => lt.1.paths ++ (next lt).6.collect
  | .pdl _ _ next => [ [X] ] ++ (PdlRule.all X).flatMap fun ⟨Y,r⟩ => (next Y r).collect
  | .freeRepeat _ => [ ] -- Not generating a pre-state here, go to companion instead !! ?? !!
  | .openLeaf _ _ => [ [X] ]
termination_by
  bt => bt.size -- size of remaining BuildTree should go down
decreasing_by
  · exact size_lt_loc H X _ next lt _
  · exact size_lt_pdl H X _ _ next Y r

lemma BuildTree.collect_nonempty (bt : BuildTree [] X) :
    bt.collect ≠ [] := by
  cases bt
  case loc nbas someLT next =>
    simp only [collect, ne_eq, List.flatMap_eq_nil_iff, List.append_eq_nil_iff, not_forall, not_and]
    rcases List.exists_mem_of_ne_nil _ someLT with ⟨lt, lt_in⟩
    use lt, lt_in
    have := OpenLocalTableau.paths_nonempty lt -- new :-)
    tauto
  all_goals
    simp [collect]
  case freeRepeat h =>
    exact FreeRepeat_nil_impossible h

lemma BuildTree.collect_contains_root (bt : BuildTree [] X) :
    ∃ π ∈ bt.collect, X ∈ π := by
  cases bt <;> simp [collect]
  case loc nbas someLT next =>
    rcases List.exists_mem_of_ne_nil _ someLT with ⟨lt, lt_in⟩
    let πs := lt.1.paths
    have πs_ne : πs ≠ [] := OpenLocalTableau.paths_nonempty lt
    rcases πs.exists_mem_of_ne_nil πs_ne with ⟨π, π_in⟩
    refine ⟨π, ⟨lt, lt.all_spec, .inl π_in⟩, ?_⟩
    have := @LocalTableau.pathsHead_eq_self X lt.1 π
    grind
  case freeRepeat h =>
    exact FreeRepeat_nil_impossible h

/-! ## Pre-states (Def 6.13) -/

/-- A pre-state is a list of sequents collected from a `BuildTree`. -/
def PreState {H X} (bt : BuildTree H X) : Type := Subtype (· ∈ bt.collect)

lemma PreState.nonempty {X} {bt : BuildTree H X} {π : PreState bt} : π.val ≠ [] := by
  rcases π with ⟨L, L_in⟩
  unfold BuildTree.collect at L_in
  simp_all
  cases bt
  case loc nbas someLT next L_in' =>
    simp_all
    rcases L_in with ⟨lt, lt_in, L_in⟩
    rcases L_in with L_in|L_in
    · exact LocalTableau.paths_mem_nonempty lt.1 L L_in
    · have IH := @PreState.nonempty _ _ (next lt).6 ⟨L, L_in⟩
      exact IH
  case pdl bas next L_in' =>
    simp_all
    rcases L_in with L_def|⟨Y, r, rule_in, L_in⟩
    · simp_all
    · have IH := @PreState.nonempty _ _ (next Y r) ⟨L, L_in⟩
      exact IH
  all_goals
    simp_all
termination_by
  bt.size
decreasing_by -- almost same termination proof as for Match.all etc above :-)
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

-- NOTE: all π.sequents have at most length 2 ??

/-! ## Collecting Formulas in Pre-state Sequents -/

/-- Λ(π) gets all formulas for a pre-state but keep the information what is loaded.
Returns the `WhateverFormula` type so that lemmas like 6.15 and 6.18 are sayable. -/
def PreState.wForms {bt : BuildTree H X} (π : PreState bt) : Finset WhateverFormula :=
  (π.val.map Sequent.wForms).flatten.toFinset

/-- Λ⁻(π) gets all formulas from a pre-state π, via unloading if needed. -/
def PreState.forms {bt : BuildTree H X} (π : PreState bt) : Finset Formula :=
  (π.val.map Sequent.bothSides).flatten.toFinset

-- TODO lemmas connecting π.wForms and π.forms:
-- if negloaded is in wForms, then its unloading is in forms
-- if loaded is in wForms, then its unloading is in forms
-- normal is in wForms iff it is in forms
-- normal is in forms iff ...
lemma PreState.mem_forms_iff {φ : Formula} {π : PreState bt} :
    φ ∈ π.forms ↔
      ( (.any (.normal φ) : WhateverFormula) ∈ π.wForms
      ∨ (∃ χ, χ.unload = φ ∧ (.any (.loaded χ) ∈ π.wForms))
      ∨ (∃ ψ, negUnload ψ = φ ∧ (.negLoad ψ ∈ π.wForms))
      ) := by
  simp only [PreState.forms, PreState.wForms, List.mem_toFinset]
  constructor
  · intro h
    rw [List.mem_flatten] at h
    rcases h with ⟨Fs, Fs_in, hφ⟩
    rw [List.mem_map] at Fs_in
    rcases Fs_in with ⟨X, X_in, rfl⟩
    rw [Sequent.mem_bothSides_iff] at hφ
    grind
  · rintro (h | ⟨χ, hχ, h⟩ | ⟨ψ, hψ, h⟩)
    all_goals
      rw [List.mem_flatten] at h
      rcases h with ⟨wFs, wFs_in, hw⟩
      rw [List.mem_map] at wFs_in
      rcases wFs_in with ⟨X, X_in, rfl⟩
      apply List.mem_flatten.mpr
      refine ⟨X.bothSides, List.mem_map.mpr ⟨X, X_in, rfl⟩, ?_⟩
      rw [Sequent.mem_bothSides_iff]
    · exact Or.inl hw
    · exact Or.inr (Or.inl ⟨χ, hχ, hw⟩)
    · exact Or.inr (Or.inr ⟨ψ, hψ, hw⟩)

lemma PreState.forms_saturated {X} {bt : BuildTree H X} {π : PreState bt} :
    saturated π.forms := by
  -- Idea: case distinction between local pre-state or pdl-prestate.
  -- For local, use `LocalTableau.paths_saturated`
  -- For PDL pre-state, use `Sequent.basic_then_saturated`.
  -- For any pre-state from later, make an IH by recursion and use it?
  rcases π with ⟨π, π_in⟩
  cases bt <;> simp [BuildTree.collect] at π_in <;> rename_i old_π_in
  case loc nbas next =>
    rcases π_in with ⟨lt, lt_in, π_in_lt|π_in_next⟩
    · exact LocalTableau.paths_saturated _ π_in_lt
    · have IH := @PreState.forms_saturated _ _ _ ⟨π, π_in_next⟩
      exact IH
  case pdl bas someR next =>
    rcases π_in with π_def|⟨Y, r, in_rule, π_in_next⟩
    · subst π_def
      simp [forms]
      exact Sequent.basic_then_saturated bas
    · have IH := @PreState.forms_saturated _ _ _ ⟨π, π_in_next⟩
      exact IH
  case openLeaf bas noRule =>
    subst π_in
    simp [forms]
    exact Sequent.basic_then_saturated bas
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

lemma Sequent.basic_to_locallyConsistent {X : Sequent} (bas : X.basic) :
    locallyConsistent X.toFinset := by
  rcases X with ⟨L, R, O⟩
  unfold locallyConsistent Sequent.toFinset at *
  constructor
  · intro hbot
    apply bas.2
    unfold Sequent.closed
    left
    simp_all
  · intro p hp hnp
    apply bas.2
    unfold Sequent.closed
    right
    refine ⟨(·p), ?_, ?_⟩
    · simp_all
    · simp_all
      rcases hnp with h | h | ⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩
      · exact Or.inl h
      · exact Or.inr h
      · rcases a with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at ha
      · rcases b with ⟨⟨α, af⟩⟩
        cases af <;> simp [LoadFormula.unload] at hb

lemma LocalTableau.paths_locallyConsistent {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths,
      locallyConsistent (List.map Sequent.bothSides L).flatten.toFinset := by
  intro L L_in
  have last_basic := LocalTableau.paths_last_basic L L_in
  have last_consistent := Sequent.basic_to_locallyConsistent last_basic
  unfold locallyConsistent at *
  constructor
  · intro bot_in
    simp only [Finset.mem_val, List.mem_toFinset] at bot_in
    apply last_consistent.1
    rw [← Sequent.bothSides_toFinset_eq_toFinset]
    exact List.mem_toFinset.mpr <|
      LocalTableau.paths_local_atom_mem_last L_in ⊥ (Or.inl rfl) bot_in
  · intro p p_in neg_p_in
    simp only [Finset.mem_val, List.mem_toFinset] at p_in neg_p_in
    apply last_consistent.2 p
    · rw [← Sequent.bothSides_toFinset_eq_toFinset]
      exact List.mem_toFinset.mpr <|
        LocalTableau.paths_local_atom_mem_last L_in (Formula.atom_prop p)
          (Or.inr ⟨p, Or.inl rfl⟩) p_in
    · rw [← Sequent.bothSides_toFinset_eq_toFinset]
      exact List.mem_toFinset.mpr <|
        LocalTableau.paths_local_atom_mem_last L_in (~(Formula.atom_prop p))
          (Or.inr ⟨p, Or.inr rfl⟩) neg_p_in

-- IDEA: helper lemma "every pre-state is either a local tableau path or a singleton and basic" ??

lemma PreState.forms_locallyConsistent {H X} {bt : BuildTree H X} {π : PreState bt} :
    locallyConsistent π.forms := by
  rcases π with ⟨π, π_in⟩
  cases bt <;> simp [BuildTree.collect] at π_in <;> rename_i π_in_old
  case loc nbas next =>
    rcases π_in with ⟨lt, lt_in, π_in_lt|π_in_next⟩
    · exact LocalTableau.paths_locallyConsistent _ π_in_lt
    · have IH := @PreState.forms_locallyConsistent _ _ _ ⟨π, π_in_next⟩
      exact IH
  case pdl bas someR next =>
    rcases π_in with π_def|⟨Y, r, in_rule, π_in_next⟩
    · subst π_def
      simp_all only [forms, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, Sequent.bothSides_toFinset_eq_toFinset]
      apply Sequent.basic_to_locallyConsistent bas
    · have IH := @PreState.forms_locallyConsistent _ _ _ ⟨π, π_in_next⟩
      exact IH
  case openLeaf bas noRule =>
    subst π_in
    simp [forms]
    apply Sequent.basic_to_locallyConsistent bas
termination_by
  bt.size
decreasing_by
  · subst_eqs; apply BuildTree.size_lt_loc
  · subst_eqs; apply BuildTree.size_lt_pdl

lemma PreState.forms_last_basic {bt : BuildTree H X} {π : PreState bt} :
    (π.val.getLast PreState.nonempty).basic := by
  rcases π with ⟨π, π_in⟩
  cases bt <;> simp [BuildTree.collect] at π_in <;> rename_i π_in_old
  case loc nbas next =>
    rcases π_in with ⟨lt, lt_in, π_in_lt|π_in_next⟩
    · exact LocalTableau.paths_last_basic _ π_in_lt
    · have IH := @PreState.forms_last_basic _ _ _ ⟨π, π_in_next⟩
      exact IH
  case pdl bas someR next =>
    rcases π_in with π_def|⟨Y, r, in_rule, π_in_next⟩
    · subst π_def
      simp only [List.getLast_singleton]
      exact bas
    · have IH := @PreState.forms_last_basic _ _ _ ⟨π, π_in_next⟩
      exact IH
  case openLeaf =>
    subst π_in
    simp_all
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

/-! ## PreStates to Matches and back again

IDEA / TODO: to prove the existence lemmas it seems useful to have helper lemmas/defs
to switch between Pre-states & matches. Can we show these?

- every pre-state must come from some match

- every match gives us a pre-state

If we have these, then we can use `Match.rewind` to "roll back up".

Note: the functions will not necessarily "round-trip".

Small worry: there is no order on Pre-States, so termination of this IH might be an issue?
Idea: use the PreState-to-Match conversion and then the Match-length as termination_by.
-/

-- TODO lemma: the result of .collect in any sub-BuildTree later (reached by some Match)
-- is also part of .collect applied to the the bigger BuildTree.

/-- For any `Match` there exists a `PreState`
containing a sequent `setEqTo` the end nof the Match. -/
lemma Match.existsPreState {bt : BuildTree [] X} (m : Match bt) :
    ∃ π : PreState bt, ∃ Z ∈ π.1, m.btAt.2.1.setEqTo Z := by
  rcases mbtAt_def : m.btAt with ⟨H', X', bt'⟩
  -- NOTE: tempting to use bt'.collect_contains_root but that would need `H' = []`.
  cases bt'
  case loc nbas someLT next =>
    simp_all
    rcases List.exists_mem_of_ne_nil _ someLT with ⟨lt, lt_in⟩
    rcases List.exists_mem_of_ne_nil _ lt.paths_nonempty with ⟨L, L_in⟩
    refine ⟨⟨L, ?_⟩ , ?_⟩
    · -- apply "collect from sub-BuildTree" lemma
      sorry
    · simp_all
      have := LocalTableau.pathsHead_eq_self L_in
      use X'
      simp
      grind
  case pdl bas someR next =>
    refine ⟨⟨[X'], ?_⟩ , by simp⟩
    -- apply "collect from sub-BuildTree" lemma
    sorry
  case freeRepeat frep =>
    -- We don't make a PreState here but go to companion first.
    simp only
    cases frep
    have m_frep : m.isFreeRepeat := by unfold isFreeRepeat; grind
    let compy := m.companionOf m_frep
    have IH := compy.existsPreState
    rcases IH with ⟨π, Z, Z_in_π, _same_Z⟩
    use π, Z, Z_in_π
    -- Using lemma that companion has the a setEqTo sequent.
    have := m.companionOf_setEqTo_sequent m_frep
    refine Sequent.setEqTo_trans _ compy.btAt.snd.fst _ ?_ _same_Z
    unfold compy
    rw [Sequent.setEqTo_symm]
    convert this
    grind
  case openLeaf =>
    refine ⟨⟨[X'], ?_⟩, by simp⟩
    -- apply "collect from sub-BuildTree" lemma
    sorry
termination_by
  m.length
decreasing_by
  -- Need lemma that companion is a shorter `Match`?
  sorry

-- TODO combining .exists_PreState and List.find? ???
def Match.toPreState {bt : BuildTree [] X} (m : Match bt) : PreState bt := by
  sorry

def PreState.toMatch {bt : BuildTree [] X} (π : PreState bt) : Match bt := by
  rcases π with ⟨π, π_in⟩
  unfold BuildTree.collect at π_in
  cases bt <;> simp at π_in
  case loc nbas someLT next =>
    sorry
  case pdl =>
    sorry
  case openLeaf =>
    sorry

/-- Round-trip. The other order does not hold because π may occur multiple times in bt. -/
lemma PreState.toMatch_toPreState {X} {bt : BuildTree [] X} (π : PreState bt) :
    π.toMatch.toPreState = π := by
  sorry

/-! ## Properties of Formula (Sets? Lists?) obtained from Pre-States -/

-- IDEA: rephrase these to be about the resulting chain, not about getForms !!

/-- TODO Lemma 6.14 (NOTE: maybe just skip this one?!) -/
lemma PreState.formsCases {π : PreState bt} : φ ∈ π.forms →
      (φ.basic ∧ φ ∈ π.val.getLast PreState.nonempty)
      -- NOTE: the `∈` might not deal with loaded formulas yet.
    ∨ (sorry) := by -- TODO how to say `φ is principal later?`
    -- Or can we say something else / phrase it as closure condition about π.forms directly?
  sorry

/-- Lemma 6.15 *free* case -/
lemma PreState.freeUnfoldDiaMem_of_nonAtom {X} {bt : BuildTree [] X} {π : PreState bt} {α φ} :
    ¬ α.isAtomic → (~⌈α⌉φ : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1 ∪ [~ Formula.boxes Xδ.2 φ]).all (· ∈ π.wForms) := by
  intro α_notAtom in_forms
  rcases π with ⟨π, π_in⟩
  -- IDEA
  -- If π comes from a .pdl step then it must be basic, use `absurd α_notAtom`.
  -- So π must come from a .loc step, and somewhere in the loc tab the unfold rule must be used?
  sorry

/-- Lemma 6.15 *loaded* case with _more than one_ loaded box -/
lemma PreState.loadUnfoldDiaMem_of_nonAtom {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    (χ : LoadFormula) :
    ¬ α.isAtomic → (.negLoad (~'⌊α⌋χ) : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1).all (· ∈ π.wForms)
                    ∧ (YsetLoad Xδ χ).2.toList.all (· ∈ π.wForms) := by
  sorry

/-- Lemma 6.15 *loaded* case with only _one_ loaded box. -/
lemma PreState.loadUnfoldDiaMem_of_nonAtom' {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    {φ : Formula} :
    ¬ α.isAtomic → (.negLoad (~'⌊α⌋φ) : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1).all (· ∈ π.wForms)
                    ∧ (YsetLoad' Xδ φ).2.toList.all (· ∈ π.wForms) := by
  sorry

/-- Lemma 6.16: pre-states are saturated and locally consistent, their last node is basic. -/
lemma PreState.locConsSatBas {X} {bt : BuildTree [] X} (π : PreState bt) :
    saturated π.forms
    ∧ locallyConsistent π.forms
    ∧ (π.val.getLast PreState.nonempty).basic :=
  ⟨π.forms_saturated, π.forms_locallyConsistent, π.forms_last_basic⟩

/-! ## Defining The Model Graph -/

/-- Definition 6.17 to get model graph from strategy tree. -/
@[simp]
def BuildTree.toModel {X} (bt : BuildTree [] X) :
    (Σ W : Finset (Finset Formula), KripkeModel W) :=
  ⟨ ((bt.collect).attach.map (PreState.forms)).toFinset -- W -- NOTE .forms here, not .wforms
  , { val := fun X p => Formula.atom_prop p ∈ X.1 -- valuation V(p)
    , Rel := fun a X Y => -- relation Rₐ
        ∃ φ, (~⌈·a⌉φ) ∈ X.1 ∧ (projection a X.1.toList).toFinset ∪ {~φ} ⊆ Y.1 }⟩

/-- Helper lemma saying (the formula sets of) all pre-states are in the model graph. -/
lemma PreState.mem_toModel {X : Sequent} {bt : BuildTree [] X} {π : PreState bt} :
    π.forms ∈ bt.toModel.fst := by
  simp
  use π
  simp
  apply List.mem_attach

instance {bt : BuildTree [] X} : Coe (PreState bt) { w : Finset Formula // w ∈ bt.toModel.1 } :=
  ⟨fun π => ⟨π.forms, π.mem_toModel⟩⟩

/-! ## Existence Lemmas -/

/-- Lemma 6.18.
Note that we use `Rel` from `BuildTree.toModel` as the `R` to use `Modelgraphs.Q`.

TODO: use Match.toPreState (after defining it) to say that node `t` is "lying" on `π`.
Also still missing the `t < u` part. Is it needed? -/
lemma PreState.loadedDiamondExistence {φ : AnyFormula} {π : PreState bt} :
  (~'⌊α⌋φ : WhateverFormula) ∈ π.wForms →
    ∃ t : Match bt,
        AnyNegFormula.mem_Sequent (t.btAt).2.1 (~''φ)
      ∧ ∃ ρ : PreState bt,
          ∃ u : Match bt,
        @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π ρ := by
  sorry

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded


/-- TODO: Induction loading for 6.20. -/
lemma freeDiamondExistenceInduction {X} {bt : BuildTree [] X}
    {ψ : Formula} -- FIXME also need that ψ is not boxed
    {α} {ηs : List Program} {π : PreState bt} :
    (~⌈α⌉⌈⌈ηs⌉⌉ψ : WhateverFormula) ∈ π.wForms →
      ∃ π' : PreState bt,
        (~⌈⌈ηs⌉⌉ψ) ∈ π'.forms -- NOTE: may occur loaded or unloaded in Λ(π')
        ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro _in_forms
  sorry

/-- Lemma 6.20: free diamond existence lemma for pre-states -/
lemma freeDiamondExistence {X} {bt : BuildTree [] X} {α} {φ : Formula} {π : PreState bt} :
  (~⌈α⌉φ : WhateverFormula) ∈ π.wForms → ∃ π' : PreState bt,
      ~φ ∈ π'.forms ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro in_forms
  let ηs_ψ := boxesOf φ
  have := @freeDiamondExistenceInduction X bt ηs_ψ.2 α ηs_ψ.1 π ?in_forms
  case in_forms =>
    convert in_forms
    exact Eq.symm (def_of_boxesOf_def rfl)
  rcases this with ⟨π', in_π'_forms, α_rel⟩
  refine ⟨π', ?_, α_rel⟩
  · convert in_π'_forms
    exact def_of_boxesOf_def rfl

/-! ## Model graph of pre-states -/

-- FIXME move me

lemma BuildTree.exists_mem_attach_forms_eq {bt : BuildTree [] H} {ρ : PreState bt} :
    ∃ a ∈ bt.collect.attach, PreState.forms a = ρ.forms := by
  simp


/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph.
Uses `BuildTree.toModel`. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS),
      ∃ Z ∈ WS, X.bothSides.toFinset ⊆ Z := by
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
    have := π.locConsSatBas -- using Lemma 6.16 for (i)
    simp_all [PreState.forms]
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
    simp only [Subtype.exists, exists_and_right, Subtype.forall]
    intro w w_in α φ in_w
    -- "The main challenge" :-)
    -- Paper proof uses Lemmas 6.18 and 6.20 here, depending on loading.
    unfold WS BuildTree.toModel at w_in
    simp only [List.mem_toFinset, List.mem_map] at w_in
    -- w must come from some pre-state:
    rcases w_in with ⟨π, π_in, def_w⟩
    subst def_w
    -- unfold PreState.forms at in_w -- NO, use lemma to switch to wforms instead?
    rw [PreState.mem_forms_iff] at in_w
    rcases in_w with in_w|(⟨χ,χul_def,in_w⟩|⟨ψ,ψul_def,in_w⟩)
    · -- normal, use 6.20
      rcases freeDiamondExistence in_w with ⟨π', in_π'_forms, α_rel⟩
      refine ⟨π'.forms, ⟨?_, α_rel⟩, in_π'_forms⟩
      unfold WS
      simp only [BuildTree.toModel, Finset.union_singleton, List.mem_toFinset, List.mem_map]
      exact bt.exists_mem_attach_forms_eq
    · -- loaded but not negated, cannot happen
      exfalso
      cases χ
      unfold LoadFormula.unload at χul_def
      grind
    · -- neg loaded, use 6.18
      rcases ψ with ⟨⟨α',χ⟩ ⟩
      simp only [negUnload, Formula.neg.injEq] at ψul_def
      rcases PreState.loadedDiamondExistence in_w with ⟨t, in_t, ρ, u, α_rel⟩
      unfold WS
      simp only [BuildTree.toModel, Finset.union_singleton, List.mem_toFinset, List.mem_map]
      refine ⟨ρ.forms, ⟨bt.exists_mem_attach_forms_eq, ?_⟩, ?_⟩
      · have : α = α' := by cases χ <;> grind [LoadFormula.unload]
        rw [this]
        exact α_rel
      · -- use `in_t : AnyNegFormula.mem_Sequent t.btAt.snd.fst (~''χ)` here.
        -- But better adjust the statement of `PreState.loadedDiamondExistence` first.
        sorry
  case X_in =>
    unfold WS
    -- Here the def of `BuildTree.allPreStates` matters.
    simp
    -- Use that there must be some pre-state containing the root.
    rcases bt.collect_contains_root with ⟨π, π_in, X_in_π⟩
    refine ⟨⟨π, π_in⟩, ?_, ?_⟩
    · apply List.mem_attach
    · intro φ φ_in
      unfold PreState.forms
      simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, exists_exists_and_eq_and]
      use X
      rw [← X.bothSides_toFinset_eq_toFinset] at φ_in
      simp [-Sequent.bothSides_toFinset_eq_toFinset] at φ_in
      grind
