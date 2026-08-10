import Pdl.TableauGame
import Pdl.LocalTableauPaths
import Pdl.PdlSteps

/-! # From winning strategies to model graphs, part 1: BuildTree and PreState (Section 6.3) -/

/-! ## Builder Strategy Tree -/

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
  | freeRepeat {H X} : FreeRepeat H X → BuildTree H X
  /-- Leaf that is (might be?!) not a repeat, but no rules can be applied. -/
  | openLeaf {H X} (bas : X.basic) (noRule : PdlRule.all X = []) : BuildTree H X
  -- Note that (L+) (L-) are *not* always applicable, because tehre might be no diamond left.
  -- And even when there is a diamond, eventually (L+) and (L-) would lead to a free repeat.
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

/-- The node picked by Builder is one of the given ones. -/
lemma BuildChoice.frth_mem {H X YS} {bc : BuildChoice H X YS} : bc.4 ∈ YS := by
  cases bc; assumption

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

/-- Appending matches: the node reached is the one reached by the second match. -/
lemma Match.btAt_append {H X} {bt : BuildTree H X} (m : Match bt) (c : Match m.btAt.2.2) :
    (m.append c).btAt = c.btAt := by
  induction m with
  | nil => rfl
  | loc tail IH => exact IH _
  | pdl tail IH => exact IH _

/-- Appending matches: the sequent reached is the one reached by the second match. -/
lemma Match.endSeq_append {H X} {bt : BuildTree H X} (m : Match bt) (c : Match m.btAt.2.2) :
    (m.append c).endSeq = c.endSeq := by
  unfold Match.endSeq
  rw [Match.btAt_append]

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

/-- Roll back to the companion. Only possibe if we started with H=[] so we know the root.
The `+ 1` is there because the `FreeRepeat` values are indices of the history starting with 0,
but `Match.rewind 0` would do nothing. (Same as the `.succ` in `companionOf` for `PathIn`.) -/
def Match.companionOf {X} {bt : BuildTree [] X} (m : Match bt)
  (h : m.isFreeRepeat) : Match bt :=
    match m.getFreeRepeat h with
    -- The free repeat says "go k steps back" where k < length of history at `m`.
    | ⟨⟨k, k_lt⟩ , same_and_free⟩ =>
      -- But to rewind m we need a k + 1 < length of m itself plus 1
      m.rewind ⟨k + 1, by grind [Match.btAt_newHist_length_eq_length_plus_oldHist]⟩

/-- The sequents visited by a `Match`, in reverse order and not including the last one.
Analogous to `PathIn.toHistory`. -/
def Match.toHistory {H X} {bt : BuildTree H X} : Match bt → History
| .nil => []
| .loc tail => tail.toHistory ++ [X]
| .pdl tail => tail.toHistory ++ [X]

@[simp]
lemma Match.toHistory_length {H X} {bt : BuildTree H X} (m : Match bt) :
    m.toHistory.length = m.length := by
  induction m <;> simp_all [toHistory]

/-- The history reached by a `Match` consists of the sequents visited, then the old history. -/
lemma Match.toHistory_append_eq_btAt_fst {H X} {bt : BuildTree H X} (m : Match bt) :
    m.toHistory ++ H = m.btAt.1 := by
  induction m <;> simp_all [toHistory, btAt]

@[simp]
lemma Match.rewind_last {H X} {bt : BuildTree H X} (m : Match bt) :
    m.rewind (Fin.last m.length) = .nil := by
  cases m
  · rfl
  · rw [rewind]; exact Fin.lastCases_last
  · rw [rewind]; exact Fin.lastCases_last

/-- Rewinding a `Match` by `k` steps gives the `k`-th element of the history,
where the end sequent of the match itself is counted as the `0`-th element.
Inspired by `PathIn.nodeAt_rewind_eq_toHistory_get`. -/
lemma Match.btAt_rewind_eq_toHistory_get {H X} {bt : BuildTree H X} (m : Match bt)
    (k : Fin (m.length + 1)) :
    (m.rewind k).btAt.2.1 = (m.btAt.2.1 :: m.toHistory).get (Fin.cast (by simp) k) := by
  induction m
  case nil H X bt =>
    rcases k with ⟨k, k_lt⟩
    simp only [length, zero_add, Nat.lt_one_iff] at k_lt
    subst k_lt
    simp [rewind, btAt, toHistory]
  case loc H X nbas someLT next lt tail IH =>
    cases k using Fin.lastCases
    case last =>
      have hlast : Match.rewind (bt := BuildTree.loc nbas someLT next) (Match.loc tail)
          (Fin.last _) = Match.nil := by
        rw [rewind]; exact Fin.lastCases_last
      rw [hlast]
      simp only [btAt, toHistory, length, List.get_eq_getElem, Fin.val_cast, Fin.val_last]
      rw [List.getElem_cons_succ, List.getElem_append_right (by simp)]
      simp
    case cast j =>
      have hcast : Match.rewind (bt := BuildTree.loc nbas someLT next) (Match.loc tail)
          j.castSucc = Match.loc (tail.rewind j) := by
        rw [rewind]; exact Fin.lastCases_castSucc ..
      rw [hcast]
      simp only [btAt, toHistory, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc]
      rw [IH j]
      simp only [List.get_eq_getElem, Fin.val_cast]
      rcases j with ⟨jv, jv_lt⟩
      simp only [length] at jv_lt
      rcases jv with _ | i
      · simp
      · rw [List.getElem_cons_succ, List.getElem_cons_succ,
          List.getElem_append_left (by simp; omega)]
  case pdl H X bas someR next Y r tail IH =>
    cases k using Fin.lastCases
    case last =>
      have hlast : Match.rewind (bt := BuildTree.pdl bas someR next) (Match.pdl tail)
          (Fin.last _) = Match.nil := by
        rw [rewind]; exact Fin.lastCases_last
      rw [hlast]
      simp only [btAt, toHistory, length, List.get_eq_getElem, Fin.val_cast, Fin.val_last]
      rw [List.getElem_cons_succ, List.getElem_append_right (by simp)]
      simp
    case cast j =>
      have hcast : Match.rewind (bt := BuildTree.pdl bas someR next) (Match.pdl tail)
          j.castSucc = Match.pdl (tail.rewind j) := by
        rw [rewind]; exact Fin.lastCases_castSucc ..
      rw [hcast]
      simp only [btAt, toHistory, List.get_eq_getElem, Fin.val_cast, Fin.val_castSucc]
      rw [IH j]
      simp only [List.get_eq_getElem, Fin.val_cast]
      rcases j with ⟨jv, jv_lt⟩
      simp only [length] at jv_lt
      rcases jv with _ | i
      · simp
      · rw [List.getElem_cons_succ, List.getElem_cons_succ,
          List.getElem_append_left (by simp; omega)]

/-- The repeat ♥ companion relation on `Match`. -/
def Match.companion {X} {bt : BuildTree [] X} (m n : Match bt) : Prop :=
  ∃ (h : m.isFreeRepeat), n = Match.companionOf m h

local notation ma:arg " ♥ " mb:arg => Match.companion ma mb

/-- The sequent at the companion is `setEqTo` the sequent at the repeat.
Analogous to `nodeAt_companionOf_setEq`. -/
lemma Match.companionOf_setEqTo_sequent (m : Match bt) h :
    (m.companionOf h).btAt.2.1.setEqTo m.btAt.2.1 := by
  unfold companionOf
  split
  next k k_lt same_and_free _ =>
    have hist_eq : m.toHistory = m.btAt.1 := by
      simpa using m.toHistory_append_eq_btAt_fst
    dsimp only
    rw [Match.btAt_rewind_eq_toHistory_get]
    simp only [List.get_eq_getElem, Fin.val_cast, List.getElem_cons_succ, hist_eq]
    exact same_and_free.1

/-- Going to the companion of a free repeat gives a strictly shorter `Match`. -/
lemma Match.companionOf_length_lt {X} {bt : BuildTree [] X} (m : Match bt) (h : m.isFreeRepeat) :
    (m.companionOf h).length < m.length := by
  unfold companionOf
  split
  next k k_lt same_and_free _ =>
    apply m.rewind_length_lt_length_of_pos
    simp [Fin.lt_def]

/-! ## Collecting Sequents for Pre-states

As possible worlds for the model graph we want to define *maximal* paths inside the build tree
that do not contain (M), (L+) or (L-) steps.

We collect the sequents along such paths directly by induction on the `BuildTree`. -/

/-- Collect pre-states in the whole BuildTree.
The local pre-states come from paths in a local tableau,
and PDL pre-states each consist of just a single node. -/
def BuildTree.collect {H X} : (bt : BuildTree H X) → List (List Sequent)
  | .loc _ _ next =>
      (OpenLocalTableau.all X).flatMap fun lt => lt.1.pathsTo (next lt).4 ++ (next lt).6.collect
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
    have := LocalTableau.pathsTo_ne_nil (lt := lt.1) (Y := (next lt).4) BuildChoice.frth_mem
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
    rcases List.exists_mem_of_ne_nil _
      (LocalTableau.pathsTo_ne_nil (lt := lt.1) (Y := (next lt).4) BuildChoice.frth_mem)
      with ⟨π, π_in⟩
    rw [LocalTableau.mem_pathsTo] at π_in
    refine ⟨π, ⟨lt, lt.all_spec, .inl π_in⟩, ?_⟩
    have := @LocalTableau.pathsHead_eq_self X lt.1 π
    grind
  case freeRepeat h =>
    exact FreeRepeat_nil_impossible h

/-- Any `BuildTree` that is not a free repeat collects at least one list containing its root.
Generalisation of `BuildTree.collect_contains_root` to non-empty histories. -/
lemma BuildTree.collect_contains_root_of_not_freeRepeat {H X} (bt : BuildTree H X)
    (h : ¬ bt.isFreeRepeat) : ∃ π ∈ bt.collect, X ∈ π := by
  cases bt <;> simp [collect]
  case loc nbas someLT next =>
    rcases List.exists_mem_of_ne_nil _ someLT with ⟨lt, lt_in⟩
    rcases List.exists_mem_of_ne_nil _
      (LocalTableau.pathsTo_ne_nil (lt := lt.1) (Y := (next lt).4) BuildChoice.frth_mem)
      with ⟨π, π_in⟩
    rw [LocalTableau.mem_pathsTo] at π_in
    refine ⟨π, ⟨lt, lt.all_spec, .inl π_in⟩, ?_⟩
    have := @LocalTableau.pathsHead_eq_self X lt.1 π
    grind
  case freeRepeat fr =>
    simp [isFreeRepeat] at h

/-! ## Pre-states (Def 6.13) -/

/-- A pre-state is a list of sequents collected from a `BuildTree`. -/
def PreState {H X} (bt : BuildTree H X) : Type := Subtype (· ∈ bt.collect)

lemma PreState.nonempty {H X} {bt : BuildTree H X} {π : PreState bt} : π.val ≠ [] := by
  rcases π with ⟨L, L_in⟩
  unfold BuildTree.collect at L_in
  simp_all
  cases bt
  case loc nbas someLT next L_in' =>
    simp_all
    rcases L_in with ⟨lt, lt_in, L_in⟩
    rcases L_in with L_in|L_in
    · exact LocalTableau.paths_mem_nonempty lt.1 L L_in.1
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

/-! ## Collecting Formulas in Pre-state Sequents -/

/-- Λ(π) gets all formulas for a pre-state but keep the information what is loaded.
Returns the `WhateverFormula` type so that lemmas like 6.15 and 6.18 are sayable. -/
def PreState.wForms {H X} {bt : BuildTree H X} (π : PreState bt) : Finset WhateverFormula :=
  (π.val.map Sequent.wForms).flatten.toFinset

/-- Λ⁻(π) gets all formulas from a pre-state π, via unloading if needed. -/
def PreState.forms {H X} {bt : BuildTree H X} (π : PreState bt) : Finset Formula :=
  (π.val.map Sequent.bothSides).flatten.toFinset

/-- Characterizing three different ways in which a formula can be in `PreState.forms`. -/
lemma PreState.mem_forms_iff {H X} {bt : BuildTree H X} {φ : Formula} {π : PreState bt} :
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

lemma BuildTree.exists_mem_attach_forms_eq {bt : BuildTree [] H} {ρ : PreState bt} :
    ∃ a ∈ bt.collect.attach, PreState.forms a = ρ.forms := by
  simp

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
    · exact LocalTableau.paths_saturated _ π_in_lt.1
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

lemma PreState.forms_locallyConsistent {H X} {bt : BuildTree H X} {π : PreState bt} :
    locallyConsistent π.forms := by
  rcases π with ⟨π, π_in⟩
  cases bt <;> simp [BuildTree.collect] at π_in <;> rename_i π_in_old
  case loc nbas next =>
    rcases π_in with ⟨lt, lt_in, π_in_lt|π_in_next⟩
    · exact LocalTableau.paths_locallyConsistent _ π_in_lt.1
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
    · exact LocalTableau.paths_last_basic _ π_in_lt.1
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

/-- The result of `BuildTree.collect` in any sub-`BuildTree` reached by a `Match`
is also part of `BuildTree.collect` applied to the bigger `BuildTree`. -/
lemma Match.collect_btAt_subset {H X} {bt : BuildTree H X} (m : Match bt) :
    ∀ π ∈ m.btAt.2.2.collect, π ∈ bt.collect := by
  induction m with
  | nil => intro π hπ; simpa [Match.btAt] using hπ
  | @loc H X nbas someLT next lt tail IH =>
    intro π hπ
    have hsub := IH π (by simpa [Match.btAt] using hπ)
    rw [BuildTree.collect]
    simp only [List.mem_flatMap, List.mem_append]
    exact ⟨lt, OpenLocalTableau.all_spec, Or.inr hsub⟩
  | @pdl H X bas someR next Y r tail IH =>
    intro π hπ
    have hsub := IH π (by simpa [Match.btAt] using hπ)
    rw [BuildTree.collect]
    simp only [List.singleton_append, List.mem_cons, List.mem_flatMap, Sigma.exists]
    exact Or.inr ⟨Y, r, PdlRule.all_spec bas r, hsub⟩

/-- For any `Match` there exists a `PreState`
containing a sequent `setEqTo` the end nof the Match. -/
lemma Match.existsPreState {X} {bt : BuildTree [] X} (m : Match bt) :
    ∃ π : PreState bt, ∃ Z ∈ π.1, m.btAt.2.1.setEqTo Z := by
  by_cases m_frep : m.isFreeRepeat
  · -- We do not make a PreState here but go to the companion first.
    have IH := (m.companionOf m_frep).existsPreState
    rcases IH with ⟨π, Z, Z_in_π, same_Z⟩
    refine ⟨π, Z, Z_in_π, ?_⟩
    -- Using lemma that the companion has a `setEqTo` sequent.
    have comp_eq := m.companionOf_setEqTo_sequent m_frep
    exact Sequent.setEqTo_trans _ _ _ ((Sequent.setEqTo_symm _ _).mp comp_eq) same_Z
  · -- The `BuildTree` we are at is not a free repeat, so it collects its own root.
    have not_frep : ¬ m.btAt.2.2.isFreeRepeat := fun h => m_frep (Match.isFreeRepeat_iff.mpr h)
    rcases m.btAt.2.2.collect_contains_root_of_not_freeRepeat not_frep with ⟨π, π_in, root_in⟩
    exact ⟨⟨π, m.collect_btAt_subset π π_in⟩, m.btAt.2.1, root_in, Sequent.setEqTo_refl _⟩
termination_by
  m.length
decreasing_by
  exact m.companionOf_length_lt m_frep

/-- The Boolean predicate used by `Match.toPreState`: does the given list of sequents
contain a sequent that is `setEqTo` the end of the given `Match`? -/
def Match.fitsPreState {X} {bt : BuildTree [] X} (m : Match bt) (π : List Sequent) : Bool :=
  π.any (fun Z => decide (m.btAt.2.1.setEqTo Z))

lemma Match.fitsPreState_iff {X} {bt : BuildTree [] X} {m : Match bt} {π : List Sequent} :
    m.fitsPreState π ↔ ∃ Z ∈ π, m.btAt.2.1.setEqTo Z := by
  simp [Match.fitsPreState]

/-- Reformulation of `Match.existsPreState` using `Match.fitsPreState`. -/
lemma Match.exists_fitsPreState {X} {bt : BuildTree [] X} (m : Match bt) :
    ∃ π ∈ bt.collect, m.fitsPreState π := by
  rcases m.existsPreState with ⟨⟨π, π_in⟩, Z, Z_in, hZ⟩
  exact ⟨π, π_in, Match.fitsPreState_iff.mpr ⟨Z, Z_in, hZ⟩⟩

/-- Thanks to `Match.existsPreState` the search for a fitting pre-state succeeds. -/
lemma Match.find?_fitsPreState_isSome {X} {bt : BuildTree [] X} (m : Match bt) :
    (bt.collect.find? m.fitsPreState).isSome := by
  cases h : bt.collect.find? m.fitsPreState
  case some => simp
  case none =>
    rcases m.exists_fitsPreState with ⟨π, π_in, hπ⟩
    exact absurd hπ (List.find?_eq_none.mp h π π_in)

/-- Pick a `PreState` for a given `Match`, using `Match.existsPreState` and `List.find?`. -/
def Match.toPreState {X} {bt : BuildTree [] X} (m : Match bt) : PreState bt :=
  ⟨(bt.collect.find? m.fitsPreState).get m.find?_fitsPreState_isSome,
    List.mem_of_find?_eq_some (Option.some_get _).symm⟩

/-- The result of `Match.toPreState` indeed contains a sequent `setEqTo` the end of the `Match`. -/
lemma Match.toPreState_spec {X} {bt : BuildTree [] X} (m : Match bt) :
    ∃ Z ∈ m.toPreState.1, m.btAt.2.1.setEqTo Z :=
  Match.fitsPreState_iff.mp (List.find?_some (Option.some_get m.find?_fitsPreState_isSome).symm)

/-- Search for the node in `bt` at which the list `p` of sequents is collected, and return the
`Match` leading to that node. Auxiliary function for `PreState.toMatch`, defined for all lists
`p` of sequents. If `p` is not collected anywhere, then we return `Match.nil` as a dummy value. -/
def BuildTree.toMatchAux : {H : History} → {X : Sequent} → (bt : BuildTree H X) →
    (p : List Sequent) → Match bt
  | _, X, .loc _ _ next, p =>
      -- If `p` is collected below one of the local tableaux, then go there, else stay here.
      match (OpenLocalTableau.all X).find? (fun lt => decide (p ∈ (next lt).6.collect)) with
      | some lt => .loc (BuildTree.toMatchAux (next lt).6 p)
      | none => .nil
  | _, X, .pdl _ _ next, p =>
      -- If `p` is collected below one of the PDL rules, then go there, else stay here.
      match (PdlRule.all X).find? (fun Yr => decide (p ∈ (next Yr.1 Yr.2).collect)) with
      | some ⟨Y, r⟩ => .pdl (BuildTree.toMatchAux (next Y r) p)
      | none => .nil
  | _, _, .freeRepeat _, _ => .nil
  | _, _, .openLeaf _ _, _ => .nil
termination_by _ _ bt _ => bt.size
decreasing_by
  · apply BuildTree.size_lt_loc
  · apply BuildTree.size_lt_pdl

/-- A collected list of sequents is still collected in the sub-`BuildTree` found for it. -/
lemma BuildTree.toMatchAux_mem_collect : {H : History} → {X : Sequent} → (bt : BuildTree H X) →
    (p : List Sequent) → p ∈ bt.collect → p ∈ (bt.toMatchAux p).btAt.2.2.collect
  | _, X, .loc nbas someLT next, p, hp => by
      rw [BuildTree.toMatchAux]
      cases h : (OpenLocalTableau.all X).find? (fun lt => decide (p ∈ (next lt).6.collect))
      case some lt =>
        have p_in := List.find?_some h
        simp only [decide_eq_true_eq] at p_in
        simpa [Match.btAt] using BuildTree.toMatchAux_mem_collect (next lt).6 p p_in
      case none => simpa [Match.btAt] using hp
  | _, X, .pdl bas someR next, p, hp => by
      rw [BuildTree.toMatchAux]
      cases h : (PdlRule.all X).find? (fun Yr => decide (p ∈ (next Yr.1 Yr.2).collect))
      case some Yr =>
        have p_in := List.find?_some h
        simp only [decide_eq_true_eq] at p_in
        rcases Yr with ⟨Y, r⟩
        simpa [Match.btAt] using BuildTree.toMatchAux_mem_collect (next Y r) p p_in
      case none => simpa [Match.btAt] using hp
  | _, _, .freeRepeat _, p, hp => by simpa [Match.btAt, BuildTree.toMatchAux] using hp
  | _, _, .openLeaf _ _, p, hp => by simpa [Match.btAt, BuildTree.toMatchAux] using hp
termination_by _ _ bt _ _ => bt.size
decreasing_by
  · apply BuildTree.size_lt_loc
  · apply BuildTree.size_lt_pdl

/-- A collected list of sequents starts with the sequent of the node where it is collected. -/
lemma BuildTree.toMatchAux_head? : {H : History} → {X : Sequent} → (bt : BuildTree H X) →
    (p : List Sequent) → p ∈ bt.collect → p.head? = some (bt.toMatchAux p).btAt.2.1
  | _, X, .loc nbas someLT next, p, hp => by
      rw [BuildTree.toMatchAux]
      cases h : (OpenLocalTableau.all X).find? (fun lt => decide (p ∈ (next lt).6.collect))
      case some lt =>
        have p_in := List.find?_some h
        simp only [decide_eq_true_eq] at p_in
        simpa [Match.btAt] using BuildTree.toMatchAux_head? (next lt).6 p p_in
      case none =>
        -- Not collected below, hence `p` must be a path in one of the local tableaux here.
        have hnone := List.find?_eq_none.mp h
        simp only [decide_eq_true_eq] at hnone
        rw [BuildTree.collect] at hp
        simp only [List.mem_flatMap, List.mem_append] at hp
        rcases hp with ⟨lt, lt_in, hp | hp⟩
        · rw [List.head?_eq_some_head (LocalTableau.paths_mem_nonempty lt.1 p
              (LocalTableau.mem_pathsTo.mp hp).1),
            LocalTableau.pathsHead_eq_self (LocalTableau.mem_pathsTo.mp hp).1]
          simp [Match.btAt]
        · exact absurd hp (hnone lt lt_in)
  | _, X, .pdl bas someR next, p, hp => by
      rw [BuildTree.toMatchAux]
      cases h : (PdlRule.all X).find? (fun Yr => decide (p ∈ (next Yr.1 Yr.2).collect))
      case some Yr =>
        have p_in := List.find?_some h
        simp only [decide_eq_true_eq] at p_in
        rcases Yr with ⟨Y, r⟩
        simpa [Match.btAt] using BuildTree.toMatchAux_head? (next Y r) p p_in
      case none =>
        -- Not collected below, hence `p` must be the singleton list `[X]` collected here.
        have hnone := List.find?_eq_none.mp h
        simp only [decide_eq_true_eq] at hnone
        rw [BuildTree.collect] at hp
        simp only [List.singleton_append, List.mem_cons, List.mem_flatMap] at hp
        rcases hp with rfl | ⟨Yr, Yr_in, hp⟩
        · simp [Match.btAt]
        · exact absurd hp (hnone Yr Yr_in)
  | _, _, .freeRepeat _, p, hp => by
      rw [BuildTree.collect] at hp; simp at hp
  | _, _, .openLeaf _ _, p, hp => by
      rw [BuildTree.collect] at hp
      simp only [List.mem_singleton] at hp
      subst hp
      simp [Match.btAt, BuildTree.toMatchAux]
termination_by _ _ bt _ _ => bt.size
decreasing_by
  · apply BuildTree.size_lt_loc
  · apply BuildTree.size_lt_pdl

/-- Every pre-state comes from a `Match`: this is the `Match` that leads to the node of the
`BuildTree` at which the pre-state `π` was collected.
(Defined for any history, not only for `H = []`.) -/
def PreState.toMatch {H X} {bt : BuildTree H X} (π : PreState bt) : Match bt :=
  bt.toMatchAux π.val

/-- Specification of `PreState.toMatch`, part one:
the pre-state is collected already in the sub-`BuildTree` reached by the match. -/
lemma PreState.toMatch_mem_collect {H X} {bt : BuildTree H X} (π : PreState bt) :
    π.val ∈ π.toMatch.btAt.2.2.collect :=
  bt.toMatchAux_mem_collect π.val π.prop

/-- Specification of `PreState.toMatch`, part two:
the pre-state starts with the sequent at the node reached by the match. -/
lemma PreState.toMatch_head {H X} {bt : BuildTree H X} (π : PreState bt) :
    π.val.head PreState.nonempty = π.toMatch.btAt.2.1 := by
  have := bt.toMatchAux_head? π.val π.prop
  rw [List.head?_eq_some_head PreState.nonempty] at this
  exact Option.some.inj this

/-- Specification of `PreState.toMatch`, part three: the sequent at the node reached by the
match is the head of the pre-state. (Reformulation of `PreState.toMatch_head`.) -/
lemma PreState.toMatch_endSeq {H X} {bt : BuildTree H X} (π : PreState bt) :
    π.toMatch.endSeq = π.val.head PreState.nonempty :=
  (π.toMatch_head).symm

/-- Not only the *first* sequent of a pre-state is reached by a `Match` (this is
`PreState.toMatch`), also the *last* sequent of a pre-state is reached by some `Match`. -/
lemma PreState.exists_match_endSeq_eq_last {H X} {bt : BuildTree H X} (π : PreState bt) :
    ∃ m : Match bt, m.endSeq = π.val.getLast PreState.nonempty := by
  rcases π with ⟨p, p_in⟩
  cases bt <;> simp [BuildTree.collect] at p_in <;> rename_i p_in_old
  case loc nbas someLT next =>
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · refine ⟨Match.loc (lt := lt) Match.nil, ?_⟩
      have hne : p ≠ [] := PreState.nonempty (π := ⟨p, p_in_old⟩)
      have := p_in_lt.2
      rw [List.getLast?_eq_some_getLast (l := p) (h := hne)] at this
      simp only [Match.endSeq, Match.btAt]
      exact (Option.some.inj this).symm
    · rcases @PreState.exists_match_endSeq_eq_last _ _ (next lt).6 ⟨p, p_in_next⟩ with ⟨m, hm⟩
      exact ⟨Match.loc m, hm⟩
  case pdl bas someR next =>
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def; exact ⟨Match.nil, by simp [Match.endSeq, Match.btAt]⟩
    · rcases @PreState.exists_match_endSeq_eq_last _ _ (next Y r) ⟨p, p_in_next⟩ with ⟨m, hm⟩
      exact ⟨Match.pdl m, hm⟩
  case openLeaf bas noRule =>
    subst p_in
    exact ⟨Match.nil, by simp [Match.endSeq, Match.btAt]⟩
termination_by bt.size
decreasing_by
  · subst_eqs; apply @BuildTree.size_lt_loc H X
  · subst_eqs; apply @BuildTree.size_lt_pdl H X

/-- Both ends of a pre-state are reached by matches, and the match reaching the last sequent
extends the one reaching the first sequent: the continuation `c` is a `Match` inside the
sub-`BuildTree` at which `π` was collected, and appending it to `π.toMatch` gives a `Match` in
the whole tree that ends at the last sequent of `π`. -/
lemma PreState.exists_endMatch {H X} {bt : BuildTree H X} (π : PreState bt) :
    ∃ c : Match π.toMatch.btAt.2.2,
        π.toMatch.endSeq = π.val.head PreState.nonempty
      ∧ (π.toMatch.append c).endSeq = π.val.getLast PreState.nonempty := by
  obtain ⟨c, hc⟩ := PreState.exists_match_endSeq_eq_last
    (bt := π.toMatch.btAt.2.2) ⟨π.val, π.toMatch_mem_collect⟩
  exact ⟨c, π.toMatch_endSeq, by rw [Match.endSeq_append]; exact hc⟩

/-- Weak round-trip that always holds: going from a pre-state to a match and back gives a
pre-state that contains a sequent set-equal to the first sequent of `π`. -/
lemma PreState.setEqTo_mem_toMatch_toPreState {X} {bt : BuildTree [] X} (π : PreState bt) :
    ∃ Z ∈ π.toMatch.toPreState.val, (π.val.head PreState.nonempty).setEqTo Z := by
  rw [π.toMatch_head]
  exact Match.toPreState_spec π.toMatch

/-- Round-trip: under the assumption that `π` is the only collected list that contains a
sequent set-equal to the sequent at the node where `π` is collected, going to the match
and back gives `π` again. -/
lemma PreState.toMatch_toPreState {X} {bt : BuildTree [] X} (π : PreState bt)
    (uniq : ∀ ρ ∈ bt.collect,
      (∃ Z ∈ ρ, (π.val.head PreState.nonempty).setEqTo Z) → ρ = π.val) :
    π.toMatch.toPreState = π := by
  apply Subtype.ext
  refine uniq _ π.toMatch.toPreState.prop ?_
  rw [π.toMatch_head]
  exact Match.toPreState_spec π.toMatch

/-- Example where the `uniq` assumption of `PreState.toMatch_toPreState` is satisfied:
an open leaf collects only one pre-state, so there the round-trip does hold. -/
lemma PreState.toMatch_toPreState_openLeaf {X} (bas : X.basic) (noRule : PdlRule.all X = [])
    (π : PreState (BuildTree.openLeaf (H := []) bas noRule)) :
    π.toMatch.toPreState = π := by
  apply π.toMatch_toPreState
  intro ρ ρ_in _
  have π_in := π.prop
  simp only [BuildTree.collect, List.mem_singleton] at ρ_in π_in
  rw [ρ_in, π_in]

/-! ## Properties of Formula (Sets? Lists?) obtained from Pre-States -/

-- IDEA: rephrase these to be about the resulting chain, not about getForms !!

/-- Every *basic* formula of a pre-state already occurs in the last (basic) sequent of that
pre-state. Note that `bothSides` is used here, so this also covers formulas from the loaded
part of a sequent. -/
lemma PreState.mem_bothSides_getLast_of_basic {H X} {bt : BuildTree H X} {π : PreState bt}
    {φ : Formula} (φ_basic : φ.basic) (φ_in : φ ∈ π.forms) :
    φ ∈ (π.val.getLast PreState.nonempty).bothSides := by
  rcases π with ⟨p, p_in⟩
  simp only [PreState.forms, List.mem_toFinset] at φ_in
  cases bt <;> simp [BuildTree.collect] at p_in <;> rename_i p_in_old
  case loc nbas someLT next =>
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · exact LocalTableau.paths_basic_mem_last p_in_lt.1 φ φ_basic φ_in
    · exact @PreState.mem_bothSides_getLast_of_basic _ _ (next lt).6 ⟨p, p_in_next⟩ φ
        φ_basic (by simpa [PreState.forms] using φ_in)
  case pdl bas someR next =>
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def
      simpa using φ_in
    · exact @PreState.mem_bothSides_getLast_of_basic _ _ (next Y r) ⟨p, p_in_next⟩ φ
        φ_basic (by simpa [PreState.forms] using φ_in)
  case openLeaf bas noRule =>
    subst p_in
    simpa using φ_in
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

/-- Lemma 6.14, weakened version. The original statement says that `φ` is principal in a rule
applied later on. We do not have the rule applications available along a pre-state, so instead
we make the case distinction on whether `φ` is basic, and give the actual content for the
first case: any basic formula of a pre-state occurs already in its last sequent.
(We also use `Sequent.bothSides` instead of `∈` to include the loaded formula.) -/
lemma PreState.formsCases {π : PreState bt} (φ_in : φ ∈ π.forms) :
      (φ.basic ∧ φ ∈ (π.val.getLast PreState.nonempty).bothSides)
    ∨ ¬ φ.basic := by
  by_cases φ_basic : φ.basic
  · exact Or.inl ⟨φ_basic, PreState.mem_bothSides_getLast_of_basic φ_basic φ_in⟩
  · exact Or.inr φ_basic

/-! ### Lemma 6.15 *free* case.

The helper lemmas needed for it are in `Pdl/Sequent.lean`, `Pdl/LocalRules.lean` and
`Pdl/LocalTableauPaths.lean`. -/

/-- Lemma 6.15 *free* case.
(Generalised from `bt : BuildTree [] X` to an arbitrary history `H`, as needed for the
recursion into sub-`BuildTree`s.) -/
lemma PreState.freeUnfoldDiaMem_of_nonAtom {H X} {bt : BuildTree H X} {π : PreState bt} {α φ} :
    ¬ α.isAtomic → (~⌈α⌉φ : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1 ∪ [~ Formula.boxes Xδ.2 φ]).all (· ∈ π.wForms) := by
  intro α_notAtom in_forms
  rcases π with ⟨p, p_in⟩
  simp only [PreState.wForms, List.mem_toFinset] at in_forms ⊢
  cases bt <;> simp [BuildTree.collect] at p_in
  case loc nbas someLT next =>
    -- If π comes from a path in one of the local tableaux here, then the unfold rule was used
    -- somewhere along that path, otherwise we recurse into the chosen sub-`BuildTree`.
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · rcases LocalTableau.paths_freeUnfoldDia (lt := lt.1) α_notAtom p p_in_lt.1 in_forms
        with ⟨Fδ, Fδ_in, hall⟩
      rcases Fδ with ⟨F, δ⟩
      exact ⟨⟨F, δ⟩, Fδ_in, by simpa [Yset] using hall⟩
    · have IH := @PreState.freeUnfoldDiaMem_of_nonAtom _ _ (next lt).6 ⟨p, p_in_next⟩ α φ α_notAtom
      simp only [PreState.wForms, List.mem_toFinset] at IH
      exact IH in_forms
  case pdl bas someR next =>
    -- A pre-state coming from a `.pdl` step is basic, so α would have to be atomic.
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at in_forms
      exact absurd (Sequent.isAtomic_of_basic_of_negBox_mem_wForms bas in_forms) α_notAtom
    · have IH := @PreState.freeUnfoldDiaMem_of_nonAtom _ _ (next Y r) ⟨p, p_in_next⟩ α φ α_notAtom
      simp only [PreState.wForms, List.mem_toFinset] at IH
      exact IH in_forms
  case openLeaf bas noRule =>
    -- Also an open leaf is basic, so again α would have to be atomic.
    subst p_in
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at in_forms
    exact absurd (Sequent.isAtomic_of_basic_of_negBox_mem_wForms bas in_forms) α_notAtom
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

/-! ### Lemma 6.15 *loaded* cases.

The helper lemmas needed for these are in `Pdl/Sequent.lean`, `Pdl/LocalRules.lean` and
`Pdl/LocalTableauPaths.lean`. -/

/-- Generic version of the *loaded* case of Lemma 6.15: a non-atomic loaded diamond in a
pre-state must have been unfolded by a `LoadRule` somewhere in the pre-state.
The two versions below are the special cases for `AnyFormula.loaded` and `AnyFormula.normal`.
(Generalised from `bt : BuildTree [] X` to an arbitrary history `H`, as needed for the
recursion into sub-`BuildTree`s.) -/
lemma PreState.loadUnfoldMem_of_nonAtom {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    {ξ : AnyFormula} :
    ¬ α.isAtomic → (.negLoad (~'⌊α⌋ξ) : WhateverFormula) ∈ π.wForms →
      ∃ ress, Nonempty (LoadRule (~'⌊α⌋ξ) ress) ∧ ∃ Fo ∈ ress,
        Fo.1.all (fun f => (f : WhateverFormula) ∈ π.wForms)
        ∧ Fo.2.toList.all (fun nl => (WhateverFormula.negLoad nl) ∈ π.wForms) := by
  intro α_notAtom in_forms
  rcases π with ⟨p, p_in⟩
  simp only [PreState.wForms, List.mem_toFinset] at in_forms ⊢
  cases bt <;> simp [BuildTree.collect] at p_in
  case loc nbas someLT next =>
    -- If π comes from a path in one of the local tableaux here, then the load rule was used
    -- somewhere along that path, otherwise we recurse into the chosen sub-`BuildTree`.
    rcases p_in with ⟨lt, lt_in, p_in_lt | p_in_next⟩
    · exact LocalTableau.paths_loadUnfoldDia (lt := lt.1) α_notAtom p p_in_lt.1 in_forms
    · have IH := @PreState.loadUnfoldMem_of_nonAtom _ _ (next lt).6 ⟨p, p_in_next⟩ α ξ α_notAtom
      simp only [PreState.wForms, List.mem_toFinset] at IH
      exact IH in_forms
  case pdl bas someR next =>
    -- A pre-state coming from a `.pdl` step is basic, so α would have to be atomic.
    rcases p_in with p_def | ⟨Y, r, in_rule, p_in_next⟩
    · subst p_def
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at in_forms
      exact absurd (Sequent.isAtomic_of_basic_of_negLoad_mem_wForms bas in_forms) α_notAtom
    · have IH := @PreState.loadUnfoldMem_of_nonAtom _ _ (next Y r) ⟨p, p_in_next⟩ α ξ α_notAtom
      simp only [PreState.wForms, List.mem_toFinset] at IH
      exact IH in_forms
  case openLeaf bas noRule =>
    -- Also an open leaf is basic, so again α would have to be atomic.
    subst p_in
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at in_forms
    exact absurd (Sequent.isAtomic_of_basic_of_negLoad_mem_wForms bas in_forms) α_notAtom
termination_by
  bt.size
decreasing_by
  · subst_eqs
    apply @BuildTree.size_lt_loc H X
  · subst_eqs
    apply @BuildTree.size_lt_pdl H X

/-- Lemma 6.15 *loaded* case with _more than one_ loaded box -/
lemma PreState.loadUnfoldDiaMem_of_nonAtom {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    (χ : LoadFormula) :
    ¬ α.isAtomic → (.negLoad (~'⌊α⌋χ) : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1).all (· ∈ π.wForms)
                    ∧ (YsetLoad Xδ χ).2.toList.all (· ∈ π.wForms) := by
  intro α_notAtom in_forms
  rcases PreState.loadUnfoldMem_of_nonAtom α_notAtom in_forms with ⟨ress, ⟨lr⟩, Fo, Fo_in, h1, h2⟩
  rw [lr.eq_unfoldDiamondLoaded] at Fo_in
  simp only [unfoldDiamondLoaded, List.mem_map] at Fo_in
  rcases Fo_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
  exact ⟨⟨F, δ⟩, Fδ_in, h1, h2⟩

/-- Lemma 6.15 *loaded* case with only _one_ loaded box. -/
lemma PreState.loadUnfoldDiaMem_of_nonAtom' {H X} {bt : BuildTree H X} {π : PreState bt} {α}
    {φ : Formula} :
    ¬ α.isAtomic → (.negLoad (~'⌊α⌋φ) : WhateverFormula) ∈ π.wForms →
      ∃ Xδ ∈ Dset α, (Xδ.1).all (· ∈ π.wForms)
                    ∧ (YsetLoad' Xδ φ).2.toList.all (· ∈ π.wForms) := by
  intro α_notAtom in_forms
  rcases PreState.loadUnfoldMem_of_nonAtom α_notAtom in_forms with ⟨ress, ⟨lr⟩, Fo, Fo_in, h1, h2⟩
  rw [lr.eq_unfoldDiamondLoaded'] at Fo_in
  simp only [unfoldDiamondLoaded', List.mem_map] at Fo_in
  rcases Fo_in with ⟨⟨F, δ⟩, Fδ_in, rfl⟩
  refine ⟨⟨F, δ⟩, Fδ_in, ?_, h2⟩
  simp only [List.all_eq_true, decide_eq_true_eq] at h1 ⊢
  intro f f_in
  apply h1
  rcases hδ : splitLast δ with _ | ⟨δ', β⟩ <;> simp [YsetLoad', hδ] <;> tauto

/-- Lemma 6.16: pre-states are saturated and locally consistent, their last node is basic. -/
lemma PreState.locConsSatBas {X} {bt : BuildTree [] X} (π : PreState bt) :
    saturated π.forms
    ∧ locallyConsistent π.forms
    ∧ (π.val.getLast PreState.nonempty).basic :=
  ⟨π.forms_saturated, π.forms_locallyConsistent, π.forms_last_basic⟩
