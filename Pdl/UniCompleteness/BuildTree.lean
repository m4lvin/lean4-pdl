import Pdl.UniCompleteness.UniTableauGame
import Pdl.Completeness.BuildTree

/-! # Uniform BuildTree -/

namespace UniGame

/-- Given a winning Builder strategy *IN THE UNIFORM GAME*, compute its `BuildTree`.
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
        have has_ends : endNodesOf (uniLocalTab X) ≠ ∅ := by
          intro lt_no_ends
          have := stillWin ⟨H, ⟨X, Sum.inr (.ltab nrep nbas (uniLocalTab X))⟩⟩ Move.prLocTab
          have has_moves := winning_has_moves (by simp) this
          simp only [tableauGame, Game.moves, theMoves, Finset.image_nonempty] at has_moves
          simp_all
        -- We show that the uniform lt must have end nodes because prover could use it to win.
        exact @List.ne_nil_of_mem (OpenLocalTableau X) ⟨uniLocalTab X, has_ends⟩
          (OpenLocalTableau.all X) OpenLocalTableau.all_spec
      .loc nbas someLT <| fun ltX => by
        have ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (.ltab nrep nbas ltX.1)⟩⟩).Nonempty :=
          winning_has_moves (by simp) <|
            stillWin ⟨H, ⟨X, Sum.inr (.ltab nrep nbas ltX.1)⟩⟩ sorry -- Move.prLocTab
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
            simp only [tableauGame, Game.Pos.moves, ne_eq, theMoves, Finset.mem_image] at mY_prop
            let oY := List.find? -- No more choice thanks to this! NEW: via `seqSort` now!?
              (fun Y => @decide (⟨_, ⟨_, posOf (X :: H) Y⟩⟩ = mY) (instDecidableEqPos _ _))
              (endNodesOf ltX.1).seqSort
            cases oY_def : oY
            · exfalso
              have hnone := List.find?_eq_none.mp oY_def
              obtain ⟨a, a_in, ha⟩ := mY_prop
              have := hnone a ((Finset.mem_seqSort _).mpr a_in)
              simp only [decide_eq_true_eq] at this
              exact this ha
            case some Y =>
              unfold oY at oY_def
              have def_mY := List.find?_some oY_def
              simp only [decide_eq_true_eq] at def_mY
              have Y_in := (Finset.mem_seqSort _).mp (List.mem_of_find?_eq_some oY_def)
              rw [← def_mY]
              exact @Move.buEnd X ltX.1 Y H nrep nbas Y_in
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
                · sorry -- rw [p_def]; exact Relation.TransGen.single ⟨Move.prLocTab⟩
            refine H'_def ▸ @buildTree s H' Y myP ?_
            -- (Remaining goal is nicer after doing `H'_def ▸` on the outside and not on `myP`.)
            rw [mY_def]
            -- Note that *two* moves have happened now, one by prover and one by Builder using `s`.
            -- Remains to show that `s` still wins.
            apply winning_of_winning_move
            sorry -- exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX.1)⟩ Move.prLocTab
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
                sorry -- exact stillWin ⟨_, X, Sum.inr (BuilderPos.ltab nrep nbas ltX.1)⟩ Move.prLocTab
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

/-- The sequent at the companion is the same as the sequent at the repeat.
Analogous to `nodeAt_companionOf_setEq`. FIXME outdated comment -/
lemma Match.companionOf_setEqTo_sequent (m : Match bt) h :
    (m.companionOf h).btAt.2.1 = m.btAt.2.1 := by
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

end UniGame
