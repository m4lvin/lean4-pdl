import Pdl.TableauGame

/-! # From winning strategies to model graphs (Section 6.3) -/

/-- List of all `PdlRule`s applicable to `X`. Code is based on part of `theMoves`
This is also similar to the definitions in `LocalAll.lean`. -/
def PdlRule.all (X : Sequent) : List (Σ Y, PdlRule X Y) :=
  match X with
  | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
        (L.attach.map (fun -- Catch a negation and all boxes (≥ 1) after it to be loaded.
                    | ⟨~φ, in_L⟩ => match bdef : boxesOf φ with
                        | (δ@δ_def:(_::_), ψ) =>
                          have notBox : ¬ ψ.isBox := by
                            have := @boxesOf_output_not_isBox φ; simp_all
                          have _in'' : (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast _⌉ψ) ∈ L := by
                            rw [def_of_boxesOf_def bdef] at in_L
                            convert in_L using 2
                            rw [← δ_def, ← @boxes_last, @List.dropLast_append_getLast]
                          [ ⟨ ( L.erase _, R
                              , some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by simp_all)⌋ψ))))
                            , .loadL _in'' notBox rfl ⟩ ]
                        | ([],_) => []
                    | _ => [] )).flatten
        ++
        (R.attach.map (fun
                    | ⟨~φ, in_R⟩ => match bdef : boxesOf φ with
                        | (δ@δ_def:(_::_), ψ) =>
                          have notBox : ¬ ψ.isBox := by
                            have := @boxesOf_output_not_isBox φ; simp_all
                          have _in'' : (~⌈⌈δ.dropLast⌉⌉⌈δ.getLast _⌉ψ) ∈ R := by
                            rw [def_of_boxesOf_def bdef] at in_R
                            convert in_R using 2
                            rw [← δ_def, ← @boxes_last, @List.dropLast_append_getLast]
                          [ ⟨ ( L, R.erase _
                              , some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by simp_all)⌋ψ))))
                            , .loadR _in'' notBox rfl ⟩ ]
                        | ([],_) => []
                    | _ => [] )).flatten
  | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
          ( match ξ_def : ξ with -- (M) rule, deterministic:
          | .normal φ => [ ⟨ ⟨ _, _, none                ⟩, .modL rfl rfl ⟩ ]
          | .loaded χ => [ ⟨ ⟨ _, _, some (Sum.inl (~'χ))⟩, .modL rfl rfl ⟩ ] )
          ++ -- (L-) rule, deterministic:
          [ match ξsp_def : ξ.split with
          | ⟨δs, φ⟩ => match sp_def : splitLast δs with
            | none =>
              ⟨ (L.insert (~(⌊·a⌋ξ).unload), R, none)
              , @PdlRule.freeL _ L R [] (·a) φ _
                  (by simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal])
                  (by simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal]) ⟩
            | some ⟨δs_, δ⟩ =>
              ⟨ (L.insert (~(⌊·a⌋ξ).unload), R, none)
              , by
                  have ξ_def : ξ = AnyFormula.loadBoxes (δs_ ++ [δ]) φ := by
                      rw [← splitLast_append_singleton] at sp_def
                      rw [splitLast_inj sp_def, ← loadMulti_split] at ξsp_def
                      have : (loadMulti δs_ δ φ).split = AnyFormula.split (loadMulti δs_ δ φ) := rfl
                      have := AnyFormula.split_inj (this ▸ ξsp_def)
                      exact this ▸ loadMulti_eq_loadBoxes
                  refine @PdlRule.freeL _ L R (·a :: δs_) δ φ _ ?_ ?_
                  · simp [ξ_def, box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
                  · simp only [Formula.boxes_cons, Prod.mk.injEq, and_true]
                    convert rfl
                    simp [ξ_def, AnyFormula.loadBoxes_unload_eq_boxes, boxes_last] ⟩
          ]
  | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
          ( match ξ_def : ξ with -- (M) rule, deterministic:
          | .normal φ => [ ⟨ ⟨ _, _, none                ⟩, .modR rfl rfl ⟩ ]
          | .loaded χ => [ ⟨ ⟨ _, _, some (Sum.inr (~'χ))⟩, .modR rfl rfl ⟩ ] )
          ++ -- (L-) rule, deterministic:
          [ match ξsp_def : ξ.split with
          | ⟨δs, φ⟩ => match sp_def : splitLast δs with
            | none =>
              ⟨ (L, R.insert (~(⌊·a⌋ξ).unload), none)
              , @PdlRule.freeR _ L R [] (·a) φ _
                  (by simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal])
                  (by simp_all [nil_of_splitLast_none, AnyFormula.split_eq_nil_is_normal]) ⟩
            | some ⟨δs_, δ⟩ =>
              ⟨ (L, R.insert (~(⌊·a⌋ξ).unload), none)
              , by
                  have ξ_def : ξ = AnyFormula.loadBoxes (δs_ ++ [δ]) φ := by
                      rw [← splitLast_append_singleton] at sp_def
                      rw [splitLast_inj sp_def, ← loadMulti_split] at ξsp_def
                      have : (loadMulti δs_ δ φ).split = AnyFormula.split (loadMulti δs_ δ φ) := rfl
                      have := AnyFormula.split_inj (this ▸ ξsp_def)
                      exact this ▸ loadMulti_eq_loadBoxes
                  refine @PdlRule.freeR _ L R (·a :: δs_) δ φ _ ?_ ?_
                  · simp [ξ_def, box_loadBoxes_append_eq_of_loaded_eq_loadBoxes]
                  · simp only [Formula.boxes_cons, Prod.mk.injEq, and_true, true_and]
                    convert rfl
                    simp [ξ_def, AnyFormula.loadBoxes_unload_eq_boxes, boxes_last] ⟩
          ]
  -- WORRY: also need to allow freeL/freeR from non-atomic loading? (to make _spec below provable)
  | _ => [] -- YOLO?

/-- NOTE: unfinished but also NOT USED at the moment / not needed at all?

Maybe it's enough to build the countermodelgraph from a buildTree that uses only the PdlRules in
`PdlRule.all` and we can ignore other (e.g. non-atomic unloading) PdlRule applications???
-/
lemma PdlRule.all_spec {X Y} (r : PdlRule X Y) : ⟨Y, r⟩ ∈ PdlRule.all X := by
  cases r
  case loadL L δs α φ R in_L notBox Y_def =>
    subst Y_def
    unfold all
    simp
    sorry
  case loadR R δs α φ L in_R notBox Y_def =>
    -- analogous
    sorry
  case freeL L R δs α φ X_def Y_def =>
    subst X_def Y_def
    cases δs <;> simp_all [all]
    · -- rw [Formula.boxes_nil] -- motive is not type correct
      sorry
    · sorry
  case freeR L R δs α φ X_def Y_def =>
    -- analogous
    sorry
  case modL L R a ξ X_def Y_def =>
    subst X_def Y_def
    cases ξ <;> simp_all [all]
  case modR L R a ξ X_def Y_def =>
    subst X_def Y_def
    cases ξ <;> simp_all [all]


-- See also Bml/CompletenessViaPaths.lean for inspiration that might be useful here.

/-- Tree data type to keep track of choices made by Builder. Might still need to be tweaked.
- Choices should be labelled with the choices made by prover?
- Maybe we also need to carry proofs in here?
-/
inductive BuildTree : GamePos → Type
  | Leaf {pos} (rp : rep pos.1 pos.2.1) : BuildTree pos
  | Step {pos} (YS : List GamePos) (next : ∀ newPos ∈ YS, BuildTree newPos) : BuildTree pos

-- QUESTION: are actually all leafs in the BuildTree backpointers?

def theRep {H X} (rp : rep H X) : Nat :=
  match h : List.findIdx? (fun Y => decide (Y.setEqTo X)) H with
  | none => by
      exfalso
      have : ∃ Y ∈ H, decide (Y.setEqTo X) = true := by aesop
      have := @List.findIdx?_eq_some_of_exists Sequent H (fun Y => Y.setEqTo X) this
      simp_all
  | some k => k

/-- The tree generated from a winning Builder strategy -/
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
        exact move.prPdl r
      .Step prMoves <| fun Y Y_in => buildTree s (stillWin _ Y_in)
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
      .Step prMoves <| fun Y Y_in => buildTree s (stillWin _ Y_in)
  -- Builder positions:
  | Sum.inr (.lpr _) => by exfalso; simp [winning] at h -- prover wins, cannot happen
  | Sum.inr (.ltab nrep nbas ltX) =>
      if ne : (tableauGame.moves ⟨H, ⟨X, Sum.inr (BuilderPos.ltab nrep nbas ltX)⟩⟩).Nonempty
      then
        -- use `s` to choose `Y ∈ endNodeOf ltX`
        let Y := (s ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ (by simp) ne)
        have stillWin : winning s Y.1 := winning_of_winning_move _ h
        have forTermination : move ⟨H, X, Sum.inr (.ltab nrep nbas ltX)⟩ Y.1 := by
          have := Y.2
          simp only [Game.Pos.moves, tableauGame, theMoves, List.mem_toFinset] at this
          have := fun Y => @move.buEnd X ltX Y H nrep nbas
          grind
        .Step [ Y.1 ] <| fun Y Y_in => by simp at Y_in; subst Y_in; exact buildTree s stillWin
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
    exact move.prPdl r
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    -- show that it's a move
    unfold prMoves at Y_in
    simp only [List.mem_map] at Y_in
    rcases Y_in with ⟨ltX, _, def_pos⟩
    subst def_pos
    apply @move.prLocTab H X nrep nbas
  · simp_wf
    simp only [tableauGame, Game.wf, WellFoundedRelation.rel]
    -- show that it's a move
    exact forTermination

-- IDEA: define paths and edge-relation inside BuildTree as in `TableauPath.lean`?
-- Then define *maximal* paths? Including going via back-edges!?

-- TODO Definition 6.13 initial, pre-state

-- TODO Lemma 6.14: how to collect formulas in a pre-state

-- TODO Lemma 6.15

-- TODO Lemma 6.16 pre-states are locally consistent and saturated, last node basic.

-- TODO Definition 6.18 to get model graph from strategy tree.

-- TODO Lemma 6.18

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded

-- TODO Lemma 6.20: diamond existence lemma for pre-states

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (mg : ModelGraph WS), X.toFinset ∈ WS := by
  let bt := buildTree s h
  sorry
