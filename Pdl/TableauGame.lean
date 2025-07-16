import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm

import Pdl.Game
import Pdl.Tableau
import Pdl.Modelgraphs

/-! # The Tableau Game (Section 6.2 and 6.3) -/

/-! ## Defining the Tableau Game (Section 6.2) -/

-- Renaming the players for the tableau game:
notation "Prover" => Player.A
notation "Builder" => Player.B

inductive ProverPos (H : History) (X : Sequent) : Type where
  | nlpRep : ¬ Nonempty (LoadedPathRepeat H X) → rep H X → ProverPos H X -- Prover loses
  | bas : ¬ rep H X → X.basic → ProverPos H X -- Prover must apply a PDL rule
  | nbas : ¬ rep H X → ¬ X.basic → ProverPos H X -- Prover must make a local LocalTableau
  deriving DecidableEq

-- TODO add proofs here that we have no rep and we only do ltX for X being nbasic
def BuilderPos (H : History) (X : Sequent) : Type :=
  LoadedPathRepeat H X -- no moves, Prover wins.
  ⊕
  LocalTableau X -- Builder must pick from endNodesOf

instance {H X} : DecidableEq (BuilderPos H X) := by
  rintro (_|_) (_|_) <;> try (simp; exact instDecidableFalse)
  · rename_i lr1 lr2
    by_cases lr1 = lr2
    · apply isTrue
      aesop
    · apply isFalse
      intro hyp
      cases hyp
      aesop
  · rename_i lt1 lt2
    by_cases lt1 = lt2
    · apply isTrue
      aesop
    · apply isFalse
      intro hyp
      cases hyp
      aesop

def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
  deriving DecidableEq

-- There's probably a more elegant way to fully avoid Nonempty and choice here?
-- Something like: def isLPR (H : History) (X : Sequent) : Prop := sorry

def LoadedPathRepeat.choice {H X} (ne : Nonempty (LoadedPathRepeat H X)) : LoadedPathRepeat H X := by
  let somek := @Fin.find (H.length)
    (fun k => (H.get k).multisetEqTo X ∧ ∀ m ≤ k, (H.get m).isLoaded = true) _
  rcases find_def : somek with _|⟨k⟩
  · exfalso
    rw [Fin.find_eq_none_iff] at find_def
    rcases ne with ⟨⟨k,bla⟩⟩
    specialize find_def k
    aesop
  · refine ⟨k, ?_⟩
    rw [Fin.find_eq_some_iff] at find_def
    aesop

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if neNlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.inl (.choice neNlp)) -- BuilderPos with no moves to let Prover win at lpr
  else
    if rep : rep H X
    then .inl (.nlpRep neNlp rep) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas rep bas) -- actual ProverPos to choose a PDL rule
      else .inl (.nbas rep bas) -- actual ProverPos to make LocalTab

-- TODO turn these below into Fintype instances? Move to LocalTableau.lean?

def OneSidedLocalRule.all : (L : List Formula) → Option (Σ B, OneSidedLocalRule L B)
  | [⊥]       =>  some ⟨∅, bot⟩
  | [φ1, ~φ2] => if h : φ1 = φ2 then h ▸ some ⟨∅, not φ1⟩ else none -- hmm else is ok?
  | [~(~(φ))] => some ⟨[[φ]], neg φ⟩
  | [φ ⋀ ψ]   => some ⟨[[φ,ψ]], con φ ψ⟩
  | [~(φ⋀ψ)]  => some ⟨[[~φ], [~ψ]], nCo φ ψ⟩
  | [⌈α⌉φ]    => if notAtm : ¬ α.isAtomic then some ⟨unfoldBox α φ, box _ _ notAtm ⟩ else none
  | [~⌈α⌉φ]   => if notAtm : ¬ α.isAtomic then some ⟨(unfoldDiamond α φ), dia α φ notAtm⟩ else none
  | _ => none

def OneSidedLocalRule.all_spec (osr : OneSidedLocalRule L B)
    : ⟨B, osr⟩ ∈ OneSidedLocalRule.all L := by
  cases osr
  all_goals
    simp [OneSidedLocalRule.all]
    try assumption

/-- Given a negated loaded formula, is there a LoadRule applicable to it? -/
def LoadRule.the : (nχ : NegLoadFormula) → Option (Σ ress, LoadRule nχ ress)
  | (~'⌊α⌋(.loaded _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia  notAtom⟩ else none
  | (~'⌊α⌋(.normal _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia' notAtom⟩ else none

def LoadRule.the_spec (lor : LoadRule (~'χ) ress) : some ⟨ress, lor⟩ = LoadRule.the (~'χ) := by
  cases lor
  all_goals
    simp [LoadRule.the]
    assumption

/-- Given a subsequent `cond` to be replaced, is there an applicable local rule?
Note that `cond` are only the principal formulas, not the whole sequent. -/
def LocalRule.all : (cond : Sequent) → Option (Σ ress, LocalRule cond ress)
  | ⟨L, [], none⟩ =>
      (OneSidedLocalRule.all L).map (fun ⟨_,orule⟩ => ⟨_, LocalRule.oneSidedL orule rfl⟩)
  | ⟨[], R, none⟩ =>
      (OneSidedLocalRule.all R).map (fun ⟨_,orule⟩ => ⟨_, LocalRule.oneSidedR orule rfl⟩)
  | ([φ1], [φ2], none) => if h : φ2 = (~φ1) then some ⟨_, by convert LRnegL φ1⟩ else
                          if h : φ1 = (~φ2) then some ⟨_, by convert LRnegR φ2⟩ else none
  | ⟨[], [], some (Sum.inl (~'⌊α⌋(.loaded χ)))⟩ =>
      if notAtm : ¬ α.isAtomic then some ⟨_, .loadedL _ (@LoadRule.dia  α _ notAtm) rfl⟩ else none
  | ⟨[], [], some (Sum.inl (~'⌊α⌋(.normal φ)))⟩ =>
      if notAtm : ¬ α.isAtomic then some ⟨_, .loadedL _ (@LoadRule.dia' α _ notAtm) rfl⟩ else none
  | ⟨[], [], some (Sum.inr (~'⌊α⌋(.loaded χ)))⟩ =>
      if notAtm : ¬ α.isAtomic then some ⟨_, .loadedR _ (@LoadRule.dia  α _ notAtm) rfl⟩ else none
  | ⟨[], [], some (Sum.inr (~'⌊α⌋(.normal φ)))⟩ =>
      if notAtm : ¬ α.isAtomic then some ⟨_, .loadedR _ (@LoadRule.dia' α _ notAtm) rfl⟩ else none
  | _ => none

def LocalRule.all_spec (lr : LocalRule L B) : ⟨B, lr⟩ ∈ LocalRule.all L := by
  cases lr <;> simp [LocalRule.all]
  case oneSidedL precond ress osr B_def =>
    have := OneSidedLocalRule.all_spec osr
    aesop
  case oneSidedR precond ress osr B_def =>
    -- Less simp'd here because we do not know L ≠ [] yet.
    have := OneSidedLocalRule.all_spec osr
    cases osr
    <;> aesop
  case LRnegR =>
    intro h
    cases h
  case loadedL αχ lrule YS_def =>
    rcases αχ with ⟨α,φ|χ⟩ <;> cases lrule <;> aesop
  case loadedR αχ lrule YS_def =>
    rcases αχ with ⟨α,φ|χ⟩ <;> cases lrule <;> aesop

/-- Given a sequent, return a list of all possible local rule applications. -/
def LocalRuleApp.all : (X : Sequent) → List (Σ C, LocalRuleApp X C)
  | ⟨L, R, o⟩ =>
      -- The idea here is to apply `LocalRule.all` to all sublists of L, R.
      -- But `List.sublists` would not be enough, because the `preconditionProof`
      -- in `LocalRuleApp` uses `List.Subperm`, not sublists.
      -- We thus consider all permutations and then their sublists.
      -- (Alternative would be to consider all sublists and then their permutations.) ???
      -- Maybe somethimg like `List.subpermutations` should be added to Mathlib?
      let Lconds := L.permutations.flatMap List.sublists
      let Rconds := R.permutations.flatMap List.sublists
      let Oconds := [ none, o ] -- might be a duplicate, but so what?
      let conds : List Sequent :=
        (Lconds.flatMap
          (fun Lcond => Rconds.flatMap
            (fun Rcond => Oconds.map
              (fun Ocond => (Lcond,Rcond,Ocond)))))
      (conds.attach.map (fun ⟨⟨Lcond,Rcond,Ocond⟩, cond_in⟩ =>
        (LocalRule.all ⟨Lcond,Rcond,Ocond⟩).map
          (fun ⟨B,lr⟩  => ⟨applyLocalRule lr (L, R, o),
            have h : Lcond.Subperm L ∧ Rcond.Subperm R ∧ Ocond ⊆ o := by
              simp only [List.map_cons, List.map_nil, List.mem_flatMap, List.mem_permutations,
                List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false, conds, Oconds, Rconds,
                Lconds] at cond_in
              rcases cond_in with ⟨Lc,Lc_sub,Rc,Rc_sub,cdef|cdef⟩ <;> cases cdef <;> simp_all
              · constructor
                · rcases Lc_sub with ⟨L0, L0_sub_L, Lcond_perm_of_L0⟩
                  rw [@List.subperm_iff]
                  use L0
                · rcases Rc_sub with ⟨R0, R0_sub_R, Rcond_perm_of_R0⟩
                  rw [@List.subperm_iff]
                  use R0
              · refine ⟨?_, ?_, ?_⟩
                · rcases Lc_sub with ⟨L0, L0_sub_L, Lcond_perm_of_L0⟩
                  rw [@List.subperm_iff]
                  use L0
                · rcases Rc_sub with ⟨R0, R0_sub_R, Rcond_perm_of_R0⟩
                  rw [@List.subperm_iff]
                  use R0
                · cases o <;> simp_all
            @LocalRuleApp.mk L R _ B o Lcond Rcond Ocond lr rfl h⟩))).reduceOption

set_option maxHeartbeats 10000000 in
lemma LocalRuleApp.all_spec X C (lrA : LocalRuleApp X C) : ⟨C, lrA⟩ ∈ LocalRuleApp.all X := by
  rcases X with ⟨L,R,O⟩
  rcases lrA with ⟨Lcond, Rcond, Ocond, rule, preconditionProof⟩
  rcases preconditionProof with ⟨subpermL, subpermR, subO⟩
  rw [List.subperm_iff] at subpermL
  rw [List.subperm_iff] at subpermR
  have := LocalRule.all_spec rule
  cases rule
  · simp only [all, List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
    List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
    List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨Lcond,[],none⟩
    aesop
  · simp only [all, List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
    List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
    List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨[],Rcond,none⟩
    aesop
  case LRnegL φ _ _ hC =>
    simp [all, List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
    List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
    List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨[φ],[~φ],none⟩
    aesop
  case LRnegR φ _ _ hC =>
    simp [all, List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
    List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
    List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨[~φ],[φ],none⟩
    aesop
  case loadedL χ lor _ _ _ C_def =>
    have := LoadRule.the_spec lor
    rcases χ  with ⟨α, ξ⟩
    rcases ξ with (φ|χ) <;> simp only [LoadRule.the, dite_not, Option.some_eq_dite_none_left,
      Option.some.injEq, Sigma.mk.injEq, exists_and_left] at this
    case normal =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      -- `O` comes from `X`, so it is the old/before olf. The `o` is the new one.
      cases O <;> cases lor
      · -- imposible, if O = none then we cannot apply a loadedL rule.
        exfalso
        simp_all
      · unfold LocalRuleApp.all
        -- // aesop from here
        simp [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inl (~'⌊α⌋AnyFormula.normal φ)))
        aesop
    case loaded =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      -- `O` comes from `X`, so it is the old/before olf. The `o` is the new one.
      cases O <;> cases lor
      · -- imposible, if O = none then we cannot apply a loadedL rule.
        exfalso
        simp_all
      · unfold LocalRuleApp.all
        -- // aesop from here
        simp [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inl (~'⌊α⌋AnyFormula.loaded χ)))
        aesop

  case loadedR χ lor _ _ _ C_def =>
    -- COPY-PASTA from loadedL case, changed inl to inr.
    have := LoadRule.the_spec lor
    rcases χ  with ⟨α, ξ⟩
    rcases ξ with (φ|χ) <;> simp only [LoadRule.the, dite_not, Option.some_eq_dite_none_left,
      Option.some.injEq, Sigma.mk.injEq, exists_and_left] at this
    case normal =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      cases O <;> cases lor
      · exfalso
        simp_all
      · unfold LocalRuleApp.all
        simp only [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inr (~'⌊α⌋AnyFormula.normal φ)))
        aesop
    case loaded =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      cases O <;> cases lor
      · exfalso
        simp_all
      · unfold LocalRuleApp.all
        simp only [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inr (~'⌊α⌋AnyFormula.loaded χ)))
        aesop

/-- At most finitely many local rule applications lead from `X` and to `B`. Note this is weaker
than "only finitely many local rules apply to `X`, because each `B` gives a different type. -/
instance LocalRuleApp.fintype {X} {C} : Fintype (LocalRuleApp X C) := by
  refine ⟨((LocalRuleApp.all X).filterMap
    (fun ⟨C', lra⟩  => if h : C' = C then some (h ▸ lra) else none)).toFinset, ?_⟩
  intro lra
  rw [List.mem_toFinset]
  simp only [List.mem_filterMap, Option.dite_none_right_eq_some, Option.some.injEq, Sigma.exists]
  use C
  simp only [exists_const, exists_eq_right]
  apply LocalRuleApp.all_spec

/-- Convert a function returning lists into a list of functions. Helper for `LocalTableau.all`. -/
def combo {α : Type} [DecidableEq α] {q : α → Type} : {L : List α}
    → (f : (x : α) → x ∈ L → List (q x))
    → List ((x : α) → x ∈ L → q x)
  | [], f => [ fun x x_in => by exfalso; cases x_in ]
  | (x :: xs), f =>
      let IH : (y : α) → y ∈ xs → List (q y) := fun y y_in => f y (by aesop)
      let fx_choices := f x (by simp)
      (combo IH).flatMap (fun g =>
        fx_choices.map (fun fx =>
          fun y y_in =>
            if h : y = x then h ▸ fx else g y (by aesop)))

/-- Characterization of members of `combo` result. Could be strengthened to ↔ later. -/
lemma combo_mem_of_forall_in {α : Type} [DecidableEq α] {q : α → Type} {L : List α}
    (f : (x : α) → x ∈ L → List (q x))
    (g : (x : α) → x ∈ L → q x)
    : (∀ x x_in, g x x_in ∈ f x x_in) → g ∈ combo f := by
  intro hyp
  induction L
  · simp only [List.not_mem_nil, combo, List.mem_cons, or_false]
    ext x x_in
    cases x_in
  case cons x xs IH =>
    simp only [combo, List.mem_flatMap, List.mem_map]
    specialize IH (fun y y_in => f y (by aesop))
    exact ⟨fun y y_in => g _ (by simp_all), IH _ (by grind), (by grind)⟩

def LocalTableau.all : (X : Sequent) → List (LocalTableau X) := fun X =>
  if bas : X.basic
  then [ .sim bas ]
  else do
    let ⟨B, (lra : LocalRuleApp X B)⟩ <- LocalRuleApp.all X
    let tabsFor (Y : Sequent) (h : Y ∈ B) : List (LocalTableau Y) := by
      have _forTermination := localRuleApp.decreases_DM lra _ h
      apply LocalTableau.all
    let nexts : List ((Y : Sequent) → Y ∈ B → LocalTableau Y) := combo tabsFor
    let next <- nexts
    return @byLocalRule X B lra next
termination_by
  X => X
decreasing_by
  exact _forTermination

lemma LocalTableau.all_spec : ltX ∈ LocalTableau.all X := by
  by_cases Xbas : X.basic
  · unfold LocalTableau.all
    cases ltX
    case pos.byLocalRule lra =>
      absurd Xbas
      exact nonbasic_of_localRuleApp lra
    · simp_all
  · unfold LocalTableau.all
    simp_all
    cases ltX
    case neg.byLocalRule B next lra =>
      refine ⟨_, lra, LocalRuleApp.all_spec _ _ _, ?_⟩
      simp only [byLocalRule.injEq, heq_eq_eq, true_and, exists_eq_right']
      apply combo_mem_of_forall_in
      intro Y Y_in
      apply LocalTableau.all_spec -- IH
    case neg.sim =>
      simp_all

instance LocalTableau.fintype {X} : Fintype (LocalTableau X) := by
  refine ⟨(LocalTableau.all X).toFinset, ?_⟩
  intro ltX
  rw [List.mem_toFinset]
  exact LocalTableau.all_spec

/-- WORK-IN-PROGRESS. This is the game defined in Section 6.2 in the paper.
In particular `tableauGame.wf` and `tableauGame.move_rel` together are Lemma 6.10: because the
wellfounded relation decreases with every move of the game, all matches must be finite.
Note that the paper does not prove Lemma 6.10 but says it is similar to Lemma 4.10 which uses the
Fischer-Ladner closure. -/
def tableauGame : Game where
  Pos := GamePos
  turn
  | ⟨_, _, .inl _⟩ => Prover
  | ⟨_, _, .inr _⟩ => Builder
  moves
  -- ProverPos:
  | ⟨H, X, .inl (.nlpRep _ _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ Xbasic)⟩ =>
      -- need to choose PDL rule application:
      match X with
      | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula

      -- ERROR here: mixing up  φ ∈ L  with  ~φ ∈ L - negation must be there already to load!

            (L.map (fun φ => match boxesOf φ with -- need ALL the boxes.
              | (δ@h:(_::_), ψ) =>
                [ ⟨_,_,posOf (X::H) (L.erase (~⌈⌈δ⌉⌉φ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊δ.getLast (by subst h; simp)⌋φ))))⟩ ]
              | ([],_) => [] ) ).flatten.toFinset
            ∪
            (R.map (fun φ => match boxesOf φ with -- need ALL the boxes.
              | (δ@h:(_::_), ψ) =>
                [ ⟨_,_,posOf (X::H) (L, R.erase (~⌈⌈δ⌉⌉φ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊δ.getLast (by subst h; simp)⌋φ))))⟩ ]
              | ([],_) => [] ) ).flatten.toFinset
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨(~φ) :: projection a L, projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inl (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L.insert (⌊·a⌋ξ).unload, R, none)⟩ }
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨projection a L, (~φ) :: projection a R, none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨projection a L, projection a R, some (Sum.inr (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L, R.insert (⌊·a⌋ξ).unload, none)⟩ }
      -- Somewhat repetitive. Is there pattern matching with "did not match before" proofs?
      | ⟨L, R, some (.inl (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inl (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
      | ⟨L, R, some (.inr (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic] at *
  | ⟨H, X, .inl (.nbas _ _)⟩ =>
      -- If not basic, let prover pick any `ltab : LocalTableau X` as new position.
      LocalTableau.fintype.1.image (fun ltab => ⟨H, X, .inr (.inr ltab)⟩)
  -- BuilderPos:
  | ⟨H, X, .inr (.inl lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.inr ltab)⟩ =>
      ((endNodesOf ltab).map (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩)).toFinset

  -- QUESTION: What is a wellfounded relation that holds for each game step?
  wf := ⟨fun p q => sorry, by sorry⟩
  move_rel := by
    rintro ⟨H, ⟨L,R,_|olf⟩, ProvPo|BuildPo⟩ nextP nextP_in <;> simp_wf
    -- `none` cases without loaded formula in X:
    · cases ProvPo <;> simp at *
      · sorry
      · sorry
    · cases BuildPo
      · exfalso; simp at * -- cannot have an lpr when not loaded
      · simp at *
        sorry
    -- `some olf` cases with loaded formula in X:
    · sorry
    · sorry

@[simp]
lemma tableauGame_turn_Prover {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inl lpr⟩ = Prover := by
  unfold Game.turn
  unfold tableauGame
  simp

@[simp]
lemma tableauGame_turn_Builder {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inr lpr⟩ = Builder := by
  unfold Game.turn tableauGame
  simp

@[simp]
lemma tableauGame_winner_nlpRep_eq_Builder :
    @winner i tableauGame sI sJ ⟨Hist, X, .inl (.nlpRep h1 h2)⟩ = Builder := by
  simp [winner, tableauGame]

@[simp]
lemma tableauGame_winner_lpr_eq_Prover :
    @winner i tableauGame sI sJ ⟨Hist, X, .inr (.inl lpr)⟩ = Prover := by
  simp [winner, tableauGame]



/-- After history `Hist`, if Prover has a winning strategy then there is a closed tableau.
Note: we skip Definition 6.9 (Strategy Tree for Prover) and just use the `Strategy` type.
This is the induction loading for `gameP`. -/
theorem gameP_general Hist (X : Sequent) (sP : Strategy tableauGame Prover)
  (h : winning sP ⟨Hist, X, posOf Hist X⟩) :
    Nonempty (Tableau Hist X) := by
  rcases pos_def : posOf Hist X with proPos|builPos
  -- ProverPos:
  · cases proPos
    · -- free repeat, but then Prover loses, which contradicts h.
      absurd h
      simp [pos_def,winning]
    case bas nrep Xbas =>
      -- basic, Prover should choose PDL rule
      rw [pos_def] at h

      have P_turn : tableauGame.turn ⟨Hist, ⟨X, posOf Hist X⟩⟩ = Prover := by
        rw [pos_def]
        simp
      -- Ask `sP` say which move to make / what rule to apply.
      let the_move := sP ⟨_ ,_, posOf Hist X⟩ ?_ ?_
      case refine_1 => rw [pos_def]; unfold Game.turn tableauGame; simp
      case refine_2 => by_contra hyp; exfalso; unfold winning winner at h; simp_all


      rcases the_move with ⟨nextPos, nextPosIn⟩
      rcases nextPos with ⟨newHist, newX, newPos⟩

      have IH := gameP_general newHist newX sP (by sorry) -- okay ??

      unfold Game.Pos.moves Game.moves tableauGame at nextPosIn
      simp [pos_def] at nextPosIn
      rcases X with ⟨L,R,_|(⟨⟨χ⟩⟩|⟨⟨χ⟩⟩)⟩
      <;> simp at *
      · rcases nextPosIn with ⟨φ, φ_in⟩|_
        · rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
          · exfalso; aesop
          · simp_all
            rcases φ_in with ⟨φ_in, new_def⟩
            cases new_def
            have φ_def : φ = ⌈δ⌉⌈⌈αs⌉⌉ ψ := by sorry
            -- leaving Prop
            constructor
            -- apply Tableau.pdl nrep Xbas (.loadL (φ_def ▸ φ_in) _)  -- see ERROR above!
            sorry
        ·

          sorry
      · sorry
      · sorry


    case nbas nrep X_nbas =>
      -- not basic, Prover should make a local tableau
      constructor
      apply Tableau.loc nrep X_nbas
      -- IDEA: now `sJ` should give us `lt`
      -- and applying an IH should give us `next` ???
      all_goals
        sorry
  -- BuilderPos:
  · rcases builPos with lpr|ltX
    · use Tableau.lrep lpr
    · -- We have a local tableau and it is the turn of Builder.
      -- IDEA: for each `Y : endNodesOf lt` there is an `sB : Strategy _ Prover` that picks `Y`.
      -- Because `sP` wins against all those `sB`, we can use `sP` to define `next`.
      -- For now we do this non-constructively via Nonempty.
      have next' : ∀ (Y : Sequent) (Y_in : Y ∈ endNodesOf ltX), Nonempty (Tableau (X :: Hist) Y) := by
        intro Y Y_in
        apply gameP_general (X :: Hist) Y sP -- Here we apply an IH.
        -- use `h`
        unfold winning at h
        -- NOTE: maybe external lemma like "winning of winning at next step chosen by other" ..
        -- Is there something like this in `Game.lean` already?
        let sJ : Strategy tableauGame Builder := sorry -- some strategy that chooses `Y` ???
        specialize h sJ
        unfold winner at h
        rw [pos_def] at h
        simp at h
        -- Hmmmmm
        unfold winning
        sorry
      have next := fun Y Y_in => Classical.choice (next' Y Y_in)
      use Tableau.loc ?_ ?_ ltX next
      -- Do the remaing two things follow from Prover winning? Or add proof fields to buildPos???
      · sorry -- need nrep
      · sorry -- need nbas
termination_by
  tableauGame.wf.2.wrap ⟨Hist, X, posOf Hist X⟩
decreasing_by
  all_goals
    apply tableauGame.move_rel
    simp [WellFounded.wrap]
  -- Need to show that a valid move was made
  · convert nextPosIn
    -- hmm??
    sorry
  · -- hmm?
    sorry

def startPos (X : Sequent) : GamePos := ⟨[], X, posOf [] X⟩

/-- If Prover has a winning strategy then there is a closed tableau. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    Nonempty (Tableau [] X) := gameP_general [] X s h

/-! ## From winning strategies to model graphs (Section 6.3) -/

-- See also Bml/CompletenessViaPaths.lean for the things needed here.

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
  sorry
