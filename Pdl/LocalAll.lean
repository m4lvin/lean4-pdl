import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.ReduceOption

import Pdl.LocalTableau

/-! # Generating all Local Tableaux -/

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
    : OneSidedLocalRule.all L = some ⟨B, osr⟩ := by
  cases osr
  all_goals
    simp [OneSidedLocalRule.all]
    try assumption

-- TODO instance OneSidedLocalRule.fintype : Fintype (OneSidedLocalRule L B) := ...

/-- Given a negated loaded formula, is there a LoadRule applicable to it? -/
def LoadRule.the : (nχ : NegLoadFormula) → Option (Σ ress, LoadRule nχ ress)
  | (~'⌊α⌋(.loaded _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia  notAtom⟩ else none
  | (~'⌊α⌋(.normal _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia' notAtom⟩ else none

def LoadRule.the_spec (lor : LoadRule (~'χ) ress) : some ⟨ress, lor⟩ = LoadRule.the (~'χ) := by
  cases lor
  all_goals
    simp [LoadRule.the]
    assumption

-- TODO LoadRule.fintype : Fintype LoadRule := ⟨LoadRule.all, LoadRule.all_spec⟩

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

-- TODO instance : Fintype (LocalRule L B) := ⟨(LocalRule.all L).toList, LocalRule.all_spec⟩

/-- Given a sequent, return a list of all possible local rule applications. -/
def LocalRuleApp.all : (X : Sequent) → List LocalRuleApp
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
          (fun ⟨B,lr⟩ =>
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
            { L := L, R := R, O:= o, preconditionProof := h, Lcond := Lcond, Rcond := Rcond,
              Ocond := Ocond, lr := lr, ress := _ }
            ))).reduceOption

lemma LocalRuleApp.all_X (X : Sequent) : ∀ lra ∈ LocalRuleApp.all X, lra.X = X := by
  intro lra lra_in
  rcases X with ⟨L, R, O⟩
  simp only [all, List.map_cons, List.map_nil, applyLocalRule, List.reduceOption_mem_iff,
    List.mem_map, List.mem_attach, true_and, Subtype.exists, List.mem_flatMap,
    List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false] at lra_in
  grind [Option.map_eq_some_iff]

set_option maxHeartbeats 10000000 in -- for aesop timeouts
lemma LocalRuleApp.all_spec (lrA : LocalRuleApp) : lrA ∈ LocalRuleApp.all lrA.X := by
  rcases lrA with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, ⟨subpermL, subpermR, subO⟩⟩
  have subpermL_ := List.subperm_iff.mp subpermL
  have subpermR_ := List.subperm_iff.mp subpermR
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
  case LRnegL φ =>
    simp only [all, List.empty_eq, List.map_cons, List.map_nil, applyLocalRule,
      List.map_attach_eq_pmap, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
      List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨[φ],[~φ],none⟩
    aesop
  case LRnegR φ =>
    simp only [all, List.empty_eq, List.map_cons, List.map_nil, applyLocalRule,
      List.map_attach_eq_pmap, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
      List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
    use ⟨[~φ],[φ],none⟩
    aesop
  case loadedL χ lor YS_def =>
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
        subst_eqs
        simp_all
      · unfold LocalRuleApp.all
        simp only [List.empty_eq, List.map_cons, List.map_nil, applyLocalRule,
          List.reduceOption_mem_iff, List.mem_map, List.mem_attach, true_and, Subtype.exists,
          List.mem_flatMap, List.mem_permutations, List.mem_sublists, List.mem_cons,
          List.not_mem_nil, or_false]
        subst_eqs
        simp only [List.empty_eq]
        use (∅, ∅, some (Sum.inl (~'⌊α⌋AnyFormula.normal φ)))
        simp only [List.nil_sublist, and_true, Option.mem_def, List.empty_eq, List.diff_nil,
          applyLocalRule, List.map_map, Option.map_eq_some_iff, mk.injEq, true_and, Sigma.exists,
          exists_prop] at *
        rw [this]
        aesop
    case loaded =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      -- `O` comes from `X`, so it is the old/before olf. The `o` is the new one.
      cases O <;> cases lor
      · -- imposible, if O = none then we cannot apply a loadedL rule.
        exfalso
        simp_all
      · unfold LocalRuleApp.all
        simp [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inl (~'⌊α⌋AnyFormula.loaded χ)))
        aesop
  case loadedR χ lor YS_def =>
    -- COPY-PASTA from loadedL case, changed inl to inr.
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
        subst_eqs
        simp_all
      · unfold LocalRuleApp.all
        simp only [List.empty_eq, List.map_cons, List.map_nil, applyLocalRule,
          List.reduceOption_mem_iff, List.mem_map, List.mem_attach, true_and, Subtype.exists,
          List.mem_flatMap, List.mem_permutations, List.mem_sublists, List.mem_cons,
          List.not_mem_nil, or_false]
        subst_eqs
        simp only [List.empty_eq]
        use (∅, ∅, some (Sum.inr (~'⌊α⌋AnyFormula.normal φ)))
        simp only [List.empty_eq, List.nil_sublist, and_true, Option.mem_def, List.diff_nil,
          applyLocalRule, List.map_map, Option.map_eq_some_iff, mk.injEq, true_and, Sigma.exists,
          exists_prop] at *
        rw [this]
        aesop
    case loaded =>
      rcases this with ⟨ress_def, ⟨α_notAtomic, lor_heq_def⟩⟩
      -- `O` comes from `X`, so it is the old/before olf. The `o` is the new one.
      cases O <;> cases lor
      · -- imposible, if O = none then we cannot apply a loadedL rule.
        exfalso
        simp_all
      · unfold LocalRuleApp.all
        simp only [List.map_cons, List.map_nil, applyLocalRule, List.map_attach_eq_pmap,
          List.empty_eq, List.reduceOption_mem_iff, List.mem_pmap, List.mem_flatMap,
          List.mem_permutations, List.mem_sublists, List.mem_cons, List.not_mem_nil, or_false]
        use (∅, ∅, some (Sum.inr (~'⌊α⌋AnyFormula.loaded χ)))
        aesop

/-
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
-/

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
    let ⟨lra, lra_mem⟩  <- (LocalRuleApp.all X).attach
    have def_X := LocalRuleApp.all_X X _ lra_mem
    let tabsFor (Y : Sequent) (h : Y ∈ lra.C) : List (LocalTableau Y) := by
      have _forTermination := localRuleApp.decreases_DM lra _ h
      apply LocalTableau.all
    let nexts : List ((Y : Sequent) → Y ∈ lra.C → LocalTableau Y) := combo tabsFor
    let next <- nexts
    return @byLocalRule X lra def_X.symm next
termination_by
  X => X
decreasing_by
  exact def_X ▸ _forTermination

lemma LocalTableau.all_spec : ltX ∈ LocalTableau.all X := by
  by_cases Xbas : X.basic
  · unfold LocalTableau.all
    cases ltX
    case pos.byLocalRule lra next X_def =>
      absurd Xbas
      exact X_def ▸ nonbasic_of_localRuleApp lra
    · simp_all
  · unfold LocalTableau.all
    simp_all
    cases ltX
    case neg.byLocalRule lra next X_def =>
      refine ⟨lra, X_def ▸ LocalRuleApp.all_spec lra, ?_⟩
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
