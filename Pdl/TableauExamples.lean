import Mathlib.Data.Finset.Basic

import Pdl.Tableau

/-! # Tableau Examples

As a sanity check we construct tableaux/proofs for some examples.
-/

example : provable (~⊥) := by
  apply provable.byTableauL
  apply Tableau.loc
  · simp [rep]
  · simp [Sequent.basic] -- works :-)
  case a.lt =>
    apply LocalTableau.byLocalRule
      ⟨[~~⊥], [], none, LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥), by simp⟩
      ?_
    · exact [([⊥], [], none)]
    · simp
    · -- build one child tableau
      intro c c_in
      simp at c_in
      subst c_in
      apply LocalTableau.byLocalRule
        ⟨[⊥], [], none, LocalRule.oneSidedL (OneSidedLocalRule.bot), by simp⟩
        ?_
      · exact []
      · simp
      · aesop
  case a.next =>
    intro Y Y_in
    exfalso -- endNodesOf is empty
    simp at Y_in

example : provable (~(p ⋀ (~p))) :=
  by
  apply provable.byTableauL
  apply Tableau.loc
  · simp [rep]
  · simp [Sequent.basic] -- works :-)
  case a.lt =>
    apply LocalTableau.byLocalRule
      ⟨[ ~~(p ⋀ (~p))], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.neg (p ⋀ (~p)))), _⟩
      ?_
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in
    apply LocalTableau.byLocalRule
      ⟨[p ⋀ (~p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)), _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in -- unique child node
    apply LocalTableau.byLocalRule
      ⟨[p, ~p], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not p), _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in
  case a.next =>
    intro Y Y_in
    exfalso -- endNodesOf is empty
    simp at Y_in

example : Tableau [] ([·p, ~(·p)], [], none) :=
  by
  apply Tableau.loc
  · simp [rep]
  · simp [Sequent.basic, Sequent.closed]
    -- Here is an example where all formulas are basic
    -- but we still to do `loc` to close the tableau.
    -- For this we made "not closed" part of `Sequent.basic`.
  case lt =>
    apply LocalTableau.byLocalRule
      ⟨[·p, ~(·p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not (·p)), _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in
  case next =>
    intro Y Y_in
    exfalso -- endNodesOf is empty
    simp at Y_in

def atP : Nat := 1

def atQ : Nat := 2
def atR : Nat := 3
def atA : Nat := 4

abbrev p : Formula := · atP
abbrev q : Formula := · atQ
abbrev r : Formula := · atR

abbrev a : Program := · atA

/-- Preparation for Example 2 from MB. -/
def subTabForEx2 : Tableau [([r⋀(~⌈a⌉p), ~ r⋀(~⌈a⌉p⋀q)], [], none)] ([r, ~(⌈a⌉p), ⌈a⌉(p⋀q)], [], none) :=
  by
  have principal : (~(⌈a⌉p)) ∈ [r, ~(⌈a⌉p), ⌈a⌉(p⋀q)] := by simp
  apply Tableau.pdl (by simp [rep, Sequent.setEqTo]; decide) (by simp [Sequent.basic, Sequent.closed])
    (@PdlRule.loadL _ [] _ _ _ principal)
  simp
  apply Tableau.pdl (by simp [rep, Sequent.setEqTo]) (by simp [Sequent.basic, Sequent.closed])
    (.modL rfl) -- Note: modL no longer needs to ask for basic.
  simp [projection]
  apply Tableau.loc
  · simp [rep, Sequent.setEqTo]
    decide
  · simp [Sequent.basic, Sequent.closed]
  case lt =>
    apply LocalTableau.byLocalRule
      ⟨ [p⋀q], [], none, LocalRule.oneSidedL (OneSidedLocalRule.con p q), _⟩
    all_goals (try simp; try rfl)
    · intro c c_in; simp at c_in; subst c_in -- unique child node
      apply LocalTableau.byLocalRule
        ⟨ [p, (~p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not p), _⟩
      all_goals (try simp; try rfl)
      · intro c c_in; simp at c_in
      · decide -- This works because p and q are concrete values, not variables :-)
  case next =>
    intro Y Y_in
    exfalso
    aesop

/-- Example 2 from MB. -/
example : Tableau [] ([r ⋀ (~(⌈a⌉p)), r ↣ ⌈a⌉(p ⋀ q)], [], none) :=
  by
  apply Tableau.loc
  · simp [rep]
  · simp [Sequent.basic, Sequent.closed]
  case lt =>
    apply LocalTableau.byLocalRule
      ⟨[r ⋀ (~(⌈a⌉p))], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.con r (~(⌈a⌉p)))), _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in -- unique child node
    apply LocalTableau.byLocalRule
      ⟨[(~(r ⋀ (~(⌈a⌉(p ⋀ q)))))], [], none,
        (LocalRule.oneSidedL (OneSidedLocalRule.nCo r (~(⌈a⌉(p ⋀ q))))), _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at *
    -- now branching!
    by_cases c = ([r, ~⌈a⌉p, ~ r], [], none) <;> simp_all
    case pos c_def =>
      subst c_def
      -- first branch, apply "not"
      apply LocalTableau.byLocalRule
        ⟨ [r, ~(r)], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.not r)), _ ⟩
      all_goals (try simp; try rfl)
      · intro c c_in; simp at *
      · decide
    case neg hyp =>
      subst c_in
      -- second branch, apply "neg" and then modal step!
      apply LocalTableau.byLocalRule
        ⟨ [~~(⌈a⌉( p ⋀q))], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.neg (⌈a⌉(p⋀q)))), _ ⟩
      all_goals (try simp; try rfl)
      intro c c_in; simp at c_in; subst c_in -- unique child node
      -- ending local tableau with a simple node:
      apply LocalTableau.sim
      simp [Sequent.basic, Sequent.closed]
  case next =>
      intro Y Y_in
      simp (config := {decide := true}) at *
      subst Y_in
      exact subTabForEx2
