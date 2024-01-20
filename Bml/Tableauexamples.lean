-- TABLEAU-EXAMPLES

import Mathlib.Data.Finset.Basic

import Bml.Syntax
import Bml.Tableau

theorem noBot : Provable (~⊥) := by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.appTab =>
    apply AppLocalTableau.mk
    apply LocalRuleApp.mk _ {~~⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥))
    simp
    use applyLocalRule (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥)) ({~~⊥}, ∅)
    rfl
    · -- build one child tableau
      intro c c_in
      simp  at c_in
      subst c_in
      let ltBot : LocalTableau ({⊥},∅) := by
        apply LocalTableau.fromRule
        apply AppLocalTableau.mk
        apply LocalRuleApp.mk _ {⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.bot))
        simp
        use []
        simp
        aesop
      exact ltBot
  case a.next =>
    -- show that endNodesOf is empty
    intro Y Y_in
    simp [endNodesOf] at *

theorem noContradiction : Provable (~(p⋀~p)) :=
  by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.appTab =>
    apply AppLocalTableau.mk
    apply LocalRuleApp.mk _ {~~(p⋀~p)} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg (p⋀~p)))
    all_goals (try simp; try rfl) -- easier than guessing "use applyLocalRule ..."
    · intro c c_in
      simp at c_in
      subst c_in -- unique child node
      let ltB : LocalTableau ({p⋀~p},∅) := by
        apply LocalTableau.fromRule
        apply AppLocalTableau.mk
        apply LocalRuleApp.mk _ {p⋀~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)))
        simp
        all_goals (try rfl)
        intro c c_in
        simp at c_in
        subst c_in -- unique child node
        let ltC : LocalTableau ({p, ~p}, ∅) := by
          apply LocalTableau.fromRule
          apply AppLocalTableau.mk
          apply LocalRuleApp.mk _ {p, ~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.not p))
          simp
          use [] -- claim that there are no more children
          simp
          aesop
        exact ltC
      exact ltB
  case a.next =>
    -- show that endNodesOf is empty
    intro Y Y_in
    simp [endNodesOf] at *

-- preparing example 2
def subTabForEx2 : ClosedTableau {r, ~(□p), □(p⋀q)} :=
  by
  apply @ClosedTableau.atm {r, ~(□p), □(p⋀q)} p (by simp) (by simp (config := {decide := true}))
  apply ClosedTableau.loc
  rotate_left
  -- con:
  apply LocalTableau.byLocalRule (@LocalRule.Con {p⋀q, ~p} p q (by simp))
  intro child childDef
  rw [Finset.mem_singleton] at childDef 
  -- not:
  apply LocalTableau.byLocalRule (@LocalRule.Not _ p _) emptyTableau
  · subst childDef; exact by decide
  · -- show that endNodesOf is empty
    intro Y
    intro YisEndNode
    simp at *

-- Example 2
example : ClosedTableau {r⋀~(□p), r↣□(p⋀q)} :=
  by
  apply ClosedTableau.loc
  rotate_left
  · -- con
    apply LocalTableau.byLocalRule
    apply LocalRule.Con
    simp only [impl, Finset.mem_insert, Finset.mem_singleton, or_false_iff]
    constructor
    intro branch branch_def
    rw [Finset.mem_singleton] at branch_def 
    rw [Finset.union_insert] at branch_def 
    -- nCo
    apply LocalTableau.byLocalRule
    apply @LocalRule.nCo _ r (~(□(p⋀q)))
    · rw [branch_def]; simp
    intro b b_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at b_in 
    refine' if h1 : b = branch \ {~(r⋀~(□(p⋀q)))} ∪ {~r} then _ else _
    · -- right branch
      -- not:
      apply LocalTableau.byLocalRule (@LocalRule.Not _ r _) emptyTableau
      subst h1
      subst branch_def
      simp
      right
      by_contra hyp
      contradiction
    · --left branch
      have h2 : b = branch \ {~(r⋀~(□(p⋀q)))} ∪ {~~(□(p⋀q))} := by tauto
      -- neg:
      apply LocalTableau.byLocalRule (@LocalRule.neg _ (□(p⋀q)) _)
      rotate_left; · rw [h2]; simp
      intro child childDef
      -- ending local tableau with a simple node:
      apply LocalTableau.sim
      rw [Finset.mem_singleton] at childDef 
      rw [childDef]
      unfold Simple; simp at *
      intro f f_notDef1 f_in_branch
      cases b_in
      · tauto
      case inr b_in =>
        rw [b_in] at f_in_branch
        simp at f_in_branch
        cases f_in_branch
        · tauto
        case inr f_in_branch =>
          rw [branch_def] at f_in_branch
          cases' f_in_branch with l r
          aesop
  · -- tableau for the simple end nodes:
    rw [conEndNodes]
    rw [nCoEndNodes]
    intro Y Yin
    simp (config := {decide := true}) at *
    · -- notnotbranch
      have Yis : Y = {r, ~(□p), □(p⋀q)} := by
        subst Yin
        ext1
        constructor <;> intro hyp
        aesop
        simp (config := {decide := true}) at *
        rcases hyp with hyp|(hyp|hyp)
        all_goals (subst hyp ; simp at *)
        right
        by_contra
        contradiction
      subst Yis
      exact subTabForEx2

