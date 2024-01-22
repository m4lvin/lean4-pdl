-- TABLEAU-EXAMPLES

import Mathlib.Data.Finset.Basic

import Bml.Syntax
import Bml.Tableau

theorem noBot : Provable (~⊥) := by
  apply Provable.byTableau
  apply ClosedTableau.loc
  swap
  · apply LocalTableau.byLocalRule (LocalRule.neg (Finset.mem_singleton.mpr (refl (~~⊥))))
    intro β inB
    rw [Finset.sdiff_self] at inB
    rw [Finset.empty_union] at inB
    rw [Finset.mem_singleton] at inB
    rw [inB]
    apply LocalTableau.byLocalRule (LocalRule.bot (Finset.mem_singleton.mpr (refl ⊥)))
    intro Y YinEmpty
    aesop
  · -- show that endNodesOf is empty
    intro Y
    intro YisEndNode
    unfold endNodesOf at *
    simp at *
    exfalso
    rcases YisEndNode with ⟨a, h, hyp⟩
    subst h
    simp at *

def emptyTableau : ∀ β : Finset Formula, β ∈ (∅ : Finset (Finset Formula)) → LocalTableau β :=
  by
  intro beta b_in_empty
  exact absurd b_in_empty (Finset.not_mem_empty beta)

-- an example:
theorem noContradiction : Provable (~(p⋀~p)) :=
  by
  apply Provable.byTableau
  apply ClosedTableau.loc
  swap
  · apply LocalTableau.byLocalRule (@LocalRule.neg _ (p⋀~p) _)
    -- neg:
    intro β β_prop
    simp at β_prop
    subst β_prop
    -- con:
    apply LocalTableau.byLocalRule (@LocalRule.Con _ p (~p) _)
    intro β2 β2_prop
    simp at β2_prop
    subst β2_prop
    -- closed:
    apply LocalTableau.byLocalRule (@LocalRule.Not _ p _) emptyTableau
    all_goals aesop
  · -- show that endNodesOf is empty
    intro Y
    intro YisEndNode
    simp at *
    exfalso
    rcases YisEndNode with ⟨a, h, hyp⟩
    subst h
    simp at *
    rcases hyp with ⟨Y, Ydef, YinEndNodes⟩
    subst Ydef
    aesop

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



def LocTab3 : LocalTableau {(p↣p) ↣ (p⋀p)} := by
  simp
  apply @LocalTableau.byLocalRule {~(~(p⋀~p) ⋀ ~(p⋀p))} _ _ _
  exact {{~~(p⋀~p)}, {~~(p⋀p)}}
  apply @LocalRule.nCo {~(~(p⋀~p) ⋀ ~(p⋀p))} (~(p⋀~p)) (~(p ⋀ p)) (Finset.mem_singleton.mpr rfl)
  intro Y h₀
  simp at h₀
  by_cases h₁ :Y = {~~(p⋀~p)}
  subst h₁ ; clear h₀
  apply @LocalTableau.byLocalRule {~~(p⋀~p)} {{p⋀~p}}
  apply @LocalRule.neg {~~(p⋀~p)} (p⋀~p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.byLocalRule {p⋀~p} {{p,~p}}
  apply @LocalRule.Con {p⋀~p} (p) (~p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.sim; exact rfl

  have h₂ : Y = {~~(p⋀p)} := by
    simp_all only [Finset.singleton_inj, Formula.neg.injEq, Formula.And.injEq, true_and, true_or, h₁]
    simp at h₀ ; exact h₀
  subst h₂ ; clear h₀ h₁
  apply @LocalTableau.byLocalRule {~~(p⋀p)} {{p⋀p}}
  apply @LocalRule.neg {~~(p⋀p)} (p⋀p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.byLocalRule {p⋀p} {{p}}
  apply @LocalRule.Con {p⋀p} (p) (p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.sim; exact rfl


def LocTab4 : LocalTableau {p↣p} := by
  simp
  apply @LocalTableau.byLocalRule {~(p⋀~p)} {{~p}, {~~p}}
  apply @LocalRule.nCo {~(p⋀~p)} (p) (~p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀
  by_cases h₁ :Y = {~p}
  subst h₁
  apply @LocalTableau.sim ; exact rfl

  have h₂ : Y = {~~p} := by
    simp_all only [Finset.singleton_inj, Formula.neg.injEq, Formula.And.injEq, true_and, true_or, h₁]
    simp at h₀ ; exact h₀
  subst h₂ ; clear h₀ h₁
  apply @LocalTableau.byLocalRule {~~p} {{p}}
  apply @LocalRule.neg {~~p} (p) (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.sim ; exact rfl


def LocTab5 : LocalTableau {~p} := by
  apply LocalTableau.sim ; exact rfl

def LocTab6 : LocalTableau {~~p} := by
  apply @LocalTableau.byLocalRule {~~p} {{p}}
  apply @LocalRule.neg {~~p} p  (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply LocalTableau.sim ; exact rfl

def LocTab7 : LocalTableau {p ⋀ q} := by
  apply @LocalTableau.byLocalRule {p ⋀ q} {{p,q}}
  apply @LocalRule.Con {p⋀q} p q (Finset.mem_singleton.mpr rfl)
  intro Y h₀ ; simp at h₀ ; subst h₀
  apply @LocalTableau.sim ; exact rfl
