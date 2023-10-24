-- TABLEAU-EXAMPLES
import Syntax
import Tableau

#align_import tableauexamples

theorem noBot : Provable (~⊥) := by
  apply Provable.byTableau
  apply ClosedTableau.loc
  swap
  · apply LocalTableau.byLocalRule (LocalRule.neg (finset.mem_singleton.mpr (refl (~~⊥))))
    intro β inB
    rw [Finset.sdiff_self] at inB 
    rw [Finset.empty_union] at inB 
    rw [Finset.mem_singleton] at inB 
    rw [inB]
    apply LocalTableau.byLocalRule (LocalRule.bot (finset.mem_singleton.mpr (refl ⊥)))
    intro Y YinEmpty
    cases YinEmpty
  · -- show that endNodesOf is empty
    intro Y
    intro YisEndNode
    unfold endNodesOf at *
    simp at *
    exfalso
    rcases YisEndNode with ⟨a, h, hyp⟩
    subst h
    simp at *
    cases hyp
#align noBot noBot

def emptyTableau : ∀ β : Finset Formula, β ∈ ∅ → LocalTableau β :=
  by
  intro beta b_in_empty
  exact absurd b_in_empty (Finset.not_mem_empty beta)
#align emptyTableau emptyTableau

-- an example:
theorem noContradiction : Provable (~(p⋏~p)) :=
  by
  apply Provable.byTableau
  apply ClosedTableau.loc
  swap
  · apply LocalTableau.byLocalRule
    -- neg:
    apply LocalRule.neg
    simp
    intro β β_prop
    simp at β_prop 
    subst β_prop
    -- con:
    apply LocalTableau.byLocalRule
    apply LocalRule.con
    simp
    constructor
    rfl
    rfl
    intro β2 β2_prop
    simp at β2_prop 
    subst β2_prop
    -- closed:
    apply LocalTableau.byLocalRule (@LocalRule.not _ p _) emptyTableau
    exact by decide
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
    finish
#align noContradiction noContradiction

-- preparing example 2
def subTabForEx2 : ClosedTableau {r, ~(□p), □(p⋏q)} :=
  by
  apply @ClosedTableau.atm {r, ~(□p), □(p⋏q)} p (by simp)
  -- show that this set is simple:
  · unfold Simple; simp at *; tauto
  apply ClosedTableau.loc
  rotate_left
  -- con:
  apply LocalTableau.byLocalRule (@LocalRule.con {p⋏q, ~p} p q (by simp))
  intro child childDef
  rw [Finset.mem_singleton] at childDef 
  -- not:
  apply LocalTableau.byLocalRule (@LocalRule.not _ p _) emptyTableau
  · subst childDef; exact by decide
  · -- show that endNodesOf is empty
    intro Y
    intro YisEndNode
    simp at *
    exfalso
    assumption
#align subTabForEx2 subTabForEx2

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic dedup -/
-- Example 2
example : ClosedTableau {r⋏~(□p), r↣□(p⋏q)} :=
  by
  apply ClosedTableau.loc
  rotate_left
  · -- con
    apply LocalTableau.byLocalRule
    apply LocalRule.con
    simp only [impl, Finset.mem_insert, Finset.mem_singleton, or_false_iff]
    constructor
    rfl
    rfl
    intro branch branch_def
    rw [Finset.mem_singleton] at branch_def 
    rw [Finset.union_insert] at branch_def 
    -- nCo
    apply LocalTableau.byLocalRule
    apply @LocalRule.nCo _ r (~(□(p⋏q)))
    · rw [branch_def]; simp
    intro b b_in
    simp only [Finset.mem_insert, Finset.mem_singleton] at b_in 
    refine' if h1 : b = branch \ {~(r⋏~(□(p⋏q)))} ∪ {~r} then _ else _
    · -- right branch
      -- not:
      apply LocalTableau.byLocalRule (@LocalRule.not _ r _) emptyTableau
      finish
    · --left branch
      have h2 : b = branch \ {~(r⋏~(□(p⋏q)))} ∪ {~~(□(p⋏q))} := by tauto
      -- neg:
      apply LocalTableau.byLocalRule (@LocalRule.neg _ (□(p⋏q)) _)
      rotate_left; · rw [h2]; simp
      intro child childDef
      -- ending local tableau with a simple node:
      apply LocalTableau.sim
      rw [Finset.mem_singleton] at childDef 
      rw [childDef]
      unfold Simple; simp at *; constructor; unfold SimpleForm
      intro f f_notDef1 f_in_branch
      cases b_in
      tauto
      rw [b_in] at f_in_branch 
      simp at f_in_branch 
      cases f_in_branch
      tauto
      rw [branch_def] at f_in_branch 
      cases' f_in_branch with l r; simp at r 
      cases r
      · subst r; unfold r
      cases r
      · subst r; unfold SimpleForm
      · exfalso; tauto
  · -- tableau for the simple end nodes:
    rw [conEndNodes]
    rw [nCoEndNodes]
    intro Y Yin
    simp at *
    split_ifs at *
    · -- not-R branch
      exfalso
      -- show that there are no endnodes!
      simp at Yin 
      exact Yin
    · -- notnotbranch
      run_tac
        dedup
      have Yis : Y = {r, ~(□p), □(p⋏q)} := by
        simp at Yin 
        subst Yin
        ext1
        constructor <;> · intro hyp; finish
      subst Yis
      exact subTabForEx2

