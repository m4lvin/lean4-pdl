-- TABLEAU-EXAMPLES

import Mathlib.Data.Finset.Basic

import Bml.Tableau

theorem noBot : Provable (~⊥) := by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {~~⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥))
    · simp
    use applyLocalRule (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥)) ({~~⊥}, ∅)
    rfl
    · -- build one child tableau
      intro c c_in
      simp  at c_in
      subst c_in
      let ltBot : LocalTableau ({⊥},∅) := by
        apply LocalTableau.fromRule
        apply LocalRuleApp.mk _ {⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.bot))
        · simp
        use []
        simp
        aesop
      exact ltBot
  case a.next =>
    -- show that endNodesOf is empty
    intro Y Y_in
    simp [endNodesOf] at *
    sorry -- since Lean v4.9.0-rc2


theorem noContradiction : Provable (~(p⋀~p)) :=
  by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {~~(p⋀~p)} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg (p⋀~p)))
    all_goals (try simp; try rfl) -- easier than guessing "use applyLocalRule ..."
    · intro c c_in
      simp at c_in
      subst c_in -- unique child node
      let ltB : LocalTableau ({p⋀~p},∅) := by
        apply LocalTableau.fromRule
        apply LocalRuleApp.mk _ {p⋀~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)))
        · simp
        all_goals (try rfl)
        intro c c_in; simp at c_in; subst c_in -- unique child node
        let ltC : LocalTableau ({p, ~p}, ∅) := by
          apply LocalTableau.fromRule
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
    sorry -- since Lean v4.9.0-rc2

-- preparing example 2
def subTabForEx2 : ClosedTableau ({·'r', ~(□p), □(p⋀q)}, {}) :=
  by
  have : Simple ({·'r', ~(□p), □(p⋀q)}, {}) := by simp [SimpleSet, Simple]
  apply ClosedTableau.atmL (by simp : ~(□p) ∈ _) this
  simp [diamondProjectTNode, projection]
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {p⋀q} {} (LocalRule.oneSidedL (OneSidedLocalRule.con p q))
    all_goals (try simp; try rfl)
    · intro c c_in; simp at c_in; subst c_in -- unique child node
      let ltB : LocalTableau ({p, q, ~p}, ∅) := by
        apply LocalTableau.fromRule
        apply LocalRuleApp.mk _ {p, ~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.not p))
        · simp
          intro f
          aesop
        use [] -- claim there are no children
        simp
        aesop
      exact ltB
  case next =>
    intro Y Y_in
    simp [endNodesOf] at *
    sorry -- since Lean v4.9.0-rc2


-- needed to ensure simple-ness in next example.
notation "r" => (·'r')

-- Example 2
example : ClosedTableau ({r⋀~(□p), r↣□(p⋀q)}, {}) :=
  by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {r⋀~(□p)} {} (LocalRule.oneSidedL (OneSidedLocalRule.con r (~(□p))))
    all_goals (try simp; try rfl)
    · intro c c_in; simp at c_in; subst c_in -- unique child node
      let ltB : LocalTableau ({r, ~(□p), ~(r⋀~(□(p⋀q)))}, ∅) := by
        apply LocalTableau.fromRule
        apply LocalRuleApp.mk _ {~(r⋀~(□(p⋀q)))} {} (LocalRule.oneSidedL (OneSidedLocalRule.ncon r (~(□(p⋀q)))))
        · simp
        · exact [ ({r, ~(□p), ~(r)},{}), ({r, ~(□p), ~~(□(p⋀q))},{}) ]
        · rfl
        · intro c c_in
          simp at c_in
          -- now branching!
          if c = ({r, ~(□p), ~(r)},{}) then _ else _
          case pos c_def =>
            subst c_def
            -- first branch, apply "not"
            apply LocalTableau.fromRule
            apply LocalRuleApp.mk _ {r, ~(r)} {} (LocalRule.oneSidedL (OneSidedLocalRule.not r))
            · simp
            · exact [] -- claim there are no children
            · rfl
            · aesop
          case neg hyp =>
            have c_def : c = ({r, ~(□p), ~~(□(p⋀q))},{}) := by aesop
            subst c_def
            -- second branch, apply "neg" and then modal step!
            apply LocalTableau.fromRule
            apply LocalRuleApp.mk _ {~~(□(p⋀q))} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg (□(p⋀q))))
            all_goals (try simp; try rfl)
            intro c c_in; simp at c_in; subst c_in -- unique child node
            -- ending local tableau with a simple node:
            apply LocalTableau.fromSimple
            simp [SimpleSet, Simple]
            aesop
      exact ltB
  case next =>
      intro Y Y_in
      simp (config := {decide := true}) at *
      sorry -- since Lean v4.9.0-rc2
      /-
      · subst Y_in
        -- rewrite the Finset in the goal to that of subTabForEx2
        have : insert (□(p⋀q)) (Finset.erase {·Char.ofNat 114, ~(□p), ~~(□(p⋀q))} (~~(□(p⋀q)))) = {·'r', ~(□p), □(p⋀q)} := by decide
        rw [this]
        exact subTabForEx2
      -/
