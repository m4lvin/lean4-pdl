-- TABLEAU-EXAMPLES

import Mathlib.Data.Finset.Basic

import Bml.Tableau

theorem noBot : Provable (~⊥) := by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.lt =>
    apply LocalTableau.fromRule
    · apply LocalRuleApp.mk _ {~~⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥))
      · simp
      · use applyLocalRule (LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥)) ({~~⊥}, ∅)
      · rfl
    · -- build one child tableau
      intro c c_in
      simp only [applyLocalRule, instBotFormula, sdiff_self, Finset.bot_eq_empty,
        Finset.empty_union, Prod.mk.eta, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at c_in
      subst c_in
      let ltBot : LocalTableau ({⊥},∅) := by
        apply LocalTableau.fromRule
        · apply LocalRuleApp.mk _ {⊥} {} (LocalRule.oneSidedL (OneSidedLocalRule.bot))
          · simp
          · use []
          · simp
        aesop
      exact ltBot
  case a.next =>
    -- show that endNodesOf is empty
    intro Y Y_in
    exfalso
    aesop

theorem noContradiction : Provable (~(p⋀~p)) :=
  by
  apply Provable.byTableau
  apply ClosedTableau.loc
  case a.lt =>
    apply LocalTableau.fromRule
    · apply LocalRuleApp.mk _ {~~(p⋀~p)} {} (LocalRule.oneSidedL (OneSidedLocalRule.neg (p⋀~p)))
      all_goals (try simp; try rfl) -- easier than guessing "use applyLocalRule ..."
    · intro c c_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at c_in
      subst c_in -- unique child node
      let ltB : LocalTableau ({p⋀~p},∅) := by
        apply LocalTableau.fromRule
        · apply LocalRuleApp.mk _ {p⋀~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)))
          · simp
          all_goals (try rfl)
        intro c c_in; simp only [applyLocalRule, sdiff_self, Finset.bot_eq_empty,
          Finset.empty_union, Prod.mk.eta, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at c_in; subst c_in -- unique child node
        let ltC : LocalTableau ({p, ~p}, ∅) := by
          apply LocalTableau.fromRule
          · apply LocalRuleApp.mk _ {p, ~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.not p))
            · simp
            · use [] -- claim that there are no more children
            · simp
          aesop
        exact ltC
      exact ltB
  case a.next =>
    -- show that endNodesOf is empty
    intro Y Y_in
    exfalso
    aesop

-- preparing example 2
def subTabForEx2 : ClosedTableau ({·'r', ~(□p), □(p⋀q)}, {}) :=
  by
  have : Simple ({·'r', ~(□p), □(p⋀q)}, {}) := by simp [SimpleSet, Simple]
  apply ClosedTableau.atmL (by simp : ~(□p) ∈ _) this
  simp only [diamondProjectTNode, projection, ↓Char.isValue, formProjection, Finset.biUnion_insert,
    Option.toFinset_none, Finset.singleton_biUnion, Option.toFinset_some, Finset.union_singleton,
    insert_empty_eq, Finset.biUnion_empty]
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    · apply LocalRuleApp.mk _ {p⋀q} {} (LocalRule.oneSidedL (OneSidedLocalRule.con p q))
      all_goals (try simp; try rfl)
    · intro c c_in; simp only [List.mem_cons, List.not_mem_nil, or_false] at c_in
      subst c_in -- unique child node
      let ltB : LocalTableau ({~p, p, q}, ∅) := by
        apply LocalTableau.fromRule
        · apply LocalRuleApp.mk _ {p, ~p} {} (LocalRule.oneSidedL (OneSidedLocalRule.not p))
          · simp only [subset_refl, and_true]
            intro f
            aesop
          · use [] -- claim there are no children
          · simp
        aesop
      exact ltB
  case next =>
    intro Y Y_in
    exfalso
    aesop

-- needed to ensure simple-ness in next example.
notation "r" => (·'r')

-- Example 2
example : ClosedTableau ({r⋀~(□p), r↣□(p⋀q)}, {}) :=
  by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    · apply LocalRuleApp.mk _ {r⋀~(□p)} {} (LocalRule.oneSidedL (OneSidedLocalRule.con r (~(□p))))
      all_goals (try simp; try rfl)
    · intro c c_in; simp only [↓Char.isValue, List.mem_cons, List.not_mem_nil, or_false] at c_in
      subst c_in -- unique child node
      let ltB : LocalTableau ({~(r⋀~(□(p⋀q))), r, ~(□p)}, ∅) := by
        apply LocalTableau.fromRule
        · apply LocalRuleApp.mk _ {~(r⋀~(□(p⋀q)))} {}
            (LocalRule.oneSidedL (OneSidedLocalRule.ncon r (~(□(p⋀q)))))
          · simp
          · exact [ ({r, ~(□p), ~(r)},{}), ({r, ~(□p), ~~(□(p⋀q))},{}) ]
          · rfl
        · intro c c_in
          simp only [↓Char.isValue, List.mem_cons, List.not_mem_nil, or_false] at c_in
          -- now branching!
          if c = ({r, ~(□p), ~(r)},{}) then _ else _
          case pos c_def =>
            subst c_def
            -- first branch, apply "not"
            apply LocalTableau.fromRule
            · apply LocalRuleApp.mk _ {r, ~(r)} {} (LocalRule.oneSidedL (OneSidedLocalRule.not r))
              · simp
              · exact [] -- claim there are no children
              · rfl
            · aesop
          case neg hyp =>
            have c_def : c = ({r, ~(□p), ~~(□(p⋀q))},{}) := by aesop
            subst c_def
            -- second branch, apply "neg" and then modal step!
            apply LocalTableau.fromRule
            · apply LocalRuleApp.mk _ {~~(□(p⋀q))} {}
                (LocalRule.oneSidedL (OneSidedLocalRule.neg (□(p⋀q))))
              all_goals (try simp; try rfl)
            intro c c_in; simp only [↓Char.isValue, List.mem_cons, List.not_mem_nil,
              or_false] at c_in; subst c_in -- unique child node
            -- ending local tableau with a simple node:
            apply LocalTableau.fromSimple
            simp [SimpleSet, Simple]
            aesop
      exact ltB
  case next =>
      intro Y Y_in
      simp (config := { decide := true }) only [↓Char.isValue, impl.eq_1, List.map_cons,
        List.map_nil, List.empty_eq, lrEndNodes, List.attach_cons, List.attach_nil, ↓reduceDIte,
        List.flatten_nil, endNodesOfSimple, List.flatten_cons, List.append_nil, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at *
      have : Y = ({·'r', ~(□p), □(p⋀q)}, {}) := by
        subst Y_in
        decide
      subst this
      exact subTabForEx2
