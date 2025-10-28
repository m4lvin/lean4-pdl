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
      ⟨[~~⊥], [], none, LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥) rfl, by simp⟩
      ?_
    · exact [([⊥], [], none)]
    · simp
    · -- build one child tableau
      intro c c_in
      simp at c_in
      subst c_in
      apply LocalTableau.byLocalRule
        ⟨[⊥], [], none, LocalRule.oneSidedL (OneSidedLocalRule.bot) rfl, by simp⟩
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
      ⟨[ ~~(p ⋀ (~p))], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.neg (p ⋀ (~p))) rfl), _⟩
      ?_
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in
    apply LocalTableau.byLocalRule
      ⟨[p ⋀ (~p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)) rfl, _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in -- unique child node
    apply LocalTableau.byLocalRule
      ⟨[p, ~p], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not p) rfl, _⟩
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
      ⟨[·p, ~(·p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not (·p)) rfl, _⟩
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
def subTabForEx2 :
    Tableau [([r⋀(~⌈a⌉p), ~ (r ⋀ (~⌈a⌉p⋀q))], [], none)] ([r, ~(⌈a⌉p), ⌈a⌉(p⋀q)], [], none) :=
  by
  have principal : (~(⌈a⌉p)) ∈ [r, ~(⌈a⌉p), ⌈a⌉(p⋀q)] := by simp
  apply Tableau.pdl (by simp [rep]; decide) (by simp [Sequent.basic, Sequent.closed])
    (@PdlRule.loadL _ [] _ _ _ _ principal (by simp [Formula.isBox]) rfl)
  simp
  apply Tableau.pdl (by simp [rep]; decide) (by simp [Sequent.basic, Sequent.closed])
    (.modL rfl rfl) -- Note: modL no longer needs to ask for basic.
  simp [projection]
  apply Tableau.loc
  · simp [rep]
    decide
  · simp [Sequent.basic, Sequent.closed]
  case lt =>
    apply LocalTableau.byLocalRule
      ⟨ [p⋀q], [], none, LocalRule.oneSidedL (OneSidedLocalRule.con p q) rfl, _⟩
    all_goals (try simp; try rfl)
    · intro c c_in; simp at c_in; subst c_in -- unique child node
      apply LocalTableau.byLocalRule
        ⟨ [p, (~p)], [], none, LocalRule.oneSidedL (OneSidedLocalRule.not p) rfl, _⟩
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
      ⟨[r ⋀ (~(⌈a⌉p))], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.con r (~(⌈a⌉p)))) rfl, _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in -- unique child node
    apply LocalTableau.byLocalRule
      ⟨[(~(r ⋀ (~(⌈a⌉(p ⋀ q)))))], [], none,
        (LocalRule.oneSidedL (OneSidedLocalRule.nCo r (~(⌈a⌉(p ⋀ q))))) rfl, _⟩
    all_goals (try simp; try rfl)
    intro c c_in; simp at *
    -- now branching!
    by_cases c = ([r, ~⌈a⌉p, ~ r], [], none) <;> simp_all
    case pos c_def =>
      subst c_def
      -- first branch, apply "not"
      apply LocalTableau.byLocalRule
        ⟨ [r, ~(r)], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.not r)) rfl, _ ⟩
      all_goals (try simp; try rfl)
      · intro c c_in; simp at *
      · decide
    case neg hyp =>
      subst c_in
      -- second branch, apply "neg" and then modal step!
      apply LocalTableau.byLocalRule
        ⟨ [~~(⌈a⌉( p ⋀q))], [], none
        , (LocalRule.oneSidedL (OneSidedLocalRule.neg (⌈a⌉(p⋀q)))) rfl, _ ⟩
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

/-- Example 4.7 involving a free repeat and thus open. -/
example : ¬ provable ((⌈∗a⌉~⌈a⌉p) ↣ p) :=
  by
  sorry

/-- Example 4.8 involving a loaded-path repeat but still open. -/
example : ¬ provable ((⌈a⌉⌈∗a⌉p) ↣ (⌈a⌉⌈∗a⌉q)) :=
  by
  sorry

-- Should this be with @[simp] in `LocalTableau.lean`?
lemma endNodesOf_cast_helper {h : X = Y} (ltX : LocalTableau X) :
    endNodesOf (h ▸ ltX) = endNodesOf ltX := by
  subst_eqs; simp

/-- Example 4.18 involving a loaded-path repeat -/
example : Tableau [] ([ ⌈∗a⌉q, ~ ⌈a⌉⌈∗(a ⋓ (?' p))⌉q ], [], none) :=
  by
  apply Tableau.loc
  · simp [rep]
  · simp [Sequent.basic, Sequent.closed]
  case lt =>
    -- (□)
    apply LocalTableau.byLocalRule
      ⟨_, _, _, (LocalRule.oneSidedL (OneSidedLocalRule.box (∗a) q (by decide))) rfl, by simp⟩
    all_goals (try simp; try rfl)
    intro Y Y_in
    simp [unfoldBox, allTP, testsOfProgram, Xset, F, P, a] at *
    subst Y_in
    apply LocalTableau.sim
    simp [Sequent.basic, Sequent.closed]
  · intro Y Y_in
    simp [unfoldBox, allTP, testsOfProgram, Xset, F, P, a] at Y_in
    subst Y_in
    have principal : (~⌈a⌉⌈∗(a)⋓(?'p)⌉q) ∈ [~⌈a⌉⌈∗(a)⋓(?'p)⌉q, q, ⌈a⌉⌈∗a⌉q] :=
      by simp
    -- (L+)
    apply Tableau.pdl (by simp [rep]; decide) (by simp [Sequent.basic, Sequent.closed])
      (PdlRule.loadL (δ := [a]) principal (by simp [Formula.isBox]) rfl)
    clear principal
    simp
    -- (M)
    apply Tableau.pdl (by simp [rep]; decide) (by simp [Sequent.basic, Sequent.closed])
      (PdlRule.modL rfl rfl)
    simp [projection]
    apply Tableau.loc
    · simp [rep]; decide
    · simp [Sequent.basic, Sequent.closed]
    case lt =>
      -- (□)
      apply LocalTableau.byLocalRule
        ⟨_, _, _, (LocalRule.oneSidedL (OneSidedLocalRule.box (∗a) q (by decide))) rfl, by simp⟩
      all_goals (try simp; try rfl)
      intro Y Y_in
      simp [unfoldBox, allTP, testsOfProgram, Xset, F, P, a] at *
      subst Y_in
      -- (◇)
      apply LocalTableau.byLocalRule
        ⟨_, _, _, (LocalRule.loadedL _ (LoadRule.dia'
        (by simp [Program.isAtomic] : ¬ (∗((·atA)⋓(?'p))).isAtomic))) rfl, by simp; rfl⟩
      all_goals (try simp; try rfl)
      intro Y Y_in
      by_cases Y = ([q, ⌈·atA⌉⌈∗·atA⌉q, ~q], [], none)
      -- branching!
      -- cases Y_in -- type mismatch when assigning motive, so work around that.
        <;> simp_all [unfoldDiamondLoaded', YsetLoad', H, splitLast]
      · subst_eqs
        apply LocalTableau.byLocalRule -- left branch: close with q and ~q
          ⟨ [q, ~(q)], [], none, (LocalRule.oneSidedL (OneSidedLocalRule.not q)) rfl, _ ⟩
        all_goals (try simp; try rfl)
        · intro _ _; simp_all
        · decide
      · clear Y_in
        apply LocalTableau.sim -- right branch: simple
        simp [Sequent.basic, Sequent.closed]
    case next =>
      intro Y Y_in
      have : Y = ([q, ⌈a⌉⌈∗a⌉q], [], some (Sum.inl (~'⌊⌊[a]⌋⌋⌊∗a⋓(?'p)⌋AnyFormula.normal q)))  := by
        simp only [List.empty_eq, List.map_nil, eq_mpr_eq_cast, endNodesOf, List.mem_flatten,
          List.mem_map, List.mem_attach, true_and, Subtype.exists, Function.comp_apply,
          Olf.change_old_none_none, ↓existsAndEq] at *
        rcases Y_in with ⟨a, ⟨Z, Z_in, def_a⟩, Y_in_l⟩
        subst def_a
        -- It seems annoying to deal with all the casting here.
        simp only [endNodesOf_cast_helper, endNodesOf, List.mem_flatten, List.mem_map,
          List.mem_attach, true_and, Subtype.exists, Function.comp_apply, Prod.exists,
          ↓existsAndEq] at Y_in_l
        rcases Y_in_l with ⟨a, ⟨Z, olf, Zolf_in, def_a⟩ , Y_in_l⟩
        subst def_a
        simp only [unfoldDiamondLoaded', YsetLoad', H, List.empty_eq, List.cons_union,
          List.nil_union, List.mem_cons, Prod.mk.injEq, List.ne_cons_self, List.cons_ne_self,
          and_self, List.not_mem_nil, or_self, not_false_eq_true, List.insert_of_not_mem,
          List.map_cons, ↓reduceIte, List.cons_append, List.nil_append, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_eq, reduceCtorEq,
          and_false, splitLast, loadMulti_cons, loadMulti_nil, or_false] at Zolf_in
        cases Zolf_in
        · aesop
        cases olf
        · simp_all
        · simp_all (decide := true)
          aesop
      clear Y_in
      subst this
      -- Note: goal here shows the history in which we now find a loaded-path repeat.
      apply Tableau.lrep
      unfold LoadedPathRepeat
      simp_all
      use 1 -- go back two pdl steps, one of which makes two local steps
      simp_all [Sequent.multisetEqTo, a]
      constructor
      · rfl
      · intro m m_lt
        cases m using Fin.cases
        · simp_all [Sequent.isLoaded]
        case succ m =>
          cases m using Fin.cases
          · simp_all [Sequent.isLoaded]
          case succ m =>
            simp_all
            have := Fin.one_lt_succ_succ m
            simp_all
            omega
