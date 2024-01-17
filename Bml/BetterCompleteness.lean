import Mathlib.Data.Finset.Basic

import Bml.Syntax
import Bml.Semantics
import Bml.Modelgraphs
import Bml.Tableau
import Bml.Soundness

open LocalTableau
open HasLength
open HasSat
open LocalRule

inductive Path: Finset Formula →  Type
  | endNode {X} (consistentX : Consistent X) (simpleX : Simple X): Path X
  | interNode {X Y} (_ : LocalRule X B) (Y_in : Y ∈ B) (tail : Path Y): Path X
open Path

@[simp]
def toFinset: Path X → Finset Formula
  | endNode _ _ => X
  | (interNode _ _ tail) => X ∪ (toFinset tail)

theorem X_in_PathX {X : Finset Formula} : (path : Path X) → X ⊆ (toFinset path) := by
  intro path f
  cases path
  case endNode => aesop
  case interNode => aesop

def pathsOf {X} : LocalTableau X  →  List (Path X) := by
  intro tX
  cases tX
  case sim simpleX  => sorry

  case byLocalRule B next lr =>
    let mylr := lr
    cases lr
    case bot h₀ =>
      exact []

    case Not φ h₀ =>
      exact []

    case neg φ h₀ =>
      specialize next (X \ {~~φ} ∪ {φ})
      simp only [Finset.mem_singleton] at next
      specialize next True.intro
      have : Finset.sum (insert φ (Finset.erase X (~~φ))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.neg h₀)
        simp
      exact List.map (λ l => interNode (neg h₀) (by simp) l) (pathsOf next)


    case Con α β h₀ =>
      specialize next (X \ {α⋀β} ∪ {α,β})
      simp at next
      specialize next True.intro
      have : Finset.sum (insert α (insert β (Finset.erase X (α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula  := by
        apply localRulesDecreaseLength (LocalRule.Con h₀)
        simp
      let IH := pathsOf next
      exact List.map (interNode (Con h₀) (by simp)) IH

    case nCo α β h₀ =>
      have next1 := next (X \ {~(α⋀β)} ∪ {~α})
      have next2 := next (X \ {~(α⋀β)} ∪ {~β})
      simp at next1 next2
      specialize next1 True.intro
      specialize next2 True.intro
      have : Finset.sum (insert (~α) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.nCo h₀)
        simp
      have : Finset.sum (insert (~β) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.nCo h₀)
        simp
      let IH1 := List.map (interNode (nCo h₀) (by simp)) (pathsOf next1)
      let IH2 := List.map (interNode (nCo h₀) (by simp)) (pathsOf next2)
      exact IH1 ++ IH2
termination_by pathsOf X tX => lengthOf X

theorem pathSaturated : (path : Path X) → Saturated (toFinset path) := by
  intro path
  intro P Q
  induction path
  case endNode X _ simpleX =>
    simp
    unfold Simple at simpleX
    simp at simpleX
    constructor
    · specialize simpleX (~~P)
      aesop
    · constructor
      · specialize simpleX (P ⋀ Q)
        aesop
      · specialize simpleX (~(P ⋀ Q))
        aesop
  case interNode B X Y locRule Y_in tail IH =>
    simp
    rcases IH with ⟨IH1, ⟨IH2, IH3⟩⟩
    constructor
    -- ~~P ∈ U → P ∈ U
    · intro nnP_in
      apply Or.inr
      cases nnP_in
      · case inl nnP_in_X =>
        have h : P ∈ Y ∨ ~~P ∈ Y := by sorry -- first refactor tableau
        cases h
        · case inl P_in_Y => exact (X_in_PathX tail P_in_Y)
        · case inr nnP_in_Y => exact (IH1 (X_in_PathX tail nnP_in_Y))
      · case inr nnP_in_tail => aesop
    · constructor
      · sorry
      · sorry

theorem consistentThenOpenTab : Consistent X → ∃ (t : Tableau X), isOpen t :=
  by
  have ⟨tX⟩ := existsTableauFor X
  -- should be easy now
  contrapose
  simp[not_exists, Consistent, Inconsistent]
  intro h
  specialize h tX
  refine Nonempty.intro ?val
  have : isClosed tX := by
    have h2 : ¬ isOpen tX ↔ ¬ ¬ isClosed tX := Iff.symm (Iff.not (Iff.symm open_iff_notClosed))
    simp_all only [not_not, not_true_eq_false, not_false_eq_true, iff_true]
  exact (isClosed_then_ClosedTab this)

theorem consistentImplies : Consistent X → ⊥ ∉ X ∧ ∀ P, P ∈ X → ~P ∉ X := by
  intro consX
  unfold Consistent Inconsistent at consX
  simp at consX
  constructor
  · by_contra bot_in_X
    let tab := byLocalRule (bot bot_in_X) (by aesop)
    have closedTab := ClosedTableau.loc tab (by aesop)
    exact IsEmpty.false closedTab
  · intro P
    by_contra h
    simp at h
    let tab := byLocalRule (Not h) (by aesop)
    have closedTab := ClosedTableau.loc tab (by aesop)
    exact IsEmpty.false closedTab

theorem pathConsistent : (path : Path X) → ⊥ ∉ (toFinset path) ∧ ∀ P, P ∈ (toFinset path) → ~P ∉ (toFinset path) := by
  intro path
  constructor
  · induction path
    case endNode X consistentX _ =>
      simp
      sorry
    case interNode => sorry
  · sorry

theorem modelExistence : (X: Finset Formula) →  Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (W : WS), X ⊆ W :=
  by
  intro X consX
  have := consistentThenOpenTab consX
  rcases this with ⟨tX, open_tX⟩
  let paths : List (Σ X, Path X) := sorry
  let WSlist : List (Finset Formula) := List.map (λ ⟨X, path⟩ => toFinset path) paths
  let WS := WSlist.toFinset
  let M : KripkeModel WS := sorry
  let pathX : Path X := sorry
  use WS, ⟨M, ?_⟩, ⟨toFinset pathX, ?_⟩
  · exact X_in_PathX pathX
  · constructor
    · intro ⟨W, W_in⟩
      simp at W_in
      choose W' pathW' h using W_in
      rcases h with ⟨_, W_eq⟩
      subst W_eq
      exact ⟨pathSaturated pathW', pathConsistent pathW'⟩
    · constructor
      · intro ⟨W, W_in⟩ p
        constructor
        · intro h
          simp at h
          sorry
        · sorry
      · constructor
        · sorry
        · sorry
  sorry

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    have ⟨WS, M, w, h⟩ := modelExistence X X_is_consistent
    use WS, M.val, w
    have := truthLemma M w
    aesop
  -- use Theorem 2:
  · exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent {φ} ↔ Satisfiable φ :=
  by
  intro f
  have := completeness {f}
  simp only [singletonSat_iff_sat] at *
  tauto

-- TODO Clean up

-- 0) Define last_node(path) := ite(path.length = 0)(∅)(path[path.length-1].fst : Finset Formula)
-- 1) Define AllPaths(X)    :=
        -- | simple X   :=
              --(X, sim)
              --YoN:   ⊥ in X?
              --YoN:   α, ~α in X?

        -- | X not simple :=
              -- Then there is a Local Rule st X R B.
              -- Go through all cases for X


-- 2) Define AllSubPaths(X) := ⋃{AllPaths(last_node path) : path ∈ AllPaths(X)}  ∪  ⋃{AllPaths(proj (last_node path); ~α) : path ∈ AllPaths(X) ∧ ~□α ∈ (last_node path) }
-- 3) Define path_to_node(path)  :=  ⋃{entry.fst : entry in path.toFinset}
-- 4) Define g      :=  {path_to_node(path) : path ∈ (AllPaths(X) ∪ AllSubPaths(X))  ∧  (last_entry path) simple ∧ ((last_entry path) simple  =>  (last_entry path) consistent)}



--Ennumerate all LocalTableaus for a given X.

-- | (simple rule) X is simple Y or N:
--      N:  ∅
--      Y:  { LocTab.sim }


--| (bot rule) ⊥ ∈ X :

--


--     N:  ∅
--     Y:  {  (LocTab.byLocRule LocRule.bot)   }


--| (Not rule)
--   { (LocTab.byLocRule LocRule.Not α)  :  α ∈ X ∧ ~α ∈ X}


-- |  (neg rule)
--    ⋃_[~~α ∈ X]     { (LocTab.byLocRule  (LocRule.neg)  (λ S ∈ { X \ {~~α}  ∪ {α} }  =>  LocTab) )  :  LocTab ∈ Ennumerate(X \ {~~α}  ∪ {α})}




-- (sim)
  -- X is simple?:
  --  Y: Add    LocTab.sim to our ennumeration and keep ennumerating
  --  N:                                           Keep ennumerating

-- (bot)
  -- ⊥ in X?:
  -- Y:  Add      LocTab.byLocRule LocRule.bot   to our ennumeration and keep ennumerating
  -- N:                                                    Keep ennumerating

-- (Not)
  -- For all α in X, st ~α in X:
  --      add LocTab.byLocRule (LocRule.Not α)  to our ennumeration and keep ennumerating

-- (neg)
  -- For all ~~α in X:
  --      recursively compute (X \ {~~α} ∪ {α}) as "LocTab_α"
  -- For all ~~α in X, for every LocTab in LocTab_α:
  --        add LocTab.byLocalRule (LocRule.neg α) LocTab  to our ennumeration and keep ennumerating

-- (Con)
  -- For all α⋀β in X:
  --      recursively compute (X \ {α⋀β} ∪ {α,β}) as "LocTab_r"
  -- For all α⋀β in X, for every LocTab in LocTab_r:
      -- add LocTab.byLocalRule (LocalRule.Con α⋀β) LocTab to our ennumeration and keep ennumerating

-- (nCo)
  -- For all ~(α⋀β) in X:
  --       recurisvely compute (X \ {~(α⋀β)} ∪ {~α}) as "LocTab_α"
  --       recurisvely compute (X \ {~(α⋀β)} ∪ {~β}) as "LocTab_β"
  -- For all ~(α⋀β) in X, for every L1 in LocTab_α, for every L2 in LocTab_β:
      -- add LocTab.byLocalRule (LocalRule.nCo ~(α⋀β) ~α) (L1, L2) to our ennumeration and keep ennumerating


instance : DecidableEq (LocalTableau X) := by sorry

def EnnumerateLocTab : (X : Finset Formula) → Finset (LocalTableau X) := by
  intro X
  -- for each rule construct all tableaux that arrise when appling that rule first
  let sim_tabs : Finset (LocalTableau X) :=
    if h : Simple X = true
    then {sim h}
    else ∅
  let bot_tabs : Finset (LocalTableau X) := by
    if h : ⊥ ∈ X
    then exact {@LocalTableau.byLocalRule X ∅ (@LocalRule.bot X h) (by aesop)}
    else exact ∅
  let Not_tabs : Finset (LocalTableau X) := by
    let S := X.filter (λ α => α ∈ X ∧ ~α ∈ X)
    let t : S → Finset (LocalTableau X)  := by
      intro ⟨α, α_in_S⟩
      have h : α ∈ X ∧ ~α ∈ X := by simp_all
      exact {@LocalTableau.byLocalRule X ∅ (LocalRule.Not h) (by aesop)}
    exact S.attach.biUnion t
  let neg_tabs : Finset (LocalTableau X) := by
    let S : Finset Formula := sorry -- {α : Formula | ~~α ∈ X}
    let t : S → Finset (LocalTableau X)  := by
      intro ⟨α, α_in_S⟩
      have h : ~~α ∈ X := sorry
      let f : { x // x ∈ EnnumerateLocTab (X \ {~~α} ∪ {α}) } → LocalTableau X := by
        intro ⟨locTabY, locTabY_in⟩
        refine @LocalTableau.byLocalRule X {X \ {~~α} ∪ {α}} (@LocalRule.neg X α h) ?_
        intro Y Y_in
        simp only [Finset.mem_singleton] at Y_in
        subst Y_in
        exact locTabY
      exact (EnnumerateLocTab (X \ {~~α} ∪ {α})).attach.map ⟨f, sorry⟩
    exact S.attach.biUnion t
  let Con_tabs : Finset (LocalTableau X) := sorry
  let nCo_tabs : Finset (LocalTableau X) := sorry
  exact sim_tabs ∪ bot_tabs ∪ Not_tabs ∪ neg_tabs ∪ Con_tabs ∪ nCo_tabs
termination_by
  EnnumerateLocTab X => lengthOf X
decreasing_by sorry

def SimLocTab : Finset Formula →  Finset (Σ Y, LocalTableau Y) := by
  intro X
  cases h : Simple X
  exact ∅
  exact { ⟨X, LocalTableau.sim h⟩ }


def botLocTab : Finset Formula → Finset (Σ Y, LocalTableau Y) := by
  intro X
  by_cases h : ⊥ ∈ X
  swap
  exact ∅
  have next : ∀ Y ∈ ∅, LocalTableau Y := by
    intro Y h₀;
    let h₁ : False := (Set.mem_empty_iff_false Y).mp h₀
    exact h₁.elim

  --exact {⟨ X, (@LocalTableau.byLocalRule X ∅ (@LocalRule.bot X h) next)⟩}
  sorry

def NotLocTab : Finset Formula → Finset (Σ Y, LocalTableau Y) := by
  intro X
  let S :=  Finset.filter (λ α => α ∈ X ∧ ~α ∈ X) (X)
  let S_to_LocTab {α} : α ∈ S → (Σ Y, LocalTableau Y)  := by
    intro h₀
    have h₁ : α ∈ X ∧ ~α ∈ X := by
      simp_all only [true_and, Finset.mem_filter, and_self_left, and_self]
    exact ⟨ X, (@LocalTableau.byLocalRule X ∅ (LocalRule.Not h₁)) sorry⟩
  exact ({ S_to_LocTab α : α ∈ S })




-- M0 (tX) :=


--     |  simple X              :=    {tX}  ∪        ⋃{ LocalTab({proj(X) ; ~α})  :  ~□α ∈ X  }

--     |  LocalRule X B lr next :=           Filter  [⋃{ M0(next Y) : Y ∈ B }]   [λ tZ,  tZ has a consistent endNode]
