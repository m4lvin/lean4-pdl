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

theorem X_in_PathX {X : Finset Formula} : (path : Path X) →  (f ∈ X) → f ∈ (toFinset path) := by
  intro path f_in
  cases path
  case endNode => aesop
  case interNode => aesop

theorem PathSaturated : (path : Path X) → Saturated (toFinset path) := by
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

theorem PathConsistent : (path : Path X) → ⊥ ∉ (toFinset path) ∧ ∀ P, P ∈ (toFinset path) → ~P ∉ (toFinset path) := by
  intro path
  constructor
  · induction path
    case endNode X consistentX _ =>
      simp
      sorry
    case interNode => sorry
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

theorem ModelExistence : (X: Finset Formula) →  Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (W : WS), X ⊆ W :=
  by
  intro X consX
  have := consistentThenOpenTab consX
  rcases this with ⟨tX, open_tX⟩
  let WS : Finset (Finset Formula) := sorry
  let M : KripkeModel WS := sorry
  let pathX : Path X := sorry
  have h : (toFinset pathX) ∈ WS := by sorry
  use WS, ⟨M, sorry⟩
  use ⟨toFinset pathX, h⟩
  sorry

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    have ⟨WS, M, w, h⟩ := ModelExistence X X_is_consistent
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

-- Maximal paths in a local tableau, from root to end node, as sets of sets.
-- pathsOf (X with children B) := { X ∪ rest | c <- B, rest <- pathsOf c }
--def pathsOf {X} : LocalTableau X → Finset (Finset Formula)
--  | @byLocalRule _ B lr next => B.attach.biUnion
--      (λ ⟨Y,h⟩ => have : lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h
--                  (pathsOf (next Y h)).image (λ fs => fs ∪ X))
--  | sim _ => { X }


inductive RuleTag : Type
| None : RuleTag
| bot : RuleTag
| Not : RuleTag
| neg : RuleTag
| Con : RuleTag
| nCoL : RuleTag
| nCoR : RuleTag
deriving DecidableEq

open RuleTag

-- def Path := List (Finset Formula × Option (Σ X B, LocalRule X B))

def pathsOf_aux {X} : LocalTableau X  →  (List (List (Finset Formula × Option (Σ X B, LocalRule X B)))) := by
  intro tX
  cases tX
  case sim simpleX  =>
    exact ([ [(X, none)] ])

  case byLocalRule B next lr =>
    let mylr := lr
    cases lr
    case bot h₀ =>
      exact ([ [ (X, some ⟨X, ∅, mylr ⟩) ] ])

    case Not φ h₀ =>
      exact ([ [ (X, some ⟨X, ∅, mylr ⟩) ] ])

    case neg φ h₀ =>
      specialize next (X \ {~~φ} ∪ {φ})
      simp at next
      specialize next True.intro
      have : Finset.sum (insert φ (Finset.erase X (~~φ))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        have := localRulesDecreaseLength (LocalRule.neg h₀) (X \ {~~φ} ∪ {φ}) (Finset.mem_singleton.mpr rfl)
        simp_all [lengthOfSet, not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert]
      let IH := pathsOf_aux next
      exact (List.map (λ l => (X, some ⟨X, {X\ {~~φ} ∪ {φ}}, mylr⟩ ) :: l) IH )


    case Con α β h₀ =>
      specialize next (X \ {α⋀β} ∪ {α,β})
      simp at next
      specialize next True.intro
      have : Finset.sum (insert α (insert β (Finset.erase X (α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula  := by
        have := localRulesDecreaseLength (LocalRule.Con h₀) (X \ {α⋀β} ∪ {α,β}) (Finset.mem_singleton.mpr rfl)
        simp_all [lengthOfSet, not_true_eq_false, sdiff_singleton_is_erase, Finset.mem_singleton]
      let IH := pathsOf_aux next
      exact (List.map (λ l => (X, some ⟨X, {X \ {α⋀β} ∪ {α,β}}, mylr⟩) :: l) (IH) )

    case nCo α β h₀ =>
      let next2 := next
      specialize next (X \ {~(α⋀β)} ∪ {~α})
      specialize next2 (X \ {~(α⋀β)} ∪ {~β})
      simp at next next2
      specialize next True.intro
      specialize next2 True.intro
      have : Finset.sum (insert (~α) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        have := localRulesDecreaseLength (LocalRule.nCo h₀) (X \ {~(α⋀β)} ∪ {~α})
        simp_all [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
      have : Finset.sum (insert (~β) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        have := localRulesDecreaseLength (LocalRule.nCo h₀) (X \ {~(α⋀β)} ∪ {~β})
        simp_all [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
      let IH := List.map ((λ l => (X, some ⟨X, {X \ {~(α⋀β)} ∪ {~α}, X \ {~(α⋀β)} ∪ {~β}}, mylr⟩) :: l)) (pathsOf_aux next)
      let IH2 := List.map ((λ l => (X, some ⟨X, {X \ {~(α⋀β)} ∪ {~α}, X \ {~(α⋀β)} ∪ {~β}}, mylr⟩) :: l)) (pathsOf_aux next2)
      exact IH ++ IH2
termination_by
  pathsOf_aux X tX => lengthOfSet X






--eraseDups
--List.toFinset l

#check Eq

instance  : DecidableEq (List (Finset Formula × Option (Σ X B, LocalRule X B))) := by
  have : DecidableEq (Finset Formula × Option (Σ X B, LocalRule X B)) := by
    have : DecidableEq (Finset Formula) := Finset.decidableEq
    have : DecidableEq (Option (Σ X B, LocalRule X B)) := by
      have : DecidableEq (Σ X B, LocalRule X B) := by
        intros a b
        rcases a with ⟨a0, a1⟩
        rcases a1 with ⟨a1, a2⟩
        rcases b with ⟨b0, b1⟩
        rcases b1 with ⟨b1, b2⟩
        simp
        have : Decidable (a0 = b0) := by exact this a0 b0
        have : Decidable (HEq ({fst := a1, snd := a2} : (a1 : Finset (Finset Formula)) × (LocalRule a0 a1)  ) ({fst := b1, snd := b2} : (b1 : Finset (Finset Formula)) × (LocalRule b0 b1) )) := by
          have : Decidable (((a1 : Finset (Finset Formula)) × (LocalRule a0 a1))  =   ((b1 : Finset (Finset Formula)) × (LocalRule b0 b1) )) := by
            sorry
          cases this ; apply Decidable.isFalse ; intro h₁ ; have h2 : (((a1 : Finset (Finset Formula)) × (LocalRule a0 a1))  =   ((b1 : Finset (Finset Formula)) × (LocalRule b0 b1) )) :=  type_eq_of_heq h₁ ; simp_all only [not_true_eq_false]
          case isTrue this1 =>
                                    -- won't let me do cases on 'this1'
            apply Decidable.isTrue ; sorry
        exact And.decidable
      exact instDecidableEqOption
    exact instDecidableEqProd
  exact List.hasDecEq


def pathsOf {X} : LocalTableau X  →  Finset (List (Finset Formula × Option (Σ X B, LocalRule X B))) := λ tX => (List.toFinset (pathsOf_aux tX))

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
