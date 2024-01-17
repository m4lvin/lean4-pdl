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

@[simp]
theorem X_in_PathX {X : Finset Formula} (path : Path X) : X ⊆ (toFinset path) := by
  intro f
  cases path
  case endNode => aesop
  case interNode => aesop

def pathsOf {X} (tX : LocalTableau X) :  List (Path X) := by
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

theorem pathSaturated (path : Path X): Saturated (toFinset path) := by
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

theorem pathConsistent (path : Path X): ⊥ ∉ (toFinset path) ∧ ∀ P, P ∈ (toFinset path) → ~P ∉ (toFinset path) := by
  induction path
  case endNode X consistentX simpleX =>
      unfold Consistent Inconsistent at consistentX
      simp at consistentX
      constructor
      · by_contra h
        simp at h
        let tab := byLocalRule (bot h) (by aesop)
        have closedTab := ClosedTableau.loc tab (by aesop)
        exact IsEmpty.false closedTab
      · simp
        intro f f_in_X
        by_contra nf_in_X
        let tab := byLocalRule (Not ⟨f_in_X, nf_in_X⟩) (by aesop)
        have closedTab := ClosedTableau.loc tab (by aesop)
        exact IsEmpty.false closedTab
  case interNode B X Y locRule Y_in pathY IH =>
    simp
    constructor
    · by_contra h
      rcases h
      case inl h => sorry
      case inr h => aesop
    · intro f f_in
      by_contra h
      sorry

theorem modelExistence (X: Finset Formula): Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (W : WS), X ⊆ W :=
  by
  intro consX
  let paths : List (Σ Y, Path Y) := sorry
  let WSlist : List (Finset Formula) := List.map (λ ⟨X, path⟩ => toFinset path) paths
  let WS := WSlist.toFinset
  let M : KripkeModel WS := by
    constructor
    -- define valuation function
    · intro ⟨w, w_in⟩ p
      exact (·p) ∈ w
    -- define relation
    · intro ⟨w, w_in⟩ ⟨v, v_in⟩
      exact projection w ⊆ v
  let pathX : Path X := sorry
  use WS, ⟨M, ?_⟩, ⟨toFinset pathX, ?_⟩
  · simp
  · constructor
    · intro ⟨W, W_in⟩
      simp at W_in
      choose W' pathW' h using W_in
      rcases h with ⟨_, W_eq⟩
      subst W_eq
      exact ⟨pathSaturated pathW', pathConsistent pathW'⟩
    · constructor
      · aesop
      · constructor
        · intro ⟨w, w_in⟩ ⟨v, v_in⟩ f wRv h
          rewrite [← proj] at h
          aesop
        · intro ⟨w, w_in⟩ f nboxf_in_w
          simp at nboxf_in_w
          sorry
  · sorry

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

theorem consistentThenOpenTab : Consistent X → ∃ (t : Tableau X), isOpen t :=
  by
  have ⟨tX⟩ := existsTableauFor X
  contrapose
  simp[not_exists, Consistent, Inconsistent]
  intro h
  specialize h tX
  refine Nonempty.intro ?val
  have : isClosed tX := by
    have h2 : ¬ isOpen tX ↔ ¬ ¬ isClosed tX := Iff.symm (Iff.not (Iff.symm open_iff_notClosed))
    simp_all only [not_not, not_true_eq_false, not_false_eq_true, iff_true]
  exact (isClosed_then_ClosedTab this)
