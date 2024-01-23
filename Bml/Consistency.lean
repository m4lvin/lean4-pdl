import Bml.Syntax
import Bml.Semantics
import Bml.Modelgraphs
import Bml.Tableau

open LocalTableau
open HasLength
open HasSat
open LocalRule


-- NEED FOLLOWING REMAINING LEMMAS TO COMPLETE EVERYTHING:
  -- Need Lemma here:  X ⊆ Y and Consistent Y  ⇒ Consistent X
  -- Need Lemma here:  Consistext X and LocalRule X B  ⇒ ∃ Y,  Y ∈ B ∧ Consistent Y
  -- Need Lemma here:  Consistent (A ∪ (B - ~~α  + α))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - α⋀β  + α + β))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~α))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~β))   ⇒  Consistent (A ∪ B)







-- Obvious consequence of Consistency
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


-- Simple + Consistent implies all projections are Consistent
theorem consisImpliesProj : Consistent X → Simple X → ∀ α, ~ (□ α) ∈ X → Consistent (projection X ∪ {~α}) := by
  intro consisX simpleX α negBoxα;
  by_contra inconsis;
  have closTab : ClosedTableau (projection X ∪ {~α}) := by
    refine Classical.choice ?_
    unfold Consistent at *; simp at *; unfold Inconsistent at *; simp at inconsis; exact inconsis
  clear inconsis
  have closTabX : ClosedTableau X := @ClosedTableau.atm X α negBoxα simpleX closTab
  unfold Consistent at *; simp at *; unfold Inconsistent at *; simp at *; exact IsEmpty.false closTabX


-- Consistent node means every LocalTableau has a Consistent endNode
theorem consThenConEndnode : Consistent X → ∀ tX : LocalTableau X, ∃ E ∈ endNodesOf ⟨X, tX⟩, Consistent E  := by
  intro consisX
  by_contra h₀; simp at h₀; rcases h₀ with ⟨LocTabX, h₀⟩
  have : ∀ E ∈ endNodesOf ⟨X, LocTabX⟩, ClosedTableau E := by
    intro E EEndnode; specialize h₀ E EEndnode; unfold Consistent Inconsistent at h₀; simp at h₀
    refine Classical.choice ?_; exact h₀
  clear h₀; rename (∀ E ∈ endNodesOf ⟨X, LocTabX⟩, ClosedTableau E) => h₀
  have closTabX : ClosedTableau X := ClosedTableau.loc LocTabX h₀
  unfold Consistent Inconsistent at *; simp at *; exact IsEmpty.false closTabX


-- Consistent node means every LocalTableau has a endNode whose projections are consistent
theorem consThenConProjEndNode : Consistent X → ∀ tX : LocalTableau X, ∃ E ∈ endNodesOf ⟨X, tX⟩, ∀ α, ~ (□ α) ∈ E → Consistent (projection E ∪ {~α})  := by
  intro consisX tX
  have : ∃ E ∈ endNodesOf ⟨X, tX⟩, Consistent E := consThenConEndnode consisX tX
  rcases this with ⟨E, EEndnode⟩; rcases EEndnode with ⟨EEndnode, consisE⟩
  use E; refine And.intro EEndnode ?_;
  have simpleE : Simple E := endNodeSimple EEndnode
  intro α negBoxα; exact consisImpliesProj consisE simpleE α negBoxα
