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
  -- Need Lemma here:  Consistent (A ∪ (B - ~~α  + α))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - α⋀β  + α + β))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~α))   ⇒  Consistent (A ∪ B)
  -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~β))   ⇒  Consistent (A ∪ B)




theorem InconsisIffNotConsis : Inconsistent X ↔ ¬ Consistent X := by
  refine iff_def.mpr ?_; refine And.intro ?_ ?_;
  intro inconsisX consisX; unfold Consistent at *; unfold Inconsistent at *; exact consisX inconsisX

  intro NotconsisX; unfold Consistent at NotconsisX; simp at NotconsisX; exact NotconsisX


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

-- Every endnode Inconsistent means root is Inconsistent
theorem InconsThenInconsEndnode : (∃ tX : LocalTableau X, ∀ E ∈ endNodesOf ⟨X, tX⟩, Inconsistent E) → Inconsistent X := by
  intro h₀; rcases h₀ with ⟨LocTabX, endNodeIncon⟩
  by_contra consisX; unfold Inconsistent at consisX; simp at consisX
  have : ∃ E ∈ endNodesOf ⟨X, LocTabX⟩, Consistent E := by
    refine consThenConEndnode ?_ ?_; unfold Consistent Inconsistent; simp; exact consisX
  aesop

theorem InconsEndnodeThenIncons : Inconsistent X → (∃ tX : LocalTableau X, ∀ E ∈ endNodesOf ⟨X, tX⟩, Inconsistent E) := by
  intro inconsisX; unfold Inconsistent at inconsisX; simp at inconsisX; rcases inconsisX with ⟨inconsisX⟩;
  let inconsisX' := inconsisX
  induction inconsisX; all_goals clear X;
  swap
  -- Simple case
  rename_i X α nBoxα simpleX closTabproj _
  use sim simpleX; unfold endNodesOf; simp; unfold Inconsistent; simp; exact Nonempty.intro inconsisX'

  -- Local-Rule case
  rename_i X LocTabX endNodes IH
  use LocTabX; exact fun E a => InconsThenInconsEndnode (IH E a)

-- Inconsistent iff there is a localTab where every endnode is Inconsistent
theorem InconsIffInconsEndnode : Inconsistent X ↔ (∃ tX : LocalTableau X, ∀ E ∈ endNodesOf ⟨X, tX⟩, Inconsistent E) := by
  refine iff_def.mpr ?_; refine And.intro ?_ ?_; exact fun a => InconsEndnodeThenIncons a; exact fun a => InconsThenInconsEndnode a




-- Consistent node means every LocalTableau has a endNode whose projections are consistent
theorem consThenConProjEndNode : Consistent X → ∀ tX : LocalTableau X, ∃ E ∈ endNodesOf ⟨X, tX⟩, ∀ α, ~ (□ α) ∈ E → Consistent (projection E ∪ {~α})  := by
  intro consisX tX
  have : ∃ E ∈ endNodesOf ⟨X, tX⟩, Consistent E := consThenConEndnode consisX tX
  rcases this with ⟨E, EEndnode⟩; rcases EEndnode with ⟨EEndnode, consisE⟩
  use E; refine And.intro EEndnode ?_;
  have simpleE : Simple E := endNodeSimple EEndnode
  intro α negBoxα; exact consisImpliesProj consisE simpleE α negBoxα


-- Consistext X and LocalRule X B  ⇒ ∃ Y,  Y ∈ B ∧ Consistent Y
theorem consistentThenConsistentChild
  (lrApp : LocalRule X C):
  Consistent X → ∃ c ∈ C, Consistent c := by
  contrapose
  unfold Consistent Inconsistent
  simp
  intro h
  -- choose closed tableaux for your children
  have c_to_cTab {c: Finset Formula} (c_in: c ∈ C): ClosedTableau c := by
    specialize h c c_in
    exact Classical.choice h
  -- build the local tableau for LR containing these tableau
  apply Nonempty.intro
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.byLocalRule lrApp
    intro c c_in
    let fooo := c_to_cTab c_in
    apply (injectLocalTab fooo)
  case a =>
    intro LR' LR'_in
    refine Classical.choice ?_
    simp at LR'_in; dsimp at LR'_in
    rcases LR'_in with ⟨c, c_in, EndNode⟩
    simp [injectLocalTab] at *
    cases def_c : c_to_cTab c_in
    case loc lt_c next =>
      rw [def_c] at EndNode
      simp at EndNode
      refine Nonempty.intro ?_
      apply next
      exact EndNode
    case atm =>
      rw [def_c] at EndNode
      aesop
