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
  rename_i X α nBoxα simpleX closTabproj IH
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
    simp at LR'_in;
    refine Classical.choice ?_
    rcases LR'_in with ⟨c, c_in, EndNode⟩
    refine Nonempty.intro ?_
    dsimp at EndNode



theorem conThenConSucc : Consistent X → LocalRule X B →  ∃ Y ∈ B, Consistent Y := by
  intro consX locRule; revert consX; contrapose; simp
  intro InconSucc; cases locRule
  · case bot bot_in_X =>
    unfold Consistent Inconsistent; simp; refine Nonempty.intro ?_
    refine ClosedTableau.loc ?_ ?_; refine @LocalTableau.byLocalRule X ∅ (LocalRule.bot bot_in_X) ?_;
    intro Y; intro YInEmpty; refine False.elim ?_; aesop
    intro Y YEndNode; simp at YEndNode

  · case Not α nα =>
    unfold Consistent Inconsistent; simp; refine Nonempty.intro ?_
    refine ClosedTableau.loc ?_ ?_; refine @LocalTableau.byLocalRule X ∅ (@LocalRule.Not X α nα) ?_;
    intro Y YInEmpty; simp at YInEmpty

    intro Y; intro YEndNode; simp at YEndNode

  · case neg α nnα =>
    have : Inconsistent (X \ {~~α} ∪ {α}) := by
      unfold Inconsistent; simp; unfold Consistent Inconsistent at InconSucc; simp at InconSucc; exact InconSucc
    clear InconSucc; rename (Inconsistent (X \ {~~α} ∪ {α})) => InconSucc
    have :  (∃ tXα : LocalTableau (X \ {~~α} ∪ {α}), ∀ E ∈ endNodesOf ⟨(X \ {~~α} ∪ {α}), tXα⟩, Inconsistent E) := InconsIffInconsEndnode.mp InconSucc
    clear InconSucc; rename (∃ tXα : LocalTableau (X \ {~~α} ∪ {α}), ∀ E ∈ endNodesOf ⟨(X \ {~~α} ∪ {α}), tXα⟩, Inconsistent E) => InconSucc
    rcases InconSucc with ⟨tXα, endNodeincon⟩
    suffices : Inconsistent X; exact InconsisIffNotConsis.mp this
    suffices : (∃ tX : LocalTableau X, ∀ E ∈ endNodesOf ⟨X, tX⟩, Inconsistent E); exact InconsIffInconsEndnode.mpr this

    let LocTabX : LocalTableau X := by
      refine @byLocalRule X {X \ {~~α} ∪ {α} } (neg nnα) ?_
      intro Y Yin
      have Yis : Y = X \ {~~α} ∪ {α} := by
        simp at *; exact Yin
      subst Yis
      exact tXα
    use LocTabX; dsimp; unfold endNodesOf; simp;
    intro E Z Zis1
    have Zis : Z = X \ {~~α} ∪ {α} := by
      simp at *; exact Zis1
    subst Zis; simp
    intro EEndnode; exact endNodeincon E EEndnode

  · case Con α β α_β =>
    sorry

  · case nCo α β nα_β =>
    have InconSuccα : Inconsistent (insert (~α) (Finset.erase X (~(α⋀β)))) := by
      unfold Consistent at *; simp at *; simp_all only [not_true_eq_false, Finset.mem_erase, ne_eq, Formula.neg.injEq, nα_β]
    have InconSuccβ : Inconsistent (insert (~β) (Finset.erase X (~(α⋀β)))) := by
      unfold Consistent at *; simp at *; simp_all only [not_true_eq_false, Finset.mem_erase, ne_eq, Formula.neg.injEq, nα_β]
    clear InconSucc
    suffices : Inconsistent X; exact InconsisIffNotConsis.mp this
    suffices : (∃ tX : LocalTableau X, ∀ E ∈ endNodesOf ⟨X, tX⟩, Inconsistent E); exact InconsIffInconsEndnode.mpr this
    have :  (∃ tXα : LocalTableau (insert (~α) (Finset.erase X (~(α⋀β)))), ∀ E ∈ endNodesOf ⟨(insert (~α) (Finset.erase X (~(α⋀β)))), tXα⟩, Inconsistent E) := InconsIffInconsEndnode.mp InconSuccα
    have :  (∃ tXβ : LocalTableau (insert (~β) (Finset.erase X (~(α⋀β)))), ∀ E ∈ endNodesOf ⟨(insert (~β) (Finset.erase X (~(α⋀β)))), tXβ⟩, Inconsistent E) := InconsIffInconsEndnode.mp InconSuccβ
    clear InconSuccα InconSuccβ; rename (∃ tXα : LocalTableau (insert (~α) (Finset.erase X (~(α⋀β)))), ∀ E ∈ endNodesOf ⟨(insert (~α) (Finset.erase X (~(α⋀β)))), tXα⟩, Inconsistent E) => InconSuccα; rename (∃ tXβ : LocalTableau (insert (~β) (Finset.erase X (~(α⋀β)))), ∀ E ∈ endNodesOf ⟨(insert (~β) (Finset.erase X (~(α⋀β)))), tXβ⟩, Inconsistent E) => InconSuccβ
    rcases InconSuccα with ⟨tXα, endNodeinconα⟩
    rcases InconSuccβ with ⟨tXβ, endNodeinconβ⟩
    let LocTabX : LocalTableau X := by
      refine @byLocalRule X {insert (~α) (Finset.erase X (~(α⋀β))), insert (~β) (Finset.erase X (~(α⋀β)))} (?_) ?_
      convert_to (LocalRule X {X \ {~(α⋀β)} ∪ {~α}, X \ {~(α⋀β)} ∪ {~β}})
      simp; exact nCo nα_β
      intro Y Yin
      have Yis : Y = insert (~α) (Finset.erase X (~(α⋀β))) ∨ Y = insert (~β) (Finset.erase X (~(α⋀β))) := by
        simp at *; exact Yin
      refine (if Yeqα : Y = insert (~α) (Finset.erase X (~(α⋀β))) then ?_ else ?_)
      -- Y = X \ {~(α⋀β)} ∪ {~α}
      subst Yeqα; exact tXα
      -- Y = X \ {~(α⋀β)} ∪ {~β}
      have Yeqβ : Y = insert (~β) (Finset.erase X (~(α⋀β))) := by
        simp at *; simp_all only [not_true_eq_false, Finset.mem_erase, ne_eq, Formula.neg.injEq, false_or, or_true, nα_β]
      subst Yeqβ; exact tXβ
    use LocTabX;
    intro E EEndNodeX
    simp at EEndNodeX; cases EEndNodeX
    rename_i EEndNodeα; exact endNodeinconα E EEndNodeα
    rename_i EEndnodeβ
    dsimp at *
    by_cases β_eq_α : (insert (~β) (Finset.erase X (~(α⋀β)))) = (insert (~α) (Finset.erase X (~(α⋀β))))
    sorry
    sorry
