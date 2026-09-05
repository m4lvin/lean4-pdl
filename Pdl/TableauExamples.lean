import Mathlib.Data.Finset.Basic

import Pdl.Soundness

/-! # Tableau Examples

As a sanity check we construct tableaux/proofs for some examples.
-/

/-- Helper: a sequent that contains a non-basic formula on the left is not basic.
(This might also fit into `Pdl/Sequent.lean`.) -/
lemma Sequent.not_basic_of_mem_L {L R : Finset Formula} {O : Olf} (φ : Formula)
    (h : φ ∈ L) (hφ : ¬ φ.basic) : ¬ Sequent.basic (L, R, O) := by
  intro bas
  exact hφ (bas.1 φ (by simp [Sequent.toFinset]; tauto))

example : provable (~⊥) := by
  apply provable.byTableauL
  apply Tableau.loc
  · simp [flprep]
    decide
  · exact Sequent.not_basic_of_mem_L (~~⊥) (by simp) (by simp [Formula.basic])
  case lt =>
    apply LocalTableau.byLocalRule
      { lr := LocalRule.oneSidedL (OneSidedLocalRule.neg ⊥) rfl
        L := _, R := _, O := _, ress := _, preconditionProof := _ } rfl ?_
    · simp
    · -- build one child tableau
      intro c c_in
      simp at c_in
      subst c_in
      apply LocalTableau.byLocalRule
        { lr := LocalRule.oneSidedL (OneSidedLocalRule.bot) rfl
        , L := _, R := _, O := _, ress := _, preconditionProof := _ } rfl ?_
      · simp
      · aesop
  case next =>
    intro Y Y_in
    exfalso -- endNodesOf is empty
    simp at Y_in

example : provable (~(p ⋀ (~p))) :=
  by
  apply provable.byTableauL
  apply Tableau.loc
  · simp
  · exact Sequent.not_basic_of_mem_L (~~(p ⋀ (~p))) (by simp) (by simp [Formula.basic])
  case lt =>
    apply LocalTableau.byLocalRule
      { lr := (LocalRule.oneSidedL (OneSidedLocalRule.neg (p ⋀ (~p))) rfl)
        L := _, R := _, O := none, ress := _, preconditionProof := _ } rfl ?_
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in
    apply LocalTableau.byLocalRule
      { lr := LocalRule.oneSidedL (OneSidedLocalRule.con p (~p)) rfl
        L := _, R := _, O := _, ress := _, preconditionProof := _ }
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in; subst c_in -- unique child node
    apply LocalTableau.byLocalRule
      { lr := LocalRule.oneSidedL (OneSidedLocalRule.not p) rfl
        L := _, R := _, O := _, ress := _, preconditionProof := _ }
    all_goals (try simp; try rfl)
    intro c c_in; simp at c_in
  case next =>
    intro Y Y_in
    exfalso -- endNodesOf is empty
    simp at Y_in

example : Tableau [] (({(·p : Formula), ~(·p : Formula)} : Finset Formula), ∅, none) :=
  by
  apply Tableau.loc
  · simp
  · simp [Sequent.basic, Sequent.closed]
    -- Here is an example where all formulas are basic
    -- but we still to do `loc` to close the tableau.
    -- For this we made "not closed" part of `Sequent.basic`.
  case lt =>
    apply LocalTableau.byLocalRule
      { lr := LocalRule.oneSidedL (OneSidedLocalRule.not (·p)) rfl
        L := _, R := _, O := _, ress := _, preconditionProof := _ }
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
    Tableau [(({r⋀(~⌈a⌉p), ~ (r ⋀ (~⌈a⌉p⋀q))} : Finset Formula), ∅, none)]
      (({r, ~(⌈a⌉p), ⌈a⌉(p⋀q)} : Finset Formula), ∅, none) :=
  by
  have principal : (~(⌈a⌉p)) ∈ ({r, ~(⌈a⌉p), ⌈a⌉(p⋀q)} : Finset Formula) := by simp
  apply Tableau.pdl (by simp [flprep, rep]; decide)
    (by simp [Sequent.basic, Sequent.closed]; decide)
    (@PdlRule.loadL _ [] _ _ _ _ principal (by simp [Formula.isBox]) rfl)
  change Tableau _ ({r, ⌈a⌉(p⋀q)}, ∅, some (Sum.inl (~'⌊a⌋(p : Formula))))
  apply Tableau.pdl (by simp [flprep, rep]; decide)
    (by simp [Sequent.basic, Sequent.closed]; decide)
    (.modL rfl rfl) -- Note: modL no longer needs to ask for basic.
  change Tableau _ ({~p, p⋀q}, ∅, none)
  apply Tableau.loc
  · simp [flprep, rep]
    decide
  · exact Sequent.not_basic_of_mem_L (p⋀q) (by simp) (by simp [Formula.basic])
  case lt =>
    apply LocalTableau.byLocalRule
      { lr := LocalRule.oneSidedL (OneSidedLocalRule.con p q) rfl
        L := _, R := _, O := _, ress := _, preconditionProof := _ }
    all_goals (try simp; try rfl)
    · intro c c_in; simp at c_in; subst c_in -- unique child node
      apply LocalTableau.byLocalRule
        { lr := LocalRule.oneSidedL (OneSidedLocalRule.not p) rfl
          L := _, R := _, O := _, ress := _, preconditionProof := _ }
      all_goals (try simp; try rfl)
      · intro c c_in; simp at c_in
      · decide -- This works because p and q are concrete values, not variables :-)
  case next =>
    intro Y Y_in
    exfalso
    aesop

/-- The local tableau used for Example 2 from MB.

Note that we never substitute the child sequents by their concrete values here.
Doing so would leave `Eq.rec`s in the term that block the computation of `endNodesOf`. -/
def ltForEx2 : LocalTableau (({r ⋀ (~(⌈a⌉p)), r ↣ ⌈a⌉(p ⋀ q)} : Finset Formula), ∅, none) := by
  apply LocalTableau.byLocalRule
    { lr := LocalRule.oneSidedL (OneSidedLocalRule.con r (~(⌈a⌉p))) rfl
      L := _, R := _, O := _, ress := _, preconditionProof := _ }
  all_goals (try simp; try rfl)
  intro c c_in
  simp at c_in
  apply LocalTableau.byLocalRule
    { L := c.1, R := c.2.1, O := c.2.2
      lr := LocalRule.oneSidedL (OneSidedLocalRule.nCo r (~(⌈a⌉(p ⋀ q)))) rfl
      ress := _, preconditionProof := ?_ } rfl ?_
  · rw [c_in]
    refine ⟨by decide, by simp, by simp⟩
  · intro c' c'_in
    simp [applyLocalRule, c_in] at c'_in
    -- now branching!
    by_cases hc : c' = ((({~ r, r, ~⌈a⌉p} : Finset Formula)), ∅, none)
    · -- first branch, apply "not"
      apply LocalTableau.byLocalRule
        { L := c'.1, R := c'.2.1, O := c'.2.2
          lr := LocalRule.oneSidedL (OneSidedLocalRule.not r) rfl
          ress := _, preconditionProof := ?_ } rfl ?_
      · rw [hc]; refine ⟨by decide, by simp, by simp⟩
      · intro c'' hc''; simp [applyLocalRule] at hc''
    · -- second branch, apply "neg" and then a simple end node
      have hc2 : c' = ((({~~(⌈a⌉(p⋀q)), r, ~⌈a⌉p} : Finset Formula)), ∅, none) := by
        rcases c'_in with h|h
        · exfalso; apply hc; rw [h]; decide
        · rw [h]; decide
      apply LocalTableau.byLocalRule
        { L := c'.1, R := c'.2.1, O := c'.2.2
          lr := LocalRule.oneSidedL (OneSidedLocalRule.neg (⌈a⌉(p⋀q))) rfl
          ress := _, preconditionProof := ?_ } rfl ?_
      · rw [hc2]; refine ⟨by decide, by simp, by simp⟩
      · intro c'' hc''
        simp [applyLocalRule, hc2] at hc''
        apply LocalTableau.sim
        rw [hc'']
        simp [Sequent.basic, Sequent.closed]
        decide

/-- Example 2 from MB. -/
example : Tableau [] (({r ⋀ (~(⌈a⌉p)), r ↣ ⌈a⌉(p ⋀ q)} : Finset Formula), ∅, none) := by
  refine Tableau.loc ?_ ?_ ltForEx2 ?_
  · simp
  · exact Sequent.not_basic_of_mem_L (r ⋀ (~(⌈a⌉p))) (by simp) (by simp [Formula.basic])
  · intro Y Y_in
    rw [show endNodesOf ltForEx2 = {(({r, ~(⌈a⌉p), ⌈a⌉(p⋀q)} : Finset Formula), ∅, none)} from
      by decide, Finset.mem_singleton] at Y_in
    subst Y_in
    exact subTabForEx2

/-- Example 4.8, but shown via `soundness`.
The corresponding partial tableau has a free repeat and is thus open. -/
example : ¬ provable ((⌈∗a⌉~⌈a⌉p) ↣ p) := by
  intro hyp
  have := soundness _ hyp
  unfold tautology at this
  absurd this
  push Not
  -- We define a single-world model with a loop where all atoms are false
  refine ⟨ Unit, ?_, (), ?_⟩
  · exact ⟨ fun w q => False
          , fun b v w => True ⟩
  · simp [evaluate]

/-- Example 4.9, but shown via `soundness`.
The corresponding partial tableau has a loaded-path repeat but is still open. -/
example (p q : Nat) (notSame : q ≠ p) :
    ¬ provable ((⌈a⌉⌈∗a⌉(·p)) ↣ (⌈a⌉⌈∗a⌉(·q))) := by
  intro hyp
  have := soundness _ hyp
  unfold tautology at this
  absurd this
  push Not
  -- We define a two-world model where only p holds at a loop at the end.
  refine ⟨ Fin 2, ?_, 0, ?_⟩
  · exact ⟨ fun w r => w = 1 ∧ r = p
          , fun b v w => w = 1 ⟩
  · simp [evaluate]
    constructor
    · intro h
      cases h
      grind
    · exact fun _ => ⟨Relation.ReflTransGen.refl, notSame⟩

-- Should this be with @[simp] in `LocalTableau.lean`?
lemma endNodesOf_cast_helper {h : X = Y} (ltX : LocalTableau X) :
    endNodesOf (h ▸ ltX) = endNodesOf ltX := by
  subst_eqs; simp

/-- The first local tableau used for Example 4.19: one application of the (□) rule. -/
def ltEx419 : LocalTableau (({⌈∗a⌉q, ~ ⌈a⌉⌈∗(a ⋓ (?' p))⌉q} : Finset Formula), ∅, none) := by
  apply LocalTableau.byLocalRule
    { lr := LocalRule.oneSidedL (OneSidedLocalRule.box (∗a) q (by decide)) rfl
      L := _, R := _, O := _, ress := _, preconditionProof := _ }
  all_goals (try simp; try rfl)
  intro Y Y_in
  apply LocalTableau.sim
  simp [unfoldBox, allTP, testsOfProgram, Bset, F, P, a] at Y_in
  rw [Y_in]
  simp [Sequent.basic, Sequent.closed]
  decide

/-- The second local tableau used for Example 4.19: the (□) rule and then the (◇) rule. -/
def ltEx419b : LocalTableau (({⌈∗a⌉q} : Finset Formula), ∅,
    some (Sum.inl (~'⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q)))) := by
  -- (□)
  apply LocalTableau.byLocalRule
    { lr := LocalRule.oneSidedL (OneSidedLocalRule.box (∗a) q (by decide)) rfl
      L := _, R := _, O := _, ress := _, preconditionProof := _ }
  all_goals (try simp; try rfl)
  intro Y Y_in
  simp [unfoldBox, allTP, testsOfProgram, Bset, F, P, a] at Y_in
  -- (◇)
  apply LocalTableau.byLocalRule
    { L := Y.1, R := Y.2.1, O := Y.2.2
      lr := LocalRule.loadedL (⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q)) (LoadRule.dia'
        (by simp [Program.isAtomic] : ¬ (∗((·atA)⋓(?'p))).isAtomic)) rfl
      ress := _, preconditionProof := ?_ } rfl ?_
  · rw [Y_in]; refine ⟨by simp, by simp, by simp⟩
  · intro Z Z_in
    simp [applyLocalRule, Y_in, unfoldDiamondLoaded', YsetLoad', Dset, splitLast] at Z_in
    -- branching!
    by_cases hZ : Z = (({q, ⌈a⌉⌈∗a⌉q, ~ q} : Finset Formula), ∅, none)
    · -- left branch: close with q and ~q
      apply LocalTableau.byLocalRule
        { L := Z.1, R := Z.2.1, O := Z.2.2
          lr := LocalRule.oneSidedL (OneSidedLocalRule.not q) rfl
          ress := _, preconditionProof := ?_ } rfl ?_
      · rw [hZ]; refine ⟨by decide, by simp, by simp⟩
      · intro W hW; simp [applyLocalRule] at hW
    · -- right branch: simple
      have hZ2 : Z = (({q, ⌈a⌉⌈∗a⌉q} : Finset Formula), ∅,
          some (Sum.inl (~'⌊a⌋(AnyFormula.loaded (⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q)))))) := by
        tauto
      apply LocalTableau.sim
      rw [hZ2]
      simp [Sequent.basic, Sequent.closed]
      decide

/-- Example 4.19 involving a loaded-path repeat -/
example : Tableau [] (({⌈∗a⌉q, ~ ⌈a⌉⌈∗(a ⋓ (?' p))⌉q} : Finset Formula), ∅, none) := by
  refine Tableau.loc ?_ ?_ ltEx419 ?_
  · simp
  · exact Sequent.not_basic_of_mem_L (⌈∗a⌉q) (by simp) (by simp [Formula.basic])
  · intro Y Y_in
    rw [show endNodesOf ltEx419
      = {(({~ ⌈a⌉⌈∗(a ⋓ (?' p))⌉q, q, ⌈a⌉⌈∗a⌉q} : Finset Formula), ∅, none)} from by decide,
      Finset.mem_singleton] at Y_in
    subst Y_in
    have principal : (~⌈a⌉⌈∗(a ⋓ (?' p))⌉q)
        ∈ ({~ ⌈a⌉⌈∗(a ⋓ (?' p))⌉q, q, ⌈a⌉⌈∗a⌉q} : Finset Formula) := by simp
    -- (L+)
    apply Tableau.pdl (by simp [flprep, rep]; decide)
      (by simp [Sequent.basic, Sequent.closed]; decide)
      (PdlRule.loadL (δ := [a]) principal (by simp [Formula.isBox]) rfl)
    change Tableau _ (({q, ⌈a⌉⌈∗a⌉q} : Finset Formula), ∅,
      some (Sum.inl (~'⌊⌊[a]⌋⌋⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q))))
    -- (M)
    apply Tableau.pdl (by simp [flprep, rep]; decide)
      (by simp [Sequent.basic, Sequent.closed]; decide)
      (PdlRule.modL rfl rfl)
    change Tableau _ (({⌈∗a⌉q} : Finset Formula), ∅,
      some (Sum.inl (~'⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q))))
    refine Tableau.loc ?_ ?_ ltEx419b ?_
    · simp [flprep, rep]; decide
    · exact Sequent.not_basic_of_mem_L (⌈∗a⌉q) (by simp) (by simp [Formula.basic])
    · intro Z Z_in
      rw [show endNodesOf ltEx419b = {(({q, ⌈a⌉⌈∗a⌉q} : Finset Formula), ∅,
          some (Sum.inl (~'⌊a⌋(AnyFormula.loaded (⌊∗(a ⋓ (?'p))⌋(AnyFormula.normal q))))))} from
        by decide, Finset.mem_singleton] at Z_in
      subst Z_in
      -- Note: the history here contains the companion of the loaded-path repeat.
      apply Tableau.lrep
      refine ⟨1, ?_, ?_⟩
      · decide
      · decide
