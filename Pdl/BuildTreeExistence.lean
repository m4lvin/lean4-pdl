import Pdl.BuildTreeModel

/-! ## Existence Lemmas -/

/-- Lemma 6.18.
Note that we use `Rel` from `BuildTree.toModel` as the `R` to use `Modelgraphs.Q`.

TODO: use `Match.toPreState` to say that node `t` is "lying" on `π`.
Also still missing the `t < u` part. Is it needed? -/
lemma PreState.loadedDiamondExistence {φ : AnyFormula} {π : PreState bt} :
  (~'⌊α⌋φ : WhateverFormula) ∈ π.wForms →
    ∃ t : Match bt,
        AnyNegFormula.mem_Sequent (t.btAt).2.1 (~''φ)
      ∧ ∃ ρ : PreState bt,
          ∃ u : Match bt,
        @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π ρ := by
  sorry

-- TODO Lemma 6.19: for any diamond we can go to a pre-state where that diamond is loaded

/-- TODO: Induction loading for 6.20. -/
lemma freeDiamondExistenceInduction {X} {bt : BuildTree [] X}
    {ψ : Formula} -- FIXME also need that ψ is not boxed
    {α} {ηs : List Program} {π : PreState bt} :
    (~⌈α⌉⌈⌈ηs⌉⌉ψ : WhateverFormula) ∈ π.wForms →
      ∃ π' : PreState bt,
        (~⌈⌈ηs⌉⌉ψ) ∈ π'.forms -- NOTE: may occur loaded or unloaded in Λ(π')
        ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro _in_forms
  sorry

/-- Lemma 6.20: free diamond existence lemma for pre-states -/
lemma freeDiamondExistence {X} {bt : BuildTree [] X} {α} {φ : Formula} {π : PreState bt} :
  (~⌈α⌉φ : WhateverFormula) ∈ π.wForms → ∃ π' : PreState bt,
      ~φ ∈ π'.forms ∧ @Modelgraphs.Q bt.toModel.1 bt.toModel.2.Rel α π π' := by
  intro in_forms
  let ηs_ψ := boxesOf φ
  have := @freeDiamondExistenceInduction X bt ηs_ψ.2 α ηs_ψ.1 π ?in_forms
  case in_forms =>
    convert in_forms
    exact Eq.symm (def_of_boxesOf_def rfl)
  rcases this with ⟨π', in_π'_forms, α_rel⟩
  refine ⟨π', ?_, α_rel⟩
  · convert in_π'_forms
    exact def_of_boxesOf_def rfl
