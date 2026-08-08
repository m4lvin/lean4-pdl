import Pdl.BuildTree

/-! ## Defining The Model Graph -/

/-- Definition 6.17 to get model graph from strategy tree. -/
@[simp]
def BuildTree.toModel {X} (bt : BuildTree [] X) :
    (Σ W : Finset (Finset Formula), KripkeModel W) :=
  ⟨ ((bt.collect).attach.map (PreState.forms)).toFinset -- W -- NOTE .forms here, not .wforms
  , { val := fun X p => Formula.atom_prop p ∈ X.1 -- valuation V(p)
    , Rel := fun a X Y => -- relation Rₐ
        ∃ φ, (~⌈·a⌉φ) ∈ X.1 ∧ (projection a X.1.toList).toFinset ∪ {~φ} ⊆ Y.1 }⟩

/-- Helper lemma saying (the formula sets of) all pre-states are in the model graph. -/
lemma PreState.mem_toModel {X : Sequent} {bt : BuildTree [] X} {π : PreState bt} :
    π.forms ∈ bt.toModel.fst := by
  simp
  use π
  simp
  apply List.mem_attach

instance {bt : BuildTree [] X} : Coe (PreState bt) { w : Finset Formula // w ∈ bt.toModel.1 } :=
  ⟨fun π => ⟨π.forms, π.mem_toModel⟩⟩
