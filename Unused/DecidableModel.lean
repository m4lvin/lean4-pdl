import Mathlib.Data.Finset.Card

import Pdl.Semantics


/-- A Kripke model where the relation and valuation are decidable.
Moreover, to get computable composition and transitive closure we
want the type of worlds to be finite and enumerable.
In fact, to avoid choice, we want a list of all worlds.
-/
structure DecidableKripkeModel (W : Type) extends KripkeModel W where
  [finW : Fintype W]
  [deceq : DecidableEq W]
  [decrel : ∀ n, DecidableRel (Rel n)]
  [decval : ∀ w n, Decidable (val w n)]

instance : Coe (DecidableKripkeModel W) (KripkeModel W) := ⟨DecidableKripkeModel.toKripkeModel⟩

-- Helper theorem, mathlib this?
theorem Finset.sdiff_ssubset_sdiff [DecidableEq α] {A B C : Finset α} (h1 : B ⊆ A) (h3 : C ⊂ B) :
    A \ B ⊂ A \ C := by
  rw [Finset.ssubset_iff] at h3
  rcases h3 with ⟨x, x_nIn_C, xC_sub_B⟩
  rw [Finset.ssubset_iff]
  use x
  constructor
  · simp_all only [Finset.mem_sdiff, not_and, Decidable.not_not]
    intro _in
    apply xC_sub_B
    simp_all
  · intro y
    simp only [Finset.mem_insert, Finset.mem_sdiff]
    rintro (y_eq_x | ⟨y_in, y_nIn⟩)
    · subst y_eq_x
      simp_all only [not_false_eq_true, and_true]
      apply h1
      apply xC_sub_B
      simp_all only [Finset.mem_insert, or_false]
    · constructor
      · exact y_in
      · by_contra y_in_C
        have : y ∈ insert x C := by aesop
        specialize xC_sub_B this
        tauto

theorem reachableFrom_terminationHelper (r : α → α → Prop) [DecidableRel r] [DecidableEq α] [α_fin : Fintype α] (here : Finset α)
    (h : (Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems).Nonempty)
    :
    (Fintype.elems \ (here ∪ Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems)).card <
  (Fintype.elems \ here).card := by
  apply Finset.card_lt_card
  apply Finset.sdiff_ssubset_sdiff
  · intro _ _
    apply α_fin.complete
  · rw [Finset.ssubset_def]
    constructor
    · intro x x_in
      simp only [Finset.mem_union, Finset.mem_filter]
      left
      exact x_in
    · rw [Finset.not_subset]
      rw [Finset.filter_nonempty_iff] at h
      rcases h with ⟨y, y_in, x, x_in, y_notIn, r_x_y⟩
      use y
      simp_all only [Finset.mem_union, Finset.mem_filter, not_false_eq_true, true_and, false_or,
        and_true]
      use x

/-- Computable definition to close a finset under the reflexive transitive closure of a relation. -/
def reachableFrom (r : α → α → Prop) [DecidableRel r] [DecidableEq α] [α_fin : Fintype α] (here : Finset α) :
    Finset α :=
  let nexts := α_fin.elems.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y)
  if _h : nexts.Nonempty then reachableFrom r (here ∪ nexts) else here
termination_by
  (α_fin.elems \ here).card
decreasing_by
  unfold nexts at _h
  apply reachableFrom_terminationHelper
  exact _h

theorem reachableFrom.subset (r : α → α → Prop) [DecidableRel r] [DecidableEq α] [α_fin : Fintype α] here :
    here ⊆ reachableFrom r here := by
  unfold reachableFrom
  simp_all only [dite_eq_ite]
  by_cases hyp : (Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems).Nonempty <;> simp_all
  have IH := reachableFrom.subset r (here ∪ Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems)
  intro x x_in
  have : x ∈ here ∪ Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems := by aesop
  exact IH this
termination_by
  (α_fin.elems \ here).card
decreasing_by
  apply reachableFrom_terminationHelper
  exact hyp

theorem reachableFrom.mem_iff (r : α → α → Prop) [DecidableRel r] [DecidableEq α] [α_fin : Fintype α] (here : Finset α) y :
    y ∈ reachableFrom r here ↔ ∃ x ∈ here, Relation.ReflTransGen r x y := by
  constructor
  · intro y_in
    unfold reachableFrom at y_in
    simp at y_in
    by_cases hyp : (Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems).Nonempty
    case pos =>
      simp only [hyp, reduceIte] at y_in
      rw [reachableFrom.mem_iff] at y_in -- needs termination argument
      clear hyp
      rcases y_in with ⟨x, x_in, r_x_y⟩
      simp at x_in
      rcases x_in with (_ | ⟨_, z, z_in, _, r_z_x⟩ )
      · use x
      · refine ⟨z, z_in, ?_⟩
        exact Relation.ReflTransGen.head r_z_x r_x_y
    case neg =>
      simp only [hyp, reduceIte] at y_in
      clear hyp
      use y
  · rintro ⟨x, x_in_here, rr_x_y⟩
    induction rr_x_y using Relation.ReflTransGen.head_induction_on
    · exact reachableFrom.subset r here x_in_here
    case head a b r_a_b rr_b_y IH =>
      by_cases b ∈ here
      · apply IH
        assumption
      · unfold reachableFrom
        simp only [dite_eq_ite]
        have nonEmp : (Finset.filter (fun y => ∃ x ∈ here, y ∉ here ∧ r x y) Fintype.elems).Nonempty :=
          ⟨b, by simp; exact ⟨Fintype.complete b, by use a⟩⟩
        simp [nonEmp]
        rw [reachableFrom.mem_iff] -- needs termination argument
        clear nonEmp
        use a
        simp
        constructor
        · left
          assumption
        · exact Relation.ReflTransGen.head r_a_b rr_b_y
termination_by
  (α_fin.elems \ here).card
decreasing_by
  · simp only [gt_iff_lt]
    apply reachableFrom_terminationHelper
    assumption
  · apply reachableFrom_terminationHelper
    assumption

/-- Used for `case star` in `relate.instDecidable` below. -/
instance decidableReflTransGen_of_decidableRel_on_finite [DecidableEq α] [Fintype α]
    (r : α → α → Prop) (h : DecidableRel r) : DecidableRel (Relation.ReflTransGen r) := by
  intro x y
  by_cases y ∈ reachableFrom r {x}
  case pos hyp =>
    rw [reachableFrom.mem_iff r {x} y] at hyp
    simp only [Finset.mem_singleton, exists_eq_left] at hyp
    exact isTrue hyp
  case neg hyp =>
    rw [reachableFrom.mem_iff r {x} y] at hyp
    simp only [Finset.mem_singleton, exists_eq_left] at hyp
    exact isFalse hyp

mutual
instance evaluate.instDecidable (M : DecidableKripkeModel W) (w : W) φ
    : Decidable (evaluate M w φ) :=
  match φ with
  | ⊥ => instDecidableFalse
  | ·_ => M.decval ..
  | _ ⋀ _ => @instDecidableAnd _ _ (evaluate.instDecidable ..) (evaluate.instDecidable ..)
  | ~_ => @instDecidableNot _ (evaluate.instDecidable ..)
  | ⌈_⌉_ => @Fintype.decidableForallFintype _ _
      (fun _ => @instDecidableForall _ _ (relate.instDecidable ..) (evaluate.instDecidable ..)) M.finW

instance relate.instDecidable (M : DecidableKripkeModel W) α (v w : W)
    : Decidable (relate M α v w) := by
  cases α
  case atom_prog a =>
    simp only [relate]
    apply M.decrel
  case sequence α β =>
    simp only [relate]
    have : DecidableEq W := M.deceq
    have : Fintype W := M.finW
    have IHα := relate.instDecidable M α
    have IHβ := relate.instDecidable M β
    apply @Fintype.decidableExistsFintype
  case union α β =>
    have IHα := relate.instDecidable M α v w
    have IHβ := relate.instDecidable M β v w
    simp
    by_cases relate M α v w <;> by_cases relate M β v w
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isFalse; tauto
  case star α =>
    simp only [relate]
    have IHα := relate.instDecidable M α
    have := M.deceq
    have : Fintype W := M.finW
    apply decidableReflTransGen_of_decidableRel_on_finite _ IHα
  case test τ =>
    simp only [relate]
    have IHτ := evaluate.instDecidable M v τ
    by_cases @decide (v = w) (M.deceq v w) <;> by_cases decide (evaluate M v τ)
    · apply isTrue; simp at *; tauto
    all_goals
      apply isFalse; simp at *; tauto
end
