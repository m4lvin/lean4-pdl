import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Sups
import Mathlib.Data.List.Basic
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.Nat.PartENat
import Mathlib.Tactic.Linarith

import Pdl.UnfoldDia
import Pdl.AxiomBlame

-- Alternative to `Paths.lean` for the proof of `correctRightIP`.

-- Currently unsure whether this is easier than doing world-paths.
-- Due to the general W type and M.Rel the distance may not be computable.
-- On the other hand, we *only need this for a proof* of correctness
-- of interpolants, not to define/compute the interpolant themselves.
-- So it may be fine to have noncomputable defs here.
-- Still leaves the map/enum problem though due to generality of W.

-- NOTE: it may be nice in general to have a Decidable evaluate.

-- TODO move parts from here to `Semantics.lean`?

/-- A Kripke model where the relation and valuation are decidable.
Moreover, to get computable composition and transitive closure we
want the type of worlds to be finite and enumerable.
In fact, to avoid choice, we want a list of all worlds.
-- TODO: weaken List to Fintype, should still be possible to define distance?
-/
structure DecidableKripkeModel (W : Type) extends KripkeModel W where
  [finW : Fintype W]
  [deceq : DecidableEq W]
  [decrel : ∀ n, DecidableRel (Rel n)]
  [decval : ∀ w n, Decidable (val w n)]

instance : Coe (DecidableKripkeModel W) (KripkeModel W) := ⟨DecidableKripkeModel.toKripkeModel⟩

-- Possibly useful reference:
-- Martin Lange (2005): *Model checking propositional dynamic logic with all extras*
-- Journal of Applied Logic
-- https://doi.org/10.1016/j.jal.2005.08.002

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


/-- In models of size `n` this is a strict upper bound for the distance.
Used only for the termination proofs below. -/
@[simp]
def localMeasureOfProg (n : Nat) : Program → Nat
  | ·_ => 1
  | α;'β => 1 + localMeasureOfProg n α + localMeasureOfProg n β
  | α⋓β => 1 + localMeasureOfProg n α + localMeasureOfProg n β
  | ∗α => 1 + (1 + n) * localMeasureOfProg n α
  | ?'_ => 1 -- tests do not contribute to distance

theorem Program.nonZeroSize {α : Program} : localMeasureOfProg n α > 0 := by cases α <;> simp

theorem distance_helper (x y k : Nat) (h : k ≤ y) (h2 : x ≠ 0) : x + y + k < 1 + x + y * x + y := by
  apply Nat.add_lt_add_of_lt_of_le _ h
  cases x
  · tauto
  · rw [mul_add]
    simp
    rw [← add_assoc]
    rw [← add_assoc]
    simp
    omega


variable (M : KripkeModel W)

inductive KripkeModel.Walk : Program → W → W → Type
| nil : Walk a w w
| cons (h : relate M α w v) (p : Walk α v u) : Walk α w u
  deriving DecidableEq

def KripkeModel.Walk.length : M.Walk α w v → ℕ
| .nil => 0
| .cons _ p => p.length.succ

attribute [refl] KripkeModel.Walk.nil

@[trans]
def KripkeModel.Walk.append {M : KripkeModel W} {w v u : W} : M.Walk α w v → M.Walk α v u → M.Walk α w u
  | .nil, q => q
  | .cons h p, q => .cons h (p.append q)

noncomputable def KripkeModel.edist (α : Program) (w v : W) : ℕ∞ := ⨅ (p : M.Walk α w v), p.length

def KripkeModel.Reachable (α : Program) (w v : W) : Prop := Nonempty (M.Walk α w v)

@[refl]
protected theorem KripkeModel.Reachable.refl (w : W) : M.Reachable α w w := ⟨.nil⟩

@[trans]
protected theorem KripkeModel.Reachable.trans {w v u : W} (hwv : M.Reachable α w v) (hvu : M.Reachable α v u) :
    M.Reachable α w u :=
  hwv.elim fun pwv => hvu.elim fun pvu => ⟨pwv.append pvu⟩

theorem KripkeModel.reachable_iff_star_relate (α : Program) (w v : W) :
    M.Reachable α w v ↔ relate M (∗α) w v := by
  constructor
  . rintro ⟨h⟩
    induction h with
    | nil => exact .refl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  . intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans M hr ⟨Walk.cons ha Walk.nil⟩


-- QUESTION: Using `ℕ∞` here which is the same as `Option Nat` but can we avoid more internals?
-- Or should we use `PartENat` here?
-- NOTE: made noncomputable when updating to v4.16.0-rc2
noncomputable def distance {W} (M : DecidableKripkeModel W) (w v : W) (α : Program): ℕ∞ :=
  match α with
  | ·_ => ite (relate M α w v) 1 ⊤
  | ?'_ => ite (relate M α w v) 0 ⊤
  | α ⋓ β => (distance M w v α) ⊓ (distance M w v β)
  | ∗α => M.edist α w v
  | α ;' β => ⨅ u : W, distance M w u α + distance M u v β

noncomputable def distance_list {W} (M : DecidableKripkeModel W) (w v : W) : (δ : List Program) → ℕ∞
| [] => have := M.deceq
        if w = v then 0 else ⊤

-- similar to α;'β case in `distance`
| (α::δ) => ⨅ (x : W), distance M w x α + distance_list M x v δ

theorem distance_list_singleton (M : DecidableKripkeModel W) :
    distance_list M w v [α] = distance M w v α :=
  iInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun x => @dite _ (x = v) (M.deceq ..)
      (by simp_all only [self_le_add_right, implies_true])
      (by simp_all only [distance_list, ite_false, add_top, le_top, implies_true]))
    (fun _ _ => ⟨v, by simp_all only [distance_list, ite_true, add_zero]⟩)

theorem ENat.min_neq_top_iff {M N : ℕ∞} : min M N ≠ ⊤ ↔ (M ≠ ⊤) ∨ (N ≠ ⊤) := min_eq_top.not.trans not_and_or

theorem distance_iff_relate (M : DecidableKripkeModel W) α w v : (distance M w v α) ≠ ⊤ ↔ relate M α w v :=
  match α with
  | ·_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.one_ne_top).symm
  | ?'_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.zero_ne_top).symm
  | _ ⋓ _ => (min_eq_top.not.trans not_and_or).trans <| or_congr (distance_iff_relate ..) (distance_iff_relate ..)
  | ∗_ => ENat.iInf_coe_ne_top.trans <| M.reachable_iff_star_relate ..
  | _ ;' _ => iInf_eq_top.not.trans <| not_forall.trans <| exists_congr fun _ =>
    WithTop.add_ne_top.trans <| and_congr (distance_iff_relate ..) (distance_iff_relate ..)

theorem List.exists_mem_singleton {p : α → Prop} : (∃ x ∈ [a], p x) ↔ p a :=
  ⟨λ⟨_, ⟨x_in, px⟩⟩ ↦ mem_singleton.mp x_in ▸ px, (⟨_, ⟨mem_singleton_self _, .⟩⟩)⟩

theorem relate_existsH_distance (M : DecidableKripkeModel W) (α : Program)
    (w_α_v : relate M α w v)
    : ∃ Fδ ∈ H α,
        evaluate M w (Con Fδ.1)
      ∧ distance_list M w v Fδ.2 = distance M w v α  :=
  match α with
  | ·_ => List.exists_mem_singleton.mpr ⟨id, distance_list_singleton _⟩
  | ?'_ => match w_α_v with | ⟨wv, wφ⟩ => List.exists_mem_singleton.mpr <|
      ⟨wφ, by simp_all only [relate, true_and, distance_list, ite_true, distance, and_self]⟩
  | α ⋓ β => (min_cases (distance M w v α) (distance M w v β)).elim
      (fun h => _)
      (fun h => _)
  | ∗α => sorry
  | α ;' β => sorry

open Classical in
noncomputable def distance' {W} (M : KripkeModel W) (w v : W) (α : Program): ℕ∞ :=
  match α with
  | ·_ => ite (relate M α w v) 1 ⊤
  | ?'_ => ite (relate M α w v) 0 ⊤
  | α ⋓ β => (distance' M w v α) ⊓ (distance' M w v β)
  | ∗α => M.edist α w v
  | α ;' β => ⨅ u : W, distance' M w u α + distance' M u v β

open Classical in
theorem distance'_iff_relate (M : KripkeModel W) α w v : (distance' M w v α) ≠ ⊤ ↔ relate M α w v :=
  match α with
  | ·_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.one_ne_top).symm
  | ?'_ => ite_ne_right_iff.trans <| (iff_self_and.mpr fun _ => ENat.zero_ne_top).symm
  | _ ⋓ _ => (min_eq_top.not.trans not_and_or).trans <| or_congr (distance'_iff_relate ..) (distance'_iff_relate ..)
  | ∗_ => ENat.iInf_coe_ne_top.trans <| M.reachable_iff_star_relate ..
  | _ ;' _ => iInf_eq_top.not.trans <| not_forall.trans <| exists_congr fun _ =>
    WithTop.add_ne_top.trans <| and_congr (distance'_iff_relate ..) (distance'_iff_relate ..)
