import Mathlib.Data.FinEnum
import Mathlib.Data.Finset.Sups
import Mathlib.Data.List.Basic
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.Nat.PartENat
import Mathlib.Tactic.Linarith

import Pdl.UnfoldDia

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
structure DecidableKripkeModel (W :Type) where
  M : KripkeModel W
  allW : List W
  h : ∀ w : W, w ∈ allW
  deceq : DecidableEq W
  decrel : ∀ n, DecidableRel (M.Rel n)
  decval : ∀ w n, Decidable (M.val w n)

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
instance evaluate.instDecidable (Mod : DecidableKripkeModel W) w φ
    : Decidable (evaluate Mod.M w φ) := by
  cases φ
  · apply isFalse
    simp only [evaluate, not_false_eq_true]
  · simp only [evaluate]
    apply Mod.decval
  case neg φ =>
    simp only [evaluate]
    have IH := evaluate.instDecidable Mod w φ
    by_cases decide (evaluate Mod.M w φ)
    · apply isFalse
      simp [Decidable.not_not] at *
      assumption
    · apply isTrue
      simp at *
      assumption
  case and φ1 φ2 =>
    have IH1 := evaluate.instDecidable Mod w φ1
    have IH2 := evaluate.instDecidable Mod w φ2
    by_cases @decide (evaluate Mod.M w φ1) IH1 <;> by_cases @decide (evaluate Mod.M w φ2) IH2
    · apply isTrue; simp at *; tauto
    all_goals
      apply isFalse; simp at *; tauto
  case box α φ =>
    simp only [evaluate]
    let reachable := Mod.allW.filter
      (fun v => @decide (relate Mod.M α w v) (relate.instDecidable Mod α w v))
    let hyp := reachable.all
      (fun v => @decide (evaluate Mod.M v φ) (evaluate.instDecidable Mod v φ))
    by_cases decide hyp
    case pos yes =>
      apply isTrue
      intro v w_v
      have : v ∈ Mod.allW := Mod.h v
      have : v ∈ reachable := by
        unfold reachable
        simp only [List.mem_filter, decide_eq_true_eq]
        tauto
      unfold hyp at yes
      simp_all
    case neg no =>
      apply isFalse
      push_neg
      unfold hyp at no
      simp at no
      rcases no with ⟨v, v_in_r, not_v_φ⟩
      aesop
  termination_by
    sizeOf φ

instance relate.instDecidable (Mod : DecidableKripkeModel W) α v w
    : Decidable (relate Mod.M α v w) := by
  cases α
  case atom_prog a =>
    simp only [relate]
    apply Mod.decrel
  case sequence α β =>
    simp only [relate]
    have : DecidableEq W := Mod.deceq
    have : Fintype W := ⟨Mod.allW.toFinset, by have := Mod.h; simp_all [List.mem_toFinset]⟩
    have IHα := relate.instDecidable Mod α
    have IHβ := relate.instDecidable Mod β
    apply @Fintype.decidableExistsFintype
  case union α β =>
    have IHα := relate.instDecidable Mod α v w
    have IHβ := relate.instDecidable Mod β v w
    simp
    by_cases relate Mod.M α v w <;> by_cases relate Mod.M β v w
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isTrue; tauto
    · apply isFalse; tauto
  case star α =>
    simp only [relate]
    have IHα := relate.instDecidable Mod α
    have := Mod.deceq
    have : Fintype W := ⟨Mod.allW.toFinset, by intro x; simp; apply Mod.h⟩
    apply decidableReflTransGen_of_decidableRel_on_finite (relate Mod.M α) IHα
  case test τ =>
    simp only [relate]
    have IHτ := evaluate.instDecidable Mod v τ
    by_cases @decide (v = w) (Mod.deceq v w) <;> by_cases decide (evaluate Mod.M v τ)
    · apply isTrue; simp at *; tauto
    all_goals
      apply isFalse; simp at *; tauto
  termination_by
    sizeOf α
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

-- QUESTION: Using `ℕ∞` here which is the same as `Option Nat` but can we avoid more internals?
-- Or should we use `PartENat` here?
-- NOTE: made noncomputable when updating to v4.16.0-rc2
noncomputable def distance {W} (Mod : DecidableKripkeModel W) (v w : W)
    : (α : Program) → ℕ∞
| ·c => if @decide (Mod.M.Rel c v w) (Mod.decrel c v w) then 1 else ⊤
| ?'τ =>
  have := evaluate.instDecidable Mod v τ
  have := Mod.deceq v w
  if v = w ∧ evaluate Mod.M v τ then 0 else ⊤
| α⋓β => min (distance Mod v w α) (distance Mod v w β)
| α;'β =>
    let α_β_distOf_via x := distance Mod v x α + distance Mod x w β
    (Mod.allW.map α_β_distOf_via).reduceOption.min?
| ∗α =>
    -- TODO when rewriting this to Finset, use `WithTop.sum_eq_top` here?
    have := Mod.deceq
    if v_eq_w : v == w
    then 0
    else
      let rec mdist k :=
          if k == 0
          then ⊤
          else
            let distOf_step_via x := distance Mod v x α + mdist (k-1)
            (Mod.allW.map distOf_step_via).reduceOption.min?
          termination_by
            localMeasureOfProg Mod.allW.length α + Mod.allW.length + k
          decreasing_by
            · cases k <;> simp_all
            · simp_all [@Nat.pos_iff_ne_zero]
      ((List.range Mod.allW.length).attach.map (fun k => mdist k.val)).reduceOption.min?
termination_by
  α => localMeasureOfProg Mod.allW.length α + Mod.allW.length
decreasing_by
  · simp; linarith
  · simp
  · simp; linarith
  · simp
  · simp only [localMeasureOfProg, gt_iff_lt]
    rw [@one_add_mul]
    rw [← Nat.add_assoc]
    apply distance_helper
    · apply Nat.le_of_lt
      rw [← List.mem_range]
      exact k.prop
    · have := @Program.nonZeroSize Mod.allW.length α
      exact Nat.not_eq_zero_of_lt this

noncomputable def distance_list {W} (Mod : DecidableKripkeModel W) (v w : W) : (δ : List Program) → ℕ∞
| [] => have := Mod.deceq v w
        if v = w then 0 else ⊤

-- similar to α;'β case in `distance`
| (α::δ) => ⨅ (x : W), distance Mod v x α + distance_list Mod x w δ

theorem distance_list_singleton (Mod : DecidableKripkeModel W) :
    distance_list Mod v w [α] = distance Mod v w α :=
  iInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun x => @dite _ (x = w) (Mod.deceq ..)
      (by simp_all only [self_le_add_right, implies_true])
      (by simp_all only [distance_list, ite_false, add_top, le_top, implies_true]))
    (fun d => fun le => ⟨w, by simp_all only [distance_list, ite_true, add_zero]⟩)

theorem ENat.min_neq_top_iff {M N : ℕ∞} : min M N ≠ ⊤ ↔ (M ≠ ⊤) ∨ (N ≠ ⊤) := min_eq_top.not.trans not_and_or

theorem distance_iff_relate (Mod : DecidableKripkeModel W) α v w :
    (distance Mod v w α) ≠ ⊤ ↔ relate Mod.M α v w := by
  cases α
  case atom_prog => simp [distance]
  case test => simp [distance]
  case sequence α β =>
    simp only [distance, relate]
    constructor
    · rw [WithTop.ne_top_iff_exists]
      rintro ⟨k, def_k⟩
      rw [← @WithTop.some_eq_coe, eq_comm, @List.min?_eq_some_iff''] at def_k
      rcases def_k with ⟨k_in, k_is_min⟩
      clear k_is_min
      simp only [Option.map_eq_map, List.reduceOption_mem_iff, List.mem_map] at k_in
      rcases k_in with ⟨x, x_in, def_k⟩
      use x
      rw [← distance_iff_relate, ← distance_iff_relate, ← WithTop.add_ne_top]
      simp_all
    · rintro ⟨x, v_α_x, x_β_w⟩
      rw [← distance_iff_relate] at v_α_x x_β_w
      rw [@WithTop.ne_top_iff_exists] at v_α_x x_β_w
      rcases v_α_x with ⟨kα, def_kα⟩
      rcases x_β_w with ⟨kβ, def_kβ⟩
      rw [← WithTop.none_eq_top]
      rw [Option.ne_none_iff_isSome]
      apply @List.isSome_min?_of_mem _ _ _ (kα + kβ)
      rw [List.reduceOption_mem_iff]
      simp only [Option.map_eq_map, List.mem_map]
      refine ⟨x, Mod.h x, ?_⟩
      rw [← def_kα, ← def_kβ]
      rfl
  case union α β =>
    simp only [distance, relate]
    constructor
    · intro has_dist
      rw [WithTop.ne_top_iff_exists] at has_dist
      rcases has_dist with ⟨k, def_k⟩
      rw [← @WithTop.some_eq_coe, eq_comm] at def_k
      rw [← distance_iff_relate, ← distance_iff_relate]
      rw [← ENat.min_neq_top_iff]
      simp_all -- `simp_all?` bug here?
    · intro is_rel
      rw [ENat.min_neq_top_iff]
      rw [distance_iff_relate, distance_iff_relate]
      exact is_rel
  case star α =>
    constructor
    . sorry
    . intro R
      induction R
      . simp only [distance, beq_self_eq_true, ↓reduceDIte, ne_eq, ENat.zero_ne_top, not_false_eq_true]
      . rename_i x y v_aS_x x_a_y fin_dis_x
        simp only [distance]
        split
        . simp only [ne_eq, ENat.zero_ne_top, not_false_eq_true]
        . sorry

theorem List.exists_mem_singleton {p : α → Prop} : (∃ x ∈ [a], p x) ↔ p a :=
  ⟨λ⟨_, ⟨x_in, px⟩⟩ ↦ mem_singleton.mp x_in ▸ px, (⟨_, ⟨mem_singleton_self _, .⟩⟩)⟩

theorem relate_existsH_distance (Mod : DecidableKripkeModel W) (α : Program)
    (v_α_w : relate Mod.M α v w)
    : ∃ Fδ ∈ H α,
        evaluate Mod.M v (Con Fδ.1)
      ∧ distance_list Mod v w Fδ.2 = distance Mod v w α  :=
  match α with
  | ·_ => List.exists_mem_singleton.mpr ⟨id, distance_list_singleton _⟩
  | ?'_ => List.exists_mem_singleton.mpr ⟨v_α_w.2, sorry⟩
  | α ⋓ β => sorry
  | ∗α => sorry
  | α ;' β => sorry


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
