-- SETSIMP
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Bml.Syntax

@[simp]
theorem union_singleton_is_insert {X : Finset Formula} {ϕ : Formula} : X ∪ {ϕ} = insert ϕ X :=
  by
  have fo := Finset.insert_eq ϕ X
  aesop

@[simp]
theorem sdiff_singleton_is_erase {X : Finset Formula} {ϕ : Formula} : X \ {ϕ} = X.erase ϕ :=
  by
  induction X using Finset.induction_on
  · simp
  ext1
  aesop

@[simp]
theorem lengthAdd {X : Finset Formula} {ϕ} :
    ϕ ∉ X → lengthOfSet (insert ϕ X) = lengthOfSet X + lengthOfFormula ϕ :=
  by
  intro notin
  unfold lengthOfSet
  rw [Finset.sum_insert notin]
  apply Nat.add_comm

@[simp]
theorem lengthOf_insert_leq_plus {X : Finset Formula} {ϕ : Formula} :
    lengthOfSet (insert ϕ X) ≤ lengthOfSet X + lengthOfFormula ϕ :=
  by
  by_cases h : ϕ ∈ X
  · rw [Finset.insert_eq_of_mem h]; simp
  · rw [lengthAdd h]

@[simp]
theorem lengthRemove (X : Finset Formula) :
    ∀ ϕ ∈ X, lengthOfSet (X.erase ϕ) + lengthOfFormula ϕ = lengthOfSet X :=
  by
  intro ϕ in_X
  have claim : lengthOfSet (insert ϕ (X \ {ϕ})) = lengthOfSet (X \ {ϕ}) + lengthOfFormula ϕ :=
    by
    apply lengthAdd
    simp
  have anotherClaim : insert ϕ (X \ {ϕ}) = X := by
    ext1
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · aesop
    · tauto
  rw [anotherClaim] at claim
  aesop

theorem lengthSetRemove (X Y : Finset Formula) (h : Y ⊆ X) :
  lengthOfSet (X \ Y) + lengthOfSet Y  = lengthOfSet X :=
  by
    induction Y using Finset.induction_on
    case empty => simp
    case insert ϕ S not_in_S ih =>
      have subs_X : S ⊆ X := subset_trans (by aesop) h
      have phi_in_X : ϕ ∈ X :=
        by
          rw [←Finset.singleton_subset_iff]
          exact subset_trans (by aesop) h
      rw [Finset.sdiff_insert X S ϕ, ←lengthRemove X ϕ, lengthAdd]
      · rw [Nat.add_comm, Nat.add_assoc,
          Nat.add_comm (lengthOfFormula ϕ) (lengthOfSet (Finset.erase (X \ S) ϕ))]
        rw [lengthRemove (X \ S) ϕ, Nat.add_comm, ih subs_X]
        · rw [lengthRemove X]; assumption
        · simp; exact And.intro phi_in_X not_in_S
      · exact not_in_S
      · exact phi_in_X

theorem lengthOfEqualSets (X Y : Finset Formula) :
  X = Y → lengthOfSet X = lengthOfSet Y :=
  by intro hyp; aesop

@[simp]
theorem sum_union_le {T} [DecidableEq T] :
    ∀ {X Y : Finset T} {F : T → ℕ}, (X ∪ Y).sum F ≤ X.sum F + Y.sum F :=
  by
  intro X Y F
  · calc
      (X ∪ Y).sum F ≤ (X ∪ Y).sum F + (X ∩ Y).sum F := by simp
      _ = X.sum F + Y.sum F := Finset.sum_union_inter
