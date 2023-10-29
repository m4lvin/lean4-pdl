-- SETSIMP
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic

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
  simp
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
  cases' em (ϕ ∈ X) with in_x not_in_x
  · rw [Finset.insert_eq_of_mem in_x]; simp
  · rw [lengthAdd not_in_x]

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
    aesop
    tauto
  rw [anotherClaim] at claim
  aesop

@[simp]
theorem sum_union_le {T} [DecidableEq T] :
    ∀ {X Y : Finset T} {F : T → ℕ}, (X ∪ Y).sum F ≤ X.sum F + Y.sum F :=
  by
  intro X Y F
  ·
    calc
      (X ∪ Y).sum F ≤ (X ∪ Y).sum F + (X ∩ Y).sum F := by simp
      _ = X.sum F + Y.sum F := Finset.sum_union_inter
