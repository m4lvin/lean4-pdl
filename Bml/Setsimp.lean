-- SETSIMP
import Syntax

#align_import setsimp

@[simp]
theorem union_singleton_is_insert {X : Finset Formula} {ϕ : Formula} : X ∪ {ϕ} = insert ϕ X :=
  by
  have fo := Finset.insert_eq ϕ X
  finish
#align union_singleton_is_insert union_singleton_is_insert

@[simp]
theorem sdiff_singleton_is_erase {X : Finset Formula} {ϕ : Formula} : X \ {ϕ} = X.eraseₓ ϕ :=
  by
  apply Finset.induction_on X
  simp
  intro g Y gNotInY IH
  ext1
  finish
#align sdiff_singleton_is_erase sdiff_singleton_is_erase

@[simp]
theorem lengthAdd {X : Finset Formula} :
    ∀ {ϕ} (h : ϕ ∉ X), lengthOfSet (insert ϕ X) = lengthOfSet X + lengthOfFormula ϕ :=
  by
  apply Finset.induction_on X
  · unfold lengthOfSet
    simp
  · intro ψ Y psiNotInY IH
    unfold lengthOfSet at *
    intro ϕ h
    finish
#align lengthAdd lengthAdd

@[simp]
theorem lengthOf_insert_leq_plus {X : Finset Formula} {ϕ : Formula} :
    lengthOfSet (insert ϕ X) ≤ lengthOfSet X + lengthOfFormula ϕ :=
  by
  cases' em (ϕ ∈ X) with in_x not_in_x
  · rw [Finset.insert_eq_of_mem in_x]; simp
  · rw [lengthAdd not_in_x]
#align lengthOf_insert_leq_plus lengthOf_insert_leq_plus

@[simp]
theorem lengthRemove (X : Finset Formula) :
    ∀ ϕ ∈ X, lengthOfSet (X.eraseₓ ϕ) + lengthOfFormula ϕ = lengthOfSet X :=
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
    finish
    tauto
  rw [anotherClaim] at claim 
  finish
#align lengthRemove lengthRemove

@[simp]
theorem sum_union_le {T} [DecidableEq T] :
    ∀ {X Y : Finset T} {F : T → ℕ}, (X ∪ Y).Sum F ≤ X.Sum F + Y.Sum F :=
  by
  intro X Y F
  ·
    calc
      (X ∪ Y).Sum F ≤ (X ∪ Y).Sum F + (X ∩ Y).Sum F := by simp
      _ = X.sum F + Y.sum F := Finset.sum_union_inter
#align sum_union_le sum_union_le

