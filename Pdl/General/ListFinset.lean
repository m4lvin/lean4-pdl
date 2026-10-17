module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Vector.Basic

/-! # General helper lemmas

Nothing in this file is about PDL. These are helper definitions and lemmas that are
used in several places and might also be in (newer versions of) Mathlib.
-/

@[expose] public section

/-! ## Helpers about `List`s and `Finset`s -/

@[simp]
def List.toFinFin [DecidableEq α] : List (List α) → Finset (Finset α )
  | LS => (LS.map (fun L => L.toFinset)).toFinset

/-- Turning a mapped list into a `Finset` is the image of the `Finset`. -/
lemma List.toFinset_map_eq_image {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

/-! ## Helpers about `List.Vector` -/

lemma List.Vector.tail_last_eq_last {k : Nat} (l : List.Vector α k.succ.succ) :
    l.tail.last = l.last := by
  rcases l with ⟨l, h_l⟩
  cases l with
  | nil => simp at h_l
  | cons => rfl
