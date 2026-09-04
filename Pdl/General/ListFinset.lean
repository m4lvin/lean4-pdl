import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Basic

/-! # General helpers about `List`s and `Finset`s

Nothing in this file is about PDL. These are helper definitions and lemmas that are
used in several places and might also be in (newer versions of) Mathlib.
-/

@[simp]
def List.toFinFin [DecidableEq α] : List (List α) → Finset (Finset α )
  | LS => (LS.map (fun L => L.toFinset)).toFinset

/-- Turning a mapped list into a `Finset` is the image of the `Finset`. -/
lemma List.toFinset_map_eq_image {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β) :
    (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

/-- The elements of a finite set, as a list of elements *together with* membership proofs.
This is the `Finset` analogue of `List.attach`. It is noncomputable because we have no
linear order on the elements, but the order of the list is irrelevant for our purposes.
-/
noncomputable def Finset.attachList {α : Type*} (s : Finset α) : List {x // x ∈ s} :=
  s.toList.attach.map (fun x => ⟨x.1, Finset.mem_toList.mp x.2⟩)

@[simp]
lemma Finset.mem_attachList {α : Type*} {s : Finset α} (a : {x // x ∈ s}) : a ∈ s.attachList :=
  List.mem_map.mpr ⟨⟨a.1, Finset.mem_toList.mpr a.2⟩, List.mem_attach _ _, rfl⟩

@[simp]
lemma Finset.attachList_map_val {α : Type*} {s : Finset α} :
    s.attachList.map Subtype.val = s.toList := by
  simp [Finset.attachList, List.map_map, Function.comp_def]
