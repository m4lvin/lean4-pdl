import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded

/-! # Finite trans-inverse image and trans-irreflexive implies wellfounded

We prove some helper lemmas about `Relation.TransGen` and `WellFounded`.
The main result here is `wf_of_finTransInvImage_of_transIrrefl`
and to be used for termination of the `tableauGame`.
-/

/-- If the transitive closure of `r` is wellfounded, then `r` itself is wellfounded.
This was for example proven in https://www.cs.utexas.edu/~EWD/ewd12xx/EWD1241.PDF (page 2 aka 3)
(but here we prove it via `WellFounded.wellFounded_iff_has_min` instead. -/
lemma wf_of_trans_wf {α : Type} {r : α → α → Prop} (trans_wf : WellFounded (Relation.TransGen r)) :
    WellFounded r := by
  rw [WellFounded.wellFounded_iff_has_min]
  rw [WellFounded.wellFounded_iff_has_min] at trans_wf
  intro s s_nE
  specialize trans_wf s s_nE
  rcases trans_wf with ⟨m, m_in_s, m_is_min⟩
  refine ⟨m, m_in_s, ?_⟩
  intro x x_in_s hyp
  absurd m_is_min x x_in_s
  exact Relation.TransGen.single hyp

theorem Finite.wf_of_irrefl_trans {α : Type} (r: α → α → Prop)
    [Finite α]
    (trans_irrefl : IsIrrefl α (Relation.TransGen r))
    : WellFounded r := by
  apply wf_of_trans_wf $ @Finite.wellFounded_of_trans_of_irrefl α _ (Relation.TransGen r) _ trans_irrefl

lemma TransGen_from_Subtype {α : Type} {r : α → α → Prop} {P : α → Prop} {x y}
    (h : Relation.TransGen (fun (x y : Subtype P) => r x.1 y.1) x y)
    : Relation.TransGen r x y := by
  induction h
  case single => apply Relation.TransGen.single; assumption
  case tail => apply Relation.TransGen.tail <;> assumption

/-- Suppose for any `p` the inverse-image of `p` under the transitive closure of `r` is finite,
and suppose the transitive closure of `r` is irreflexive. Then `r` is wellfounded. -/
theorem wf_of_finTransInvImage_of_transIrrefl {α : Type}
    (r : α → α → Prop)
    (finTransInvImage : ∀ p : α, Finite { q : α // Relation.TransGen r q p }) -- Note the inverse.
    (trans_irrefl : IsIrrefl α (Relation.TransGen r))
    : WellFounded r := by
  -- Suppose there is an infinite descending sequence.
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  by_contra hyp
  simp at hyp
  rcases hyp with ⟨f, f_⟩
  -- Get the starting point `p` of the sequence.
  let p := f 0
  specialize finTransInvImage p
  -- Let r' be r within the inverse image of the transitive closure at `p`.
  let β : Type := { q : α // Relation.TransGen r q p }
  let r' : β → β → Prop := fun x y => r x.1 y.1
  -- Show that r' is also irrefelxive.
  have r'_irrefl : IsIrrefl _ (Relation.TransGen r') := by
    constructor
    rintro ⟨x, _⟩ r'_x_x
    absurd trans_irrefl.1 x
    exact TransGen_from_Subtype r'_x_x
  -- By assumption the inverse image of r' at `p` is also finite, so r' must be well founded.
  have := @Finite.wf_of_irrefl_trans β r' finTransInvImage r'_irrefl
  -- Hence there is no infinite descending r'-sequence.
  rw [WellFounded.wellFounded_iff_no_descending_seq] at this
  absurd this
  simp
  -- But we can get such a r'-sequence from the r-sequence, contradiction!
  have claim : ∀ k : ℕ, Relation.TransGen r (f k.succ) p := by
    intro k
    induction k
    case zero => apply Relation.TransGen.single; apply f_
    case succ IH => exact Relation.TransGen.head (f_ _) IH
  let f' : ℕ → β := fun k => ⟨f k.succ, by apply claim⟩
  refine ⟨f', by simp_all [p, β, r', f']⟩
