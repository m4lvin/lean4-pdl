
/-- This no longer holds, now that we continue at loaded non-lprs.
Was only used for flipEdge.wellFounded which now uses a different argument. -/
lemma PathIn.mem_history_multisetEqTo_then_lrep {tab : Tableau Hist X} (p : PathIn tab) :
    (∃ Y ∈ (tabAt p).1, Y.multisetEqTo (nodeAt p)) → (tabAt p).2.2.isLrep := by
  rintro ⟨Y, h1, h2⟩
  generalize h : tabAt p = tp
  rcases tp with ⟨H, Z, t⟩
  simp [nodeAt] at h2
  rw [h] at h2
  cases t
  case loc _ _   nrep _ => sorry
    -- exact nrep ⟨Y, by have := Sequent.setEqTo_of_multisetEqTo; aesop⟩
  case pdl _ _ _ nrep _ => sorry
    -- exact nrep ⟨Y, by have := Sequent.setEqTo_of_multisetEqTo; aesop⟩
  case lrep             => simp [Tableau.isLrep]

lemma single_of_transgen {α} {r} {a c : α} : Relation.TransGen r a c → ∃ b, r a b := by
  intro h
  induction h
  case single b e => use b
  case tail d e ih => assumption

instance flipEdge.instIsIrrefl : @Std.Irrefl (PathIn tab) (Relation.TransGen (flip edge)) := by
  constructor
  intro p p_p
  rw [Relation.transGen_swap] at p_p
  have p_in_Hist_p := edge_TransGen_then_mem_History p_p
  have := PathIn.mem_history_multisetEqTo_then_lrep p ⟨nodeAt p, by simpa⟩
  rcases (single_of_transgen p_p) with ⟨_,   ⟨_, _, _, _, _, _, _, _, h, _⟩
                                           | ⟨_, _, _, _, _, _, _, h, _⟩⟩
  <;> rw [h] at this <;> contradiction

/-- The `flip edge` relation in a tableau is well-founded. -/
theorem flipEdge.wellFounded :
  WellFounded (flip (@edge _ _ tab)) := by
  apply Finite.wellfounded_of_irrefl_TC _ flipEdge.instIsIrrefl
-/
