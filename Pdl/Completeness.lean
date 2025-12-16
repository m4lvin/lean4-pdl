import Pdl.Soundness
import Pdl.BuildTree

/-! # Completeness Proof (Section 6.4) -/

open HasSat

/-- Helper for `completeness`. Uses `gameP` and `strmg`. -/
lemma modelExistence {X} : consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.toFinset ⊆ W :=
  by
  intro consX
  rcases gamedet tableauGame (startPos X) with ProverHasWinningS | BuilderHasWinningS
  · absurd consX
    rcases ProverHasWinningS with ⟨sP, winning_sP⟩
    simp_all only [inconsistent]
    exact gameP _ (sP) winning_sP
  · rcases BuilderHasWinningS with ⟨sB, winning_sB⟩
    rcases strmg X sB winning_sB with ⟨WS, mg, Z, Z_in_WS, X_sub_Z⟩
    exact ⟨WS, mg, ⟨Z, Z_in_WS⟩, X_sub_Z⟩

/-- Theorem 6.1 -/
theorem completeness : ∀ X, consistent X → satisfiable X :=
  by
  rintro ⟨L, R, O⟩ X_is_consistent
  have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
  use WS, M.val, w
  simp only [Sequent.toFinset, Finset.union_assoc, modelCanSemImplySequent, List.mem_union_iff,
    Option.mem_toList, Option.map_eq_some_iff, Sum.exists, Sum.elim_inl, negUnload,
    Sum.elim_inr] at *
  intro f f_in
  apply truthLemma M w f
  apply h
  aesop

theorem consIffSat : ∀ X, X.isFree → (consistent X ↔ satisfiable X) :=
  fun X X_isFree => ⟨completeness X, correctness X X_isFree⟩

theorem singletonConsIffSat : ∀ φ, consistent ([φ],[],none) ↔ satisfiable φ :=
  by
  intro φ
  have := consIffSat ⟨[φ], [], none⟩
  simp [this, instSequentHasSat, modelCanSemImplySequent]
