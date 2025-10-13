import Pdl.Soundness
import Pdl.TableauGame

/-! # Completeness (Section 6) -/

open HasSat

theorem modelExistence {X} : consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.toFinset ⊆ W :=
  by
  intro consX
  rcases gamedet tableauGame (startPos X) with ProverHasWinningS | BuilderHasWinningS
  · absurd consX
    rcases ProverHasWinningS with ⟨sP, winning_sP⟩
    simp_all [inconsistent]
    exact gameP _ (sP) winning_sP
  · rcases BuilderHasWinningS with ⟨sB, winning_sB⟩
    rcases strmg X sB winning_sB with ⟨WS, mg, X_in_WS⟩
    use WS, mg, ⟨X.toFinset, X_in_WS⟩

theorem completeness : ∀ X, consistent X → satisfiable X :=
  by
  rintro ⟨L, R, O⟩ X_is_consistent
  have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
  use WS, M.val, w
  simp [modelCanSemImplySequent, Sequent.toFinset] at *
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
