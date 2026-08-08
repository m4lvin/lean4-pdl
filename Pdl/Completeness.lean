import Pdl.Soundness
import Pdl.BuildTreeExistence

/-! # Completeness Proof (Section 6.4) -/

open HasSat

/-- Theorem 6.21: If Builder has a winning strategy then there is a model graph.
Uses `BuildTree.toModel`. -/
theorem strmg (X : Sequent) (s : Strategy tableauGame Builder) (h : winning s (startPos X)) :
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS),
      ∃ Z ∈ WS, X.bothSides.toFinset ⊆ Z := by
  unfold startPos at h
  rcases posOf_for_startPos X with ⟨proPos, posOf_def⟩
  let bt := buildTree s (posOf_def ▸ h)
  let WS := bt.toModel.1
  let M := bt.toModel.2
  refine ⟨WS, ⟨M, ⟨?a, ?b, ?c, ?d⟩⟩, ?X_in⟩
  -- show the model graph properties
  case a =>
    rintro ⟨X, X_in⟩
    unfold WS at X_in
    simp at X_in
    rcases X_in with ⟨π, in_all, def_X⟩
    have := π.locConsSatBas -- using Lemma 6.16 for (i)
    simp_all [PreState.forms]
  -- "(b, c) will follow immediately from the definition"
  case b =>
    simp_all [M]
  case c =>
    intro X Y a φ X_a_Y aφ_in_X -- pick any ⌈a⌉φ
    simp only [M] at X_a_Y
    rcases X_a_Y with ⟨ψ, in_X, sub_Y⟩ -- relation was witnessed by ⌈a⌉ψ
    apply sub_Y -- show that φ is in projection
    simp_all
  case d =>
    simp only [Subtype.exists, exists_and_right, Subtype.forall]
    intro w w_in α φ in_w
    -- "The main challenge" :-)
    -- Paper proof uses Lemmas 6.18 and 6.20 here, depending on loading.
    unfold WS BuildTree.toModel at w_in
    simp only [List.mem_toFinset, List.mem_map] at w_in
    -- w must come from some pre-state:
    rcases w_in with ⟨π, π_in, def_w⟩
    subst def_w
    -- unfold PreState.forms at in_w -- NO, use lemma to switch to wforms instead?
    rw [PreState.mem_forms_iff] at in_w
    rcases in_w with in_w|(⟨χ,χul_def,in_w⟩|⟨ψ,ψul_def,in_w⟩)
    · -- normal, use 6.20
      rcases freeDiamondExistence in_w with ⟨π', in_π'_forms, α_rel⟩
      refine ⟨π'.forms, ⟨?_, α_rel⟩, in_π'_forms⟩
      unfold WS
      simp only [BuildTree.toModel, Finset.union_singleton, List.mem_toFinset, List.mem_map]
      exact bt.exists_mem_attach_forms_eq
    · -- loaded but not negated, cannot happen
      exfalso
      cases χ
      unfold LoadFormula.unload at χul_def
      grind
    · -- neg loaded, use 6.18
      rcases ψ with ⟨⟨α',χ⟩ ⟩
      simp only [negUnload, Formula.neg.injEq] at ψul_def
      rcases PreState.loadedDiamondExistence in_w with ⟨t, in_t, ρ, u, α_rel⟩
      unfold WS
      simp only [BuildTree.toModel, Finset.union_singleton, List.mem_toFinset, List.mem_map]
      refine ⟨ρ.forms, ⟨bt.exists_mem_attach_forms_eq, ?_⟩, ?_⟩
      · have : α = α' := by cases χ <;> grind [LoadFormula.unload]
        rw [this]
        exact α_rel
      · -- use `in_t : AnyNegFormula.mem_Sequent t.btAt.snd.fst (~''χ)` here.
        -- But better adjust the statement of `PreState.loadedDiamondExistence` first.
        sorry
  case X_in =>
    unfold WS
    -- Here the def of `BuildTree.allPreStates` matters.
    simp
    -- Use that there must be some pre-state containing the root.
    rcases bt.collect_contains_root with ⟨π, π_in, X_in_π⟩
    refine ⟨⟨π, π_in⟩, ?_, ?_⟩
    · apply List.mem_attach
    · intro φ φ_in
      unfold PreState.forms
      simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, exists_exists_and_eq_and]
      use X
      rw [← X.bothSides_toFinset_eq_toFinset] at φ_in
      simp [-Sequent.bothSides_toFinset_eq_toFinset] at φ_in
      grind

/-- Helper for `completeness`. Uses `gameP` and `strmg`. -/
lemma modelExistence {X} : consistent X →
    ∃ (WS : Finset (Finset Formula)) (_ : ModelGraph WS) (W : WS), X.bothSides.toFinset ⊆ W :=
  by
  intro consX
  rcases gamedet tableauGame (startPos X) with ProverHasWinningS | BuilderHasWinningS
  · absurd consX
    rcases ProverHasWinningS with ⟨sP, winning_sP⟩
    simp_all [inconsistent]
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
  simp [modelCanSemImplySequent] at *
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
