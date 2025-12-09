import Bml.Semantics
import Bml.BigConDis

def isBisimulation {W W' : Type} (Z : W → W' → Prop)
  (M : KripkeModel W) (M' : KripkeModel W') : Prop :=
  -- valuations
  (∀ w w' c, Z w w' → (M.val w c ↔ M'.val w' c))
  -- forward
  ∧
  (∀ w w', Z w w' → ∀ v, M.Rel w v → (∃ v', Z v v' ∧ M'.Rel w' v'))
  -- backward
  ∧
  (∀ w w', Z w w' → ∀ v', M'.Rel w' v' → (∃ v, Z v v' ∧ M.Rel w v))

/-- Two pointed models are bisimilar iff there exists a bisimulation connecting them. -/
def bisimilar : (KripkeModel W × W) → (KripkeModel W' × W') → Prop
  | (M, w), (M', w') => ∃ Z, isBisimulation Z M M' ∧ Z w w'

theorem modelEquiv_iff_bisimilar {W : Type} (finW : Fintype W) (finW' : Fintype W')
    (M : KripkeModel W) (w : W) (M' : KripkeModel W') (w' : W') :
    ((M,w) ≣ (M',w')) ↔ bisimilar (M,w) (M',w') := by
  constructor
  · intro Mw_equiv_Mw
    simp only [bisimilar, isBisimulation]
    refine ⟨?Z, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · exact (fun v v' => (M,v) ≣ (M',v')) -- let Z be semantic equivalence
    · intro v v' c hZ -- agreement
      exact hZ (Formula.atom_prop c)
    · intro w w' c v w_v -- showing the forth condition
      unfold modelEquiv at c
      unfold modelEquiv
      simp only [modelCanSemImplyForm]
      by_contra hyp
      simp only [not_exists, not_and] at hyp
      have claim : ∀ wᵢ' : Subtype (M'.Rel w'),
          ∃ (ψᵢ : Formula), (M,v) ⊨ ψᵢ ∧ ¬ (M', wᵢ'.val) ⊨ ψᵢ := by
        rintro ⟨wᵢ', w'_wᵢ'⟩
        simp only [modelCanSemImplyForm]
        specialize hyp wᵢ'
        rw [propext (not_iff_false_intro w'_wᵢ')] at hyp
        simp only [imp_false, not_forall] at hyp
        rcases hyp with ⟨ψ0, bla⟩
        by_cases Evaluate (M, v) ψ0
        · use ψ0; aesop
        · use ~ψ0; aesop
      let f (wᵢ' : Subtype (M'.Rel w')) : Formula := Exists.choose (claim wᵢ')
      let subfin : Fintype (Subtype (M'.Rel w')) :=
        @Subtype.fintype W' _ (fun _ => Classical.dec _) finW'
      let φ := ~(□(~ bigCon (subfin.elems.toList.map f)))
      have : (M,w) ⊨ φ := by
        simp [φ]
        refine ⟨v, w_v, ?_⟩
        unfold Fintype.elems subfin Subtype.fintype Fintype.subtype f
        simp only [Finset.filter_val, Finset.mem_mk, Multiset.mem_pmap, Subtype.mk.injEq,
          Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, exists_prop,
          exists_eq_right, modelCanSemImplyForm, forall_self_imp]
        intro wᵢ' w'_wᵢ'
        have := Exists.choose_spec (claim ⟨wᵢ', w'_wᵢ'⟩)
        tauto
      have : ¬ (M',w') ⊨ φ := by
        simp [φ]
        intro wᵢ' w'_wᵢ'
        have := Exists.choose_spec (claim ⟨wᵢ', w'_wᵢ'⟩)
        refine ⟨wᵢ', w'_wᵢ', ?_⟩
        unfold Fintype.elems subfin Subtype.fintype Fintype.subtype f
        simp only [Finset.filter_val, Finset.mem_mk, Multiset.mem_pmap, Subtype.mk.injEq,
          Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, exists_prop,
          exists_eq_right, modelCanSemImplyForm]
        tauto
      absurd c
      simp only [modelCanSemImplyForm, not_forall]
      use φ
      tauto
    · intro w w' c v' w'_v' -- showing the back condition
      -- COPY-PASTA from forth direction, just adding and removing primes :-)
      unfold modelEquiv at c
      unfold modelEquiv
      simp only [modelCanSemImplyForm]
      by_contra hyp
      simp only [not_exists, not_and] at hyp
      have claim : ∀ wᵢ : Subtype (M.Rel w),
          ∃ (ψᵢ : Formula), (M',v') ⊨ ψᵢ ∧ ¬ (M, wᵢ.val) ⊨ ψᵢ := by
        rintro ⟨wᵢ, w_wᵢ⟩
        simp only [modelCanSemImplyForm]
        specialize hyp wᵢ
        rw [propext (not_iff_false_intro w_wᵢ)] at hyp
        simp only [imp_false, not_forall] at hyp
        rcases hyp with ⟨ψ0, bla⟩
        by_cases Evaluate (M', v') ψ0
        · use ψ0; aesop
        · use ~ψ0; aesop
      let f (wᵢ : Subtype (M.Rel w)) : Formula := Exists.choose (claim wᵢ)
      let subfin : Fintype (Subtype (M.Rel w)) :=
        @Subtype.fintype W _ (fun _ => Classical.dec _) finW
      let φ := ~(□(~ bigCon (subfin.elems.toList.map f)))
      have : (M',w') ⊨ φ := by
        simp [φ]
        refine ⟨v', w'_v', ?_⟩
        unfold Fintype.elems subfin Subtype.fintype Fintype.subtype f
        simp only [Finset.filter_val, Finset.mem_mk, Multiset.mem_pmap, Subtype.mk.injEq,
          Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, exists_prop,
          exists_eq_right, modelCanSemImplyForm, forall_self_imp]
        intro wᵢ w_wᵢ
        have := Exists.choose_spec (claim ⟨wᵢ, w_wᵢ⟩)
        tauto
      have : ¬ (M,w) ⊨ φ := by
        simp [φ]
        intro wᵢ w_wᵢ
        have := Exists.choose_spec (claim ⟨wᵢ, w_wᵢ⟩)
        refine ⟨wᵢ, w_wᵢ, ?_⟩
        unfold Fintype.elems subfin Subtype.fintype Fintype.subtype f
        simp only [Finset.filter_val, Finset.mem_mk, Multiset.mem_pmap, Subtype.mk.injEq,
          Multiset.mem_filter, Finset.mem_val, Finset.mem_univ, true_and, exists_prop,
          exists_eq_right, modelCanSemImplyForm]
        tauto
      absurd c
      simp only [modelCanSemImplyForm, not_forall]
      use φ
      tauto
    · exact Mw_equiv_Mw
  · intro Mw_bisim_Mw' φ
    induction φ generalizing w w' with
    | bottom =>
      simp
    | atom_prop p =>
      rcases Mw_bisim_Mw' with ⟨Z, ⟨⟨hVal, _, _⟩, hZ⟩⟩
      exact hVal w w' p hZ
    | neg φ ih =>
      specialize ih w w'
      tauto
    | And φ ψ ihφ ihψ =>
      specialize ihφ w w'
      specialize ihψ w w'
      aesop
    | box φ ih =>
      rcases Mw_bisim_Mw' with ⟨Z, ⟨⟨prop, forth, back⟩, w_Z_w'⟩ ⟩
      constructor
      · intro w_boxphi
        simp
        intro v' w'_v'
        have := back _ _ w_Z_w' v' w'_v'
        rcases this with ⟨v, v_Z_v', w_v⟩
        simp at w_boxphi
        have := w_boxphi v w_v
        specialize ih v v' ⟨Z, by tauto⟩
        tauto
      · intro w'_boxphi
        simp
        intro v w_v
        have := forth _ _ w_Z_w' v w_v
        rcases this with ⟨v', v_Z_v', w'_v'⟩
        simp at w'_boxphi
        have := w'_boxphi v' w'_v'
        specialize ih v v' ⟨Z, by tauto⟩
        tauto
