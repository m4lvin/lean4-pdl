import Bml.Semantics

def isBisimulation {W W': Type} (Z : W → W' → Prop)
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

-- FIXME: move to Semantics.lean
def modelEquiv (Mw : KripkeModel W × W) (Mw' : KripkeModel W' × W') : Prop :=
  ∀ (φ : Formula), Mw ⊨ φ ↔ Mw' ⊨ φ

infixl:77 "≣" => modelEquiv

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
      let S' := { u' : finW'.elems // M'.Rel w' u'  }
      have claim : ∀ wᵢ' : S', ∃ (ψᵢ : Formula), (M,v) ⊨ ψᵢ ∧ ¬ (M', wᵢ'.val.val) ⊨ ψᵢ := by
        rintro ⟨wᵢ', w'_wᵢ'⟩
        simp only [modelCanSemImplyForm]
        specialize hyp wᵢ'
        rw [propext (not_iff_false_intro w'_wᵢ')] at hyp
        simp only [imp_false, not_forall] at hyp
        rcases hyp with ⟨ψ0, bla⟩
        by_cases Evaluate (M, v) ψ0
        · use ψ0; aesop
        · use ~ψ0; aesop
      let φ := ~(□(~ BigConjunction (sorry /- idea: map using choice and claim -/)))
      have : (M,w) ⊨ φ := by sorry
      have : ¬ (M',w') ⊨ φ := by sorry
      absurd c
      simp only [modelCanSemImplyForm, not_forall]
      use φ
      tauto
    · intro w w' c v' w'_v' -- showing the back condition
      -- should be analogous to forth direction
      sorry
    · exact Mw_equiv_Mw
  · intro Mw_bisim_Mw'
    intro φ
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
