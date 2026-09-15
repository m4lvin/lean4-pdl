import Pdl.Semantics
import Pdl.Vocab

/-! # Bisimulation -/

/-! ## Internal Bisimulation — TODO generalize to non-internal -/

section Bisim

variable {W : Type} (M : KripkeModel W) (Z : W → W → Prop) (vo : Vocab)

/-- A bisimulation on `M`, for the given vocabulary. -/
structure IsBisim : Prop where
  symm : ∀ x y, Z x y → Z y x
  atoms : ∀ x y, Z x y → ∀ n ∈ vo.atomProps, (M.val x n ↔ M.val y n)
  zig : ∀ x y, Z x y → ∀ c ∈ vo.atomProgs, ∀ x', M.Rel c x x' → ∃ y', M.Rel c y y' ∧ Z x' y'

variable {M Z letters}

mutual

theorem IsBisim.relate (hZ : IsBisim M Z vo) :
    ∀ α, α.voc ⊆ vo → ∀ x y x', Z x y → relate M α x x' → ∃ y', relate M α y y' ∧ Z x' y'
  | ·c, hv, x, y, x', hxy, h => hZ.zig x y hxy c (by simp_all [Vocab.atomProgs]) x' h
  | α ;' β, hv, x, y, x', hxy, h => by
      obtain ⟨z, h1, h2⟩ := h
      obtain ⟨z', h1', hzz'⟩ := hZ.relate α (by simp_all; grind) x y z (by grind [Program.voc]) h1
      obtain ⟨y', h2', hy'⟩ := hZ.relate β (by simp_all; grind) z z' x' (by grind [Program.voc]) h2
      exact ⟨y', ⟨z', h1', h2'⟩, hy'⟩
  | α ⋓ β, hv, x, y, x', hxy, h => by
      rcases h with hα | hβ
      · obtain ⟨y', h', hy'⟩ := hZ.relate α (by simp_all; grind) x y x' (by grind [Program.voc]) hα
        exact ⟨y', Or.inl h', hy'⟩
      · obtain ⟨y', h', hy'⟩ := hZ.relate β (by simp_all; grind) x y x' (by grind [Program.voc]) hβ
        exact ⟨y', Or.inr h', hy'⟩
  | ∗α, hv, x, y, x', hxy, h => by
      simp only [_root_.relate] at h ⊢
      induction h generalizing y with
      | refl => exact ⟨y, Relation.ReflTransGen.refl, hxy⟩
      | tail _ hstep IH =>
          obtain ⟨z', hz', hzz'⟩ := IH y hxy
          obtain ⟨y', hy', hy''⟩ := hZ.relate α (by simp_all) _ z' _ (by grind [Program.voc]) hstep
          exact ⟨y', Relation.ReflTransGen.tail hz' hy', hy''⟩
  | ?'τ, hv, x, y, x', hxy, h => by
      simp only [Program.voc, _root_.relate, ↓existsAndEq, true_and] at *
      rcases h with ⟨same_x, x_τ⟩
      have IH := IsBisim.evaluate hZ τ (by grind [Program.voc]) x y hxy
      rw [IH] at x_τ
      subst same_x
      exact ⟨x_τ, hxy⟩

theorem IsBisim.evaluate (hZ : IsBisim M Z vo) :
    ∀ φ, φ.voc ⊆ vo → ∀ x y, Z x y → (evaluate M x φ ↔ evaluate M y φ)
  | ⊥, _, _, _, _ => Iff.rfl
  | ·n, hv, x, y, hxy => hZ.atoms x y hxy n (by simp_all [Vocab.atomProps])
  | ~φ, hv, x, y, hxy => by
      simp only [_root_.evaluate]
      rw [hZ.evaluate φ (fun n hn => by simp_all; grind) x y hxy]
  | φ ⋀ ψ, hv, x, y, hxy => by
      simp only [_root_.evaluate]
      rw [hZ.evaluate φ (fun n hn => by simp_all; grind) x y hxy,
        hZ.evaluate ψ (fun n hn => by simp_all; grind) x y hxy]
  | ⌈α⌉ φ, hv, x, y, hxy => by
      have hvφ : φ.voc ⊆ vo := fun n hn => by simp_all; grind
      simp only [_root_.evaluate]
      constructor
      · intro h y' hyy'
        obtain ⟨x', hxx', hx'y'⟩ :=
          hZ.relate α (by simp_all; grind) y x y' (hZ.symm x y hxy) hyy'
        exact (hZ.evaluate φ hvφ x' y' (hZ.symm _ _ hx'y')).mp (h x' hxx')
      · intro h x' hxx'
        obtain ⟨y', hyy', hx'y'⟩ :=
          hZ.relate α (by simp_all; grind) x y x' (by simp_all) hxx'
        exact (hZ.evaluate φ hvφ x' y' hx'y').mpr (h y' hyy')

end -- mutual

end Bisim
