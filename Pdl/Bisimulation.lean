import Pdl.Semantics
import Pdl.Vocab

/-! # Bisimulation -/

/-! ## Internal Bisimulation — TODO generalize to non-internal -/

section Bisim

variable {W : Type} (M : KripkeModel W) (Z : W → W → Prop) (letters : ℕ → Prop)

/-- A bisimulation on `M`, for the proposition letters in `letters`. -/
structure IsBisim : Prop where
  symm : ∀ x y, Z x y → Z y x
  atoms : ∀ x y, Z x y → ∀ n, letters n → (M.val x n ↔ M.val y n)
  zig : ∀ x y, Z x y → ∀ c x', M.Rel c x x' → ∃ y', M.Rel c y y' ∧ Z x' y'

variable {M Z letters}

mutual

theorem IsBisim.relate (hZ : IsBisim M Z letters) :
    ∀ (α : Program) (x y x' : W), (∀ n, Sum.inl n ∈ α.voc → letters n) →
    Z x y → relate M α x x' → ∃ y', relate M α y y' ∧ Z x' y'
  | ·c, x, y, x', hv, hxy, h => hZ.zig x y hxy c x' h
  | α ;' β, x, y, x', hv, hxy, h => by
      obtain ⟨z, h1, h2⟩ := h
      obtain ⟨z', h1', hzz'⟩ := hZ.relate α x y z (by grind [Program.voc]) hxy h1
      obtain ⟨y', h2', hy'⟩ := hZ.relate β z z' x' (by grind [Program.voc]) hzz' h2
      exact ⟨y', ⟨z', h1', h2'⟩, hy'⟩
  | α ⋓ β, x, y, x', hv, hxy, h => by
      rcases h with hα | hβ
      · obtain ⟨y', h', hy'⟩ := hZ.relate α x y x' (by grind [Program.voc]) hxy hα
        exact ⟨y', Or.inl h', hy'⟩
      · obtain ⟨y', h', hy'⟩ := hZ.relate β x y x' (by grind [Program.voc]) hxy hβ
        exact ⟨y', Or.inr h', hy'⟩
  | ∗α, x, y, x', hv, hxy, h => by
      simp only [_root_.relate] at h ⊢
      induction h generalizing y with
      | refl => exact ⟨y, Relation.ReflTransGen.refl, hxy⟩
      | tail _ hstep IH =>
          obtain ⟨z', hz', hzz'⟩ := IH y hxy
          obtain ⟨y', hy', hy''⟩ := hZ.relate α _ z' _ (by grind [Program.voc]) hzz' hstep
          exact ⟨y', Relation.ReflTransGen.tail hz' hy', hy''⟩
  | ?'τ, x, y, x', hv, hxy, h => by
      simp
      simp at h
      rcases h with ⟨same_x, x_τ⟩
      have IH := IsBisim.evaluate hZ τ (by grind [Program.voc]) x y hxy
      rw [IH] at x_τ
      subst same_x
      exact ⟨x_τ, hxy⟩

theorem IsBisim.evaluate (hZ : IsBisim M Z letters) : ∀ (φ : Formula),
    (∀ n, Sum.inl n ∈ φ.voc → letters n) →
    ∀ x y, Z x y → (evaluate M x φ ↔ evaluate M y φ)
  | ⊥, _, _, _, _ => Iff.rfl
  | ·n, hv, x, y, hxy => hZ.atoms x y hxy n (hv n (by simp))
  | ~φ, hv, x, y, hxy => by
      simp only [_root_.evaluate]
      rw [hZ.evaluate φ (fun n hn => hv n (by simpa using hn)) x y hxy]
  | φ ⋀ ψ, hv, x, y, hxy => by
      simp only [_root_.evaluate]
      rw [hZ.evaluate φ (fun n hn => hv n (by simp [hn])) x y hxy,
        hZ.evaluate ψ (fun n hn => hv n (by simp [hn])) x y hxy]
  | ⌈α⌉ φ, hv, x, y, hxy => by
      have hvφ : ∀ n, Sum.inl n ∈ φ.voc → letters n := fun n hn => hv n (by simp [hn])
      simp only [_root_.evaluate]
      constructor
      · intro h y' hyy'
        obtain ⟨x', hxx', hx'y'⟩ :=
          hZ.relate α y x y' (by grind [Formula.voc]) (hZ.symm x y hxy) hyy'
        exact (hZ.evaluate φ hvφ x' y' (hZ.symm _ _ hx'y')).mp (h x' hxx')
      · intro h x' hxx'
        obtain ⟨y', hyy', hx'y'⟩ :=
          hZ.relate α x y x' (by grind [Formula.voc]) hxy hxx'
        exact (hZ.evaluate φ hvφ x' y' hx'y').mpr (h y' hyy')

end -- mutual

end Bisim
