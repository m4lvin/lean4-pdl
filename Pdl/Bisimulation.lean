import Pdl.Semantics
import Pdl.Vocab

/-! # Bisimulation -/

section Bisim

/-- A bisimulation between `M` and `M2`, for the given vocabulary. -/
structure IsBisim {W W2 : Type} (M : KripkeModel W) (M2 : KripkeModel W2)
  (Z : W → W2 → Prop) (vo : Vocab) : Prop where
  atoms : ∀ x y, Z x y → ∀ n ∈ vo.atomProps, (M.val x n ↔ M2.val y n)
  zig : ∀ x y, Z x y → ∀ c ∈ vo.atomProgs, ∀ x', M.Rel c x x' → ∃ y', M2.Rel c y y' ∧ Z x' y'
  zag : ∀ x y, Z x y → ∀ c ∈ vo.atomProgs, ∀ y', M2.Rel c y y' → ∃ x', M.Rel c x x' ∧ Z x' y'

theorem IsBisim.symm (hZ : IsBisim M M2 Z vo) : IsBisim M2 M (flip Z) vo := by
  constructor
  case atoms =>
    intro x y hxy p p_in
    rw [hZ.atoms y x hxy p p_in]
  case zig =>
    intro x y hxy a a_in x' xx'
    rcases hZ.zag y x hxy a a_in x' xx' with ⟨y', yy', Zy'x'⟩
    grind [flip]
  case zag =>
    intro x y hxy a a_in y' yy'
    rcases hZ.zig y x hxy a a_in y' yy' with ⟨x', xx', Zx'y'⟩
    grind [flip]

mutual

/-- Extend `IsBisim.zig` from atomic programs to all programs. -/
theorem IsBisim.relate (hZ : IsBisim M M2 Z vo) :
    ∀ α, α.voc ⊆ vo → ∀ x y x', Z x y → relate M α x x' → ∃ y', relate M2 α y y' ∧ Z x' y'
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

/-- Bisimilar states agree on all formulas in the given vocabulary. -/
theorem IsBisim.evaluate (hZ : IsBisim M M2 Z vo) :
    ∀ φ, φ.voc ⊆ vo → ∀ x y, Z x y → (evaluate M x φ ↔ evaluate M2 y φ)
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
        -- In order to apply IsBisim.relate to hZ.symm we avoid `variable {W W2} M M2` etc. above.
        obtain ⟨x', hxx', hx'y'⟩ :=
          hZ.symm.relate α (by simp_all; grind) y x y' hxy hyy'
        exact (hZ.evaluate φ hvφ x' y' hx'y').mp (h x' hxx')
      · intro h x' hxx'
        obtain ⟨y', hyy', hx'y'⟩ :=
          hZ.relate α (by simp_all; grind) x y x' (by simp_all) hxx'
        exact (hZ.evaluate φ hvφ x' y' hx'y').mpr (h y' hyy')

end -- mutual

end Bisim
