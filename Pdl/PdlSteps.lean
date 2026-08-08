import Pdl.AllPdlRule

/-! # Concrete PDL rule applications

Helpers to *construct* `PdlRule` applications, and to describe the sequents they lead to.
These are used in `Pdl/BuildTree.lean` to walk through a `BuildTree` when proving the
existence lemmas for the model graph.

The main results are:
- `PdlRule.exists_freeL` and `PdlRule.exists_freeR`: the (L-) rule is always applicable to a
  loaded sequent, and it does not change the set of formulas.
- `PdlRule.loadL_atomic` and `PdlRule.loadR_atomic`: the (L+) rule applied to an atomic
  diamond `~⌈·a⌉⌈⌈ηs⌉⌉ψ` (where `ψ` is not a box).
- `Sequent.modTarget` together with `PdlRule.modL_target` and `PdlRule.modR_target`:
  the (M) rule applied to an atomic loaded box.
- `Sequent.exists_atomic_modal_steps`: the combination of (L+) and (M), giving the
  `a`-successor of a free basic sequent.
-/

/-! ## The (L-) rule -/

/-- The (L-) rule is applicable to any left-loaded sequent, and the resulting sequent is
obtained by inserting the unloaded formula on the left. -/
lemma PdlRule.exists_freeL {L R : List Formula} {nlf : NegLoadFormula} :
    Nonempty (PdlRule (L, R, some (Sum.inl nlf)) (L.insert (negUnload nlf), R, none)) := by
  rcases nlf with ⟨χ⟩
  rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, rfl⟩
  exact ⟨PdlRule.freeL rfl (by simp)⟩

/-- The (L-) rule is applicable to any right-loaded sequent. -/
lemma PdlRule.exists_freeR {L R : List Formula} {nlf : NegLoadFormula} :
    Nonempty (PdlRule (L, R, some (Sum.inr nlf)) (L, R.insert (negUnload nlf), none)) := by
  rcases nlf with ⟨χ⟩
  rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, rfl⟩
  exact ⟨PdlRule.freeR rfl (by simp)⟩

/-- Unloading does not change which formulas occur in a sequent. -/
lemma Sequent.mem_bothSides_freeL {L R : List Formula} {nlf : NegLoadFormula} {f : Formula} :
    f ∈ Sequent.bothSides (L, R, some (Sum.inl nlf))
    ↔ f ∈ Sequent.bothSides (L.insert (negUnload nlf), R, none) := by
  rcases nlf with ⟨χ⟩
  simp only [Sequent.bothSides_eq, Olf.L_inl, Olf.R_inl, List.append_nil,
    List.mem_append, List.mem_singleton, List.mem_insert_iff, negUnload]
  tauto

/-- Unloading does not change which formulas occur in a sequent. -/
lemma Sequent.mem_bothSides_freeR {L R : List Formula} {nlf : NegLoadFormula} {f : Formula} :
    f ∈ Sequent.bothSides (L, R, some (Sum.inr nlf))
    ↔ f ∈ Sequent.bothSides (L, R.insert (negUnload nlf), none) := by
  rcases nlf with ⟨χ⟩
  simp only [Sequent.bothSides_eq, Olf.L_inr, Olf.R_inr, List.append_nil,
    List.mem_append, List.mem_singleton, List.mem_insert_iff, negUnload]
  tauto

/-! ## The (L+) rule for atomic diamonds -/

/-- The (L+) rule applied to a free atomic diamond on the left. -/
def PdlRule.loadL_atomic {L R : List Formula} {a : Nat} {ηs : List Program} {ψ : Formula}
    (h_in : (~⌈·a⌉⌈⌈ηs⌉⌉ψ) ∈ L) (hnb : ¬ ψ.isBox) :
    PdlRule (L, R, none)
      (L.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ), R, some (Sum.inl (~'(⌊·a⌋(AnyFormula.loadBoxes ηs ψ))))) := by
  set δfull : List Program := (·a : Program) :: ηs with hδfull
  have hne : δfull ≠ [] := by simp [hδfull]
  have hsplit : δfull.dropLast ++ [δfull.getLast hne] = δfull := List.dropLast_append_getLast hne
  have hform : (⌈⌈δfull.dropLast⌉⌉⌈δfull.getLast hne⌉ψ) = (⌈·a⌉⌈⌈ηs⌉⌉ψ) := by
    rw [← boxes_last, hsplit]; simp [hδfull]
  have h1 : (AnyFormula.loaded (loadMulti δfull.dropLast (δfull.getLast hne) ψ))
      = AnyFormula.loadBoxes δfull (.normal ψ) := by
    rw [loadMulti_eq_loadBoxes, hsplit]
  have h2 : AnyFormula.loadBoxes δfull (AnyFormula.normal ψ)
      = AnyFormula.loaded (⌊·a⌋(AnyFormula.loadBoxes ηs ψ)) := by
    change AnyFormula.loadBoxes ((·a : Program) :: ηs) _ = _
    rw [AnyFormula.loadBoxes_cons]
  have hload : (⌊⌊δfull.dropLast⌋⌋⌊δfull.getLast hne⌋(ψ : AnyFormula))
      = (⌊·a⌋(AnyFormula.loadBoxes ηs ψ)) := AnyFormula.loaded.inj (h1.trans h2)
  rw [← hform, ← hload]
  exact PdlRule.loadL (by rw [hform]; exact h_in) hnb rfl

/-- The (L+) rule applied to a free atomic diamond on the right. -/
def PdlRule.loadR_atomic {L R : List Formula} {a : Nat} {ηs : List Program} {ψ : Formula}
    (h_in : (~⌈·a⌉⌈⌈ηs⌉⌉ψ) ∈ R) (hnb : ¬ ψ.isBox) :
    PdlRule (L, R, none)
      (L, R.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ), some (Sum.inr (~'(⌊·a⌋(AnyFormula.loadBoxes ηs ψ))))) := by
  set δfull : List Program := (·a : Program) :: ηs with hδfull
  have hne : δfull ≠ [] := by simp [hδfull]
  have hsplit : δfull.dropLast ++ [δfull.getLast hne] = δfull := List.dropLast_append_getLast hne
  have hform : (⌈⌈δfull.dropLast⌉⌉⌈δfull.getLast hne⌉ψ) = (⌈·a⌉⌈⌈ηs⌉⌉ψ) := by
    rw [← boxes_last, hsplit]; simp [hδfull]
  have h1 : (AnyFormula.loaded (loadMulti δfull.dropLast (δfull.getLast hne) ψ))
      = AnyFormula.loadBoxes δfull (.normal ψ) := by
    rw [loadMulti_eq_loadBoxes, hsplit]
  have h2 : AnyFormula.loadBoxes δfull (AnyFormula.normal ψ)
      = AnyFormula.loaded (⌊·a⌋(AnyFormula.loadBoxes ηs ψ)) := by
    change AnyFormula.loadBoxes ((·a : Program) :: ηs) _ = _
    rw [AnyFormula.loadBoxes_cons]
  have hload : (⌊⌊δfull.dropLast⌋⌋⌊δfull.getLast hne⌋(ψ : AnyFormula))
      = (⌊·a⌋(AnyFormula.loadBoxes ηs ψ)) := AnyFormula.loaded.inj (h1.trans h2)
  rw [← hform, ← hload]
  exact PdlRule.loadR (by rw [hform]; exact h_in) hnb rfl

/-! ## The (M) rule -/

/-- The sequent reached by the (M) rule from `⟨L, R, some (Sum.inl (~'⌊·A⌋ξ))⟩`. -/
def Sequent.modTargetL (A : Nat) (L R : List Formula) (ξ : AnyFormula) : Sequent :=
  match ξ with
  | .normal φ => ⟨(~φ) :: projection A L, projection A R, none⟩
  | .loaded χ => ⟨projection A L, projection A R, some (Sum.inl (~'χ))⟩

/-- The sequent reached by the (M) rule from `⟨L, R, some (Sum.inr (~'⌊·A⌋ξ))⟩`. -/
def Sequent.modTargetR (A : Nat) (L R : List Formula) (ξ : AnyFormula) : Sequent :=
  match ξ with
  | .normal φ => ⟨projection A L, (~φ) :: projection A R, none⟩
  | .loaded χ => ⟨projection A L, projection A R, some (Sum.inr (~'χ))⟩

/-- The (M) rule applied to a left-loaded atomic box. -/
def PdlRule.modL_target {A : Nat} {L R : List Formula} {ξ : AnyFormula} :
    PdlRule ⟨L, R, some (Sum.inl (~'⌊·A⌋ξ))⟩ (Sequent.modTargetL A L R ξ) :=
  PdlRule.modL rfl (by cases ξ <;> rfl)

/-- The (M) rule applied to a right-loaded atomic box. -/
def PdlRule.modR_target {A : Nat} {L R : List Formula} {ξ : AnyFormula} :
    PdlRule ⟨L, R, some (Sum.inr (~'⌊·A⌋ξ))⟩ (Sequent.modTargetR A L R ξ) :=
  PdlRule.modR rfl (by cases ξ <;> rfl)

/-- The negation of the unloaded rest is in the sequent reached by (M). -/
lemma Sequent.mem_modTargetL_unload {A : Nat} {L R : List Formula} {ξ : AnyFormula} :
    (~ ξ.unload) ∈ (Sequent.modTargetL A L R ξ).bothSides := by
  cases ξ <;> simp [Sequent.modTargetL, Sequent.bothSides_eq, Olf.L, Olf.R, AnyFormula.unload]

/-- The negation of the unloaded rest is in the sequent reached by (M). -/
lemma Sequent.mem_modTargetR_unload {A : Nat} {L R : List Formula} {ξ : AnyFormula} :
    (~ ξ.unload) ∈ (Sequent.modTargetR A L R ξ).bothSides := by
  cases ξ <;> simp [Sequent.modTargetR, Sequent.bothSides_eq, Olf.L, Olf.R, AnyFormula.unload]

/-- The (M) rule keeps the `A`-projection of the free part of the sequent. -/
lemma Sequent.projection_mem_modTargetL {A : Nat} {L R : List Formula} {ξ : AnyFormula}
    {ρ : Formula} (h : (⌈·A⌉ρ) ∈ L ∨ (⌈·A⌉ρ) ∈ R) : ρ ∈ (Sequent.modTargetL A L R ξ).bothSides := by
  cases ξ <;>
    simp only [Sequent.modTargetL, Sequent.bothSides_eq, Olf.L, Olf.R,
      List.append_nil, List.mem_append, List.mem_cons, proj] <;>
    tauto

/-- The (M) rule keeps the `A`-projection of the free part of the sequent. -/
lemma Sequent.projection_mem_modTargetR {A : Nat} {L R : List Formula} {ξ : AnyFormula}
    {ρ : Formula} (h : (⌈·A⌉ρ) ∈ L ∨ (⌈·A⌉ρ) ∈ R) : ρ ∈ (Sequent.modTargetR A L R ξ).bothSides := by
  cases ξ <;>
    simp only [Sequent.modTargetR, Sequent.bothSides_eq, Olf.L, Olf.R,
      List.append_nil, List.mem_append, List.mem_cons, proj] <;>
    tauto

/-! ## Combining (L+) and (M) -/

/-- Loading an atomic diamond keeps the sequent basic. -/
lemma Sequent.basic_loadL_atomic {L R : List Formula} {a : Nat} {ηs : List Program} {ψ : Formula}
    (hbas : Sequent.basic (L, R, none)) :
    Sequent.basic
      (L.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ), R, some (Sum.inl (~'(⌊·a⌋(AnyFormula.loadBoxes ηs ψ))))) := by
  constructor
  · intro f f_in
    simp only [List.mem_append, Option.map_some, Sum.elim_inl, Option.toList_some,
      List.mem_singleton, negUnload] at f_in
    rcases f_in with (f_in | f_in) | rfl
    · exact hbas.1 f (by simp [List.mem_of_mem_erase f_in])
    · exact hbas.1 f (by simp [f_in])
    · simp
  · intro hcon
    apply hbas.2
    rcases hcon with hbot | ⟨f, f_in, nf_in⟩
    · left
      rcases hbot with h | h
      · exact Or.inl (List.mem_of_mem_erase h)
      · exact Or.inr h
    · right
      refine ⟨f, ?_, ?_⟩
      · rcases f_in with h | h
        · exact Or.inl (List.mem_of_mem_erase h)
        · exact Or.inr h
      · rcases nf_in with h | h
        · exact Or.inl (List.mem_of_mem_erase h)
        · exact Or.inr h

/-- Loading an atomic diamond keeps the sequent basic. -/
lemma Sequent.basic_loadR_atomic {L R : List Formula} {a : Nat} {ηs : List Program} {ψ : Formula}
    (hbas : Sequent.basic (L, R, none)) :
    Sequent.basic
      (L, R.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ), some (Sum.inr (~'(⌊·a⌋(AnyFormula.loadBoxes ηs ψ))))) := by
  constructor
  · intro f f_in
    simp only [List.mem_append, Option.map_some, Sum.elim_inr, Option.toList_some,
      List.mem_singleton, negUnload] at f_in
    rcases f_in with (f_in | f_in) | rfl
    · exact hbas.1 f (by simp [f_in])
    · exact hbas.1 f (by simp [List.mem_of_mem_erase f_in])
    · simp
  · intro hcon
    apply hbas.2
    rcases hcon with hbot | ⟨f, f_in, nf_in⟩
    · left
      rcases hbot with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_erase h)
    · right
      refine ⟨f, ?_, ?_⟩
      · rcases f_in with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_of_mem_erase h)
      · rcases nf_in with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_of_mem_erase h)

/-- Two PDL steps, first (L+) and then (M), lead from a free basic sequent containing the
atomic diamond `~⌈·a⌉⌈⌈ηs⌉⌉ψ` (with `ψ` not a box) to a sequent that contains `~⌈⌈ηs⌉⌉ψ`
and the whole `a`-projection of the sequent we started from. -/
lemma Sequent.exists_atomic_modal_steps {L R : List Formula} {a : Nat} {ηs : List Program}
    {ψ : Formula} (hnb : ¬ ψ.isBox) (hbas : Sequent.basic (L, R, none))
    (h_in : (~⌈·a⌉⌈⌈ηs⌉⌉ψ) ∈ Sequent.bothSides (L, R, none)) :
    ∃ Y1 Y2 : Sequent, Nonempty (PdlRule (L, R, none) Y1) ∧ Y1.basic
      ∧ Nonempty (PdlRule Y1 Y2)
      ∧ (~⌈⌈ηs⌉⌉ψ) ∈ Y2.bothSides
      ∧ ∀ ρ, (⌈·a⌉ρ) ∈ Sequent.bothSides (L, R, none) → ρ ∈ Y2.bothSides := by
  have hboth : ∀ f : Formula, f ∈ Sequent.bothSides (L, R, (none : Olf)) ↔ (f ∈ L ∨ f ∈ R) := by
    intro f; simp [Sequent.bothSides_eq, Olf.L, Olf.R]
  have hunload : (AnyFormula.loadBoxes ηs ψ).unload = ⌈⌈ηs⌉⌉ψ :=
    AnyFormula.loadBoxes_unload_eq_boxes
  rcases (hboth _).mp h_in with hL | hR
  · refine ⟨_, Sequent.modTargetL a (L.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ)) R (AnyFormula.loadBoxes ηs ψ),
      ⟨PdlRule.loadL_atomic hL hnb⟩, Sequent.basic_loadL_atomic hbas,
      ⟨PdlRule.modL_target⟩, ?_, ?_⟩
    · have := @Sequent.mem_modTargetL_unload a (L.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ)) R
        (AnyFormula.loadBoxes ηs ψ)
      rwa [hunload] at this
    · intro ρ hρ
      apply Sequent.projection_mem_modTargetL
      rcases (hboth _).mp hρ with h | h
      · exact Or.inl (List.mem_erase_of_ne (by simp) |>.mpr h)
      · exact Or.inr h
  · refine ⟨_, Sequent.modTargetR a L (R.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ)) (AnyFormula.loadBoxes ηs ψ),
      ⟨PdlRule.loadR_atomic hR hnb⟩, Sequent.basic_loadR_atomic hbas,
      ⟨PdlRule.modR_target⟩, ?_, ?_⟩
    · have := @Sequent.mem_modTargetR_unload a L (R.erase (~⌈·a⌉⌈⌈ηs⌉⌉ψ))
        (AnyFormula.loadBoxes ηs ψ)
      rwa [hunload] at this
    · intro ρ hρ
      apply Sequent.projection_mem_modTargetR
      rcases (hboth _).mp hρ with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_erase_of_ne (by simp) |>.mpr h)
