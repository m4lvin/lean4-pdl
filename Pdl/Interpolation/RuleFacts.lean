import Pdl.Interpolation.Cluster

/-! # How the rules of a tableau act on the two components

This file collects the facts about the rules of a (split) tableau that the facts about a
proper cluster in `Pdl.ClusterFacts` are proved from:

* vocabulary preservation (Lemma 9.2): along the tableau the vocabulary of each of the two
  components only shrinks;
* right rules do not change the left component, and left rules do not change the right
  component (provided the loaded formula is on the right);
* a node with a coarse child loaded on the right is itself loaded on the right, and a node
  with children applies a left or a right rule;
* loaded-path repeats and the Dershowitz-Manna measure: going down along left rules
  strictly decreases the label.
-/

open HasSat

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Entailment from the left component of a node -/

/-- `Λ₁(t) ⊨ φ`: the formula `φ` follows from the left component of the fine node `t`. -/
def FinePathIn.leftEntails {Hist} {Y : Sequent} {tab : Tableau Hist Y}
    (t : FinePathIn tab) (φ : Formula) : Prop :=
  ∀ (W : Type) (M : KripkeModel W) (w : W),
    (∀ ψ ∈ t.label.left, evaluate M w ψ) → evaluate M w φ

/-! ### Vocabulary preservation

Lemma 9.2 of the paper: along the tableau the vocabulary of each of the two components
only shrinks.  "By inspection of the rules": for local rules this is
`localRule_does_not_increase_vocab_L` and `localRule_does_not_increase_vocab_R`, and for
the PDL rules we check the six cases directly. -/

section VocPreservation

/-- Membership in the vocabulary of a `Finset` of formulas.
This is `Finset.mem_fvoc` from `Pdl/Interpolation/Local.lean`. -/
lemma mem_fvoc_iff {L : Finset Formula} {x} : x ∈ L.fvoc ↔ ∃ φ ∈ L, x ∈ φ.voc :=
  Finset.mem_fvoc

/-- Since sequents now use `Finset`s, being "set equal" is just being equal. -/
lemma Sequent.left_fvoc_eq_of_eq {X Y : Sequent} (h : X = Y) :
    X.left.fvoc = Y.left.fvoc := by rw [h]

/-- Since sequents now use `Finset`s, being "set equal" is just being equal. -/
lemma Sequent.right_fvoc_eq_of_eq {X Y : Sequent} (h : X = Y) :
    X.right.fvoc = Y.right.fvoc := by rw [h]

/-- A local rule application does not increase the vocabulary of the left component.
This is the left half of `localRuleApp_does_not_increase_jvoc`. -/
lemma LocalRuleApp.left_fvoc_subset (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.left.fvoc ⊆ lra.X.left.fvoc := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Lsub := localRule_does_not_increase_vocab_L lrule _ res_in
    simp only [Sequent.left_eq] at Lsub
    have hcond : ∀ y ∈ (Lcond ∪ Ocond.L).fvoc, y ∈ L.fvoc ∨ y ∈ O.L.fvoc := by
      intro y hy
      rw [Finset.fvoc_union, Finset.mem_union] at hy
      rcases hy with h | h
      · exact Or.inl (Finset.fvoc_mono preconditionProof.1 h)
      · exact Or.inr (Finset.fvoc_mono (Olf.L_subset_of_subset preconditionProof.2.2) h)
    have hres : ∀ y ∈ (Lres ∪ Ores.L).fvoc, y ∈ L.fvoc ∨ y ∈ O.L.fvoc :=
      fun y hy => hcond y (Lsub hy)
    intro x x_in
    simp only [LocalRuleApp.X, Sequent.left_eq, Finset.fvoc_union, Finset.mem_union] at x_in ⊢
    rcases x_in with (h | h) | h
    · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
    · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
    · rcases Ores with _ | z
      · refine Or.inr (Finset.fvoc_mono ?_ h)
        simpa only [Olf.change, Option.overwrite] using Olf.L_sdiff_subset
      · rw [Olf.change_some] at h
        exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- A local rule application does not increase the vocabulary of the right component.
This is the right half of `localRuleApp_does_not_increase_jvoc`. -/
lemma LocalRuleApp.right_fvoc_subset (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.right.fvoc ⊆ lra.X.right.fvoc := by
  match lra with
  | @LocalRuleApp.mk L R O Lcond Rcond Ocond ress lrule C hC preconditionProof =>
    subst hC
    rintro ⟨cL, cR, cO⟩ C_in
    simp only [applyLocalRule, Finset.mem_image] at C_in
    rcases C_in with ⟨⟨Lres, Rres, Ores⟩, res_in, def_c⟩
    simp only at def_c
    cases def_c
    have Rsub := localRule_does_not_increase_vocab_R lrule _ res_in
    simp only [Sequent.right_eq] at Rsub
    have hcond : ∀ y ∈ (Rcond ∪ Ocond.R).fvoc, y ∈ R.fvoc ∨ y ∈ O.R.fvoc := by
      intro y hy
      rw [Finset.fvoc_union, Finset.mem_union] at hy
      rcases hy with h | h
      · exact Or.inl (Finset.fvoc_mono preconditionProof.2.1 h)
      · exact Or.inr (Finset.fvoc_mono (Olf.R_subset_of_subset preconditionProof.2.2) h)
    have hres : ∀ y ∈ (Rres ∪ Ores.R).fvoc, y ∈ R.fvoc ∨ y ∈ O.R.fvoc :=
      fun y hy => hcond y (Rsub hy)
    intro x x_in
    simp only [LocalRuleApp.X, Sequent.right_eq, Finset.fvoc_union, Finset.mem_union] at x_in ⊢
    rcases x_in with (h | h) | h
    · exact Or.inl (Finset.fvoc_mono Finset.sdiff_subset h)
    · exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inl h)
    · rcases Ores with _ | z
      · refine Or.inr (Finset.fvoc_mono ?_ h)
        simpa only [Olf.change, Option.overwrite] using Olf.R_sdiff_subset
      · rw [Olf.change_some] at h
        exact hres x (by rw [Finset.fvoc_union, Finset.mem_union]; exact Or.inr h)

/-- Inside a local tableau the vocabulary of the left component only shrinks. -/
lemma LocalPathIn.last_left_fvoc_subset : ∀ {X : Sequent} {lt : LocalTableau X}
    (lp : LocalPathIn lt), lp.last.left.fvoc ⊆ X.left.fvoc
  | _, _, .nil => by simp [LocalPathIn.last]
  | _, .byLocalRule lra X_def next, .cons Y_in tail => by
      simp only [LocalPathIn.last]
      exact subset_trans (LocalPathIn.last_left_fvoc_subset tail)
        (X_def ▸ lra.left_fvoc_subset _ Y_in)

/-- Inside a local tableau the vocabulary of the right component only shrinks. -/
lemma LocalPathIn.last_right_fvoc_subset : ∀ {X : Sequent} {lt : LocalTableau X}
    (lp : LocalPathIn lt), lp.last.right.fvoc ⊆ X.right.fvoc
  | _, _, .nil => by simp [LocalPathIn.last]
  | _, .byLocalRule lra X_def next, .cons Y_in tail => by
      simp only [LocalPathIn.last]
      exact subset_trans (LocalPathIn.last_right_fvoc_subset tail)
        (X_def ▸ lra.right_fvoc_subset _ Y_in)

lemma endNodesOf_left_fvoc_subset : ∀ {X : Sequent} (lt : LocalTableau X),
    ∀ Y ∈ endNodesOf lt, Y.left.fvoc ⊆ X.left.fvoc
  | _, .sim _, Y, hY => by rw [mem_endNodesOf_sim] at hY; simp [hY]
  | _, .byLocalRule lra X_def next, Y, hY => by
      obtain ⟨Z, Z_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact subset_trans (endNodesOf_left_fvoc_subset _ Y hY) (X_def ▸ lra.left_fvoc_subset _ Z_in)

lemma endNodesOf_right_fvoc_subset : ∀ {X : Sequent} (lt : LocalTableau X),
    ∀ Y ∈ endNodesOf lt, Y.right.fvoc ⊆ X.right.fvoc
  | _, .sim _, Y, hY => by rw [mem_endNodesOf_sim] at hY; simp [hY]
  | _, .byLocalRule lra X_def next, Y, hY => by
      obtain ⟨Z, Z_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact subset_trans (endNodesOf_right_fvoc_subset _ Y hY)
        (X_def ▸ lra.right_fvoc_subset _ Z_in)

lemma projection_fvoc_subset (A : Nat) (L : Finset Formula) :
    (Finset.projection A L).fvoc ⊆ L.fvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  exact ⟨⌈·A⌉ψ, Finset.mem_projection.mp hψ, by simp; tauto⟩

/-- A PDL rule does not increase the vocabulary of the left component. -/
lemma PdlRule.left_fvoc_subset {X Y : Sequent} (r : PdlRule X Y) :
    Y.left.fvoc ⊆ X.left.fvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  cases r
  case loadR L R δ α φ hin hnb hY =>
    subst hY; simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case freeR L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case loadL L δ α φ R hin hnb hY =>
    subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Finset.mem_of_mem_erase hψ, hx⟩
    · exact ⟨_, hin, by simpa [LoadFormula.unload] using hx⟩
  case freeL L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Or.inl hψ, hx⟩
    · exact ⟨_, Or.inr rfl, by simpa [LoadFormula.unload] using hx⟩
  case modL L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.left_eq, Olf.L_none, Olf.L_inl, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    · rcases hψ with rfl | hψ
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
    · rcases hψ with hψ | rfl
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
  case modR L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.left_eq, Olf.L_none, Olf.L_inr, Finset.union_empty] at hψ ⊢
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩

/-- A PDL rule does not increase the vocabulary of the right component. -/
lemma PdlRule.right_fvoc_subset {X Y : Sequent} (r : PdlRule X Y) :
    Y.right.fvoc ⊆ X.right.fvoc := by
  intro x hx
  rw [mem_fvoc_iff] at hx ⊢
  obtain ⟨ψ, hψ, hx⟩ := hx
  cases r
  case loadL L δ α φ R hin hnb hY =>
    subst hY; simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case freeL L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    exact ⟨ψ, hψ, hx⟩
  case loadR R δ α φ L hin hnb hY =>
    subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Finset.mem_of_mem_erase hψ, hx⟩
    · exact ⟨_, hin, by simpa [LoadFormula.unload] using hx⟩
  case freeR L R δ α φ hX hY =>
    subst hX; subst hY
    simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
      Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    rcases hψ with hψ | rfl
    · exact ⟨ψ, Or.inl hψ, hx⟩
    · exact ⟨_, Or.inr rfl, by simpa [LoadFormula.unload] using hx⟩
  case modR L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.right_eq, Olf.R_none, Olf.R_inr, Finset.union_empty,
        Finset.mem_union, Finset.mem_singleton] at hψ ⊢
    · rcases hψ with rfl | hψ
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
    · rcases hψ with hψ | rfl
      · exact ⟨_, Or.inl (Finset.mem_projection.mp hψ), by simp; tauto⟩
      · exact ⟨_, Or.inr rfl, by simp [LoadFormula.unload] at hx ⊢; tauto⟩
  case modL L R A ξ hX hY =>
    subst hX
    cases ξ <;> subst hY <;>
      simp only [Sequent.right_eq, Olf.R_none, Olf.R_inl, Finset.union_empty] at hψ ⊢
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩
    · exact ⟨_, Finset.mem_projection.mp hψ, by simp; tauto⟩

lemma edge_left_fvoc_subset {H : History} {Z : Sequent} {tab' : Tableau H Z} {s t : PathIn tab'}
    (h : s ⋖_ t) : (nodeAt t).left.fvoc ⊆ (nodeAt s).left.fvoc := by
  rcases nodeAt_of_edge h with ⟨lt, hlt⟩ | hr
  · exact endNodesOf_left_fvoc_subset lt _ hlt
  · obtain ⟨r⟩ := hr
    exact r.left_fvoc_subset

lemma edge_right_fvoc_subset {H : History} {Z : Sequent} {tab' : Tableau H Z} {s t : PathIn tab'}
    (h : s ⋖_ t) : (nodeAt t).right.fvoc ⊆ (nodeAt s).right.fvoc := by
  rcases nodeAt_of_edge h with ⟨lt, hlt⟩ | hr
  · exact endNodesOf_right_fvoc_subset lt _ hlt
  · obtain ⟨r⟩ := hr
    exact r.right_fvoc_subset

lemma cEdge_left_fvoc_subset {s t : PathIn tab} (h : s ◃ t) :
    (nodeAt t).left.fvoc ⊆ (nodeAt s).left.fvoc := by
  rcases h with h | ⟨lpr, hs, rfl⟩
  · exact edge_left_fvoc_subset h
  · exact le_of_eq (Sequent.left_fvoc_eq_of_eq (nodeAt_companionOf_setEq s lpr hs))

lemma cEdge_right_fvoc_subset {s t : PathIn tab} (h : s ◃ t) :
    (nodeAt t).right.fvoc ⊆ (nodeAt s).right.fvoc := by
  rcases h with h | ⟨lpr, hs, rfl⟩
  · exact edge_right_fvoc_subset h
  · exact le_of_eq (Sequent.right_fvoc_eq_of_eq (nodeAt_companionOf_setEq s lpr hs))

/-- Lemma 8.10, left component: along `◃` the vocabulary only shrinks. -/
lemma cReach_left_fvoc_subset {s t : PathIn tab} (h : s ◃* t) :
    (nodeAt t).left.fvoc ⊆ (nodeAt s).left.fvoc := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hst IH => exact subset_trans (cEdge_left_fvoc_subset hst) IH

/-- Lemma 8.10, right component: along `◃` the vocabulary only shrinks. -/
lemma cReach_right_fvoc_subset {s t : PathIn tab} (h : s ◃* t) :
    (nodeAt t).right.fvoc ⊆ (nodeAt s).right.fvoc := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hst IH => exact subset_trans (cEdge_right_fvoc_subset hst) IH

/-- Lemma 8.10 combination of both components. Not used directly. -/
lemma cReach_fvoc_subset {s t : PathIn tab} (h : s ◃* t) :
    (nodeAt t).left.fvoc ⊆ (nodeAt s).left.fvoc ∧
    (nodeAt t).right.fvoc ⊆ (nodeAt s).right.fvoc :=
  ⟨ cReach_left_fvoc_subset h
  , cReach_right_fvoc_subset h ⟩

/-- The label of a fine node has a smaller vocabulary than the coarse node it lies in. -/
lemma FinePathIn.label_left_fvoc_subset_base : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'),
    f.label.left.fvoc ⊆ (nodeAt f.base).left.fvoc
  | _, _, _, .inLoc lp _ => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        LocalPathIn.last_left_fvoc_subset lp
  | _, _, _, .pdlHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .lrepHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .loc Y_in tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_left_fvoc_subset_base tail
  | _, _, _, .pdl tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_left_fvoc_subset_base tail

lemma FinePathIn.label_right_fvoc_subset_base : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'),
    f.label.right.fvoc ⊆ (nodeAt f.base).right.fvoc
  | _, _, _, .inLoc lp _ => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        LocalPathIn.last_right_fvoc_subset lp
  | _, _, _, .pdlHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .lrepHere => by simp [FinePathIn.label, FinePathIn.base, nodeAt, tabAt]
  | _, _, _, .loc Y_in tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_right_fvoc_subset_base tail
  | _, _, _, .pdl tail => by
      simpa [FinePathIn.label, FinePathIn.base, nodeAt, tabAt] using
        FinePathIn.label_right_fvoc_subset_base tail

end VocPreservation

/-! ### Right rules do not change the left component

The two "right" local rules only act on the right component and on a loaded formula on the
right, so they leave the left component of the sequent unchanged.  The `(M)` rule does
change the left component, but it is a `Tableau.pdl` step and hence only applies to a basic
sequent, whose right component is then basic as well. -/

section RightRules

lemma LocalRuleApp.left_eq_of_isRightRule (lra : LocalRuleApp) (h : lra.isRightRule) :
    ∀ Y ∈ lra.C, Y.left = lra.X.left := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  cases lr
  case oneSidedR Rres orule YS_def =>
    intro Y hY
    exact oneSidedR_preserves_left (LRO := (L,R,O)) pre.2.1 orule YS_def Y hY
  case loadedR χ lrule YS_def =>
    intro Y hY
    refine loadedR_preserves_left (LRO := (L,R,O)) χ ?_ lrule YS_def Y hY
    exact (Option.some_subseteq.mp pre.2.2).symm
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- The right component of a basic sequent is basic. -/
lemma Sequent.basic_rightOnly {X : Sequent} (h : X.basic) : X.rightOnly.basic := by
  rcases X with ⟨L, R, O⟩
  obtain ⟨hb, hc⟩ := h
  constructor
  · intro f hf
    apply hb
    simp only [Sequent.rightOnly, Sequent.toFinset, Finset.empty_union, Finset.mem_union] at hf ⊢
    tauto
  · intro hcl
    apply hc
    rcases hcl with hbot | ⟨f, hf, hnf⟩
    · left
      revert hbot
      simp_all [Sequent.rightOnly, Sequent.L, Sequent.R]
    · right
      refine ⟨f, ?_, ?_⟩ <;>
        simp_all [Sequent.rightOnly, Sequent.L, Sequent.R]

/-- Where a right rule is applied, it is either a local rule or the node is basic (because
the `(M)` rule is only applied at basic nodes). -/
lemma FinePathIn.lra_or_basic_of_usesRightRule : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), f.usesRightRule →
      (∃ lra, f.lra? = some lra ∧ lra.isRightRule) ∨ f.label.basic
  | _, _, _, .inLoc lp hint, h => by
      simp only [FinePathIn.usesRightRule, FinePathIn.lra?] at h ⊢
      rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
      · rw [hlt] at h
        exact Or.inl ⟨lra, rfl, h⟩
      · rw [hlt] at h; simp at h
  | _, _, .pdl _ bas _ _, .pdlHere, _ => Or.inr bas
  | _, _, _, .lrepHere, h => by simp [FinePathIn.usesRightRule] at h
  | _, _, _, .loc Y_in tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lra?, FinePathIn.label] using
        FinePathIn.lra_or_basic_of_usesRightRule tail h
  | _, _, _, .pdl tail, h => by
      simp only [FinePathIn.usesRightRule] at h
      simpa [FinePathIn.lra?, FinePathIn.label] using
        FinePathIn.lra_or_basic_of_usesRightRule tail h

/-- At a node where a right rule is applied to a non-basic right component, all children
have the same left component as the node itself. -/
lemma FinePathIn.children_left_eq_of_usesRightRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (hr : f.usesRightRule)
    (hb : ¬ f.label.rightOnly.basic) : ∀ g ∈ f.children, g.label.left = f.label.left := by
  rcases f.lra_or_basic_of_usesRightRule hr with ⟨lra, hlra, hright⟩ | hbas
  · obtain ⟨hX, hC⟩ := f.lra?_spec hlra
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact lra.left_eq_of_isRightRule hright _ hmem
  · exact absurd (Sequent.basic_rightOnly hbas) hb

/-- A right local rule cannot be applied when the right component of the sequent is basic:
the rule only looks at the right component and at a loaded formula on the right, so it
would also be applicable to the sequent with an empty left component. -/
lemma LocalRuleApp.not_rightOnly_basic_of_isRightRule (lra : LocalRuleApp)
    (h : lra.isRightRule) : ¬ lra.X.rightOnly.basic := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr
  case oneSidedR ress orule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, Rcond, none, _, LocalRule.oneSidedR orule YS_def, _, rfl,
        ⟨Finset.empty_subset _, pre.2.1, by simp⟩⟩
    simpa [Sequent.rightOnly] using this
  case loadedR χ lrule YS_def =>
    have := nonbasic_of_localRuleApp
      ⟨∅, R, O, ∅, ∅, some (Sum.inr (~'χ)), _, LocalRule.loadedR χ lrule YS_def, _, rfl,
        ⟨Finset.empty_subset _, Finset.empty_subset _, pre.2.2⟩⟩
    simpa [Sequent.rightOnly] using this
  all_goals
    simp [LocalRuleApp.isRightRule, LocalRule.isRightRule] at h

/-- The right component of the child obtained by applying the modal rule `(M)` to a sequent
whose loaded formula `~⌊·A⌋ξ` is on the right. Note that it only depends on `A`, on `ξ` and
on the right component `R` of the sequent, and hence only on `Λ₂` of the node. -/
def modRChildRightOnly (A : Nat) (ξ : AnyFormula) (R : Finset Formula) : Sequent :=
  match ξ with
  | .normal φ => ⟨∅, {~φ} ∪ Finset.projection A R, none⟩
  | .loaded χ => ⟨∅, Finset.projection A R, some (Sum.inr (~'χ))⟩

/-- At a fine node with a *basic* right component where a right rule is applied, that rule
is one of the three `PdlRule`s acting on the right — and in particular the node is a node
in the coarse sense. The three cases are `(L+)`, where the node is free, `(L-)`, whose
unique child is free, and the modal rule `(M)`, whose unique child has the projected left
component and a right component determined by `Λ₂` of the node. -/
lemma FinePathIn.basicRightStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesRightRule) (hb : f.label.rightOnly.basic) :
      (f.atBigRoot ∧ f.label.2.2 = none)
      ∨ (∃ g, f.children = {g} ∧ g.atBigRoot ∧ g.label.2.2 = none)
      ∨ (∃ A ξ, f.label.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, f.children = {g} ∧ g.atBigRoot
          ∧ g.label.left = Finset.projection A f.label.left
          ∧ g.label.rightOnly = modRChildRightOnly A ξ f.label.2.1) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesRightRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [FinePathIn.label] at hb
      rw [X_def] at hb
      exact absurd hb (lra.not_rightOnly_basic_of_isRightRule h)
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label, FinePathIn.children, FinePathIn.atBigRoot]
    cases r with
    | loadR hmem hnb hY => exact Or.inl ⟨trivial, rfl⟩
    | freeR hX hY =>
      exact Or.inr (Or.inl ⟨_, rfl, by simp [FinePathIn.atBigRoot],
        by simp [FinePathIn.label, hY]⟩)
    | @modR Y' L R A X' ξ hX hY =>
      subst hX
      right; right
      refine ⟨A, ξ, rfl, _, rfl, by simp [FinePathIn.atBigRoot], ?_, ?_⟩ <;>
        cases ξ <;> simp_all [modRChildRightOnly, Sequent.rightOnly, FinePathIn.label]
    | _ => simp [PdlRule.isRightRule] at h
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.loc Y_in g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .loc Y_in g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simp only [FinePathIn.label] at hb ⊢
    simp only [FinePathIn.children, FinePathIn.atBigRoot]
    rcases IH h hb with ⟨hbr, h1⟩ | ⟨g, hg, hgbr, hg2⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
    · exact Or.inl ⟨hbr, h1⟩
    · exact Or.inr (Or.inl ⟨.pdl g, by simp [hg], by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg2⟩)
    · exact Or.inr (Or.inr ⟨A, ξ, hA, .pdl g, by simp [hg],
        by simpa [FinePathIn.atBigRoot] using hgbr,
        by simpa [FinePathIn.label] using hg1, by simpa [FinePathIn.label] using hg2⟩)

/-- A fine node that is a node in the coarse sense has the label of that coarse node. -/
lemma FinePathIn.label_eq_nodeAt_base {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.atBigRoot) : f.label = nodeAt f.base := by
  have := congrArg FinePathIn.label (f.eq_toFine_base_of_atBigRoot h)
  rwa [PathIn.label_toFine] at this

/-! ### Left rules do not change the right component

Dually, a left local rule leaves the right component of the sequent unchanged, provided the
loaded formula is on the right (otherwise the `(¬)` rule for the loaded formula on the left
would change the `Olf`). The left `PdlRule`s `(L+)`, `(L-)` and `(M)` are all only
applicable when the loaded formula is *not* on the right. -/

lemma LocalRuleApp.rightOnly_eq_of_isLeftRule (lra : LocalRuleApp) (h : lra.isLeftRule)
    (hR : lra.O.isRight) : ∀ Y ∈ lra.C, Y.rightOnly = lra.X.rightOnly := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  replace hR : O.isRight := hR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    intro Y hY
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Ln, -, rfl⟩ := hres
    simp [Sequent.rightOnly, Olf.change]
  case loadedL χ lrule YS_def =>
    exfalso
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    rw [hO] at hR
    simp at hR
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule] at h

/-- Where a left rule is applied, it is a local rule, unless the loaded formula is not on
the right (which for a node of a `LoadedCluster` cannot happen). -/
lemma FinePathIn.leftRuleStep {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesLeftRule) :
    (∃ lra, f.lra? = some lra ∧ lra.isLeftRule) ∨ (f.atBigRoot ∧ ¬ f.label.2.2.isRight) := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp hint =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at h
      exact Or.inl ⟨lra, by simp only [FinePathIn.lra?, hlt], h⟩
    · rw [hlt] at h; simp at h
  | @pdlHere Hist X Y nrep bas r next =>
    simp only [FinePathIn.usesLeftRule] at h
    right
    refine ⟨by simp [FinePathIn.atBigRoot], ?_⟩
    simp only [FinePathIn.label]
    cases r with
    | loadL hmem hnb hY => simp
    | freeL hX hY => subst hX; simp
    | modL hX hY => subst hX; simp
    | _ => simp [PdlRule.isLeftRule] at h
  | lrepHere => simp [FinePathIn.usesLeftRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases IH h with ⟨lra, h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lra, by simpa [FinePathIn.lra?] using h1, h2⟩
    · exact Or.inr ⟨by simpa [FinePathIn.atBigRoot] using h1, by simpa [FinePathIn.label] using h2⟩
  | pdl tail IH =>
    simp only [FinePathIn.usesLeftRule] at h
    rcases IH h with ⟨lra, h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨lra, by simpa [FinePathIn.lra?] using h1, h2⟩
    · exact Or.inr ⟨by simpa [FinePathIn.atBigRoot] using h1, by simpa [FinePathIn.label] using h2⟩

/-- Part of Lemma 9.7 (c): at a node with the loaded formula on the right where a left rule
is applied, all children have the same right component as the node itself. -/
lemma FinePathIn.children_rightOnly_eq_of_usesLeftRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.usesLeftRule) (hR : f.label.2.2.isRight) :
    ∀ g ∈ f.children, g.label.rightOnly = f.label.rightOnly := by
  rcases f.leftRuleStep h with ⟨lra, hlra, hleft⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lra?_spec hlra
    rw [hX] at hR
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact lra.rightOnly_eq_of_isLeftRule hleft hR _ hmem
  · exact absurd hR hno

/-- Local invertibility of a left rule, for the left component only: if the left component
of the premise holds at a world, then so does the left component of one of the conclusions.

Note that `localRuleTruth` does not give this, since it also speaks about the right
component, which need not hold at the world in question. That the loaded formula is on the
right is needed to exclude the rule for a loaded formula on the left. -/
lemma LocalRuleApp.left_sat_of_isLeftRule {lra : LocalRuleApp} (hl : lra.isLeftRule)
    (hR : lra.O.isRight) {W : Type} {M : KripkeModel W} {w : W}
    (hw : ∀ φ ∈ lra.X.left, evaluate M w φ) :
    ∃ Y ∈ lra.C, ∀ φ ∈ Y.left, evaluate M w φ := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  simp only [LocalRuleApp.X, Sequent.left_eq] at hw hl hR ⊢
  cases lr
  case oneSidedL ress' orule YS_def =>
    subst YS_def
    subst hC
    have hcon : evaluate M w (con Lcond.fsort) :=
      conEval.mpr (fun f hf =>
        hw f (Finset.mem_union_left _ (pre.1 (Formula.mem_fsort.mp hf))))
    have hdis := (oneSidedLocalRuleTruth orule W M w).mp hcon
    rw [Finset.disconEval] at hdis
    obtain ⟨res, hres, hresw⟩ := hdis
    refine ⟨(L \ Lcond ∪ res, R \ ∅ ∪ ∅, Olf.change O none none), ?_, ?_⟩
    · simp only [applyLocalRule, Finset.image_image, Finset.mem_image, Function.comp_apply]
      exact ⟨res, hres, rfl⟩
    · intro f hf
      simp only [Sequent.left_eq, Finset.mem_union, Olf.change_old_none_none] at hf
      rcases hf with (hf | hf) | hf
      · exact hw f (Finset.mem_union_left _ (Finset.sdiff_subset hf))
      · exact hresw f hf
      · exact hw f (Finset.mem_union_right _ hf)
  case loadedL χ lrule YS_def =>
    exfalso
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    rw [hO] at hR
    simp at hR
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRule.isLeftRule] at hl

/-- Local invertibility at a fine node where a left rule is applied, for the left component
only: if a formula follows from the left component of every child, then it follows from the
left component of the node itself. -/
lemma FinePathIn.leftEntails_of_children_of_usesLeftRule {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.usesLeftRule)
    (hR : f.label.2.2.isRight) {φ : Formula}
    (hch : ∀ g ∈ f.children, g.leftEntails φ) : f.leftEntails φ := by
  rcases f.leftRuleStep h with ⟨lra, hlra, hleft⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lra?_spec hlra
    intro W M w hw
    rw [hX] at hR hw
    obtain ⟨Y, hY, hYw⟩ := lra.left_sat_of_isLeftRule hleft hR hw
    have hmem : Y ∈ f.children.image FinePathIn.label := by
      rw [hC]; exact hY
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hmem
    exact hch g hg W M w hYw
  · exact absurd hR hno

end RightRules

/-! ### Loading on the right is inherited upwards, and rules with children are left or right

Two ingredients for the descent of Lemma 9.7 (d) below. First, a fine node that has a
coarse child loaded on the right is itself loaded on the right — this is what lets us apply
`FinePathIn.children_rightOnly_eq_of_usesLeftRule` at the fine nodes of a cluster. Second,
a fine node with children applies a left or a right rule: the only local rules that are
neither are the closing rules, and those have no children. -/

section UpwardsRight

/-- If a child of a local rule application is loaded on the right, then so is its premise.
The local rules for a loaded formula on the *left* never produce a loading on the right,
and the one-sided rules do not change the loaded formula at all. -/
lemma LocalRuleApp.isRight_of_mem_C (lra : LocalRuleApp) :
    ∀ Y ∈ lra.C, Y.2.2.isRight → lra.X.2.2.isRight := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  intro Y hY hYR
  cases lr
  case oneSidedL ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Ln, -, rfl⟩ := hres
    simpa [Olf.change] using hYR
  case oneSidedR ress orule YS_def =>
    subst YS_def
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨Rn, -, rfl⟩ := hres
    simpa [Olf.change] using hYR
  case LRnegL => simp [applyLocalRule] at hY
  case LRnegR => simp [applyLocalRule] at hY
  case loadedL χ lrule YS_def =>
    exfalso
    subst YS_def
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp only [applyLocalRule, Finset.mem_image] at hY
    obtain ⟨res, hres, rfl⟩ := hY
    obtain ⟨⟨Lnew, Onew⟩, -, rfl⟩ := hres
    rcases Onew with _ | o <;> simp_all [Olf.isRight, Olf.change]
  case loadedR χ lrule YS_def =>
    have hO := (Option.some_subseteq.mp pre.2.2).symm
    subst hO
    simp [Olf.isRight]

/-- If some end node of a local tableau is loaded on the right, then so is its root. -/
lemma LocalTableau.isRight_of_mem_endNodesOf : ∀ {Z : Sequent} (lt : LocalTableau Z),
    ∀ Y ∈ endNodesOf lt, Y.2.2.isRight → Z.2.2.isRight
  | _, .sim _, Y, hY, hYR => by
      rw [mem_endNodesOf_sim] at hY
      exact hY ▸ hYR
  | _, .byLocalRule lra X_def next, Y, hY, hYR => by
      subst X_def
      obtain ⟨W, W_in, hY⟩ := mem_endNodesOf_byLocalRule_iff.mp hY
      exact lra.isRight_of_mem_C W W_in
        (LocalTableau.isRight_of_mem_endNodesOf (next W W_in) Y hY hYR)

/-- The end nodes below a local path are end nodes of the local tableau at that path. -/
lemma LocalPathIn.mem_endNodesOf_ltAt {Z : Sequent} {lt : LocalTableau Z}
    (lp : LocalPathIn lt) :
    ∀ Yh ∈ lp.endNodesBelow, (Yh : Sequent) ∈ endNodesOf lp.ltAt := by
  induction lp with
  | nil => intro Yh _; exact Yh.2
  | cons Y_in tail IH =>
    intro Yh h
    simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h
    obtain ⟨Z, hZ, hmem, rfl⟩ := h
    exact IH ⟨Z, hZ⟩ hmem

/-- A fine node that is not a coarse node and has a coarse child loaded on the right is
itself loaded on the right. (For coarse nodes this is false: the `(L+)` rule loads a free
node.) -/
lemma FinePathIn.isRight_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      ∀ q ∈ f.coarseChildrenBelow, (nodeAt q).2.2.isRight → f.label.2.2.isRight
  | _, _, _, .inLoc lp _, _, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, hmem, rfl⟩ := hq
      rw [nodeAt_loc_nil] at hqR
      exact LocalTableau.isRight_of_mem_endNodesOf lp.ltAt Y
        (lp.mem_endNodesOf_ltAt ⟨Y, Y_in⟩ hmem) hqR
  | _, _, _, .pdlHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _, _, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_loc] at hqR
      exact tail.isRight_of_mem_coarseChildrenBelow
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR
  | _, _, _, .pdl tail, hbr, q, hq, hqR => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rw [nodeAt_pdl] at hqR
      exact tail.isRight_of_mem_coarseChildrenBelow
        (by simpa [FinePathIn.atBigRoot] using hbr) q' hq' hqR

/-- A local rule application with at least one child is a left or a right rule: only the
closing rules `(¬)` are neither, and they have no results. -/
lemma LocalRuleApp.isLeftRule_or_isRightRule_of_C_ne_empty (lra : LocalRuleApp)
    (h : lra.C ≠ ∅) : lra.isLeftRule ∨ lra.isRightRule := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  subst hC
  cases lr
  case LRnegL => simp [applyLocalRule] at h
  case LRnegR => simp [applyLocalRule] at h
  all_goals
    simp [LocalRuleApp.isLeftRule, LocalRuleApp.isRightRule, LocalRule.isLeftRule,
      LocalRule.isRightRule]

/-- A fine node that has children applies a left or a right rule. -/
lemma FinePathIn.usesLeftRule_or_usesRightRule_of_children_ne_empty {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab') (h : f.children ≠ ∅) :
    f.usesLeftRule ∨ f.usesRightRule := by
  induction f with
  | @inLoc Hist Y nrep nbas lt next lp lp_int =>
    have hlp : lp.children ≠ ∅ := by
      intro hnil
      exact h (by simp [FinePathIn.children, hnil])
    have hlab : lp.ltAt.childLabels ≠ ∅ := by
      rw [← lp.map_last_children]
      simpa using hlp
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    rcases hlt : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [hlt] at hlab
      exact lra.isLeftRule_or_isRightRule_of_C_ne_empty
        (by simpa [LocalTableau.childLabels] using hlab)
    · exfalso
      unfold LocalPathIn.isInternal at lp_int
      rw [hlt] at lp_int
      simp [LocalTableau.hasRule] at lp_int
  | @pdlHere _ _ _ _ _ r _ =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    cases r <;> simp [PdlRule.isLeftRule, PdlRule.isRightRule]
  | lrepHere => simp [FinePathIn.children] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    exact IH (by intro hnil; exact h (by simp [FinePathIn.children, hnil]))
  | pdl tail IH =>
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule]
    exact IH (by intro hnil; exact h (by simp [FinePathIn.children, hnil]))

end UpwardsRight

/-! ### Loaded-path repeats and the Dershowitz-Manna measure

The three lemmas here are what replaces the paper's Fact `lprAreCritical` in the proof of
Lemma 9.7 (d) below: instead of showing that the modal rule is applied between a companion
and its repeat we show that going down along *left* rules strictly decreases the
Dershowitz-Manna measure of the label, while a companion carries exactly the same label as
its repeat. -/

section LrepAndMeasure

/-- A node where a rule is applied is not a loaded-path repeat.
This would better belong next to `edge` in `Pdl/TableauPath.lean`. -/
lemma PathIn.not_isLrep_of_edge {s t : PathIn tab} (h : s ⋖_ t) : ¬ s.isLrep := by
  unfold PathIn.isLrep
  rcases h with ⟨_, _, _, _, _, _, _, _, hs, -⟩ | ⟨_, _, _, _, _, _, _, hs, -⟩ <;>
    rw [hs] <;> simp [Tableau.isLrep]

/-- A fine node whose base is a loaded-path repeat is that coarse node itself, because a
loaded-path repeat is a leaf and hence has no local tableau with internal nodes.
This would better belong next to `atBigRoot` in `Pdl/Interpolation/FinePath.lean`. -/
lemma FinePathIn.atBigRoot_of_base_isLrep {H Z} {tab' : Tableau H Z} (f : FinePathIn tab')
    (h : f.base.isLrep) : f.atBigRoot := by
  induction f with
  | inLoc lp lp_int => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep] at h
  | pdlHere => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep] at h
  | lrepHere => simp [FinePathIn.atBigRoot]
  | loc Y_in tail IH =>
    simpa [FinePathIn.atBigRoot] using IH (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)
  | pdl tail IH =>
    simpa [FinePathIn.atBigRoot] using IH (by simpa [FinePathIn.base, PathIn.isLrep, tabAt] using h)

/-- Where a left rule is applied at a node with the loaded formula on the right, the labels
of all children are strictly smaller in the Dershowitz-Manna ordering: by
`FinePathIn.leftRuleStep` the rule applied there is a local rule, and local rules decrease
the measure. -/
lemma FinePathIn.children_lt_Sequent_of_usesLeftRule {H Z} {tab' : Tableau H Z}
    (f : FinePathIn tab') (h : f.usesLeftRule) (hR : f.label.2.2.isRight) :
    ∀ g ∈ f.children, lt_Sequent g.label f.label := by
  rcases f.leftRuleStep h with ⟨lra, hlra, -⟩ | ⟨-, hno⟩
  · obtain ⟨hX, hC⟩ := f.lra?_spec hlra
    intro g hg
    have hmem : g.label ∈ lra.C := by
      rw [← hC]; exact Finset.mem_image_of_mem FinePathIn.label hg
    rw [hX]
    exact localRuleApp.decreases_DM lra _ hmem
  · exact absurd hR hno

end LrepAndMeasure
