import Pdl.Interpolation.PreInterpolant
import Pdl.Interpolation.RuleFacts

/-! # Facts about a proper cluster (Section 9 of the paper)

This file proves the facts about a proper loaded cluster `C` that the proofs of
Lemma 10.1 (`Pdl.ClusterItp`) and Lemma 10.3 (`Pdl.ClusterRho`) use:

* `LoadedCluster.exists_right_of_proper` is Lemma 9.7 (d): if `C_Δ` is non-empty then so
  is `C^R_Δ`;
* `LoadedCluster.vocL_fineCLplus` and `LoadedCluster.vocR_fineCLplus` say that the
  vocabulary of both components only shrinks along the tableau, applied to the nodes of
  `C⁺`, all of which are below the root `r` of the cluster;
* `LoadedCluster.loadedProgVoc_of_proper` says that the leading atomic program `a` of the
  loaded formula of a basic `Δ ∈ Λ₂[C]` is in the joint vocabulary of the root;
* `LoadedCluster.leftPropagation_of_proper` is the inner induction in the proof of
  Lemma 10.3;
* `LoadedCluster.rightRuleChildren_of_uniform` is Lemma 9.7 (f) — the only place where
  uniformity of the tableau is needed;
* `LoadedCluster.modalStep_of` is Lemma 9.7 (e) in the semantic form used in the proof of
  Lemma 10.3.

All of them are proved from properness of the cluster, which is part of `LoadedCluster`,
except for `rightRuleChildren_of_uniform` which also needs
`LoadedCluster.HasUniformSteps`.

The facts about the rules of the tableau that they rely on are in `Pdl.RuleFacts`.
-/

open HasSat

variable {X : Sequent} {tab : Tableau .nil X}

/-! ### The two standing assumptions of the paper

The paper fixes a *uniform* closed tableau and a *proper* cluster in it, and both assumptions
are used in Section 9.  Neither of them holds for an arbitrary values of the `Tableau` type.

* the `Tableau` type does not force any coherence between the rules applied at different
  nodes, whereas uniformity (U1/U2) makes the rule applied at a node with a loaded,
  non-basic right component depend only on that component.

This is captured in the form needed here in `LoadedCluster.HasUniformSteps`.

Note that this file never *unfolds* `LoadedCluster.HasUniformSteps`: it is only used
opaquely, as the hypothesis of `LoadedCluster.stepOf_spec` and as the conclusion of
`LoadedCluster.uniformOfUniTab`.  So the definition of `HasUniformSteps` may still be
changed (for example from a `List` comparison to a `Finset.image` one) without affecting
anything here, as long as those two statements are kept.
-/

namespace LoadedCluster

/-! ### The vocabulary fields -/

/-- Every fine node of `C⁺` is `◃`-reachable from the root of the cluster. -/
lemma root_cReach_base_of_mem_fineCLplus (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineCLplus) : C.root ◃* f.base := by
  rcases Finset.mem_union.mp hf with hf | hf
  · exact C.root_reaches_all _ ((C.mem_fineCL f).mp (List.mem_toFinset.mp hf)).1
  · simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset] at hf
    obtain ⟨⟨g, hg, hfg⟩, -⟩ := hf
    have hgr : C.root ◃* g.base := C.root_reaches_all _ ((C.mem_fineCL g).mp hg).1
    rcases g.base_of_mem_children f hfg with h | h
    · exact h ▸ hgr
    · exact hgr.tail (Or.inl h)

/-- The vocabulary of the left component only shrinks
below the root of the cluster. -/
lemma vocL_fineCLplus (C : LoadedCluster tab) :
    ∀ f ∈ C.fineCLplus, f.label.left.fvoc ⊆ (nodeAt C.root).left.fvoc := fun f hf =>
  subset_trans (FinePathIn.label_left_fvoc_subset_base f)
    (cReach_left_fvoc_subset (C.root_cReach_base_of_mem_fineCLplus hf))

/-- The vocabulary of the right component only shrinks
below the root of the cluster. -/
lemma vocR_fineCLplus (C : LoadedCluster tab) :
    ∀ f ∈ C.fineCLplus, f.label.right.fvoc ⊆ (nodeAt C.root).right.fvoc := fun f hf =>
  subset_trans (FinePathIn.label_right_fvoc_subset_base f)
    (cReach_right_fvoc_subset (C.root_cReach_base_of_mem_fineCLplus hf))

/-! ### The remaining fields -/

/-- Lemma 9.7 (e): at a node `t` of `C^R_Δ` with `Δ` basic the rule applied is the modal
rule `(M)` for the loaded formula `~⌊·A⌋ξ` of `Δ`. Its unique child `u` satisfies
`Λ₁(u) = (Λ₁(t))_A`, and its right component only depends on `Δ`.

Properness is needed to exclude the two other right `PdlRule`s: `(L+)` is only applied at
a free node, while `(L-)` makes its unique child free, and both contradict Lemma 9.4 (a)
because by Lemma 9.4 (c) some child of `t` is again in the cluster. -/
lemma basicModalStepAt (C : LoadedCluster tab) {Δ : Sequent}
    (hb : Δ.basic) {t : FinePathIn tab} (ht : t ∈ C.nodesWithFineRight Δ) :
    ∃ A ξ, Δ.2.2 = some (Sum.inr (~'⌊·A⌋ξ)) ∧ ∃ g, t.children = {g} ∧ g.atBigRoot
      ∧ g.label.left = Finset.projection A t.label.left
      ∧ g.label.rightOnly = modRChildRightOnly A ξ Δ.2.1 := by
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  have hDl : Δ.2.2 = t.label.2.2 := by rw [← ht_lab]; rfl
  have hDr : Δ.2.1 = t.label.2.1 := by rw [← ht_lab]; rfl
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rcases t.basicRightStep ht_right (ht_lab ▸ hb) with
    ⟨hbr, hnone⟩ | ⟨g, hg, hgbr, hgnone⟩ | ⟨A, ξ, hA, g, hg, hgbr, hg1, hg2⟩
  · exfalso
    have hrl := C.all_right_loaded t.base hmf.1
    rw [← t.label_eq_nodeAt_base hbr, hnone] at hrl
    simp at hrl
  · exfalso
    rw [hg, Finset.mem_singleton] at hc
    subst hc
    have hrl := C.all_right_loaded c.base hcmf.1
    rw [← c.label_eq_nodeAt_base hgbr, hgnone] at hrl
    simp at hrl
  · exact ⟨A, ξ, by rw [hDl]; exact hA, g, hg, hgbr, hg1, by rw [hDr]; exact hg2⟩

/-- Every element of `stepOf Δ` is the right component of a child of some node of `C^R_Δ`,
namely of the first one. -/
lemma exists_child_rightOnly_of_mem_stepOf (C : LoadedCluster tab) {Δ Pi : Sequent}
    (hPi : Pi ∈ C.stepOf Δ) :
    ∃ f ∈ C.nodesWithFineRight Δ, ∃ g ∈ f.children, g.label.rightOnly = Pi := by
  unfold stepOf at hPi
  cases hh : (C.nodesWithFineRight Δ).head? with
  | none => rw [hh] at hPi; simp at hPi
  | some f =>
    rw [hh] at hPi
    simp only [Finset.mem_image] at hPi
    obtain ⟨g, hg, rfl⟩ := hPi
    exact ⟨f, List.mem_of_mem_head? hh, g, hg, rfl⟩

/-! ### The descent for Lemma 9.7 (d)

The paper picks a node `t ∈ C_Δ` that is minimal in the tree order and then follows
left-rule children downwards; by `FinePathIn.children_rightOnly_eq_of_usesLeftRule` this
stays inside `C_Δ`, and closing rules are excluded because they have no children while
Lemma 9.4 (c) (`nonLpr_some_child_in_C`, which needs properness) provides one.

The descent itself is `FinePathIn.descent` from `Pdl.FinePathDescent`: fine children are not
structurally smaller, so the recursion is justified by the well-foundedness of the flipped
fine child relation. -/

/-- Every fine node of the cluster is loaded on the right, i.e. Lemma 9.4 (a) at the fine
level. For nodes that are coarse nodes this is `all_right_loaded`; for the intermediate
nodes of a local tableau it follows because a coarse child of theirs is in the cluster and
loading on the right is inherited upwards inside a local tableau. -/
lemma memFine_label_isRight (C : LoadedCluster tab) {f : FinePathIn tab} (hf : C.memFine f) :
    f.label.2.2.isRight := by
  by_cases hbr : f.atBigRoot
  · rw [f.label_eq_nodeAt_base hbr]
    exact C.all_right_loaded _ hf.1
  · obtain ⟨q, hq, hqC⟩ := hf.2.resolve_left hbr
    exact f.isRight_of_mem_coarseChildrenBelow hbr q hq (C.all_right_loaded q hqC)

/-- Every label in `Λ₂[C]` is loaded on the right. -/
lemma isRight_of_mem_lambdaTwo (C : LoadedCluster tab) {Δ : Sequent} (hΔ : Δ ∈ C.lambdaTwo) :
    Δ.2.2.isRight := by
  simp only [lambdaTwo, Finset.mem_image, List.mem_toFinset] at hΔ
  obtain ⟨f, hf, rfl⟩ := hΔ
  exact C.memFine_label_isRight ((C.mem_fineCL f).mp hf)

/-- The descent of Lemma 9.7 (d): if `C_Δ` is non-empty then either `C^R_Δ` is non-empty,
or `C_Δ` contains a loaded-path repeat.

Starting from any node of `C_Δ` we follow children: as long as no right rule is applied and
no repeat is reached, the node has a child in the cluster (Lemma 9.4 (c), which needs
properness) with the same right component (Lemma 9.7 (c)), and the descent terminates by
`FinePathIn.descent` — but a childless node of the cluster which is not a repeat would
contradict Lemma 9.4 (c).

This is the paper's descent. It is no longer needed for Lemma 9.7 (d) below, which is now
proved via `isLrep_of_mem_nodesWithFine`, but it is kept as the direct formalisation of the
argument in the paper. -/
lemma exists_right_or_lrep (C : LoadedCluster tab) {Δ : Sequent}
    (hΔ : Δ ∈ C.lambdaTwo) :
    C.nodesWithFineRight Δ ≠ [] ∨ ∃ f ∈ C.nodesWithFine Δ, f.base.isLrep := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hR, hlrep⟩ := hcon
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ ((C.mem_lambdaTwo_iff Δ).mp hΔ)
  have hΔR : Δ.2.2.isRight := C.isRight_of_mem_lambdaTwo hΔ
  have down : ∀ u : FinePathIn tab, u ∈ C.nodesWithFine Δ → u.children ≠ ∅ →
      ∃ g ∈ u.children, g ∈ C.nodesWithFine Δ := by
    intro u hu hne
    have hu' := hu
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hu'
    obtain ⟨hu_CL, hu_lab⟩ := hu'
    obtain ⟨g, hg, hgmf⟩ := C.exists_child_memFine_of_not_isLrep ((C.mem_fineCL u).mp hu_CL)
      (hlrep u hu)
    refine ⟨g, hg, ?_⟩
    have huleft : u.usesLeftRule := by
      rcases u.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with h | h
      · exact h
      · exfalso
        have hmem : u ∈ C.nodesWithFineRight Δ := by
          simp only [nodesWithFineRight, List.mem_filter]
          exact ⟨hu, h⟩
        rw [hR] at hmem
        simp at hmem
    have huR : u.label.2.2.isRight := by rw [show u.label.2.2 = Δ.2.2 by rw [← hu_lab]; rfl]
                                         exact hΔR
    have hgl : g.label.rightOnly = u.label.rightOnly :=
      u.children_rightOnly_eq_of_usesLeftRule huleft huR g hg
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
    exact ⟨(C.mem_fineCL g).mpr hgmf, by rw [hgl, hu_lab]⟩
  obtain ⟨v, hv, hvnil⟩ := FinePathIn.descent down t ht
  have hv_CL : v ∈ C.fineCL := by
    simp only [nodesWithFine, List.mem_filter] at hv
    exact hv.1
  obtain ⟨g, hg, -⟩ :=
    C.exists_child_memFine_of_not_isLrep ((C.mem_fineCL v).mp hv_CL) (hlrep v hv)
  rw [hvnil] at hg
  simp at hg

/-- If a node of `C_Δ` is a loaded-path repeat then its companion is again a node of `C_Δ`,
it carries the same label, and it is *not* a loaded-path repeat itself.

That the companion is in the cluster is Lemma 9.4 (c) (`lpr_comp_in_C`); that it carries
the same label is `nodeAt_companionOf_setEq` — note that with `Finset` sequents this is
literal equality; and it is not a repeat because it is a proper ancestor of the repeat,
while a repeat is a leaf. -/
lemma exists_companion_mem_nodesWithFine (C : LoadedCluster tab) {Δ : Sequent}
    {f : FinePathIn tab} (hf : f ∈ C.nodesWithFine Δ) (hl : f.base.isLrep) :
    ∃ c : PathIn tab, c.toFine ∈ C.nodesWithFine Δ ∧ ¬ c.isLrep ∧ nodeAt c = f.label := by
  have hf' := hf
  simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf'
  obtain ⟨hf_CL, hf_lab⟩ := hf'
  have hmf : C.memFine f := (C.mem_fineCL f).mp hf_CL
  have hbase : f.label = nodeAt f.base :=
    f.label_eq_nodeAt_base (f.atBigRoot_of_base_isLrep hl)
  rcases h2 : (tabAt f.base).2.2 with _ | _ | lpr
  case lrep =>
    have heart : f.base ♥ (companionOf f.base lpr h2) := ⟨lpr, h2, rfl⟩
    have hc_CL : companionOf f.base lpr h2 ∈ C.CL := C.lpr_comp_in_C f.base hmf.1 heart
    have hc_node : nodeAt (companionOf f.base lpr h2) = f.label := by
      rw [nodeAt_companionOf_setEq f.base lpr h2, hbase]
    refine ⟨companionOf f.base lpr h2, ?_, ?_, hc_node⟩
    · simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
      refine ⟨(C.mem_fineCL _).mpr (C.memFine_toFine hc_CL), ?_⟩
      rw [PathIn.label_toFine, hc_node, hf_lab]
    · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp (companion_lt heart)
      exact PathIn.not_isLrep_of_edge hb
  all_goals
    exfalso
    unfold PathIn.isLrep at hl
    rw [h2] at hl
    simp [Tableau.isLrep] at hl

/-- Every node of `C_Δ` is a loaded-path repeat, provided `C^R_Δ` is empty.

This is the key step for Lemma 9.7 (d). The proof is by well-founded induction on the label
along the Dershowitz-Manna ordering `lt_Sequent`: at a node of `C_Δ` that is not a repeat a
left rule is applied — a right rule is excluded by the assumption — so by Lemma 9.4 (c)
there is a child in the cluster, its right component is still `Δ` by Lemma 9.7 (c) and its
label is strictly smaller. Applying the induction hypothesis to that child makes it a
repeat, and then its companion is again in `C_Δ` with the *same*, hence still smaller,
label, but is not a repeat — contradicting the induction hypothesis. -/
lemma isLrep_of_mem_nodesWithFine (C : LoadedCluster tab) {Δ : Sequent}
    (hR : C.nodesWithFineRight Δ = []) : ∀ f ∈ C.nodesWithFine Δ, f.base.isLrep := by
  have key : ∀ Y : Sequent, ∀ f ∈ C.nodesWithFine Δ, f.label = Y → f.base.isLrep := by
    intro Y
    induction Y using IsWellFounded.induction lt_Sequent with
    | _ Y IH =>
      intro f hf hlab
      by_contra hnl
      have hf' := hf
      simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hf'
      obtain ⟨hf_CL, hf_lab⟩ := hf'
      have hmf : C.memFine f := (C.mem_fineCL f).mp hf_CL
      obtain ⟨g, hg, hgmf⟩ := C.exists_child_memFine_of_not_isLrep hmf hnl
      have hne : f.children ≠ ∅ := by
        intro hnil
        rw [hnil] at hg
        simp at hg
      have hleft : f.usesLeftRule := by
        rcases f.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with h | h
        · exact h
        · exfalso
          have hmem : f ∈ C.nodesWithFineRight Δ := by
            simp only [nodesWithFineRight, List.mem_filter]
            exact ⟨hf, h⟩
          rw [hR] at hmem
          simp at hmem
      have hfR : f.label.2.2.isRight := C.memFine_label_isRight hmf
      have hgmem : g ∈ C.nodesWithFine Δ := by
        simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
        refine ⟨(C.mem_fineCL g).mpr hgmf, ?_⟩
        rw [f.children_rightOnly_eq_of_usesLeftRule hleft hfR g hg, hf_lab]
      have hglt : lt_Sequent g.label Y :=
        hlab ▸ f.children_lt_Sequent_of_usesLeftRule hleft hfR g hg
      have hglrep : g.base.isLrep := IH g.label hglt g hgmem rfl
      obtain ⟨c, hc_mem, hc_nl, hc_lab⟩ := C.exists_companion_mem_nodesWithFine hgmem hglrep
      exact hc_nl (by simpa using IH g.label hglt c.toFine hc_mem (by simp [hc_lab]))
  intro f hf
  exact key f.label f hf rfl

/-- Lemma 9.7 (d): if `C_Δ` is non-empty then so is `C^R_Δ`.

Where the paper uses its Fact `lprAreCritical` — on the path from a companion to its repeat
the modal rule is applied at least once — we argue with the Dershowitz-Manna measure
instead: if `C^R_Δ` were empty then by `isLrep_of_mem_nodesWithFine` all nodes of `C_Δ`
would be loaded-path repeats, but the companion of such a repeat is again in `C_Δ` and is
not a repeat. (Since `Sequent` now uses `Finset`s, a repeat carries exactly the same label
as its companion, cf. `nodeAt_companionOf_setEq`.) -/
lemma exists_right_of_proper (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ [] := by
  intro Δ hΔ hnil
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ ((C.mem_lambdaTwo_iff Δ).mp hΔ)
  obtain ⟨c, hc_mem, hc_nl, -⟩ :=
    C.exists_companion_mem_nodesWithFine hf (C.isLrep_of_mem_nodesWithFine hnil f hf)
  exact hc_nl (by simpa using C.isLrep_of_mem_nodesWithFine hnil _ hc_mem)

/-- The leading atomic program of a basic label of `Λ₂[C]` is in the joint vocabulary.

That it is in the vocabulary of `Γ₂` is vocabulary preservation. That it is in the
vocabulary of `Γ₁` — which the paper does not mention, but which its Lemma 10.1 needs —
uses Lemma 9.7 (e): the modal rule is applied at some `t ∈ C^R_Δ` and its child `u` is
again in `C`, so `Λ₁(u) = (Λ₁(t))_a` is non-empty by Lemma 9.4 (b), which forces a box
`⌈a⌉ψ` in `Λ₁(t)`. -/
lemma loadedProgVoc_of_proper (C : LoadedCluster tab) :
    (nodeAt C.root).left ≠ {} → ∀ Δ ∈ C.lambdaTwo, Δ.basic →
      (Δ.loadedProg).voc ⊆ jvoc (nodeAt C.root) := by
  intro hG1 Δ hΔ hb
  obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ (C.exists_right_of_proper Δ hΔ)
  obtain ⟨A, xi, hAxi, g, hg, hgbr, hgleft, -⟩ := C.basicModalStepAt hb ht
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht'
  have hmf : C.memFine t := (C.mem_fineCL t).mp ht_CL
  obtain ⟨c, hc, hcmf⟩ := C.exists_child_memFine_of_not_isLrep hmf
    (t.not_isLrep_base_of_usesRightRule ht_right)
  rw [hg, Finset.mem_singleton] at hc
  have hgmf : C.memFine g := hc ▸ hcmf
  -- The left component of the root is non-empty, hence so is that of every node of `C`.
  have hroot1 : (nodeAt C.root).1 ≠ ∅ := by
    intro h
    apply hG1
    have hrr := C.root_loaded_right
    rcases hh : nodeAt C.root with ⟨L, R, O⟩
    rw [hh] at h hrr
    rcases O with _ | (o | o) <;> simp_all [Sequent.left]
  have hg1 : (nodeAt g.base).1 ≠ ∅ := fun h =>
    hroot1 ((C.left_empty_iff_root_left_empty g.base hgmf.1).mp h)
  have hgne : g.label.left ≠ ∅ := by
    rw [g.label_eq_nodeAt_base hgbr]
    intro h
    rcases hh : nodeAt g.base with ⟨L, R, O⟩
    rw [hh] at h hg1
    simp only [Sequent.left_eq, Finset.union_eq_empty] at h
    exact hg1 h.1
  -- Hence there is a box `⌈·A⌉ψ` in the left component of `t`.
  rw [hgleft] at hgne
  obtain ⟨ψ, hψ⟩ := Finset.nonempty_iff_ne_empty.mpr hgne
  have hbox : (⌈·A⌉ψ) ∈ t.label.left := Finset.mem_projection.mp hψ
  have htplus : t ∈ C.fineCLplus := Finset.mem_union_left _ (List.mem_toFinset.mpr ht_CL)
  have hAleft : (Sum.inr A : Sum Nat Nat) ∈ (nodeAt C.root).left.fvoc := by
    apply C.vocL_fineCLplus t htplus
    exact mem_fvoc_iff.mpr ⟨_, hbox, by simp⟩
  have hAright : (Sum.inr A : Sum Nat Nat) ∈ (nodeAt C.root).right.fvoc := by
    apply C.vocR_fineCLplus t htplus
    have hO : t.label.2.2 = some (Sum.inr (~'⌊·A⌋xi)) := by rw [← ht_lab] at hAxi; exact hAxi
    refine mem_fvoc_iff.mpr ⟨~(⌊·A⌋xi).unload, ?_, ?_⟩
    · rcases hh : t.label with ⟨L, R, O⟩
      rw [hh] at hO
      subst hO
      simp [Sequent.right, Olf.R]
    · cases xi <;> simp [LoadFormula.unload]
  have hlp : Δ.loadedProg = (·A : Program) := by
    obtain ⟨L, R, O⟩ := Δ
    simp only at hAxi
    subst hAxi
    cases xi <;> rfl
  rw [hlp]
  intro x hx
  simp only [Program.voc, Finset.mem_singleton] at hx
  subst hx
  simp only [jvoc, Finset.mem_inter]
  exact ⟨hAleft, hAright⟩

/-- The inner induction in the proof of Lemma 10.3: if a formula follows from the left
component of every node of `C^R_Δ` and of every exit node with right component `Δ`, then it
follows from the left component of every node of `C⁺_Δ`. This packages Lemma 9.7 (a) —
every node of `C_Δ` is in `C^L_Δ` or in `C^R_Δ` — with the local invertibility of the rules
applied at the nodes of `C^L_Δ`.

The argument is a descent along the children of `t`: an exit is covered by the second
hypothesis and a node of `C^R_Δ` by the first, while at a node of `C^L_Δ` all children stay
in `C⁺_Δ` (by `FinePathIn.children_rightOnly_eq_of_usesLeftRule` and
`LoadedCluster.mem_fineCLplus_of_child`) and the local invertibility of the left rule
applied there transfers the entailment back up. That last step is
`FinePathIn.leftEntails_of_children_of_usesLeftRule`; note that `FinePathIn.locally_sound`
is *not* enough here, because it speaks about the whole label while `leftEntails` only
assumes the left component, so we need the left-only invertibility
`LocalRuleApp.left_sat_of_isLeftRule`.

The descent is not along the fine child relation but, as in `isLrep_of_mem_nodesWithFine`,
by well-founded induction on the label along the Dershowitz-Manna ordering `lt_Sequent`:
left rules strictly decrease the label, and this makes the remaining case, a loaded-path
repeat in `C_Δ`, work out. At such a repeat no rule is applied, but by
`exists_companion_mem_nodesWithFine` its companion is again a node of `C_Δ` with exactly the
same label and is not a repeat, so the claim at the companion — which is the same claim,
since `leftEntails` only depends on the label — is obtained from the very same case
distinction, at the same label.

Properness of the cluster is used through `LoadedCluster.exists_child_memFine_of_not_isLrep`
(Lemma 9.4 (c)), which is why no separate properness hypothesis is needed. -/
lemma leftPropagation_of_proper (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, ∀ φ : Formula,
      (∀ u ∈ C.nodesWithFineRight Δ, u.leftEntails φ) →
      (∀ u ∈ C.exitsWithFine Δ, u.leftEntails φ) →
      ∀ t ∈ C.plusNodesWithFine Δ, t.leftEntails φ := by
  intro Δ _ φ hRight hExit
  -- The claim at a node of `C_Δ` that is *not* a loaded-path repeat, given the claim at
  -- all nodes of `C⁺_Δ` with a strictly smaller label.
  have step : ∀ Y : Sequent,
      (∀ Y', lt_Sequent Y' Y → ∀ t' ∈ C.plusNodesWithFine Δ, t'.label = Y' → t'.leftEntails φ) →
      ∀ u ∈ C.nodesWithFine Δ, ¬ u.base.isLrep → u.label = Y → u.leftEntails φ := by
    intro Y IH u hu hnl hlab
    have hu' := hu
    simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq] at hu'
    obtain ⟨hu_CL, hu_lab⟩ := hu'
    have hmf : C.memFine u := (C.mem_fineCL u).mp hu_CL
    have huR : u.label.2.2.isRight := C.memFine_label_isRight hmf
    obtain ⟨g0, hg0, -⟩ := C.exists_child_memFine_of_not_isLrep hmf hnl
    have hne : u.children ≠ ∅ := by
      intro hnil
      rw [hnil] at hg0
      simp at hg0
    rcases u.usesLeftRule_or_usesRightRule_of_children_ne_empty hne with hleft | hright
    · -- A left rule: all children are in `C⁺_Δ` and have a strictly smaller label, so the
      -- claim holds at them, and local invertibility transfers it to `u`.
      refine u.leftEntails_of_children_of_usesLeftRule hleft huR ?_
      intro g hg
      refine IH g.label (hlab ▸ u.children_lt_Sequent_of_usesLeftRule hleft huR g hg) g ?_ rfl
      simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨C.mem_fineCLplus_of_child hu_CL hg,
        by rw [u.children_rightOnly_eq_of_usesLeftRule hleft huR g hg, hu_lab]⟩
    · -- A right rule: this is the first hypothesis.
      exact hRight u (by simp only [nodesWithFineRight, List.mem_filter]; exact ⟨hu, hright⟩)
  -- The claim at all nodes of `C⁺_Δ`, by well-founded induction on the label.
  have key : ∀ Y : Sequent, ∀ t ∈ C.plusNodesWithFine Δ, t.label = Y → t.leftEntails φ := by
    intro Y
    induction Y using IsWellFounded.induction lt_Sequent with
    | _ Y IH =>
      intro t ht hlab
      have ht' := (C.mem_plusNodesWithFine_iff Δ t).mp ht
      by_cases hmf : C.memFine t
      · have htf : t ∈ C.nodesWithFine Δ := by
          simp only [nodesWithFine, List.mem_filter, decide_eq_true_eq]
          exact ⟨(C.mem_fineCL t).mpr hmf, ht'.2⟩
        by_cases hl : t.base.isLrep
        · -- A loaded-path repeat: its companion carries the same label, is again a node of
          -- `C_Δ` and is not a repeat, so the claim there is the claim here.
          obtain ⟨c, hc_mem, hc_nl, hc_lab⟩ := C.exists_companion_mem_nodesWithFine htf hl
          have hc := step Y IH c.toFine hc_mem (by rw [PathIn.base_toFine]; exact hc_nl)
            (by rw [PathIn.label_toFine, hc_lab, hlab])
          intro W M w hw
          exact hc W M w (by rw [PathIn.label_toFine, hc_lab]; exact hw)
        · exact step Y IH t htf hl hlab
      · -- Not a node of the cluster, hence an exit: this is the second hypothesis.
        refine hExit t ((C.mem_exitsWithFine_iff Δ t).mpr ⟨?_, ht'.2⟩)
        rcases Finset.mem_union.mp ht'.1 with h | h
        · exact absurd ((C.mem_fineCL t).mp (List.mem_toFinset.mp h)) hmf
        · exact h
  exact fun t ht => key t.label t ht rfl

/-- Lemma 9.7 (f): at a non-basic `Δ` the children of any `t ∈ C^R_Δ` are the `Λ₁(t);Π`
for `Π ∈ stepOf Δ`.  Here only the existence of a node of `C⁺_Π` with the same left
component as `t` is recorded, which is what the proof of Lemma 10.3 uses. -/
lemma rightRuleChildren_of_uniform (C : LoadedCluster tab) (hU : C.HasUniformSteps) :
    ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
      ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi, u.label.left = t.label.left := by
  intro Δ _ hnb t ht Pi hPi
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  obtain ⟨⟨ht_CL, ht_lab⟩, ht_right⟩ := ht'
  rw [← C.stepOf_spec hU Δ ht] at hPi
  simp only [Finset.mem_image] at hPi
  obtain ⟨u, hu, hlab⟩ := hPi
  refine ⟨u, ?_, ?_⟩
  · simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨C.mem_fineCLplus_of_child ht_CL hu, hlab⟩
  · exact t.children_left_eq_of_usesRightRule ht_right (ht_lab ▸ hnb) u hu

/-- Lemma 9.7 (e), in the semantic form used in the proof of Lemma 10.3.

Note that no uniformity is needed here: by `basicModalStepAt` the right components of the
children of a node of `C^R_Δ` with `Δ` basic are determined by `Δ` alone, so the list
`stepOf Δ`, read off the first node of `C^R_Δ`, describes the children of every node of
`C^R_Δ`. -/
lemma modalStep_of (C : LoadedCluster tab) :
    ∀ Δ ∈ C.lambdaTwo, Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
      ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi,
        ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ ψ ∈ t.label.left, evaluate M w ψ) →
          relate M Δ.loadedProg w v → ∀ ψ ∈ u.label.left, evaluate M v ψ := by
  intro Δ _ hb t ht Pi hPi
  obtain ⟨f0, hf0, g0, hg0, hg0lab⟩ := C.exists_child_rightOnly_of_mem_stepOf hPi
  obtain ⟨A, xi, hAxi, g, hg, -, hgleft, hgright⟩ := C.basicModalStepAt hb ht
  obtain ⟨A', xi', hAxi', g0', hg0', -, -, hg0right⟩ := C.basicModalStepAt hb hf0
  have hAA : A' = A ∧ xi' = xi := by
    rw [hAxi] at hAxi'
    simp only [Option.some.injEq, Sum.inr.injEq] at hAxi'
    rcases xi' with φ | χ <;> rcases xi with φ' | χ' <;> simp_all
  rw [hAA.1, hAA.2] at hg0right
  rw [hg0', Finset.mem_singleton] at hg0
  subst hg0
  have hPi_eq : Pi = g.label.rightOnly := by rw [← hg0lab, hg0right, hgright]
  have ht' := ht
  simp only [nodesWithFineRight, nodesWithFine, List.mem_filter, decide_eq_true_eq] at ht'
  refine ⟨g, ?_, ?_⟩
  · simp only [plusNodesWithFine, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨C.mem_fineCLplus_of_child ht'.1.1 (by rw [hg]; simp), hPi_eq.symm⟩
  · have hlp : Δ.loadedProg = (·A : Program) := by
      obtain ⟨L, R, O⟩ := Δ
      simp only at hAxi
      subst hAxi
      cases xi <;> rfl
    intro W M w v hw hrel ψ hψ
    rw [hgleft] at hψ
    have hbox := hw _ (Finset.mem_projection.mp hψ)
    rw [hlp] at hrel
    exact hbox v hrel

end LoadedCluster
