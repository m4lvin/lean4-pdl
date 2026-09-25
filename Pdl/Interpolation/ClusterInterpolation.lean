import Pdl.Interpolation.ClusterSatDown

/-! # Interpolants for proper clusters (Lemma 9.3)

This file contains the interpolation step for proper clusters: given interpolants for all
exit nodes of a cluster, we build an interpolant for the root of the cluster.

The ingredients live in the files imported here:
`Pdl.InterpolationCluster` (the cluster `C`, its quasi-tableau `Q` of Def 9.8, the region
formulas `θ_Δ` of Def 9.13 and Lemma 9.14),
`Pdl.Interpolation.QFormula` (Def 9.15, Def 9.16 and Fact 9.17),
`Pdl.Interpolation.PreInterpolant` (the pre-interpolants of Def 9.18),
`Pdl.Interpolation.ClusterItp` (Def 9.20 and Lemma 10.1),
`Pdl.Interpolation.ClusterRho` (Def 10.2 and Lemma 10.3)
and `Pdl.Interpolation.ClusterSatDown` (Lemmas 10.6, 10.7 and 10.8).

The three conditions on the interpolant `θ_r := C.itp θ` of Definition 9.20 are exactly

* `LoadedCluster.itp_voc` (Lemma 10.1),
* `LoadedCluster.left_unsat_neg_itp` (Lemma 10.3), and
* `LoadedCluster.right_unsat_itp` (Lemma 10.8).

What this file adds is the *interface*: the interpolants `θ` used by those three results
are indexed by the **fine** exit nodes of the cluster, i.e. also by nodes *inside* a local
tableau, while `clusterInterpolation_right` is only given interpolants for the exits in the
coarse `PathIn` sense. The first half of the file bridges that gap, by pushing the
interpolants of the coarse exits upwards through the local tableaux with
`LocalTableau.interpolant`.
-/

open HasSat

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Flipping Interpolants -/

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp_all [HasSat.satisfiable]
  grind

/-- Transport an interpolant to the flipped tableau. -/
def PartInterpolant.flipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p)) : PartInterpolant (nodeAt p.flip) :=
  ⟨~ip.1, by rw [PathIn.nodeAt_flip]; exact IsPartInterpolant.flip ip.2⟩

/-- Transport an interpolant back from the flipped tableau. -/
def PartInterpolant.unflipPath {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p.flip)) : PartInterpolant (nodeAt p) := by
  refine ⟨~ip.1, ?_⟩
  have h : (nodeAt p.flip).flip = nodeAt p := by rw [PathIn.nodeAt_flip, Sequent.flip_flip]
  exact h ▸ IsPartInterpolant.flip ip.2

/-! ## From the coarse exits to the fine exits

A fine exit of the cluster is either a coarse node — then it is an exit in the coarse sense
and we are given an interpolant for it — or a node inside a local tableau from which the
cluster is never re-entered. In the latter case all end nodes of the local tableau below it
are coarse exits, and we obtain an interpolant by local interpolation. -/

/-- Every end node of the local tableau at a local path is an end node of the whole local
tableau that is below that path. -/
lemma LocalPathIn.exists_mem_endNodesBelow {Y : Sequent} :
    ∀ {Z : Sequent} {lt : LocalTableau Z} (lp : LocalPathIn lt), Y ∈ endNodesOf lp.ltAt →
      ∃ hY : Y ∈ endNodesOf lt, (⟨Y, hY⟩ : {W : Sequent // W ∈ endNodesOf lt}) ∈ lp.endNodesBelow
  | _, lt, .nil, h => ⟨h, by simp [LocalPathIn.endNodesBelow]⟩
  | _, .byLocalRule lra X_def next, .cons Y_in tail, h => by
      obtain ⟨hY, hmem⟩ := LocalPathIn.exists_mem_endNodesBelow tail h
      refine ⟨?_, ?_⟩
      · exact mem_endNodesOf_byLocalRule_iff.mpr ⟨_, Y_in, hY⟩
      · simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists]
        exact ⟨Y, hY, hmem, rfl⟩

/-- A coarse child below a fine node really is a child of the base of that fine node. -/
lemma FinePathIn.edge_of_mem_coarseChildrenBelow : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ∀ q ∈ f.coarseChildrenBelow, f.base ⋖_ q
  | _, _, _, .inLoc lp _, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
      obtain ⟨Y, Y_in, -, rfl⟩ := hq
      simp [FinePathIn.base]
  | _, _, _, .pdlHere, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_singleton] at hq
      subst hq
      simp [FinePathIn.base]
  | _, _, _, .lrepHere, q, hq => by simp [FinePathIn.coarseChildrenBelow] at hq
  | _, _, _, .loc Y_in tail, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      simpa [FinePathIn.base, loc_edge_loc_iff_edge] using
        FinePathIn.edge_of_mem_coarseChildrenBelow tail q' hq'
  | _, _, _, .pdl tail, q, hq => by
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      simpa [FinePathIn.base, pdl_edge_pdl_iff_edge] using
        FinePathIn.edge_of_mem_coarseChildrenBelow tail q' hq'

/-- A sharpening of `FinePathIn.base_of_mem_children`: a fine child that lies at a
different coarse node is a coarse node itself. -/
lemma FinePathIn.base_of_mem_children' : ∀ {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab'), ∀ g ∈ f.children, g.base = f.base ∨ (f.base ⋖_ g.base ∧ g.atBigRoot)
  | _, _, _, .inLoc lp lp_int, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨lp', -, rfl⟩ := hg
      split
      · exact Or.inr ⟨by simp [FinePathIn.base], by simp [FinePathIn.atBigRoot]⟩
      · exact Or.inl rfl
  | _, _, _, .pdlHere, g, hg => by
      simp only [FinePathIn.children, Finset.mem_singleton] at hg
      subst hg
      exact Or.inr ⟨by simp [FinePathIn.base], by simp [FinePathIn.atBigRoot]⟩
  | _, _, _, .lrepHere, g, hg => by simp [FinePathIn.children] at hg
  | _, _, _, .loc Y_in tail, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      rcases FinePathIn.base_of_mem_children' tail g' hg' with h | ⟨h1, h2⟩
      · exact Or.inl (by simp [FinePathIn.base, h])
      · exact Or.inr ⟨by simpa [FinePathIn.base, loc_edge_loc_iff_edge] using h1,
          by simpa [FinePathIn.atBigRoot] using h2⟩
  | _, _, _, .pdl tail, g, hg => by
      simp only [FinePathIn.children, Finset.mem_image] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      rcases FinePathIn.base_of_mem_children' tail g' hg' with h | ⟨h1, h2⟩
      · exact Or.inl (by simp [FinePathIn.base, h])
      · exact Or.inr ⟨by simpa [FinePathIn.base, pdl_edge_pdl_iff_edge] using h1,
          by simpa [FinePathIn.atBigRoot] using h2⟩

/-- **Local interpolation at fine nodes.** If a fine node is not a coarse node, i.e. it
lies properly inside a local tableau, and we have interpolants for all coarse children
below it — these are the end nodes of that local tableau that are reachable from it — then
we have an interpolant for the fine node itself. This is `LocalTableau.interpolant` applied
to the part of the local tableau below the node. -/
lemma FinePathIn.exists_interpolant_of_coarse : ∀ {H : History} {Z : Sequent}
    {tab' : Tableau H Z} (f : FinePathIn tab'), ¬ f.atBigRoot →
      (∀ q ∈ f.coarseChildrenBelow, ∃ θ, isPartInterpolant (nodeAt q) θ) →
      ∃ θ, isPartInterpolant f.label θ
  | _, _, _, .inLoc lp lp_int, _, h => by
      have endθs : ∀ Y ∈ endNodesOf lp.ltAt, PartInterpolant Y := by
        intro Y hY
        have hex : ∃ θ, isPartInterpolant Y θ := by
          obtain ⟨hY', hmem⟩ := lp.exists_mem_endNodesBelow hY
          have := h (PathIn.loc hY' .nil) (by
            simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists]
            exact ⟨Y, hY', hmem, rfl⟩)
          rwa [nodeAt_loc_nil] at this
        exact ⟨hex.choose, hex.choose_spec⟩
      have := LocalTableau.interpolant lp.ltAt endθs
      exact ⟨this.1, this.2⟩
  | _, _, _, .pdlHere, hbr, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .lrepHere, hbr, _ => absurd (by simp [FinePathIn.atBigRoot]) hbr
  | _, _, _, .loc Y_in tail, hbr, h => by
      refine FinePathIn.exists_interpolant_of_coarse tail
        (by simpa [FinePathIn.atBigRoot] using hbr) ?_
      intro q hq
      have := h (PathIn.loc Y_in q)
        (by simp only [FinePathIn.coarseChildrenBelow]; exact List.mem_map_of_mem hq)
      rwa [nodeAt_loc] at this
  | _, _, _, .pdl tail, hbr, h => by
      refine FinePathIn.exists_interpolant_of_coarse tail
        (by simpa [FinePathIn.atBigRoot] using hbr) ?_
      intro q hq
      have := h (PathIn.pdl q)
        (by simp only [FinePathIn.coarseChildrenBelow]; exact List.mem_map_of_mem hq)
      rwa [nodeAt_pdl] at this

open Classical in
/-- An interpolant for the label of a fine node, whenever one exists. This is the map `θ`
on the fine exit nodes that Definitions 9.13 and 9.18 need. -/
noncomputable def FinePathIn.itp {H : History} {Z : Sequent} {tab' : Tableau H Z}
    (f : FinePathIn tab') : Formula :=
  if h : ∃ θ, isPartInterpolant f.label θ then h.choose else ⊤

lemma FinePathIn.itp_spec {H : History} {Z : Sequent} {tab' : Tableau H Z} {f : FinePathIn tab'}
    (h : ∃ θ, isPartInterpolant f.label θ) : isPartInterpolant f.label f.itp := by
  rw [FinePathIn.itp, dif_pos h]
  exact h.choose_spec

namespace LoadedCluster

/-- Every coarse child below a fine exit of the cluster is a coarse exit of the cluster. -/
lemma mem_exits_of_mem_coarseChildrenBelow (C : LoadedCluster tab) {f : FinePathIn tab}
    (hbase : f.base ∈ C.CL) (hf : ¬ C.memFine f) :
    ∀ q ∈ f.coarseChildrenBelow, q ∈ C.exits := by
  intro q hq
  have hnot : ∀ q' ∈ f.coarseChildrenBelow, q' ∉ C.CL := by
    intro q' hq' hq'CL
    exact hf ⟨hbase, Or.inr ⟨q', hq', hq'CL⟩⟩
  rw [LoadedCluster.exits, Finset.mem_filter, Finset.mem_biUnion]
  refine ⟨⟨f.base, hbase, ?_⟩, hnot q hq⟩
  exact PathIn.children_spec.mp (f.edge_of_mem_coarseChildrenBelow q hq)

/-- A fine exit of the cluster that is a coarse node is a coarse exit of the cluster. -/
lemma mem_exits_base_of_mem_fineExits (C : LoadedCluster tab) {f : FinePathIn tab}
    (hf : f ∈ C.fineExits) (hbr : f.atBigRoot) : f.base ∈ C.exits := by
  simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset,
    decide_eq_true_eq] at hf
  obtain ⟨⟨g, hg, hfg⟩, hnot⟩ := hf
  have hgCL : g.base ∈ C.CL := ((C.mem_fineCL g).mp hg).1
  have hfCL : f.base ∉ C.CL := fun hin => hnot ⟨hin, Or.inl hbr⟩
  have hedge : g.base ⋖_ f.base := by
    rcases g.base_of_mem_children' f hfg with h | ⟨h, -⟩
    · exact absurd (h ▸ hgCL) hfCL
    · exact h
  rw [LoadedCluster.exits, Finset.mem_filter, Finset.mem_biUnion]
  exact ⟨⟨g.base, hgCL, PathIn.children_spec.mp hedge⟩, hfCL⟩

/-- Interpolants for the coarse exits of the cluster give interpolants for all fine exits. -/
lemma exists_itp_of_mem_fineExits (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ) :
    ∀ f ∈ C.fineExits, ∃ θ, isPartInterpolant f.label θ := by
  intro f hf
  have hf' := hf
  simp only [fineExits, Finset.mem_filter, Finset.mem_sup, List.mem_toFinset,
    decide_eq_true_eq] at hf'
  obtain ⟨⟨g, hg, hfg⟩, hnot⟩ := hf'
  by_cases hbr : f.atBigRoot
  · -- `f` is a coarse node, hence a coarse exit.
    have := exitIPs _ (C.mem_exits_base_of_mem_fineExits hf hbr)
    rw [← PathIn.label_toFine, ← f.eq_toFine_base_of_atBigRoot hbr] at this
    exact this
  · -- `f` lies properly inside a local tableau; use local interpolation.
    have hbase : f.base = g.base := by
      rcases g.base_of_mem_children' f hfg with h | ⟨-, h⟩
      · exact h
      · exact absurd h hbr
    have hbaseCL : f.base ∈ C.CL := hbase ▸ ((C.mem_fineCL g).mp hg).1
    refine f.exists_interpolant_of_coarse hbr ?_
    intro q hq
    exact exitIPs q (C.mem_exits_of_mem_coarseChildrenBelow hbaseCL hnot q hq)

/-- The interpolants of the fine exit nodes of the cluster, given interpolants for the
coarse exits. This is the map `θ` of Definitions 9.13, 9.18 and 9.20. -/
lemma fineExits_itp_spec (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ) :
    ∀ f ∈ C.fineExits, isPartInterpolant f.label (FinePathIn.itp f) :=
  fun f hf => FinePathIn.itp_spec (C.exists_itp_of_mem_fineExits exitIPs f hf)

end LoadedCluster


/-! ## Where uniformity is needed

The facts about a proper cluster that the proofs of Lemmas 10.1, 10.3 and 10.7 use are
proved in `Pdl.ClusterFacts` and `Pdl.ClusterSatDownFacts`. All of them follow from
properness of the cluster, which is part of `LoadedCluster`, except for
`LoadedCluster.rightRuleChildren_of_uniform`, which also needs uniformity of the tableau
(conditions U1/U2, formalised as `LoadedCluster.HasUniformSteps` with
`LoadedCluster.stepOf_spec`, and obtained from `tab.isUniform` by
`LoadedCluster.uniformOfUniTab`).

The reason is that `C.stepOf Δ` reads the right components of the children of the *first*
node of `C^R_Δ`, while the facts quantify over all nodes of `C^R_Δ`:

* `LoadedCluster.rightRuleChildren_of_uniform` (used at non-basic type-3 nodes in the proof
  of Lemma 10.3) says that for *every* `t ∈ C^R_Δ` and every `Π ∈ stepOf Δ` there is a node
  of `C⁺_Π` with the same left component as `t`. Its proof takes the children of `t`, so it
  needs the right components of those children to be the list `stepOf Δ` — which for a
  non-basic `Δ` is precisely `stepOf_spec`, i.e. uniformity.
* `LoadedCluster.modalStep_of` and `LoadedCluster.basicStep_of` also quantify over
  `t ∈ C^R_Δ`, but only for *basic* `Δ`. There the rule applied is the modal rule for the
  unique loaded formula of `Δ` (Lemma 9.7 (e)), so the right components of the children are
  determined by `Δ` alone; this is what `LoadedCluster.basicModalStepAt` shows, and it is
  why `modalStep_of` needs no uniformity.
* The remaining facts (`LoadedCluster.nonBasicStep_of`, `LoadedCluster.stepOf_lt_Sequent`,
  `LoadedCluster.leftPropagation_of_proper`, `LoadedCluster.exists_right_of_proper`, the
  vocabulary facts) speak about `Δ` and `stepOf Δ` only, or about local invertibility at a
  single node, and are independent of uniformity.
-/

/-! ## Interpolants for proper clusters -/

/-- Lemma 9.3 for the case where the loaded formula is on the right side:
given interpolants for all exits of the cluster `C`, interpolate the root of `C`.

The interpolant is `C.itp θ` from Definition 9.20, where `θ` gives the interpolants of the
*fine* exit nodes, obtained from the given interpolants of the coarse exits by
`LoadedCluster.fineExits_itp_spec`. Its three defining properties are Lemma 10.1
(`itp_voc`), Lemma 10.3 (`left_unsat_neg_itp`) and Lemma 10.8 (`right_unsat_itp`). -/
noncomputable def clusterInterpolation_right {tab : Tableau .nil X} (Xfree : X.isFree)
    (t_u : tab.isUniform)
    (C : LoadedCluster tab) (exitIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt C.root) := by
  classical
  -- Because we have a uniform tableau, also the fixed cluster C must have uniform steps.
  have hU : C.HasUniformSteps := LoadedCluster.uniformOfUniTab C t_u
  have exitIPs' : ∀ e ∈ C.exits, ∃ θ, isPartInterpolant (nodeAt e) θ :=
    fun e he => ⟨(exitIPs e he).1, (exitIPs e he).2⟩
  have hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (FinePathIn.itp f) :=
    C.fineExits_itp_spec exitIPs'
  refine ⟨C.itp FinePathIn.itp, C.itp_voc _ hθ, C.left_unsat_neg_itp hU hθ, ?_⟩
  by_cases hΓ₁ : (nodeAt C.root).left = {}
  · rw [LoadedCluster.itp, if_pos hΓ₁]
    have := tableauThenNotSat tab Xfree C.root
    exact Sequent.satisfiable_top_cons_right hΓ₁ this
  · exact C.right_unsat_itp hθ hΓ₁

/-- Lemma 9.3: Given a loaded node `s` that is the first node of its cluster, and given
interpolants for all exits of that cluster, we get an interpolant for `s`.
Note how `s_cr` is exactly what is needed to make a `LoadedCluster` here. -/
noncomputable def clusterInterpolation {tab : Tableau .nil X} (Xfree : X.isFree)
    (t_u : tab.isUniform) (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_proper : s ◃⁺ s) (s_loaded : (nodeAt s).isLoaded)
    (exitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt s) := by
  by_cases s_right : (nodeAt s).2.2.isRight
  case pos =>
    -- The loaded formula is on the right, so we can use `clusterInterpolation_right`.
    exact clusterInterpolation_right Xfree t_u (LoadedCluster.ofClusterRoot s s_cr s_proper s_right)
      (fun e e_in => exitIPs e ((LoadedCluster.mem_exits_iff _ e).mp e_in))
  case neg =>
    -- The loaded formula is on the left, so we "flip" the whole tableau.
    have s_flip_right : (nodeAt s.flip).2.2.isRight := by
      rw [PathIn.nodeAt_flip]
      rcases hh : nodeAt s with ⟨L, R, O⟩
      rw [hh] at s_right s_loaded
      cases O
      · simp [Sequent.isLoaded] at s_loaded
      case some val => cases val <;> simp_all [Sequent.flip, Olf.flip]
    have s_proper_flip := cEdgeTrans_flip_of_cEdgeTrans s_proper
    let C : LoadedCluster tab.flip :=
      LoadedCluster.ofClusterRoot s.flip (PathIn.isClusterRoot_flip s_cr) s_proper_flip s_flip_right
    have flipIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e) := by
      intro e e_in
      have e_exit : isExitOf s.flip e := (LoadedCluster.mem_exits_iff _ e).mp e_in
      rw [← PathIn.flip_unflip e] at e_exit ⊢
      exact PartInterpolant.flipPath (exitIPs e.unflip (isExitOf_flip.mp e_exit))
    have : X.flip.isFree := by rw [Sequent.flip_isFree]; exact Xfree
    exact PartInterpolant.unflipPath (clusterInterpolation_right this t_u.flip C flipIPs)
