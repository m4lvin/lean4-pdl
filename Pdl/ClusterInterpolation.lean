import Pdl.PreInterpolant

/-! # Interpolants for proper clusters (Lemma 9.3)

This file contains the interpolation step for proper clusters: given interpolants for all
exit nodes of a cluster, we build an interpolant for the root of the cluster.

The ingredients live in the files imported here:
`Pdl.InterpolationCluster` (the cluster `C`, its quasi-tableau `Q` of Def 9.8, the region
formulas `θ_Δ` of Def 9.13 and Lemma 9.14), `Pdl.QFormula` (Def 9.15, Def 9.16 and
Fact 9.17) and `Pdl.PreInterpolant` (the pre-interpolants of Def 9.18).
-/

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Flipping Interpolants -/

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp_all
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

/-! ## Interpolants for proper clusters -/

/-- Lemma 9.3 for the case where the loaded formula is on the right side:
given interpolants for all exits of the cluster `C`, interpolate the root of `C`. -/
def clusterInterpolation_right (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt C.root) := by
  sorry

/-- Lemma 9.3: Given a loaded node `s` that is the first node of its cluster, and given
interpolants for all exits of that cluster, we get an interpolant for `s`.
Note how `s_cr` is exactly what is needed to make a `LoadedCluster` here. -/
def clusterInterpolation (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_loaded : (nodeAt s).isLoaded)
    (exitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt s) := by
  by_cases s_right : (nodeAt s).2.2.isRight
  case pos =>
    -- The loaded formula is on the right, so we can use `clusterInterpolation_right`.
    exact clusterInterpolation_right (LoadedCluster.ofClusterRoot s s_cr s_right)
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
    let C : LoadedCluster tab.flip :=
      LoadedCluster.ofClusterRoot s.flip (PathIn.isClusterRoot_flip s_cr) s_flip_right
    have flipIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e) := by
      intro e e_in
      have e_exit : isExitOf s.flip e := (LoadedCluster.mem_exits_iff _ e).mp e_in
      rw [← PathIn.flip_unflip e] at e_exit ⊢
      exact PartInterpolant.flipPath (exitIPs e.unflip (isExitOf_flip.mp e_exit))
    exact PartInterpolant.unflipPath (clusterInterpolation_right C flipIPs)
