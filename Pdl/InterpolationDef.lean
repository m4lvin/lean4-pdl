import Pdl.Flip
import Pdl.InterpolationCluster

/-! # Defining interpolants (Section 9)

Note that we can skip much of Subsection 8.2 because we worked already with split tableaux anyway.

NOTE: We may need extra work for *uniformity* though.
-/

/-! ## Interpolants for PdlRules applied to free nodes

The only rule treated here is (L+), i.e. `loadL` and `loadR`.
-/

def freePdlRuleInterpolant {X Y} (r : PdlRule X Y) (Xfree : X.isFree) (θY : PartInterpolant Y)
    : PartInterpolant X := by
  rcases θY with ⟨θ, θ_ip_Y⟩
  cases r
  case loadL in_L notBox Y_def =>
    use θ
    subst Y_def
    rcases θ_ip_Y with ⟨hYvoc, hYL, hYR⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x x_in
      specialize hYvoc x_in
      simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.left_eq, Olf.L_inl, unload_boxes,
        LoadFormula.unload, List.map_append, List.map_cons, Formula.voc, List.map_nil,
        List.toFinset_append, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.union_singleton, Finset.sup_insert, id_eq, Finset.sup_eq_union', Sequent.right_eq,
        Olf.R_inl, List.append_nil, Finset.mem_inter, Finset.mem_union, Finset.mem_sup,
        List.mem_toFinset, List.mem_map, exists_exists_and_eq_and] at hYvoc
      simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.left_eq, Olf.L_none, List.append_nil,
        Sequent.right_eq, Olf.R_none, Finset.mem_inter, Finset.mem_sup, List.mem_toFinset,
        List.mem_map, id_eq, exists_exists_and_eq_and]
      rcases hYvoc with ⟨x_from, ⟨φ, φ_inR, x_from_φ⟩⟩
      constructor
      · rcases x_from with (hx|hx)
        · exact ⟨_, in_L, hx⟩
        · grind
      · use φ
    all_goals
      clear notBox Xfree
      simp at *
      grind
  case loadR in_R notBox Y_def=>
    use θ
    subst Y_def
    rcases θ_ip_Y with ⟨hYvoc, hYL, hYR⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x x_in
      specialize hYvoc x_in
      simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.left_eq, Olf.L_inr, List.append_nil,
        Sequent.right_eq, Olf.R_inr, unload_boxes, LoadFormula.unload, List.map_append,
        List.map_cons, Formula.voc, List.map_nil, List.toFinset_append, List.toFinset_cons,
        List.toFinset_nil, insert_empty_eq, Finset.union_singleton, Finset.sup_insert, id_eq,
        Finset.sup_eq_union', Finset.mem_inter, Finset.mem_sup, List.mem_toFinset, List.mem_map,
        exists_exists_and_eq_and, Finset.mem_union] at hYvoc
      simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.left_eq, Olf.L_none, List.append_nil,
        Sequent.right_eq, Olf.R_none, Finset.mem_inter, Finset.mem_sup, List.mem_toFinset,
        List.mem_map, id_eq, exists_exists_and_eq_and]
      rcases hYvoc with ⟨⟨φ, φ_inR, x_from_φ⟩, x_from⟩
      constructor
      · use φ
      · rcases x_from with (hx|hx)
        · exact ⟨_, in_R, hx⟩
        · grind
    all_goals
      clear notBox Xfree
      simp at *
      grind
  all_goals
    exfalso
    subst_eqs

/-! ## From Tableau to Interpolant -/

/-- Ideally this would be a computable `def` and not an existential.
But currently `PathIn.strong_upwards_inductionOn` only works with `Prop` motive.

Note the extra hypothesis `s.isClusterRoot`: to interpolate at a loaded node we need to
know that it is the *first* node of its cluster along the branch leading to it, because
otherwise we cannot make a `LoadedCluster`. In particular, this hypothesis holds whenever
the parent of `s` is free (see `PathIn.isClusterRoot_of_edge_from_free`), which is the case
for all children of the free nodes we recurse into below. It also holds for the exits of a
cluster (see `isClusterRoot_of_isExitOf`), which need not have a free parent, but which are
always the first node of their own cluster.

At the root of the tableau the hypothesis is free of charge: `.nil` has no parent at all,
so `PathIn.isClusterRoot_nil` holds vacuously and `tabToInt` below can discharge it. Hence
we do not even need the (harmless, since we always start with a free sequent) additional
assumption that the root sequent `X` is free. -/
theorem tabToIntAt {X : Sequent} (tab : Tableau .nil X) (s : PathIn tab) :
    s.isClusterRoot → ∃ θ, isPartInterpolant (nodeAt s) θ := by
  induction s using PathIn.strong_upwards_inductionOn -- Strong!
  next s IH =>
  intro s_cr
  -- case distinction before or after `induction`?
  by_cases (nodeAt s).isLoaded
  case pos s_loaded =>
    -- HARD case, here we want to use `clusterInterpolation` and that is why we used
    -- `PathIn.strong_upwards_inductionOn` to have an IH applicable to "far away" exits.
    -- The exits of the cluster of `s` are proper successors of `s` and are themselves
    -- cluster roots, so the IH is applicable to them.
    have myExitIPs : ∀ e : PathIn tab, isExitOf s e → PartInterpolant (nodeAt e) := by
      intro e e_exit
      have IHe := IH (lt_of_isExitOf s_cr e_exit) (isClusterRoot_of_isExitOf e_exit)
      exact ⟨IHe.choose, IHe.choose_spec⟩
    rcases clusterInterpolation s s_cr s_loaded myExitIPs with ⟨θ, h_θ⟩
    exact ⟨θ, h_θ⟩
  case neg s_free =>
    -- EASY case, singleton cluster because not loaded.
    simp at s_free
    have s_isFree : (nodeAt s).isFree := by simp [Sequent.isFree, s_free]
    rcases s_def : tabAt s with ⟨Hist, X, s_tab⟩
    cases s_tab_def : s_tab
    case loc nbas ltX nrep nexts =>
      /- -- Interestingly, we do not *yet* care about the end node being free here.
      have Xfree : X.isFree := by rw [nodeAt, s_def] at s_free; grind [Sequent.isFree]
      have endFree := fun Y => @endNodesOf_free_are_free _ Y ltX Xfree
      -/
      have endIPsExist : ∀ Y ∈ endNodesOf ltX, ∃ θ, isPartInterpolant Y θ := by
        intro Y Y_in
        subst s_tab_def -- hmm?
        -- Need to make a path-step to Y, def and proofs about it inspired by `Soundness.lean`
        let s_to_u : PathIn (tabAt s).2.2 := s_def ▸ @PathIn.loc _ _ nrep nbas ltX nexts Y Y_in .nil
        let u := s.append s_to_u
        have s_u : s ⋖_ u := by
          unfold u s_to_u
          apply edge_append_loc_nil
          grind
        specialize IH (Relation.TransGen.single s_u)
          (PathIn.isClusterRoot_of_edge_from_free s_isFree s_u)
        have tabAt_u_def : tabAt u = ⟨_, ⟨Y, nexts Y Y_in⟩⟩ := by
          unfold u s_to_u
          rw [tabAt_append]
          have : (tabAt (PathIn.loc Y_in PathIn.nil : PathIn (Tableau.loc nrep nbas ltX nexts)))
              = ⟨X :: _, ⟨Y, nexts Y Y_in⟩⟩ := by simp_all
          convert this <;> try rw [s_def]
          rw [eqRec_heq_iff_heq]
        unfold nodeAt at IH
        rw [tabAt_u_def] at IH
        exact IH
      let ltIP := LocalTableau.interpolant ltX ?endNodeIPs
      · rcases ltIP with ⟨θ, X_ip_θ⟩
        use θ
        unfold nodeAt
        rw [s_def]
        simp_all
      · intro Y Y_in
        specialize endIPsExist Y Y_in
        exact ⟨endIPsExist.choose, endIPsExist.choose_spec⟩
    case pdl Y bas r nrep next =>
      subst s_tab_def
      -- The def of `t` here is inspired by the proof of `tableauThenNotSat` (with s/t swapped).
      let s_to_t : PathIn (Tableau.pdl nrep bas r next) := (.pdl .nil)
      let t : PathIn tab := s.append (s_def ▸ s_to_t)
      have s_t : s ⋖_ t := by
          convert @edge_append_pdl_nil .nil _ tab s (s_def ▸ nrep)
                                        (s_def ▸ bas) Y (s_def ▸ r) (s_def ▸ next) ?_ <;> grind
      have def_Y : nodeAt t = Y := by
        simp only [t, s_to_t, nodeAt_append]
        convert @nodeAt_pdl_nil _ _ _ nrep bas next r <;> grind
      specialize IH (Relation.TransGen.single s_t)
        (PathIn.isClusterRoot_of_edge_from_free s_isFree s_t)
      unfold nodeAt at s_free
      rw [s_def] at s_free
      simp only at s_free
      unfold nodeAt
      rw [s_def]
      simp only
      rw [def_Y] at IH
      rcases IH with ⟨θY, θY_ip_Y⟩
      have := freePdlRuleInterpolant r (by grind [Sequent.isFree]) ⟨θY, θY_ip_Y⟩
      rcases this with ⟨θX, θX_ipX⟩
      use θX
    case lrep lpr =>
      exfalso
      absurd s_free
      rw [nodeAt, s_def]
      simp only [Bool.not_eq_false]
      apply LoadedPathRepeat_rep_isLoaded lpr

theorem tabToInt {X : Sequent} (tab : Tableau .nil X) :
    ∃ θ, isPartInterpolant X θ := tabToIntAt tab .nil PathIn.isClusterRoot_nil
