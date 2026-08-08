import Pdl.LocalTableau
import Pdl.LocalRules

/-! # Paths in Local Tableaux

Here we collect the paths of sequents within a `LocalTableau`, i.e. the lists of sequents
from the root to an end node, and show that they are saturated and locally consistent.

This is used for the pre-states in the completeness proof, see `BuildTree.lean`. -/

def LocalTableau.paths : {X : _} → LocalTableau X → List (List Sequent)
  | .(_), (@byLocalRule X lra _ next) =>
      (lra.C.attach.flatMap (fun ⟨Y, h⟩ => (next Y h).paths)).map (X :: ·)
  | .(_), (@sim X _) => [[X]]
termination_by
  X => X -- pick up instance WellFoundedRelation Sequent from above!
decreasing_by
  subst_eqs
  apply localRuleApp.decreases_DM lra Y h

lemma LocalTableau.paths_mem_nonempty {X} (lt : LocalTableau X) :
    ∀ L ∈ lt.paths, L ≠ [] := by
  intro L L_in; cases lt <;> grind [paths]

lemma LocalTableau.pathsHead_eq_self {X} {lt : LocalTableau X} :
    ∀ {L}, (h : L ∈ lt.paths) → L.head (LocalTableau.paths_mem_nonempty lt _ h) = X := by
  cases lt <;> simp_all [paths]
  case byLocalRule lra next X_def =>
    intro L1 Y Z Z_in Y_in def_L1
    subst def_L1
    simp

lemma LocalTableau.pathsLast_eq_endNodes {X} {lt : LocalTableau X} :
    lt.paths.attach.map
      (fun ⟨L,h⟩ => L.getLast (LocalTableau.paths_mem_nonempty lt L h)) = endNodesOf lt := by
  induction lt
  case byLocalRule X lra X_def next IH =>
    -- this case is from aristotle.harmonic.fun
    have map_attach_last (ls : List (List Sequent)) (hne : ∀ L ∈ ls, L ≠ []) :
        ls.attach.map (fun ⟨L, h⟩ => (fun x => some x) (L.getLast (hne L h))) =
          ls.map List.getLast? := by
      induction ls with
      | nil => simp
      | cons L ls ih =>
        simp only [List.attach_cons, List.map_cons, List.cons.injEq]
        constructor
        · exact (List.getLast?_eq_some_getLast (hne L (by simp))).symm
        · simpa only [List.map_map] using
            ih (fun K h => hne K (by simp [h]))
    apply (Option.some_injective Sequent).list_map
    simp only [List.map_map]
    change (LocalTableau.byLocalRule lra X_def next).paths.attach.map
      (fun ⟨L, h⟩ => some (L.getLast (LocalTableau.paths_mem_nonempty _ L h))) = _
    rw [map_attach_last (LocalTableau.byLocalRule lra X_def next).paths
      (LocalTableau.paths_mem_nonempty _)]
    simp only [paths, endNodesOf, List.map_flatMap]
    have map_flatten (xss : List (List Sequent)) :
        List.map some xss.flatten = (xss.map (List.map some)).flatten := by
      induction xss <;> simp_all
    rw [map_flatten]
    apply congrArg List.flatten
    simp only [List.map_map]
    apply List.map_inj_left.mpr
    intro Yh Yh_in
    rcases Yh with ⟨Y, Y_in⟩
    rw [show List.map (List.getLast? ∘ List.cons X) (next Y Y_in).paths =
      List.map List.getLast? (next Y Y_in).paths by
        apply List.map_inj_left.mpr
        intro L L_in
        have hne := LocalTableau.paths_mem_nonempty (next Y Y_in) L L_in
        change (X :: L).getLast? = L.getLast?
        rw [List.getLast?_eq_some_getLast hne,
          List.getLast?_eq_some_getLast (List.cons_ne_nil X L)]
        exact congrArg some (List.getLast_cons hne)]
    have hIH := congrArg (List.map some) (IH Y Y_in)
    simp only [List.map_map] at hIH
    change (next Y Y_in).paths.attach.map
      (fun ⟨L, h⟩ => some (L.getLast (LocalTableau.paths_mem_nonempty _ L h))) = _ at hIH
    rw [map_attach_last (next Y Y_in).paths
      (LocalTableau.paths_mem_nonempty (next Y Y_in))] at hIH
    exact hIH
  case sim bas =>
    simp_all [paths]
    ext
    simp [paths]
    grind

/-- Any open local tableau has at least one path (from root to some end node).
Does not hold for `LocalTableau` which might end with "contradiction/closing" rule applications. -/
lemma OpenLocalTableau.paths_nonempty {X} (lt : OpenLocalTableau X) :
    lt.1.paths ≠ [] := by
  rcases lt with ⟨lt, lt_has_ends⟩
  have := @LocalTableau.pathsLast_eq_endNodes X lt
  grind

lemma LocalTableau.paths_last_basic {X} {lt : LocalTableau X} :
    ∀ L, (h : L ∈ lt.paths) → (L.getLast (LocalTableau.paths_mem_nonempty lt L h)).basic := by
  intro L L_in
  apply (@endNodesOf_basic _ _ lt)
  rw [← @LocalTableau.pathsLast_eq_endNodes _ lt]
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  grind

lemma LocalTableau.paths_saturated {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths,
      saturated (List.map Sequent.bothSides L).flatten.toFinset := by
  cases lt
  case byLocalRule lra next X_def =>
    intro L L_in
    simp [paths] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, def_L⟩
    have IH := LocalTableau.paths_saturated _ L'_in
    subst def_L
    subst X_def
    -- use separate lemma "LocalRuleApp preserves saturatedness backwards" here.
    apply @lra.preserve_saturated_up Y Y_in _ ?_ IH
    -- because L' is a path from `next y : LocalTableau Y` it must start with Y.
    have := LocalTableau.pathsHead_eq_self L'_in
    grind
  case sim Xbas =>
    simp [paths]
    have := X.basic_then_saturated
    exact Sequent.basic_then_saturated Xbas
termination_by
  X -- using DM ordering on `X` here
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-- An atomic formula anywhere in a local tableau path still occurs at the end of the path. -/
lemma LocalTableau.paths_local_atom_mem_last {X} {lt : LocalTableau X} {L} (L_in : L ∈ lt.paths) f :
    (f = ⊥ ∨ ∃ p : Nat, f = (Formula.atom_prop p) ∨ f = (~(Formula.atom_prop p))) →
      f ∈ (List.map Sequent.bothSides L).flatten →
        f ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).bothSides := by
  cases lt
  case byLocalRule lra next X_def =>
    intro f_kind f_in
    simp [paths] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have L'_ne := LocalTableau.paths_mem_nonempty (next Y Y_in) L' L'_in
    rw [List.getLast_cons L'_ne]
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at f_in
    apply LocalTableau.paths_local_atom_mem_last L'_in f f_kind
    rcases f_in with f_in_X | f_in_tail
    · have f_in_Y := lra.preserve_local_atom_down Y Y_in f f_kind (by simpa [X_def] using f_in_X)
      have head_eq := LocalTableau.pathsHead_eq_self L'_in
      rcases L' with _ | ⟨Z, L''⟩
      · contradiction
      · simp only [List.map_cons, List.flatten_cons, List.mem_append]
        left
        simp only [List.head_cons] at head_eq
        subst Y
        exact f_in_Y
    · exact f_in_tail
  case sim bas =>
    intro f_kind f_in
    simp [paths] at L_in
    subst L
    simpa using f_in
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

lemma LocalTableau.paths_locallyConsistent {X} {lt : LocalTableau X} :
    ∀ L ∈ lt.paths,
      locallyConsistent (List.map Sequent.bothSides L).flatten.toFinset := by
  intro L L_in
  have last_basic := LocalTableau.paths_last_basic L L_in
  have last_consistent := Sequent.basic_to_locallyConsistent last_basic
  unfold locallyConsistent at *
  constructor
  · intro bot_in
    simp only [Finset.mem_val, List.mem_toFinset] at bot_in
    apply last_consistent.1
    rw [← Sequent.bothSides_toFinset_eq_toFinset]
    exact List.mem_toFinset.mpr <|
      LocalTableau.paths_local_atom_mem_last L_in ⊥ (Or.inl rfl) bot_in
  · intro p p_in neg_p_in
    simp only [Finset.mem_val, List.mem_toFinset] at p_in neg_p_in
    apply last_consistent.2 p
    · rw [← Sequent.bothSides_toFinset_eq_toFinset]
      exact List.mem_toFinset.mpr <|
        LocalTableau.paths_local_atom_mem_last L_in (Formula.atom_prop p)
          (Or.inr ⟨p, Or.inl rfl⟩) p_in
    · rw [← Sequent.bothSides_toFinset_eq_toFinset]
      exact List.mem_toFinset.mpr <|
        LocalTableau.paths_local_atom_mem_last L_in (~(Formula.atom_prop p))
          (Or.inr ⟨p, Or.inr rfl⟩) neg_p_in

/-- Along any path in a local tableau, a non-atomic free diamond must be unfolded:
if `~⌈α⌉φ` occurs (unloaded) somewhere on the path and `α` is not atomic, then all formulas of
one of the unfoldings `Yset Fδ φ` occur (unloaded) on the path as well.
Analogous to `LocalTableau.paths_saturated`, but for `Sequent.wForms`. -/
lemma LocalTableau.paths_freeUnfoldDia {X} {lt : LocalTableau X} {α φ} (notAtom : ¬ α.isAtomic) :
    ∀ L ∈ lt.paths, (~⌈α⌉φ : WhateverFormula) ∈ (L.map Sequent.wForms).flatten →
      ∃ Fδ ∈ Dset α, (Yset Fδ φ).all
        (fun f => (f : WhateverFormula) ∈ (L.map Sequent.wForms).flatten) := by
  cases lt
  case byLocalRule lra next X_def =>
    intro L L_in hmem
    simp only [paths, List.mem_map, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have Y_mem_L' : Y ∈ L' := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [← this]
      exact List.head_mem _
    -- If the diamond occurs in the tail of the path, then we can use the IH:
    have tail_case : (~⌈α⌉φ : WhateverFormula) ∈ (L'.map Sequent.wForms).flatten →
        ∃ Fδ ∈ Dset α, (Yset Fδ φ).all
          (fun f => (f : WhateverFormula) ∈ ((X :: L').map Sequent.wForms).flatten) := by
      intro hin
      rcases LocalTableau.paths_freeUnfoldDia (lt := next Y Y_in) notAtom L' L'_in hin
        with ⟨Fδ, Fδ_in, hall⟩
      refine ⟨Fδ, Fδ_in, ?_⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at hall ⊢
      intro f f_in
      simp only [List.map_cons, List.flatten_cons, List.mem_append]
      exact Or.inr (hall f f_in)
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
    rcases hmem with hX | htail
    · subst X_def
      rcases lra.wForms_negBox_preserved_or_unfolded Y_in hX with hkeep | ⟨Fδ, Fδ_in, hall⟩
      · apply tail_case
        simp only [List.mem_flatten, List.mem_map]
        exact ⟨Y.wForms, ⟨Y, Y_mem_L', rfl⟩, hkeep⟩
      · refine ⟨Fδ, Fδ_in, ?_⟩
        simp only [List.all_eq_true, decide_eq_true_eq] at hall ⊢
        intro f f_in
        simp only [List.map_cons, List.flatten_cons, List.mem_append]
        refine Or.inr ?_
        simp only [List.mem_flatten, List.mem_map]
        exact ⟨Y.wForms, ⟨Y, Y_mem_L', rfl⟩, hall f f_in⟩
    · exact tail_case htail
  case sim bas =>
    intro L L_in hmem
    simp only [paths, List.mem_singleton] at L_in
    subst L_in
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hmem
    exact absurd (Sequent.isAtomic_of_basic_of_negBox_mem_wForms bas hmem) notAtom
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-- Along any path in a local tableau, a non-atomic loaded diamond must be unfolded:
if `~'⌊α⌋ξ` occurs (loaded) somewhere on the path and `α` is not atomic, then the results of
one application of the corresponding `LoadRule` occur on the path as well.
This is the loaded analogue of `LocalTableau.paths_freeUnfoldDia`. -/
lemma LocalTableau.paths_loadUnfoldDia {X} {lt : LocalTableau X} {α} {ξ : AnyFormula}
    (notAtom : ¬ α.isAtomic) :
    ∀ L ∈ lt.paths, (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ (L.map Sequent.wForms).flatten →
      ∃ ress, Nonempty (LoadRule (~'⌊α⌋ξ) ress) ∧ ∃ Fo ∈ ress,
        Fo.1.all (fun f => (f : WhateverFormula) ∈ (L.map Sequent.wForms).flatten)
        ∧ Fo.2.toList.all
            (fun nl => (WhateverFormula.negLoad nl) ∈ (L.map Sequent.wForms).flatten) := by
  cases lt
  case byLocalRule lra next X_def =>
    intro L L_in hmem
    simp only [paths, List.mem_map, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have Y_mem_L' : Y ∈ L' := by
      have := LocalTableau.pathsHead_eq_self L'_in
      rw [← this]
      exact List.head_mem _
    -- If the diamond occurs in the tail of the path, then we can use the IH:
    have tail_case : (WhateverFormula.negLoad (~'⌊α⌋ξ)) ∈ (L'.map Sequent.wForms).flatten →
        ∃ ress, Nonempty (LoadRule (~'⌊α⌋ξ) ress) ∧ ∃ Fo ∈ ress,
          Fo.1.all (fun f => (f : WhateverFormula) ∈ ((X :: L').map Sequent.wForms).flatten)
          ∧ Fo.2.toList.all
              (fun nl => (WhateverFormula.negLoad nl)
                ∈ ((X :: L').map Sequent.wForms).flatten) := by
      intro hin
      rcases LocalTableau.paths_loadUnfoldDia (lt := next Y Y_in) notAtom L' L'_in hin
        with ⟨ress, hress, Fo, Fo_in, hall, hall2⟩
      refine ⟨ress, hress, Fo, Fo_in, ?_, ?_⟩
      all_goals
        simp only [List.all_eq_true, decide_eq_true_eq] at hall hall2 ⊢
        intro f f_in
        simp only [List.map_cons, List.flatten_cons, List.mem_append]
      · exact Or.inr (hall f f_in)
      · exact Or.inr (hall2 f f_in)
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
    rcases hmem with hX | htail
    · subst X_def
      rcases lra.wForms_negLoad_preserved_or_unfolded Y_in hX with
        hkeep | ⟨ress, hress, Fo, Fo_in, hall, hall2⟩
      · apply tail_case
        simp only [List.mem_flatten, List.mem_map]
        exact ⟨Y.wForms, ⟨Y, Y_mem_L', rfl⟩, hkeep⟩
      · refine ⟨ress, hress, Fo, Fo_in, ?_, ?_⟩
        all_goals
          simp only [List.all_eq_true, decide_eq_true_eq] at hall hall2 ⊢
          intro f f_in
          simp only [List.map_cons, List.flatten_cons, List.mem_append]
          refine Or.inr ?_
          simp only [List.mem_flatten, List.mem_map]
        · exact ⟨Y.wForms, ⟨Y, Y_mem_L', rfl⟩, hall f f_in⟩
        · exact ⟨Y.wForms, ⟨Y, Y_mem_L', rfl⟩, hall2 f f_in⟩
    · exact tail_case htail
  case sim bas =>
    intro L L_in hmem
    simp only [paths, List.mem_singleton] at L_in
    subst L_in
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hmem
    exact absurd (Sequent.isAtomic_of_basic_of_negLoad_mem_wForms bas hmem) notAtom
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-- A basic formula anywhere in a local tableau path still occurs at the end of the path.
Analogous to `LocalTableau.paths_local_atom_mem_last`, but for all basic formulas. -/
lemma LocalTableau.paths_basic_mem_last {X} {lt : LocalTableau X} {L} (L_in : L ∈ lt.paths) f :
    f.basic → f ∈ (List.map Sequent.bothSides L).flatten →
      f ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).bothSides := by
  cases lt
  case byLocalRule lra next X_def =>
    intro f_basic f_in
    simp [paths] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have L'_ne := LocalTableau.paths_mem_nonempty (next Y Y_in) L' L'_in
    rw [List.getLast_cons L'_ne]
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at f_in
    apply LocalTableau.paths_basic_mem_last L'_in f f_basic
    rcases f_in with f_in_X | f_in_tail
    · have f_in_Y := lra.preserve_basic_down Y Y_in f f_basic (by simpa [X_def] using f_in_X)
      have head_eq := LocalTableau.pathsHead_eq_self L'_in
      rcases L' with _ | ⟨Z, L''⟩
      · contradiction
      · simp only [List.map_cons, List.flatten_cons, List.mem_append]
        left
        simp only [List.head_cons] at head_eq
        subst Y
        exact f_in_Y
    · exact f_in_tail
  case sim bas =>
    intro f_basic f_in
    simp [paths] at L_in
    subst L
    simpa using f_in
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-! ## Paths ending at a given end node

In the completeness proof (see `Pdl/BuildTree.lean`) Builder picks one end node of a local
tableau, and only the paths ending at that end node should be used as pre-states. -/

/-- The paths of a local tableau that end at a given node. -/
def LocalTableau.pathsTo {X} (lt : LocalTableau X) (Y : Sequent) : List (List Sequent) :=
  lt.paths.filter (fun p => p.getLast? = some Y)

@[simp]
lemma LocalTableau.mem_pathsTo {X} {lt : LocalTableau X} {Y p} :
    p ∈ lt.pathsTo Y ↔ p ∈ lt.paths ∧ p.getLast? = some Y := by
  simp [pathsTo]

/-- There is at least one path to each end node. -/
lemma LocalTableau.pathsTo_ne_nil {X} {lt : LocalTableau X} {Y} (h : Y ∈ endNodesOf lt) :
    lt.pathsTo Y ≠ [] := by
  rw [← LocalTableau.pathsLast_eq_endNodes] at h
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at h
  rcases h with ⟨L, L_in, rfl⟩
  intro hcon
  have L_in_pathsTo : L ∈ lt.pathsTo (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)) := by
    simp only [LocalTableau.mem_pathsTo]
    exact ⟨L_in, List.getLast?_eq_some_getLast _⟩
  rw [hcon] at L_in_pathsTo
  simp at L_in_pathsTo

/-- All end nodes of a local tableau for a free sequent are free.
Consequence of `LocalRuleApp.preserve_free`. -/
lemma LocalTableau.endNodesOf_free {X} (lt : LocalTableau X) (hfree : X.O = none) :
    ∀ Y ∈ endNodesOf lt, Y.O = none := by
  cases lt
  case byLocalRule lra next X_def =>
    intro Y hY
    rw [endNodesOf] at hY
    simp only [List.mem_flatten, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hY
    rcases hY with ⟨_, ⟨Z, Z_in, rfl⟩, hY⟩
    have hO : lra.O = none := by rw [X_def] at hfree; simpa [LocalRuleApp.X] using hfree
    exact LocalTableau.endNodesOf_free (next Z Z_in) (lra.preserve_free hO Z Z_in) Y hY
  case sim => intro Y hY; simp [endNodesOf] at hY; subst hY; exact hfree
termination_by X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Z_in

/-! ## Atomic loaded diamonds are preserved

A loaded diamond `~'⌊·a⌋ξ` with an *atomic* program cannot be "used up" by a local rule:
the only `LoadRule` applicable to it gives back the very same loaded formula.
This is the counterpart of `LocalTableau.paths_loadUnfoldDia` for atomic programs. -/

/-- The only `LoadRule` result for an atomic loaded diamond is the loaded diamond itself. -/
lemma LoadRule.atomic_ress_eq {a : Nat} {ξ : AnyFormula} {ress}
    (lr : LoadRule (~'⌊·a⌋ξ) ress) : ress = [([], some (~'⌊·a⌋ξ))] := by
  cases ξ
  case normal φ =>
    rw [lr.eq_unfoldDiamondLoaded']
    simp [unfoldDiamondLoaded', Dset, YsetLoad', splitLast]
  case loaded χ =>
    rw [lr.eq_unfoldDiamondLoaded]
    simp [unfoldDiamondLoaded, Dset, YsetLoad, LoadFormula.boxes]

/-- A local rule application preserves an atomic loaded diamond. -/
lemma LocalRuleApp.preserve_negLoad_atomic_down (lra : LocalRuleApp) {a : Nat} {ξ : AnyFormula}
    (h : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ lra.X.wForms) :
    ∀ Y ∈ lra.C, (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ Y.wForms := by
  intro Y Y_in
  rcases lra.wForms_negLoad_preserved_or_unfolded Y_in h with hkeep | ⟨ress, ⟨lr⟩, Fo, Fo_in, _, h2⟩
  · exact hkeep
  · rw [lr.atomic_ress_eq] at Fo_in
    simp only [List.mem_singleton] at Fo_in
    subst Fo_in
    simpa using h2

/-- An atomic loaded diamond anywhere in a local tableau path still occurs at the end of it.
Analogous to `LocalTableau.paths_basic_mem_last`, but for the loaded formula. -/
lemma LocalTableau.paths_negLoad_atomic_mem_last {X} {lt : LocalTableau X} {L}
    (L_in : L ∈ lt.paths) {a : Nat} {ξ : AnyFormula}
    (hmem : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ (L.map Sequent.wForms).flatten) :
    (WhateverFormula.negLoad (~'⌊·a⌋ξ))
      ∈ (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).wForms := by
  cases lt
  case byLocalRule lra next X_def =>
    simp only [paths, List.mem_map, List.mem_flatMap, List.mem_attach, true_and,
      Subtype.exists] at L_in
    rcases L_in with ⟨L', ⟨Y, Y_in, L'_in⟩, rfl⟩
    have L'_ne := LocalTableau.paths_mem_nonempty (next Y Y_in) L' L'_in
    rw [List.getLast_cons L'_ne]
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at hmem
    apply LocalTableau.paths_negLoad_atomic_mem_last L'_in
    rcases hmem with hX | htail
    · have hY : (WhateverFormula.negLoad (~'⌊·a⌋ξ)) ∈ Y.wForms :=
        lra.preserve_negLoad_atomic_down (by simpa [X_def] using hX) Y Y_in
      have head_eq := LocalTableau.pathsHead_eq_self L'_in
      rcases L' with _ | ⟨Z, L''⟩
      · contradiction
      · simp only [List.map_cons, List.flatten_cons, List.mem_append]
        left
        simp only [List.head_cons] at head_eq
        subst Y
        exact hY
    · exact htail
  case sim bas =>
    simp only [paths, List.mem_singleton] at L_in
    subst L_in
    simpa using hmem
termination_by
  X
decreasing_by
  subst_eqs
  exact localRuleApp.decreases_DM _ _ Y_in

/-- The last node of a path in a local tableau for a *free* sequent is free.
Consequence of `LocalTableau.endNodesOf_free`. -/
lemma LocalTableau.paths_last_free {X} {lt : LocalTableau X} (hfree : X.O = none) {L}
    (L_in : L ∈ lt.paths) :
    (L.getLast (LocalTableau.paths_mem_nonempty lt L L_in)).O = none := by
  refine LocalTableau.endNodesOf_free lt hfree _ ?_
  rw [← LocalTableau.pathsLast_eq_endNodes]
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  exact ⟨L, L_in, rfl⟩
