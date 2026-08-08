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
