import Pdl.Flip
import Pdl.LocalInterpolation
import Pdl.Soundness

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

/-! ## Cluster tools -/

def repeatsOf {tab : Tableau .nil X} (s : PathIn tab) : List (PathIn tab) :=
  sorry

def all_cEdge {X} {tab : Tableau .nil X} (s : PathIn tab) : List (PathIn tab) :=
  sorry

lemma all_cEdge_spec {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    t ∈ all_cEdge s ↔ ((s ⋖_ t) ∨ s ♥ t) := by
  sorry

def all_cEdge_rev {X} {tab : Tableau .nil X} (t : PathIn tab) : List (PathIn tab) :=
  sorry

lemma all_cEdge_rev_spec {X} {tab : Tableau .nil X} (s t : PathIn tab) :
    s ∈ all_cEdge_rev t ↔ ((s ⋖_ t) ∨ s ♥ t) := by
  sorry

/-- Loaded nodes "below" the given one, also allowing ♥ steps. -/
def loadedBelow : PathIn tab → List (PathIn tab) := sorry

/-- Loaded nodes "above" the given one, also allowing *backwards* ♥ steps. -/
def loadedAbove : PathIn tab → List (PathIn tab) := sorry

/-- List of all other nodes in the same cluster, essentially a constructive version of `clusterOf`.
Computed as the intersection of `loadedAbove` and `loadedBelow`. -/
def clusterListOf (p : PathIn tab) : List (PathIn tab) := loadedBelow p  ∩  loadedBelow p

lemma clusterListOf_spec (p : PathIn tab) :
    q ∈ clusterListOf p  ↔  p ≡ᶜ q := by
  sorry

-- TODO: how to convert `clusterListOf` result back to a tree?
-- Essentially, this would incorporate Lemma 8.14 (a).

def rootOf : List (PathIn tab) → PathIn tab := sorry -- just take the shortest?

-- Or would it be better to already construct (partial) trees instead of lists directly?

-- OR just assume we are given the root of a cluster and use the tableau as it is to define `Q`?

/-- Lemma 8.14 (b) for left side -/
lemma cluster_all_left_loaded {p : PathIn tab} (h : (nodeAt p).2.2.isLeft) :
    ∀ q ∈ clusterListOf p, (nodeAt q).2.2.isLeft := by
  sorry

/-- Lemma 8.14 (b) for right side -/
lemma cluster_all_right_loaded {p : PathIn tab} (h : (nodeAt p).2.2.isRight) :
    ∀ q ∈ clusterListOf p, (nodeAt q).2.2.isRight := by
  sorry

def isExitIn : Sequent → List Sequent → Prop := sorry

instance : Decidable (isExitIn X C) := sorry

/-! ## Quasi-Tableaux -/

-- Alternative idea for Definition 9.8 quasi-tableau:
-- Instead of labelling nodes in Q with finite sequents, label them with the path to where
-- that sequent comes from in `Λ₂[C⁺]`?

inductive Typ | one | two | three -- lower case because these are not `Type`s.
open Typ

/-- Simple tree data type for `Q` in Def. 7.31. -/
inductive QuasiTab : Type | QNode : (k : Typ) → (Δ : Sequent) → (next : List QuasiTab) → QuasiTab
open QuasiTab

-- TODO add invariant?!

-- TODO use `rep` instead of `X ∈ Hist` maybe?

def Qchildren (C : List Sequent) : (k : Typ) → (Hist : List Sequent) → (X : Sequent) → List QuasiTab
| .one, Hist, X => -- case k(x)=1
    if X ∈ Hist ∨ isExitIn X C -- if x is a repeat (TODO??: in Q) or it is an exit,
      then [ ] -- then x is a leaf.
      else [ QNode .two X (Qchildren C .two (X :: Hist) X) ]
| .two, Hist, X => -- case k(x)=2
    [ QNode .three X (Qchildren C .three (X :: Hist) X) ]
| .three, Hist, X => -- case k(x)=3
    if X.basic -- (Paper does "not basic" first.)
    then
      -- unique child with .one and result of PDL rule application
      -- PROBLEM: needs uniformity?
      sorry
    else
      -- create children based on local rule
      sorry
termination_by
  1 -- O.o ... see remark after Def 7.31 ;-)
decreasing_by
  · sorry
  · sorry

/-- Quasi-Tableau from Def 9.8. Here we "start the construction", then use `Qchildren`.
No names for the nodes as we use an inductive type, so we just write `X` for `Δₓ` -/
def Q {r : PathIn tab} : QuasiTab :=
  let X := nodeAt r -- FIXME wlog we only want the right sequent. But `.R` is not enogh !?!?!?!?!?
  QNode .one X (Qchildren ((clusterListOf r).map nodeAt) .one [] X)

/-! ## Interpolants for proper clusters -/

/-- Starting at root, return the list of earliest free (i.e. unloaded nodes).
These are the "exits" from a loaded cluster.
A repeat has no exit (because to ensure termination we do not rewind here.)
Free nodes are their own (only) exit. -/
def exitsOf (tab : Tableau Hist X) : List (PathIn tab) :=
  if X.isLoaded
  then
    match tab with
    | .lrep _ => [] -- A repeat has no exit.
    | .loc _ _ lt next => (endNodesOf lt).attach.flatMap (fun ⟨Y,Y_in⟩ =>
                                  (exitsOf (next Y Y_in)).map (PathIn.loc Y_in))
    | .pdl _ _ _ next => (exitsOf next).map PathIn.pdl
  else
    [ .nil ] -- Free nodes are their own (only) exit.

lemma loaded_iff_exitsOf_non_nil {tab : Tableau Hist X} :
    X.isLoaded ↔ ∀ q ∈ exitsOf tab, q ≠ .nil := by
  constructor
  · intro Xload q q_in
    unfold exitsOf at q_in
    simp only [Xload, ↓reduceIte] at q_in
    cases tab <;> simp at q_in <;> grind
  · intro no_nil
    unfold exitsOf at no_nil
    grind

-- move to TableauPath.lean later
def PathIn.children : (p : PathIn tab) → List (PathIn tab) := sorry

/-- Specific version of `clusterInterpolation` where loaded formula is on the right side.
This may need additional hypotheses to say that we start at the root of the cluster. -/
def clusterInterpolation_right {Hist L R nlf}
    (tab : Tableau Hist (L, R, some (Sum.inr nlf)))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some (Sum.inr nlf)) := by
  sorry

/-! ### Helper lemmas for `mem_existsOf_of_flip` (dependent-type / HEq plumbing) -/

/-- `PathIn.nil` over heterogeneously-equal tableaux are heterogeneously equal. -/
theorem PathIn_nil_heq {H1 X1 H2 X2} {t1 : Tableau H1 X1} {t2 : Tableau H2 X2}
    (hH : H1 = H2) (hX : X1 = X2) (h : HEq t1 t2) :
    HEq (PathIn.nil : PathIn t1) (PathIn.nil : PathIn t2) := by
  subst hH hX; obtain rfl := eq_of_heq h; rfl

/-- This lemma about `PathIn.flip` is here because it is also about `exitsOf`. -/
lemma mem_existsOf_of_flip {Hist X} {tab : Tableau Hist X}
    (s : PathIn tab.flip) (s_in : s ∈ (exitsOf tab.flip : List (PathIn tab.flip)))
    : (PathIn_type_flip_flip ▸ s.flip) ∈ exitsOf tab := by
  induction tab with
  | loc nrep nbas lt next ih =>
    rename_i Hist X
    unfold exitsOf at s_in ⊢
    by_cases hX : X.isLoaded
    · simp only [Sequent.flip_isLoaded, hX, ↓reduceIte] at *
      simp only [Sequent.flip, Olf.flip, Tableau.flip, List.mem_flatMap, List.mem_attach,
        List.mem_map, true_and, Subtype.exists] at *
      rcases s_in with ⟨Yf, Yf_in, e, e_in, def_s⟩
      rcases exists_flip_of_endNodesOf Yf_in with ⟨Y, def_Yf, Y_in⟩
      subst def_Yf
      rcases Y with ⟨LY, RY, (_|lr_nlf_Y)⟩
      · subst def_s
        simp [Sequent.flip] at e
        simp [Sequent.flip] at *
        rw! (castMode := .all) [Olf.flip_none] at e_in; simp at e_in
        have Y_in' : (LY, RY, none) ∈ endNodesOf lt := by
          have := endNodesOf_flip Yf_in; simpa [Sequent.flip_flip] using this
        refine ⟨ (LY,RY,none), Y_in', .nil, ?_, ?_⟩
        · unfold exitsOf
          simp [Sequent.isLoaded]
        · unfold exitsOf at e_in
          simp [Sequent.isLoaded] at e_in
          subst e_in
          simp only [PathIn.flip]
          -- HEq business: `PathIn.flip` commutes with `.loc .nil` (up to casts).
          apply eq_of_heq
          refine HEq.trans ?_ (eqRec_heq_iff_heq.mpr HEq.rfl).symm
          congr 1
          · exact Sequent.map_flip_map_flip.symm
          · exact Sequent.flip_flip.symm
          · exact proof_irrel_heq _ _
          · exact proof_irrel_heq _ _
          · exact (flip_aux_LocalTableau_flip_flip_heq lt).symm
          · symm
            apply Function.hfunext rfl
            intro ⟨aL, aR, aO⟩ a' ha
            obtain rfl := eq_of_heq ha
            apply Function.hfunext
            · rw [endNodesOf_flip_flip]
            · intro b b' hb
              simp only [eqRec_heq_iff_heq]
              refine HEq.trans (Tableau_flip_heq (by simp [Sequent.flip, Olf.flip])
                (by simp [Sequent.flip, Olf.flip]) (eqRec_heq_iff_heq.mpr HEq.rfl)) ?_
              refine HEq.trans (flip_aux_Tableau_flip_flip_heq _) ?_
              congr 1 <;> first
                | exact proof_irrel_heq _ _
                | simp [Sequent.flip, Olf.flip, Option.map_map]
          · exact proof_irrel_heq _ _
          · refine PathIn_nil_heq ?_ ?_ ?_
            · simp [List.map_cons]
              exact Sequent.flip_flip.symm
            · exact Sequent.flip_flip.symm
            · symm
              refine HEq.trans (flip_aux_Tableau_flip_flip_heq _) ?_
              congr 1
      · -- Y is loaded; the `Sum.inl` and `Sum.inr` cases are identical.
        rcases lr_nlf_Y with (nlfY | nlfY) <;>
        · simp [Sequent.flip] at *
          unfold Sequent.flip at e e_in
          simp at e e_in
          unfold Olf.flip at e e_in
          simp at e e_in
          have := endNodesOf_flip Yf_in
          simp only [Sequent.flip_flip] at this
          refine ⟨(LY, RY, some _), this, ?_⟩
          use (PathIn_type_flip_flip ▸ e.flip)
          refine ⟨ih _ _ e e_in, ?_⟩
          -- `PathIn.flip` commutes with `.loc` (up to casts).
          subst def_s
          apply eq_of_heq
          simp only [PathIn.flip]
          refine HEq.trans ?_ (eqRec_heq_iff_heq.mpr HEq.rfl).symm
          congr 1
          case e_5 => exact (flip_aux_LocalTableau_flip_flip_heq lt).symm
          case e_6 =>
            symm
            apply Function.hfunext rfl
            intro a a' ha
            obtain rfl := eq_of_heq ha
            obtain ⟨aL, aR, aO⟩ := a
            apply Function.hfunext
            · rw [endNodesOf_flip_flip]
            · intro b b' hb
              simp only [eqRec_heq_iff_heq]
              refine HEq.trans (Tableau_flip_heq (by simp [Sequent.flip, Olf.flip])
                (by simp [Sequent.flip, Olf.flip]) (eqRec_heq_iff_heq.mpr HEq.rfl)) ?_
              refine HEq.trans (flip_aux_Tableau_flip_flip_heq _) ?_
              congr 1 <;> first
                | exact proof_irrel_heq _ _
                | simp [Sequent.flip, Olf.flip, Option.map_map]
          case e_9 =>
            simp only [eqRec_heq_iff_heq]
            exact (flip_aux_eq_mpr_heq _ _).symm
          all_goals first
            | exact proof_irrel_heq _ _
            | exact Sequent.flip_flip.symm
            | simp
    · simp only [Sequent.flip_isLoaded, hX, Bool.false_eq_true, ↓reduceIte,
        List.mem_singleton] at *
      subst s_in
      apply eq_of_heq
      rw [eqRec_heq_iff_heq]
      simp only [PathIn.flip]
      congr 1 <;> simp
  | pdl nrep bas r next ih =>
    rename_i Hist X Y
    unfold exitsOf at s_in ⊢
    by_cases hX : X.isLoaded
    · simp only [Sequent.flip_isLoaded, hX, ↓reduceIte] at *
      simp_all only [Sequent.flip, Olf.flip, Tableau.flip, List.mem_map]
      rcases s_in with ⟨e, e_in, def_s⟩
      rcases Y with ⟨LY, RY, (_|lr_nlf_Y)⟩ -- to get that Y is loaded
      · subst def_s
        unfold exitsOf at ⊢ e_in
        simp [Sequent.isLoaded] at *
        subst e_in
        -- `PathIn.flip` of `.pdl .nil` is `.pdl .nil` (up to casts).
        exact (PathIn.flip_flip (PathIn.pdl PathIn.nil)).symm
      · refine ⟨PathIn_type_flip_flip ▸ e.flip, ?_, ?_⟩
        · exact ih e e_in
        rw [← def_s]
        simp
        -- HEq business: `PathIn.flip` commutes with `.pdl` (up to casts).
        apply eq_of_heq
        simp only [PathIn.flip]
        refine HEq.trans ?_ (eqRec_heq_iff_heq.mpr HEq.rfl).symm
        congr 1 <;> first
          | rfl
          | exact Sequent.flip_flip.symm
          | exact Sequent.map_flip_map_flip.symm
          | exact (flip_aux_PdlRule_flip_flip_heq r).symm
          | exact flip_aux_PdlRule_flip_flip_heq r
          | exact (flip_aux_Tableau_flip_flip_heq next).symm
          | exact flip_aux_Tableau_flip_flip_heq next
          | exact eqRec_heq_iff_heq.mpr HEq.rfl
          | exact proof_irrel_heq _ _
    · simp only [Sequent.flip_isLoaded, hX, Bool.false_eq_true, ↓reduceIte,
        List.mem_singleton] at *
      subst s_in
      apply eq_of_heq
      rw [eqRec_heq_iff_heq]
      simp only [PathIn.flip]
      congr 1 <;> simp
  | lrep lpr =>
    rename_i X Hist
    unfold exitsOf at s_in ⊢
    by_cases hX : X.isLoaded
    · simp only [Sequent.flip_isLoaded, hX, ↓reduceIte] at *
      simp [Sequent.flip, Olf.flip] at *
      simp_all [Tableau.flip]
    · simp only [Sequent.flip_isLoaded, hX, Bool.false_eq_true, ↓reduceIte,
        List.mem_singleton] at *
      subst s_in
      apply eq_of_heq
      rw [eqRec_heq_iff_heq]
      simp only [PathIn.flip]
      congr 1 <;> simp

def exitsOf_flip {tab : Tableau Hist (L, R, some nlf)}
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e)) :
    ∀ e ∈ exitsOf tab.flip, PartInterpolant (nodeAt e) := by
  intro e e_in
  specialize exitIPs _ (mem_existsOf_of_flip _ e_in)
  have : (nodeAt (PathIn_type_flip_flip ▸ e.flip)) = (nodeAt e).flip := by
    convert PathIn.nodeAt_flip <;> simp_all [Sequent.flip, Olf.flip]
  rw [this] at exitIPs
  rcases exitIPs with ⟨θ, ⟨hVoc, hL, hR⟩⟩
  refine ⟨~θ, ?_, ?_, ?_⟩
  · intro x x_in
    specialize hVoc x_in
    simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.flip_left, Sequent.flip_right,
      Finset.mem_inter, Finset.mem_sup, List.mem_toFinset, List.mem_map, id_eq,
      exists_exists_and_eq_and] at hVoc
    aesop
  · simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.flip_left, Sequent.flip_right, listHasSat,
    List.mem_cons, forall_eq_or_imp, evaluate, not_exists, not_and, not_forall, not_not] at *
    intro W M w w_θ
    exact hR W M w w_θ
  · simp only [jvoc, List.fvoc, Vocab.fromList, Sequent.flip_left, Sequent.flip_right, listHasSat,
    List.mem_cons, forall_eq_or_imp, evaluate, not_exists, not_and, not_forall] at *
    intro W M w not_w_θ
    exact hL W M w not_w_θ

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩
  · clear l_ip r_ip
    simp_all
    intro x x_in
    specialize voc x_in
    simp_all
  · simp_all
  · simp_all


/-! ### Cluster Interpolation -/

/-- Given a tableau where the root is loaded, and exit interpolants, interpolate the root. -/
def clusterInterpolation {Hist L R snlf}
    (tab : Tableau Hist (L, R, some snlf))
    (exitIPs : ∀ e ∈ exitsOf tab, PartInterpolant (nodeAt e))
    : PartInterpolant (L, R, some snlf) := by
  cases snlf
  case inl nlf =>
    -- We "flip" the left/right sides of `tab` so we can apply the wlog version.
    let f_tab := tab.flip
    let f_exitIPs : ∀ e ∈ exitsOf tab.flip, PartInterpolant (nodeAt e) := exitsOf_flip exitIPs
    have := @clusterInterpolation_right _ _ _ nlf f_tab f_exitIPs
    rcases this with ⟨θ, isInter⟩
    refine ⟨~θ, ?_⟩
    apply IsPartInterpolant.flip isInter
  case inr nlf =>
    exact @clusterInterpolation_right _ _ _ nlf tab exitIPs

/-- Ideally this would be a computable `def` and not an existential.
But currently `PathIn.strong_upwards_inductionOn` only works with `Prop` motive. -/
theorem tabToIntAt {X : Sequent} (tab : Tableau .nil X) (s : PathIn tab) :
    ∃ θ, isPartInterpolant (nodeAt s) θ := by
  induction s using PathIn.strong_upwards_inductionOn -- Strong!
  next s IH =>
  -- case distinction before or after `induction`?
  by_cases (nodeAt s).isLoaded
  case pos s_loaded =>
    -- HARD case, here we want to use `clusterInterpolation` and that is why we used
    -- `PathIn.strong_upwards_inductionOn` to have an IH applicable to "far away" exits.
    -- WORRY: the IH here is not morally true, might later need to restrict it to free nodes.
    -- Now we use `s_loaded` to get the right input type for `clusterInterpolation`.
    rcases tab_s_def : tabAt s with ⟨Hist, ⟨L,R, olf⟩, tabNew⟩
    cases olf
    case none =>
      exfalso
      unfold nodeAt at s_loaded
      rw [tab_s_def] at s_loaded
      simp [Sequent.isLoaded] at s_loaded
    case some lr_nlf =>
      let myExitIPs : ∀ e ∈ exitsOf tabNew, PartInterpolant (nodeAt e) := by
        intro e e_in
        specialize @IH (s.append (tab_s_def ▸ e)) ?_
        · apply PathIn.lt_append_non_nil _ tab_s_def
          -- Use that `exitsOf` something loaded are proper successors.
          unfold nodeAt at s_loaded
          have := (@loaded_iff_exitsOf_non_nil _ _ (tabAt s).2.2).mp s_loaded (tab_s_def ▸ e) ?_
          · convert this <;> grind
          grind
        have := IH.choose_spec
        simp only [nodeAt_append] at this IH
        refine ⟨IH.choose, ?_⟩
        convert this <;> try rw [tab_s_def]
        rw! [tab_s_def]; simp
      have := @clusterInterpolation _ L R lr_nlf tabNew myExitIPs
      rcases this with ⟨θ, h_θ⟩
      use θ
      unfold nodeAt
      rw [tab_s_def]
      simp
      exact h_θ
  case neg s_free =>
    -- EASY case, singleton cluster because not loaded.
    simp at s_free
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
    ∃ θ, isPartInterpolant X θ := tabToIntAt tab .nil
