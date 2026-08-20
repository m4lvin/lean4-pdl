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

/-! ## helpers belonging elsewhere -/

-- move to TableauPath.lean later
def PathIn.children (p : PathIn tab) : List {q : PathIn tab // p ⋖_ q} :=
  match h : tabAt p with
  | ⟨H, X, .loc nflprep nbas lt next⟩ =>
      (endNodesOf lt).attach.map (fun ⟨Y,Y_in⟩ => ⟨_, edge_append_loc_nil _ _ Y_in h⟩ )
  | ⟨H,X, .pdl nflprep bas r next⟩ =>
      [ ⟨_, @edge_append_pdl_nil _ _ _ p (h ▸ nflprep) (h ▸ bas) _ (by convert r; grind)
            (by convert next <;> grind) (by simp_all; grind)⟩ ]
  | ⟨H,X, .lrep _⟩ => []

def PathIn.isLPR (p : PathIn tab) : Prop := (tabAt p).2.2.isLrep

/-! ## NEW structure idea for clusters -/

/-- Being a *cluster root*: there is no `◃` path from `s` back to a parent of `s`.
As a parent `p` of `s` always has a `◃` path to `s`, this says that no parent of `s` is
`≡ᶜ` to `s` (see `PathIn.isClusterRoot_iff`), i.e. that `s` is the first node of its own
cluster along the branch leading to `s`.

Note that this is *vacuously true* for `.nil`, the root of the whole tableau, which has no
parent at all. This is why we quantify over all parents instead of demanding that a parent
exists: the root of a tableau may already be loaded. -/
def PathIn.isClusterRoot {X} {tab : Tableau .nil X} (s : PathIn tab) : Prop :=
  ∀ p : PathIn tab, p ⋖_ s → ¬ s ◃* p

/-- The root of the whole tableau is a cluster root, because it has no parent. -/
lemma PathIn.isClusterRoot_nil {X} {tab : Tableau .nil X} :
    (PathIn.nil : PathIn tab).isClusterRoot := by
  intro p p_nil
  exfalso
  have := edge_then_length_lt p_nil
  simp at this

/-- Equivalent formulation of `PathIn.isClusterRoot` using `≡ᶜ`. -/
lemma PathIn.isClusterRoot_iff {X} {tab : Tableau .nil X} {s : PathIn tab} :
    s.isClusterRoot ↔ ∀ p : PathIn tab, p ⋖_ s → ¬ p ≡ᶜ s := by
  unfold PathIn.isClusterRoot cEquiv
  constructor
  · rintro h p p_s ⟨-, s_p⟩
    exact h p p_s s_p
  · intro h p p_s s_p
    exact h p p_s ⟨Relation.ReflTransGen.single (Or.inl p_s), s_p⟩

/-- If the parent of `t` is free, then `t` is a cluster root.
This is the case for all children of free nodes in the recursion of `tabToIntAt`. -/
lemma PathIn.isClusterRoot_of_edge_from_free {X} {tab : Tableau .nil X} {s t : PathIn tab}
    (s_free : (nodeAt s).isFree) (s_t : s ⋖_ t) : t.isClusterRoot := by
  rw [PathIn.isClusterRoot_iff]
  intro p p_t
  have p_eq_s : p = s := edge_leftInjective _ _ _ p_t s_t
  subst p_eq_s
  exact ePropB.h _ _ (ePropB.c_single _ _ s_free s_t)

/-- If all parents of `s` are free — which for a loaded `s` says exactly that `s` is the
first loaded node along the branch leading to it — then `s` is a cluster root. -/
lemma PathIn.isClusterRoot_of_parents_free {X} {tab : Tableau .nil X} {s : PathIn tab}
    (h : ∀ p : PathIn tab, p ⋖_ s → (nodeAt p).isFree) : s.isClusterRoot := by
  intro p p_s
  exact PathIn.isClusterRoot_of_edge_from_free (h p p_s) p_s p p_s

/-- Def 8.14: `e` is an *exit* of the cluster of `s`, i.e. `e ∈ C⁺ \ C` where `C` is the
cluster of `s`: it is not in the cluster of `s`, but it is a child of a node in it. -/
def isExitOf {X} {tab : Tableau .nil X} (s e : PathIn tab) : Prop :=
  ¬ (e ≡ᶜ s)  ∧  ∃ t : PathIn tab, (t ≡ᶜ s) ∧ t ⋖_ e

/-- Exits of a cluster are cluster roots.
This is one of the two things needed to keep the `tabToIntAt` recursion going. -/
lemma isClusterRoot_of_isExitOf {X} {tab : Tableau .nil X} {s e : PathIn tab}
    (h : isExitOf s e) : e.isClusterRoot := by
  rcases h with ⟨e_not_s, t, t_s, t_e⟩
  rw [PathIn.isClusterRoot_iff]
  intro p p_e p_e_equiv
  absurd e_not_s
  have p_eq_t : p = t := edge_leftInjective _ _ _ p_e t_e
  subst p_eq_t
  exact ⟨p_e_equiv.2.trans t_s.1, t_s.2.trans p_e_equiv.1⟩

/-- Any `⋖_` path is also a `◃` path. -/
lemma cReach_of_le {X} {tab : Tableau .nil X} {s t : PathIn tab} (h : s ≤ t) : s ◃* t :=
  h.mono (fun _ _ h => Or.inl h)

/-- If `u < s` then some parent of `s` is reachable from `u` (possibly `u` itself). -/
lemma exists_parent_of_lt {X} {tab : Tableau .nil X} {u s : PathIn tab} (h : u < s) :
    ∃ p : PathIn tab, u ≤ p ∧ p ⋖_ s := by
  cases h with
  | single u_s => exact ⟨u, Relation.ReflTransGen.refl, u_s⟩
  | tail u_d d_s => exact ⟨_, u_d.to_reflTransGen, d_s⟩

/-- Lemma 8.15 (a): clusters are subtrees. Here in the form we need it: the root of a
cluster is `≤` all nodes of its cluster. -/
lemma PathIn.le_of_cEquiv_of_isClusterRoot {X} {tab : Tableau .nil X} {s t : PathIn tab}
    (s_cr : s.isClusterRoot) (h : s ≡ᶜ t) : s ≤ t := by
  -- No node of the cluster of `s` is a proper ancestor of `s`:
  have not_lt : ∀ u : PathIn tab, u < s → s ◃* u → False := by
    intro u u_lt_s s_to_u
    obtain ⟨p, u_le_p, p_s⟩ := exists_parent_of_lt u_lt_s
    exact s_cr p p_s (s_to_u.trans (cReach_of_le u_le_p))
  -- Now walk along the `◃` path from `s`, staying inside the cluster.
  have key : ∀ u : PathIn tab, s ◃* u → u ◃* s → s ≤ u := by
    intro u s_to_u
    induction s_to_u with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail v u s_v v_u ih =>
      intro u_to_s
      have s_to_u : s ◃* u := s_v.tail v_u
      have s_le_v : s ≤ v := ih (Relation.ReflTransGen.head v_u u_to_s)
      rcases v_u with v_e_u | v_h_u
      · -- A child step goes down, so we can just extend the path.
        exact s_le_v.tail v_e_u
      · -- A companion step goes up, so we must use that `s` is a cluster root.
        have u_lt_v : u < v := companion_lt v_h_u
        rcases eq_or_ne s v with s_eq_v | s_ne_v
        · exact absurd (s_eq_v ▸ u_lt_v) (fun h => (not_lt u h s_to_u).elim)
        · have s_lt_v : s < v := Relation.TransGen_of_ReflTransGen s_le_v s_ne_v
          rcases path_revEuclidean' s u v s_lt_v u_lt_v with s_le_u | u_le_s
          · exact s_le_u
          · rcases eq_or_ne u s with u_eq_s | u_ne_s
            · exact u_eq_s ▸ Relation.ReflTransGen.refl
            · exact absurd (Relation.TransGen_of_ReflTransGen u_le_s u_ne_s)
                (fun h => (not_lt u h s_to_u).elim)
  exact key t h.1 h.2

/-- Exits of the cluster of a cluster root `s` are proper descendants of `s`.
This is the second thing needed to keep the `tabToIntAt` recursion going, and it needs
that clusters are subtrees, i.e. Lemma 8.15 (a). -/
lemma lt_of_isExitOf {X} {tab : Tableau .nil X} {s e : PathIn tab}
    (s_cr : s.isClusterRoot) (h : isExitOf s e) : s < e := by
  obtain ⟨-, t, t_s, t_e⟩ := h
  have s_le_t : s ≤ t := PathIn.le_of_cEquiv_of_isClusterRoot s_cr ((cEquiv.symm t s).mp t_s)
  exact Relation.TransGen.tail' s_le_t t_e

/-- A cluster, starting at a right-loaded `root` which is not ≡ᶜ to any parent of it.

Note that there is no explicit `parent` field: the root of the whole tableau may itself be
loaded and then has no parent. Instead, `root_not_to_parent` quantifies over all parents of
the root — which is exactly the property `PathIn.isClusterRoot` that `tabToIntAt` maintains
as an invariant. -/
structure LoadedCluster {X} (tab : Tableau .nil X) where
  /-- The root of the cluster. -/
  root : PathIn tab
  /-- There is no ◃ path from the root to any parent of it. -/
  root_not_to_parent : root.isClusterRoot
  /-- The root is loaded on the right. -/
  root_loaded_right : (nodeAt root).2.2.isRight
  /-- List of all paths in the cluster. -/
  CL : List (PathIn tab)
  /-- The root is in the cluster. -/
  root_mem_CL : root ∈ CL
  /-- All elements of `CL` are ≡ᶜ and thus can reach each other. -/
  CL_equiv : ∀ s ∈ CL, ∀ t ∈ CL, s ≡ᶜ t
  /-- All paths that are ≡ᶜ to something in `CL` are also in `CL`. -/
  CL_complete : ∀ s ∈ CL, ∀ t, (s ≡ᶜ t) → t ∈ CL
  /-- The root can reach all nodes of the cluster. -/
  root_reaches_all : ∀ s ∈ CL, root ◃* s

-- The entry point is `clusterInterpolation`, which is given a node together with a proof
-- that it is a cluster root, and uses `LoadedCluster.ofClusterRoot` below.

/-- Make the `LoadedCluster` of a right-loaded node that is the first node of its cluster.
This is the way `tabToIntAt` now gets hold of a `LoadedCluster`. -/
def LoadedCluster.ofClusterRoot {X} {tab : Tableau .nil X} (s : PathIn tab)
    (s_cr : s.isClusterRoot) (s_loaded_right : (nodeAt s).2.2.isRight) : LoadedCluster tab where
  root := s
  root_not_to_parent := s_cr
  root_loaded_right := s_loaded_right
  CL := clusterListOf s
  root_mem_CL := by
    rw [clusterListOf_spec]
    exact (eProp tab).1.refl s
  CL_equiv := by
    intro u u_in v v_in
    rw [clusterListOf_spec] at u_in v_in
    exact (eProp tab).1.trans ((eProp tab).1.symm u_in) v_in
  CL_complete := by
    intro u u_in v u_v
    rw [clusterListOf_spec] at u_in ⊢
    exact (eProp tab).1.trans u_in u_v
  root_reaches_all := by
    intro u u_in
    rw [clusterListOf_spec] at u_in
    exact u_in.1

-- TODO: make ≣ᶜ decidable

/-- The exits of the cluster, i.e. `C⁺ \ C` from Def 8.14. -/
def LoadedCluster.exits (C : LoadedCluster tab) : List (PathIn tab) :=
  (C.CL.flatMap (fun t => t.children.map Subtype.val)).filter (fun e => e ∉ C.CL)

/-- C⁺, the cluster plus its exits. -/
def LoadedCluster.CL_plus (C : LoadedCluster tab) : List (PathIn tab) :=
  C.CL ++ C.exits

/-- The list `C.exits` contains exactly the exits in the sense of `isExitOf`. -/
lemma LoadedCluster.mem_exits_iff (C : LoadedCluster tab) (e : PathIn tab) :
    e ∈ C.exits ↔ isExitOf C.root e := by
  sorry

/-- Lemma 9.4 (a) -/
lemma LoadedCluster.all_right_loaded (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).2.2.isRight := by
  sorry

/-- Lemma 9.4 (b) -/
lemma LoadedCluster.left_empty_iff_root_left_empty (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).2.1 = [] ↔ (nodeAt C.root).2.1 = [] := by
  sorry

/-- Part of Lemma 9.4 (c): All children of t belong to C⁺. -/
lemma LoadedCluster.children_in_plus (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ∀ c ∈ t.children, c.val ∈ C.CL_plus := by
  sorry

/-- Part of Lemma 9.4 (c): If t is not an lpr, then at least one child is in C. -/
lemma LoadedCluster.nonLpr_some_child_in_C (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ¬ t.isLPR → ∃ c ∈ t.children, t ∈ C.CL := by
  sorry

/-- Part of Lemma 9.4 (c): If t is an lpr, then its companion is in C. -/
lemma LoadedCluster.lpr_comp_in_C (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, t ♥ comp → comp ∈ C.CL := by
  sorry

/-- Def 9.6: All nodes in cluster with a certain list (WORRY should it be set??) on the right.
TODO: `.right` might not get or not keep track of the loaded formula!
Better use `List WhateverFormula` and `Sequent.wForms` here maybe?
-/
def LoadedCluster.nodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
    C.CL.filter (fun p => decide ((nodeAt p).right = Δ))

def LoadedCluster.plusNodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
    C.CL_plus.filter (fun p => decide ((nodeAt p).right = Δ))

-- TODO defs "where a left/right rule is applied"

-- TODO Lemma 9.7 (a)

-- TODO Lemma 9.7 (b)

-- TODO Lemma 9.7 (c)

-- TODO Lemma 9.7 (d)

-- TODO Lemma 9.7 (e)

-- TODO Lemma 9.7 (f)


def isExitIn : Sequent → List Sequent → Prop := sorry

instance : Decidable (isExitIn X C) := sorry


-- Or would it be better to already construct (partial) trees instead of lists directly?

-- OR just assume we are given the root of a cluster and use the tableau as it is to define `Q`?

/-! ## Quasi-Tableaux (Def 9.8) -/

-- Alternative idea for quasi-tableau:
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
    if X ∈ Hist ∨ isExitIn X C -- if x is a repeat (in Q) or it is an exit,
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
  1 -- O.o ... remark after Def 9.8, but it does not say how to convince Lean of termination ;-)
decreasing_by
  · sorry
  · sorry

/-- Quasi-Tableau from Def 9.8. Here we "start the construction", then use `Qchildren`.
No names for the nodes as we use an inductive type, so we just write `X` for `Δₓ` -/
def Q {r : PathIn tab} : QuasiTab :=
  let X := nodeAt r -- FIXME wlog we only want the right sequent. But `.R` is not enogh !?!?!?!?!?
  QNode .one X (Qchildren ((clusterListOf r).map nodeAt) .one [] X)

/-! ## Interpolants for proper clusters -/

/-- Lemma 9.3 for the case where the loaded formula is on the right side:
given interpolants for all exits of the cluster `C`, interpolate the root of `C`. -/
def clusterInterpolation_right {X} {tab : Tableau .nil X} (C : LoadedCluster tab)
    (exitIPs : ∀ e ∈ C.exits, PartInterpolant (nodeAt e))
    : PartInterpolant (nodeAt C.root) := by
  sorry

/-! ### Flipping the tableaux to make left side loaded wlog.  -/

/-- When `X` is an interpolant for `X`, then `~θ` is an interpolant for `X.flip`. -/
lemma IsPartInterpolant.flip : isPartInterpolant X θ → isPartInterpolant X.flip (~θ) := by
  rintro ⟨voc, l_ip, r_ip⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp_all
  grind

/-! ### Flipping paths in a whole tableau

The three `sorry`s here are pure bookkeeping: flipping a whole tableau is a bijection on
nodes that preserves the child relation `⋖_` and the companion relation `♥`, and hence
also `◃`, `≡ᶜ`, clusters and their exits. -/

/-- Undo `PathIn.flip`: flipping twice is the identity (up to the cast). -/
def PathIn.unflip {X} {tab : Tableau .nil X} (p : PathIn tab.flip) : PathIn tab :=
  PathIn_type_flip_flip ▸ p.flip

@[simp]
lemma PathIn.flip_unflip {X} {tab : Tableau .nil X} (p : PathIn tab.flip) :
    p.unflip.flip = p := by
  sorry

/-- Flipping a tableau does not change which nodes are children of which. -/
lemma edge_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ⋖_ q.flip) ↔ p ⋖_ q := by
  sorry

/-- Flipping a tableau changes neither the child nor the companion relation,
hence it also does not change reachability. -/
lemma cReach_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ◃* q.flip) ↔ p ◃* q := by
  sorry

lemma cEquiv_flip {X} {tab : Tableau .nil X} {p q : PathIn tab} :
    (p.flip ≡ᶜ q.flip) ↔ p ≡ᶜ q := by
  unfold cEquiv
  rw [cReach_flip, cReach_flip]

lemma PathIn.isClusterRoot_flip {X} {tab : Tableau .nil X} {p : PathIn tab}
    (h : p.isClusterRoot) : (p.flip).isClusterRoot := by
  intro q q_edge
  rw [← PathIn.flip_unflip q] at q_edge ⊢
  rw [edge_flip] at q_edge
  rw [cReach_flip]
  exact h _ q_edge

lemma isExitOf_flip {X} {tab : Tableau .nil X} {s e : PathIn tab} :
    isExitOf s.flip e.flip ↔ isExitOf s e := by
  unfold isExitOf
  rw [cEquiv_flip]
  constructor
  · rintro ⟨no, t, t_s, t_e⟩
    refine ⟨no, t.unflip, ?_, ?_⟩
    · rw [← cEquiv_flip, PathIn.flip_unflip]
      exact t_s
    · rw [← edge_flip, PathIn.flip_unflip]
      exact t_e
  · rintro ⟨no, t, t_s, t_e⟩
    exact ⟨no, t.flip, cEquiv_flip.mpr t_s, edge_flip.mpr t_e⟩

/-- Transport an interpolant to the flipped tableau. -/
def PartInterpolant.flipPath {X} {tab : Tableau .nil X} {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p)) : PartInterpolant (nodeAt p.flip) :=
  ⟨~ip.1, by rw [PathIn.nodeAt_flip]; exact IsPartInterpolant.flip ip.2⟩

/-- Transport an interpolant back from the flipped tableau. -/
def PartInterpolant.unflipPath {X} {tab : Tableau .nil X} {p : PathIn tab}
    (ip : PartInterpolant (nodeAt p.flip)) : PartInterpolant (nodeAt p) := by
  refine ⟨~ip.1, ?_⟩
  have h : (nodeAt p.flip).flip = nodeAt p := by rw [PathIn.nodeAt_flip, Sequent.flip_flip]
  exact h ▸ IsPartInterpolant.flip ip.2

/-! ### Cluster Interpolation -/

/-- Lemma 9.3: Given a loaded node `s` that is the first node of its cluster, and given
interpolants for all exits of that cluster, we get an interpolant for `s`.

Note how `s_cr` is exactly what is needed to make a `LoadedCluster` here.

This is `noncomputable` only because we decide on which side the loaded formula is. -/
noncomputable def clusterInterpolation {X} {tab : Tableau .nil X} (s : PathIn tab)
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
