import Pdl.Flip
import Pdl.KeepRight
import Pdl.LocalInterpolation

/-! # Defining interpolants (Section 9)

Note that we can skip much of Subsection 8.2 because we worked already with split tableaux anyway.

NOTE: We may need extra work for *uniformity* though.
-/

variable {X : Sequent} {tab : Tableau .nil X}

/-! ## Collecting Cluster Nodes in a List

We define the lists `loadedBelow` and `loadedAbove` of nodes that are reachable from / can reach
a given node via `◃` *by filtering `allPaths`*: a tableau has only finitely many nodes and
`PathIn.elem_allPaths` says that `allPaths tab` contains all of them, so we can simply keep
those nodes that are `◃`-related to `p` in the desired direction.
Then `clusterListOf_spec` is immediate. -/

/-- Loaded nodes "below" the given one, also allowing ♥ steps. Includes the node itself. -/
def loadedBelow (p : PathIn tab) : List (PathIn tab) :=
  p :: (allPaths tab).filter (fun q => ((p ◃⁺ q) ∧ (nodeAt q).isLoaded))

/-- Loaded nodes "above" the given one, also allowing *backwards* ♥ steps.
Includes the node itself. -/
def loadedAbove (p : PathIn tab) : List (PathIn tab) :=
  p :: (allPaths tab).filter (fun q => decide ((q ◃⁺ p) ∧ (nodeAt q).isLoaded))

@[simp]
lemma mem_loadedBelow {p q : PathIn tab} :
    q ∈ loadedBelow p  ↔  q = p ∨ ((p ◃⁺ q) ∧ (nodeAt q).isLoaded) := by
  simp [loadedBelow, PathIn.elem_allPaths]

@[simp]
lemma mem_loadedAbove {p q : PathIn tab} :
    q ∈ loadedAbove p  ↔  q = p ∨ ((q ◃⁺ p) ∧ (nodeAt q).isLoaded) := by
  simp [loadedAbove, PathIn.elem_allPaths]

/-- A free node is alone in its cluster (cf. Remark 4.18 in the paper). -/
lemma eq_of_cEquiv_of_isFree {p q : PathIn tab}
    (p_free : (nodeAt p).isFree) (p_q : p ≡ᶜ q) : q = p := by
  rcases p_q with ⟨p_to_q, q_to_p⟩
  rcases Relation.ReflTransGen.cases_head p_to_q with p_eq_q | ⟨l, p_l, l_to_q⟩
  · exact p_eq_q.symm
  · exfalso
    have l_to_p : l ◃* p := Relation.ReflTransGen.trans l_to_q q_to_p
    cases p_l
    case inl p_edge_l =>
      have p_lt_l := ePropB.c_single p l p_free p_edge_l
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp l_to_p with l_eq_p | l_c_p
      · subst l_eq_p
        exact path_is_irreflexive (Relation.TransGen.single p_edge_l)
      · exact p_lt_l.2 l_c_p
    case inr p_heart_l =>
      have := (companion_loaded p_heart_l).1
      simp only [Sequent.isFree, this] at p_free
      simp at p_free

/-- List of all other nodes in the same cluster, essentially a constructive version of `clusterOf`.
Computed as the intersection of `loadedAbove` and `loadedBelow`. -/
def clusterListOf (p : PathIn tab) : List (PathIn tab) :=
  loadedBelow p  ∩  loadedAbove p

lemma clusterListOf_spec {q : PathIn tab} (p : PathIn tab) :
    q ∈ clusterListOf p  ↔  p ≡ᶜ q := by
  rw [clusterListOf, List.mem_inter_iff, mem_loadedBelow, mem_loadedAbove]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | ⟨p_q, -⟩
    · exact (eProp tab).1.refl _
    · rcases h2 with rfl | ⟨q_p, -⟩
      · exact (eProp tab).1.refl _
      · exact ⟨p_q.to_reflTransGen, q_p.to_reflTransGen⟩
  · intro p_c_q
    rcases eq_or_ne q p with rfl | q_ne_p
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have q_loaded : (nodeAt q).isLoaded := by
        by_contra q_not_loaded
        exact q_ne_p (eq_of_cEquiv_of_isFree
          (by simp_all [Sequent.isFree]) ((cEquiv.symm p q).mp p_c_q)).symm
      exact ⟨ Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.1 (Ne.symm q_ne_p), q_loaded⟩
            , Or.inr ⟨Relation.TransGen_of_ReflTransGen p_c_q.2 q_ne_p, q_loaded⟩ ⟩

/-! ## Cluster roots -/

/-- Being a *cluster root*: there is no `◃` path from `s` back to a parent of `s`.
As a parent `p` of `s` always has a `◃` path to `s`, this says that no parent of `s` is
`≡ᶜ` to `s` (see `PathIn.isClusterRoot_iff`), i.e. that `s` is the first node of its own
cluster along the branch leading to `s`.

Note that this is *vacuously true* for `.nil`, the root of the whole tableau, which has no
parent at all. This is why we quantify over all parents instead of demanding that a parent
exists: the root of a tableau may already be loaded. -/
def PathIn.isClusterRoot (s : PathIn tab) : Prop :=
  ∀ p : PathIn tab, p ⋖_ s → ¬ s ◃* p

lemma PathIn.isClusterRoot_flip {p : PathIn tab}
    (h : p.isClusterRoot) : (p.flip).isClusterRoot := by
  intro q q_edge
  rw [← PathIn.flip_unflip q] at q_edge ⊢
  rw [edge_flip] at q_edge
  rw [cReach_flip]
  exact h _ q_edge

/-- The root of the whole tableau is a cluster root, because it has no parent. -/
lemma PathIn.isClusterRoot_nil :
    (PathIn.nil : PathIn tab).isClusterRoot := by
  intro p p_nil
  exfalso
  have := edge_then_length_lt p_nil
  simp at this

/-- Equivalent formulation of `PathIn.isClusterRoot` using `≡ᶜ`. -/
lemma PathIn.isClusterRoot_iff {s : PathIn tab} :
    s.isClusterRoot ↔ ∀ p : PathIn tab, p ⋖_ s → ¬ p ≡ᶜ s := by
  unfold PathIn.isClusterRoot cEquiv
  constructor
  · rintro h p p_s ⟨-, s_p⟩
    exact h p p_s s_p
  · intro h p p_s s_p
    exact h p p_s ⟨Relation.ReflTransGen.single (Or.inl p_s), s_p⟩

/-- If the parent of `t` is free, then `t` is a cluster root.
This is the case for all children of free nodes in the recursion of `tabToIntAt`. -/
lemma PathIn.isClusterRoot_of_edge_from_free {s t : PathIn tab}
    (s_free : (nodeAt s).isFree) (s_t : s ⋖_ t) : t.isClusterRoot := by
  rw [PathIn.isClusterRoot_iff]
  intro p p_t
  have p_eq_s : p = s := edge_leftInjective _ _ _ p_t s_t
  subst p_eq_s
  exact ePropB.h _ _ (ePropB.c_single _ _ s_free s_t)

/-- If all parents of `s` are free — which for a loaded `s` says exactly that `s` is the
first loaded node along the branch leading to it — then `s` is a cluster root. -/
lemma PathIn.isClusterRoot_of_parents_free {s : PathIn tab}
    (h : ∀ p : PathIn tab, p ⋖_ s → (nodeAt p).isFree) : s.isClusterRoot := by
  intro p p_s
  exact PathIn.isClusterRoot_of_edge_from_free (h p p_s) p_s p p_s

/-- Def 8.14: `e` is an *exit* of the cluster of `s`, i.e. `e ∈ C⁺ \ C` where `C` is the
cluster of `s`: it is not in the cluster of `s`, but it is a child of a node in it. -/
def isExitOf (s e : PathIn tab) : Prop :=
  ¬ (e ≡ᶜ s)  ∧  ∃ t : PathIn tab, (t ≡ᶜ s) ∧ t ⋖_ e

lemma isExitOf_flip {s e : PathIn tab} :
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

/-- Exits of a cluster are cluster roots.
This is one of the two things needed to keep the `tabToIntAt` recursion going. -/
lemma isClusterRoot_of_isExitOf {s e : PathIn tab}
    (h : isExitOf s e) : e.isClusterRoot := by
  rcases h with ⟨e_not_s, t, t_s, t_e⟩
  rw [PathIn.isClusterRoot_iff]
  intro p p_e p_e_equiv
  absurd e_not_s
  have p_eq_t : p = t := edge_leftInjective _ _ _ p_e t_e
  subst p_eq_t
  exact ⟨p_e_equiv.2.trans t_s.1, t_s.2.trans p_e_equiv.1⟩

-- FIXME move / already exists with other name?
/-- Any `⋖_` path is also a `◃` path. -/
lemma cReach_of_le {s t : PathIn tab} (h : s ≤ t) : s ◃* t :=
  h.mono (fun _ _ h => Or.inl h)

/-- If `u < s` then some parent of `s` is reachable from `u` (possibly `u` itself). -/
lemma exists_parent_of_lt {u s : PathIn tab} (h : u < s) :
    ∃ p : PathIn tab, u ≤ p ∧ p ⋖_ s := by
  cases h with
  | single u_s => exact ⟨u, Relation.ReflTransGen.refl, u_s⟩
  | tail u_d d_s => exact ⟨_, u_d.to_reflTransGen, d_s⟩

/-- Lemma 8.15 (a): clusters are subtrees. Here in the form we need it: the root of a
cluster is `≤` all nodes of its cluster. -/
lemma PathIn.le_of_cEquiv_of_isClusterRoot {s t : PathIn tab}
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
lemma lt_of_isExitOf {s e : PathIn tab}
    (s_cr : s.isClusterRoot) (h : isExitOf s e) : s < e := by
  obtain ⟨-, t, t_s, t_e⟩ := h
  have s_le_t : s ≤ t := PathIn.le_of_cEquiv_of_isClusterRoot s_cr ((cEquiv.symm t s).mp t_s)
  exact Relation.TransGen.tail' s_le_t t_e

/-! ## Loaded Clusters -/

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

namespace LoadedCluster

-- The entry point is `clusterInterpolation`, which is given a node together with a proof
-- that it is a cluster root, and uses `LoadedCluster.ofClusterRoot` below.

/-- Make the `LoadedCluster` of a right-loaded node that is the first node of its cluster.
This is the way `tabToIntAt` now gets hold of a `LoadedCluster`. -/
def ofClusterRoot (s : PathIn tab)
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

/-- The exits of the cluster, i.e. `C⁺ \ C` from Def 8.14. -/
def exits (C : LoadedCluster tab) : List (PathIn tab) :=
  (C.CL.flatMap (fun t => t.children.map Subtype.val)).filter (fun e => e ∉ C.CL)

/-- C⁺, the cluster plus its exits. -/
def CL_plus (C : LoadedCluster tab) : List (PathIn tab) :=
  C.CL ++ C.exits

/-- The list `C.CL` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_CL_iff (C : LoadedCluster tab) (p : PathIn tab) :
    p ∈ C.CL ↔ p ≡ᶜ C.root :=
  ⟨ fun p_in => C.CL_equiv p p_in C.root C.root_mem_CL
  , fun p_c_root => C.CL_complete C.root C.root_mem_CL p ((cEquiv.symm p C.root).mp p_c_root) ⟩

/-- The list `C.exits` contains exactly the exits in the sense of `isExitOf`. -/
lemma mem_exits_iff (C : LoadedCluster tab) (e : PathIn tab) :
    e ∈ C.exits ↔ isExitOf C.root e := by
  rw [LoadedCluster.exits, List.mem_filter, List.mem_flatMap]
  simp only [decide_eq_true_eq, isExitOf, ← PathIn.children_spec]
  constructor
  · rintro ⟨⟨t, t_in, t_e⟩, e_not_in⟩
    exact ⟨ fun e_c_root => e_not_in ((C.mem_CL_iff e).mpr e_c_root)
          , t, (C.mem_CL_iff t).mp t_in, t_e ⟩
  · rintro ⟨e_not_root, t, t_root, t_e⟩
    exact ⟨ ⟨t, (C.mem_CL_iff t).mpr t_root, t_e⟩
          , fun e_in => e_not_root ((C.mem_CL_iff e).mp e_in) ⟩

/-- All nodes that are `◃`-between the root of a cluster and itself are loaded. -/
lemma isLoaded_of_between (C : LoadedCluster tab) {v : PathIn tab}
    (h1 : C.root ◃* v) (h2 : v ◃* C.root) : (nodeAt v).isLoaded := by
  by_contra v_free
  have root_eq_v : C.root = v := eq_of_cEquiv_of_isFree v_free ⟨h2, h1⟩
  have v_right := C.root_loaded_right
  rw [root_eq_v] at v_right
  apply v_free
  rcases hh : nodeAt v with ⟨L, R, _|(o|o)⟩ <;> rw [hh] at v_right <;>
    simp_all [Sequent.isLoaded]

/-- Lemma 9.4 (a) -/
lemma all_right_loaded (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).2.2.isRight := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  exact (cReach_inv t_root.2
    (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).1

/-- Lemma 9.4 (b): the left component of a node in the cluster is empty iff the left
component of the root of the cluster is empty. Note that here the left component is the
free side, because a `LoadedCluster` is loaded on the right.
As `Sequent.left ⟨L,R,O⟩ = L ++ O.L` and `O.L = []` for the nodes in the cluster by
`LoadedCluster.all_right_loaded`, this is the same as `Λ₁(t) = ∅ ↔ Λ₁(r) = ∅`. -/
lemma left_empty_iff_root_left_empty (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, (nodeAt t).1 = [] ↔ (nodeAt C.root).1 = [] := by
  intro t t_in
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  constructor
  · exact (cReach_inv t_root.1
      (fun v h1 h2 => C.isLoaded_of_between (t_root.2.trans h1) h2)
      (C.all_right_loaded t t_in)).2
  · exact (cReach_inv t_root.2
      (fun v h1 h2 => C.isLoaded_of_between h1 (h2.trans t_root.1)) C.root_loaded_right).2

/-- Part of Lemma 9.4 (c): All children of t belong to C⁺. -/
lemma children_in_plus (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, ∀ c ∈ t.children, c.val ∈ C.CL_plus := by
  intro t t_in c _
  rw [LoadedCluster.CL_plus, List.mem_append]
  by_cases c_in : c.val ∈ C.CL
  · exact Or.inl c_in
  · refine Or.inr ((C.mem_exits_iff c.val).mpr ⟨fun c_root => c_in ?_, t, ?_, c.2⟩)
    · exact (C.mem_CL_iff c.val).mpr c_root
    · exact (C.mem_CL_iff t).mp t_in

/-- Part of Lemma 9.4 (c): If `t` is not an lpr, then at least one child is in C.
This needs that the cluster is proper, i.e. that its root lies on a `◃`-cycle. -/
lemma nonLpr_some_child_in_C (C : LoadedCluster tab)
    (C_proper : C.root ◃⁺ C.root) :
    ∀ t ∈ C.CL, ¬ t.isLrep → ∃ c ∈ t.children, c.val ∈ C.CL := by
  intro t t_in t_not_lrep
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  -- Because the cluster is proper, also `t` lies on a `◃`-cycle:
  have t_cycle : t ◃⁺ t := Relation.TransGen.trans_right t_root.1
    (Relation.TransGen.trans_left C_proper t_root.2)
  obtain ⟨u, t_u, u_t⟩ := Relation.TransGen.head'_iff.mp t_cycle
  -- The first step of that cycle cannot be a ♥ step, because `t` is not an lpr:
  rcases t_u with t_edge_u | ⟨lpr, h_lrep, rfl⟩
  · rw [PathIn.children_spec, List.mem_map] at t_edge_u
    obtain ⟨c, c_in, rfl⟩ := t_edge_u
    exact ⟨c, c_in, (C.mem_CL_iff c.val).mpr ⟨u_t.trans t_root.1,
      t_root.2.trans (Relation.ReflTransGen.single (Or.inl c.2))⟩⟩
  · exact absurd (by unfold PathIn.isLrep; rw [h_lrep]; trivial) t_not_lrep

/-- Part of Lemma 9.4 (c): If t is an lpr, then its companion is in C. -/
lemma lpr_comp_in_C (C : LoadedCluster tab) :
    ∀ t ∈ C.CL, t ♥ comp → comp ∈ C.CL := by
  intro t t_in t_comp
  have t_root : t ≡ᶜ C.root := (C.mem_CL_iff t).mp t_in
  refine (C.mem_CL_iff comp).mpr ⟨?_, ?_⟩
  · -- comp ◃* root, because comp is above t.
    exact (cReach_of_le (companion_lt t_comp).to_reflTransGen).trans t_root.1
  · -- root ◃* comp, going via t.
    exact t_root.2.tail (Or.inr t_comp)

/-- Def 9.6: All nodes in cluster with a certain list (WORRY should it be set??) on the right.
TODO: `.right` might not get or not keep track of the loaded formula!
Better use `List WhateverFormula` and `Sequent.wForms` here maybe?
-/
def nodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
  C.CL.filter (fun p => decide ((nodeAt p).right = Δ))

def plusNodesWith (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
  C.CL_plus.filter (fun p => decide ((nodeAt p).right = Δ))

/- PROBLEM -- On the `Tableau` level a `loc` is not either left or right rule, but can be a mix!
def Tableau.usesLeftRule (tab : Tableau H X) : Prop := sorry
-/

-- WORRY: do we need `loc`-intermediate notes for the construction of the pseudo tableau?
-- Then the nodes in `LoadedCluster` might not be enough.

-- TODO defs "where a left/right rule is applied"
/-- Nodes that have Δ as the right and a left rule applied to them. -/
def nodesWithLeft (C : LoadedCluster tab) (Δ : List Formula) : List (PathIn tab) :=
  C.CL.filter (fun p => @decide
    ((nodeAt p).right = Δ ∧ sorry /- (tabAt p).2.2.usesLeftRule -/) sorry)

-- TODO Lemma 9.7 (a) first part
lemma nodesWith_union (C : LoadedCluster tab) (Δ : List Formula) :
    C.nodesWith Δ = C.nodesWithLeft Δ /- ++ C.nodesWithRight Δ -/ := by
  sorry

-- TODO Lemma 9.7 (b)

-- TODO Lemma 9.7 (c)

-- TODO Lemma 9.7 (d)

-- TODO Lemma 9.7 (e)

-- TODO Lemma 9.7 (f)

end LoadedCluster

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

/-! ### Flipping Interpolants -/

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
