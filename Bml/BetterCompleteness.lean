
import Bml.Syntax
import Bml.Semantics
import Bml.Modelgraphs
import Bml.Tableau
import Bml.Consistency

open LocalTableau
open HasLength
open HasSat
open LocalRule


-- Maximal paths in a local tableau, from root to end node, as sets of sets.
-- pathsOf (X with children B) := { X ∪ rest | c <- B, rest <- pathsOf c }
def pathsOf {X} : LocalTableau X → Finset (Finset Formula)
  | @byLocalRule _ B lr next => B.attach.biUnion
    (λ ⟨Y,h⟩ => have : lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h
    (pathsOf (next Y h)).image (λ fs => fs ∪ X))
  | sim _ => { X }


lemma X_in_PathX (X path : Finset Formula) {tX : LocalTableau X} (h₀ : path ∈ (pathsOf tX)) : X ⊆ path := by
  cases tX; swap
  all_goals
    unfold pathsOf at h₀
    simp at h₀
  aesop
  rename_i B next lr; rcases h₀ with ⟨Y, YInB, path', _, eq⟩; subst eq; exact Finset.subset_union_right path' X;


lemma boxInPath1 {tR : LocalTableau R} : ∀ E ∈ endNodesOf ⟨R, tR⟩, ∀ α, □ α ∈ R → □ α ∈ E := by
  induction tR; all_goals clear R
  swap
  · case sim R simpleR =>
    simp

  · case byLocalRule X B locRule next IH =>
    intro E EEndnode α Boxα; simp at EEndnode; rcases EEndnode with ⟨Y, YInB, EEndnode⟩; dsimp at EEndnode
    apply IH; exact EEndnode;
    clear EEndnode E IH next
    cases locRule
    · case intro.intro.a.bot bot_in_X =>
      cases YInB
    · case intro.intro.a.Not =>
      cases YInB
    · case intro.intro.a.neg β nnβ =>
      have : Y = X \ {~~β} ∪ {β} := by
        simp at *; aesop
      subst Y
      refine Finset.mem_union_left {β} ?h;
      refine Finset.mem_sdiff.mpr ?h.a; aesop
    · case intro.intro.a.Con β γ γβ =>
      have : Y = X \ {β⋀γ} ∪ {β,γ} := by
        simp at *; aesop
      subst Y
      refine Finset.mem_union_left {β, γ} ?_
      refine Finset.mem_sdiff.mpr ?_; aesop
    · case intro.intro.a.nCo β γ nγβ =>
      have : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
        simp at *; aesop
      cases this
      · case inl =>
        subst Y
        refine Finset.mem_union_left {~β} ?_;
        refine Finset.mem_sdiff.mpr ?_; aesop
      · case inr =>
        subst Y
        refine Finset.mem_union_left {~γ} ?_;
        refine Finset.mem_sdiff.mpr ?_; aesop


lemma boxInPath2 {tR : LocalTableau R} : ∀ E ∈ endNodesOf ⟨R, tR⟩, ∀ α, ~(□ α) ∈ R → ~(□ α) ∈ E := by
  induction tR; all_goals clear R
  swap
  · case sim R simpleR =>
    simp

  · case byLocalRule X B locRule next IH =>
    intro E EEndnode α Boxα; simp at EEndnode; rcases EEndnode with ⟨Y, YInB, EEndnode⟩; dsimp at EEndnode
    apply IH; exact EEndnode;
    clear EEndnode E IH next
    cases locRule
    · case intro.intro.a.bot bot_in_X =>
      cases YInB
    · case intro.intro.a.Not =>
      cases YInB
    · case intro.intro.a.neg β nnβ =>
      have : Y = X \ {~~β} ∪ {β} := by
        simp at *; aesop
      subst Y
      refine Finset.mem_union_left {β} ?h;
      refine Finset.mem_sdiff.mpr ?h.a; aesop
    · case intro.intro.a.Con β γ γβ =>
      have : Y = X \ {β⋀γ} ∪ {β,γ} := by
        simp at *; aesop
      subst Y
      refine Finset.mem_union_left {β, γ} ?_
      refine Finset.mem_sdiff.mpr ?_; aesop
    · case intro.intro.a.nCo β γ nγβ =>
      have : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
        simp at *; aesop
      cases this
      · case inl =>
        subst Y
        refine Finset.mem_union_left {~β} ?_;
        refine Finset.mem_sdiff.mpr ?_; aesop
      · case inr =>
        subst Y
        refine Finset.mem_union_left {~γ} ?_;
        refine Finset.mem_sdiff.mpr ?_; aesop


-- Need Lemma here: X ⊆ Y and Consistent Y  ⇒ COnsistent X
lemma boxInPath {tR : LocalTableau R} : ∀ path ∈ pathsOf tR, (Consistent path) → ∃ E ∈ endNodesOf ⟨R, tR⟩, Consistent E ∧ (∀ α, □ α ∈ path → □ α ∈ E) ∧ (∀ α, ~(□ α) ∈ path → ~(□ α) ∈ E)  := by
  let tR' := tR
  induction tR; all_goals clear R
  swap
  · case sim  R simpleR =>
    unfold pathsOf; simp

  · case byLocalRule R B locRule next IH =>
    intro path pathPath consispath; unfold pathsOf at pathPath; simp at pathPath; rcases pathPath with ⟨Y, YInB, path', path'Path, eq⟩; subst eq
    -- Need Lemma here: X ⊆ Y and COnsistent Y  ⇒ COnsistent X
    have consispath' : Consistent path' := by sorry
    specialize IH Y YInB path' path'Path consispath'; rcases IH with ⟨E, EEndnode, consisE, Boxpath', nBoxpath'⟩
    simp; use E; refine And.intro ?_ ?_; use Y; use YInB;
    refine And.intro consisE ?_; refine And.intro ?_ ?_
    all_goals
      intro α h₀; cases h₀
    aesop; swap; aesop
    all_goals
      have : E ∈ endNodesOf ⟨R, tR'⟩ := by
        unfold endNodesOf; simp; exact BEx.intro Y YInB EEndnode
      rename_i h₀
    exact boxInPath1 E this α h₀
    exact boxInPath2 E this α h₀





-- Need Lemma here:  Consistext X and LocalRule X B  ⇒ ∃ Y,  Y ∈ B ∧ Consistent Y
-- Need Lemma here:  Consistent (A ∪ (B - ~~α  + α))   ⇒  Consistent (A ∪ B)
-- Need Lemma here:  Consistent (A ∪ (B - α⋀β  + α + β))   ⇒  Consistent (A ∪ B)
-- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~α))   ⇒  Consistent (A ∪ B)
-- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~β))   ⇒  Consistent (A ∪ B)
lemma existsConPath (consisX : Consistent X) (LocTabX : LocalTableau X) : ∃ path ∈ pathsOf LocTabX, Consistent path := by
  let LocTabX' := LocTabX
  induction LocTabX; all_goals clear X
  swap
  exact List.exists_mem_cons_of [] consisX

  rename_i X B locRule next IH; simp at IH
  unfold pathsOf; simp; dsimp
  -- Need Lemma here:  Consistext X and LocalRule X B  ⇒ ∃ Y,  Y ∈ B ∧ Consistent Y
  have BNonempty : ∃ Y,  Y ∈ B ∧ Consistent Y := by sorry
  rcases BNonempty with ⟨Y, YInB, consisY⟩
  specialize IH Y YInB consisY
  rcases IH with ⟨path', path'Path, consispath'⟩
  use (path' ∪ X); refine And.intro ?_ ?_; use Y; use YInB; use path'
  cases locRule
  · case h.refine_2.bot =>
    cases YInB;
  · case h.refine_2.Not =>
    cases YInB;
  · case h.refine_2.neg α nnα =>
    have : Y = X \ {~~α} ∪ {α} := by
      simp at YInB; simp at *; exact YInB
    subst Y
    have consispath'UY : Consistent (path' ∪ (X \ {~~α} ∪ {α})) := by
      have : path' ∪ (X \ {~~α} ∪ {α}) = path' := by
        have : (X \ {~~α} ∪ {α}) ⊆ path' := X_in_PathX (X \ {~~α} ∪ {α}) path' path'Path
        exact Finset.union_eq_left.mpr this
      simp_all only [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
    -- Need Lemma here:  Consistent (A ∪ (B - ~~α  + α))   ⇒  Consistent (A ∪ B)
    sorry
  · case h.refine_2.Con α β αβ =>
    have : Y = X \ {α⋀β} ∪ {α, β} := by
      simp at YInB; simp at *; aesop
    subst Y
    have consispath'UY : Consistent (path' ∪ (X \ {α⋀β} ∪ {α, β})) := by
      have : path' ∪ (X \ {α⋀β} ∪ {α, β} ) = path' := by
        have : (X \ {α⋀β} ∪ {α, β} ) ⊆ path' := X_in_PathX (X \ {α⋀β} ∪ {α, β}) path' path'Path
        exact Finset.union_eq_left.mpr this
      simp_all only [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
    -- Need Lemma here:  Consistent (A ∪ (B - α⋀β  + α + β))   ⇒  Consistent (A ∪ B)
    sorry
  · case h.refine_2.nCo α β nαβ =>
    have : Y = X \ {~(α⋀β)} ∪ {~α} ∨ Y = X \ {~(α⋀β)} ∪ {~β} := by
      simp at YInB; simp at *; aesop
    cases this
    · case inl =>
      subst Y
      have consispath'UY : Consistent (path' ∪ (X \ {~(α⋀β)} ∪ {~α})) := by
        have : path' ∪ (X \ {~(α⋀β)} ∪ {~α} ) = path' := by
          have : (X \ {~(α⋀β)} ∪ {~α} ) ⊆ path' := X_in_PathX (X \ {~(α⋀β)} ∪ {~α}) path' path'Path
          exact Finset.union_eq_left.mpr this
        simp_all only [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
      -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~α))   ⇒  Consistent (A ∪ B)
      sorry
    · case inr =>
      subst Y
      have consispath'UY : Consistent (path' ∪ (X \ {~(α⋀β)} ∪ {~β})) := by
        have : path' ∪ (X \ {~(α⋀β)} ∪ {~β} ) = path' := by
          have : (X \ {~(α⋀β)} ∪ {~β} ) ⊆ path' := X_in_PathX (X \ {~(α⋀β)} ∪ {~β}) path' path'Path
          exact Finset.union_eq_left.mpr this
        simp_all only [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
      -- Need Lemma here:  Consistent (A ∪ (B - ~(α⋀β) + ~β))   ⇒  Consistent (A ∪ B)
      sorry


lemma pathSat1 {α} {X} {tX : LocalTableau X} : ∀ path ∈ (pathsOf tX), ~~α ∈ path → α ∈ path := by
  induction tX
  swap
  clear X; rename_i X simpleX; intro path pathInPaths nnαInPath;
  unfold pathsOf at pathInPaths; simp at pathInPaths
  subst path; by_contra h₀ ; clear h₀
  unfold Simple at *; simp at *; specialize simpleX (~~α) nnαInPath; simp at *

  clear X; rename_i X B lr next IH; intro path pathInPaths nnαInPath;
  unfold pathsOf at pathInPaths ; simp at pathInPaths ; rcases pathInPaths with ⟨Y, YInB, path', path'InPaths, path'UX⟩ ; dsimp at path'InPaths; subst path
  by_cases nnαInX : ~~α ∈ X; swap
  refine Finset.mem_union_left X ((IH Y YInB path' path'InPaths) ?_); simp_all only [Finset.mem_union, or_false, forall_true_left];
  cases lr
-- bot rule
  by_contra h₀; clear h₀; exact (List.mem_nil_iff Y).mp YInB

-- Not rule
  by_contra h₀; clear h₀; exact (List.mem_nil_iff Y).mp YInB

-- neg rule
  rename_i β nnβInX;
  have : Y = X \ {~~β} ∪ {β} := by
    simp at YInB; simp; exact YInB
  subst Y; by_cases αEqβ : α = β
  -- α = β
  case pos =>
    subst α ; clear IH nnαInX nnαInPath
    have : β ∈ path' := by
      have : β ∈ (X \ {~~β} ∪ {β}) := by
        simp_all only [not_true_eq_false, sdiff_singleton_is_erase, union_singleton_is_insert, Finset.mem_erase]
        exact Finset.mem_insert_self β (Finset.erase X (~~β))
      have : (X \ {~~β} ∪ {β}) ⊆ path' := by
        apply (X_in_PathX (X \ {~~β} ∪ {β}) (path') ?_)
        apply (next (X \ {~~β} ∪ {β}) ?_)
        exact Finset.mem_singleton.mpr rfl
        exact path'InPaths
      tauto
    exact Finset.mem_union_left X this

  -- α ≠ β
  case neg =>
    have : ~~α ≠ ~~β := by
      aesop
    have : ~~α ∈ path' := by
      have : ~~α ∈ (X \ {~~β} ∪ {β}) := by
        simp_all only [Finset.mem_union, or_true, not_true_eq_false, sdiff_singleton_is_erase]
        apply Or.inl
        exact Finset.mem_erase_of_ne_of_mem this nnαInX
      apply (X_in_PathX (X \ {~~β} ∪ {β}) (path') ?_)
      exact this
      refine next (X \ {~~β} ∪ {β}) ?_
      exact Finset.mem_singleton.mpr rfl
      exact path'InPaths
    aesop

-- Con rule
  rename_i β γ βγInX;
  have : Y = X \ {β⋀γ} ∪ {β,γ} := by
    simp at YInB; simp; exact YInB
  subst Y;
  have : ~~α ∈ path' := by
    have : ~~α ∈ X \ {β⋀γ} ∪ {β, γ} := by
      simp_all only [Finset.mem_union, or_true, not_true_eq_false, sdiff_singleton_is_erase, Finset.mem_singleton]
      apply Or.inl
      refine Finset.mem_erase_of_ne_of_mem ?h.a nnαInX
      exact (bne_iff_ne (~~α) (β⋀γ)).mp rfl
    apply (X_in_PathX (X \ {β⋀γ} ∪ {β, γ} ) (path') ?_)
    exact this
    refine next (X \ {β⋀γ} ∪ {β, γ} ) ?_
    exact Finset.mem_singleton.mpr rfl
    exact path'InPaths
  aesop

--nCo rule
  rename_i β γ nβγInX;
  have : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
    simp at YInB; simp; exact YInB
  cases this

  -- Y = X - {~(β⋀γ)} + {~β}
  subst Y
  have : ~~α ∈ path' := by
    have : ~~α ∈ X \ {~(β⋀γ)} ∪ {~β} := by
      simp_all only [Finset.mem_union, or_true, not_true_eq_false, sdiff_singleton_is_erase, Finset.mem_singleton]
      apply Or.inl
      refine Finset.mem_erase_of_ne_of_mem ?_ nnαInX
      exact (bne_iff_ne (~~α) (~(β⋀γ))).mp rfl
    apply (X_in_PathX (X \ {~(β⋀γ)} ∪ {~β} ) (path') ?_)
    exact this
    refine next (X \ {~(β⋀γ)} ∪ {~β} ) ?_
    exact Finset.mem_insert_self (X \ {~(β⋀γ)} ∪ {~β}) {X \ {~(β⋀γ)} ∪ {~γ}}
    exact path'InPaths
  aesop


  -- Y = X - {~(β⋀γ)} + {~γ}
  subst Y
  have : ~~α ∈ path' := by
    have : ~~α ∈ X \ {~(β⋀γ)} ∪ {~γ} := by
      simp_all only [Finset.mem_union, or_true, not_true_eq_false, sdiff_singleton_is_erase, Finset.mem_singleton]
      apply Or.inl
      refine Finset.mem_erase_of_ne_of_mem ?_ nnαInX
      exact (bne_iff_ne (~~α) (~(β⋀γ))).mp rfl
    apply (X_in_PathX (X \ {~(β⋀γ)} ∪ {~γ} ) (path') ?_)
    exact this
    refine next (X \ {~(β⋀γ)} ∪ {~γ} ) ?_
    refine Finset.mem_insert_of_mem ?_ ; exact Finset.mem_singleton.mpr rfl
    exact path'InPaths
  aesop



inductive M0 (T0 : Σ Z0, LocalTableau Z0) : (Σ root, LocalTableau root) → Prop
| a : M0 T0 T0

| b (T : Σ root, LocalTableau root) : (M0 T0 T) → ∀ Y ∈ endNodesOf (T), ∀ local_tab_Y, M0 T0 ⟨Y, local_tab_Y⟩

| c (T : Σ root, LocalTableau root) : (M0 T0 T) → ∀ Y ∈ endNodesOf (T), ∀ α, ~ (□ α) ∈ Y → ∀ local_tab_proj,  M0 T0 ⟨projection Y ∪ {~α}, local_tab_proj⟩






-- Need to Finish Saturated lemma here:
theorem modelExistence {X} : Consistent X →
    ∃ (WS : Set (Finset Formula)) (M : ModelGraph WS) (w : WS), (M.val, w) ⊨ X :=
  by
  intro consX
  have LocTabX := existsLocalTableauFor X; cases LocTabX; rename_i LocTabX
  use { Z | ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ Z ∈ pathsOf (RTab.snd) ∧ Consistent Z}

  -- By truthLemma, suffices to build ModelGraph for
  --  { Z | ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ Z ∈ pathsOf (RTab.snd) ∧ Consistent Z}
  suffices M : ModelGraph { Z | ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ Z ∈ pathsOf (RTab.snd) ∧ Consistent Z}
  use M;
  have existsConPath: ∃ path ∈ pathsOf LocTabX, Consistent path := existsConPath consX LocTabX
  rcases existsConPath with ⟨path, pathInPathsOf, consisPath⟩
  have h₀ : ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ path ∈ pathsOf (RTab.snd) ∧ Consistent path := by
    use ⟨X, LocTabX⟩; refine And.intro M0.a ?_; exact And.intro (pathInPathsOf) consisPath;
  use ⟨path, h₀⟩
  simp;
  intro f fINX
  refine truthLemma ?_ ?_ ?_ ?_; simp
  have : X ⊆ path := X_in_PathX X path pathInPathsOf
  exact this fINX

  -- Building ModelGraph for
  --  { Z | ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ Z ∈ pathsOf (RTab.snd) ∧ Consistent Z}
  unfold ModelGraph; dsimp
  refine { val := ?M.val, property := ?M.property }
  --Build the Kripke Model
  refine KripkeModel.mk ?_ ?_
  --Build the valuation
  intro ⟨path, _⟩ p
  exact (·p) ∈ path
  -- Build the relation
  intro ⟨path1, _⟩ ⟨path2, _⟩
  exact (∀ P, (□ P) ∈ path1 → P ∈ path2)


  dsimp; refine And.intro ?_ ?_
  --Proving property i of ModelGraphs:
  intro path; rcases path with ⟨path, RTab, RTab_reachable, pathPath, consispath⟩
  dsimp
  -- Need to Finish Saturated lemma here:
  have : Saturated path := by sorry
  have : Formula.bottom ∉ path ∧ ∀ P ∈ path, ~P ∉ path := consistentImplies consispath
  aesop

  refine And.intro ?_ ?_
  -- Proving property ii of ModelGraphs
  tauto

  refine And.intro ?_ ?_
  --Proving property iii of ModelGraphs
  tauto

  --Proving property iv of ModelGraphs
  intro path1 α nBoxα; rcases path1 with ⟨path1, RTab, RTab_reachable, path1Path, consispath1⟩; dsimp at nBoxα


  -- Have magical consistent endnode that gives us all key properties:
  let E := boxInPath path1 path1Path consispath1; rcases E with ⟨E, EEndnode, consisE, boxpath1, nboxpath1⟩

  have consisprojE : Consistent (projection E ∪ {~α}) := by
    have simpleE : Simple E := by exact endNodeSimple EEndnode
    have  h₀ : ~(□ α) ∈ E := by exact nboxpath1 α nBoxα
    exact consisImpliesProj consisE simpleE α (nboxpath1 α nBoxα)

  -- Have LocalTableau for proj E + ~ α:
  have LocTabprojE := existsLocalTableauFor (projection E ∪ {~ α}); rcases LocTabprojE with ⟨LocTabprojE⟩

  -- Have consistent path that extends proj E + ~ α:
  have path2 := existsConPath consisprojE LocTabprojE; rcases path2 with ⟨path2, path2Path, consispath2⟩

  have h_path2 : ∃ RTab,  M0 ⟨X, LocTabX⟩ RTab ∧ path2 ∈ pathsOf (RTab.snd) ∧ Consistent path2 := by
    use ⟨projection E ∪ {~α}, LocTabprojE⟩;
    have : M0 ⟨X, LocTabX⟩ ⟨projection E ∪ {~α}, LocTabprojE⟩ := by
      exact M0.c RTab RTab_reachable E EEndnode α (nboxpath1 α nBoxα) LocTabprojE
    simp_all only [Sigma.eta, union_singleton_is_insert, and_self, path2Path, consispath2]

  use ⟨path2, h_path2⟩
  refine And.intro ?_ ?_; swap;
  all_goals
    have : (projection E ∪ {~α}) ⊆ path2 := by exact X_in_PathX (projection E ∪ {~α}) path2 path2Path
  aesop
  intro β Boxβ;
  have boxInE : □ β ∈ E := by exact boxpath1 β Boxβ
  apply this
  refine Finset.mem_union_left {~α} ?h.refine_1.a.h
  unfold projection; aesop
