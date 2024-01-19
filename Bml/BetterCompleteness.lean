import Mathlib.Data.Finset.Basic

import Bml.Syntax
import Bml.Semantics
import Bml.Modelgraphs
import Bml.Tableau
import Bml.Soundness

open LocalTableau
open HasLength
open HasSat
open LocalRule

def formulasInNegBox (X: Finset Formula): Finset Formula :=
  X.biUnion λ α => (match α with | ~(□f) => {f} | _ => {})

theorem formulasInNegBoxIff {X}: α ∈ formulasInNegBox X ↔  ~(□α) ∈ X := by
  rw[formulasInNegBox]
  aesop

noncomputable def M₀ (LR : TNode): List (Σ Z, LocalTableau Z) := by
  let tX := aLocalTableauFor LR
  cases tX
  -- If X is not simple, add a tableau for X and process endnodes of that tableau
  · case fromRule C appTab =>
    let nextNodes := endNodesOf ⟨LR, fromRule appTab⟩
    let worlds': {x // x ∈ nextNodes} → List (Σ Z, LocalTableau Z) := by
      intro ⟨Y, Y_in⟩
      have _ : lengthOf Y < lengthOf LR := by
        exact endNodesOfLocalRuleLT Y_in
      exact M₀ Y
    exact ⟨LR, tX⟩ :: (nextNodes.attach.map worlds').join
  -- If X is simple, add a tableau for X and process (projection X) ∪ {~α} for each formula ~□α ∈ X
  · case fromSimple isSimple => sorry
    /-let next: { x // x ∈ formulasInNegBox LR} → List (Σ Z, LocalTableau Z) := by
      intro ⟨α, α_in⟩
      have _ : lengthOf (projection LR ∪ {~α}) < lengthOf LR := by
        rw [formulasInNegBoxIff] at α_in
        sorry --exact atmRuleDecreasesLength α_in
      exact ⟨LR, tX⟩ :: M₀ (projection X ∪ {~α})
    exact ((formulasInNegBox LR).attach.toList.map next).join-/
termination_by M₀ X => lengthOf X
decreasing_by aesop

inductive Path: TNode →  Type
  | endNode {LR} (isConsistent : Consistent LR) (isSimple : Simple LR): Path LR
  | interNode {LR Y} (_ : AppLocalTableau LR C) (Y_in : Y ∈ C) (tail : Path Y): Path LR
open Path

@[simp]
def toTNode: Path (L, R) → TNode
  | endNode _ _ => (L, R)
  | (interNode _ _ tail) =>
    let (Ltail, Rtail) := toTNode tail
    (L ∪ Ltail, R ∪ Rtail)

@[simp]
theorem X_in_PathX {X : Finset Formula} (path : Path X) : X ⊆ (toFinset path) := by
  intro f
  cases path
  case endNode => aesop
  case interNode => aesop

def endNodeOf: Path X → Finset Formula
  | endNode _ _ => X
  | interNode _ _ tail => endNodeOf tail

theorem endNodeIsSimple (path : Path X): Simple (endNodeOf path) := by
  induction path
  all_goals aesop

theorem endNodeProjection (path : Path X): projection (toFinset path) = projection (endNodeOf path) := by
  induction path
  case endNode cosX simX => aesop
  case interNode lr Y_in tail IH =>
    rename_i B X Y
    unfold projection
    simp only [toFinset]
    sorry

theorem endNodeSubsetEndNodes (path: Path X) (tX: LocalTableau X): endNodeOf path ∈ endNodesOf ⟨X, tX⟩ := by
  sorry

def pathsOf (tX : LocalTableau X) :  List (Path X) := by
  cases tX
  case sim simpleX  => sorry

  case byLocalRule B next lr =>
    let mylr := lr
    cases lr
    case bot h₀ =>
      exact []

    case Not φ h₀ =>
      exact []

    case neg φ h₀ =>
      specialize next (X \ {~~φ} ∪ {φ})
      simp only [Finset.mem_singleton] at next
      specialize next True.intro
      have : Finset.sum (insert φ (Finset.erase X (~~φ))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.neg h₀)
        simp
      exact List.map (λ l => interNode (neg h₀) (by simp) l) (pathsOf next)


    case Con α β h₀ =>
      specialize next (X \ {α⋀β} ∪ {α,β})
      simp at next
      specialize next True.intro
      have : Finset.sum (insert α (insert β (Finset.erase X (α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula  := by
        apply localRulesDecreaseLength (LocalRule.Con h₀)
        simp
      let IH := pathsOf next
      exact List.map (interNode (Con h₀) (by simp)) IH

    case nCo α β h₀ =>
      have next1 := next (X \ {~(α⋀β)} ∪ {~α})
      have next2 := next (X \ {~(α⋀β)} ∪ {~β})
      simp at next1 next2
      specialize next1 True.intro
      specialize next2 True.intro
      have : Finset.sum (insert (~α) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.nCo h₀)
        simp
      have : Finset.sum (insert (~β) (Finset.erase X (~(α⋀β)))) lengthOfFormula < Finset.sum X lengthOfFormula := by
        apply localRulesDecreaseLength (LocalRule.nCo h₀)
        simp
      let IH1 := List.map (interNode (nCo h₀) (by simp)) (pathsOf next1)
      let IH2 := List.map (interNode (nCo h₀) (by simp)) (pathsOf next2)
      exact IH1 ++ IH2
termination_by pathsOf X tX => lengthOf X

def aPathOf (tX : LocalTableau X) (conX : Consistent X) : Path X := by
  sorry -- using pathsOf or replace pathsOf with this

theorem M₀closure1: tabY ∈ M₀ X → Z ∈ endNodesOf tabY → ⟨Z, aLocalTableauFor Z⟩ ∈ M₀ X := by sorry

theorem M₀closure2: ⟨Y, sim simpleX⟩ ∈ M₀ X → ~(□α) ∈ X →
        ⟨(projection Y ∪ {α}), aLocalTableauFor (projection Y ∪ {α})⟩ ∈ M₀ X := by sorry

theorem pathSaturated (path : Path X): Saturated (toFinset path) := by
  intro P Q
  induction path
  case endNode X _ simpleX =>
    simp
    unfold Simple at simpleX
    simp at simpleX
    constructor
    · specialize simpleX (~~P)
      aesop
    · constructor
      · specialize simpleX (P ⋀ Q)
        aesop
      · specialize simpleX (~(P ⋀ Q))
        aesop
  case interNode B X Y locRule Y_in tail IH =>
    simp
    rcases IH with ⟨IH1, ⟨IH2, IH3⟩⟩
    constructor
    -- ~~P ∈ U → P ∈ U
    · intro nnP_in
      apply Or.inr
      cases nnP_in
      · case inl nnP_in_X =>
        rename_i Z; clear Z
        cases locRule
        · case bot bot_in_X =>
          refine False.elim ?_
          exact (List.mem_nil_iff Y).mp Y_in
        · case Not α α_nα_in_X =>
          refine False.elim ?_
          exact (List.mem_nil_iff Y).mp Y_in
        · case neg α nnα_in_X =>
          have : Y = (X \ {~~α} ∪ {α}) := by
            simp at *; exact Y_in
          clear Y_in; subst Y
          by_cases P = α
          · case pos P_eq_α =>
            subst P
            apply X_in_PathX; refine Finset.mem_union_right (X \ {~~α}) ?_; exact Finset.mem_singleton.mpr rfl
          · case neg P_neq_α =>
            apply IH1;
            apply X_in_PathX; refine Finset.mem_union_left {α} ?_; refine Finset.mem_sdiff.mpr ?_
            refine (and_iff_right nnP_in_X).mpr ?_; aesop
        · case Con α β α_β_in_X =>
          have : Y = (X \ {α⋀β} ∪ {α,β}) := by
            simp_all only [not_true_eq_false, sdiff_singleton_is_erase, Finset.mem_singleton, Finset.union_insert]
          clear Y_in; subst Y
          apply IH1
          apply X_in_PathX
          refine Finset.mem_union_left {α, β} ?_
          refine Finset.mem_sdiff.mpr ?_
          aesop
        · case nCo α β nα_β_in_X =>
          have : Y = (X \ {~(α⋀β)} ∪ {~α}) ∨ Y = (X \ {~(α⋀β)} ∪ {~β}) := by
            simp at *; exact Y_in
          clear Y_in; rename Y = X \ {~(α⋀β)} ∪ {~α} ∨ Y = X \ {~(α⋀β)} ∪ {~β} => Y_in
          cases Y_in; all_goals subst Y
          apply IH1
          apply X_in_PathX
          refine Finset.mem_union_left {~α} ?inl.a.h
          refine Finset.mem_sdiff.mpr ?inl.a.h.a
          aesop
          apply IH1
          apply X_in_PathX
          refine Finset.mem_union_left {~β} ?inr.a.h
          refine Finset.mem_sdiff.mpr ?inr.a.h.a
          aesop
      · case inr nnP_in_tail => aesop
    · constructor
    -- P⋀Q ∈ U  → P ∈ U  and Q ∈ U
      · case intro.intro.right.left Z =>
        clear Z
        intro P_Q_in_X
        refine { left := ?left, right := ?right }
        · case left =>
          cases locRule
          · case bot bot_in_X =>
            refine False.elim ?_
            exact (List.mem_nil_iff Y).mp Y_in
          · case Not α α_nα_in_X =>
            refine False.elim ?_
            exact (List.mem_nil_iff Y).mp Y_in
          · case neg α nnα_in_X =>
            apply Or.inr; refine (IH2 ?_).left
            have : Y = (X \ {~~α} ∪ {α}) := by
              simp at *; exact Y_in
            clear Y_in; subst Y
            have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
              intro h₀
              have : (P⋀Q ∈ X \ {~~α} ∪ {α}) := by
                refine Finset.mem_union_left {α} ?_
                refine Finset.mem_sdiff.mpr ?_
                aesop
              clear h₀; rename ((P⋀Q ∈ X \ {~~α} ∪ {α})) => h₀
              refine X_in_PathX ?_ ?_
              exact h₀
            aesop
          · case Con β γ β_γ_in_X =>
            by_cases (P⋀Q) = (β⋀γ)
            · case pos eq =>
              simp at eq; cases eq; subst P; subst Q
              apply Or.inr
              have : Y = (X \ {β⋀γ} ∪ {β,γ}) := by
                simp at *; exact Y_in
              clear Y_in; subst Y
              apply X_in_PathX
              refine Finset.mem_union_right (X \ {β⋀γ}) ?intro.h.a.h
              exact Finset.mem_insert_self β {γ}
            · case neg neq =>
              apply Or.inr
              have : Y = (X \ {β⋀γ} ∪ {β,γ}) := by
                simp at *; exact Y_in
              clear Y_in; subst Y
              refine (IH2 ?_).left
              have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
                intro h₀
                apply X_in_PathX
                aesop
              aesop
          · case nCo β γ nβ_γ_in_X =>
            have eq : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
              simp at *; exact Y_in
            cases eq
            all_goals
              clear Y_in; subst Y
              apply Or.inr
              refine (IH2 ?_).left
              have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
                intro h₀
                apply X_in_PathX
                aesop
              aesop
        · case right =>
          cases locRule
          · case bot bot_in_X =>
            refine False.elim ?_
            exact (List.mem_nil_iff Y).mp Y_in
          · case Not α α_nα_in_X =>
            refine False.elim ?_
            exact (List.mem_nil_iff Y).mp Y_in
          · case neg α nnα_in_X =>
            apply Or.inr; refine (IH2 ?_).right
            have : Y = (X \ {~~α} ∪ {α}) := by
              simp at *; exact Y_in
            clear Y_in; subst Y
            have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
              intro h₀
              have : (P⋀Q ∈ X \ {~~α} ∪ {α}) := by
                refine Finset.mem_union_left {α} ?_
                refine Finset.mem_sdiff.mpr ?_
                aesop
              clear h₀; rename ((P⋀Q ∈ X \ {~~α} ∪ {α})) => h₀
              refine X_in_PathX ?_ ?_
              exact h₀
            aesop
          · case Con β γ β_γ_in_X =>
            by_cases (P⋀Q) = (β⋀γ)
            · case pos eq =>
              simp at eq; cases eq; subst P; subst Q
              apply Or.inr
              have : Y = (X \ {β⋀γ} ∪ {β,γ}) := by
                simp at *; exact Y_in
              clear Y_in; subst Y
              apply X_in_PathX
              aesop
            · case neg neq =>
              apply Or.inr
              have : Y = (X \ {β⋀γ} ∪ {β,γ}) := by
                simp at *; exact Y_in
              clear Y_in; subst Y
              refine (IH2 ?_).right
              have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
                intro h₀
                apply X_in_PathX
                aesop
              aesop
          · case nCo β γ nβ_γ_in_X =>
            have eq : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
              simp at *; exact Y_in
            cases eq
            all_goals
              clear Y_in; subst Y
              apply Or.inr
              refine (IH2 ?_).right
              have : (P⋀Q ∈ X) → (P⋀Q ∈ toFinset tail) := by
                intro h₀
                apply X_in_PathX
                aesop
              aesop
      -- ~(P⋀Q) ∈ U   → ~P ∈ U  or  ~Q ∈ U
      · case intro.intro.right.right Z =>
        intro nP_Q_in_path
        cases locRule
        · case bot bot_in_X =>
            refine False.elim ?_
            exact (List.mem_nil_iff Y).mp Y_in
        · case Not α α_nα_in_X =>
          refine False.elim ?_
          exact (List.mem_nil_iff Y).mp Y_in
        · case neg α nnα_in_X =>
          have : Y = (X \ {~~α} ∪ {α}) := by
            simp at *; exact Y_in
          clear Y_in; subst Y
          have nP_Q_in_tail : ~(P⋀Q) ∈ toFinset tail := by
            cases nP_Q_in_path
            apply X_in_PathX; refine Finset.mem_union_left {α} ?_; aesop
            aesop
          clear nP_Q_in_path
          aesop
        · case Con β γ β_γ_in_X =>
          have : Y = X \ {β⋀γ} ∪ {β,γ} := by
            simp at *; exact Y_in
          clear Y_in; subst Y
          have nP_Q_in_tail : ~(P⋀Q) ∈ toFinset tail := by
            cases nP_Q_in_path
            apply X_in_PathX; refine Finset.mem_union_left {β, γ} ?_; aesop
            aesop
          clear nP_Q_in_path
          aesop
        · case nCo β γ nβ_γ_in_X =>
          have eq : Y = X \ {~(β⋀γ)} ∪ {~β} ∨ Y = X \ {~(β⋀γ)} ∪ {~γ} := by
            simp at *; exact Y_in
          cases eq
          · case inl =>
            clear Y_in; subst Y
            by_cases ~(P⋀Q) = ~(β⋀γ)
            · case pos eq =>
                simp at eq; cases eq; subst P; subst Q
                have : ~β ∈ toFinset tail := by
                  apply X_in_PathX
                  aesop
                aesop
            · case neg neq =>
                have : ~(P⋀Q) ∈ toFinset tail := by
                  cases nP_Q_in_path
                  apply X_in_PathX; refine Finset.mem_union_left {~β} ?_; refine Finset.mem_sdiff.mpr ?_; aesop
                  aesop
                aesop
          · case inr =>
            clear Y_in; subst Y
            by_cases ~(P⋀Q) = ~(β⋀γ)
            · case pos eq =>
                simp at eq; cases eq; subst P; subst Q
                have : ~γ ∈ toFinset tail := by
                  apply X_in_PathX
                  aesop
                aesop
            · case neg neq =>
                have : ~(P⋀Q) ∈ toFinset tail := by
                  cases nP_Q_in_path
                  apply X_in_PathX; refine Finset.mem_union_left {~γ} ?_; refine Finset.mem_sdiff.mpr ?_; aesop
                  aesop
                aesop

theorem pathConsistent (path : Path X): ⊥ ∉ (toFinset path) ∧ ∀ P, P ∈ (toFinset path) → ~P ∉ (toFinset path) := by
  induction path
  case endNode X consistentX simpleX =>
      unfold Consistent Inconsistent at consistentX
      simp at consistentX
      constructor
      · by_contra h
        simp at h
        let tab := byLocalRule (bot h) (by aesop)
        have closedTab := ClosedTableau.loc tab (by aesop)
        exact IsEmpty.false closedTab
      · simp
        intro f f_in_X
        by_contra nf_in_X
        let tab := byLocalRule (Not ⟨f_in_X, nf_in_X⟩) (by aesop)
        have closedTab := ClosedTableau.loc tab (by aesop)
        exact IsEmpty.false closedTab
  case interNode B X Y locRule Y_in pathY IH =>
    simp
    constructor
    · by_contra h
      rcases h
      case inl h => sorry
      case inr h => aesop
    · intro f f_in
      by_contra h
      sorry

theorem modelExistence (X: Finset Formula): Consistent X →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (W : WS), X ⊆ W :=
  by
  intro consX
  -- TO DO make this less ugly
  let pathsOf': (Σ Y, LocalTableau Y) → List (Σ Y, Path Y) := by
    exact λ ⟨Y, tabY⟩ => (pathsOf tabY).map (λ x => ⟨Y, x⟩)
  let paths : List (Σ Y, Path Y) := ((M₀ X).map pathsOf').join
  let WSlist : List (Finset Formula) := paths.map (λ ⟨X, path⟩ => toFinset path)
  let WS := WSlist.toFinset
  let M : KripkeModel WS := by
    constructor
    -- define valuation function
    · intro ⟨w, w_in⟩ p
      exact (·p) ∈ w
    -- define relation
    · intro ⟨w, w_in⟩ ⟨v, v_in⟩
      exact projection w ⊆ v
  let pathX : Path X := aPathOf (aLocalTableauFor X) consX
  use WS, ⟨M, ?_⟩, ⟨toFinset pathX, ?_⟩
  · simp
  · constructor
    · intro ⟨W, W_in⟩
      simp only [List.mem_toFinset, List.mem_join, List.mem_map, Function.comp_apply, Sigma.exists] at W_in
      choose W' pathW' h using W_in
      rcases h with ⟨_, W_eq⟩
      subst W_eq
      exact ⟨pathSaturated pathW', pathConsistent pathW'⟩
    · constructor
      · aesop
      · constructor
        · intro ⟨w, w_in⟩ ⟨v, v_in⟩ f wRv h
          rewrite [← proj] at h
          aesop
        · intro ⟨w, w_in⟩ f nboxf_in_w
          simp at nboxf_in_w
          simp at w_in
          choose w' h w_in_w' using w_in
          choose Y tY YtY_in w'_eq using h
          subst w'_eq
          simp at w_in_w'
          choose wPath wPath_in w_eq using w_in_w'
          subst w_eq
          simp
          let Y' := endNodeOf wPath
          sorry
  · sorry

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    have ⟨WS, M, w, h⟩ := modelExistence X X_is_consistent
    use WS, M.val, w
    have := truthLemma M w
    aesop
  -- use Theorem 2:
  · exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent {φ} ↔ Satisfiable φ :=
  by
  intro f
  have := completeness {f}
  simp only [singletonSat_iff_sat] at *
  tauto

theorem consistentImplies : Consistent X → ⊥ ∉ X ∧ ∀ P, P ∈ X → ~P ∉ X := by
  intro consX
  unfold Consistent Inconsistent at consX
  simp at consX
  constructor
  · by_contra bot_in_X
    let tab := byLocalRule (bot bot_in_X) (by aesop)
    have closedTab := ClosedTableau.loc tab (by aesop)
    exact IsEmpty.false closedTab
  · intro P
    by_contra h
    simp at h
    let tab := byLocalRule (Not h) (by aesop)
    have closedTab := ClosedTableau.loc tab (by aesop)
    exact IsEmpty.false closedTab

theorem consistentThenOpenTab : Consistent X → ∃ (t : Tableau X), isOpen t :=
  by
  have ⟨tX⟩ := existsTableauFor X
  contrapose
  simp[not_exists, Consistent, Inconsistent]
  intro h
  specialize h tX
  refine Nonempty.intro ?val
  have : isClosed tX := by
    have h2 : ¬ isOpen tX ↔ ¬ ¬ isClosed tX := Iff.symm (Iff.not (Iff.symm open_iff_notClosed))
    simp_all only [not_not, not_true_eq_false, not_false_eq_true, iff_true]
  exact (isClosed_then_ClosedTab this)
