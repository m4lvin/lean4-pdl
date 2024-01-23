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

@[simp]
theorem formulasInNegBoxIff: α ∈ formulasInNegBox X ↔  ~(□α) ∈ X := by
  rw[formulasInNegBox]
  aesop

def isConsLocTab : (Σ Y, LocalTableau Y) → Prop := λ ⟨Y,_⟩ => Consistent Y

def ConsLocalTab := Subtype isConsLocTab

noncomputable def M₀ (LR : TNode) (consistentLR: Consistent LR): List ConsLocalTab := by
  let tLR := aLocalTableauFor LR
  cases tLR
  -- If LR is not simple, add a tableau for LR and process endnodes of that tableau
  · case fromRule C appTab =>
    let nextNodes := endNodesOf ⟨LR, fromRule appTab⟩
    let worlds': {x // x ∈ nextNodes} → List ConsLocalTab := by
      intro ⟨Y, Y_in⟩
      have _ : lengthOf Y < lengthOf LR := by
        exact endNodesOfLocalRuleLT Y_in
      exact M₀ Y sorry -- filter Y to be consistent
    exact ⟨⟨LR, tLR⟩, consistentLR⟩  :: (nextNodes.attach.map worlds').join
  -- If LR is simple, add a tableau for LR and process diamondProjectTNode for each diamond in LR
  · case fromSimple isSimple =>
    rcases eq : LR with ⟨L,R⟩
    subst eq
    let nextL: { x // x ∈ formulasInNegBox L} → List ConsLocalTab := by
      intro ⟨α, α_in⟩
      have : lengthOfTNode (diamondProjectTNode (Sum.inl (~α)) (L, R)) < lengthOfTNode (L,R) := by
        rw [formulasInNegBoxIff] at α_in
        apply atmRuleLDecreasesLength α_in
      exact ⟨⟨(L, R), tLR⟩, consistentLR⟩  :: M₀ (diamondProjectTNode (Sum.inl (~α)) (L, R)) sorry
    let nextR: { x // x ∈ formulasInNegBox R} → List ConsLocalTab := by
      intro ⟨α, α_in⟩
      have : lengthOfTNode (diamondProjectTNode (Sum.inr (~α)) (L, R)) < lengthOfTNode (L,R) := by
        rw [formulasInNegBoxIff] at α_in
        apply atmRuleRDecreasesLength α_in
      exact ⟨⟨(L, R), tLR⟩, consistentLR⟩ :: M₀ (diamondProjectTNode (Sum.inr (~α)) (L, R)) sorry
    let resL := ((formulasInNegBox L).attach.toList.map nextL).join
    let resR := ((formulasInNegBox R).attach.toList.map nextR).join
    exact resL ++ resR
termination_by M₀ LR _ => lengthOf LR
decreasing_by aesop

--theorem consThenProjectionCons (conLT: ConsLocalTab LR):
theorem M₀closure1: ⟨tabY, consY⟩ ∈ M₀ X consX → Z ∈ endNodesOf tabY → (consZ: Consistent Z)
    → ⟨⟨Z, aLocalTableauFor Z⟩, conZ⟩  ∈ M₀ X conX := by sorry
/-
-- do we need two versions?
theorem M₀closure2: ⟨tabY, consY⟩ ∈ M₀ (L, R) consLR → ~(□α) ∈ L →
        ⟨diamondProjectTNode (Sum.inl φ) (L, R), aLocalTableauFor (diamondProjectTNode (Sum.inl φ) (L, R))⟩ ∈ M₀ X consX := by sorry

theorem M₀closure3: ⟨Y, fromSimple isSimple⟩ ∈ M₀ (L, R) → ~(□α) ∈ R →
        ⟨diamondProjectTNode (Sum.inr φ) (L, R), aLocalTableauFor (diamondProjectTNode (Sum.inr φ) (L, R))⟩ ∈ M₀ X := by sorry
-/
inductive M0 (T0 : ConsLocalTab) : ConsLocalTab → Prop
| a : M0 T0 T0
| b (T : ConsLocalTab) : (M0 T0 T) → ∀ Y ∈ endNodesOf T.1, (consY: Consistent Y) →
  ∀ local_tab_Y, M0 T0 ⟨⟨Y, local_tab_Y⟩, consY⟩
| c (T : ConsLocalTab) : (M0 T0 T) → ∀ Y ∈ endNodesOf T.1, (consY: Consistent Y) →
  ∀ α, ~(□α) ∈ Y.1 → ∀ local_tab_proj,  M0 T0 ⟨⟨diamondProjectTNode (Sum.inl (~α)) Y, local_tab_proj⟩, sorry⟩


inductive Path: TNode →  Type
  | endNode {LR} (isConsistent : Consistent LR) (isSimple : Simple LR): Path LR
  | interNode {LR Y} (_ : AppLocalTableau LR C) (Y_in : Y ∈ C) (tail : Path Y): Path LR
open Path

@[simp]
def toFinset: Path (L,R) → Finset Formula
  | endNode _ _ => L ∪ R
  | (interNode _ _ tail) => L ∪ R ∪ toFinset tail

@[simp]
theorem X_in_PathX (path : Path (L,R)) : L ∪ R ⊆ (toFinset path) := by
  cases path
  case endNode => simp [instTNodeHasSubset]
  case interNode Y C C_in tail appTab =>
    simp_all only [instTNodeHasSubset,instHasSubsetProdFinsetFormula, toFinset, instTNodeUnion,
      instUnionProdFinsetFormula, Finset.subset_union_left, and_self]

def endNodeOf: Path LR → TNode
  | endNode _ _ => LR
  | interNode _ _ tail => endNodeOf tail

theorem endNodeIsSimple (path : Path X): Simple (endNodeOf path) := by
  induction path
  all_goals aesop

theorem endNodeIsConsistent (path : Path X): Consistent (endNodeOf path) := by
  induction path
  all_goals aesop

/-theorem endNodeProjection (path : Path (L,R)): projection (toFinset path) = projectTNode (endNodeOf path) := by
  cases path
  case endNode cosX simX => aesop
  case interNode LR Y_in tail appTab =>
    simp only [endNodeOf]
    rw[← endNodeProjection tail]
    unfold projectTNode
    sorry
termination_by endNodeProjection path => lengthOfTNode (L,R)
decreasing_by sorry-/

theorem endNodeSubsetEndNodes (path: Path X) (tX: LocalTableau X): endNodeOf path ∈ endNodesOf ⟨X, tX⟩ := by
  sorry

theorem consistentThenConsistentChild
    (isConsistent: Consistent LR) (appTab : AppLocalTableau LR C): ∃ c ∈ C, Consistent c := by
  sorry

noncomputable def aPathOf (tab : LocalTableau LR) (isConsistent : Consistent LR) : Path LR := by
  cases tab
  case fromSimple isSimple  => exact endNode isConsistent isSimple
  case fromRule C appTab  =>
    choose c c_in c_consistent using consistentThenConsistentChild isConsistent appTab
    have : lengthOf c < lengthOf LR := by
      apply AppLocalTableau.DecreasesLength appTab c_in
    let pathOf_c := aPathOf (getSubTabs appTab c c_in) c_consistent
    exact interNode appTab c_in pathOf_c
termination_by aPathOf tab isConsistent => lengthOf LR

theorem pathSaturated (path : Path LR): Saturated (toFinset path) := by
  /-intro P Q
  induction path
  case endNode X _ simpleX =>
    simp
    unfold SimpleSetDepr at simpleX
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
                aesop-/
    sorry

theorem pathConsistent (path : Path TN): ⊥ ∉ toFinset path ∧ ∀ P, P ∈ toFinset path → ~P ∉ toFinset path := by
  induction path
  case endNode LR consistentX simpleX =>
      unfold Consistent Inconsistent at consistentX
      simp at consistentX
      constructor
      · by_contra bot_in
        simp at bot_in
        cases bot_in
        · case inl bot_in =>
          have rule := LocalRule.oneSidedL OneSidedLocalRule.bot
          have h1 : ∅ = applyLocalRule rule LR := by aesop
          have h2 : {⊥} ⊆ LR.1 ∧ ∅ ⊆ LR.2 := by aesop
          have appTab := @LocalRuleApp.mk _ _ ∅ _ _ _ rule h1 h2
          have tab := fromRule (AppLocalTableau.mk appTab sorry)
          have closedTab : ClosedTableau LR := sorry -- ClosedTableau.loc tab (by aesop)
          exact IsEmpty.false closedTab
        · sorry
      · simp
        intro f f_in_X
        by_contra nf_in_X
        let tab: AppLocalTableau LR ∅ := sorry -- byLocalRule (Not ⟨f_in_X, nf_in_X⟩) (by aesop)
        have closedTab := ClosedTableau.loc tab (by sorry)
        exact IsEmpty.false closedTab
  case interNode B X Y locRule Y_in pathY IH =>
    simp
    constructor
    · by_contra h1
      rcases h1
      case inl bot_in => sorry
      case inr bot_in => sorry
    · intro f f_in
      by_contra h
      sorry

noncomputable def toWorld: ConsLocalTab →  Finset Formula
  | ⟨⟨_, tabLR⟩, consistentLR⟩ => aPathOf tabLR consistentLR |> toFinset

theorem worldSaturated (conLT: ConsLocalTab): Saturated (toWorld conLT) := by
  sorry

theorem worldConsistent (conLT: ConsLocalTab): ⊥ ∉ toWorld conLT ∧ ∀ P, P ∈ toWorld conLT → ~P ∉ toWorld conLT := by sorry

theorem modelExistence: Consistent (L,R) →
    ∃ (WS : Finset (Finset Formula)) (M : ModelGraph WS) (W : WS), (L ∪ R) ⊆ W :=
  by
  intro consLR
  let WS := ((M₀ (L,R) consLR).map toWorld).toFinset
  let M : KripkeModel WS := by
    constructor
    -- define valuation function
    · intro ⟨w, w_in⟩ p
      exact (·p) ∈ w
    -- define relation
    · intro ⟨w, w_in⟩ ⟨v, v_in⟩
      exact projection w ⊆ v
  let pathLR : Path (L,R) := aPathOf (aLocalTableauFor (L,R)) consLR
  use WS, ⟨M, ?_⟩, ⟨toFinset pathLR, ?_⟩
  · simp
  · constructor
    · intro ⟨W, W_in⟩
      simp at W_in
      choose W' pathW' h using W_in
      subst h
      exact ⟨worldSaturated W', worldConsistent W'⟩
    · constructor
      · aesop
      · constructor
        · intro ⟨w, w_in⟩ ⟨v, v_in⟩ f wRv h
          rewrite [← proj] at h
          aesop
        · intro ⟨w, w_in⟩ f nboxf_in_w
          simp at nboxf_in_w
          simp at w_in
          choose w' w'_in w_eq using w_in
          subst w_eq
          simp at *
          let v_node := endNodeOf (aPathOf w'.1.2 w'.2)
          let v'_in : v_node ∈ endNodesOf w'.1 := by apply endNodeSubsetEndNodes
          have cons_v : Consistent v_node := sorry
          let v': ConsLocalTab := ⟨⟨v_node, aLocalTableauFor v_node⟩, cons_v⟩
          have v_in : v' ∈ M₀ (L,R) consLR := M₀closure1 w'_in v'_in cons_v
          have nboxf_in_v' : ~(□f) ∈ v_node.1 ∨ ~(□f) ∈ v_node.2 := by sorry
          cases nboxf_in_v'
          case inl nboxf_in => sorry
          case inr nboxf_in => sorry
  · simp
    use ⟨⟨(L,R), aLocalTableauFor (L,R)⟩, consLR⟩
    unfold toWorld
    simp
    sorry
/-
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
-/
