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

def ConsTNode := Subtype fun Y => Consistent Y

@[simp]
instance : HasLength ConsTNode := ⟨λ ⟨LR,_⟩ => lengthOf LR⟩

@[simp]
def toFinset : ConsTNode → Finset Formula := λ ⟨⟨L,R⟩,_⟩ => L ∪ R

inductive Path: ConsTNode →  Type
  | endNode (isSimple : Simple LR): Path ⟨LR, LR_cons⟩
  | interNode (_ : AppLocalTableau LR C) (c_in : c ∈ C)
    (tail : Path ⟨c, c_cons⟩): Path ⟨LR, LR_cons⟩
open Path

@[simp]
def pathToFinset: Path ⟨(L,R), cons⟩  → Finset Formula
  | endNode _ => L ∪ R
  | (interNode _ _ tail) => L ∪ R ∪ pathToFinset tail

@[simp]
theorem X_in_PathX (path : Path ⟨(L,R),LR_cons⟩) : L ∪ R ⊆ (pathToFinset path) := by
  cases path
  case endNode => simp [instTNodeHasSubset]
  case interNode Y C C_in tail appTab =>
    simp_all only [instTNodeHasSubset,instHasSubsetProdFinsetFormula, pathToFinset, instTNodeUnion,
      instUnionProdFinsetFormula, Finset.subset_union_left, and_self]

@[simp]
def endNodeOf: Path ⟨LR,LR_cons⟩ → ConsTNode
  | endNode _ => ⟨LR, LR_cons⟩
  | interNode _ _ tail => endNodeOf tail

theorem endNodeIsSimple (path : Path consLR): Simple (endNodeOf path).1 := by
  induction path
  all_goals aesop

-- Not sure if needed
theorem endNodeProjection (path : Path X) {h: (L, R) = projectTNode (endNodeOf path).1}: projection (pathToFinset path) = L ∪ R := by
  /-cases path
  case endNode cosX simX =>
    aesop
  case interNode LR Y_in tail appTab =>
    simp only [endNodeOf]
    rw[← endNodeProjection tail]
    unfold projectTNode-/
    sorry
--termination_by endNodeProjection path => lengthOfTNode (L,R)
--decreasing_by sorry

--theorem endNodeInPath {path : Path X} {h : (L,R) = endNodeOf path}: L ∪ R ⊆ (pathToFinset path) := by sorry

--theorem endNodeSubsetEndNodes (path: Path X) (tX: LocalTableau X): endNodeOf path ∈ endNodesOf ⟨X, tX⟩ := by


theorem consistentThenConsistentChild
    (isConsistent: Consistent LR) (appTab : AppLocalTableau LR C): ∃ c ∈ C, Consistent c := by
  sorry

theorem consThenProjectLCons: (Consistent (L,R)) → (~(□α) ∈ L) →
  Consistent (diamondProjectTNode (Sum.inl α) (L,R)) := by sorry

theorem consThenProjectRCons: (Consistent (L,R)) → (~(□α)∈ R) →
  Consistent (diamondProjectTNode (Sum.inr α) (L,R)) := by sorry

theorem pathSaturated (path : Path LR): Saturated (pathToFinset path) := by
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
            have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
              have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
              have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
            have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
              have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
              have : (P⋀Q ∈ X) → (P⋀Q ∈ pathToFinset tail) := by
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
          have nP_Q_in_tail : ~(P⋀Q) ∈ pathToFinset tail := by
            cases nP_Q_in_path
            apply X_in_PathX; refine Finset.mem_union_left {α} ?_; aesop
            aesop
          clear nP_Q_in_path
          aesop
        · case Con β γ β_γ_in_X =>
          have : Y = X \ {β⋀γ} ∪ {β,γ} := by
            simp at *; exact Y_in
          clear Y_in; subst Y
          have nP_Q_in_tail : ~(P⋀Q) ∈ pathToFinset tail := by
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
                have : ~β ∈ pathToFinset tail := by
                  apply X_in_PathX
                  aesop
                aesop
            · case neg neq =>
                have : ~(P⋀Q) ∈ pathToFinset tail := by
                  cases nP_Q_in_path
                  apply X_in_PathX; refine Finset.mem_union_left {~β} ?_; refine Finset.mem_sdiff.mpr ?_; aesop
                  aesop
                aesop
          · case inr =>
            clear Y_in; subst Y
            by_cases ~(P⋀Q) = ~(β⋀γ)
            · case pos eq =>
                simp at eq; cases eq; subst P; subst Q
                have : ~γ ∈ pathToFinset tail := by
                  apply X_in_PathX
                  aesop
                aesop
            · case neg neq =>
                have : ~(P⋀Q) ∈ pathToFinset tail := by
                  cases nP_Q_in_path
                  apply X_in_PathX; refine Finset.mem_union_left {~γ} ?_; refine Finset.mem_sdiff.mpr ?_; aesop
                  aesop
                aesop-/
    sorry

theorem pathConsistent (path : Path TN): ⊥ ∉ pathToFinset path ∧ ∀ P, P ∈ pathToFinset path → ~P ∉ pathToFinset path := by
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

theorem pathProjection (path: Path consLR): projection (pathToFinset path) = projection (toFinset (endNodeOf path)) := by sorry

theorem pathDiamond (path: Path consLR) (α_in: ~(□α) ∈ pathToFinset path): ~(□α) ∈ toFinset (endNodeOf path) := by sorry
  /-induction aPathOf ⟨LR, LR_cons⟩
  case endNode LR LR_cons LR_simple =>
    rcases h : conLR with ⟨LR', LR_cons'⟩
    have: LR = LR':= by simp
    simp_all!
    sorry
  case interNode => sorry

  cases path_eq: aPathOf ⟨LR, LR_cons⟩
  case endNode isSimple => aesop
  case interNode C c c_cons c_in tail _ appTab =>
    simp_all
    have : endNodeOf (aPathOf ⟨c, c_cons⟩) = endNodeOf (aPathOf ⟨LR, LR_cons⟩) := by sorry
    have := AppLocalTableau.DecreasesLength appTab c_in
    rcases α_in
    case inl α_in =>
      have := AppLocalTableau.PreservesDiamondL appTab α_in c_in
      have α_in_c': ~(□α) ∈ toWorld ⟨c, c_cons⟩ := by
        apply Finset.mem_of_subset LR_in_toWorldLR
        aesop
      have := worldDiamond ⟨c, c_cons⟩ α_in_c'
      simp_all
    case inr α_in =>
      cases α_in
      case inl α_in =>
        have := AppLocalTableau.PreservesDiamondR appTab α_in c_in
        have α_in_c': ~(□α) ∈ toWorld ⟨c, c_cons⟩ := by
          apply Finset.mem_of_subset LR_in_toWorldLR
          aesop
        have := worldDiamond ⟨c, c_cons⟩ α_in_c'
        simp_all
      case inr α_in => exact worldDiamond ⟨c, c_cons⟩ α_in
termination_by worldDiamond conTN α_in => lengthOf conTN
decreasing_by simp_wf; sorry-/

-- given a consistent TNode LR, gives a (consistent) path in aLocalTableauFor LR
noncomputable def aPathOf (conLR : ConsTNode) : Path conLR := by
  cases (aLocalTableauFor conLR.1)
  case fromSimple isSimple  => exact endNode isSimple
  case fromRule C appTab  =>
    choose c c_in c_cons using consistentThenConsistentChild conLR.2 appTab
    have : lengthOf c < lengthOf conLR.1 := by
      apply AppLocalTableau.DecreasesLength appTab c_in
    exact interNode appTab c_in (aPathOf ⟨c, c_cons⟩)
termination_by aPathOf conLR => lengthOf conLR

noncomputable def toWorld (consLR: ConsTNode): Finset Formula :=
  pathToFinset (aPathOf consLR)

inductive M₀ (T0 : ConsTNode) : ConsTNode → Prop
| base : M₀ T0 T0
| inductiveL (T : ConsTNode) : (M₀ T0 T) → ⟨⟨L,R⟩, LR_cons⟩ = (endNodeOf (aPathOf T)) → ∀ α, (h: ~(□α) ∈ L) →
  M₀ T0 ⟨diamondProjectTNode (Sum.inl α) ⟨L,R⟩, by apply consThenProjectLCons LR_cons h⟩

| inductiveR (T : ConsTNode) : (M₀ T0 T) →  ⟨⟨L,R⟩, LR_cons⟩ = (endNodeOf (aPathOf T)) → ∀ α, (h: ~(□α) ∈ R) →
  M₀ T0 ⟨diamondProjectTNode (Sum.inr α) ⟨L,R⟩, by apply consThenProjectRCons LR_cons h⟩

theorem modelExistence: Consistent (L,R) →
    ∃ (WS : Set (Finset Formula)) (_ : ModelGraph WS) (W : WS), (L ∪ R) ⊆ W :=
  by
  intro LR_cons
  let roots := {consTNode | (M₀ ⟨(L,R), LR_cons⟩) consTNode}
  let WS := {toWorld consLT | consLT ∈ roots}
  let M : KripkeModel WS := by
    constructor
    -- define valuation function
    · intro ⟨w, _⟩ p
      exact (·p) ∈ w
    -- define relation
    · intro ⟨w, _⟩ ⟨v, _⟩
      exact projection w ⊆ v
  let pathLR := aPathOf ⟨(L,R), LR_cons⟩
  use WS, ⟨M, ?_⟩, ⟨pathToFinset pathLR, ?_⟩
  · simp
  · constructor
    · intro ⟨W, W_in⟩
      simp_all
      choose W' _ h using W_in
      subst h
      exact ⟨pathSaturated (aPathOf W'), pathConsistent (aPathOf W')⟩
    · constructor
      · aesop
      · constructor
        · intro ⟨w, w_in⟩ ⟨v, v_in⟩ f wRv h
          rewrite [← proj] at h
          aesop
        · intro ⟨w, w_in⟩ f nboxf_in_w
          simp_all
          choose w' w'_in w_eq using w_in
          subst w_eq
          let v' := endNodeOf (aPathOf w')
          rcases v'_eq : v' with ⟨⟨v'L, v'R⟩, v_cons⟩
          let v := toFinset v'
          have v_eq : v = v'L ∪ v'R := by
            change toFinset v' = v'L ∪ v'R
            rw[v'_eq]
            simp_all
          have nboxf_in_v : ~(□f) ∈ v'L ∪ v'R := by
            have := pathDiamond (aPathOf w') nboxf_in_w
            rw[←v_eq]
            aesop
          simp at nboxf_in_v
          cases nboxf_in_v
          case inl nboxf_in =>
            let u_root := diamondProjectTNode (Sum.inl f) ⟨v'L, v'R⟩
            let u' : ConsTNode := ⟨u_root, (by apply consThenProjectLCons v_cons nboxf_in)⟩
            have u_eq: u_root = (projection v'L ∪ {~f}, projection v'R) := by
              simp only
              unfold diamondProjectTNode
              aesop
            have u_sub: u_root.1 ∪ u_root.2 ⊆ toWorld u' := by apply X_in_PathX
            use toWorld u'
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ = projection v := by rw [pathProjection (aPathOf w')]
                _ ⊆ u_root.1 ∪ u_root.2 := by rw[u_eq, v_eq, projectionUnion]; simp
                _ ⊆ toWorld u' := by exact u_sub
            constructor
            · have h := M₀.inductiveL w' w'_in (Eq.symm v'_eq)
              simp at h
              specialize h f nboxf_in
              use u'
            · have nf_in : ~f ∈ u_root.1 ∪ u_root.2 := by
                simp
                unfold diamondProjectTNode
                split
                all_goals simp_all
              apply u_sub nf_in
          case inr nboxf_in =>
            let u_root := diamondProjectTNode (Sum.inr f) ⟨v'L, v'R⟩
            let u' : ConsTNode := ⟨u_root, (by apply consThenProjectRCons v_cons nboxf_in)⟩
            have u_eq: u_root = (projection v'L, projection v'R ∪ {~f}) := by
              simp only
              unfold diamondProjectTNode
              aesop
            have u_sub: u_root.1 ∪ u_root.2 ⊆ toWorld u' := by apply X_in_PathX
            use toWorld u'
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ = projection v := by rw [pathProjection (aPathOf w')]
                _ ⊆ u_root.1 ∪ u_root.2 := by rw[u_eq, v_eq, projectionUnion]; simp
                _ ⊆ toWorld u' := by exact u_sub
            constructor
            · have h := M₀.inductiveR w' w'_in (Eq.symm v'_eq)
              specialize h f nboxf_in
              use u'
            · have nf_in : ~f ∈ u_root.1 ∪ u_root.2 := by
                simp
                unfold diamondProjectTNode
                split
                all_goals simp_all
              apply u_sub nf_in
  · use ⟨(L,R), LR_cons⟩
    unfold toWorld
    simp
    exact M₀.base

-- Theorem 4, page 37
theorem completeness : ∀ X, Consistent X ↔ Satisfiable X :=
  by
  intro X
  constructor
  · intro X_is_consistent
    have ⟨WS, M, w, h⟩ := modelExistence X_is_consistent
    use WS, M.val, w
    have := truthLemma M w
    aesop
  -- use Theorem 2:
  · sorry -- exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent ({φ},{}) ↔ Satisfiable φ :=
  by
  intro f
  have := completeness ({f},{})
  simp only [singletonSat_iff_sat] at *
  sorry -- tauto

/-
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
-/
