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
open OneSidedLocalRule

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

/-
-- simp does not work here
def lengthOfPath: Path consLR → ℕ
  | endNode _ => 1
  | interNode _ _ tail => 1 + lengthOfPath tail

@[simp]
theorem lengthOfPathDecreasing {h: path = interNode appTab c_in tail}: lengthOfPath path < lengthOfPath tail := by
  subst h
  --unfold lengthOfPath
  sorry

@[simp]
instance : HasLength (Path ⟨LR, consLR⟩) := ⟨lengthOf LR⟩
-/
@[simp]
def pathToFinset: Path ⟨(L,R), cons⟩  → Finset Formula
  | endNode _ => L ∪ R
  | (interNode _ _ tail) => L ∪ R ∪ pathToFinset tail

@[simp]
theorem LR_in_PathLR (path : Path ⟨(L,R),LR_cons⟩) : L ∪ R ⊆ (pathToFinset path) := by
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


theorem consistentThenConsistentChild (appTab : AppLocalTableau LR C):
  Consistent LR → ∃ c ∈ C, Consistent c := by
  contrapose
  unfold Consistent Inconsistent
  simp_all
  sorry

theorem consThenProjectLCons: (Consistent (L,R)) → (~(□α) ∈ L) →
  Consistent (diamondProjectTNode (Sum.inl α) (L,R)) := by sorry

theorem consThenProjectRCons: (Consistent (L,R)) → (~(□α)∈ R) →
  Consistent (diamondProjectTNode (Sum.inr α) (L,R)) := by sorry

theorem pathSaturated (path : Path consLR): Saturated (pathToFinset path) := by
  intro P Q
  induction path
  case endNode LR LR_cons LR_simple =>
    unfold Simple SimpleSet at LR_simple
    rcases LR_simple with ⟨L_simple, R_simple⟩
    simp_all
    constructor
    · intro nnP_in
      cases nnP_in
      · case inl nnP_in_L =>
        specialize L_simple ⟨~~P, nnP_in_L⟩;
        simp at L_simple
      · case inr nnP_in_R =>
        specialize R_simple ⟨~~P, nnP_in_R⟩;
        simp at R_simple
    · constructor
      · intro PQ_in
        cases PQ_in
        · case inl PQ_in_L =>
          specialize L_simple ⟨P ⋀ Q, PQ_in_L⟩
          simp at L_simple
        · case inr PQ_in_R =>
          specialize R_simple ⟨P ⋀ Q, PQ_in_R⟩;
          simp at R_simple
      · intro PQ_in
        cases PQ_in
        · case inl PQ_in_L =>
          specialize L_simple ⟨~(P ⋀ Q), PQ_in_L⟩
          simp at L_simple
        · case inr PQ_in_R =>
          specialize R_simple ⟨~(P ⋀ Q), PQ_in_R⟩;
          simp at R_simple
  case interNode LR C LR' LR'_cons LR_cons appTab LR'_in tail IH =>
    simp_all!
    rcases IH with ⟨IH1, ⟨IH2, IH3⟩⟩
    rcases appTab with ⟨lrApp, next⟩
    rename_i L R
    constructor
    -- ~~P ∈ U → P ∈ U
    · intro nnP_in
      apply Or.inr
      apply Or.inr
      cases nnP_in
      · case inl nnP_in_L =>
        have h := LocalRuleUniqueL nnP_in_L lrApp (neg P) rfl
        specialize h LR' LR'_in
        cases h
        · case inl nnP_in_L' =>
          apply IH1
          apply LR_in_PathLR
          simp_all
        · case inr P_in_L' =>
          apply LR_in_PathLR
          simp_all
      · case inr nnP_in =>
        cases nnP_in
        · case inl nnP_in_R =>
          have h := LocalRuleUniqueR nnP_in_R lrApp (neg P) rfl
          specialize h LR' LR'_in
          cases h
          · case inl nnP_in_R' =>
            apply IH1
            apply LR_in_PathLR
            simp_all
          · case inr P_in_R' =>
            apply LR_in_PathLR
            simp_all
        · case inr nnP_in_tail => simp_all
    · constructor
    -- P⋀Q ∈ U  → P ∈ U  and Q ∈ U
      · intro PQ_in
        cases PQ_in
        · case inl PQ_in_L =>
          have h := LocalRuleUniqueL PQ_in_L lrApp (con P Q) rfl
          specialize h LR' LR'_in
          cases h
          · case inl PQ_in_L' =>
            have : P⋀Q ∈ pathToFinset tail := by
              apply LR_in_PathLR
              simp_all
            aesop
          · case inr P_Q_in_L' =>
            constructor
            all_goals
              apply Or.inr
              apply Or.inr
              apply LR_in_PathLR
              aesop
        · case inr PQ_in =>
          cases PQ_in
          · case inl PQ_in_R =>
            have h := LocalRuleUniqueR PQ_in_R lrApp (con P Q) rfl
            specialize h LR' LR'_in
            cases h
            · case inl PQ_in_R' =>
              have : P⋀Q ∈ pathToFinset tail := by
                apply LR_in_PathLR
                simp_all
              aesop
            · case inr P_Q_in_R' =>
              constructor
              all_goals
                apply Or.inr
                apply Or.inr
                apply LR_in_PathLR
                aesop
          case inr PQ_in_tail => simp_all
      -- ~(P⋀Q) ∈ U   → ~P ∈ U  or  ~Q ∈ U
      · intro nPQ_in
        cases nPQ_in
        · case inl nPQ_in_L =>
          have h := LocalRuleUniqueL nPQ_in_L lrApp (ncon P Q) rfl
          specialize h LR' LR'_in
          cases h
          · case inl nPQ_in_L' =>
            have : ~(P⋀Q) ∈ pathToFinset tail := by
              apply LR_in_PathLR
              simp_all
            aesop
          · case inr nP_nQ_in_L' =>
            simp_all
            cases nP_nQ_in_L'
            case inl nP_in_L'=>
              apply Or.inl
              apply_rules [Or.inr, LR_in_PathLR]
              simp_all
            case inr nQ_in_L' =>
              apply_rules [Or.inr, LR_in_PathLR]
              simp_all
        · case inr PQ_in =>
          cases PQ_in
          case inl nPQ_in_R =>
            have h := LocalRuleUniqueR nPQ_in_R lrApp (ncon P Q) rfl
            specialize h LR' LR'_in
            cases h
            · case inl nPQ_in_R' =>
              have : ~(P⋀Q) ∈ pathToFinset tail := by
                apply LR_in_PathLR
                simp_all
              aesop
            · case inr nP_nQ_in_R' =>
              simp_all
              cases nP_nQ_in_R'
              case inl nP_in_R'=>
                apply Or.inl
                apply_rules [Or.inr, LR_in_PathLR]
                simp_all
              case inr nQ_in_R' =>
                apply_rules [Or.inr, LR_in_PathLR]
                simp_all
          case inr nPQ_in_tail =>
            simp_all
            cases IH3
            all_goals simp_all

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

theorem pathProjection (path: Path consLR): projection (pathToFinset path) ⊆ projection (toFinset (endNodeOf path)) := by
  intro α α_in
  rewrite [proj] at *
  induction path
  case endNode LR LR_cons LR_simple => aesop
  case interNode LR C c c_cons LR_cons appTab c_in tail IH =>
    simp_all
    apply IH
    rcases appTab with ⟨ruleA, subTabs⟩
    rcases ruleA with ⟨ress, Lcond, Rcond, lr, Lcond_in, Rcond_in⟩
    rename_i L R C_eq
    subst C_eq
    cases α_in
    case inl α_in =>
      apply Finset.mem_of_subset (LR_in_PathLR tail)
      cases lr
      case oneSidedL ress orule =>
        cases orule
        all_goals aesop
      all_goals aesop
    case inr α_in =>
      cases α_in
      case inl α_in =>
        apply Finset.mem_of_subset (LR_in_PathLR tail)
        cases lr
        case oneSidedR ress orule =>
          cases orule
          all_goals aesop
        all_goals aesop
      case inr α_in => assumption

theorem pathDiamond (path: Path consLR) (α_in: ~(□α) ∈ pathToFinset path): ~(□α) ∈ toFinset (endNodeOf path) := by
  induction path
  case endNode LR LR_cons LR_simple => aesop
  case interNode LR C c c_cons LR_cons appTab c_in tail IH =>
    simp_all
    apply IH
    rcases appTab with ⟨ruleA, subTabs⟩
    rcases ruleA with ⟨ress, Lcond, Rcond, lr, Lcond_in, Rcond_in⟩
    rename_i L R C_eq
    subst C_eq
    cases α_in
    case inl α_in =>
      apply Finset.mem_of_subset (LR_in_PathLR tail)
      cases lr
      case oneSidedL ress orule =>
        cases orule
        all_goals aesop
      all_goals aesop
    case inr α_in =>
      cases α_in
      case inl α_in =>
        apply Finset.mem_of_subset (LR_in_PathLR tail)
        cases lr
        case oneSidedR ress orule =>
          cases orule
          all_goals aesop
        all_goals aesop
      case inr α_in => assumption

-- given a consistent TNode LR, gives a (consistent) path in aLocalTableauFor LR
noncomputable def aPathOf (conLR : ConsTNode) : Path conLR := by
  cases (aLocalTableauFor conLR.1)
  case fromSimple isSimple  => exact endNode isSimple
  case fromRule C appTab  =>
    choose c c_in c_cons using consistentThenConsistentChild appTab conLR.2
    have : lengthOf c < lengthOf conLR.1 := by
      apply AppLocalTableau.DecreasesLength appTab c_in
    exact interNode appTab c_in (aPathOf ⟨c, c_cons⟩)
termination_by aPathOf conLR => lengthOf conLR

noncomputable def toWorld (consLR: ConsTNode): Finset Formula :=
  pathToFinset (aPathOf consLR)

inductive M₀ (T0 : ConsTNode) : ConsTNode → Prop
| base : M₀ T0 T0
| inductiveL (T : ConsTNode) : (M₀ T0 T) → ⟨⟨L,R⟩, LR_cons⟩ = endNodeOf (aPathOf T) → ∀ α, (h: ~(□α) ∈ L) →
  M₀ T0 ⟨diamondProjectTNode (Sum.inl α) ⟨L,R⟩, by apply consThenProjectLCons LR_cons h⟩

| inductiveR (T : ConsTNode) : (M₀ T0 T) →  ⟨⟨L,R⟩, LR_cons⟩ = endNodeOf (aPathOf T) → ∀ α, (h: ~(□α) ∈ R) →
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
            have u_sub: u_root.1 ∪ u_root.2 ⊆ toWorld u' := by apply LR_in_PathLR
            use toWorld u'
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ ⊆ projection v := by apply pathProjection (aPathOf w')
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
            have u_sub: u_root.1 ∪ u_root.2 ⊆ toWorld u' := by apply LR_in_PathLR
            use toWorld u'
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ ⊆ projection v := by apply pathProjection (aPathOf w')
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
  · exact correctness X

theorem singletonCompleteness : ∀ φ, Consistent ({φ},{}) ↔ Satisfiable φ :=
  by
  intro f
  have := completeness ({f},{})
  simp only [singletonSat_iff_sat] at *
  aesop

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
