import Mathlib.Data.Finset.Basic

import Bml.Modelgraphs
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

/--
A `Path ctn` is a maximal path of consistent TNodes starting with `ctn` and connected by `LocalRuleApp`s.
This does *not* have to be a path in any particular `LocalTableau`.
-/
inductive Path: ConsTNode →  Type
  | endNode (isSimple : Simple LR): Path ⟨LR, LR_cons⟩
  | interNode (_ : LocalRuleApp LR C) (c_in : c ∈ C)
    (tail : Path ⟨c, c_cons⟩): Path ⟨LR, LR_cons⟩
open Path

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

theorem endNodeIsSimple (path : Path consLR) (eq: consLR' = endNodeOf (path)): Simple consLR'.1 := by
  induction path
  all_goals aesop

theorem consistentThenConsistentChild
  (lrApp : LocalRuleApp (L,R) C):
  Consistent (L,R) → ∃ c ∈ C, Consistent c := by
  contrapose
  unfold Consistent Inconsistent
  simp
  intro h
  -- choose closed tableaux for your children
  have c_to_cTab {c: TNode} (c_in: c ∈ C): ClosedTableau c := by
    specialize h c c_in
    exact Classical.choice h
  -- build the local tableau for LR containing these tableau
  apply Nonempty.intro
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule lrApp
    intro c c_in
    let fooo := c_to_cTab c_in
    apply closedToLocal fooo
  case next =>
    intro LR' LR'_in
    have := endNodeIsEndNodeOfChild lrApp LR'_in
    clear LR'_in
    rcases this with ⟨c, LR'_in⟩
    choose c_in_C LR'_in2 using LR'_in
    simp [closedToLocal] at *
    cases def_c : c_to_cTab c_in_C
    case loc lt_c next =>
      rw [def_c] at LR'_in2
      simp at LR'_in2
      apply next
      exact LR'_in2
    case atmL =>
      rw [def_c] at LR'_in2
      aesop
    case atmR =>
      rw [def_c] at LR'_in2
      aesop

theorem consThenProjectLCons (α_in: ~(□α) ∈ L) (LR_simple: Simple (L,R)): (Consistent (L,R)) →
  Consistent (diamondProjectTNode (Sum.inl α) (L,R)) := by
  contrapose
  unfold Consistent Inconsistent
  simp_all
  intro cTab
  exact ⟨ClosedTableau.atmL α_in LR_simple cTab⟩

theorem consThenProjectRCons (α_in: ~(□α) ∈ R) (LR_simple: Simple (L,R)): (Consistent (L,R)) →
  Consistent (diamondProjectTNode (Sum.inr α) (L,R)) := by
  contrapose
  unfold Consistent Inconsistent
  simp_all
  intro cTab
  exact ⟨ClosedTableau.atmR α_in LR_simple cTab⟩

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
  case interNode LR C LR' LR'_cons LR_cons lrApp LR'_in tail IH =>
    simp_all!
    rcases IH with ⟨IH1, ⟨IH2, IH3⟩⟩
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

def botTableauL (bot_in: ⊥ ∈ LR.1): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {⊥} {} (LocalRule.oneSidedL OneSidedLocalRule.bot)
    simp_all
    use []
    simp
    aesop
  case next => aesop

def botTableauR (bot_in: ⊥ ∈ LR.2): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {} {⊥} (LocalRule.oneSidedR OneSidedLocalRule.bot)
    simp_all
    use []
    simp
    aesop
  case next => aesop

def notTableauLL (pp_in: (·pp) ∈ LR.1) (npp_in: (~·pp) ∈ LR.1): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {·pp,~·pp} {} (LocalRule.oneSidedL (OneSidedLocalRule.not (·pp)))
    simp_all [Finset.subset_iff]
    use []
    simp
    aesop
  case next => aesop

def notTableauLR (pp_in: (·pp) ∈ LR.1) (npp_in: (~·pp) ∈ LR.2): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {·pp} {~·pp} (LocalRule.LRnegL (·pp))
    simp_all [Finset.subset_iff]
    use []
    simp
    aesop
  case next => aesop

def notTableauRL (pp_in: (·pp) ∈ LR.2) (npp_in: (~·pp) ∈ LR.1): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {~·pp} {·pp} (LocalRule.LRnegR (·pp))
    simp_all [Finset.subset_iff]
    use []
    simp
    aesop
  case next => aesop

def notTableauRR (pp_in: (·pp) ∈ LR.2) (npp_in: (~·pp) ∈ LR.2): ClosedTableau LR := by
  apply ClosedTableau.loc
  case lt =>
    apply LocalTableau.fromRule
    apply LocalRuleApp.mk _ {} {·pp,~·pp} (LocalRule.oneSidedR (OneSidedLocalRule.not (·pp)))
    simp_all [Finset.subset_iff]
    use []
    simp
    aesop
  case next => aesop

theorem pathConsistent (path : Path TN): ⊥ ∉ pathToFinset path ∧ ∀ (pp: Char), (·pp)  ∈ pathToFinset path → ~(·pp) ∉ pathToFinset path := by
  induction path
  case endNode LR consistentLR simpleLR =>
      unfold Consistent Inconsistent at consistentLR
      simp at consistentLR
      constructor
      · by_contra bot_in
        simp at bot_in
        cases bot_in
        case inl bot_in =>
          exact IsEmpty.false (botTableauL bot_in)
        case inr bot_in =>
          exact IsEmpty.false (botTableauR bot_in)
      · intro pp pp_in
        by_contra npp_in
        simp_all
        cases pp_in
        case inl pp_in =>
          cases npp_in
          case inl npp_in =>
            exact IsEmpty.false (notTableauLL pp_in npp_in)
          case inr npp_in =>
            exact IsEmpty.false (notTableauLR pp_in npp_in)
        case inr pp_in =>
          cases npp_in
          case inl npp_in =>
            exact IsEmpty.false (notTableauRL pp_in npp_in)
          case inr npp_in =>
            exact IsEmpty.false (notTableauRR pp_in npp_in)
  case interNode LR C LR' LR'_cons LR_cons lrApp LR'_in tail IH =>
    constructor
    · by_contra h
      unfold Consistent Inconsistent at *
      simp at LR'_cons LR_cons
      simp_all -- handels the case ⊥ ∈ pathToFinset tail
      cases h
      case inl bot_in =>
        exact IsEmpty.false (botTableauL bot_in)
      case inr bot_in =>
        exact IsEmpty.false (botTableauR bot_in)
    · intro pp pp_in
      by_contra npp_in
      rcases IH with ⟨IH1, IH2⟩
      specialize IH2 pp
      have : (·pp) ∈ pathToFinset tail ∧  (~·pp) ∈ pathToFinset tail:= by
        rcases lrApp with ⟨ress, Lcond,Rcond, lr, Lcond_in, Rcond_in⟩
        rename_i L R C_eq
        subst C_eq
        simp_all
        constructor
        · rcases pp_in with pp_in | pp_in | pp_in
          · apply LR_in_PathLR
            simp
            apply Or.inl
            cases_type* LocalRule OneSidedLocalRule
            all_goals aesop
          · apply LR_in_PathLR
            simp
            apply Or.inr
            cases_type* LocalRule OneSidedLocalRule
            all_goals aesop
          · assumption
        · rcases npp_in with npp_in | npp_in | npp_in
          · apply LR_in_PathLR
            simp
            apply Or.inl
            cases_type* LocalRule OneSidedLocalRule
            all_goals aesop
          · apply LR_in_PathLR
            simp
            apply Or.inr
            cases_type* LocalRule OneSidedLocalRule
            all_goals aesop
          · assumption
      simp_all

theorem pathProjection (path: Path consLR): projection (pathToFinset path) ⊆ projection (toFinset (endNodeOf path)) := by
  intro α α_in
  rewrite [proj] at *
  induction path
  case endNode LR LR_cons LR_simple => aesop
  case interNode LR C c c_cons LR_cons lrApp c_in tail IH =>
    simp_all
    apply IH
    rcases lrApp with ⟨ress, Lcond, Rcond, lr, Lcond_in, Rcond_in⟩
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
  case interNode LR C c c_cons LR_cons lrApp c_in tail IH =>
    simp_all
    apply IH
    rcases lrApp with ⟨ress, Lcond, Rcond, lr, Lcond_in, Rcond_in⟩
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
  case fromRule C lrApp =>
    choose c c_in c_cons using consistentThenConsistentChild lrApp conLR.2
    have : lengthOf c < lengthOf conLR.1 := by
      apply localRuleAppDecreasesLength lrApp c c_in
    exact interNode lrApp c_in (aPathOf ⟨c, c_cons⟩)
termination_by
  lengthOf conLR

noncomputable def toWorld (consLR: ConsTNode): Finset Formula :=
  pathToFinset (aPathOf consLR)

inductive M₀ (T0 : ConsTNode) : ConsTNode → Prop
| base : M₀ T0 T0

| inductiveL (T : ConsTNode) : (M₀ T0 T) → (eq: ⟨⟨L,R⟩, LR_cons⟩ = endNodeOf (aPathOf T)) → ∀ α, (h: ~(□α) ∈ L) →
  M₀ T0 ⟨diamondProjectTNode (Sum.inl α) ⟨L,R⟩, by
    apply consThenProjectLCons h (endNodeIsSimple (aPathOf T) eq) LR_cons⟩

| inductiveR (T : ConsTNode) : (M₀ T0 T) →  (eq: ⟨⟨L,R⟩, LR_cons⟩ = endNodeOf (aPathOf T)) → ∀ α, (h: ~(□α) ∈ R) →
  M₀ T0 ⟨diamondProjectTNode (Sum.inr α) ⟨L,R⟩, by
    apply consThenProjectRCons h (endNodeIsSimple (aPathOf T) eq) LR_cons⟩

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
        · -- notation: w_world for world, w for TNode, w' for ConsTNode
          intro ⟨w_world, w_world_in⟩ f nboxf_in_w
          unfold WS at w_world_in
          simp at w_world_in
          rcases w_world_in with ⟨ w', w'_in, w_world_eq⟩
          subst w_world_eq
          let v' := endNodeOf (aPathOf w')
          have v'_def : v' = endNodeOf (aPathOf w') := by aesop
          rcases v' with ⟨⟨vL, vR⟩, v_cons⟩
          have nboxf_in_v : ~(□f) ∈ vL ∪ vR := by
            have := pathDiamond (aPathOf w') nboxf_in_w
            rw[←v'_def] at this
            simp_all
          have v_simp: Simple (vL,vR) := by
            apply endNodeIsSimple (aPathOf w') v'_def
          simp at nboxf_in_v
          cases nboxf_in_v
          case inl nboxf_in =>
            let u := diamondProjectTNode (Sum.inl f) ⟨vL, vR⟩
            have u_cons := consThenProjectLCons nboxf_in v_simp v_cons
            let u' : ConsTNode := ⟨u, u_cons⟩
            have u_eq: u = (projection vL ∪ {~f}, projection vR) := by
              simp (config := {zetaDelta := true}) only
              unfold diamondProjectTNode
              aesop
            use ⟨toWorld u', ?_⟩
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ ⊆ projection (toFinset (endNodeOf (aPathOf w'))) := by apply pathProjection (aPathOf w')
                _ ⊆ projection (vL ∪ vR) := by rw[← v'_def]; simp
                _ ⊆ u.1 ∪ u.2 := by rw[u_eq, projectionUnion]; simp
                _ ⊆ toWorld u' := by apply LR_in_PathLR
            · have nf_in : ~f ∈ u.1 ∪ u.2 := by
                simp (config := {zetaDelta := true})
                unfold diamondProjectTNode
                split
                all_goals simp_all
              apply (LR_in_PathLR _) nf_in
            · have h := M₀.inductiveL w' w'_in v'_def
              simp at h
              specialize h f nboxf_in
              use u'
              simp_all only [union_singleton_is_insert, and_true]
              exact h
          case inr nboxf_in =>
            let u := diamondProjectTNode (Sum.inr f) ⟨vL, vR⟩
            let u' : ConsTNode := ⟨u, (by apply consThenProjectRCons nboxf_in v_simp v_cons)⟩
            have u_eq: u = (projection vL, projection vR ∪ {~f}) := by
              simp (config := {zetaDelta := true}) only
              unfold diamondProjectTNode
              aesop
            have u_sub: u.1 ∪ u.2 ⊆ toWorld u' := by apply LR_in_PathLR
            use ⟨toWorld u', ?_⟩
            constructor
            · calc
                projection (toWorld w') = projection (pathToFinset (aPathOf w')) := by aesop
                _ ⊆ projection (toFinset (endNodeOf (aPathOf w'))) := by apply pathProjection (aPathOf w')
                _ ⊆ projection (vL ∪ vR) := by rw[← v'_def]; simp
                _ ⊆ u.1 ∪ u.2 := by rw[u_eq, projectionUnion]; simp
                _ ⊆ toWorld u' := by apply LR_in_PathLR
            · have nf_in : ~f ∈ u.1 ∪ u.2 := by
                simp (config := {zetaDelta := true})
                unfold diamondProjectTNode
                split
                all_goals simp_all
              apply u_sub nf_in
            · have h := M₀.inductiveR w' w'_in v'_def
              specialize h f nboxf_in
              use u'
              simp_all only [union_singleton_is_insert, and_true]
              exact h
  · use ⟨(L,R), LR_cons⟩
    unfold toWorld
    simp [pathLR]
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
