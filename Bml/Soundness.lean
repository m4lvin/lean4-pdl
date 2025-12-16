-- SOUNDNESS

import Bml.Tableau


open HasSat

open Classical in
/-- Combine a collection of pointed models with one new world using the given valuation. -/
-- TODO: rewrite to term mode?
def combinedModel {β : Type} (collection : β → Σ W : Type, KripkeModel W × W)
    (newVal : Char → Prop) :
    KripkeModel (Sum Unit (Σ k : β, (collection k).fst)) × Sum Unit (Σ k : β, (collection k).fst) :=
  by
  constructor
  constructor
  · -- making the valuation function:
    intro world
    cases world
    case inl newWorld => -- the one new world
      cases newWorld
      exact newVal -- use new given valuation here!!
    case inr oldWorld => -- world in one of the given models:
      rcases oldWorld with ⟨R, w⟩
      exact (collection R).snd.fst.val w
  · -- defining relations:
    intro worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl => exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld =>
      exact HEq oldWorld.snd (collection oldWorld.fst).snd.snd -- conect new world to given points.
    case inr.inl => exact False -- no connection from models to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      rcases oldWorldOne with ⟨kOne, wOne⟩
      rcases oldWorldTwo with ⟨kTwo, wTwo⟩
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.fst.Rel wOne wTwo
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()

/-- The combined model preserves all truths at the old worlds. -/
theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      Evaluate ((combinedModel collection newVal).fst, Sum.inr ⟨R, oldWorld⟩) f ↔
        Evaluate ((collection R).snd.fst, oldWorld) f :=
  by
    intro f
    induction f <;> intro R oldWorld
    case bottom => aesop
    case atom_prop c =>
      unfold combinedModel
      simp
    case neg f f_IH =>
      unfold Evaluate
      rw [f_IH R oldWorld]
    case And f g f_IH g_IH =>
      unfold Evaluate
      rw [f_IH R oldWorld]
      rw [g_IH R oldWorld]
    case box f f_IH =>
      unfold Evaluate
      constructor
      · intro true_in_combo   otherWorld rel_in_old_model
        specialize f_IH R otherWorld
        rw [← f_IH]
        specialize true_in_combo (Sum.inr ⟨R, otherWorld⟩)
        apply true_in_combo
        unfold combinedModel
        simpa
      · intro true_in_old
        simp only [Sum.forall]
        constructor
        · intro newWorld
          unfold combinedModel
          -- the new world is never reachable, trivial case
          tauto
        · rintro ⟨otherR, otherWorld⟩
          intro rel_in_new_model
          specialize f_IH otherR otherWorld
          unfold combinedModel at rel_in_new_model
          have sameR : R = otherR := by aesop
          subst sameR
          rw [f_IH]
          apply true_in_old
          -- remains to show that related in old model
          simp_all


/-- The combined model for X satisfies X. -/
theorem combMo_sat_LR {L R : Finset Formula} {β : Set Formula}
    {beta_def : β = {F : Formula | f_in_TNode (~F.box) (L, R)}}
    (simple_LR : Simple (L, R)) (not_closed_LR : ¬Closed (L ∪ R))
    (collection : β → Σ W : Type, KripkeModel W × W)
    (all_pro_sat :
      ∀ F : β,
        ∀ f ∈ (projection (L ∪ R) ∪ {~F}),
          Evaluate ((collection F).snd.fst, (collection F).snd.snd) f) :
    ∀ f, f_in_TNode f (L, R)
      → Evaluate
        ((combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).fst,
          (combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).snd)
        f :=
  by
    intro f f_in_LR
    unfold Simple SimpleSet at simple_LR
    simp only [Finset.mem_attach, SimpleForm, forall_const, Subtype.forall] at simple_LR
    simp only [f_in_TNode, Finset.mem_union] at f_in_LR
    rw [←Finset.mem_union] at f_in_LR
    cases f
    -- no induction because (L, R) is simple
    case bottom =>
      unfold Closed at not_closed_LR
      aesop
    case atom_prop =>
      unfold combinedModel
      unfold Evaluate
      aesop
    case
      neg f =>
      -- subcases :-/
      cases f
      case atom_prop =>
        unfold combinedModel
        unfold Evaluate
        unfold Closed at not_closed_LR
        rw [not_or] at not_closed_LR
        aesop
      case box f =>
        -- set coMo := ,
        simp only [Evaluate, not_forall]
        -- need reachable world with ~f, use the β-witness
        let h : f ∈ β := by rw [beta_def]; use f_in_LR
        let oldWorld : Sum Unit (Σ k : β, (collection k).fst) :=
          Sum.inr ⟨⟨f, h⟩, (collection ⟨f, h⟩).snd.snd⟩
        use oldWorld
        constructor
        · -- show that f is false at old world
          have coMoLemma :=
            combMo_preserves_truth_at_oldWOrld collection (fun c : Char => (·c) ∈ (L ∪ R)) f ⟨f, h⟩
              (collection ⟨f, h⟩).snd.snd
          rw [coMoLemma]
          specialize all_pro_sat ⟨f, h⟩ (~f)
          unfold Evaluate at all_pro_sat
          simp only [Finset.mem_union, Prod.mk.eta, projectionUnion, Finset.union_singleton,
            Finset.mem_insert, true_or, forall_const] at *
          exact all_pro_sat
        ·-- show that worlds are related in combined model (def above, case 2)
          aesop
      case bottom => tauto
      case neg f =>
        rw [Finset.mem_union] at f_in_LR
        cases f_in_LR
        case inl hyp =>
          have := simple_LR.1 (~~f) hyp
          simp at this
        case inr hyp =>
          have := simple_LR.2 (~~f) hyp
          simp at this
      case And f g =>
        rw [Finset.mem_union] at f_in_LR
        cases f_in_LR
        case inl hyp =>
          have := simple_LR.1 (~(f⋀g)) hyp
          simp at this
        case inr hyp =>
          have := simple_LR.2 (~(f⋀g)) hyp
          simp at this
    case And fa fb =>
      rw [Finset.mem_union] at f_in_LR
      cases f_in_LR
      case inl hyp =>
        have := simple_LR.1 (fa⋀fb) hyp
        simp at this
      case inr hyp =>
        have := simple_LR.2 (fa⋀fb) hyp
        simp at this
    case box f =>
      unfold Evaluate
      intro otherWorld is_rel
      cases otherWorld
      · cases is_rel
      case inr otherWorld => -- otherWorld cannot be the (unreachable) new world
        have coMoLemma :=
          combMo_preserves_truth_at_oldWOrld collection (fun c => (·c) ∈ (L ∪ R)) f otherWorld.fst
            otherWorld.snd
        rw [coMoLemma]
        specialize all_pro_sat otherWorld.fst f
        simp only [projectionUnion, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
          Prod.mk.eta] at all_pro_sat
        rw [or_imp] at all_pro_sat
        rcases all_pro_sat with ⟨_, all_pro_sat_right⟩
        rw [←proj] at f_in_LR
        simp only [f_in_TNode, Finset.mem_union, projectionUnion, Sigma.eta] at *
        specialize all_pro_sat_right f_in_LR
        have sameWorld : otherWorld.snd = (collection otherWorld.fst).snd.snd := by
          rw [heq_iff_eq.mp (HEq.symm is_rel)]
        rw [sameWorld]
        exact all_pro_sat_right

/--
Lemma 1 (page 16)
A simple set of formulas X is satisfiable if and only if
it is not closed  and  for all ¬[A]R ∈ X also XA; ¬R is satisfiable.
-/
theorem Lemma1_simple_sat_iff_all_projections_sat {LR : TNode} :
    Simple LR → (Satisfiable LR
      ↔   ¬ Closed (LR.1 ∪ LR.2)
        ∧ ∀ F, f_in_TNode (~(□F)) LR → Satisfiable (projection (LR.1 ∪ LR.2) ∪ {~F})) :=
  by
    intro LR_is_simple
    constructor
    · -- left to right
      intro sat_LR
      unfold Satisfiable at *
      rcases sat_LR with ⟨W, M, w, w_sat_LR⟩
      constructor
      · -- show that X is not closed:
        by_contra hyp
        unfold Closed at hyp
        rcases hyp with bot_in_LR | f_and_notf_in_LR
        · exact w_sat_LR ⊥ bot_in_LR
        · rcases f_and_notf_in_LR with ⟨f, f_in_LR, notf_in_LR⟩
          let w_sat_f := w_sat_LR f f_in_LR
          let w_sat_notf := w_sat_LR (~f) notf_in_LR
          exact absurd w_sat_f w_sat_notf
      · -- show that for each ~[]R ∈ X the projection with ~R is satisfiable:
        intro R notboxr_in_LR
        let w_sat_notboxr := w_sat_LR (~(□R)) notboxr_in_LR
        unfold Evaluate at w_sat_notboxr
        simp only [Evaluate, not_forall, exists_prop] at w_sat_notboxr
        rcases w_sat_notboxr with ⟨v, w_rel_v, v_sat_notr⟩
        use W, M, v
        intro g
        simp only [Finset.mem_union, f_in_TNode, projectionUnion, Finset.union_singleton,
          Finset.mem_insert] at *
        rw [or_imp]
        constructor
        · intro g_is_notR
          rw [g_is_notR]
          exact v_sat_notr
        · intro boxg_in_LR
          repeat rw [proj] at boxg_in_LR
          rw [←Finset.mem_union]at boxg_in_LR
          specialize w_sat_LR (□g)
          aesop
    · -- right to left
      intro rhs
      rcases rhs with ⟨not_closed_LR, all_pro_sat⟩
      unfold Satisfiable at *
      -- Let's build a new Kripke model!
      let (L, R) := LR
      let β := {F : Formula | f_in_TNode (~(□F)) (L, R)}
      -- beware, using Axioms of Choice here!
      choose typeFor this_pro_sat using all_pro_sat
      choose modelFor this_pro_sat using this_pro_sat
      choose worldFor this_pro_sat using this_pro_sat
      -- define the collection:
      let collection : β → Σ W : Type, KripkeModel W × W :=
        by
        intro k
        rcases k with ⟨R, notboxr_in_LR⟩
        use typeFor R notboxr_in_LR, modelFor R notboxr_in_LR, worldFor R notboxr_in_LR
      let newVal c := f_in_TNode (Formula.atom_prop c) (L, R)
      let BigM := combinedModel collection newVal
      use Sum Unit (Σ k : β, (collection k).fst)
      use BigM.fst, BigM.snd
      -- apply Lemma, missing last argument "all_pro_sat"
      -- we need to use that X_is_simple (to restrict cases what phi can be)
      -- and that X is not closed (to ensure that it is locally consistent)
      apply combMo_sat_LR LR_is_simple not_closed_LR collection
      -- it remains to show that the new big model satisfies X
      <;> grind

theorem localRuleSoundness
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule (Lcond, Rcond) ress)
    (Δ : Finset Formula) :
    (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond) → ∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2) :=
  by
    intro satLR
    cases rule
    <;> simp only [Evaluate, Finset.mem_insert, Finset.mem_union, Finset.notMem_empty,
      Finset.union_assoc, Finset.union_empty, Finset.union_singleton, List.empty_eq,
      List.mem_map, List.not_mem_nil, exists_exists_and_eq_and, exists_false, false_and,
      false_or, forall_eq_or_imp, modelCanSemImplySet, or_false] at *
    <;> ( first
        | ( rename_i siderule
            cases siderule
            <;> simp only [instBotFormula, Finset.mem_insert, Finset.mem_singleton, List.empty_eq,
              List.not_mem_nil, false_and, exists_const] at *
            case bot => specialize satLR ⊥; tauto
            case not φ =>
              have : Evaluate (M, w) (~φ) := by
                specialize satLR (~φ); tauto
              aesop
            case neg φ =>
              have : Evaluate (M, w) (~~φ) := by
                specialize satLR (~~φ); tauto
              aesop
            case con φ ψ =>
              have : Evaluate (M, w) (φ⋀ψ) := by
                specialize satLR (φ⋀ψ); tauto
              aesop
            case ncon φ ψ =>
              have : Evaluate (M, w) (~(φ⋀ψ)) := by
                specialize satLR (~(φ⋀ψ)); tauto
              cases Classical.em (Evaluate (M, w) φ)
              <;> aesop)
        | aesop)

theorem ruleImpliesChildSat
    {C : List TNode}
    {LR : TNode}
    {ruleApp : LocalRuleApp LR C} :
    Satisfiable LR → ∃c ∈ C, Satisfiable c :=
  by
    intro satLR
    let (L, R) := LR
    rcases satLR with ⟨W, M, w, satM⟩
    rcases ruleApp with ⟨ress, Lcond, Rcond, lrule, preproofL, preproofR⟩
    let Δ := (L ∪ R) \ (Lcond ∪ Rcond)
    have : ∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2) :=
      localRuleSoundness M w lrule Δ (by simp (config := {zetaDelta := true}); aesop)
    aesop

theorem oneSidedRule_implies_child_sat_L
  {ruleApp : LocalRuleApp (L, R) C}
  (def_ruleA : ruleApp =
    (@LocalRuleApp.mk L R C (List.map (fun res => (res, ∅)) _) _ _ rule hC preproof))
  (rule_is_left : rule = LocalRule.oneSidedL orule)
  : Satisfiable (L ∪ X) → ∃c ∈ C.attach, Satisfiable (c.1.1 ∪ X) :=
  by
    intro hyp
    rcases hyp with ⟨W, M, w, satM⟩
    rcases ruleApp with ⟨ress, Lcond, Rcond, lrule, preproofL, preproofR⟩
    have : ∃res ∈ ress, (M, w) ⊨ (X ∪ res.1 ∪ res.2) :=
      localRuleSoundness M w lrule X (by aesop)
    aesop

theorem oneSidedRule_implies_child_sat_R
  {ruleApp : LocalRuleApp (L, R) C}
  (def_ruleA : ruleApp =
    (@LocalRuleApp.mk L R C (List.map (fun res => (∅, res)) _) _ _ rule hC preproof))
  (rule_is_right : rule = LocalRule.oneSidedR orule)
  : Satisfiable (R ∪ X) → ∃c ∈ C.attach, Satisfiable (c.1.2 ∪ X) :=
    by
      intro hyp
      rcases hyp with ⟨W, M, w, satM⟩
      rcases ruleApp with ⟨ress, Lcond, Rcond, lrule, preproofL, preproofR⟩
      have : ∃res ∈ ress, (M, w) ⊨ (X ∪ res.1 ∪ res.2) :=
        localRuleSoundness M w lrule X (by aesop)
      aesop

/--
The critical rule is sound and preserves satisfiability "downwards".
NOTE: This is stronger than Lemma 1, but we do not need.
-/
theorem atmSoundness {LR : TNode} {f} (not_box_f_in_LR : f_in_TNode (~(□f)) LR) :
    Satisfiable LR → Satisfiable (projection (LR.1 ∪ LR.2) ∪ {~f}) :=
  by
  intro satLR
  unfold Satisfiable at satLR
  rcases satLR with ⟨W, M, w, w_sat_LR⟩
  refine ⟨W, ?_⟩
  simp only [projectionUnion, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
    forall_eq_or_imp, Evaluate]
  -- get the other reachable world:
  let w_sat_not_box_f := w_sat_LR (~f.box) not_box_f_in_LR
  unfold Evaluate at w_sat_not_box_f
  simp only [Evaluate, not_forall, exists_prop] at w_sat_not_box_f
  rcases w_sat_not_box_f with ⟨v, w_rel_v, v_not_sat_f⟩
  -- show that the projection is satisfiable:
  use M, v
  constructor
  · exact v_not_sat_f
  intro phi phi_in_proj
  rw [proj] at phi_in_proj
  cases phi_in_proj
  · specialize w_sat_LR phi.box (by simp only [Finset.mem_union]; left; assumption)
    simp only [Evaluate] at w_sat_LR
    exact w_sat_LR v w_rel_v
  case inr hyp =>
    rw [proj] at hyp
    specialize w_sat_LR phi.box (by simp only [Finset.mem_union]; right; assumption)
    exact w_sat_LR v w_rel_v

theorem localTableauAndEndNodesUnsatThenNotSat (LR : TNode) {ltLR : LocalTableau LR} :
    (∀Y, Y ∈ endNodesOf ⟨LR, ltLR⟩ → ¬Satisfiable Y) → ¬Satisfiable LR :=
  by
  intro endsOfLRnotSat
  cases ltLR
  case fromRule C next ruleA =>
    by_contra satLR
    have someChildSat : ∃c ∈ C, Satisfiable c :=
      @ruleImpliesChildSat C LR ruleA satLR
    rcases ruleA with ⟨ress, Lcond, Rcond, lrule, preproofL, preproofR⟩
    rename_i L R hC
    have prepf : Lcond ⊆ L ∧ Rcond ⊆ R := And.intro preproofL preproofR
    rcases someChildSat with ⟨c, c_sat⟩
    set ltc := next c c_sat.left
    have endNodesInclusion :
      ∀ Z ∈ endNodesOf ⟨c, ltc⟩,
        Z ∈ endNodesOf ⟨(L,R), LocalTableau.fromRule
          (@LocalRuleApp.mk _ _ C ress Lcond Rcond lrule hC prepf) next⟩ :=
      by
        simp only [lrEndNodes, List.mem_flatten, List.mem_map, List.mem_attach, true_and,
          Subtype.exists, ↓existsAndEq]
        intro Z Z_endOF_c
        use c
        tauto
    have endsOfcnotSat : ∀Z1, Z1 ∈ endNodesOf ⟨c, ltc⟩ → ¬Satisfiable Z1 :=
      by intro Z1 Z1_is_endOf_c; apply endsOfLRnotSat Z1 (endNodesInclusion Z1 Z1_is_endOf_c)
    have : (∀Z, Z ∈ endNodesOf ⟨c , ltc⟩ → ¬Satisfiable Z) → ¬Satisfiable c :=
      by
        have := localRuleAppDecreasesLength
          (@LocalRuleApp.mk _ _ C ress Lcond Rcond lrule hC prepf) c c_sat.left -- for termination
        apply localTableauAndEndNodesUnsatThenNotSat c
    exact (this endsOfcnotSat) (c_sat.right)
  case fromSimple hSimple =>
    apply endsOfLRnotSat
    simp
termination_by
  _ => lengthOfTNode LR

theorem tableauThenNotSat : ∀ X, ClosedTableau X → ¬Satisfiable X :=
  by
  intro X t
  induction t
  case loc LR appTab _ IH =>
    apply localTableauAndEndNodesUnsatThenNotSat LR
    · intro Z ZisEndOfY
      exact IH Z ZisEndOfY
  case atmL LR φ notBoxPhiInY Y_is_simple ltProYnPhi notSatProj =>
    let (L,R) := LR
    rw [Lemma1_simple_sat_iff_all_projections_sat Y_is_simple]
    simp only [f_in_TNode, Finset.mem_union, union_singleton_is_insert, not_and, not_forall,
      exists_prop]
    intro nClo
    use φ
    constructor
    · tauto
    · convert notSatProj
      simp only [diamondProjectTNode, setHasSat, Finset.mem_union, Finset.mem_insert,
        forall_eq_or_imp, Evaluate, TNodeHasSat, union_singleton_is_insert]
      constructor
      · rintro ⟨W,M,w,claim⟩
        use W, M, w
        intro f f_in
        aesop
      · rintro ⟨W,M,w,claim⟩
        use W, M, w
        have := claim (~φ)
        aesop
  case atmR LR φ notBoxPhiInY Y_is_simple ltProYnPhi notSatProj =>
    let (L,R) := LR
    rw [Lemma1_simple_sat_iff_all_projections_sat Y_is_simple]
    simp only [f_in_TNode, Finset.mem_union, union_singleton_is_insert, not_and, not_forall,
      exists_prop]
    intro _
    use φ
    constructor
    · tauto
    · convert notSatProj
      simp only [diamondProjectTNode, setHasSat, Finset.mem_union, Finset.mem_insert,
        forall_eq_or_imp, Evaluate, TNodeHasSat, union_singleton_is_insert]
      constructor <;>
      ( rintro ⟨W,M,w,claim⟩
        use W, M, w)
      · intro f f_in
        have := claim.2 (~φ)
        aesop
      · have := claim (~φ)
        aesop

/-- Theorem 2, page 30 -/
theorem correctness : ∀LR : TNode, Satisfiable LR → Consistent LR :=
  by
    intro LR
    contrapose
    unfold Consistent
    unfold Inconsistent
    simp only [not_nonempty_iff, not_isEmpty_iff, Nonempty.forall]
    intro hyp
    apply tableauThenNotSat LR hyp

theorem soundTableau : ∀φ, Provable φ → ¬Satisfiable ({~φ} : Finset Formula) :=
  by
    intro phi prov
    rcases prov with ⟨tabl⟩
    exact tableauThenNotSat ({~phi}, ∅) tabl

theorem soundness : ∀φ, Provable φ → Tautology φ :=
  by
    intro φ prov
    apply notsatisfnotThenTaut
    rw [← singletonSat_iff_sat]
    apply soundTableau
    exact prov
