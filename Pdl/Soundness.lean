import Pdl.Tableau
import Pdl.LocalTableau
import Pdl.Semantics

open Classical

open HasSat


-- Combine a collection of pointed models with one new world using the given valuation.
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
      cases' oldWorld with R w
      exact (collection R).snd.fst.val w
  · -- defining relations:
    intro prog worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl =>
      exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld =>
      exact HEq oldWorld.snd (collection oldWorld.fst).snd.snd -- conect new world to given points.
    case inr.inl => exact False -- no connection from models to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      cases' oldWorldOne with kOne wOne
      cases' oldWorldTwo with kTwo wTwo
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.fst.Rel prog wOne wTwo
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()

theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) f ↔
        evaluate (collection R).snd.fst oldWorld f :=
    by
    intro mF mR moW
    apply @Formula.rec
      (λφ => ∀ (R : β) (oldWorld : (collection R).fst),
      evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) φ ↔
        evaluate (collection R).snd.fst oldWorld φ)
       (λπ => True)
       (by -- Case Bottom
          intro R oW
          aesop
        )
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (sorry)
       (mF)

/-
theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) f ↔
        evaluate (collection R).snd.fst oldWorld f :=
    by
    intro f
    cases f <;>
    intro R oldWorld
    case bottom => aesop
    case atom_prop c =>
      unfold combinedModel
      simp
    case neg f =>
      unfold evaluate
      have IH := combMo_preserves_truth_at_oldWOrld collection newVal f R oldWorld
      tauto
    case and f g =>
      unfold evaluate
      have IH_f := combMo_preserves_truth_at_oldWOrld collection newVal f R oldWorld
      have IH_g := combMo_preserves_truth_at_oldWOrld collection newVal g R oldWorld
      tauto
    case box f =>
      unfold evaluate
      constructor
      · intro true_in_combo
        intro otherWorld rel_in_old_model
        have IH_f := combMo_preserves_truth_at_oldWOrld collection newVal f
        specialize IH_f R otherWorld
        rw [←IH_f]
        specialize true_in_combo (Sum.inr ⟨R, otherWorld⟩)
        apply true_in_combo
        unfold combinedModel
        rename_i a
        cases a <;> simp at *     -- maybe try to prove separate relate / program thms?
        case atom_prog a => aesop
        case sequence a₁ a₂ =>
          rcases rel_in_old_model with ⟨w, hw⟩
          -- use w
          sorry
        case union a₁ a₂ =>
          cases' rel_in_old_model with rela₁ rela₂
          · simp [rela₁] at *
            sorry
          · sorry
        case star a₁ =>
          sorry
        case test p =>
          cases' rel_in_old_model with left right
          simp [left] at *
          unfold evaluate at *
          sorry
      · intro true_in_old
        simp
        constructor
        · intro newWorld
          unfold combinedModel
          intro hyp
          unfold evaluate at *
          unfold relate at *
          sorry
        -- the new world is never reachable, trivial case
        · intro otherR otherWorld
          intro rel_in_new_model
          have IH_f := combMo_preserves_truth_at_oldWOrld collection newVal f
          specialize IH_f otherR otherWorld
          unfold combinedModel at rel_in_new_model
          have sameR : R = otherR := by sorry -- aesop
          subst sameR
          rw [IH_f]
          apply true_in_old
          -- remains to show that related in old model
          simp_all
          sorry
          -- exact rel_in_new_model
-/

/-
-- The combined model for X satisfies X.
theorem combMo_sat_LR {L R : Finset Formula} {β : Set Formula}
    {beta_def : β = {F : Formula | f_in_TNode (~F.box) (L, R)}} (simple_LR : Simple (L, R)) (not_closed_LR : ¬Closed (L ∪ R))
    (collection : β → Σ W : Type, KripkeModel W × W)
    (all_pro_sat :
      ∀ F : β,
        ∀ f, (f ∈ (projection (L ∪ R) ∪ {~F})) → Evaluate ((collection F).snd.fst, (collection F).snd.snd) f) :
    ∀ f, f_in_TNode f (L, R)
      → Evaluate
        ((combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).fst,
          (combinedModel collection fun c => Formula.atom_prop c ∈ (L ∪ R)).snd)
        f :=
  by
    intro f f_in_LR
    unfold Simple SimpleSet at simple_LR
    simp at simple_LR
    simp at f_in_LR
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
      -- subcases :
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
          simp at *
          exact all_pro_sat
        ·-- show that worlds are related in combined model (def above, case 2)
          unfold combinedModel
          simp
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
        simp at all_pro_sat
        rw [or_imp] at all_pro_sat
        cases' all_pro_sat with _ all_pro_sat_right
        rw [←proj] at f_in_LR
        simp at *
        specialize all_pro_sat_right f_in_LR
        have sameWorld : otherWorld.snd = (collection otherWorld.fst).snd.snd := by
          rw [heq_iff_eq.mp (HEq.symm is_rel)]
        rw [sameWorld]
        exact all_pro_sat_right


-- Lemma 1 (page 16)
-- A simple set of formulas X is satisfiable if and only if
-- it is not closed  and  for all ¬[A]R ∈ X also XA; ¬R is satisfiable.
theorem Lemma1_simple_sat_iff_all_projections_sat {LR : TNode} :
    Simple LR → (Satisfiable LR ↔ ¬Closed (LR.1 ∪ LR.2) ∧ ∀ F, f_in_TNode (~(□F)) LR → Satisfiable (projection (LR.1 ∪ LR.2) ∪ {~F})) :=
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
        cases' hyp with bot_in_LR f_and_notf_in_LR
        · exact w_sat_LR ⊥ bot_in_LR
        · rcases f_and_notf_in_LR with ⟨f, f_in_LR, notf_in_LR⟩
          let w_sat_f := w_sat_LR f f_in_LR
          let w_sat_notf := w_sat_LR (~f) notf_in_LR
          exact absurd w_sat_f w_sat_notf
      · -- show that for each ~[]R ∈ X the projection with ~R is satisfiable:
        intro R notboxr_in_LR
        let w_sat_notboxr := w_sat_LR (~(□R)) notboxr_in_LR
        unfold Evaluate at w_sat_notboxr
        simp at w_sat_notboxr
        rcases w_sat_notboxr with ⟨v, w_rel_v, v_sat_notr⟩
        use W, M, v
        intro g
        simp at *
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
      cases' rhs with not_closed_LR all_pro_sat
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
        cases' k with R notboxr_in_LR
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
      intro R f f_inpro_or_notr
      cases' R with R notrbox_in_LR
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Subtype.coe_mk] at *
      specialize this_pro_sat R notrbox_in_LR
      cases' f_inpro_or_notr with f_inpro f_is_notboxR
      · -- if f is in the projection
        specialize this_pro_sat f
        rw [or_imp] at this_pro_sat
        cases' this_pro_sat with this_pro_sat_l this_pro_sat_r
        exact this_pro_sat_l f_inpro
      · -- case where f is ~[]R
        cases f_is_notboxR
        case refl =>
          specialize this_pro_sat (~R)
          rw [or_imp] at this_pro_sat
          cases' this_pro_sat with this_pro_sat_l this_pro_sat_r
          tauto
      simp

-/

theorem localRuleSoundnessNoneLoaded
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule (Lcond, Rcond, Option.none) ress)
    (Δ : List Formula) :
    (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond) → ∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2.1) :=
  by
    intro satLR
    cases rule
    <;> simp at *
    case oneSidedL _ rule =>
      cases rule
      <;> simp at *
      case bot => specialize satLR ⊥; tauto
      case not φ =>
        have : evaluate M w (~φ) := by
          specialize satLR (~φ); tauto
        aesop
      case neg φ =>
        have : evaluate M w (~~φ) := by
          specialize satLR (~~φ); tauto
        aesop
      case con φ ψ =>
        have : evaluate M w (φ⋀ψ) := by
          specialize satLR (φ⋀ψ); tauto
        aesop
      case nCo φ ψ =>
        have : evaluate M w (~(φ⋀ψ)) := by
          specialize satLR (~(φ⋀ψ)); tauto
        cases Classical.em (evaluate M w φ) <;> aesop
      case nTe φ ψ =>
        have : evaluate M w (~⌈?'φ⌉ψ) := by
          specialize satLR (~⌈?'φ⌉ψ); tauto
        aesop
      case nSe a b f =>
        have : evaluate M w (~⌈a;'b⌉f) := by
          specialize satLR (~⌈a;'b⌉f); tauto
        aesop
      case uni a b f =>
        have : evaluate M w (⌈a⋓b⌉f) := by
          specialize satLR (⌈a⋓b⌉f); tauto
        aesop
      case seq a b f =>
        have : evaluate M w (⌈a;'b⌉f) := by
          specialize satLR (⌈a;'b⌉f); tauto
        aesop
      case tes f g =>
        have : evaluate M w (⌈?'f⌉g) := by
          specialize satLR (⌈?'f⌉g); tauto
        unfold evaluate at this
        unfold relate at this
        simp at *
        apply Or.inl
        intro f₁ hf₁
        specialize satLR f₁
        cases' hf₁ with in_delta neg_f
        · aesop
        · rw [neg_f]
          simp [evaluate]
          sorry
          -- intro f₂ hf₂
          -- cases' hf₂ with in_delta is_g
          -- · aesop
          -- · sorry

          -- simp [is_g] at *
          -- apply this
          -- specialize satLR f
          -- apply satLR
      case nUn a b f =>
        have : evaluate M w (~⌈a⋓b⌉f) := by
          specialize satLR (~⌈a⋓b⌉f); tauto
        aesop
      case sta a f =>
        have : evaluate M w (⌈∗a⌉f) := by
          specialize satLR (⌈∗a⌉f); tauto
        sorry
      case nSt a f => sorry
    case oneSidedR => sorry
    case LRnegL => sorry
    case LRnegR => sorry
