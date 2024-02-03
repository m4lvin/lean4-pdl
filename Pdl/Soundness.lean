import Pdl.Tableau
import Pdl.LocalTableau
import Pdl.Semantics
import Pdl.Discon

import Mathlib.Tactic.Ring

open Classical

open HasSat


-- Combine a collection of pointed models with one new world using the given valuation.
-- TODO: rewrite to term mode?
def combinedModel {β : Type} (collection : β → Σ W : Type, Char × KripkeModel W × W)
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
      exact (collection R).snd.snd.fst.val w
  · -- defining relations:
    intro prog worldOne worldTwo
    cases worldOne <;> cases worldTwo -- four cases about two new or old worlds
    case inl.inl =>
      exact False -- no reflexive loop at the new world.
    case inl.inr newWorld oldWorld => -- connect new world to given points.
      exact (HEq oldWorld.snd (collection oldWorld.fst).snd.snd) ∧ (HEq prog (collection oldWorld.fst).snd.fst)
    case inr.inl => exact False -- no connection from old worlds to new world
    case inr.inr oldWorldOne oldWorldTwo =>
      -- connect two old worlds iff they are from the same model and were connected there already:
      cases' oldWorldOne with kOne wOne
      cases' oldWorldTwo with kTwo wTwo
      have help : kOne = kTwo → Prop := by
        intro same
        have sameCol : collection kOne = collection kTwo := by rw [← same]
        rw [← sameCol] at wTwo
        exact (collection kOne).snd.snd.fst.Rel prog wOne wTwo
      exact dite (kOne = kTwo) (fun same => help same) fun _ => False
  · -- point at the new world:
    left
    exact ()


theorem combMo_preserves_truth_at_oldWOrld {β : Type}
    (collection : β → Σ W : Type, Char × KripkeModel W × W) (newVal : Char → Prop) :
    ∀ (f : Formula) (R : β) (oldWorld : (collection R).fst),
      evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) f ↔
        evaluate (collection R).snd.snd.fst oldWorld f :=
    by
    intro mF mR moW
    apply @Formula.rec
      (λφ => ∀ (R : β) (oldWorld : (collection R).fst),  -- Formula IH
        evaluate (combinedModel collection newVal).fst (Sum.inr ⟨R, oldWorld⟩) φ ↔
          evaluate (collection R).snd.snd.fst oldWorld φ)
      -- Program IH 1: relations within models are preserved
      (λπ => (∀ (R : β) (oldWorld₁ oldWorld₂ : (collection R).fst),
        relate (combinedModel collection newVal).fst π (Sum.inr ⟨R, oldWorld₁⟩) (Sum.inr ⟨R, oldWorld₂⟩) ↔
          relate (collection R).snd.snd.fst π oldWorld₁ oldWorld₂)
            -- Program IH 2: if old worlds are from different models they are not related
            ∧ (∀ (R₁ R₂ : β) (oldWorld₁ : (collection R₁).fst) (oldWorld₂ : (collection R₂).fst),
              R₁ ≠ R₂ → ¬(relate (combinedModel collection newVal).fst π (Sum.inr ⟨R₁, oldWorld₁⟩) (Sum.inr ⟨R₂, oldWorld₂⟩)))
              -- Program IH 3: no old world can see the new world
              ∧ (∀ (R : β) (oldWorld : (collection R).fst),
                ¬(relate (combinedModel collection newVal).fst π (Sum.inr ⟨R, oldWorld⟩) (Sum.inl Unit.unit))))
      (by tauto)      -- case bottom
      (by aesop)      -- case atom_prop
      (by aesop)      -- case neg
      (by aesop)      -- case and
      ( by            -- case box
          intro α f IH_a IH_f R oldWorld
          constructor
          · aesop
          · intro true_in_old
            unfold evaluate at true_in_old
            simp
            constructor
            · intro newWorld  -- new world
              intro old_rel_new
              absurd old_rel_new
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · intro otherR otherWorld  -- old world
              intro rel_in_new_model
              specialize IH_f otherR otherWorld
              simp_all
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              specialize sameR R otherR oldWorld otherWorld
              simp_all
              subst sameR
              aesop
      )
      ( by          -- case atom_prog
          intro a
          constructor
          · intro R oldWorld₁ oldWorld₂    -- first half of Program IH
            constructor <;>
            ( intro new_rel
              unfold relate at *
              unfold KripkeModel.Rel at *
              unfold combinedModel at *
              aesop
            )
          · unfold combinedModel at *; aesop   -- second half of Program IH
      )
      ( by          -- case sequence
          intro a b IH_a IH_b
          constructor
          · intro R oldWorld₁ oldWorld₂          -- first half of Program IH
            constructor
            · intro new_rel
              unfold relate at new_rel
              rcases new_rel with ⟨u, a_rel_u, u_rel_b⟩
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              cases' u with u_new u_old
              · absurd a_rel_u
                apply noNewL
              · rcases u_old with ⟨otherR, otherWorld⟩ -- old world
                specialize sameR R otherR oldWorld₁ otherWorld
                simp_all
                subst sameR
                aesop
            · intro old_rel
              unfold relate at old_rel
              unfold relate
              rcases old_rel with ⟨u, a_rel_u, u_rel_b⟩
              use (Sum.inr ⟨R, u⟩)
              aesop
          constructor
          · intro R₁ R₂ oldWorld₁ oldWorld₂ hneq hrel     -- second half of Program IH
            unfold relate at hrel
            rcases hrel with ⟨u, a_rel_u, _⟩
            rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
            cases' u with u_new u_old
            · absurd a_rel_u
              apply noNewL
            · rcases u_old with ⟨otherR, otherWorld⟩ -- old world
              specialize sameR R₁ otherR oldWorld₁ otherWorld
              simp_all
          · intro R oldWorld
            unfold relate
            rintro ⟨u, a_rel_to_u, b_rel_u_to⟩
            cases u
            · absurd a_rel_to_u
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · absurd b_rel_u_to
              rcases IH_b with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
      )
      (by aesop)       -- case union
      (by              -- case star
        intro a IH_a
        constructor
        · intro R oldWorld₁ oldWorld₂                  -- first half of Program IH
          have star_preserved : ∀ (w v : (collection R).fst),
            Relation.ReflTransGen (relate (combinedModel collection newVal).fst a)
              (Sum.inr ⟨R, w⟩) (Sum.inr ⟨R, v⟩) ↔ Relation.ReflTransGen (relate (collection R).snd.snd.fst a) w v :=
            by
            intro w v
            rw [starIffFinitelyManySteps]
            rw [starIffFinitelyManySteps]
            -- alternatively, use @Relation.ReflTransGen.head_induction_on here?
            sorry
          constructor <;> aesop
        constructor
        · intro R₁ R₂ oldWorld₁ oldWorld₂ hneq        -- second half of Program IH
          unfold relate
          rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
          specialize sameR R₁ R₂ oldWorld₁ oldWorld₂ hneq
          sorry -- again @Relation.ReflTransGen.head_induction_on
        · intro R oldWorld
          unfold relate
          intro star_rel
          cases starCases star_rel
          case inl hyp => simp at hyp
          case inr hyp =>
            rcases hyp.2 with ⟨u, _neq_u, a_rel_to_u, b_rel_u_to⟩
            cases u
            · absurd a_rel_to_u
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              apply noNewL
            · absurd b_rel_u_to
              rcases IH_a with ⟨IH_rel, sameR, noNewL⟩
              sorry -- apply noNewL -- not working, need induction?
      )
      (by aesop)       -- case test
      (mF)


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


-- I wanted to do a variation of the bml localRuleSoundness using the
-- soundness rules in Pdl.LocalTableau
-- But only just found out that LocalRule is now defined on TNodes
-- whereas it was defined on Subpairs in the bml version
-- so either needs a rewrite or types maybe need to be changed back
theorem localRuleSoundness
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule (L, R, O) ress) -- used to be Lcond, Rcond (, Ocond)
    (Δ : List Formula) :
    (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond) → ∃res ∈ ress, (M, w) ⊨ res := -- used to be (M, w) ⊨ Δ ∪ res.1 ∪ res.2
  by sorry

-- alternative ruleImpliesChildSat using localRuleTruth from Semantics
theorem ruleImpliesChildSat
    {C : List TNode}
    {LR : TNode}
    (M : KripkeModel W)
    (w : W)
    (ruleApp : LocalRuleApp (LR.L, LR.R, LR.O) C) :
    (M, w) ⊨ LR → ∃c ∈ C, (M, w) ⊨ c :=
  by
    intro satLR
    let (L, R, O) := LR
    rcases ruleApp with ⟨O, Lcond, Rcond, Ocond, rule, preproofL, preproofR⟩
    cases rule
    case oneSidedL ress rule hC =>    -- the most of this should be moved to localRuleSoundness above
      have condiscon : Con Lcond ≡ discon ress := oneSidedLocalRuleTruth rule
      have satCon: (M, w) ⊨ Con Lcond := by
        have satLcond : ∀ f ∈ Lcond, evaluate M w f := subsetSat (by aesop) preproofL
        rw [←conEval] at satLcond
        tauto
      have satDis : (M, w) ⊨ discon ress :=
        equivSat (Con Lcond) (discon ress) condiscon satCon
      have evalDis : evaluate M w (discon ress) := by tauto
      have : ∃ res ∈ ress, ∀ f ∈ res, evaluate M w f := by
        rw [disconEval ress] at evalDis
        assumption
      rcases this with ⟨res, in_ress, eval_res⟩
      -- in bml aesop could solve this :(
      have some_child : ∃ c ∈ C, c = (L \ Lcond ∪ res, R, O) := by sorry
      rcases some_child with ⟨c, hc⟩
      use c
      constructor
      · exact hc.left
      · rw [hc.right]
        sorry -- should be easy
    case oneSidedR ress rule hC => sorry  -- the exact same pf as above (most of it should be done in localRuleSoundness)
    case LRnegL => sorry
    case LRnegR => sorry
    case loadedL => sorry -- here use loadedRuleTruth from Semantics
    case loadedR => sorry




-- Issue: deterministic timeout when I run everything together / use tactic combinators
-- like I did in the bml file
-- (oneSidedL/oneSidedR are completely copy-pasted, so are LRnegL/LRnegR)
-- even though every case by itself doesn't cause any problems
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
    case oneSidedL _ rule => sorry
      /-
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
        have eval_test : evaluate M w (⌈?'f⌉g) := by
          specialize satLR (⌈?'f⌉g); tauto
        cases Classical.em (evaluate M w f) <;> aesop
      case nUn a b f =>
        have : evaluate M w (~⌈a⋓b⌉f) := by
          specialize satLR (~⌈a⋓b⌉f); tauto
        aesop
      case sta a f =>
        have : evaluate M w (⌈∗a⌉f) := by
          specialize satLR (⌈∗a⌉f); tauto
        simp at this
        -- dagtableau stuff which I don't understand
        sorry
      case nSt a f =>
        have : evaluate M w (~⌈∗a⌉f) := by
          specialize satLR (~⌈∗a⌉f); tauto
        simp_all
        rcases this with ⟨v, hv⟩
        cases' Classical.em (evaluate M w f) with evalf nevalf
        · apply Or.inr
          simp [dagEndNodes]
          -- dagtableau stuff which I don't understand
          sorry
        · aesop
      -/
    case oneSidedR => sorry
    case LRnegL φ =>
      have : evaluate M w φ ∧ evaluate M w (~φ) := by
        constructor
        · specialize satLR φ; aesop
        · specialize satLR (~φ); aesop
      aesop
    case LRnegR φ =>
      have : evaluate M w φ ∧ evaluate M w (~φ) := by
        constructor
        · specialize satLR φ; aesop
        · specialize satLR (~φ); aesop
      aesop

-- this is all redundant if you can use loadRuleTruth from LocalTableau
theorem localRuleSoundnessLoadedL
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule (Lcond, Rcond, some (Sum.inl (~'χ))) ress)
    (Δ : List Formula) :
    (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond ∪ [~ unload χ]) → ∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2.1) :=
  by
    intro satLR
    cases rule
    simp [loadRuleTruth] at *
    case loadedL ress lrule =>
      cases lrule
      case nUn a b χ =>
        let unl_χ := ~ unload χ
        specialize satLR unl_χ
        simp at *
        sorry
      case nUn' => sorry
      case nSe => sorry
      case nSe' => sorry
      case nSt => sorry
      case nSt' => sorry
      case nTe => sorry
      case nTe' => sorry


theorem localRuleSoundnessLoadedR
    (M : KripkeModel W)
    (w : W)
    (rule : LocalRule (Lcond, Rcond, some (Sum.inr (~'χ))) ress)
    (Δ : List Formula) :
    (M, w) ⊨ (Δ ∪ Lcond ∪ Rcond ∪ [~ unload χ]) → ∃res ∈ ress, (M, w) ⊨ (Δ ∪ res.1 ∪ res.2.1) :=
  by
    intro satLR
    cases rule
    simp at *
    case loadedR ress lrule =>
      let unl_χ := ~ unload χ
      specialize satLR unl_χ
      simp at *
      cases lrule
      case nUn => sorry
      case nUn' => sorry
      case nSe => sorry
      case nSe' => sorry
      case nSt => sorry
      case nSt' => sorry
      case nTe => sorry
      case nTe' => sorry

-- * Tools for saying that different kinds of formulas are in a TNode

@[simp]
instance : Membership Formula TNode :=
  ⟨fun φ X => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula_in_TNode := fun nlf (X : TNode) => X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

@[simp]
instance : Membership NegLoadFormula TNode := ⟨NegLoadFormula_in_TNode⟩

def AnyFormula := Sum Formula LoadFormula

inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula

local notation "~''" φ:arg => AnyNegFormula.neg φ

@[simp]
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (λ ⟨M,w⟩ af => match af with
   | ⟨Sum.inl f⟩ => evaluate M w f
   | ⟨Sum.inr f⟩ => evaluate M w (unload f)
   )

@[simp]
def anyNegLoad : Program → AnyFormula → NegLoadFormula
| α, Sum.inl φ => ~'⌊α⌋φ
| α, Sum.inr χ => ~'⌊α⌋χ

local notation "~'⌊" α "⌋" χ => anyNegLoad α χ

-- set_option trace.Meta.synthInstance true -- turn this on to debug ∈ below.
@[simp]
def AnyNegFormula_in_TNode := fun (anf : AnyNegFormula) (X : TNode) => match anf with
| ⟨Sum.inl φ⟩ => (~φ) ∈ X
| ⟨Sum.inr χ⟩ => NegLoadFormula_in_TNode (~'χ) X -- FIXME: ∈ not working here

@[simp]
instance : Membership AnyNegFormula TNode := ⟨AnyNegFormula_in_TNode⟩

-- * Helper functions, to be moved to (Local)Tableau.lean

-- TODO delete this, if computable version works
noncomputable def endNodeIsEndNodeOfChildNonComp (lrA)
  (E_in: E ∈ endNodesOf ⟨X, LocalTableau.byLocalRule lrA subTabs⟩) :
  @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf ⟨x, subTabs x h⟩) := by
  simp [endNodesOf] at E_in
  choose l h E_in using E_in
  choose c c_in l_eq using h
  subst l_eq
  use c
  use c_in

-- TODO: move this to LocalTableau?
def endNode_to_endNodeOfChild
    {E X : TNode}
    {lTab}
    (E_in: E ∈ endNodesOf ⟨X, lTab⟩)
    (lrA : LocalRuleApp X C)
    (h := lTab = LocalTableau.byLocalRule lrA subTabs)
    : @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf ⟨x, subTabs x h⟩) :=
  by
  cases lTab

  all_goals sorry

-- TODO: move this to LocalTableau.
theorem endNodeOfChild_to_endNode
    {X Y: TNode}
    {ltX}
    {C : List TNode}
    (lrA : LocalRuleApp X C)
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA subTabs)
    (Y_in : Y ∈ C)
    {Z : TNode}
    (Z_in: Z ∈ endNodesOf ⟨Y, subTabs Y Y_in⟩)
    : Z ∈ endNodesOf ⟨X, ltX⟩ :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp
    use endNodesOf ⟨Y,subTabs Y Y_in⟩
    constructor
    · use Y, Y_in
    · exact Z_in
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp
    use endNodesOf ⟨Y,subTabs Y Y_in⟩
    constructor
    · use Y, Y_in
    · rw [h']
      exact Z_in

-- * Navigating through tableaux

-- Given our representation of condition 6a, now we want to prove MB Lemma 7.
--
-- To represent both the whole Tableau and a specific node in it we use
-- a "List TNode" path to say "go to this child, then to this child, etc."
-- These paths:
-- - can go through/across multiple LocalTableau, like LHistories
--   and unlike the Paths used in the Complteness Proof
-- - are over the relation that includes back-loops.

-- Given:
-- - a local tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path or a local end node and the remaining path
-- TOOD: rewrite with more match cases in term mode without "by"?
def tabInLocalAt (ltX : LocalTableau X) : List TNode → Option (TNode ⊕ (Subtype (fun Y => Y ∈ endNodesOf ⟨X, ltX⟩) × List TNode))
| [] => some (Sum.inl X) -- we have reached the destination
| (Y::rest) => by
    cases ltX
    case byLocalRule B lnext lrApp =>
      refine if Y_in : Y ∈ B then ?_ else ?_
      · cases tabInLocalAt (lnext Y Y_in) rest -- make a recursive call!
        case none => exact none -- not found.
        case some foo =>
          cases foo
          case inl Z =>
            exact some (Sum.inl Z) -- found it!
          case inr Z_ =>
            rcases Z_ with ⟨⟨Z,Z_in⟩, remainder⟩
            apply some
            apply Sum.inr
            refine ⟨⟨Z, ?_⟩, ?_⟩
            · apply endNodeOfChild_to_endNode lrApp lnext rfl Y_in Z_in
            · exact remainder
      · exact none -- cannot follow path
    case sim X_simp =>
      apply some
      apply Sum.inr
      constructor
      · use X
        rw [endNodesOf, List.mem_singleton]
      · exact Y::rest -- Problem: This case means "reminder" may be of same length still.

-- Given:
-- - a tableau (not necessarily a root)
-- - a path to be walked
-- return if succeeds: the TNode at the end of the path
def tabInAt : (Σ X HistX, ClosedTableau HistX X) → List TNode → Option TNode
| ⟨X, hX, tab⟩, [] => some X -- we have reached the destination
| ⟨X, hX, tab⟩, (Y::rest) => by
      cases tab
      case loc ltX next =>
        cases tabInLocalAt ltX (Y::rest)
        case none => exact none
        case some lt_res =>
          cases lt_res
          case inl Z => exact some Z -- reached end of path inside the local tableau.
          case inr Y_end_remainder =>
            rcases Y_end_remainder with ⟨⟨Y, Y_in⟩, remainder⟩
            have : remainder.length < (Y::rest).length := sorry -- needed for termination, may need to add this in tabInLocalAt
            exact tabInAt ⟨Y, record hX X, next Y Y_in⟩ remainder
      case mrkL =>
        -- apply tabInAt ?
        sorry
      case rep isRep =>
        exact none -- fail, we cannot go to Y (and should be using Loopy from below!)
      all_goals sorry
termination_by
   tabInAt Xhtab toWalk => toWalk.length

/-

PROBLEM: returning only TNodes instead of ClosedTableau is not enough to implement the loopy version!

-- Given:
-- - the root of a tableau
-- - a path already walked - needed to go back up to companion?!
-- - a path still to be walked
-- return: the tableau at the end of the path, possibly by looping via condition 6 repeats
def tabInAtLoopy : (Σ X, ClosedTableau ([],[]) X) → List TNode → List TNode → Option TNode
| ⟨X, tab⟩, _, [] => some X -- we have reached the destination
| ⟨X, tab⟩, done, (Y::rest) => by
      cases tab_def : tabInAt ⟨X, ([],[]), tab⟩ done
      case none =>
        exact none -- this should never happen :-(
      case some Y_ =>
        rcases Y_ with ⟨Y, HistY, ctY⟩
        cases ctY
        case loc ltY next =>
          cases ltY
          case byLocalRule B lnext lrApp =>
            refine if Y_in : Y ∈ B then ?_ else ?_
            · exact tabInAtLoopy ⟨X, tab⟩ (done ++ [Y]) rest -- move down a real step
            · exact none
          case sim Y_simp =>
            have ctY := next Y
            simp [endNodesOf, List.mem_singleton] at ctY

            cases ctY _

            all_goals sorry

        case mrkL =>
          -- apply tabInAt ?
          sorry
        case rep isRep =>
          let (bef, aft) := hX
          simp only [condSixRepeat, List.any_eq_true] at isRep
          rcases isRep with ⟨⟨k,Y⟩, getk, X_is_Y⟩ -- is k the index now? start with 0 or 1?
          -- now go back to the companion (and thus allow the path to be longer than the actual tableau)
          let newDone : List TNode := done.drop (k+1) -- undo the steps since companion
          have : newDone.length + (Y::rest).length < done.length + (Y::rest).length := by
            zify
            simp_all
            -- ring -- why not working?
            sorry
          exact tabInAt ⟨X, (bef, aft), tab⟩ newDone (Y::rest)
        all_goals sorry
termination_by
  tabInAt Xhtab done todo => done.length + todo.length
decreasing_by simp_wf; simp_all


-- MB: Lemma 7
theorem loadedDiamondPaths
  {Root Δ : TNode}
  (tab : ClosedTableau ([],[]) Root) -- ensure History = [] here to prevent repeats from "above".
  (path_to_Δ : List TNode)
  (h : some tabΔ = tabInAt ⟨Root,_,tab⟩ [] path_to_Δ)
  {M : KripkeModel W} {v : W}
  (φ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋φ) Δ) -- FIXME: ∈ not working here?
  (v_X : (M,v) ⊨ Δ)
  (v_α_w : relate M α v w)
  (w_φ : (M,w) ⊨ ~''φ)
  : ∃ path_Δ_to_Γ : List TNode,
    ∃ Γ ∈ tabInAt ⟨Root,_,tab⟩ [] (path_to_Δ ++ path_Δ_to_Γ),
    (AnyNegFormula_in_TNode (~''φ) Γ.1) -- FIXME: ∈ not working here?
    ∧
    (M,w) ⊨ Γ.1 :=
  by
  let ⟨L,R,O⟩ := Δ
  let ⟨ΔNode, ΔHist, ΔTab⟩ := tabΔ
  -- cases tab -- No, we want to distinguish by cases what is happening at Δ
  cases ΔTab
  case mrkL =>
    -- it should be impossible to apply (M+)
    -- because we already have a loaded formula in Δ
    simp at negLoad_in
    cases negLoad_in
    case inl hyp => subst hyp; sorry
    all_goals sorry

  all_goals sorry
-/
