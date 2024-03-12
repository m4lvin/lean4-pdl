-- LOCAL TABLEAU

import Pdl.Setsimp
import Pdl.Discon
import Pdl.DagTableau
import Pdl.Vocab

open Undag HasLength

-- TABLEAU NODES

-- A tableau node has two lists of formulas and one or no negated loaded formula.
def TNode := List Formula × List Formula × Option (Sum NegLoadFormula NegLoadFormula) -- ⟨L, R, o⟩
  deriving DecidableEq, Repr

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - loading is not changed in local tableaux, but must be tracked through it.
-- - each (loaded) formula can be on the left/right/both
-- - we also need to track loading and the side "through" dagger tableau.

-- We do not care about the order of the lists.
-- TNodes should be considered equal when their Finset versions are equal.
-- Hint: use List.toFinset.ext_iff with this.
def TNode.setEqTo : TNode → TNode → Bool
| (L,R,O), (L',R',O') => L.toFinset == L'.toFinset ∧ R.toFinset == R'.toFinset ∧ O == O'

def TNode.toFinset : TNode → Finset Formula
| (L,R,O) => (L.toFinset ∪ R.toFinset) ∪ (O.map (Sum.elim negUnload negUnload)).toFinset

@[simp]
def TNode.L : TNode → List Formula := λ⟨L,_,_⟩ => L
@[simp]
def TNode.R : TNode → List Formula := λ⟨_,R,_⟩ => R
@[simp]
def TNode.O : TNode → Option (Sum NegLoadFormula NegLoadFormula) := λ⟨_,_,O⟩ => O

def TNode.isLoaded : TNode → Bool
| ⟨_, _, none  ⟩ => False
| ⟨_, _, some _⟩ => True

open HasVocabulary
def sharedVoc : TNode → Finset Char := λN => voc N.L ∩ voc N.R
instance tNodeHasVocabulary : HasVocabulary (TNode) := ⟨sharedVoc⟩

instance modelCanSemImplyTNode : vDash (KripkeModel W × W) TNode :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

-- silly but useful:
instance modelCanSemImplyLLO : vDash (KripkeModel W × W) (List Formula × List Formula × Option (Sum NegLoadFormula NegLoadFormula)) :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

instance tNodeHasSat : HasSat TNode :=
  HasSat.mk fun Δ => ∃ (W : Type) (M : KripkeModel W) (w : W), (M,w) ⊨ Δ

-- LOCAL TABLEAU

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def Closed : Finset Formula → Prop := fun X => ⊥ ∈ X ∨ ∃ f ∈ X, (~f) ∈ X

-- Local rules replace a given set of formulas by other sets, one for each branch.
-- (In Haskell this is "ruleFor" in Logic.PDL.Prove.Tree.)
inductive OneSidedLocalRule : List Formula → List (List Formula) → Type
  -- PROP LOGIC
  -- closing rules:
  | bot                 : OneSidedLocalRule [⊥]      ∅
  | not (φ   : Formula) : OneSidedLocalRule [φ, ~φ]  ∅
  | neg (φ   : Formula) : OneSidedLocalRule [~~φ]    [[φ]]
  | con (φ ψ : Formula) : OneSidedLocalRule [φ ⋀ ψ]  [[φ,ψ]]
  | nCo (φ ψ : Formula) : OneSidedLocalRule [~(φ⋀ψ)] [[~φ], [~ψ]]
  -- PROGRAMS
  -- one-child rules:
  | nTe (φ ψ)   : OneSidedLocalRule [~⌈?'φ⌉ψ]  [ [φ, ~ψ] ]
  | nSe (a b f) : OneSidedLocalRule [~⌈a;'b⌉f] [ [~⌈a⌉⌈b⌉f] ]
  | uni (a b f) : OneSidedLocalRule [⌈a⋓b⌉f]   [ [⌈a⌉f, ⌈b⌉f] ]
  | seq (a b f) : OneSidedLocalRule [⌈a;'b⌉f]  [ [⌈a⌉⌈b⌉f] ]
  -- splitting rules:
  | tes (f g)   : OneSidedLocalRule [⌈?'f⌉g]    [ [~f], [g] ]
  | nUn (a b f) : OneSidedLocalRule [~⌈a ⋓ b⌉f] [ [~⌈a⌉f], [~⌈b⌉f] ]
  -- STAR
  -- NOTE: we "manually" already make the first unravel/dagger step here to satisfy the (Neg)DagFormula type.
  | sta (a f) : OneSidedLocalRule [⌈∗a⌉f] (boxDagEndNodes ({f}, [ inject [a] a f ]))
  | nSt (a f) : OneSidedLocalRule [~⌈∗a⌉f] ([ [~f] ] ++ (dagEndNodes (∅, NegDagFormula.neg (inject [a] a f))))

theorem oneSidedLocalRuleTruth (lr : OneSidedLocalRule X B) : Con X ≡ discon B :=
  by
  intro W M w
  cases lr
  all_goals try (simp; done) -- takes care of all propositional rules
  all_goals try (aesop; done) -- takes care of three more rules

  case nUn a b φ => -- from {~⌈a ⋓ b⌉φ} to {~⌈a⌉φ} or {~⌈b⌉φ}
    constructor
    · aesop
    · intro w_X
      simp only [discon, Con, evaluate, Formula.or, ← or_iff_not_and_not] at w_X
      cases w_X
      all_goals aesop

  -- STAR RULES
  case nSt a φ =>
    constructor
    · -- soundness
      intro w_naSphi
      have := notStarSoundness M w a φ w_naSphi
      rcases this with ⟨Γ, Γ_in, w_Γ⟩
      rw [disconEval]
      simp [evaluatePoint,modelCanSemImplyList] at *
      aesop
    · -- invertibility
      intro w_X
      simp at w_X
      rw [disconEval] at w_X
      simp
      rcases w_X with ⟨Y,⟨Y_in, sat_Y⟩⟩
      cases Y_in
      · use w
        constructor
        · apply Relation.ReflTransGen.refl
        · simp at sat_Y; assumption
      · have := notStarInvert M w _ (by aesop) (~⌈a⌉⌈∗a⌉φ)
        simp [vDash, modelCanSemImplyDagTabNode] at this
        rcases this with ⟨z, w_a_z, y, z_aS_x, y_nf⟩
        use y
        constructor
        · apply Relation.ReflTransGen.head
          all_goals aesop
        · assumption

  case sta a f =>
    constructor
    · -- soundness
      intro Mw_X
      rw [disconEval]
      apply starSoundness M w ([f], [inject [a] a f])
      intro phi phi_in
      simp [vDash, undag, modelCanSemImplyDagTabNode, inject] at phi_in
      cases phi_in
      case inl phi_is_f =>
            subst phi_is_f
            simp at *
            apply Mw_X _ Relation.ReflTransGen.refl
      case inr phi_is_aaSf =>
            subst phi_is_aaSf
            simp at *
            intro v w_a_v z v_a_z
            exact Mw_X _ (Relation.ReflTransGen.head w_a_v v_a_z)
    · -- invertibility
      intro w_B
      have Mw_X := starInvert M w ([f], [inject [a] a f])
      specialize Mw_X _
      · rw [disconEval] at w_B
        exact w_B
      simp at *
      intro v w_aS_v
      cases Relation.ReflTransGen.cases_head w_aS_v
      case inl w_is_v =>
        subst w_is_v
        specialize Mw_X f
        simp at Mw_X
        exact Mw_X
      case inr hyp =>
        rcases hyp with ⟨z, w_a_z, z_aS_v⟩
        specialize Mw_X (⌈a⌉⌈∗a⌉f)
        simp at Mw_X
        exact Mw_X z w_a_z v z_aS_v


-- LOADED rule applications
-- Only the local rules ¬u, ¬; ¬* and ¬? may be applied to loaded formulas (MB page 19).
-- Each rule replaces the loaded formula by:
-- - up to one loaded formula,
-- - and a set of normal formulas.
-- It's annoying to need each rule twice here (due to the definition of LoadFormula).
inductive LoadRule : NegLoadFormula → List (List Formula × Option NegLoadFormula) → Type
  | nUn  {α β χ} : LoadRule (~'⌊α⋓β ⌋(χ : LoadFormula)) [ (∅, some (~'⌊α⌋χ)), (∅, some (~'⌊β⌋χ)) ]
  | nUn' {α β φ} : LoadRule (~'⌊α⋓β ⌋(φ : Formula    )) [ (∅, some (~'⌊α⌋φ)), (∅, some (~'⌊β⌋φ)) ]
  | nSe  {α β χ} : LoadRule (~'⌊α;'β⌋(χ : LoadFormula)) [ (∅, some (~'⌊α⌋⌊β⌋χ)) ]
  | nSe' {α β φ} : LoadRule (~'⌊α;'β⌋(φ : Formula    )) [ (∅, some (~'⌊α⌋⌊β⌋φ)) ]
  -- Now we use loaded dagger diamond tableau:
  | nSt  {α χ}   : LoadRule (~'⌊∗α  ⌋(χ : LoadFormula)) ([ (∅, some (~'χ)) ] ++
     loadDagEndNodes (∅, (Sum.inr (NegDagLoadFormula.neg (injectLoad α χ)))))
  | nSt' {α φ}   : LoadRule (~'⌊∗α  ⌋(φ : Formula    )) ([ ([~φ], none) ] ++
     loadDagEndNodes (∅, (Sum.inr (NegDagLoadFormula.neg (injectLoad' α φ)))))
  | nTe  {φt χ}  : LoadRule (~'⌊?'φt⌋(χ : LoadFormula)) [ ([φt], some (~'χ)) ]
  | nTe' {φt φ}  : LoadRule (~'⌊?'φt⌋(φ : Formula    )) [ ([φt, ~φ], none) ]

theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~(unload χ)) ≡ dis (B.map (λ (fs, o) => Con (fs ++ (o.map negUnload).toList))) :=
  by
  intro W M w
  cases lr

  case nTe => simp
  case nTe' => simp

  case nSe => aesop
  case nSe' => aesop

  case nUn α β χ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nUn α β (unload χ)) W M w
    simp at *
    exact this
  case nUn' α β φ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nUn α β φ) W M w
    simp at *
    exact this

  case nSt α χ =>
    constructor
    · -- soundness
      intro w_naSchi
      have := loadNotStarSoundness M w α χ w_naSchi
      rcases this with ⟨Γ, Γ_in, w_Γ⟩
      simp at Γ_in
      simp
      rw [disEvalHT, disEval]
      cases Γ_in
      case inl Γ_def =>
        subst Γ_def
        left
        apply w_Γ
        simp
      case inr Γ_in =>
        right
        simp only [List.mem_map, Prod.exists]
        refine ⟨?_, ⟨Γ.1, Γ.2, ?_⟩, ?_⟩
        · exact Con (Γ.1 ++ Option.toList (Option.map negUnload Γ.2))
        · simp; assumption
        · rw [conEval]; apply w_Γ
    · -- invertibility
      intro w_X
      simp [disEvalHT, disEval] at w_X
      cases w_X
      · simp; use w
      case inr hyp =>
        simp at hyp
        rcases hyp with ⟨f, ⟨Γ1, Γ2, ⟨Γ_in_ends, def_f⟩⟩, w_Γ⟩
        let thelf := NegDagLoadFormula.neg (DagLoadFormula.box α (DagLoadFormula.ldg α χ))
        have := loadNotStarInvert M w ([], Sum.inr thelf) ⟨⟨Γ1,Γ2⟩, ⟨Γ_in_ends, ?_⟩⟩
        · simp [vDash, modelCanSemImplyLoadDagTabNode, evaluateLDDTNode] at *
          rcases this with ⟨z, w_a_z, y, z_aS_x, y_nf⟩
          use y
          constructor
          · exact Relation.ReflTransGen.head w_a_z z_aS_x
          · assumption
        · intro g g_in -- for the ?_ above
          subst def_f
          rw [conEval] at w_Γ
          aesop
  case nSt' α φ =>
    -- analogous to nSt, but using loadNotStarSoundness' with a φ instead of χ.
    constructor
    · -- soundness
      intro w_naSchi
      have := loadNotStarSoundness' M w α φ w_naSchi
      rcases this with ⟨Γ, Γ_in, w_Γ⟩
      simp at Γ_in
      simp
      rw [disEvalHT, disEval]
      cases Γ_in
      case inl Γ_def =>
        subst Γ_def
        left
        apply w_Γ
        simp
      case inr Γ_in =>
        right
        simp only [List.mem_map, Prod.exists]
        refine ⟨?_, ⟨Γ.1, Γ.2, ?_⟩, ?_⟩
        · exact Con (Γ.1 ++ Option.toList (Option.map negUnload Γ.2))
        · simp; assumption
        · rw [conEval]; apply w_Γ
    · -- invertibility
      intro w_X
      simp [disEvalHT, disEval] at w_X
      cases w_X
      · simp; use w
      case inr hyp =>
        simp at hyp
        rcases hyp with ⟨f, ⟨Γ1, Γ2, ⟨Γ_in_ends, def_f⟩⟩, w_Γ⟩
        let thelf := NegDagLoadFormula.neg (DagLoadFormula.box α (DagLoadFormula.dag α φ))
        have := loadNotStarInvert M w ([], Sum.inr thelf) ⟨⟨Γ1,Γ2⟩, ⟨Γ_in_ends, ?_⟩⟩
        · simp [vDash, modelCanSemImplyLoadDagTabNode, evaluateLDDTNode] at *
          rcases this with ⟨z, w_a_z, y, z_aS_x, y_nf⟩
          use y
          constructor
          · exact Relation.ReflTransGen.head w_a_z z_aS_x
          · assumption
        · intro g g_in -- for the ?_ above
          subst def_f
          rw [conEval] at w_Γ
          aesop

-- A LocalRule is a OneSidedLocalRule or a LoadRule.
-- Formulas can be in four places now: left, right, loaded left, loaded right.
inductive LocalRule : TNode → List TNode → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅,none) $ ress.map $ λ res => (res,∅,none)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond,none) $ ress.map $ λ res => (∅,res,none)
  | LRnegL (ϕ : Formula) : LocalRule ([ϕ], [~ϕ], none) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ([~ϕ], [ϕ], none) ∅ -- ~ϕ occurs on the left side,  ϕ on the right
  -- NOTE: do we need neg rules for ({unload χ}, ∅, some (Sum.inl ~χ)) and (∅, {unload χ}, some (Sum.inr ~χ)), ..here?
  -- Probably not, because then we could also have closed before/without loading!
  | loadedL (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inl (~'χ))) $ ress.map $ λ (X, o) => (X, ∅, o.map Sum.inl)
  | loadedR (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inr (~'χ))) $ ress.map $ λ (X, o) => (∅, X, o.map Sum.inr)

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond, Ocond) ress) : TNode → List TNode
  | ⟨L, R, O⟩ => ress.map $ λ (Lnew, Rnew, Onew) => match Onew with
      | none                 => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, O)
      | some (Sum.inl (~'χ)) => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, some (Sum.inl (~'χ)))
      | some (Sum.inr (~'χ)) => (L.diff Lcond ++ Lnew, R.diff Rcond ++ Rnew, some (Sum.inr (~'χ)))

-- mathlib this?
@[simp]
instance Option.instHasSubsetOption : HasSubset (Option α) := HasSubset.mk
  λ o1 o2 =>
  match o1, o2 with
  | none, _ => True
  | some _, none => False
  | some f, some g => f = g

-- mathlib this?
@[simp]
theorem Option.some_subseteq {O : Option α} : (some x ⊆ O) ↔ some x = O := by
  cases O
  all_goals simp

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : List Formula}
       {C : List TNode}
       {ress : List TNode}
       {O : Option (Sum NegLoadFormula NegLoadFormula)}
       (Lcond Rcond : List Formula)
       (Ocond : Option (Sum NegLoadFormula NegLoadFormula))
       (rule : LocalRule (Lcond, Rcond, Ocond) ress)
       {hC : C = applyLocalRule rule (L,R,O)}
       (preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R ∧ Ocond ⊆ O)
       : LocalRuleApp (L,R,O) C

theorem localRuleTruth
    {L R : List Formula}
    {C : List TNode}
    (O : Option (Sum NegLoadFormula NegLoadFormula))
    (lrA : LocalRuleApp (L,R,O) C) (M : KripkeModel W) (w : W)
  : (M,w) ⊨ (L,R,O) ↔ ∃ Ci ∈ C, (M,w) ⊨ Ci
  := by
  rcases lrA with ⟨Lcond, Rcond, Ocond, rule, preconditionProof⟩
  cases rule

  case oneSidedL ress orule hC =>
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff, List.mem_append]
        exact Or.inl $ Or.inl $ preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with (((f_in_L | f_in_Y) | f_in_R) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl $ List.diff_subset L Lcond f_in_L
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          tauto
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff, List.mem_append] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · rcases em (f ∈ Lcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Lcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl $ Or.inl $ List.mem_diff_of_mem f_in_L f_notin_cond
      · apply w_LYRO; simp_all
      · apply w_LYRO; simp_all
  case oneSidedR ress orule hC =>
    -- based on oneSidedL case
    have := oneSidedLocalRuleTruth orule W M w
    have osTruth := oneSidedLocalRuleTruth orule W M w
    subst hC
    simp [applyLocalRule] at *
    constructor
    · intro w_LRO
      have : evaluate M w (discon ress) := by
        rw [← osTruth, conEval]
        intro f f_in; apply w_LRO
        simp only [List.mem_union_iff, List.mem_append]
        exact Or.inl $ Or.inr $ preconditionProof f_in
      rw [disconEval] at this
      rcases this with ⟨Y, Y_in, claim⟩
      use Y
      constructor
      · exact Y_in
      · intro f f_in
        simp only [List.mem_union_iff, List.mem_append] at f_in
        rcases f_in with ((f_in_L | (f_in_R | f_in_Y)) | f_in_O)
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inl f_in_L
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inr $ List.diff_subset R Rcond f_in_R
        · exact claim f f_in_Y
        · apply w_LRO f; simp only [List.mem_union_iff, List.mem_append]
          exact Or.inr f_in_O
    · rintro ⟨Y, Y_in, w_LYRO⟩
      intro f f_in
      simp only [List.mem_union_iff, List.mem_append] at f_in
      rcases f_in with ((f_in_L | f_in_R) | f_in_O)
      · apply w_LYRO; simp_all
      · rcases em (f ∈ Rcond) with f_in_cond | f_notin_cond
        · have : ∀ f ∈ Rcond, evaluate M w f := by
            rw [← conEval, osTruth, disconEval]
            use Y
            constructor
            · exact Y_in
            · intro f f_in; apply w_LYRO; simp_all
          exact this f f_in_cond
        · apply w_LYRO
          simp only [List.mem_union_iff, List.mem_append]
          exact Or.inl $ Or.inr $ Or.inl $ List.mem_diff_of_mem f_in_R f_notin_cond
      · apply w_LYRO; simp_all

  case LRnegL φ hC =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop
  case LRnegR φ hC =>
    subst hC
    simp [applyLocalRule] at *
    intro hyp
    have := hyp φ
    have := hyp (~φ)
    aesop

  case loadedL ress χ lrule hC  =>
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp [modelCanSemImplyForm,modelCanSemImplyLLO] at *
    constructor
    · intro hyp
      have hyp' := hyp (~unload χ)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L ++ X, R, some (Sum.inl (~'χ)))
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L ++ X, R, some (Sum.inl val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in; subst def_f; rw [conEval] at w_f
          simp only [List.mem_union_iff, List.mem_append, List.mem_singleton] at g_in
          rcases g_in with ((g_in|g_in)|g_in)|g_in
          all_goals aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O
      all_goals simp at *
      · have := w_Ci f
        aesop
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (X ++ Option.toList (Option.map negUnload (some val)))
          constructor
          · use X, some val
          · rw [conEval]
            simp only [Option.map_some', negUnload, Option.toList_some, List.mem_append, List.mem_singleton]
            intro g g_in
            rcases g_in with (_|g_def)
            · apply w_Ci; simp_all
            · subst g_def; apply w_Ci; simp_all

  case loadedR ress χ lrule hC =>
    -- based on loadedL case
    have := loadRuleTruth lrule W M w
    rw [disEval] at this
    subst hC
    simp at preconditionProof
    subst preconditionProof
    simp [modelCanSemImplyForm,modelCanSemImplyLLO] at *
    constructor
    · intro hyp
      have hyp' := hyp (~unload χ)
      simp at hyp'
      rw [this] at hyp'
      rcases hyp' with ⟨f, ⟨X , O, in_ress, def_f⟩, w_f⟩
      cases O
      · use (L, R ++ X, some (Sum.inr (~'χ)))
        constructor
        · use X, none; simp only [Option.map_none', and_true]; exact in_ress
        · intro g; subst def_f; rw [conEval] at w_f; specialize hyp g; aesop
      case some val =>
        use (L, R ++ X, some (Sum.inr val))
        constructor
        · use X, some val; simp only [Option.map_some', and_true]; exact in_ress
        · intro g g_in; subst def_f; rw [conEval] at w_f
          simp only [List.mem_union_iff, List.mem_append, List.mem_singleton] at g_in
          rcases g_in with (g_in|(g_in|g_in))|g_in
          all_goals aesop
    · rintro ⟨Ci, ⟨⟨X, O, ⟨in_ress, def_Ci⟩⟩, w_Ci⟩⟩
      intro f f_in
      subst def_Ci
      cases O
      all_goals simp at *
      · have := w_Ci f
        aesop
      case some val =>
        rcases f_in with (f_in|f_in)|f_in
        · apply w_Ci; simp_all
        · apply w_Ci; simp_all
        · subst f_in
          simp only [evaluate]
          rw [this]
          use Con (X ++ Option.toList (Option.map negUnload (some val)))
          constructor
          · use X, some val
          · rw [conEval]
            simp only [Option.map_some', negUnload, Option.toList_some, List.mem_append, List.mem_singleton]
            intro g g_in
            rcases g_in with (_|g_def)
            · apply w_Ci; simp_all
            · subst g_def; apply w_Ci; simp_all

-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
@[simp]
def isSimpleForm : Formula → Bool
  | ⊥ => True -- TODO: change to False, covered by bot rule?
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

def isSimpleSet : Finset Formula → Bool
  | X => ∀ P ∈ X, isSimpleForm P

def isSimpleNode : TNode → Bool
  | (L, R, o) => ∀ f ∈ L ++ R ++ (o.map (Sum.elim negUnload negUnload)).toList, isSimpleForm f

-- MB: Definition 8
-- a local tableau for X, must be maximal
inductive LocalTableau : TNode → Type
  | byLocalRule {X B} (_ : LocalRuleApp X B) (next : ∀ Y ∈ B, LocalTableau Y) : LocalTableau X
  | sim {X} : isSimpleNode X → LocalTableau X

open LocalTableau

-- LOCAL END NODES AND TERMINATION

@[simp]
def lengthOfTNode : TNode -> ℕ
  | (L, R, none) => lengthOf L + lengthOf R
  | (L, R, some (Sum.inl (~'χ))) => lengthOf L + lengthOf R + lengthOf (~ unload χ)
  | (L, R, some (Sum.inr (~'χ))) => lengthOf L + lengthOf R + lengthOf (~ unload χ)

@[simp]
instance tnodeHasLength : HasLength TNode := ⟨lengthOfTNode⟩

theorem localRuleDecreasesLengthSide (rule : LocalRule condit ress) :
  ∀ r ∈ ress, lengthOf r < lengthOf condit :=
    by
    intro r r_in_ress
    cases rule
    case LRnegL => simp at *
    case LRnegR => simp at *
    case oneSidedL orule =>
      cases orule
      all_goals
        simp at *
      all_goals
        sorry -- should be analogous to oneSidedR
    case oneSidedR orule =>
      cases orule
      all_goals
        simp at *
      all_goals
        try subst_eqs
        try simp
        try linarith
      all_goals
        sorry -- some of the goals here are wrong due to using lengthOf, need a local measure!
    case loadedL lrule =>
      cases lrule
      all_goals
        simp at *
        cases r_in_ress
      all_goals
        try subst_eqs
        simp at *
      all_goals
        try linarith
      all_goals
        sorry
    case loadedR =>
      sorry -- should be analogous to loadedL

-- TODO: is this even going to be true for our new system?
-- Maybe use a different measure than lengthOf? Also Dershowitz-Manna?
theorem localRuleApp.decreaseLength {X : TNode} {B : List TNode}
    (lrA : LocalRuleApp X B) : ∀ Y ∈ B, lengthOf Y < lengthOf X :=
  by
  rcases lrA with ⟨Lcond,Rcond,OCond,rule,preconP⟩
  rename_i L R ress O B_def
  subst B_def
  intro Y Y_in
  simp [applyLocalRule] at Y_in
  rcases Y_in with ⟨⟨Lnew,Rnew,Onew⟩, Y_in_ress, claim⟩
  have := localRuleDecreasesLengthSide rule Y
  sorry

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → List TNode
  | ⟨X, @byLocalRule _ B lr next⟩ =>
    (B.attach.map fun ⟨Y, h⟩ =>
      have : lengthOf Y < lengthOf X := localRuleApp.decreaseLength lr Y h
      endNodesOf ⟨Y, next Y h⟩).join
  | ⟨X, sim _⟩ => [X]
termination_by
  X => lengthOf X.1
decreasing_by
  convert this
