-- TABLEAU

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Option
import Mathlib.Data.List.Card

import Pdl.Syntax
import Pdl.Measures
import Pdl.Setsimp
import Pdl.Semantics
import Pdl.Discon
import Pdl.DagTableau

open Undag

open HasLength

-- TABLEAU nodes

-- A tableau node has a set of formulas and one or no negated loaded formula.
def TNode := List Formula × List Formula × Option (Sum NegLoadFormula NegLoadFormula) -- ⟨L, R, o⟩
  deriving DecidableEq -- TODO Repr

instance modelCanSemImplyTNode : vDash (KripkeModel W × W) TNode :=
  vDash.mk (λ ⟨M,w⟩ ⟨L, R, o⟩ => ∀ f ∈ L ∪ R ∪ (o.map (Sum.elim negUnload negUnload)).toList, evaluate M w f)

-- Some thoughts about the TNode type:
-- - one formula may be loaded
-- - loading is not changed in local tableaux, but must be tracked through it.
-- - each (loaded) formula is left/right/both --> annotation or actually have two sets X1 and X2 here?
-- - also need to track loading and side "through" dagger tableau. (loading only for diamond dagger?)

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
      intro w_naSf
      simp at w_naSf
      simp [discon]
      rw [disconEval]
      rcases w_naSf with ⟨y, x_rel_y, y_nf⟩
      cases starCases x_rel_y -- NOTE: Relation.ReflTransGen.cases_head without ≠ is not enough here ...
      case inl w_is_y =>
        subst w_is_y
        use [~φ]
        simp
        exact y_nf
      case inr hyp =>
        -- (... because we need to get the in-equality here to get the contradiction below.)
        rcases hyp with ⟨_, z, w_neq_z, w_a_z, z_aS_y⟩
        -- MB now distinguishes whether a is atomic, we don't care.
        have := notStarSoundnessAux a M w z ([]) (DagFormula.dag a φ)
        specialize this _ w_a_z _
        · intro g g_in
          simp at g_in
          subst g_in
          simp
          exact ⟨z, ⟨w_a_z, ⟨y, ⟨z_aS_y, y_nf⟩⟩⟩⟩
        · simp [vDash,modelCanSemImplyForm]
          use y
        rcases this with ⟨Γ, Γ_in, w_Γ, caseOne | caseTwo⟩
        · rcases caseOne with ⟨A, as, _, _, Γ_normal⟩
          use Γ.1
          constructor
          · have := dagNormal_is_dagEnd Γ_in Γ_normal
            aesop
          · intro f f_in
            aesop
        · absurd caseTwo.2 -- contradiction!
          exact w_neq_z
    · -- want to use notStarInvert, but that does not know/care about loading (but here should be okay.)
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
     loadDagEndNodes (X, some (Sum.inr (NegDagLoadFormula.neg (injectLoad a χ)))))
  | nSt' {α φ}   : LoadRule (~'⌊∗α  ⌋(φ : Formula    )) ([ ([~φ], none) ] ++
     loadDagEndNodes (X, some (Sum.inr (NegDagLoadFormula.neg (injectLoad' a φ)))))
  | nTe  {φt χ}  : LoadRule (~'⌊?'φt⌋(χ : LoadFormula)) [ ([φt], some (~'χ)) ]
  | nTe' {φt φ}  : LoadRule (~'⌊?'φt⌋(φ : Formula    )) [ ([φt, ~φ], none) ]

theorem loadRuleTruth (lr : LoadRule (~'χ) B) :
    (~(unload χ)) ≡ dis (B.map (λ (fs, o) => Con (fs ++ (o.map negUnload).toList))) :=
  by
  intro W M w
  cases lr
  all_goals try (simp; done)
  all_goals try (aesop; done)
  all_goals simp

  case nUn α β χ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nUn α β (unload χ)) W M w
    simp at this
    exact this
  case nUn' α β φ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nUn α β φ) W M w
    simp at this
    exact this

  case nSt α χ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nSt α (unload χ)) W M w
    simp at this
    -- First need to implement loadDagEndNodes
    sorry
  case nSt' α φ =>
    have := oneSidedLocalRuleTruth (OneSidedLocalRule.nSt α φ) W M w
    simp at this
    -- First need to implement loadDagEndNodes
    sorry

-- A LocalRule is a OneSidedLocalRule or a LoadRule.
-- Formulas can be in four places now: left, right, loaded left, loaded right.
inductive LocalRule : TNode → List TNode → Type
  | oneSidedL (orule : OneSidedLocalRule precond ress) : LocalRule (precond,∅,none) $ ress.map $ λ res => (res,∅,none)
  | oneSidedR (orule : OneSidedLocalRule precond ress) : LocalRule (∅,precond,none) $ ress.map $ λ res => (∅,res,none)
  | LRnegL (ϕ : Formula) : LocalRule ({ϕ}, {~ϕ}, none) ∅ --  ϕ occurs on the left side, ~ϕ on the right
  | LRnegR (ϕ : Formula) : LocalRule ({~ϕ}, {ϕ}, none) ∅ -- ~ϕ occurs on the left side,  ϕ on the right
  -- NOTE: do we need neg rules for ({unload χ}, ∅, some (Sum.inl ~χ)) and (∅, {unload χ}, some (Sum.inr ~χ)), ..here?
  -- Probably not, because then we could also have closed before/without loading!
  | loadedL (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inl (~'χ))) $ ress.map $ λ (X, o) => (X, ∅, o.map Sum.inl)
  | loadedR (χ : LoadFormula) (lrule : LoadRule (~'χ) ress) :
      LocalRule (∅, ∅, some (Sum.inr (~'χ))) $ ress.map $ λ (X, o) => (∅, X, o.map Sum.inr)

@[simp]
def applyLocalRule (_ : LocalRule (Lcond, Rcond, Ocond) C) : TNode → List TNode
  | ⟨L, R, o⟩ => C.map $ λ (Lnew, Rnew, Onew) => match Onew with
      | none => (L \ Lcond ∪ Lnew, R \ Rcond ∪ Rnew, o)
      | some (Sum.inl (~'χ)) => (L \ Lcond ∪ Lnew, R \ Rcond ∪ Rnew, some (Sum.inl (~'χ)))
      | some (Sum.inr (~'χ)) => (L \ Lcond ∪ Lnew, R \ Rcond ∪ Rnew, some (Sum.inr (~'χ)))

instance : HasSubset (Option (NegLoadFormula ⊕ NegLoadFormula)) := HasSubset.mk
  λ o1 o2 =>
  match o1, o2 with
  | none, _ => True
  | some _, none => False
  | some f, some g => f == g

inductive LocalRuleApp : TNode → List TNode → Type
  | mk {L R : List Formula}
       {C : List TNode}
       (O : Option (Sum NegLoadFormula NegLoadFormula))
       (Lcond Rcond : List Formula)
       (Ocond : Option (Sum NegLoadFormula NegLoadFormula))
       (rule : LocalRule (Lcond, Rcond, Ocond) C)
       (preconditionProof : Lcond ⊆ L ∧ Rcond ⊆ R ∧ Ocond ⊆ O)
       : LocalRuleApp (L,R,o) $ applyLocalRule rule (L,R,o)

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

-- needed for endNodesOf
instance localTableauHasSizeof : SizeOf (Σ X, LocalTableau X) :=
  ⟨fun ⟨X, _⟩ => lengthOf X⟩


-- TODO: is this even going to be true for our new system?
-- Maybe use a different measure than lengthOf? Also Dershowitz-Manna?
theorem localRuleApp.decreaseLength {X : TNode} {B : List TNode}
    (r : LocalRuleApp X B) : ∀ Y ∈ B, lengthOf Y < lengthOf X :=
  by
  cases r
  all_goals intro β inB; simp at *
  -- TODO: see Bml, first enable additional simps in Pdl.Setsimp
  all_goals sorry

-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, LocalTableau X) → List TNode
  | ⟨X, @byLocalRule _ B lr next⟩ =>
    (B.attach.map fun ⟨Y, h⟩ =>
      have : lengthOf Y < lengthOf X := localRuleApp.decreaseLength lr Y h
      endNodesOf ⟨Y, next Y h⟩).join
  | ⟨X, sim _⟩ => [X]

-- PROJECTIONS

@[simp]
def formProjection : Char → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

def projection : Char → List Formula → List Formula
  | A, X => (X.map fun x => (formProjection A x)).reduceOption

@[simp]
theorem proj : g ∈ projection A X ↔ (⌈·A⌉g) ∈ X :=
  by
  rw [projection]
  simp
  induction X
  aesop
  aesop


-- TABLEAUX

-- (MB: Definition 16, page 29)
-- TODO: do we want a ClosedTableau or more general Tableau type?
-- If more general, do we want an "open" constructor with(out) arguments/proofs?

-- A tableau for X is either of:
-- - a local tableau for X followed by tableaux for all end nodes,
-- - a (M+) loading rule application
-- - a (At) modal rule application (two cases due to LoadFormula type)
-- - a good repeat (MB condition six)

def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)

-- From ~⌈α⌉φ to ~'⌊α⌋χ
def toNegLoad (α : Program) (φ : Formula) : NegLoadFormula :=
  match boxesOf φ with
    | ([],f) => ~'⌊α⌋f
    | (bs,f) => sorry

-- NOTES about the History type:
-- - The newest/lowest TNode should be the head of the list.
-- - we also need the rule that is applied to check isCritical.
--   Add "× LocalRuleApp" to History type? Need Σ.
-- - currently we only track "big" steps, do we need local steps?
--
def History : Type := List TNode -- This may not be enough!

-- A history is loaded iff it always contains a loaded formula.
def isLoaded : History → Bool
  | [] => True
  | ((_,_,some _)::rest) => isLoaded rest
  | ((_,_,none  )::_) => False

def isCriticalTo : TNode → (Hist : History) → Bool
  | X, [] => False
  | X, (Y::rest) =>
      if X == Y then sorry else sorry -- need to know the rules that were applied!

-- MB Condition 6, simplified to only represent closed tableau:
--
-- A node t repeating s can be treated as a closed end node if
-- the path from s to t is critical and loaded.
def isCondSixRepeat : TNode → History → Bool :=
  by sorry

-- The "Step" notation has two jobs:
-- - flip the order in the definition below to be more natural.
-- - avoid having to repeat "parent" to build the history.
notation "Step" Ct:arg Hist:arg parent:arg child:arg => Ct (parent::Hist) child → Ct Hist parent

-- ClosedTableau [parent, grandparent, ...] child
inductive ClosedTableau : History → TNode → Type
  -- Do a local tableau:
  | loc {X} (lt : LocalTableau X) : (∀ Y ∈ endNodesOf ⟨X, lt⟩, ClosedTableau Hist Y) → ClosedTableau Hist X
  -- The (M+) rule:
  | mrkL : (~⌈α⌉φ) ∈ L → Step ClosedTableau Hist (L.remove ((~⌈α⌉φ)), R, some (Sum.inl (toNegLoad α φ)))
                                                 (L, R, none)
  | mrkR : (~⌈α⌉φ) ∈ R → Step ClosedTableau Hist (L, R.remove ((~⌈α⌉φ)), some (Sum.inr (toNegLoad α φ)))
                                                 (L, R, none)
  -- The (At) rule:
  -- TODO: can we avoid the four cases?
  | atmL   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inl (~'χ)))
  | atmL'  {A X φ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L ++ [~φ], projection A R, none)
  | atmR   {A X χ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inr (~'⌊·A⌋(χ : LoadFormula)))⟩
                                                              (projection A L, projection A R, some (Sum.inr (~'χ)))
  | atmR'  {A X φ} : isSimpleNode X → Step ClosedTableau Hist ⟨L, R, some (Sum.inl (~'⌊·A⌋(φ : Formula)))⟩
                                                              (projection A L, projection A R ++ [~φ], none)
  | repeat {X Hist} (rep : isCondSixRepeat X Hist) : ClosedTableau Hist X
  --
  -- If we want only finite tableaux then 6 has to be eager! Add its negation in all other rules?

inductive Provable : Formula → Prop
  | byTableauL {φ : Formula} : ClosedTableau [] ⟨[~φ], [], none⟩ → Provable φ
  | byTableauR {φ : Formula} : ClosedTableau [] ⟨[], [~φ], none⟩ → Provable φ

-- MB: Definition 17, page 30
def Inconsistent : List Formula → Prop
  | X => ∃ L R, L ++ R = X ∧ Nonempty (ClosedTableau [] ⟨L, R, none⟩)

def Consistent : List Formula → Prop
  | X => ¬Inconsistent X
