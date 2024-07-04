-- SOUNDNESS

import Pdl.Tableau

import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

open Classical

open HasSat

/-- ## Tools for saying that different kinds of formulas are in a TNode -/

@[simp]
instance : Membership Formula TNode :=
  ⟨fun φ X => φ ∈ X.L ∨ φ ∈ X.R⟩

@[simp]
def NegLoadFormula_in_TNode := fun nlf (X : TNode) => X.O = some (Sum.inl nlf) ∨ X.O = some (Sum.inr nlf)

@[simp]
instance NegLoadFormula.HasMem_TNode : Membership NegLoadFormula TNode := ⟨NegLoadFormula_in_TNode⟩

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

/-- ## Helper functions, TODO: move to (Local)Tableau.lean -/

-- TODO Computable version possible?
noncomputable def endNode_to_endNodeOfChildNonComp (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  @Subtype TNode (fun x => ∃ h, E ∈ endNodesOf (subTabs x h)) := by
  simp [endNodesOf] at E_in
  choose l h E_in using E_in
  choose c c_in l_eq using h
  subst l_eq
  use c
  use c_in

theorem endNodeIsEndNodeOfChild (lrA)
  (E_in: E ∈ endNodesOf (@LocalTableau.byLocalRule X _ lrA subTabs)) :
  ∃ Y h, E ∈ endNodesOf (subTabs Y h) := by
  have := endNode_to_endNodeOfChildNonComp lrA E_in
  use this
  aesop

theorem endNodeOfChild_to_endNode
    {X Y: TNode}
    {ltX}
    {C : List TNode}
    (lrA : LocalRuleApp X C)
    subTabs
    (h : ltX = LocalTableau.byLocalRule lrA subTabs)
    (Y_in : Y ∈ C)
    {Z : TNode}
    (Z_in: Z ∈ endNodesOf (subTabs Y Y_in))
    : Z ∈ endNodesOf ltX :=
  by
  cases h' : subTabs Y Y_in -- No induction needed for this!
  case sim Y_isSimp =>
    subst h
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · exact Z_in
  case byLocalRule C' subTabs' lrA' =>
    subst h
    rw [h'] at Z_in
    simp
    use endNodesOf (subTabs Y Y_in)
    constructor
    · use Y, Y_in
    · rw [h']
      exact Z_in

/-- ## Navigating through tableaux with PathIn -/

-- To define ancestor / decendant relations inside tableaux we need to
-- represent both the whole Tableau and a specific node in it.
-- For this we use `PathInLocal` and `PathIn`.
-- They basically say "go to this child, then to this child, etc."
--
-- TODO: Do we need paths that go through/across multiple LocalTableau like
--       LHistories and unlike the Paths used in the Complteness Proof
--
-- TODO: Do we need paths that include back-loops?


-- UNUSED
inductive PathInLocal : ∀ {X}, LocalTableau X → Type
| byLocalRuleStep :
    (h : Y ∈ B)
    → PathInLocal (next Y h)
    → PathInLocal (LocalTableau.byLocalRule lrApp (next: ∀ Y ∈ B, LocalTableau Y))
| simEnd : PathInLocal (LocalTableau.sim _)

-- Three ways to make a path: empty, local step or pdl step.
-- The `loc` ad `pdl` steps correspond to two out of three constructors of `ClosedTableau`.
inductive PathIn : ∀ {H X}, ClosedTableau H X → Type
| nil : PathIn _
| loc : (Y_in : Y ∈ endNodesOf lt) → (tail : PathIn (next Y Y_in)) → PathIn (ClosedTableau.loc lt next)
| pdl : (r : PdlRule Γ Δ) → PathIn (child : ClosedTableau (Γ :: Hist) Δ) → PathIn (ClosedTableau.pdl r child)

def tabAt : PathIn tab → Σ H X, ClosedTableau H X
| .nil => ⟨_,_,tab⟩
| .loc _ tail => tabAt tail
| .pdl _ p_child => tabAt p_child

def nodeAt {H X} {tab : (ClosedTableau H X)} : PathIn tab → TNode
| .nil => X
| .loc _ tail => nodeAt tail
| .pdl _ p_child => nodeAt p_child

def PathIn.append (p : PathIn tab) (q : PathIn (tabAt p).2.2) : PathIn tab := match p with
  | .nil => q
  | .loc Y_in tail => .loc Y_in (PathIn.append tail q)
  | .pdl r p_child => .pdl r (PathIn.append p_child q)

/-! ## Parents, Children, Ancestors and Descendants -/

/-- One-step children, with changed type. Use `children` instead. -/
def children' (p : PathIn tab) : List (PathIn (tabAt p).2.2) := match tabAt p with
  | ⟨_, _, ClosedTableau.loc lt _next⟩  =>
      ((endNodesOf lt).attach.map (fun ⟨_, Y_in⟩ => [ .loc Y_in .nil ] )).join
  | ⟨_, _, ClosedTableau.pdl r _ct⟩  => [ .pdl r .nil ]
  | ⟨_, _, ClosedTableau.rep _⟩  => [ ]

/-- List of one-step children, given by paths from the same root. -/
def children (p : PathIn tab) : List (PathIn tab) := (children' p).map (PathIn.append p)

/-- The parent-child relation `s ◃ t` in a tableau -/
def edge {H X} {ctX : ClosedTableau H X} (s : PathIn ctX) (t : PathIn ctX) : Prop :=
  t ∈ children s

/-- Notation ◃ for `edge` (because ⋖ in notes is taken in Mathlib). -/
notation s:arg " ◃ " t:arg => edge s t

/-- Enable "<" notation for transitive closure of ⋖ -/
instance : LT (PathIn tab) := ⟨Relation.TransGen edge⟩

/-- Enable "≤" notation for transitive closure of ⋖ -/
instance : LE (PathIn tab) := ⟨Relation.ReflTransGen edge⟩

@[simp]
def PathIn.head {tab : ClosedTableau Hist X} (_ : PathIn tab) : TNode := X

@[simp]
def PathIn.last (t : PathIn tab) : TNode := (tabAt t).2.1

/-- Convert a path to a History. Does not include the last node. -/
def PathIn.toHistory {tab : ClosedTableau Hist X} : (t : PathIn tab) → History
| .nil => []
| .pdl _ tail => tail.toHistory ++ [X]
| .loc _ tail => tail.toHistory ++ [X]

/-- Convert a path to a list of nodes. Reverse of the history and does include the last node. -/
def PathIn.toList {tab : ClosedTableau Hist X} : (t : PathIn tab) → List TNode
| .nil => [X]
| .pdl _ tail => X :: tail.toList
| .loc _ tail => X :: tail.toList

/-- The length of a path is the number of actual steps. -/
@[simp]
def PathIn.length : (t : PathIn tab) → ℕ
| .nil => 0
| .pdl _ tail => tail.length + 1
| .loc _ tail => tail.length + 1

-- TODO:  length = history length

/-- A path gives the same list of nodes as the history of its last node, reversed. -/
theorem PathIn.toHistory_eq_Hist {tab : ClosedTableau Hist X} (t : PathIn tab) :
    t.toHistory ++ Hist = (tabAt t).1 := by
  induction tab
  all_goals
    cases t <;> simp_all [tabAt, PathIn.toHistory]

theorem PathIn.root_length_eq_Hist.length (tab : ClosedTableau .nil X) (s : PathIn tab) :
    (tabAt s).fst.length = s.toHistory.length := by
  have := PathIn.toHistory_eq_Hist s
  rw [← this]
  simp

def PathIn.isLoaded (t : PathIn tab) : Prop :=
match t with
  | .nil => t.head.isLoaded
  | .pdl _ tail => t.head.isLoaded ∧ tail.isLoaded
  | .loc _ tail => t.head.isLoaded ∧ tail.isLoaded

/-- A path is critical iff the (M) rule is used on it. -/
def PathIn.isCritical (t : PathIn tab) : Prop :=
match t with
  | .nil => False
  | .pdl r _ => match r with
     | .atmL _ _ => True
     | .atmR _ _ => True
     | .atmL' _ _ => True
     | .atmR' _ _ => True
     | _ => False
  | .loc _ tail => tail.isCritical

/-- Prefix of a path, taking only the first `k` steps. -/
def PathIn.prefix {tab : ClosedTableau Hist X} : (t : PathIn tab) → (k : Fin (t.length + 1)) → PathIn tab
| .nil, _ => .nil
| .pdl r tail, k => Fin.cases (.nil) (fun j => .pdl r (tail.prefix j)) k
| .loc Y_in tail, k => Fin.cases (.nil) (fun j => .loc Y_in (tail.prefix j)) k

/-- The list of a prefix of a path is the same as the prefix of the list of the path. -/
theorem PathIn.prefix_toList_eq_toList_take {tab : ClosedTableau Hist X} (t : PathIn tab) (k : Fin (t.length + 1)) :
    (t.prefix k).toList = (t.toList).take (k + 1) := by
  induction tab
  case loc rest Y lt next IH =>
    cases t
    case nil =>
      simp [PathIn.toList, PathIn.prefix]
    case loc Z Z_in tail =>
      simp [PathIn.toList, PathIn.prefix]
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList, PathIn.prefix]
  case pdl =>
    cases t
    case nil =>
      simp_all [PathIn.toList, PathIn.prefix]
    case pdl rest Y Z r tab IH tail =>
      simp [PathIn.toList, PathIn.prefix]
      induction k using Fin.inductionOn <;> simp_all [PathIn.toList, PathIn.prefix]
  case rep =>
    cases t
    simp_all [PathIn.toList, PathIn.prefix]

-- theorem idea : k + j = length → prefix k). append (suffix j) = same ...

/-- Rewinding a path, removing the last `k` steps. Cannot go into Hist.
Used to go to the companion of a repeat. -/
def PathIn.rewind : (t : PathIn tab) → (k : Fin (t.toHistory.length)) → PathIn tab
| .nil, _ => .nil
| .loc Y_in tail, k => Fin.cases (PathIn.loc Y_in tail) (PathIn.loc Y_in ∘ tail.rewind) k
| .pdl r tail, k => Fin.cases (PathIn.pdl r tail) (PathIn.pdl r ∘ tail.rewind) k

/-! ## Companion, ccEdge, cEdge, etc. -/

/-- To get the companion of an LPR node we go as many steps back as the LPR says. -/
def companionOf {X} {tab : ClosedTableau .nil X} (s : PathIn tab) lpr
 (_ : (tabAt s).2.2 = ClosedTableau.rep lpr) : PathIn tab :=
  s.rewind (PathIn.root_length_eq_Hist.length tab s ▸ lpr.val)

/-- s ♥ t means s is a LPR and its companion is t -/
def companion {X} {tab : ClosedTableau .nil X} (s t : PathIn tab) : Prop :=
  ∃ (lpr : _) (h : (tabAt s).2.2 = ClosedTableau.rep lpr),
      t = companionOf s lpr h

notation pa:arg " ♥ " pb:arg => companion pa pb

/-- Successor relation plus back loops: ◃' (MB: page 26) -/
def ccEdge {X} {ctX : ClosedTableau .nil X} (s t : PathIn ctX) : Prop :=
  s ◃ t  ∨  ∃ u, s ♥ u ∧ u ◃ t

notation pa:arg " ⋖ᶜᶜ " pb:arg => ccEdge pa pb

/-- We have: ⋖ᶜ = ⋖ ∪ ♥ -/
example : pa ⋖ᶜᶜ pb ↔ (pa ◃ pb) ∨ ∃ pc, pa ♥ pc ∧ pc ◃ pb := by
  simp_all [ccEdge]

def cEdge {X} {ctX : ClosedTableau .nil X} (t s : PathIn ctX) : Prop :=
  (t ◃ s) ∨ t ♥ s

notation pa:arg " ⋖ᶜ " pb:arg => cEdge pa pb

/-- We have: ⋖ᶜ = ⋖ ∪ ♥ -/
example : pa ⋖ᶜ pb ↔ (pa ◃ pb) ∨ pa ♥ pb := by
  simp_all [cEdge]

/-! ## ≡_E and Clusters -/

-- TODO: how to define the equivalence relation given by E:
-- Use `EqvGen` from Mathlib or manual "both ways Relation.ReflTransGen"?

-- manual
def cEquiv {X} {tab : ClosedTableau .nil X} (pa pb : PathIn tab) : Prop :=
    Relation.ReflTransGen cEdge pa pb
  ∧ Relation.ReflTransGen cEdge pb pa

notation t:arg " ≡_E " s:arg => cEquiv t s

def clusterOf {tab : ClosedTableau .nil X} (p : PathIn tab) := Quot.mk cEquiv p

-- better?
def E_equiv_alternative {tab : ClosedTableau .nil X} (pa pb : PathIn tab) : Prop :=
  EqvGen cEdge pa pb

def clusterOf_alternative {tab : ClosedTableau .nil X} (p : PathIn tab) :=
  Quot.mk E_equiv_alternative p

def simpler {X} {tab : ClosedTableau .nil X}
  (s t : PathIn tab) : Prop := Relation.TransGen cEdge t s ∧ ¬ Relation.TransGen cEdge s t

notation t:arg " ⊏_c " s:arg => simpler t s

theorem eProp (tab : ClosedTableau .nil X) :
    Equivalence (@cEquiv _ tab)
    ∧
    WellFounded (@simpler _ tab) := by
  constructor
  · constructor
    · intro _
      simp [cEquiv]
      exact Relation.ReflTransGen.refl
    · intro _ _
      simp [cEquiv]
      tauto
    · intro s u t
      simp [cEquiv]
      intro s_u u_s u_t t_u
      exact ⟨ Relation.ReflTransGen.trans s_u u_t
            , Relation.ReflTransGen.trans t_u u_s ⟩
  · constructor
    intro s
    -- need to show `Acc` - induction on path `s` maybe?
    unfold simpler
    sorry

theorem eProp2 (tab : ClosedTableau .nil X) (s u t : PathIn tab) :
      (s ◃ t → (t ⊏_c s) ∨ (t ≡_E s)) -- (a)
    ∧ (s ♥ t → t ≡_E s) -- (b)
    ∧ ((nodeAt s).isFree → edge s t → t ⊏_c s) -- (c)
    ∧ ((nodeAt s).isLoaded → (nodeAt t).isFree → edge s t → t ⊏_c s) -- (d)
    ∧ (t ⊏_c u ∧ u ⊏_c s → t ⊏_c s) -- (e)
    ∧ (ccEdge s t ∧ ¬(s ≡_E t)  →  t ⊏_c s) -- (f)
  := by
refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
all_goals
  simp_all [edge, cEdge, ccEdge, cEquiv, simpler, companion]
-- (a)
· intro t_childOf_s
  have s_cEdge_t : TC cEdge s t := by
    apply TC.base
    simp_all [cEdge]
    left
    assumption
  if Relation.TransGen cEdge t s
  then
    right
    constructor
    · apply Relation.TransGen.to_reflTransGen
      assumption
    · apply Relation.ReflTransGen.single
      simp [cEdge]
      left
      exact t_childOf_s
  else
    tauto
-- (b)
·
  sorry
-- (c)
·
  sorry
-- (d)
·
  sorry
-- (e)
·
  sorry
-- (f)
·
  sorry

/-! ## Soundness -/

theorem loadedDiamondPaths {Root Δ : TNode}
  (tab : ClosedTableau .nil Root) -- LoadHistory.nil to prevent repeats from "above"
  (path_to_Δ : PathIn tab)
  (h : Δ = nodeAt path_to_Δ)
  {M : KripkeModel W} {v : W}
  (φ : AnyFormula)
  (negLoad_in : NegLoadFormula_in_TNode (~'⌊α⌋φ) Δ) -- FIXME: ∈ not working here?
  (v_X : (M,v) ⊨ Δ)
  (v_α_w : relate M α v w)
  (w_φ : (M,w) ⊨ ~''φ)
  : ∃ Γ : TNode,
    ∃ path_to_Γ : PathIn tab,
        Γ = nodeAt path_to_Γ
      -- TODO: must be an extension of path_to_Δ
      ∧ (AnyNegFormula_in_TNode (~''φ) Γ) -- FIXME: ∈ not working here?
      ∧ (M,w) ⊨ Γ :=
  by
  have := eProp2 tab
  let ⟨L,R,O⟩ := Δ
  -- by induction on the complexity of α
  cases α
  -- TODO
  all_goals sorry

theorem tableauThenNotSat (tab : ClosedTableau .nil Root) (t : PathIn tab) : ¬satisfiable (nodeAt t) :=
  by
  -- by induction on the well-founded strict partial order ⊏
  apply @WellFounded.induction _ simpler ((eProp tab).2 : _) _ t
  clear t
  intro t IH
  sorry

theorem correctness : ∀LR : TNode, satisfiable LR → consistent LR :=
  by
    intro LR
    contrapose
    unfold consistent
    unfold inconsistent
    simp only [not_nonempty_iff, not_isEmpty_iff, not_exists, not_forall, exists_prop, Nonempty.forall]
    intro hyp
    apply tableauThenNotSat hyp .nil

theorem soundTableau : ∀φ, provable φ → ¬satisfiable ({~φ} : Finset Formula) :=
  by
    intro φ prov
    rcases prov with ⟨tabl⟩|⟨tabl⟩
    exact tableauThenNotSat tabl .nil
    exact tableauThenNotSat tabl .nil

-- See `tableauThenNotSat` for the actual proof of what the notes call soundness.
theorem soundness : ∀φ, provable φ → tautology φ :=
  by
    intro φ prov
    apply notsatisfnotThenTaut
    rw [← singletonSat_iff_sat]
    apply soundTableau
    exact prov
