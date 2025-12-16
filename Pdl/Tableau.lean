import Mathlib.Data.List.ReduceOption

import Pdl.LocalTableau

/-! # PDL-Tableaux (Section 4) -/

open HasLength

/-! ## Projections -/

@[simp]
def formProjection : Nat → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

def projection : Nat → List Formula → List Formula
  | A, X => (X.map fun x => (formProjection A x)).reduceOption

@[simp]
theorem proj : g ∈ projection A X ↔ (⌈·A⌉g) ∈ X :=
  by
  induction X
  case nil =>
    simp only [projection, formProjection, beq_iff_eq, List.map_nil, List.not_mem_nil, iff_false]
    exact List.count_eq_zero.mp rfl
  case cons =>
    simp only [projection, formProjection, beq_iff_eq, List.map_cons, List.mem_cons]
    rw [List.reduceOption_mem_iff]
    aesop

/-! ## Loading and Loaded Histories -/

/-- A history is a list of Sequents.
This only tracks "big" steps, hoping we do not need steps within a local tableau.
The head of the first list is the newest Sequent. -/
abbrev History : Type := List Sequent

/-- We have a repeat iff the history contains a node that is `setEqTo` the current node. -/
def rep (Hist : History) (X : Sequent) : Prop := ∃ Y ∈ Hist, Y.setEqTo X

instance {H X} : Decidable (rep H X) := by
  unfold rep
  induction H
  · apply isFalse; simp_all
  case cons Y YS IH =>
    simp only [List.mem_cons, exists_eq_or_imp]
    exact instDecidableOr

/-- A lpr means we can go `k` steps back in the history to
reach an equal node, and all nodes on the way are loaded.
Note: `k=0` means the first element of `Hist` is the companion. -/
def LoadedPathRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k).multisetEqTo X ∧ ∀ m ≤ k, (Hist.get m).isLoaded)

lemma LoadedPathRepeat.to_rep {Hist X} (lpr : LoadedPathRepeat Hist X) : rep Hist X := by
  rcases lpr with ⟨k, same, all_loaded⟩
  use List.get Hist k
  simp_all only [List.get_eq_getElem, List.getElem_mem, true_and]
  exact Sequent.setEqTo_of_multisetEqTo _ _ same

instance : DecidableEq (LoadedPathRepeat Hist X) := Subtype.instDecidableEq

/-- If there is any loaded path repeat, then we can compute one.
FIXME There is probably a more elegant way, avoiding `Nonempty` and `Fin.find?`.
Something like: def getLPR (H : History) (X : Sequent) : Option ... := ...
that might also give us uniqueness of LPRs? -/
def LoadedPathRepeat.choice {H X} (ne : Nonempty (LoadedPathRepeat H X)) :
    LoadedPathRepeat H X := by
  let somek := @Fin.find? (H.length)
    (fun k => (H.get k).multisetEqTo X ∧ ∀ m ≤ k, (H.get m).isLoaded = true)
  rcases find_def : somek with _|⟨k⟩
  · exfalso
    rw [Fin.find?_eq_none_iff] at find_def
    rcases ne with ⟨⟨k,bla⟩⟩
    specialize find_def k
    aesop
  · refine ⟨k, ?_⟩
    rw [Fin.find?_eq_some_iff] at find_def
    aesop

theorem LoadedPathRepeat_comp_isLoaded {Hist X} (lpr : LoadedPathRepeat Hist X) :
    (Hist.get lpr.val).isLoaded := by
  rcases lpr with ⟨j, claim⟩
  apply claim.2 j (le_refl j)

theorem LoadedPathRepeat_rep_isLoaded {Hist X} (lpr : LoadedPathRepeat Hist X) : X.isLoaded := by
  rcases lpr with ⟨k, claim⟩
  rw [← multisetEqTo_isLoaded_iff claim.1]
  exact claim.2 k (le_refl k)

instance {H X} : Decidable (Nonempty (LoadedPathRepeat H X)) := by
  by_cases ∃ k, (H.get k).multisetEqTo X ∧ ∀ m ≤ k, (H.get m).isLoaded
  case pos h =>
    apply isTrue
    rcases h with ⟨k, same, all_le_loaded⟩
    exact ⟨k, same, all_le_loaded⟩
  case neg h =>
    apply isFalse
    simp only [not_nonempty_iff]
    constructor
    rintro ⟨k, same, all_le_loaded⟩
    push_neg at h
    specialize h k same
    aesop

/-! ## The PDL rules -/

/-- A rule to go from `X` to `Y`. Note the four variants of the modal rule. -/
@[grind]
inductive PdlRule : (X : Sequent) → (Y : Sequent) → Type
  -- The (L+) rule:
  | loadL {L δ α φ Y R} : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ L → ¬ φ.isBox
      → Y = (L.erase (~⌈⌈δ⌉⌉⌈α⌉φ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋φ)))) → PdlRule (L, R, none) Y
  | loadR {R δ α φ Y L} : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ R → ¬ φ.isBox
      → Y = (L, R.erase (~⌈⌈δ⌉⌉⌈α⌉φ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋φ)))) → PdlRule (L, R, none) Y
  -- The (L-) rule:
  | freeL {X L R δ α φ Y} :
        X = (L, R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
      → Y = (L.insert (~⌈⌈δ⌉⌉⌈α⌉φ), R, none)
      → PdlRule X Y
  | freeR {X L R δ α φ Y} :
        X = (L, R, some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
      → Y = (L, R.insert (~⌈⌈δ⌉⌉⌈α⌉φ), none)
      → PdlRule X Y
  -- The (M) rule:
  | modL {Y L R A X ξ} :
        X = ⟨L, R, some (Sum.inl (~'⌊·A⌋(ξ : AnyFormula)))⟩
      → Y = ( match ξ with | .normal φ => ⟨(~φ) :: projection A L, projection A R, none⟩
                           | .loaded χ => ⟨projection A L, projection A R, some (Sum.inl (~'χ))⟩ )
      → PdlRule X Y
  | modR {Y L R A X ξ} :
        X = ⟨L, R, some (Sum.inr (~'⌊·A⌋(ξ : AnyFormula)))⟩
      → Y = ( match ξ with | .normal φ => ⟨projection A L, (~φ) :: projection A R, none⟩
                           | .loaded χ => ⟨projection A L, projection A R, some (Sum.inr (~'χ))⟩ )
      → PdlRule X Y
deriving DecidableEq

def PdlRule.isModal {X Y} : PdlRule X Y → Prop
| .loadL _ _ _ => False
| .loadR _ _ _ => False
| .freeL _ _ => False
| .freeR _ _ => False
| .modL _ _ => True
| .modR _ _ => True

/--
The `Tableau [parent, grandparent, ...] child` type.

A closed tableau for X is either of:
- a local tableau for X followed by closed tableaux for all end nodes,
- a PDL rule application
- a successful loaded repeat (MB condition six)
-/
inductive Tableau : History → Sequent → Type
  | loc {X} (nrep : ¬ rep Hist X) (nbas : ¬ X.basic) (lt : LocalTableau X)
            (next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y) : Tableau Hist X
  | pdl {X Y} (nrep : ¬ rep Hist X) (bas : X.basic) (r : PdlRule X Y)
              (next : Tableau (X :: Hist) Y) : Tableau Hist X
  | lrep {X Hist} (lpr : LoadedPathRepeat Hist X) : Tableau Hist X

def Tableau.size {Hist X} : Tableau Hist X → Nat
  | .loc _ _ lt next => 1 + ((endNodesOf lt).attach.map (fun ⟨Y, Y_in⟩ => (next Y Y_in).size)).sum
  | .pdl _ _ _ next => 1 + next.size
  | .lrep _ => 1

lemma Tableau.size_next_lt_of_loc
    (tab_def : tab = Tableau.loc nrep nbas lt next) Y Y_in
    : (next Y Y_in).size < tab.size := by
  subst tab_def
  simp only [size]
  rw [@Nat.lt_one_add_iff]
  apply List.le_sum_of_mem
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
  use Y, Y_in

lemma Tableau.size_next_lt_of_pdl
    (tab_def : tab = Tableau.pdl nrep bas r next)
    : next.size < tab.size := by
  simp_all [Tableau.size]

instance instDecidableExistsEndNodeOf {X} {lt : LocalTableau X}
    {f : (Y : Sequent) → Y ∈ endNodesOf lt → Prop}
    {dec : (Y : Sequent) → (Y_in : Y ∈ endNodesOf lt) → Decidable (f Y Y_in)} :
    Decidable (∃ Y, ∃ Y_in : Y ∈ endNodesOf lt, f Y Y_in) := by
  if h : (endNodesOf lt).attach.any (fun ⟨Y,Y_in⟩ => decide (f Y Y_in)) then
    apply isTrue
    aesop
  else
    apply isFalse
    aesop

instance Tableau.instDecidableEq {Hist X} {tab1 tab2 : Tableau Hist X} :
    Decidable (tab1 = tab2) := by
  rcases tab1_def : tab1 with (⟨nrep1,nbas1,lt1,next1⟩|@⟨_,X2,Y2,nrep2,bas2,r2,next2⟩|_)
  all_goals
    rcases tab2 with (⟨nrep2,nbas2,lt2,next2⟩|@⟨_,X1,Y1,nrep1,bas1,r1,next1⟩|_)
  · by_cases h : lt1 = lt2
    · subst h
      simp only [loc.injEq, heq_eq_eq, true_and]
      have := fun (Y : Sequent) (Y_in : Y ∈ endNodesOf lt1) =>
        @Tableau.instDecidableEq _ _ (next1 Y Y_in) (next2 Y Y_in)
      have : Decidable (∃ Y, ∃ Y_in : Y ∈ endNodesOf lt1, next1 Y Y_in ≠ next2 Y Y_in) := by
        apply instDecidableExistsEndNodeOf
        intro Y Y_in
        simp only [ne_eq]
        exact @instDecidableNot _ (this Y Y_in)
      by_cases ∃ Y, ∃ Y_in : Y ∈ endNodesOf lt1, next1 Y Y_in ≠ next2 Y Y_in
      · apply isFalse; aesop
      · apply isTrue; aesop
    · apply isFalse; aesop
  all_goals
    simp_all only [reduceCtorEq, pdl.injEq, lrep.injEq]
  case pdl.pdl =>
    by_cases h : Y1 = Y2
    · subst h
      simp_all only [not_false_eq_true, heq_eq_eq, true_and]
      by_cases h : r2 = r1
      · subst h
        simp only [true_and]
        apply Tableau.instDecidableEq
      · apply isFalse
        tauto
    · apply isFalse
      tauto
  all_goals
    infer_instance
termination_by
  -- Note: cannot use DM ordering here, because PDL rules (L+) and (L-) do not decrease it.
  tab1.size
decreasing_by
  · exact Tableau.size_next_lt_of_loc tab1_def Y Y_in
  · exact Tableau.size_next_lt_of_pdl tab1_def

def Tableau.isLrep {Hist X} : (Tableau Hist X) → Prop
  | .loc .. => False
  | .pdl .. => False
  | .lrep .. => True

inductive provable : Formula → Prop
  | byTableauL {φ : Formula} : Tableau .nil ⟨[~φ], [], none⟩ → provable φ
  | byTableauR {φ : Formula} : Tableau .nil ⟨[], [~φ], none⟩ → provable φ

/-- A Sequent is inconsistent if there exists a closed tableau for it. -/
def inconsistent : Sequent → Prop
  | LR => Nonempty (Tableau .nil LR)

/-- A `Sequent` is consistent iff it is not inconsistent. -/
def consistent : Sequent → Prop
  | LR => ¬inconsistent LR
