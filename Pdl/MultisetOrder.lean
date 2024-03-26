import Mathlib.Tactic.Linarith
import Mathlib.Data.Multiset.Basic
import Mathlib.Logic.Relation

-- Dershowitz-Manna ordering for Lists
-- It is usually defined on multisets, but works for lists too because
-- count, i.e. number of occurrences, is invariant under permutation.

-- This is the standard definition ...
-- originally formalized in Lean 3 by Pedro Minicz
-- https://gist.github.com/b-mehta/ee89376db987b749bd5120a2180ce3df
@[simp]
def dm' (α) := List α
@[simp]
def to_dm' {α} (s : List α) : dm' α := s
@[simp]
instance {α : Type u} [DecidableEq α] [LT α] : LT (dm' α) :=
  { lt := λ M N =>
    ∃ (X Y : List α),
      X ≠ ∅
      ∧ (X : List α) ≤ (N : List α)
      ∧ M = (N.diff X) ++ Y
      ∧ ∀ y ∈ Y, ∃ x ∈ X, y < x }
--
-- ... but we use the alternative by Huet and Oppen:
@[simp]
def dm (α) := List α
@[simp]
def to_dm {α} (s : List α) : dm α := s
@[simp]
instance {α : Type u} [DecidableEq α] [LT α] : LT (dm α) :=
  { lt := λ M N =>  -- M < N iff ...
      M ≠ N
    ∧ ∀ ψ_y, -- for all y
      M.count ψ_y > N.count ψ_y → -- M(y) > N(y) implies there is an x > y
        ∃ ψ_x, ψ_y < ψ_x ∧ M.count ψ_x < N.count ψ_x } -- M(x) < N(x)

-- Yet another definition of multiset ordering. This is the one used by coq CoLoR library.
@[simp]
def mul (α) := List α
@[simp]
def to_mul {α} (s : List α) : mul α := s
@[simp]
instance {α : Type u} [DecidableEq α] [Membership α (mul α)]: Membership α (mul α) :=
{ mem := λ a s => a ∈ to_mul s }

@[simp]
instance {α : Type u} [DecidableEq α] [LT α] : LT (mul α) :=
  { lt := λ M N =>  -- M < N iff ...
    ∃ (X Y Z: List α),
      X ≠ ∅
      ∧ M = Z ++ Y
      ∧ N = Z ++ X
      ∧ ∀ y ∈ Y, ∃ x ∈ X, y < x } -- For the different part, each of X's element is smaller than some Y's element.

-- TODO: Prove the equivalence of the definitions.

-- The standard result about the Dershowitz–Manna ordering.
-- Someone should get this into Mathlib.

theorem wf_mul {α : Type u} [DecidableEq α] [LT α]
    (t :  WellFoundedLT α) :
    WellFounded ((LT.lt) : Multiset α → Multiset α → Prop) := by
  apply WellFounded.intro
  intro dma
  apply Acc.intro dma
  intro dmb h
  sorry

-- theorem mOrd_acc {α : Type u} : ∀ M : mul (α), (∀ x : α, Membership.mem x (mul α)) -> Acc ltA _) -> Acc _ _ := by
--   sorry

theorem wf_dm {α : Type u} [DecidableEq α] [LT α]
    (t :  WellFoundedLT α) :
    WellFounded ((LT.lt) : dm α → dm α → Prop) := by
  apply WellFounded.intro
  intro dma
  apply Acc.intro dma
  intro dmb h
  apply _
  intros
  sorry

instance [DecidableEq α] [LT α] (t : WellFoundedLT α) : IsWellFounded (dm α) (LT.lt) := by
  constructor
  exact wf_dm t













-- Haitian's translation of the proof from coq
-- inductive MultisetRedGt : multiset α → multiset α → Prop
-- | MSetRed : ∀ (X : multiset α) (a : α) (Y : multiset α),
--     ∀ {A B : multiset α},
--     A = X + {a} →
--     B = X + Y →
--     (∀ y, y ∈ Y → a > y) →
--     MultisetRedGt A B

-- inductive MultisetRedGt (A B : multiset α) : Prop
-- | MSetRed : ∀ X a Y,
--     A = X + {a} →
--     B = X + Y →
--     (∀ y, y ∈ Y → a > y) →
--     MultisetRedGt A B

inductive MultisetRedLt [DecidableEq α][LT α] (M N: Multiset α) : Prop :=
| RedLt : ∀ (X Y:Multiset α) (a : α) ,
       (M = X + Y) →
       (N = X + {a}) →
       (∀ y, y ∈ Y → y < a) → MultisetRedLt M N

theorem not_MultisetRedLt_0 [DecidableEq α][LT α] (M: Multiset α) : ¬ (MultisetRedLt M 0) := by
  intro h
  cases h with
  | RedLt X Y a M nonsense _ =>
    have contra : a ∈ (0 : Multiset α):= by
      rw [nonsense]
      aesop
    contradiction
  -- unfold MultisetRedLt at m0
  -- but this would mean 0 = X + {a}, which is impossible.

def MultisetLt [DecidableEq α][LT α] : Multiset α → Multiset α → Prop :=
TC MultisetRedLt

def MultisetLt' [DecidableEq α][LT α] : Multiset α → Multiset α → Prop :=
Relation.TransGen MultisetRedLt

inductive MultisetLT {α} [DecidableEq α] [Preorder α] : (M : Multiset α) → (N : Multiset α) → Prop :=
  | MLT : ∀ (X Y Z: Multiset α),
        Y ≠ ∅ →
        M = Z + X →
        N = Z + Y →
        (∀ x ∈ X, ∃ y ∈ Y, x < y) → MultisetLT M N

-- variable {A : Type u} [DecidableEq A] [LT A] (ltA : A → A → Prop)
-- def ltA {A : Type u} [DecidableEq A] [LT A]  : A → A → Prop := let
-- def AccA : (A → Prop) := Acc ltA

#check Acc
-- #check AccA
-- instance [DecidableEq A] : DecidableEq A := by
--   apply inst
def ACC_M [DecidableEq α][Preorder α] : Multiset α → Prop := Acc MultisetLT
def AccM [DecidableEq α][Preorder α] : Multiset α → Prop := Acc MultisetLt
def AccM_1 [DecidableEq α][Preorder α] : Multiset α → Prop := Acc MultisetRedLt


#check MultisetLT
#check ACC_M

theorem nonsense {α : Type u} : ∀ x : α, ∀ M : Multiset (α), x ∈ M := by sorry


def X_mul : (Multiset ℕ) := {1,1,2}
def Y_mul : (Multiset ℕ) := {1,2,1}
def Z_mul : (Multiset ℕ) := {1,2}
def W_mul : (Multiset ℕ) := {1}
def A_mul : (Multiset ℕ) := {1,3}

#eval X_mul = Y_mul
#eval X_mul = Z_mul
#eval X_mul = Z_mul + W_mul
#eval 1 ∈ X_mul
-- The first one gives true: permutation invariant
-- The second one gives false: duplicates do matter
-- The third one gives true: `+` operation is working for Multisets
-- The fourth one gives true: `∈` operation is working for Multisets



-- def MultisetLT {α : Type u} [DecidableEq α][LT α](M : Multiset α) (N : Multiset α) : Prop :=
--   ∃ (X Y Z: Multiset α),
--         X ≠ ∅
--         ∧ M = Z + Y
--         ∧ N = Z + X
--         ∧ ∀ y ∈ Y, ∃ x ∈ X, y < x


-- This is the crucial lemma. The rest just showing different definitions of relations are equivalent.
-- And the real crucial part seems to be an existing lemma in coq (Transitive_Closure.Acc_clos_trans) which says that the transitive closure of a well-founded relation is also well-founded.
-- The corresponding lemma in Lean is:
#check TC.wf






lemma mord_acc [DecidableEq α] [Preorder α] : ∀ M : Multiset α, (∀ x, x ∈ M -> Acc LT.lt x) → AccM M := by
  intros
  unfold AccM
  unfold MultisetLt
  sorry


lemma mord_acc_mOrd_acc [DecidableEq α] [Preorder α] : ∀ X:Multiset α, AccM X → ACC_M X := by sorry


-- It uses `mord_acc_mOrd_acc` and `mord_acc`, which still need to be proved.
lemma mOrd_acc  [DecidableEq α] [Preorder α]: ∀ (M: Multiset α), (∀ x:α, (x ∈ M) →  (Acc LT.lt x)) → (ACC_M M) := by
  intros
  apply mord_acc_mOrd_acc
  apply mord_acc
  assumption

  -- Proof.
  --   intros.
  --   apply mord_acc_mOrd_acc.
  --   apply mord_acc; trivial.
  -- Qed.

-- theorem helper {α : Type u} [DecidableEq α] [LT α]
-- (wf_lt :  WellFoundedLT α) (x : α) : Acc LT.lt x := by
--   apply wf_lt.induction x
--   intro y h
--   exact Acc.intro y h

-- This is the desired theorem
-- It uses `mOrd_acc`, which still needs to be proved.
theorem mord_wf {α : Type u} [DecidableEq α] [Preorder α]
    (wf_lt :  WellFoundedLT α) :
    WellFounded (MultisetLT : Multiset α → Multiset α → Prop) := by
    apply WellFounded.intro
    intro dma
    apply Acc.intro dma
    intro dmb _
    apply mOrd_acc
    intro x _
    apply wf_lt.induction x
    intro y h
    apply Acc.intro y
    exact h
    -- apply helper
    -- assumption




-- Assuming the necessary context
variables {A B : Type} {R : A → A → Prop} {T : B → B → Prop}
variables {morphism : A → B → Prop}

theorem acc_homo (h : ∀ (x y : B) (x' : A), morphism x' x → T y x → ∃ (y' : A), R y' x' ∧ morphism y' y) :
  ∀ (x : A), Acc R x → ∀ (x' : B), morphism x x' → Acc T x' := by sorry
  -- intros x h_acc_x
  -- induction h_acc_x with x acc_x ih
  -- intros x' h_morphism,

  -- apply acc.intro x',
  -- intros y h_T_y_x',
  -- cases h x' h_morphism with y' h_R_y'_x' h_morphism_y'_y,
  -- exact ih y' h_R_y'_x' _ h_T_y_x' h_morphism_y'_y,

















-- Haitian's own attempt


#eval 1 ::ₘ {1,2} = {2} + {1,1}
#eval Multiset.erase {1,2} 1 = {1,2} - {1}

-- the conjunction operator takes precedence over the disjunction operator, so that p ∧ q ∨ r means (p ∧ q) ∨ r rather than p ∧ (q ∨ r)

lemma meq_union_meq : ∀ {α : Type u} [DecidableEq α] [Preorder α] {M N P : Multiset α},
      M + P = N + P →
            M = N := by aesop

lemma meq_union_meq_reverse : ∀ {α : Type u} [DecidableEq α] [Preorder α] {M N P : Multiset α},
      M = N →
            M + P = N + P := by aesop

@[simp]
lemma mul_cons_trivial : ∀ {α : Type u} [DecidableEq α] [LT α] {a : α} {M : Multiset α},
       M + {a} = a ::ₘ M := by
      intros
      ext
      simp [Multiset.count_cons, Multiset.count_singleton, Multiset.count_add]

@[simp]
lemma mul_erase_trivial : ∀ {α : Type u} [DecidableEq α] [LT α] {a : α} {M : Multiset α},
       M - {a} = Multiset.erase M a := by
       intros
       ext
       simp [Multiset.erase_singleton]
       simp [Multiset.count_cons, Multiset.count_singleton, Multiset.count_add]
       aesop
      --  simp [mset_sub, Multiset.erase]

lemma mul_mem_not_erase : ∀ {α : Type u} [DecidableEq α] [LT α] {a a0: α} {M X : Multiset α},
      M = Multiset.erase (a0 ::ₘ X) a → ¬ a = a0 → a0 ∈ M := by
      intros _ _ _ a a0 M X H hyp
      rw [H]
      have : a0 ∈ Multiset.erase (a0 ::ₘ X) a ↔ a0 ∈ (a0 ::ₘ X) := by
        apply Multiset.mem_erase_of_ne
        aesop
      rw [this]
      aesop

lemma mem_erase_cons : ∀ {α : Type u} [DecidableEq α] [LT α] {a0: α} {M : Multiset α},
      a0 ∈ M → M = M - {a0} + {a0} := by
      aesop?

lemma neq_negeq1 : ¬ a0 = a → a0 ≠ a := by aesop

lemma neq_negeq2 : ¬ a = a0 → a0 ≠ a := by aesop

lemma neq_erase : ∀ {α : Type u} [DecidableEq α] [LT α] {a a0: α} (M : Multiset α)(h: a0 ≠ a), Multiset.count a0 (Multiset.erase M a) = Multiset.count a0 M := by
  intros _ _ _ a a0 M h
  have : Multiset.count a0 (a ::ₘ (Multiset.erase M a)) = Multiset.count a0 (a ::ₘ M) := by aesop
  aesop

lemma cons_erase : ∀ {α : Type u} [DecidableEq α] [LT α] {a a0: α} {M X : Multiset α},
      a ::ₘ M = X + {a0} → M = X + {a0} - {a} := by
      intros α _ _ a a0 M X H
      if hyp : a = a0 then
        aesop
      else
        have a0_a: a0 ≠ a := by apply neq_negeq2 hyp
        ext b
        simp [Multiset.count_cons, Multiset.count_singleton, Multiset.count_add]
        have H : Multiset.count b (a ::ₘ M) = Multiset.count b (X + {a0}) := by aesop
        if ba : b = a then

          rw [ba]
          rw [ba] at H
          have : a ∈ X + {a0} := by
            by_contra h
            have absurd3 : Multiset.count a (a ::ₘ M) > 0 := by simp
            aesop
          have : Multiset.count a (a ::ₘ M) = Multiset.count a M + 1 := by simp
          have : Multiset.count a (a0 ::ₘ X) = Multiset.count a (Multiset.erase (a0 ::ₘ X) a) + 1 := by simp ; aesop
          aesop
        else if ba0 : b = a0 then
          rw [ba0]
          rw [ba0] at H
          -- have this1: Multiset.count a0 (Multiset.erase (a ::ₘ M) a) = Multiset.count a0 (Multiset.erase (a0 ::ₘ X) a) := by
          --   have : M = Multiset.erase (a ::ₘ M) a := by
          --     simp
          --   simp
          --   have this1: Multiset.count a0 M = Multiset.count a0 (a ::ₘ M) := by
          --     rw [Multiset.count_cons_of_ne a0_a M]
          --   have this2: Multiset.count a0 (Multiset.erase (a0 ::ₘ X) a) = Multiset.count a0 (X + {a0}) := by
          --     --rw [Multiset.count_cons_of_ne this M]
          --     have this3: Multiset.count a0 (Multiset.erase (a0 ::ₘ X) a) = Multiset.count a0 (a0 ::ₘ X) := by
          --       -- simp

          --       rw [neq_erase (a0 ::ₘ X) a0_a]
          --     rw [this3]
          --     simp
          --   rw [this1]
          --   rw [this2]
          --   -- aesop (maximum recursion depth) Ask Malvin about this.
          --   exact H
          have : Multiset.count a0 (Multiset.erase (a ::ₘ M) a) = Multiset.count a0 (Multiset.erase (a ::ₘ M) a) := by
            simp
          have : Multiset.count a0 (a ::ₘ M) = Multiset.count a0 X + 1 := by aesop
          have : Multiset.count a0 M = Multiset.count a0 (a ::ₘ M) := by
            have : a0 ≠ a := by aesop
            rw [Multiset.count_cons_of_ne this M]
          aesop
          -- have : Multiset.count a0 (a ::ₘ M) = Multiset.count a0 M := by aesop
          else
          have : Multiset.count b M = Multiset.count b (a ::ₘ M) := by
            have : b ≠ a := by aesop
            -- have : ∀s, Multiset.count a s = Multiset.count a (b ::ₘ s) := by
            rw [Multiset.count_cons_of_ne this M]
          rw [this ]
          have : Multiset.count b (X + {a0}) = Multiset.count b (Multiset.erase (a0 ::ₘ X) a) := by
            simp
            aesop
          aesop

#check Multiset.count_cons_of_ne
       -- may need case distinction here on whether a = a0

lemma red_insert : ∀ {α : Type u} [DecidableEq α] [LT α] {a : α} {M N : Multiset α},
      MultisetRedLt N (a ::ₘ M) →
      ∃ (M' : Multiset α),
          N = (a ::ₘ M') ∧ MultisetRedLt M' M
        ∨ N = M + M' ∧ (∀ x : α, x ∈ M' → x < a) := by
        intros _ _ _ a M N H
        rcases H with ⟨X, Y, a0, H1, H0, H2⟩
        -- cases h : (decide (a = a0))
        if hyp : a = a0 then
          --subst hyp  (this would remove hyp)
           exists Y; right; apply And.intro
           . rw [H1]
             rw [add_left_inj]
             rw [mul_cons_trivial] at H0
             aesop
           . aesop
        else
          exists (Y + (M - {a0}))
          left
          constructor --; apply And.intro
          . rw [H1]
            have : X = (M - {a0} + {a}) := by
              simp at *
              ext b
              rw [Multiset.count_cons]
              simp [Multiset.ext, Multiset.count_cons] at H0
              if h : b = a then
                rw [h]
                have := H0 b
                aesop
              else
                have := H0 b
                aesop
            subst this
            rw [add_comm]
            aesop
          . constructor
            · change Y + (M - {a0}) = (M - {a0}) + Y
              rw [add_comm]
            · change M = M - {a0} + {a0}
              have this0: M = X + {a0} - {a} := by apply cons_erase ; exact H0
              have a0M: a0 ∈ M := by
                apply mul_mem_not_erase
                . change M = Multiset.erase (a0 ::ₘ X) a
                  rw [mul_erase_trivial] at this0
                  rw [mul_cons_trivial] at this0
                  exact this0
                . exact hyp
              apply mem_erase_cons
              . exact a0M
            exact H2

lemma mord_wf_1 {α : Type u} {_ : Multiset α} [DecidableEq α] [Preorder α] :
    ∀ (a : α) (M0 : Multiset α),
    (∀ b (M : Multiset α), LT.lt b a → AccM_1 M → AccM_1 (b ::ₘ M)) →
    AccM_1 M0 →
    (∀ M, MultisetRedLt M M0 → AccM_1 (a ::ₘ M)) →
    AccM_1 (a ::ₘ M0) := by
       intros a M0 H1 H2 H3
       constructor
       intros N N_lt
       change AccM_1 N
       rcases (red_insert N_lt) with ⟨x, H, H0⟩
       case h.intro.inr h =>
        rcases h with ⟨H, H0⟩
        rw [H]
        clear H --It is weired that removing this line cause aesop to not be able to prove it. Even though it reports after `exhaustive` search?
        induction x using Multiset.induction with
        | empty =>
          aesop
        | cons h =>
          rename_i _ _ a0 M
          have trivial: M0 + a0 ::ₘ M= a0 ::ₘ (M0 + M) := by aesop
          rw [trivial]
          aesop
       case h.intro.inl.intro =>
        aesop


lemma mord_wf_2 {α : Type u} {M : Multiset α} [DecidableEq α] [Preorder α] :
  ∀ (a : α),
  (∀ (b : α), ∀ (M : Multiset α), LT.lt b a → AccM_1 M → AccM_1 (b ::ₘ M)) →
  ∀ M, AccM_1 M → AccM_1 (a ::ₘ M) := by
    unfold AccM_1
    intros _ H M H0
    induction H0 with
    | intro x wfH wfH2 =>
      apply mord_wf_1
      . aesop
      . intros b x a
        unfold AccM_1
        apply H
        assumption
      . constructor
        aesop
      . aesop


lemma mord_wf_3 {α : Type u} {_ : Multiset α} [DecidableEq α] [Preorder α] :
  ∀ (a:α), Acc LT.lt a → ∀ (M : Multiset α), AccM_1 M → AccM_1 (a ::ₘ M) := by
  intro w w_a
  induction w_a with
  | intro x _ ih =>
      intro M accM1
      apply @mord_wf_2 α M _ _ _ _ _ accM1
      simp_all

-- Acc_ind =
-- fun (A : Type) (R : A -> A -> Prop) (P : A -> Prop)
--   (f : forall x : A, (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) =>
-- fix F (x : A) (a : Acc R x) {struct a} : P x :=
--   match a with
--   | Acc_intro _ a0 => f x a0 (fun (y : A) (r : R y x) => F y (a0 y r))
--   end
--      : forall (A : Type) (R : A -> A -> Prop) (P : A -> Prop),
--        (forall x : A, (forall y : A, R y x -> Acc R y) -> (forall y : A, R y x -> P y) -> P x) -> forall x : A, Acc R x -> P x

-- Arguments Acc_ind [A]%type_scope [R]%function_scope (P f)%function_scope [x] a

def Acc_ind {A : Type u} {R : A → A → Prop} {P : A → Prop} (f : ∀ (x : A), (∀ (y : A), R y x → Acc R y) → (∀ (y : A), R y x → P y) → P x) (x : A) (h : Acc R x) : P x := by
  induction h with
  | intro =>
  apply f
  . assumption
  . assumption



#check Multiset.induction_on

-- TODO1:
-- The `lt_wf` to `Lt_wf` turns out to be unnecessary.
-- If all elements of a multiset M is accessible given the underlying relation `LT.lt`, then the multiset M is accessible given the `MultisetRedLt` relation.
-- It uses `not_MultisetRedLt_0` (proved) and `mord_wf_3` (not proved yet).
lemma mred_acc {α : Type u} [DecidableEq α] [Preorder α] :
      ∀ (M : Multiset α), (∀x, x ∈ M → Acc LT.lt x) → AccM_1 M  := by
      intros M wf_el
      induction M using Multiset.induction_on with -- In Coq: mset_ind : forall P : Multiset -> Prop, P empty -> (forall (M : Multiset) (a : A), P M -> P (M + {{a}})) -> forall M : Multiset, P M
      | empty =>
        constructor
        intro y y_lt
        absurd y_lt
        apply not_MultisetRedLt_0
      | cons ih =>
        apply mord_wf_3
        . assumption
        . apply wf_el
          aesop
        . apply ih
          intros
          apply wf_el
          aesop

-- If `LT.lt` is well-founded, then `MultisetRedLt` is well-founded.
-- lemma `mred_acc` needed.
lemma RedLt_wf {α : Type u} [DecidableEq α] [Preorder α]
      (wf_lt : WellFoundedLT α) : WellFounded (MultisetRedLt : Multiset α → Multiset α → Prop) := by
      constructor
      intros a
      apply mred_acc
      intros x _
      apply wf_lt.induction x
      intros y h
      apply Acc.intro y
      assumption

-- If `MultisetRedLt` is well-founded, then its transitive closure, namely `MultisetLt` is also well-founded.
lemma Lt_wf [DecidableEq α] [LT α]
      (h : WellFounded (MultisetRedLt : Multiset α → Multiset α → Prop)) :
      WellFounded (MultisetLt : Multiset α → Multiset α → Prop) := by
      unfold MultisetLt
      apply TC.wf
      assumption









































-- TODO2:
-- The relation `MultisetLt` is equivalent to `MultisetLT`.
-- This one is a bit tricky to prove at the moment. Maybe stick to Coq's proof to prove `mord_acc_mOrd_acc` first? But that also requires similar proofs. I think we could just prove this straight.
-- I didn't expect this part to be hard.

-- def X_mul : (Multiset ℕ) := {1,1,2}
-- def Y_mul : (Multiset ℕ) := {1,2,1}
-- def Z_mul : (Multiset ℕ) := {1,2}
-- def W_mul : (Multiset ℕ) := {1}
-- def A_mul : (Multiset ℕ) := {1,3}

#print MultisetLt
#print MultisetRedLt
#print MultisetLT
#eval Multiset.inter {0,1} {1} = {1}
#eval Z_mul - A_mul = {2}

lemma mul_geq_zero [DecidableEq α] [LT α] : ∀ (M : Multiset α), M ≥ 0 := by
  intro M
  rcases M
  aesop?

notation M:arg " <_DM " N:arg => MultisetLT M N
notation M:arg " ≤_DM " N:arg => MultisetLT M N ∨ M = N
notation M:arg " ≥_DM " N:arg => MultisetLT N M ∨ M = N

-- lemma mul_not_lower_zero [DecidableEq α] [Preorder α] : ∀ (M : Multiset α), ¬ M <_DM 0 := by
--       intro M
--       have M_geq_0: M ≥ 0 := Multiset.zero_le M
--       by_contra M_le_0
--       rw [ge_iff_le] at *

--       sorry

-- This is not true in general: See counterexample below!
lemma WRONG_list_count_subset_le [DecidableEq α] [LT α] : ∀ (N M : List α), N ⊆ M →  List.count a N ≤ List.count a M := by
  intros N M h
  if H : a ∈ N then
    have : a ∈ M := by aesop
    have : List.count a N = 1 := by sorry
    sorry
  else aesop

#eval [1,1] ⊆ [1,2]
#eval List.count 1 [1,1] ≤ List.count 1 [1,2]

--This is also not true in general
lemma WRONG_mem_sub_diff [DecidableEq α] [LT α] : ∀ (M N: Multiset α), N ⊆ M → M = M - N + N := by
  intros M N h
  ext a
  simp
  have H: Multiset.count a N ≤ Multiset.count a M := by
    rcases N with ⟨Ns⟩
    rcases M with ⟨Ms⟩
    simp at *
    apply WRONG_list_count_subset_le
    exact h
  rcases N with ⟨Ns⟩
  rcases M with ⟨Ms⟩
  simp at *
  rw [Nat.sub_add_cancel]
  exact H

-- lemma list_count_subset_le [DecidableEq α] [LT α] : ∀ (a : α) (N M : List α), N ≤ M →  List.count a N ≤ List.count a M := by
--   intros a N M h
--   if H : a ∈ N then
--     sorry
--   else aesop

-- lemma mem_leq_diff [DecidableEq α] [LT α] : ∀ (M N: Multiset α), N ≤ M → M = M - N + N := by
--   intros M N h
--   -- induction N
--   simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, add_tsub_cancel_of_le] -- Does not work here? --Ask Malvin.
--   ext a
--   simp
--   have H: Multiset.count a N ≤ Multiset.count a M := by

--     rcases N with ⟨Ns⟩
--     rcases M with ⟨Ms⟩
--     simp at *
--     apply list_count_subset_le
--     sorry
--   sorry

lemma mem_leq_diff [DecidableEq α] [Preorder α] : ∀ (M N: Multiset α), N ≤ M → M = M - N + N := by
  intros M N h
  rw [← Multiset.union_def]
  rw [Multiset.eq_union_left]
  exact h

lemma obvious {α} [pre : Preorder α] :  ∀ {a b c : α},
  a < b → b < c → a < c := by
  apply @lt_trans α pre

lemma le_sub_add {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (M N P : Multiset α) , N ≤ M → M - N + P = M + P - N  := by
        intro M N P h
        have : M - N + P + N = M + P - N + N := by
          have : M - N + P + N = M - N + N + P := by
            have : M - N + P + N = M - N + (P + N) := by
              apply add_assoc (M - N)
            rw [this]
            have : M - N + N + P = M - N + (N + P) := by apply add_assoc (M - N)
            rw [this]
            have : P + N = N + P := by apply add_comm P N
            simp_all only [ge_iff_le]
          rw [this]
          have : M + P - N + N = M + P := by
            have : M + P - N + N = (M + P) ∪ N := by apply Eq.refl
            have : (M + P) ∪ N = M + P:= by
              apply Multiset.eq_union_left
              have : M ≤ M + P := by simp_all only [ge_iff_le, le_add_iff_nonneg_right, zero_le]
              apply le_trans h this
            simp_all only [ge_iff_le]
          rw [this]
          have : M - N + N = M := by
            have : M = M - N + N := by
              apply mem_leq_diff
              exact h
            rw [← this]
          simp_all only [ge_iff_le]
        simp_all only [ge_iff_le, add_left_inj]

lemma le_eq_sub : ∀ (M N P Q : ℕ) , M ≤ P → M + N = P + Q → N = Q + (P - M):= by
  intros M N P Q h0 h1
  have := tsub_add_cancel_of_le h0
  linarith



  -- simp_all
  -- have : N = P + Q - M := by sorry
  -- rw [this]
  -- have : Q + (P - M) = (Q + P) - M := by
  --   rw [add_sub_cancel']
  --   rw [←add_assoc]


  -- have h1 : M + (N - Q) = P := by sorry
  --   -- rw [add_sub_cancel', ←add_assoc, h, add_assoc, add_comm Q, ←add_assoc, add_assoc, add_sub_cancel']

  -- have h2 : N - Q + Q = Q + (N - Q) := by sorry
  -- { rw nat.add_sub_cancel' },
  -- rw [←h1, h2],



#check add_assoc
-- Constant CoLoR.Util.Multiset.MultisetOrder.MultisetOrder.MSet.double_split
-- Module Import MSet := MultisetTheory.Multiset MC.
lemma double_split {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (M N P Q: Multiset α) ,  M + N = P + Q → N = N ∩ Q + (P - M)  := by
        intros M N P Q h
        ext x
        rw [Multiset.count_add]
        rw [Multiset.count_inter]
        rw [Multiset.count_sub]
        have H0 : Multiset.count x M + Multiset.count x N = Multiset.count x P + Multiset.count x Q := by
          rw [Multiset.ext] at h
          simp_all only [Multiset.mem_add, Multiset.count_add]
        if l_u : Multiset.count x M ≤ Multiset.count x P then
          have : Multiset.count x N ≥ Multiset.count x Q := by linarith

          aesop --Ask Malvin: how to replace aesop with more explicit tactics?
          apply le_eq_sub (Multiset.count x M) (Multiset.count x N) (Multiset.count x P) (Multiset.count x Q)
          aesop
          exact H0
          -- use H0
        else
          simp_all only [not_le, gt_iff_lt]
          have : Multiset.count x N ≤ Multiset.count x Q := by linarith
          aesop
          apply le_of_lt
          exact l_u



lemma in_notin_diff {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (x : α) (X Y: Multiset α) ,  x ∈ X → x ∉ Y → x ∈ X - Y  := by
        intros x X Y x_in_X x_notin_Y
        have : Multiset.count x X ≥ 1 := by
          rw [← Multiset.one_le_count_iff_mem] at x_in_X
          exact x_in_X
        have : Multiset.count x Y = 0 := by apply Multiset.count_eq_zero_of_not_mem; exact x_notin_Y
        rw [← Multiset.one_le_count_iff_mem]
        rw [Multiset.count_sub]
        aesop



lemma WRONG_inter_add_dist {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (M N P : Multiset α) ,  P ∩ (M + N) = P ∩ M + P ∩ N  := by
        intros M N P
        if h0 : P ≤ M then

          sorry
        else
          if h1 : P ≤ N then
            sorry
          else
            sorry


lemma WRONG_add_inter_complement {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (M N P : Multiset α) ,  P ≤ M + N → P = P ∩ M + P ∩ N  := by
        intros M N P h
        let X := M + N


        sorry
        -- have : P ≤ P ∩ M + P ∩ N := by sorry
        -- have : P ≥ P ∩ M + P ∩ N := by sorry
        -- rw [eq_iff_le_not_lt]
        -- constructor
        -- aesop
        -- by_contra
        -- apply not_le_of_lt
        -- rw [not_le_of_lt] at this
        -- aesop

-- Two lemmas needed: double_split, in_notin_diff (proved)
lemma LT_trans {α} [pre : Preorder α] [dec : DecidableEq α]:
      ∀ (M N P : Multiset α) , MultisetLT N M → MultisetLT P N → MultisetLT P M := by
      intros M N P LTNM LTPN
      rcases LTNM with ⟨Y1, X1, Z1, X1_ne, N1_def, M1_def, Ord1⟩
      rcases LTPN with ⟨Y2, X2, Z2, X2_ne, P2_def, N2_def, Ord2⟩
      apply MultisetLT.MLT (Y2 + (Y1 - X2)) (X1 + (X2 - Y1)) (Z1 ∩ Z2)
      . aesop
      . rw [P2_def]
        have : Z1 ∩ Z2 + (Y2 + (Y1 - X2)) = Z1 ∩ Z2 + (Y1 - X2) + Y2 := by
          have : (Y2 + (Y1 - X2)) = (Y1 - X2) + Y2 := by rw [add_comm]
          rw [this]
          rw [add_assoc]
        rw [this]
        apply meq_union_meq_reverse
        have : Z1 ∩ Z2 + (Y1 - X2) = Z2 ∩ Z1 + (Y1 - X2) := by
          rw [Multiset.inter_comm]
        rw [this]
        rw [← double_split]
        rw [add_comm]
        rw [← N2_def]
        rw [N1_def]
        apply add_comm
      . rw [M1_def]
        have : Z1 ∩ Z2 + (X1 + (X2 - Y1)) = Z1 ∩ Z2 + (X2 - Y1) + X1 := by
          have : (X1 + (X2 - Y1)) = (X2 - Y1) + X1 := by rw [add_comm]
          rw [this]
          rw [add_assoc]
        rw [this]
        apply meq_union_meq_reverse
        apply double_split
        rw [add_comm]
        rw [← N1_def]
        rw [N2_def]
        apply add_comm
      . intros y y_in_union
        if y_in : y ∈ Y2 then
          rcases (Ord2 y y_in) with ⟨x, x_in_X2, y_lt_x⟩
          if x_in : x ∈ Y1 then
            rcases (Ord1 x x_in) with ⟨x', x'_in_X1, x_lt_x'⟩
            use x'
            constructor
            . rw [Multiset.mem_add]
              constructor
              exact x'_in_X1
            . exact lt_trans y_lt_x x_lt_x'
            else
              use x
              constructor
              . rw [add_comm]
                rw [Multiset.mem_add]
                constructor
                apply in_notin_diff
                exact x_in_X2
                exact x_in
              . exact y_lt_x
          else
            have y_in : y ∈ (Y1 - X2) := by aesop
            let h := (Ord1 y)
            have y_in_Y1 : y ∈ Y1 := by

              have : Y1 - X2 ≤ Y1 := by aesop
              apply Multiset.mem_of_le
              exact this
              exact y_in
            let _ := h y_in_Y1
            aesop

-- -- lemma LT_trans {α} [pre : Preorder α] [dec : DecidableEq α] [LT : LT α]:
-- --       Transitive (@MultisetLT α dec LT) := by
-- lemma WRONG_LT_trans {α} [pre : Preorder α] [dec : DecidableEq α]:
--       ∀ (M N P : Multiset α) , MultisetLT M N → MultisetLT N P → MultisetLT M P  := by
--       intros M N P LTMN LTNP
--       rcases LTMN with ⟨X, Y, Z, Y_not_empty, MZX, NZY, h⟩
--       rcases LTNP with ⟨X', Y', Z', Y'_not_empty,NZX',PZY', h' ⟩
-- -- Useful results throughout the proof:
--       have H0: Multiset.inter Z Z' ≤ Z' := by apply Multiset.inter_le_right
--       have H1: Y' ≤ (Z' + Y' - Multiset.inter Z Z') := by
--           -- have H1: Multiset.inter Z Z' ≤ Z' + Y' := by
--           --   apply le_trans
--           --   exact H0
--           --   aesop
--           have : Y' ≤ Y' + Z' - Multiset.inter Z Z' := by
--             have : Y' + Z' - Multiset.inter Z Z' = Y' + (Z' - Multiset.inter Z Z') := by
--               apply add_tsub_assoc_of_le
--               exact H0
--             aesop
--           have : Y' + Z' = Z' + Y' := by
--             apply add_comm
--           aesop

--       apply MultisetLT.MLT ((Z+X) - (Multiset.inter Z Z')) ((Z'+Y')-(Multiset.inter Z Z')) (Multiset.inter Z Z') -- I think the application is wrong here! But maybe it also works? Discuss with Malvin!
--       . aesop
--         -- The rest is when we have H: Y' ≤_DM (Z' + Y' - Multiset.inter Z Z') instead of Y' ≤ (Z' + Y' - Multiset.inter Z Z')
--         -- cases H
--         -- -- with ⟨X,Y,Z,h0,h1,h2,h3⟩
--         -- case MLT.MLT.a.inl H := by
--         --   cases H
--         --   aesop
--         -- case MLT.MLT.a.inr H := by
--         --   rw [H] at Y'_not_empty
--         --   exact Y'_not_empty
--       . rw [MZX]
--         have : Multiset.inter Z Z' ≤ Z + X := by
--           have : Multiset.inter Z Z' ≤ Z := by apply Multiset.inter_le_left
--           apply le_trans
--           exact this
--           aesop
--         aesop_subst [NZY, PZY', MZX]
--         simp_all only [Multiset.empty_eq_zero]
--         simp_all [ne_eq]
--       . rw [PZY']
--         have : Multiset.inter Z Z' ≤ Z' + Y' := by
--           have : Multiset.inter Z Z' ≤ Z' := by apply Multiset.inter_le_right
--           apply le_trans
--           exact this
--           aesop
--         aesop_subst [NZX', PZY', MZX]
--         simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, add_tsub_cancel_of_le]
--       . intro x
--         intro H
--         have H' : Z + X - Multiset.inter Z Z' = Z - Multiset.inter Z Z' + X := by -- Use the fact that Multiset.inter Z Z' ≤ Z

--           have Z_Z'_le_Z : Multiset.inter Z Z' ≤ Z := by apply Multiset.inter_le_left

--           have : Z + X - Multiset.inter Z Z' + Multiset.inter Z Z'= Z - Multiset.inter Z Z' + X + Multiset.inter Z Z' := by
--             have : Multiset.inter Z Z' ≤ Z + X := by apply le_trans ; exact Z_Z'_le_Z ; aesop
--             have : Z + X - Multiset.inter Z Z' = Z - Multiset.inter Z Z' + X := by
--               have : Z + X - Multiset.inter Z Z' + Multiset.inter Z Z' = Z - Multiset.inter Z Z' + X + Multiset.inter Z Z' := by
--                 have : Z + X - Multiset.inter Z Z' + Multiset.inter Z Z' = Z + X := by
--                   have : Z + X - Multiset.inter Z Z' + Multiset.inter Z Z' = Z + X + Multiset.inter Z Z' - Multiset.inter Z Z' := by
--                     apply le_sub_add
--                     exact this
--                   aesop -- use add_tsub_assoc_of_le
--                 have : Z - Multiset.inter Z Z' + X + Multiset.inter Z Z' = Z + X := by
--                   have : Z - Multiset.inter Z Z' + X = Z + X - Multiset.inter Z Z' := by
--                     apply le_sub_add
--                     exact Z_Z'_le_Z

--                   rw [this]
--                   simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le]
--                 aesop
--               aesop
--             aesop
--           aesop
--         if hyp : x ∈ Z - Multiset.inter Z Z' then
--           have x_in_X': x ∈ X' := by
--             have : Z - Multiset.inter Z Z' ≤ X' := by
--               have : Z - Multiset.inter Z Z' = Z - Z' := by apply Multiset.sub_inter
--               -- simp
--               have : Z ≤ X' + Z' := by
--                 simp_all only [ge_iff_le, le_add_iff_nonneg_right, zero_le]
--                 have : X' + Z' = Z' + X' := by apply add_comm
--                 rw [this]
--                 simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, Multiset.mem_add, true_or, le_add_iff_nonneg_right, zero_le]
--               simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, Multiset.mem_add, tsub_le_iff_right]
--             apply Multiset.mem_of_le
--             exact this
--             exact hyp

--           have yY : ∃ y ∈ Y', x < y := (h' x x_in_X')
--           -- have : Y' ≤ Z' + Y' - Multiset.inter Z Z':= by sorry
--           rcases yY with ⟨y,y_in_Y', xy⟩
--           use y
--           have : y ∈ Z' + Y' - Multiset.inter Z Z' := by
--             exact Multiset.mem_of_le H1 y_in_Y'
--           aesop
--         else
--           have hyp: x ∈ X := by
--             have : x ∈ Z - Multiset.inter Z Z' + X := by aesop
--             aesop
--           have yY : ∃ y ∈ Y, x < y := h x hyp
--           rcases yY with ⟨y, y_in_Y, xy⟩
--           if hyp': y ∈ Z' - Z then
--             use y
--             constructor
--             . have y_in_Z'_ZZ' : y ∈ Z' - Multiset.inter Z Z' := by
--                 have : Z' - Z = Z' - Multiset.inter Z Z' := by
--                   have : Z' - Multiset.inter Z Z' = Z' - Z' ∩ Z := by
--                     have : Multiset.inter Z Z' = Z' ∩ Z := by apply Multiset.inter_comm
--                     rw [this]
--                   rw [this]
--                   rw [Multiset.sub_inter]
--                 aesop
--               have : Z' - Multiset.inter Z Z' ≤ Z' + Y' - Multiset.inter Z Z' := by
--                 have : Z' ≤ Z' + Y' := by aesop
--                 aesop
--                 have : Z' + Y' = Z' + Y' - Multiset.inter Z Z' + Multiset.inter Z Z' := by
--                   apply mem_leq_diff
--                   apply le_trans H0
--                   simp_all only [ge_iff_le, le_add_iff_nonneg_right, zero_le]
--                 rw [← this]
--                 apply Multiset.le_add_right

--               apply Multiset.mem_of_le
--               exact this
--               assumption
--             . assumption
--           else
--             use y
--             constructor
--             . sorry
--             . assumption

--             have yX' : y ∈ X' := by
--               have Y_Z'_X' : Y - Z' ≤ X' := by
--                 have : Y ≤ N := by simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, Multiset.mem_add, or_true, le_add_iff_nonneg_left, zero_le]

--                 have : Y - Z'  ≤ N - Z' := by
--                   -- use Y ≤ N
--                   have : Y ≤ N - Z' + Z' := by
--                     have : N - Z' + Z' = N := by
--                       have : N - Z' + Z' = N ∪ Z' := by apply Multiset.union_def
--                       have : N ∪ Z' = N := by
--                         have : Z' ≤ N := by
--                           rw [Multiset.le_iff_exists_add]
--                           use X'
--                         apply Multiset.eq_union_left
--                         exact this
--                       aesop
--                     aesop
--                   rw [Multiset.sub_le_iff_le_add]
--                   exact this
--                 have : X' = N - Z' := by
--                   have : X' + Z' = N - Z' + Z' := by
--                     have : N - Z' + Z' = N := by
--                       have : N - Z' + Z' = N ∪ Z' := by apply Multiset.union_def
--                       have : N ∪ Z' = N := by
--                         have : Z' ≤ N := by
--                           rw [Multiset.le_iff_exists_add]
--                           use X'
--                         apply Multiset.eq_union_left
--                         exact this
--                       aesop
--                     rw [this]
--                     rw [NZX']
--                     apply add_comm
--                   simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, Multiset.mem_add, or_true, le_add_iff_nonneg_left, zero_le, tsub_le_iff_right, add_left_inj, add_le_iff_nonpos_right, nonpos_iff_eq_zero, tsub_eq_zero_iff_le, add_tsub_cancel_left]

--                 rw [this]
--                 assumption
--               sorry
--               -- have y_Y_Z': y ∈ Y - Z' := by
--               --   have : Y = (Y - Z') + (Z' - Z) := by
--               --     have : Y - Z' = Y - (Y ∩ Z') := by
--               --       rw [Multiset.sub_inter]
--               --     rw [this]
--               --     have : Z' - Z = Y ∩ Z' := by -- wrong?
--               --       have : Z' - Z = Z' - (Z' ∩ Z) := by rw [Multiset.sub_inter]
--               --       rw [this]
--               --       have : Z' - Z' ∩ Z + Z' ∩ Z = Y ∩ Z' + Z' ∩ Z := by
--               --         have : Z' - Z' ∩ Z + Z' ∩ Z = Z' := by rw [← mem_leq_diff] ; rw [Multiset.inter_comm] ; exact H0
--               --         rw [this]
--               --         have : Y ∩ Z' = Z' ∩ Y := by apply Multiset.inter_comm
--               --         rw [this]
--               --         apply add_inter_complement
--               --         rw [add_comm Y Z]
--               --         rw [← NZY]
--               --         aesop
--               --       aesop
--               --     rw [this]
--               --     have : Y ∩ Z' ≤ Y := by apply Multiset.inter_le_left
--               --     apply mem_leq_diff
--               --     simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, Multiset.mem_add, or_true, Multiset.mem_inter, true_and, Multiset.le_inter_iff, le_refl, tsub_le_iff_right]
--               --   rw [this] at y_in_Y
--               --   rw [Multiset.mem_add] at y_in_Y
--               --   cases y_in_Y with
--               --   | inl => assumption
--               --   | inr h =>
--               --     apply False.elim
--               --     exact hyp' h

--               -- apply Multiset.mem_of_le
--               -- exact Y_Z'_X'
--               -- exact y_Y_Z'
--             have y'_Y': ∃ y' ∈ Y', y < y' := h' y yX'
--             rcases y'_Y' with ⟨w, w_in_Y', yw⟩
--             use w
--             constructor
--             . exact Multiset.mem_of_le H1 w_in_Y'
--             . exact lt_trans xy yw

-- lemma LT_trans {α} [pre : Preorder α] [dec : DecidableEq α] [LT : LT α]:
--       Transitive (@MultisetLT α dec LT) := by
--       intros M N P LTMN LTNP
--       rcases LTMN with ⟨X, Y, Z, Y_not_empty, MZX, NZY, h⟩
--       rcases LTNP with ⟨X', Y', Z', Y'_not_empty,NZX',PZY', h' ⟩
--       apply MultisetLT.MLT ((Z+X) - (Multiset.inter Z Z')) ((Z'+Y')-(Multiset.inter Z Z')) (Multiset.inter Z Z')
--       . have H0: Multiset.inter Z Z' ≤ Z' := by apply Multiset.inter_le_right
--         have H: Y' ≤ (Z' + Y' - Multiset.inter Z Z') := by
--           -- have H1: Multiset.inter Z Z' ≤ Z' + Y' := by
--           --   apply le_trans
--           --   exact H0
--           --   aesop
--           have : Y' ≤ Y' + Z' - Multiset.inter Z Z' := by
--             have : Y' + Z' - Multiset.inter Z Z' = Y' + (Z' - Multiset.inter Z Z') := by
--               apply add_tsub_assoc_of_le
--               exact H0
--             aesop
--           have : Y' + Z' = Z' + Y' := by
--             apply add_comm
--           aesop

--         aesop
--         -- The rest is when we have H: Y' ≤_DM (Z' + Y' - Multiset.inter Z Z') instead of Y' ≤ (Z' + Y' - Multiset.inter Z Z')
--         -- cases H
--         -- -- with ⟨X,Y,Z,h0,h1,h2,h3⟩
--         -- case MLT.MLT.a.inl H := by
--         --   cases H
--         --   aesop
--         -- case MLT.MLT.a.inr H := by
--         --   rw [H] at Y'_not_empty
--         --   exact Y'_not_empty
--       . rw [MZX]
--         have : Multiset.inter Z Z' ≤ Z + X := by
--           have : Multiset.inter Z Z' ≤ Z := by apply Multiset.inter_le_left
--           apply le_trans
--           exact this
--           aesop
--         aesop_subst [NZY, PZY', MZX]
--         simp_all only [Multiset.empty_eq_zero]
--         simp_all [ne_eq]
--       . rw [PZY']
--         have : Multiset.inter Z Z' ≤ Z' + Y' := by
--           have : Multiset.inter Z Z' ≤ Z' := by apply Multiset.inter_le_right
--           apply le_trans
--           exact this
--           aesop
--         aesop_subst [NZX', PZY', MZX]
--         simp_all only [Multiset.empty_eq_zero, ne_eq, ge_iff_le, add_tsub_cancel_of_le]
--       . intro x
--         intro H
--         have H' : Z + X - Multiset.inter Z Z' = Z - Multiset.inter Z Z' + X := by sorry
--         if hyp : x ∈ Z - Multiset.inter Z Z' then
--           have x_in_X': x ∈ X' := by
--             -- have h: x ∈ Z - Multiset.inter Z Z' := by

--             --   sorry
--             have : Z - Multiset.inter Z Z' ≤ X' := by sorry
--             apply Multiset.mem_of_le
--             exact this
--             exact hyp
--           have yY : ∃ y ∈ Y', x < y := (h' x x_in_X')
--           -- have : Y' ≤ Z' + Y' - Multiset.inter Z Z':= by sorry
--           rcases yY with ⟨y,y_in, xy⟩
--           use y
--           have : y ∈ Z' + Y' - Multiset.inter Z Z' := by
--             sorry
--           aesop
--         else
--           have hyp: x ∈ X := by
--             have : x ∈ Z - Multiset.inter Z Z' + X := by aesop
--             aesop
--           have yY : ∃ y ∈ Y, x < y := h x hyp
--           rcases yY with ⟨y, y_in, xy⟩
--           if hyp': y ∈ Z' - Z then
--             sorry
--           else
--             have yX' : y ∈ X' := by sorry
--             have y'_Y': ∃ y' ∈ Y', y < y' := h' y yX'
--             rcases y'_Y' with ⟨w, w_in_Y', yw⟩
--             use w
--             constructor
--             . sorry
--             .
--               apply obvious
--               sorry



-- lemma filter_disjoint :

#check Multiset.card


-- def sub1 : ℕ → ℕ
-- | zero     => zero
-- | (succ x) => x



-- def f' [DecidableEq α][Preorder α] {X : List α} : α → List α := fun y' => X.filter (fun x => x < y')


-- def g' {X : List α} : List α → List α
-- | []     => []
-- | (x::xs) => List.join (f' x) (g' xs)


--Ask Malvin: The problem is if I don't use [LT α] < will be both used for A and Multiset A. However, it seems like lean can tell the difference.

lemma nat_not_0 : ∀ (n : ℕ), n ≠ 0 → n ≥ 1 := by
  intros n h
  cases n
  . contradiction
  . exact Nat.succ_le_iff.mpr (Nat.zero_lt_succ _)

lemma nat_not_0_not_1 : ∀ (n : ℕ), n ≠ 0 → n ≠ 1 → n ≥ 2 := by
  intros n h0 h1
  cases n
  case zero => contradiction
  case succ m =>
    cases m
    case zero => contradiction
    case succ n=>
      apply Nat.succ_le_succ
      aesop

-- variable (p : α → Prop) [DecidablePred p]
-- lemma filter_disjoint [dec : DecidableEq α] [Preorder α] : ∀ (M : Multiset α), (Multiset.inter (Multiset.filter p M) M) - (Multiset.filter p M) = 0 := by
--   intros M
--   ext a
--   simp only [Multiset.count_sub, Multiset.count_inter, Multiset.count_zero]
--   by_cases h : p a
--   case pos => rw [Multiset.count_filter_of_pos h, max_eq_right (le_refl _)]
--   case neg => sorry


 lemma direct_subset_red [dec : DecidableEq α] [Preorder α] [DecidableRel (fun (x : α) (y: α) => x < y)] : ∀ (M N : Multiset α), MultisetLT M N →  MultisetLt M N := by
      intros M N LTXY
      cases LTXY
      case MLT X Y Z Y_not_empty MZX NZY h =>
        unfold MultisetLt
        revert Z X M N
        induction Y using Multiset.strongInductionOn
        case ih Y IH =>
          intro M N X Z M_def N_def X_lt_Y
          cases em (Multiset.card Y = 0)
          · simp_all
          cases em (Multiset.card Y = 1)
          case inl hyp' hyp=>
            rw [Multiset.card_eq_one] at hyp
            rcases hyp with ⟨y,Y'_def⟩
            apply TC.base
            rw [Y'_def] at N_def
            apply @MultisetRedLt.RedLt α _ _ M N Z X y M_def N_def
            simp [Y'_def] at X_lt_Y
            exact X_lt_Y
          case inr hyp' hyp =>
            have : ∃ a, a ∈ Y := by
              rw [← Y.card_pos_iff_exists_mem]
              cases foo : Multiset.card Y
              tauto
              simp
            rcases this with ⟨y,claim⟩
            let newY := Y.erase y
            have newY_nonEmpty : newY ≠ ∅ := by
              have card_Y_ge_2 : Multiset.card Y ≥ 2 := by
                apply nat_not_0_not_1
                exact hyp'
                exact hyp
              have : Multiset.card (Multiset.erase Y y) ≥ 1 := by
                rw [Multiset.card_erase_eq_ite]
                aesop -- Don't know how to make it more explicit. Ask Malvin!
                have card_Y_g_1 : 1 < Multiset.card Y := by aesop
                exact Nat.pred_le_pred card_Y_g_1
              have : 0 < Multiset.card (Multiset.erase Y y) := by aesop
              rw [Multiset.card_pos] at this
              aesop
            have newY_sub_Y : newY < Y := by simp; exact claim
            let f : α → Multiset α := fun y' => X.filter (fun x => x < y')
            -- let f' : α → List α := fun y' => (Multiset.toList X).filter (fun x => x < y') --toList uses choice
            -- let g : Multiset α → Multiset α := fun M => sorry
            -- let h : List α → List α → List α -- Why is h not recognized in this recursive call?
            --    | [], _ => []
            --    | (y :: ys), X' => (Multiset.toList X').filter (fun x => x < y) ++ (h ys (X' - ((Multiset.toList X').filter (fun x => x < y))))

            let N' := Z + newY + f y -- DecidableRel
            apply TC.trans
            case intro.b => exact N'
            -- step from N' to M
            · apply IH newY newY_sub_Y newY_nonEmpty
              -- change M = (Z + f y) + (newY.map f).join -- This might be wrong actually
              change M = (Z + f y) + (X - f y) -- new try
              ·
                have : f y ≤ X := Multiset.filter_le (fun x => x < y) X
                ext a
                have count_lt := Multiset.count_le_of_le a this
                rw [M_def]
                simp_all
                let x := Multiset.count a X
                let z := Multiset.count a Z
                let fx := Multiset.count a (Multiset.filter (fun x => x < y) X)
                change z + x = z + fx + (x - fx)
                change fx ≤ x at count_lt
                have : x = fx + (x - fx) := by aesop
                linarith
              · have : Z + newY + f y = Z + f y + newY := by
                  have : newY + f y = f y + newY := by apply add_comm
                  have : Z + newY + f y = Z + (newY + f y) := by apply add_assoc
                  rw [this]
                  have : Z + f y + newY = Z + (f y + newY) := by apply add_assoc
                  rw [this]
                  aesop
                aesop
              · intro x x_in --use X_lt_Y -- It is still correct here
                let X_lt_Y := X_lt_Y x
                have : x ∈ X := by
                  have Xfy_le_X : X - f y ≤ X:= by aesop
                  apply Multiset.mem_of_le Xfy_le_X
                  exact x_in
                let X_lt_Y := X_lt_Y this
                rcases X_lt_Y with ⟨t, t_in_Y, x_lt_t⟩
                use t --it might already be wrong here
                constructor
                -- .
                --   if t_ne_y : t ≠ y then
                --     simp
                --     rw [Multiset.mem_erase_of_ne]
                --     exact t_in_Y
                --     exact t_ne_y
                --   else
                --     exfalso
                --     have : x ∈ f y := by sorry
                --     aesop

                --     sorry

                . if t_in_newY : t ∈ newY then  -- The abandoned proof that t ∈ newY
                    exact t_in_newY
                    else
                      exfalso
                      have : t = y := by
                        have : Y = newY + {y} := by aesop
                        rw [this] at t_in_Y
                        rw [Multiset.mem_add] at t_in_Y
                        have : t ∈ ( {y} : Multiset α) := by exact Or.resolve_left t_in_Y t_in_newY
                        rw [← Multiset.mem_singleton]
                        assumption
                      have : x ∈ f y := by aesop
                      have x_notin_Xfy : x ∉ X - f y := by
                        by_contra
                        let neg_f : α → Multiset α := fun y' => X.filter (fun x => ¬ x < y')
                        have : X - f y = neg_f y := by
                          have fy_negfy_X : f y + neg_f y = X := by
                            rw [Multiset.filter_add_not]
                          have fy_le_X : f y ≤ X := by
                            apply Multiset.filter_le _ X
                          have : X - f y + f y = neg_f y + f y := by
                            have : X = X - f y + f y := by
                              apply mem_leq_diff
                              exact fy_le_X
                            rw [← this]
                            rw [← fy_negfy_X]
                            apply add_comm
                          aesop
                        aesop
                      aesop
                . exact x_lt_t




            -- single step N to N'
            · have : MultisetRedLt N' N := by
                apply MultisetRedLt.RedLt (Z + newY) (f y) y
                . rfl
                . have newY_y_Y: newY + {y} = Y := by aesop
                  have : Z + newY + {y} = Z + (newY + {y}) := by apply add_assoc
                  rw [this]
                  rw [newY_y_Y]
                  exact N_def
                . aesop
              apply TC.base
              exact this


 lemma direct_subset_red' [DecidableEq α] [Preorder α]: ∀ (M N : Multiset α), MultisetLT M N →  MultisetLt M N := by
      intros M N LTXY
      cases LTXY
      case MLT W Y Z Y_not_empty MZW NZY h =>
        unfold MultisetLt
        let n := Multiset.card Y
        cases n_case : n -- using Nat.strongInductionOn
        case zero =>
          simp_all
        case succ k =>
          -- have := direct_subset_red ...

          have hyp0: TC MultisetRedLt (Z+Y) (N) := by sorry
          have hyp1: TC MultisetRedLt (M) (Z+Y) := by


            sorry
          apply TC.trans
          exact hyp1
          exact hyp0


-- It uses `LT_trans`, which still needs to be proved.
-- Is this gonna be hard to prove? Why does the coq proof use some other ways to prove:  mord_acc_mOrd_acc (Acc_homo), mOrd_acc.
lemma Lt_LT_equiv [DecidableEq α] [Preorder α] [DecidableRel (fun (x : α) (y: α) => x < y)]:
      (MultisetLt : Multiset α → Multiset α → Prop) = (MultisetLT : Multiset α → Multiset α → Prop) := by
      funext X Y
      apply propext
      constructor
      · -- Lt → LT:
        intros hLt
        -- unfold MultisetLT
        -- rw [MultisetLt] at hLt
        induction hLt with
        | base a b hLt => --should be easy: use `use`
          rcases hLt with ⟨Z, X, y, a_def, b_def, X_lt_y⟩  -- This used to work
          -- constructor
          use X
          simp
          simp
          assumption

        | trans Z W A _ _ aih bih => -- it suffices to show MultisetLT is transitive
          exact LT_trans _ _ _ bih aih

      · -- LT → Lt:
        apply direct_subset_red


-- If two relations are equivalent and one of them is well-founded, then the other one is also well-founded.
lemma equiv_r_wf [DecidableEq α] [LT α] (h1 : WellFounded (r1 :  Multiset α → Multiset α → Prop)) (h2: r1 = r2): WellFounded r2 := by
  aesop

-- The desired theorem. If `LT.lt` is well-founded, then `MultisetLT` is well-founded.
theorem dm_wf' [DecidableEq α][ Preorder α] [DecidableRel (fun (x : α) (y: α) => x < y)](wf_lt :  WellFoundedLT α) :
      WellFounded (MultisetLT : Multiset α → Multiset α → Prop) := by
      apply (equiv_r_wf (Lt_wf (RedLt_wf wf_lt)) Lt_LT_equiv)
