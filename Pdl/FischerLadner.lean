import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

import Pdl.Measures

/-! # Fischer-Ladner Closure

Here we define a closure on sets of formulas.
Our main reference for this closure is the proof of Theorem 3.2 in [FL1979].
See also Definition 4.79 and Exercise 4.8.2 in [BRV2001].

- [FL1979] Michael J. Fischer and Richard E. Ladner (1979):
  *Propositional dynamic logic of regular programs*.
	Journal of Computer and System Sciences, vol 18, no 2, pp. 194--211.
	<https://doi.org/10.1016/0022-0000(79)90046-1>

- [BRV2001] Patrick Blackburn, Maarten de Rijke and Yde Venema (2001):
	*Modal Logic*.
	Cambridge University Press.
  <https://www.mlbook.org/>

-/

/-! ## Naive Single-step  -/

def Formula.fischerLadnerStep : Formula → List Formula
| ⊥ => []
| ·_ => []
| φ⋀ψ => [φ, ψ]
| ⌈·_⌉φ => [φ]
| ⌈α;'β⌉φ => [ ⌈α⌉⌈β⌉φ ]
| ⌈α⋓β⌉φ => [ ⌈α⌉φ, ⌈β⌉φ ]
| ⌈∗α⌉φ => [ φ, ⌈α⌉⌈∗α⌉φ ]
| ⌈?'τ⌉φ => [ τ, φ ] -- hmm?
| ~~φ => [~φ]
| ~⊥ => []
| ~(·_) => []
| ~(φ⋀ψ) => [ ~φ, ~ψ ]
| ~⌈·_⌉φ => [ ~φ]
| ~⌈α;'β⌉φ => [ ~⌈α⌉⌈β⌉φ ]
| ~⌈α⋓β⌉φ => [ ~⌈α⌉φ, ~⌈β⌉φ ]
| ~⌈∗α⌉φ => [ ~φ, ~⌈α⌉⌈∗α⌉φ ]
| ~⌈?'τ⌉φ => [ ~τ, ~φ ] -- hmm?

/-! ## PreFormulas

The proof of Theorem 3.2 in [FL1979] uses fresh variables, which would mean we have to
compute those and then work with `repl_in_F` to get the original formula back, etc.
Instead, here we use a new `PreForm` type that allows us to mark the subformula after
a box to not be taken apart further in the recursive step `PreForm.fischerLadnerStep`.
In particular, we define
-/

/-- A (non-)negated sequence of boxes before a formula that should (not) be taken apart. -/
def PreForm : Type := Bool × Option Program × Sum Formula Formula

/-- No negation, empty list of boxes and to still be taken apart. -/
def PreForm.ofFormula (ψ : Formula) : PreForm := ⟨True, none, Sum.inl ψ⟩

-- instance : Coe Formula (PreForm) := ⟨PreForm.ofFormula⟩ -- unused.

def PreForm.toForm : PreForm → Formula
| (b, αs, lrφ) => (if b then id else Formula.neg) $ Formula.boxes αs.toList (lrφ.elim id id)

/-! Length of a `PreForm`. Crucially, this does not count the `.inr` part. -/
@[simp]
def PreForm.length : PreForm → Nat
| (_, α, Sum.inl φ) => (α.map lengthOfProgram).getD 0 + lengthOfFormula φ
| (_, α, Sum.inr _) => (α.map lengthOfProgram).getD 0 -- NOT counting φ here

/-! ## Single Step -/

/-- Inspired by [FL1979] proof of Theorem 3.2. -/
def PreForm.fischerLadnerStep : PreForm → List PreForm
| ⟨_, none, Sum.inl (⊥)⟩ => []
| ⟨_, none, Sum.inl (·_)⟩ => []
| ⟨b, none, Sum.inl (φ⋀ψ)⟩ => [ ⟨b, none, Sum.inl φ⟩, ⟨b, none, Sum.inl ψ⟩ ]
| ⟨true, none, Sum.inl (~φ)⟩ => [ ⟨false, none, Sum.inl φ⟩ ] -- ~φ staying the same
| ⟨false, none, Sum.inl (~φ)⟩ => [ ⟨false, none, Sum.inl φ⟩ ] -- ~~φ to ~φ
| ⟨b, none, Sum.inl (⌈α⌉φ)⟩ => [ ⟨b, α, Sum.inl φ⟩ ] -- [α]φ staying the same
| ⟨_, none, Sum.inr _⟩ => [ ] -- blocked formula generates nothing.
-- Boxes before formulas still to be taken apart:
| ⟨b, ·_, Sum.inl φ⟩ => [ ⟨b, none, Sum.inl φ⟩ ]
| ⟨b, α;'β, Sum.inl φ⟩ => [ ⟨b, α, Sum.inr (⌈β⌉φ)⟩, ⟨b, β, Sum.inl φ⟩ ]
| ⟨b, α⋓β, Sum.inl φ⟩ => [ ⟨b, α, Sum.inr φ⟩, ⟨b, β, Sum.inr φ⟩, ⟨b, none, Sum.inl φ⟩ ]
| ⟨b, ∗α, Sum.inl φ⟩ => [ ⟨b, none, Sum.inl φ⟩, ⟨b, α, Sum.inr (⌈∗α⌉φ)⟩ ]
| ⟨true, ?'τ, Sum.inl φ⟩ => [ ⟨true, none, Sum.inl τ⟩, ⟨true, none, Sum.inl φ⟩ ]
| ⟨false, ?'τ, Sum.inl φ⟩ => [ ⟨false, none, Sum.inl τ⟩, ⟨false, none, Sum.inl φ⟩ ]
-- Boxes before blocked formulas:
| ⟨b, ·_, Sum.inr φ⟩ => [ ⟨b, none, Sum.inr φ⟩ ]
| ⟨b, α;'β, Sum.inr φ⟩ => [ ⟨b, α, Sum.inr (⌈β⌉φ)⟩, ⟨b, β, Sum.inr φ⟩ ]
| ⟨b, α⋓β, Sum.inr φ⟩ => [ ⟨b, α, Sum.inr (φ)⟩, ⟨b, β, Sum.inr (φ)⟩, ⟨b, none, Sum.inr φ⟩ ]
| ⟨b, ∗α, Sum.inr φ⟩ => [ ⟨b, none, Sum.inr φ⟩, ⟨b, α, Sum.inr (⌈∗α⌉φ)⟩ ]
| ⟨true, ?'τ, Sum.inr φ⟩ => [ ⟨true, none, Sum.inr τ⟩, ⟨true, none, Sum.inr φ⟩ ]
| ⟨false, ?'τ, Sum.inr φ⟩ => [ ⟨false, none, Sum.inr τ⟩, ⟨false, none, Sum.inr φ⟩ ]

/-- Unused, weaker than `PreForm.fischerLadnerStep_sum_down`. -/
lemma PreForm.fischerLadnerStep_down {pφ pψ : PreForm} :
    pψ ∈ pφ.fischerLadnerStep → pψ.length < PreForm.length pφ := by
  rcases pφ with ⟨b, _|α, φ|φ⟩
  case none.inl =>
    intro ψ_def
    cases φ <;> cases b <;> simp [PreForm.fischerLadnerStep] at ψ_def
    all_goals
      subst_eqs
      simp_all
    all_goals
      cases ψ_def <;> subst_eqs <;> simp_all; omega
  case none.inr =>
    simp [PreForm.fischerLadnerStep]
  case some.inl =>
    intro ψ_def
    cases α <;> simp [PreForm.fischerLadnerStep] at ψ_def
    case atom_prog a => simp_all
    case sequence => cases ψ_def <;> simp_all; omega
    case union => rcases ψ_def with _|_|_ <;> (subst_eqs; simp <;> try omega)
    case star => cases ψ_def <;> (subst_eqs; simp <;> try omega)
    case test => cases b <;> simp_all <;> cases ψ_def <;> simp_all <;> omega
  case some.inr =>
    intro ψ_def
    cases α <;> simp [PreForm.fischerLadnerStep] at ψ_def
    case atom_prog a => simp_all
    case sequence => cases ψ_def <;> simp_all ; omega
    case union => rcases ψ_def with _|_|_ <;> (subst_eqs; simp <;> omega)
    case star => cases ψ_def <;> (subst_eqs; simp; try omega)
    case test => cases b <;> simp_all <;> cases ψ_def <;> simp_all

/-- With `fresherLadnerStepPre` the (sum of) `PreForm.length` goes down.
Here `h` is needed to exclude the .inr case (wher we would claim 0 < 0). -/
lemma PreForm.fischerLadnerStep_sum_down (pφ : PreForm) (h : ¬ pφ.2.2.isRight):
    ((PreForm.fischerLadnerStep pφ).map PreForm.length).sum < PreForm.length pφ := by
  rcases pφ with ⟨b, _|α, φ|φ⟩
  case none.inl =>
    cases φ <;> cases b <;> simp [PreForm.fischerLadnerStep]
  case none.inr =>
    exfalso
    simp at h
  case some.inl =>
    cases α <;> simp [PreForm.fischerLadnerStep] <;> try omega
    case test => cases b <;> simp_all
  case some.inr =>
    cases α <;> simp [PreForm.fischerLadnerStep]
    case test => cases b <;> simp_all

/-! ## Single Step -/

def PreForm.fischerLadnerClosure (pfs : List PreForm) : List PreForm :=
  let new := pfs.flatMap (fun pφ =>
    if _forTermination : pφ.2.2.isRight then [] else
        let toAdd := PreForm.fischerLadnerStep pφ
        let newer := PreForm.fischerLadnerClosure toAdd
        newer)
  pfs ++ new
termination_by
  (pfs.map PreForm.length).sum
decreasing_by
  apply lt_of_lt_of_le (PreForm.fischerLadnerStep_sum_down _ _forTermination)
  apply List.le_sum_of_mem
  simp
  use pφ

/-! ## Closure for normal Formulas -/

def fischerLadnerClosure (fs : List Formula) : List Formula :=
  (fs.flatMap (fun φ => PreForm.fischerLadnerClosure [ PreForm.ofFormula φ ])).map PreForm.toForm

lemma fLC_closed_under_step (φ : Formula) :
    φ.fischerLadnerStep ⊆ fischerLadnerClosure [φ] := by
  cases φ <;> simp [Formula.fischerLadnerStep]
  case neg φ =>
    cases φ <;> try simp
    case neg φ =>
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case and φ1 φ2 =>
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case box α φ =>
      cases α
      all_goals
        simp [fischerLadnerClosure,PreForm.ofFormula]
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.toForm, PreForm.fischerLadnerStep]
      case atom_prog a =>
        unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
      case sequence α β =>
        right
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
      all_goals -- union, star and test
        constructor <;> right
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
        · unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          unfold PreForm.fischerLadnerClosure
          simp [PreForm.fischerLadnerStep]
  case and φ1 φ2 =>
    simp [fischerLadnerClosure,PreForm.ofFormula]
    unfold PreForm.fischerLadnerClosure
    simp [PreForm.toForm, PreForm.fischerLadnerStep]
    unfold PreForm.fischerLadnerClosure
    simp [PreForm.fischerLadnerStep]
  case box α φ =>
    cases α
    all_goals
      simp [fischerLadnerClosure,PreForm.ofFormula]
      unfold PreForm.fischerLadnerClosure
      simp [PreForm.toForm, PreForm.fischerLadnerStep]
    case atom_prog a =>
      unfold PreForm.fischerLadnerClosure
      unfold PreForm.fischerLadnerClosure -- twice, but not inf. often!
      simp [PreForm.fischerLadnerStep]
    case sequence α β =>
      right
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
    all_goals -- union, star and test
      constructor <;> right
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]
      · unfold PreForm.fischerLadnerClosure
        unfold PreForm.fischerLadnerClosure
        simp [PreForm.fischerLadnerStep]

-- TODO NEXT

-- lemma that fischerLadnerClosure is "transitive" ...
