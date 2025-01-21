import Bml.Semantics

def Bisimulation (W W': Type) (M : KripkeModel W) (M' : KripkeModel W') : Type :=
  sorry

def bisimilar : (KripkeModel W × W) → (KripkeModel W × W) → Prop :=
  sorry

def modelEquiv (Mw : KripkeModel W × W) (Mw' : KripkeModel W' × W') : Prop :=
  ∀ (φ : Formula), Mw ⊨ φ ↔ Mw' ⊨ φ

infixl:77 "≣" => modelEquiv

theorem modelEquiv_iff_bisimilar (M : KripkeModel W) (w : W) :
  ((M,w) ≣ (M',w')) ↔ bisimilar (M,w) (M',w') := by
  constructor
  · sorry
  · sorry
