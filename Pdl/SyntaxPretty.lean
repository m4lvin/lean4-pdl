import Pdl.Syntax

declare_syntax_cat form
declare_syntax_cat prog

syntax "P " num : form
syntax form " ∧ " form : form
syntax form " ∨ " form : form
syntax "¬" form : form
syntax "(" form ")" : form
syntax form " → " form : form
syntax form " ↔ " form : form

syntax "[f|" form "]" : term

syntax "[p|" prog "]" : prog

-- syntax to value

macro_rules
  | `([f| P $x:num]) => `(Formula.atom_prop $x)
  | `([f| $x ∧ $y]) => `(Formula.and [f|$x] [f|$y])
  | `([f| $x ∨ $y]) => `(Formula.or [f|$x] [f|$y])
  | `([f| ¬ $x]) => `(Formula.neg [f|$x])
  | `([f| ($x)]) => `([f|$x])
  | `([f| $x → $y]) => `(Formula.imp [f|$x] [f|$y])

def bla : Formula := [f| P 1 ∧ P 2]

-- Lean terms to pretty stuff in InfoView

@[app_unexpander Formula.atom_prop]
def unexpandAtom : Lean.PrettyPrinter.Unexpander
  | `($_ $n:num) => `([f| P $n])
  | _ => throw ()

@[app_unexpander Formula.or]
def unexpandDisj : Lean.PrettyPrinter.Unexpander
  | `($_ [f| $f] [f| $g]) => `([f| $f ∨ $g])
  | _ => throw ()

@[app_unexpander Formula.and]
def unexpandConj : Lean.PrettyPrinter.Unexpander
  | `($_ [f| $f] [f| $g]) => `([f| $f ∧ $g])
  | _ => throw ()

@[app_unexpander Formula.neg]
def unexpandNeg : Lean.PrettyPrinter.Unexpander
  | `($_ [f| P $x]) => `([f| ¬P $x])
  | `($_ [f| $f]) => `([f| ¬($f)])
  | _ => throw ()

#check [f| ¬ P 1 ∨ P 2]

/-
ideas:
- undeline via unicode to replace ⌊ etc
  https://en.wikipedia.org/wiki/Underscore#Unicode
- underscore P₁₂ ??
-/
