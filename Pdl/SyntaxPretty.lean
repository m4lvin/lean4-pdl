import Pdl.Syntax

declare_syntax_cat form
declare_syntax_cat prog

syntax "P" num : form
syntax ident : form
syntax form " ∧ " form : form
syntax form " ∨ " form : form
syntax "¬" form : form
syntax "(" form ")" : form
syntax form " → " form : form
syntax form " ↔ " form : form

syntax "[f|" form "]" : term

syntax "[p|" prog "]" : prog

def String.subscriptToNat? (s : String) : Option Nat :=
  let s' := s.toList.toArray.map (fun c => match c with
    | '₀' => '0'
    | '₁' => '1'
    | '₂' => '2'
    | '₃' => '3'
    | '₄' => '4'
    | '₅' => '5'
    | '₆' => '6'
    | '₇' => '7'
    | '₈' => '8'
    | '₉' => '9'
    | _ => c)
  s'.toList.asString.toNat?

-- syntax to value
macro_rules
  | `([f| P $x:num]) => `(Formula.atom_prop $x)
  | `([f| $s:ident]) => match s.getId.toString.toList with
    | 'P' :: n => match n.asString.subscriptToNat? with
       | some n => `(Formula.atom_prop $(Lean.quote n))
       | none => match n.asString.toNat? with
         | some n => `(Formula.atom_prop $(Lean.quote n))
         | none => throw Lean.Macro.Exception.unsupportedSyntax
    | _ => throw Lean.Macro.Exception.unsupportedSyntax
  | `([f| $x ∧ $y]) => `(Formula.and [f|$x] [f|$y])
  | `([f| $x ∨ $y]) => `(Formula.or [f|$x] [f|$y])
  | `([f| ¬ $x]) => `(Formula.neg [f|$x])
  | `([f| ($x)]) => `([f|$x])
  | `([f| $x → $y]) => `(Formula.imp [f|$x] [f|$y])

def bla : Formula := [f| P₁ ∧ P2]

-- Lean terms to pretty stuff in InfoView
@[app_unexpander Formula.atom_prop]
def unexpandAtom : Lean.PrettyPrinter.Unexpander
  | `($_ $n:num) => if n.getNat < 9
      then
        let Pstr := "P" ++ (Nat.toSubscriptString n.getNat)
        let Pident : Lean.Ident := Lean.mkIdent <| Lean.Name.mkSimple Pstr
        let Pform : Lean.TSyntax `form := { raw := Pident.raw } -- crude coercion
        -- Because Lean won't accept otherwise that an `ident` is a `form`.
        `([f| $Pform])
      else `([f| P $n])
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

#eval (Nat.toSubscriptString 12) == ((Nat.toSubscriptString 1) ++ (Nat.toSubscriptString 2))
#check Formula.atom_prop
#check [f| ¬ P1 ∨ P₂ ∧ P 3 ]

/-
ideas:
- undeline via unicode to replace ⌊ etc
  https://en.wikipedia.org/wiki/Underscore#Unicode
-/
