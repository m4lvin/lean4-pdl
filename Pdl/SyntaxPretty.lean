import Pdl.Syntax

declare_syntax_cat form
declare_syntax_cat prog

/- would this make sense?
declare_syntax_cat pdl
syntax form : pdl
syntax prog : pdl
syntax "⌜" pdl "⌝" : term
-/

syntax "P" num : form
syntax ident : form
syntax form " ∧ " form : form
syntax form " ∨ " form : form
syntax "¬" form : form
syntax "(" form ")" : form
syntax form " → " form : form
syntax form " ↔ " form : form
syntax "[" prog "]" form : form

syntax "⌜" form "⌝" : term

syntax "A" num : prog
syntax ident : prog
syntax prog " ; " prog : prog
syntax prog " ∪ " prog : prog
syntax "?" form : prog
syntax "(" prog ")" : prog
syntax prog "* " : prog

syntax "⌞" prog "⌟" : term

-- Nice helper tricker by Andrés.
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

set_option pp.rawOnError true

/-- Mapping the syntax to values. -/
macro_rules
  -- formulas:
  | `(⌜ P $x:num ⌝) => `(Formula.atom_prop $x)
  | `(⌜ $s:ident ⌝) => match s.getId.toString.toList with
    | 'P' :: n => match n.asString.subscriptToNat? with
       | some n => `(Formula.atom_prop $(Lean.quote n))
       | none => match n.asString.toNat? with
         | some n => `(Formula.atom_prop $(Lean.quote n))
         | none => throw Lean.Macro.Exception.unsupportedSyntax
    | _ => throw Lean.Macro.Exception.unsupportedSyntax
  | `(⌜ $x ∧ $y ⌝) => `(Formula.and ⌜$x⌝ ⌜$y⌝)
  | `(⌜ $x ∨ $y ⌝) => `(Formula.or ⌜$x⌝ ⌜$y⌝)
  | `(⌜ ¬ $x ⌝) => `(Formula.neg ⌜$x⌝)
  | `(⌜ ($x) ⌝) => `(⌜$x⌝)
  | `(⌜ $x → $y ⌝) => `(Formula.imp ⌜$x⌝ ⌜$y⌝)
  -- programs:
  | `(⌞ $x ∪ $y ⌟) => `(Program.union ⌞$x⌟ ⌞$y⌟)
  | `(⌞ $s:ident ⌟) => match s.getId.toString.toList with
    | 'A' :: n => match n.asString.subscriptToNat? with
      | some n => `(Program.atom_prog $(Lean.quote n))
      | none => match n.asString.toNat? with
        | some n => `(Program.atom_prog $(Lean.quote n))
        | none => throw Lean.Macro.Exception.unsupportedSyntax
    | _ => throw Lean.Macro.Exception.unsupportedSyntax
  | `(⌜ [$α] $φ ⌝) => `(Formula.box ⌞$α⌟ ⌜$φ⌝ )

def bla : Formula := ⌜[A₁] P₁ ∧ P2 ∧ P 8 ∧ P 9 ⌝

#eval bla -- not pretty, because there is no unexpander yet

-- Lean terms to pretty stuff in InfoView
@[app_unexpander Formula.atom_prop]
def unexpandAtom : Lean.PrettyPrinter.Unexpander
  | `($_ $n:num) => if n.getNat < 9
      then
        let Pstr := "P" ++ (Nat.toSubscriptString n.getNat)
        let Pident : Lean.Ident := Lean.mkIdent <| Lean.Name.mkSimple Pstr
        let Pform : Lean.TSyntax `form := { raw := Pident.raw } -- crude coercion
        -- Because Lean won't accept otherwise that an `ident` is a `form`.
        `(⌜$Pform⌝)
      else `(⌜P $n⌝)
  | _ => throw ()

@[app_unexpander Formula.or]
def unexpandDisj : Lean.PrettyPrinter.Unexpander
  | `($_ ⌜$f⌝ ⌜$g⌝) => `(⌜$f ∨ $g⌝)
  | _ => throw ()

@[app_unexpander Formula.and]
def unexpandConj : Lean.PrettyPrinter.Unexpander
  | `($_ ⌜$f⌝ ⌜$g⌝) => `(⌜$f ∧ $g⌝)
  | _ => throw ()

@[app_unexpander Formula.neg]
def unexpandNeg : Lean.PrettyPrinter.Unexpander
  | `($_ ⌜P $x⌝) => `(⌜¬P $x⌝)
  | `($_ ⌜¬ $f⌝) => `(⌜¬¬($f)⌝)
  | `($_ ⌜$f⌝) => `(⌜¬($f)⌝)
  | _ => throw ()

@[app_unexpander Formula.box]
def unexpandBox : Lean.PrettyPrinter.Unexpander
  | `($_ ⌞$α⌟ ⌜$f⌝) => `(⌜ [ $α ] $f ⌝)
  | _ => throw ()

@[app_unexpander Program.union]
def unexpandUnion : Lean.PrettyPrinter.Unexpander
  | `($_ ⌞$a⌟ ⌞$b⌟) => `(⌞ $a ∪ $b⌟)
  | _ => throw ()

#eval bla -- pretty now, but why is 9 not a subscript?

#eval (Nat.toSubscriptString 12) == ((Nat.toSubscriptString 1) ++ (Nat.toSubscriptString 2))
#check Formula.atom_prop
#eval ⌜¬ P1 ∨ P₂ ∧ P 3⌝

#eval ⌜[A1] ¬ P1 ∨ P₂ ∧ P 3⌝ -- not using `unexpandBox` apparently?

/-
ideas:
- undeline via unicode to replace ⌊ etc
  https://en.wikipedia.org/wiki/Underscore#Unicode
-/
