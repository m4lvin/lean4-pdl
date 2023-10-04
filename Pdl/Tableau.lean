import Pdl.Syntax
import Pdl.Semantics
import Pdl.Discon

-- TABLEAU

-- TODO: upper vs lower case messy
inductive Rule
  | bot : Rule
  | neg : Rule
  | imp : Rule
  | Con : Rule
  | negCon : Rule
  | tst : Rule
  | negTst : Rule
  | seq : Rule
  | negSeq : Rule
  | cup : Rule
  | negCup : Rule
  | atm : Rule
  | Star : Rule

-- actually ¬n ?

-- NOTE: to be replaced with defintiions for basic modal logic in tablean project
inductive Tableau
  | leaf : Set Formula → Tableau
  | Rule : Rule → List (Set Formula) → Tableau

def projection : Char → Formula → Option Formula
  | a, ⌈·b⌉ f => if a = b then some f else none
  | _, _ => none

-- Given a formula, is their an applicable rule?
-- If so, which one, and what formulas are the result?
def ruleFor : Formula → Option (Rule × Set (Set Formula) × (Formula → Option Formula))
  -- Nothing to do:
  | ·c => none
  | ~·c => none
  | ~⊥ => none
  -- Single-branch rules:
  | ⊥ => some (Rule.bot, {∅}, some)
  | ~~f => some (Rule.neg, {{f}}, some)
  | f⋀g => some (Rule.Con, {{f, g}}, some)
  | ~⌈✓f⌉ g => some (Rule.negTst, {{f, ~g}}, some)
  |-- TODO should remove marking
    ~⌈a;b⌉ f =>
    some (Rule.negSeq, {{~⌈a⌉ (⌈b⌉ f)}}, some)
  | ⌈·a⌉ f => none
  | ⌈Program.union a b⌉ f => some (Rule.cup, {{⌈a⌉ f, ⌈b⌉ f}}, some)
  | ⌈a;b⌉ f => some (Rule.seq, {{⌈a⌉ (⌈b⌉ f)}}, some)
  -- TODO: assumption for now: only may be applied if there is a marking!?
  | ⌈∗a⌉ f => none
  -- Splitting rules:
  | ~f⋀g => some (Rule.negCon, {{~f}, {~g}}, some)
  | ⌈✓f⌉ g => some (Rule.tst, {{~f}, {g}}, some)
  | ~⌈Program.union a b⌉ f => some (Rule.negCup, {{~⌈a⌉ f}, {~⌈b⌉ f}}, some)
  | ~⌈∗a⌉ f => some (Rule.Star, {{~f}, {~⌈a⌉ (⌈∗a⌉ f)}}, some)
  | ~⌈·a⌉ f => some (Rule.atm, {{~f}}, projection a)
  -- TODO should sometimes remove marking?
  -- n-star / stopping rules?
  | †f => none
  | ~†f => none
