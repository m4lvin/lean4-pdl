import Std.Tactic.NoMatch

import Pdl.Syntax

inductive DagFormula : Type
  | dag : Program → Formula → DagFormula -- ⌈α†⌉φ
  | box : Program → DagFormula → DagFormula  -- ⌈α⌉ψ
  deriving Repr, DecidableEq

@[simp]
def DagFormula.boxes : List Program → DagFormula → DagFormula
  | [], ψ => ψ
  | (α :: rest), ψ => DagFormula.box α (DagFormula.boxes rest ψ)

inductive NegDagFormula : Type
  | neg : DagFormula → NegDagFormula
  deriving Repr, DecidableEq

local notation "⌈" α "†⌉" φ => DagFormula.dag α φ
local notation "⌈" α "⌉" ψ => DagFormula.box α ψ
local notation "⌈⌈" ps "⌉⌉" df => DagFormula.boxes ps df

local notation "~" ψ => NegDagFormula.neg ψ

-- Borzechowski's function "f".
class Undag (α : Type) where
  undag : α → Formula

open Undag

@[simp]
def undagDagFormula
  | (⌈α†⌉f) => (Formula.box (∗α) f)
  | (⌈α⌉df) => (Formula.box α (undagDagFormula df))

@[simp]
instance UndagDagFormula : Undag DagFormula := Undag.mk undagDagFormula

@[simp]
def undagNegDagFormula : NegDagFormula → Formula
  | (~ ψ) => ~ undag ψ
@[simp]
instance UndagNegDagFormula : Undag NegDagFormula := Undag.mk undagNegDagFormula

@[simp]
def inject : List Program → Program → Formula → DagFormula
  | ps, α, φ => (DagFormula.boxes ps (DagFormula.dag α φ))

@[simp]
theorem undag_boxes : undagDagFormula (⌈⌈ps⌉⌉df) = ⌈⌈ps⌉⌉(undag df) :=
  by
  cases ps
  simp
  simp
  apply undag_boxes

@[simp]
lemma undag_inject {φ} : undag (inject ps α φ) = (⌈⌈ps⌉⌉(⌈∗ α⌉φ)) :=
  by
  simp

theorem ProgramSequenceNotSelfContaining : ∀ (p q: Program), ¬ (p = (p ;' q)) := fun.
theorem ProgramUnionNotSelfContainingLeft : ∀ (p q: Program), ¬ (p = (p⋓q)) := fun.
theorem ProgramUnionNotSelfContainingLeft' : ∀ (p q: Program), ¬ ((p⋓q) = p) := fun.
theorem ProgramUnionNotSelfContainingRight : ∀ (p q: Program), ¬ (q = (p⋓q)) := fun.
theorem ProgramUnionNotSelfContainingRight' : ∀ (p q: Program), ¬ ((p⋓q) = q) := fun.
theorem ProgramTestNotSelfContain (ψ : DagFormula) (φ : Formula) : (¬ψ = ⌈?'φ⌉ψ) := fun.
theorem ProgramStarNotSelfContain (α : Program) : ¬ ((∗α) = α) := fun.
theorem ProgramBoxStarNotSelfContain (α : Program) (ψ : DagFormula) : ¬ ((⌈∗α⌉ψ) = ψ) := fun.
