import Pdl.Syntax

-- ft may be Formula or DagFormula
inductive Loaded (ft : Type) : Type
  | free : Formula → Loaded ft
  | loadnbox : List Program → Formula → Loaded ft
  deriving Repr
