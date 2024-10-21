import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
# Find why something depends on which axioms

This code is by Kyle Miller from here:
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/.E2.9C.94.20Finding.20usages.20of.20.60sorry.60.20in.20external.20code/near/430509619

Importing this file provides a comment `#axiom_blame` that creates output like this:

```
#axiom_blame FinEnum.toList

'FinEnum.toList' depends on axioms:

* Quot.sound: FinEnum.toList → Equiv.instFunLike → Equiv.instFunLike.proof_1 → EquivLike.toFunLike → EquivLike.toFunLike.proof_1 → Function.LeftInverse.eq_rightInverse → Function.RightInverse.comp_eq_id → funext → Quot.sound

* Classical.choice: FinEnum.toList → List.finRange → List.finRange.proof_1 → List.mem_range → Init.Data.List.Nat.Range._auxLemma.10 → List.mem_range'_1 → Init.Data.List.Nat.Range._auxLemma.9 → List.mem_range' → Init.Data.Nat.Lemmas._auxLemma.9 → Nat.self_eq_add_left → Classical.propDecidable → Classical.choice

* propext: FinEnum.toList → List.finRange → List.finRange.proof_1 → List.mem_range → Init.Data.List.Nat.Range._auxLemma.10 → propext
```
-/

section
open Lean Elab Command

namespace CollectAxiomBlame

structure State where
  visited : NameSet      := {}
  axioms  : NameMap (List Name) := {}

abbrev M := ReaderT Environment $ StateM State

partial def collect (src : List Name) (c : Name) : M Unit := do
  let collectExpr (src' : List Name) (e : Expr) : M Unit := e.getUsedConstants.forM (collect src')
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    let src' := c :: src
    match env.find? c with
    | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with axioms := s.axioms.insert c src' }
    | some (ConstantInfo.defnInfo v)   => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr src' v.type
    | some (ConstantInfo.recInfo v)    => collectExpr src' v.type
    | some (ConstantInfo.inductInfo v) => collectExpr src' v.type *> v.ctors.forM (collect src')
    | none                             => pure ()

end CollectAxiomBlame

elab "#axiom_blame " id:ident : command => Elab.Command.liftTermElabM do
  let n ← Elab.realizeGlobalConstNoOverloadWithInfo id
  Elab.addCompletionInfo <| .id id id.getId (danglingDot := false) {} none
  let env ← getEnv
  let (_, s) := ((CollectAxiomBlame.collect [] n).run env).run {}
  if s.axioms.isEmpty then
    logInfo m!"'{n}' does not depend on any axioms"
  else
    let mut msgs := #[]
    for (ax, decls) in s.axioms do
      msgs := msgs.push m!"* {ax}: {MessageData.joinSep (decls.reverse.map toMessageData) " → "}"
      logInfo m!"'{n}' depends on axioms:\n\n{MessageData.joinSep msgs.toList "\n\n"}"
  logInfo m!"{n}"

end
