import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
# Find why something depends on which axioms

This code is by Kyle Miller from https://is.gd/Ug5sXu

Importing this file provides a comment `#axiom_blame` that creates output like this:

```
#axiom_blame interpolation

'interpolation' depends on axioms:

* Quot.sound: interpolation → Interpolant → Vocab → Finset → Finset.mk → Multiset.Nodup → Multiset.Nodup._proof_1 → List.Perm.nodup_iff → List.Perm.pairwise_iff → List.pairwise_middle → List.pairwise_append → forall_congr → funext → Quot.sound

* Classical.choice: interpolation → Interpolant → Finset.instPartialOrder → Finset.instSetLike → Finset.instSetLike._proof_1 → Multiset.Nodup.ext → List.perm_ext_iff_of_nodup → Classical.propDecidable → Classical.choice

* propext: interpolation → Interpolant → Vocab → Finset → Finset.mk → Multiset.Nodup → Multiset.Nodup._proof_1 → propext
Theorem.lean:54:0
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
