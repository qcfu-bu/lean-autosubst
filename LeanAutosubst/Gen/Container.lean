/-
# Container-shape inference (§4a, the on-demand container recognition).

Reads an inductive declaration and classifies it as a *unary regular polynomial functor* — the class
of types `autosubst` can thread substitution through as a nested container (`List`, `Option`, a user
`Tree`, …). This is **structural metaprogramming only**: no typeclass, no instance, no registry. When
`autosubst` meets a head `(F …)` it tries `containerShape? F`; the generator then emits a mutual
structural helper + per-constructor congruences directly from the returned shape (the generator never
calls a `map`). The standard `List`/`Option` are recognised by this very same check.

A constructor argument is classified against the inductive's element parameter `α`: `α` ⟶ an
**element** slot, `F α` ⟶ a **recursive** slot, no-`α` ⟶ **inert** (carried unchanged). Anything
else (`α` under another container, contravariant, dependent) ⟹ not a regular functor, declined.
Scope: single-parameter regular containers (binary `Prod` is handled inline by the generator;
function-space and nested-`F (G α)` types decline).
-/
import Lean

open Lean Meta

namespace Autosubst.Gen

/-- The role of one constructor argument in a container's structural traversal. -/
inductive ArgKind
  | /-- the element parameter `α` — gets the threaded operation applied. -/ elem
  | /-- the inductive itself `F α` — recurse via the mutual helper. -/ recurse
  | /-- mentions no `α` — carried unchanged. -/ inert
  deriving Repr, BEq, Inhabited

/-- A container's constructors and their per-argument classification (`Name` = the ctor, the array =
one `ArgKind` per explicit argument after the type parameters). -/
abbrev ContainerShape := Array (Name × Array ArgKind)

/-- Classify the arguments of `ctorName` (a constructor of a 1-parameter inductive `indName`) against
the ctor's own element parameter. Returns `none` if `α` occurs in an unsupported position. -/
def classifyCtor (indName ctorName : Name) (numParams : Nat) :
    MetaM (Option (Array ArgKind)) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallBoundedTelescope ctorInfo.type numParams fun ctorParams body =>
    forallTelescope body fun args _ => do
      let α := ctorParams[numParams - 1]!
      let mut kinds : Array ArgKind := #[]
      for arg in args do
        let ty ← inferType arg
        if ty == α then kinds := kinds.push .elem
        else if ty.isAppOf indName && ty.getAppArgs.back? == some α then kinds := kinds.push .recurse
        else if ty.containsFVar α.fvarId! then return none   -- `α` in an unsupported position
        else kinds := kinds.push .inert
      return some kinds

/-- The full classification of `indName` as a unary container, or `none` if it is **not** a
single-parameter regular polynomial functor — including when it is not an inductive at all (a `def`
like `cod = fun α => X → α`), has the wrong arity, or uses its parameter in an unsupported position.
Robust (never throws), so it can be tried **on demand** on any head appearing in a signature. -/
def containerShape? (indName : Name) : MetaM (Option ContainerShape) := do
  let some (.inductInfo indInfo) := (← getEnv).find? indName | return none
  if indInfo.numParams != 1 then return none
  let mut shape : ContainerShape := #[]
  for c in indInfo.ctors do
    match ← classifyCtor indName c indInfo.numParams with
    | none => return none
    | some ks => shape := shape.push (c, ks)
  return some shape

end Autosubst.Gen
