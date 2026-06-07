/-
# Container-shape inference (§4a, the on-demand container recognition).

Reads an inductive declaration and classifies it as a regular polynomial functor in its type
parameters — the class of types `autosubst` can thread substitution through as a nested container
(`List`, `Option`, a user `Tree`, a parameterized user box, a bifunctor, …). This is **structural
metaprogramming only**: no typeclass, no instance, no registry. When `autosubst` meets a head
`(F …)` it tries `containerShape? F`; the generator then emits a mutual structural helper +
per-constructor congruences directly from the returned shape (the generator never calls a `map`).
The standard `List`/`Option` are recognised by this very same check.

A constructor argument is classified against the inductive's type parameters: parameter `i` ⟶ an
**element** slot for applied argument `i`, `F α₀ ... αₙ` ⟶ a **recursive** slot, no parameter
occurrences ⟶ **inert** (carried unchanged). Anything else (a parameter under another container,
contravariant, dependent, or a non-uniform recursive occurrence) ⟹ not a regular functor, declined.
The binary `Prod` is handled inline by the generator; function-space and nested-`F (G α)` types
decline.
-/
import Lean

open Lean Meta

namespace Autosubst.Gen

/-- The role of one constructor argument in a container's structural traversal. -/
inductive ArgKind
  | /-- type parameter `i` — gets the threaded operation for the applied argument in slot `i`. -/ elem (idx : Nat)
  | /-- the inductive itself `F α` — recurse via the mutual helper. -/ recurse
  | /-- mentions no type parameter — carried unchanged. -/ inert
  deriving Repr, BEq, Inhabited

/-- A container's constructors and their per-argument classification (`Name` = the ctor, the array =
one `ArgKind` per explicit argument after the type parameters). -/
abbrev ContainerShape := Array (Name × Array ArgKind)

/-- Classify the arguments of `ctorName` against all inductive parameters. Returns `none` if a
parameter occurs in an unsupported position. -/
def classifyCtor (indName ctorName : Name) (numParams : Nat) :
    MetaM (Option (Array ArgKind)) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallBoundedTelescope ctorInfo.type numParams fun ctorParams body =>
    forallTelescope body fun args _ => do
      let mut kinds : Array ArgKind := #[]
      for arg in args do
        let ty ← inferType arg
        match ctorParams.findIdx? (fun p => ty == p) with
        | some i => kinds := kinds.push (.elem i)
        | none =>
          let recArgs := ty.getAppArgs
          let isUniformRec :=
            ty.isAppOf indName &&
              recArgs.size == numParams &&
              Id.run do
                let mut ok := true
                for i in [:numParams] do
                  ok := ok && recArgs[i]! == ctorParams[i]!
                ok
          if isUniformRec then kinds := kinds.push .recurse
          else if ctorParams.any (fun p => ty.containsFVar p.fvarId!) then
            return none
          else kinds := kinds.push .inert
      return some kinds

/-- The full classification of `indName` as a regular container, or `none` if it is **not** a
polynomial functor in its parameters — including when it is not an inductive at all (a `def` like
`cod = fun α => X → α`) or uses a parameter in an unsupported position. Robust (never throws), so it
can be tried **on demand** on any head appearing in a signature. -/
def containerShape? (indName : Name) : MetaM (Option ContainerShape) := do
  let some (.inductInfo indInfo) := (← getEnv).find? indName | return none
  if indInfo.numParams < 1 then return none
  let mut shape : ContainerShape := #[]
  for c in indInfo.ctors do
    match ← classifyCtor indName c indInfo.numParams with
    | none => return none
    | some ks => shape := shape.push (c, ks)
  return some shape

end Autosubst.Gen
