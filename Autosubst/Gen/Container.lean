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
parameter occurs in an unsupported position. Declines (per the module doc) when a constructor
field is implicit/instance-implicit (the emitters destructure/apply ctors fully explicitly), when a
field's type depends on an *earlier field* (a genuinely dependent constructor — the per-ctor
congruence would be ill-typed), or when a non-leaf constructor has a type parameter that occurs in
none of its field types (an uninferable/phantom parameter — the congruence cannot pin it). -/
def classifyCtor (indName ctorName : Name) (numParams : Nat) :
    MetaM (Option (Array ArgKind)) := do
  let ctorInfo ← getConstInfoCtor ctorName
  forallBoundedTelescope ctorInfo.type numParams fun ctorParams body =>
    forallTelescope body fun args _ => do
      let mut kinds : Array ArgKind := #[]
      let mut seenFields : Array Expr := #[]   -- earlier field fvars (dependent-field detection)
      for arg in args do
        -- A field with non-default binder info (implicit/instance) can't be matched and re-applied
        -- explicitly the way every emitter does; decline rather than emit over-/under-applied ctors.
        match (← arg.fvarId!.getDecl).binderInfo with
        | .default => pure ()
        | _ => return none
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
          else if seenFields.any (fun f => ty.containsFVar f.fvarId!) then
            return none   -- a field whose type depends on an earlier field: genuinely dependent
          else kinds := kinds.push .inert
        seenFields := seenFields.push arg
      -- A non-leaf constructor (one that gets a generated congruence) must let every type parameter
      -- be inferred from some field's type; otherwise the congruence has an unsolvable metavariable.
      if kinds.any (· != ArgKind.inert) then
        for p in ctorParams do
          let used ← args.anyM (fun a => return (← inferType a).containsFVar p.fvarId!)
          unless used do return none
      return some kinds

/-- The full classification of `indName` as a regular container, or `none` if it is **not** a
polynomial functor in its parameters — including when it is not an inductive at all (a `def` like
`cod = fun α => X → α`) or uses a parameter in an unsupported position. Robust (never throws), so it
can be tried **on demand** on any head appearing in a signature. -/
def containerShape? (indName : Name) : MetaM (Option ContainerShape) := do
  let env ← getEnv
  -- Resolve the head name honoring the current namespace and `open`s (the DSL hands us the surface
  -- ident verbatim), so a container reached via `open`, the enclosing namespace, or `_root_.` is
  -- recognised instead of being declined as "not a regular functor". Fall back to the raw name so a
  -- genuinely unknown/irregular head still declines through the same path.
  let cands ← resolveGlobalName indName
  let indName := (cands.findSome? fun (n, fields) =>
    if fields.isEmpty then
      match env.find? n with
      | some (.inductInfo _) => some n
      | _ => none
    else none).getD indName
  let some (.inductInfo indInfo) := env.find? indName | return none
  if indInfo.numParams < 1 then return none
  -- Indexed families, empty (constructor-less) inductives, and `Prop`-valued inductives cannot be
  -- threaded as Type-valued containers (ill-typed match arms / empty matches / kernel universe
  -- errors downstream); decline them here so they route through the clean `badFunctor` message.
  if indInfo.numIndices != 0 then return none
  if indInfo.ctors.isEmpty then return none
  let resultIsProp ← forallTelescopeReducing indInfo.type fun _ body =>
    return match body with | .sort lvl => lvl == Level.zero | _ => false
  if resultIsProp then return none
  let mut shape : ContainerShape := #[]
  for c in indInfo.ctors do
    match ← classifyCtor indName c indInfo.numParams with
    | none => return none
    | some ks => shape := shape.push (c, ks)
  return some shape

end Autosubst.Gen
