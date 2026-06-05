/-
# Phase 2 — Signature IR (the parsed HOAS spec).

Lean analogue of the reference generator's `lib/language.ml`. These types are the
*data* a HOAS spec is lowered to: sorts, constructors, argument positions, binders,
and (functor) argument heads. The frontend ([Frontend/Elab.lean]) produces a `Spec`;
the analyzer ([IR/Signature.lean]) refines it into an analyzed `Signature`.

Designed for **multi-sorting** and **nested containers** from the start (Scope §1/§4a):
- `ArgHead.functor` models a container (`List`, `Prod`, `Option`, `Vector`, …) applied
  to sub-heads, so a sort nested inside a container is discoverable by the analyzer.
- `Binder.vector` models the variadic `bind <p, s>` form.
-/

open Lean

namespace Autosubst.IR

/-- A sort identifier (name of a syntactic category). We use `Name` so generated
declarations can use it directly. -/
abbrev SortId := Name

/-- A binder introduced at a constructor-argument position. `single s` is `bind s in _`;
`vector p s` is the variadic `bind <p, s> in _`. -/
inductive Binder where
  | single (sort : SortId)
  | vector (param : Name) (sort : SortId)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The sort of variable a binder introduces. -/
def Binder.boundSort : Binder → SortId
  | .single s => s
  | .vector _ s => s

/-- The head type of a constructor argument, after stripping its binders.
`sort s` references a declared sort; `functor f args` is a container applied to sub-heads;
`ext` is an external Lean type opaque to substitution (carried, never recursed into). -/
inductive ArgHead where
  | sort (s : SortId)
  | functor (f : Name) (args : List ArgHead)
  | ext (head : Name)
  deriving Repr, BEq, Inhabited

/-- All declared sorts mentioned (recursively) in a head — used to build the dependency
graph. `ext` heads contribute none. Mirrors `language.ml`'s `getArgSorts`. -/
partial def ArgHead.argSorts : ArgHead → List SortId
  | .sort s => [s]
  | .functor _ args => args.flatMap ArgHead.argSorts
  | .ext _ => []

/-- Every functor/container head name occurring (recursively) in an argument head — the candidates
the analyzer/generator test for container-hood on demand. -/
partial def ArgHead.functorHeads : ArgHead → List SortId
  | .sort _ | .ext _ => []
  | .functor f args => f :: args.flatMap ArgHead.functorHeads

/-- A constructor argument: a (possibly empty) list of binders wrapping a head type.
`bind a, b in h` ⇒ `{ binders := [a, b], head := h }`. -/
structure Position where
  binders : List Binder
  head : ArgHead
  deriving Repr, BEq, Inhabited

/-- A single (non-variable) constructor. `params` are variadic parameters like `(p : Nat)`. -/
structure Constructor where
  name : Name
  params : List (Name × SortId) := []
  positions : List Position
  deriving Repr, BEq, Inhabited

/-- A declared sort together with its (non-variable) constructors. -/
structure SortDecl where
  name : SortId
  ctors : List Constructor
  deriving Repr, BEq, Inhabited

/-- The parsed HOAS spec: sorts in declaration ("canonical") order. -/
structure Spec where
  sorts : List SortDecl
  deriving Repr, BEq, Inhabited

/-- The declared sort names, in canonical order. -/
def Spec.sortNames (s : Spec) : List SortId := s.sorts.map (·.name)

/-- Every declared sort referenced in a constructor's argument heads. -/
def Constructor.argSorts (c : Constructor) : List SortId :=
  c.positions.flatMap (fun p => p.head.argSorts)

end Autosubst.IR
