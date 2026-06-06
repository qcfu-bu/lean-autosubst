/-
# Phase 2 — Signature analysis.

Lean analogue of the reference generator's `lib/sigAnalyzer.ml`. Refines a parsed `Spec`
into an analyzed `Signature` by computing, per the exact Autosubst algorithm:

1. the **dependency graph**: edge `t → v` iff sort `v` is an argument head in a
   constructor of `t`;
2. the **open (substitution) sorts**: `x` is open iff it is bound somewhere *and* the
   bound variable can actually occur (non-vacuous, via transitive closure). A binder that
   can never occur is a *vacuous* binding — an error;
3. the **substitution vector** of `t`: the open sorts (in canonical order) that are
   *reflexively* reachable from `t` — i.e. the maps `ren_t`/`subst_t` must thread;
4. the **components**: strongly-connected components (mutual blocks), dependency-ordered.
-/
import LeanAutosubst.IR.Language

open Lean

namespace Autosubst.IR

/-- A sort enriched with the results of analysis. -/
structure SortInfo where
  name : SortId
  params : List Param := []
  ctors : List Constructor
  /-- Has variables (a `var_` constructor): bound somewhere, non-vacuously. -/
  isOpen : Bool
  /-- Substitution vector: open sorts (canonical order) reflexively reachable from `name`.
  `ren_name`/`subst_name` take one map per entry; empty ⇒ the sort needs no substitution. -/
  substVec : List SortId
  /-- Direct dependency successors (sorts referenced in argument heads). -/
  args : List SortId
  deriving Repr

/-- The fully analyzed signature. -/
structure Signature where
  sorts : List SortInfo
  /-- SCCs / mutual blocks, dependency-ordered (a block precedes blocks that depend on it). -/
  components : List (List SortId)
  deriving Repr

namespace Signature

/-- The default container/functor heads when none are inferred — the standard Lean containers. The
real recognised set is computed **on demand** by `Frontend.Elab` (any inductive regular in its type
parameters — `containerShape?`) and passed into `analyze` as `containers`. -/
def supportedFunctors : List Name := [`List, `Option, `Prod]

/-- The name of an unsupported functor head that wraps a declared sort (so substitution *would*
need to thread through it), if any. `List (cod term)` reports `cod`; `List Nat`, `Array Bool`
(no declared sort inside) are fine as opaque leaves. `containers` is the recognised set (standard +
registered). -/
partial def badFunctor (containers : List Name) (declared : List SortId) : ArgHead → Option Name
  | .sort _ args => args.findSome? (badFunctor containers declared)
  | .ext _ | .opaque _ => none
  | .functor f args =>
    if !containers.contains f && (args.flatMap ArgHead.argSorts).any declared.contains then
      some f
    else args.findSome? (badFunctor containers declared)

/-- Direct successors of `t`: declared sorts referenced in `t`'s constructor argument heads. -/
def directArgs (sp : Spec) (t : SortId) : List SortId :=
  match sp.sorts.find? (·.name == t) with
  | none => []
  | some sd => (sd.ctors.flatMap Constructor.argSorts).eraseDups.filter sp.sortNames.contains

/-- Fixpoint expansion of a reachability frontier. -/
partial def closure (succ : SortId → List SortId) (acc frontier : List SortId) : List SortId :=
  let next := (frontier.flatMap succ).filter (fun y => !acc.contains y) |>.eraseDups
  if next.isEmpty then acc else closure succ ((acc ++ next).eraseDups) next

/-- Sorts reachable from `t` in ≥1 step (transitive closure). -/
def reachStrict (succ : SortId → List SortId) (t : SortId) : List SortId :=
  closure succ (succ t).eraseDups (succ t)

/-- Sorts reachable from `t` in ≥0 steps (reflexive-transitive closure). -/
def reachRefl (succ : SortId → List SortId) (t : SortId) : List SortId :=
  (t :: reachStrict succ t).eraseDups

/-- Analyze a parsed spec, or fail with a vacuous-binding error. `sc` selects the well-scoped
backend, which alone supports variadic `bind ⟨p, _⟩` binders (the unscoped/`Nat` variadic form is
unported, as upstream — see plan.md §9/§10). -/
def analyze (sp : Spec) (sc : Bool := false) (containers : List Name := supportedFunctors) :
    Except String Signature := do
  let succ := directArgs sp
  let canonical := sp.sortNames
  let paramSig (ps : List Param) : List (Name × Syntax × Bool) :=
    ps.map fun p => (p.name, p.type, p.implicit)
  match sp.sorts with
  | [] => pure ()
  | sd0 :: rest =>
      let base := paramSig sd0.params
      for sd in rest do
        unless paramSig sd.params == base do
          throw s!"Parameterized mutual signatures currently require compatible parameter telescopes; \
            sort '{sd.name}' does not match sort '{sd0.name}'."
  -- (1b) reject variadic binders `bind ⟨p, t⟩` in **unscoped** mode — unported there (would lower
  -- to a *single* lift, silently wrong). In scoped mode they are threaded via `scons_p`/`shift_p`
  -- (plan.md §9/§10). Fixed-arity multi-binders `bind a, b` are fine in both.
  unless sc do
    for sd in sp.sorts do
      for c in sd.ctors do
        for pos in c.positions do
          for b in pos.binders do
            if let .vector _ x := b then
              throw s!"Variadic binder 'bind ⟨_, {x}⟩' in constructor '{c.name}' of sort '{sd.name}' \
                is not supported in unscoped mode (use `autosubst wellscoped`; the unscoped variadic \
                form is unported, as upstream)."
  -- (1c) reject heads we can't thread substitution through. `containers` is the set of heads
  -- recognised **on demand** as container functors (`Prod`, or a regular polynomial functor in its
  -- type parameters — `List`/`Option`/a user `Tree`); a head wrapping a declared sort that is *not* one of these
  -- (a function-space "functor" like `fol`'s `cod`, a non-regular/nested or dependent type) cannot be
  -- threaded and is rejected here rather than lowered to undefined code.
  for sd in sp.sorts do
    for c in sd.ctors do
      for pos in c.positions do
        if let some f := badFunctor containers canonical pos.head then
          throw s!"Cannot thread substitution through container head '{f}' in constructor \
            '{c.name}' of sort '{sd.name}': '{f}' must be `Prod` or an inductive regular in its \
            type parameters, whose constructor arguments use parameters only as elements, \
            uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). \
            Function-space or non-regular types (like `cod`) are unsupported."
  -- (2) binder analysis: collect open sorts; reject vacuous bindings.
  let mut openSet : List SortId := []
  for sd in sp.sorts do
    for c in sd.ctors do
      for pos in c.positions do
        for b in pos.binders do
          let x := b.boundSort
          let nonVacuous := pos.head.argSorts.any (fun a => (reachStrict succ a).contains x)
          if nonVacuous then
            openSet := x :: openSet
          else
            throw s!"Vacuous binding of '{x}' in constructor '{c.name}' of sort '{sd.name}'"
  let openSorts := openSet.eraseDups
  let isOpen (t : SortId) : Bool := openSorts.contains t
  -- (2b) variadic binders are supported only for **single-open-sort** signatures (the reference
  -- `variadic.sig` shape): then the bound sort always coincides with the lone substitution
  -- component, so the `up_list_b_v` tower has `b = v`. Multi-open-sort variadic (cross-sort
  -- `up_list_b_v` with `b ≠ v`) is unported.
  let hasVariadic := sp.sorts.any fun sd => sd.ctors.any fun c => c.positions.any fun pos =>
    pos.binders.any fun b => match b with | .vector _ _ => true | _ => false
  if hasVariadic && openSorts.length > 1 then
    throw s!"Variadic binders 'bind ⟨p, _⟩' are only supported for single-substitution-sort \
      signatures (open sorts here: {openSorts}); multi-sort variadic binding is unported."
  -- (3) substitution vectors.
  let sortInfos := sp.sorts.map fun sd =>
    let refl := reachRefl succ sd.name
    { name := sd.name, params := sd.params, ctors := sd.ctors, isOpen := isOpen sd.name
    , substVec := canonical.filter (fun s => isOpen s && refl.contains s)
    , args := succ sd.name }
  -- (4) components: group canonical sorts into SCCs, ordered by first appearance.
  let sameComp (u v : SortId) : Bool := (reachRefl succ u).contains v && (reachRefl succ v).contains u
  let mut comps : List (List SortId) := []
  for t in canonical do
    unless comps.any (·.contains t) do
      comps := comps ++ [canonical.filter (sameComp t)]
  return { sorts := sortInfos, components := comps }

end Signature
end Autosubst.IR
