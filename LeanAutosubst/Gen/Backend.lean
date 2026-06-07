/-
# Phase 8 — Variable-backend abstraction (unscoped `Nat` vs well-scoped `Fin`).

The generator is parameterized over a `scoped : Bool` flag (set by `autosubst wellscoped …`).
This module isolates everything that differs between the two backends so the rest of `Gen/*`
threads a single `sc : Bool`:

  • the prelude identifiers that differ (`scons`/`var_zero`/`shift`/`up_ren`/`up_ren_ren` live in
    `Autosubst.Scoped` in scoped mode, `Autosubst` in unscoped mode);
  • the **scope-index machinery**: in scoped mode a substitution sort `s` is indexed by one `Nat`
    per entry of its substitution vector (`tm : Nat → Nat → Type`), maps become `Fin m → Fin n`
    / `Fin m → s …`, and every declaration gains scope parameters. We exploit Lean's
    `autoImplicit`: scope variables appear as free identifiers `<stage>_<sort>` (e.g. `m_tm`,
    `k_ty`) in the generated types and Lean auto-binds them — so only the *types* change, not the
    proof terms / match arms, which stay shared with the unscoped path.

A **stage** is a letter (`"m"`,`"k"`,`"l"`,`"n"`) naming a point in a composition chain; a map
for component `v` going from stage `A` to `B` has type `Fin A_v → Fin B_v` (renaming) or
`Fin A_v → v <B-scopes>` (substitution). Sharing the stage letter across composing maps is what
makes their scopes line up (`xi : Fin m_v → Fin k_v`, `zeta : Fin k_v → Fin l_v`).
-/
import Lean
import LeanAutosubst.Prelude.Unscoped
import LeanAutosubst.Prelude.Scoped
import LeanAutosubst.IR.Signature

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-! ## Shared signature lookups -/

/-- The `var_<sort>` constructor name. -/
def varName (s : SortId) : Name := Name.mkSimple s!"var_{s}"

/-- Substitution vector of `s` (open sorts, canonical order, reflexively reachable). -/
def vecOf (sig : Signature) (s : SortId) : List SortId :=
  (sig.sorts.find? (·.name == s)).map (·.substVec) |>.getD []

/-- All open (variable-carrying) sorts. -/
def openSorts (sig : Signature) : List SortId :=
  sig.sorts.filterMap (fun si => if si.isOpen then some si.name else none)

/-- Sorts in a component that actually get `ren`/`subst` (non-empty substitution vector). -/
def substSortsOf (sig : Signature) (comp : List SortId) : List SortInfo :=
  comp.filterMap (fun n => sig.sorts.find? (fun si => si.name == n && !si.substVec.isEmpty))

/-- The shared parameter telescope for this signature. The analyzer currently requires all sorts in
a signature to have compatible telescopes, so the first sort's telescope is canonical. -/
def sigParams (sig : Signature) : List Param :=
  sig.sorts.head?.map (·.params) |>.getD []

/-- Reconstruct the user-facing binder for an inductive parameter. -/
def paramBinder (p : Param) : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  let ty : Term := ⟨p.type⟩
  match p.kind with
  | .explicit =>
      `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent p.name) : $ty))
  | .implicit =>
      `(Lean.Parser.Term.bracketedBinderF| { $(mkIdent p.name) : $ty })
  | .strictImplicit =>
      `(Lean.Parser.Term.bracketedBinderF| ⦃ $(mkIdent p.name) : $ty ⦄)
  | .instImplicit =>
      `(Lean.Parser.Term.bracketedBinderF| [$(mkIdent p.name) : $ty])

/-- Generated operations and lemmas rebind ordinary sort parameters implicitly, even when the
inductive parameter was explicit, so users do not have to write `subst_Tm Ann σ t`. Instance
parameters remain instance implicit so typeclass search continues to apply. -/
def paramImplicitBinder (p : Param) : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  let ty : Term := ⟨p.type⟩
  match p.kind with
  | .instImplicit =>
      `(Lean.Parser.Term.bracketedBinderF| [$(mkIdent p.name) : $ty])
  | _ =>
      `(Lean.Parser.Term.bracketedBinderF| { $(mkIdent p.name) : $ty })

def sigImplicitBinders (sig : Signature) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :=
  sigParams sig |>.toArray.mapM paramImplicitBinder

def sortParamArgs (sig : Signature) (v : SortId) : List Term :=
  ((sig.sorts.find? (·.name == v)).map (·.params) |>.getD []).map fun p => (mkIdent p.name : Term)

/-- Explicitly apply a generated sort/type former to arguments, bypassing implicit-argument
inference. This is essential for sorts with implicit parameters (`@Tm Srt Ann`). -/
def explicitApp (head : Ident) (args : List Term) : CommandElabM Term := do
  if args.isEmpty then
    pure head
  else
    let args := args.toArray
    `(@$head $args*)

/-- A generated sort applied to its declaration parameters plus explicit scope/index arguments. -/
def sortTyWithScopeArgs (sig : Signature) (v : SortId) (scopes : List Term) : CommandElabM Term :=
  explicitApp (mkIdent v) (sortParamArgs sig v ++ scopes)

/-! ## Mode-dependent prelude identifiers -/

def funcompI : Ident := mkIdent ``Autosubst.funcomp
def idI      : Ident := mkIdent ``id
def sconsI    (sc : Bool) : Ident := mkIdent (if sc then ``Autosubst.Scoped.scons else ``Autosubst.scons)
def varZeroI  (sc : Bool) : Ident := mkIdent (if sc then ``Autosubst.Scoped.var_zero else ``Autosubst.var_zero)
def shiftI    (sc : Bool) : Ident := mkIdent (if sc then ``Autosubst.Scoped.shift else ``Autosubst.shift)
def upRenI    (sc : Bool) : Ident := mkIdent (if sc then ``Autosubst.Scoped.up_ren else ``Autosubst.up_ren)
def upRenRenI (sc : Bool) : Ident := mkIdent (if sc then ``Autosubst.Scoped.up_ren_ren else ``Autosubst.up_ren_ren)

/-! ## Scope-index machinery (scoped mode only) -/

/-- Scope variable for component `v` at stage `st` (auto-bound implicit), e.g. `m_tm`. -/
def scopeVar (st : String) (v : SortId) : Ident := mkIdent (Name.mkSimple s!"{st}_{v}")

/-- The sort `v` applied to its substitution-vector scopes at stage `st`. Unscoped (or a sort
with empty vector, e.g. STLC's `ty`) ⟹ the bare sort identifier; otherwise `v st_u1 st_u2 …`. -/
def sortTyAt (sc : Bool) (sig : Signature) (v : SortId) (st : String) : CommandElabM Term := do
  let mut scopes : List Term := []
  if sc then
    for u in vecOf sig v do scopes := scopes ++ [(scopeVar st u : Term)]
  sortTyWithScopeArgs sig v scopes

/-- The type of a map for component `v` from stage `domSt` to `codSt`:
unscoped `Nat → Nat` / `Nat → v`; scoped `Fin domSt_v → Fin codSt_v` / `Fin domSt_v → v <cod>`. -/
def mapTy (sc : Bool) (sig : Signature) (forRen : Bool) (v : SortId) (domSt codSt : String) :
    CommandElabM Term := do
  if !sc then
    if forRen then `(Nat → Nat) else `(Nat → $(← sortTyAt sc sig v codSt))
  else if forRen then
    `(Fin $(scopeVar domSt v) → Fin $(scopeVar codSt v))
  else
    `(Fin $(scopeVar domSt v) → $(← sortTyAt sc sig v codSt))

/-- A bracketed binder `(nm : <mapTy …>)` for a component map. -/
def mapBinder (sc : Bool) (sig : Signature) (forRen : Bool) (v : SortId) (domSt codSt : String)
    (nm : Name) : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent nm) : $(← mapTy sc sig forRen v domSt codSt)))

/-- Increment count for sort `u` introduced by `binders` (number of `single u` binders;
variadic binders contribute a *symbolic* `+ p` instead — see `scopeBumped`). -/
def binderInc (binders : List Binder) (u : SortId) : Nat :=
  binders.foldl (fun acc b => match b with | .single s => if s == u then acc + 1 else acc | _ => acc) 0

/-- `t + 1 + … + 1` (`k` times). -/
def addOnes (t : Term) (k : Nat) : CommandElabM Term := do
  let mut r := t
  for _ in [0:k] do r ← `($r + 1)
  return r

/-- The scope of component `u` at stage `st`, bumped by every binder that introduces `u`-variables:
`+ 1` for each `single u` binder and `+ <p>` for each variadic `vector p u` binder (the runtime
count). For non-variadic positions this is exactly `addOnes (scopeVar st u) (binderInc …)`. -/
def scopeBumped (st : String) (binders : List Binder) (u : SortId) : CommandElabM Term := do
  let mut t : Term := scopeVar st u
  for b in binders do
    match b with
    | .single s => if s == u then t ← `($t + 1)
    | .vector p s => if s == u then t ← `($t + $(mkIdent p))
  return t

/-- Does any constructor use a variadic `bind ⟨p, _⟩` binder? (Gates the variadic code paths so
non-variadic signatures are untouched.) -/
def hasVariadic (sig : Signature) : Bool :=
  sig.sorts.any fun si => si.ctors.any fun c => c.positions.any fun pos =>
    pos.binders.any fun b => match b with | .vector _ _ => true | _ => false

/-- Sorts that occur as the bound sort of some variadic `bind ⟨p, b⟩` binder. The `_list`
up-helpers are generated for `(b, v)` with `b` such a sort and `v` an open component. -/
def variadicBoundSorts (sig : Signature) : List SortId := Id.run do
  let mut acc : List SortId := []
  for si in sig.sorts do
    for c in si.ctors do
      for pos in c.positions do
        for b in pos.binders do
          if let .vector _ s := b then unless acc.contains s do acc := acc ++ [s]
  return acc

end Autosubst.Gen
