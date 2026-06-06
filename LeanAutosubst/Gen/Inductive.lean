/-
# Phase 3/8 — Inductive (and congruence) generation.

Consumes an analyzed `Signature` and produces de Bruijn `inductive` command syntax (one per
component — a `mutual … end` block for a genuine SCC, a lone `inductive` for a singleton),
each open sort getting its variable constructor and every user constructor lowered by **erasing
binders**. Also emits the `congr_<ctor>` congruence lemmas.

Two backends (plan.md §4), selected by `sc : Bool`:
  • **unscoped** — `var_<s> : Nat → s`, fields are the bare head types;
  • **well-scoped** — a substitution sort `s` is indexed by one `Nat` per substitution-vector
    entry (`tm : Nat → Nat → Type`), `var_<s> : Fin n_s → s …`, and a binder `bind u in h`
    increments the `u`-scope of `h`. Scope variables are free identifiers auto-bound by Lean
    (`autoImplicit`), so only the constructor *types* change.

We emit *command syntax* and let Lean's own inductive elaborator do the work (`elabCommand`):
de Bruijn syntax is strictly positive, so this is exactly the clean path.
-/
import Lean
import LeanAutosubst.Gen.Backend

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-- The `congr_<ctor>` lemma name. -/
def congrName (c : Name) : Name := Name.mkSimple s!"congr_{c}"

/-- An argument head ⟶ its de Bruijn field type. Binders are passed for scope increments
(scoped mode); they are erased in unscoped mode. `sc` selects the backend. -/
partial def headToTerm (sc : Bool) (sig : Signature) (binders : List Binder) (h : ArgHead) :
    CommandElabM Term := do
  match h with
  | .sort w args =>
    if !args.isEmpty then
      let argTerms ← args.mapM (headToTerm sc sig [])
      explicitApp (mkIdent w) argTerms
    else if !sc then
      sortTyAt sc sig w "n"
    else
      let vec := vecOf sig w
      if vec.isEmpty then sortTyAt sc sig w "n"
      else
        let mut t ← sortTyAt false sig w "n"
        for u in vec do
          t ← `($t $(← scopeBumped "n" binders u))
        pure t
  | .ext e  => pure (mkIdent e)
  | .opaque stx => pure ⟨stx⟩
  | .functor f args => do
      -- containers carry their elements unchanged structurally; element binders propagate.
      let mut t : Term := mkIdent f
      for a in args do
        t ← `($t $(← headToTerm sc sig binders a))
      pure t

/-- The Lean type of a constructor parameter (`(p : nat)` ⟶ `Nat`); other declared types pass
through. Variadic-binder counts are the only parameters in practice, so this is always `Nat`. -/
def paramTypeTerm (t : SortId) : Term := if t == `nat then mkIdent ``Nat else mkIdent t

/-- A constructor's full type `(p : Nat) → … → T0 → T1 → … → Sort`. Variadic parameters (e.g.
`lam (p : nat)`) become leading explicit `Nat` arguments; the result sort is applied to its scope
variables, with each field scope-bumped per its binders (`+1` single / `+p` variadic). -/
def ctorType (sc : Bool) (sig : Signature) (sort : SortId) (c : IR.Constructor) :
    CommandElabM Term := do
  let fields ← c.positions.toArray.mapM (fun p => headToTerm sc sig p.binders p.head)
  let result ← sortTyAt sc sig sort "n"
  let body ← fields.foldrM (fun f acc => `($f → $acc)) result
  c.params.foldrM (fun (pn, pty) acc => `(($(mkIdent pn) : $(paramTypeTerm pty)) → $acc)) body

/-- The (name, type) pairs of all constructors of a sort: `var_<s>` (if open) then user ctors. -/
def sortCtors (sc : Bool) (sig : Signature) (si : SortInfo) : CommandElabM (Array (Ident × Term)) := do
  let mut out : Array (Ident × Term) := #[]
  if si.isOpen then
    let result ← sortTyAt sc sig si.name "n"
    let varTy ← if sc then `(Fin $(scopeVar "n" si.name) → $result) else `(Nat → $result)
    out := out.push (mkIdent (varName si.name), varTy)
  for c in si.ctors do
    out := out.push (mkIdent c.name, ← ctorType sc sig si.name c)
  return out

/-- Does an argument head mention a container/functor (nested inductive)? -/
partial def headHasFunctor : ArgHead → Bool
  | .functor _ _ => true
  | _ => false

/-- A sort whose constructors nest a container is a nested inductive; Lean's `DecidableEq`
deriving handler does not apply to it (only `Repr` is attempted). -/
def siHasContainer (si : SortInfo) : Bool :=
  si.ctors.any (fun c => c.positions.any (fun p => headHasFunctor p.head))

/-- Is this sort scope-indexed (scoped mode + non-empty substitution vector)? Such sorts get a
`Nat → … → Type` header and no `deriving` (deriving handlers don't cover indexed families). -/
def isIndexed (sc : Bool) (sig : Signature) (si : SortInfo) : Bool :=
  sc && !(vecOf sig si.name).isEmpty

/-- The `Nat → … → Type` header type for a scope-indexed sort (one `Nat` per vector entry). -/
def indexedHeader (sig : Signature) (si : SortInfo) : CommandElabM Term := do
  let mut hdr : Term ← `(Type _)
  for _ in vecOf sig si.name do hdr ← `(Nat → $hdr)
  return hdr

/-- A single `inductive <sort> where …` command. The convenience `Repr`/`DecidableEq` instances are
**not** attached here — they are derived separately, best-effort (`genDerivingCommands`), so a
foreign field type that lacks those instances (any external Lean type, lowercase or not) does not
break generation. -/
def genInductive (sc : Bool) (sig : Signature) (si : SortInfo) : CommandElabM (TSyntax `command) := do
  let ctors ← sortCtors sc sig si
  let cnames := ctors.map (·.1)
  let ctys := ctors.map (·.2)
  if isIndexed sc sig si then
    let hdr ← indexedHeader sig si
    let pbs ← si.params.toArray.mapM paramBinder
    `(command| inductive $(mkIdent si.name) $pbs* : $hdr where
        $[| $cnames:ident : $ctys:term]*)
  else
    let pbs ← si.params.toArray.mapM paramBinder
    `(command| inductive $(mkIdent si.name) $pbs* where
        $[| $cnames:ident : $ctys:term]*)

/-- The inductive command for a whole component (a `mutual` block iff the SCC is non-trivial). -/
def genComponent (sc : Bool) (sig : Signature) (comp : List SortId) : CommandElabM (TSyntax `command) := do
  let sis := comp.filterMap (fun n => sig.sorts.find? (·.name == n)) |>.toArray
  let inds ← sis.mapM (genInductive sc sig)
  if h : inds.size = 1 then
    pure inds[0]
  else
    `(command| mutual $inds* end)

/-- Does this head (recursively) carry substitutable content — a `.sort w` whose `ren`/`subst`
actually does something (non-empty vector)? External heads and sorts with empty vectors don't. -/
partial def headSubstitutable (sig : Signature) : ArgHead → Bool
  | .sort w args => !(vecOf sig w).isEmpty || args.any (headSubstitutable sig)
  | .ext _ | .opaque _ => false
  | .functor _ args => args.any (headSubstitutable sig)

/-- A *leaf* constructor carries no substitutable content: nullary, or all-`ext` like
`const : Nat → tm`. `ren`/`subst` leave it unchanged, so every tower case for it is `rfl`. -/
def ctorIsLeaf (sig : Signature) (c : IR.Constructor) : Bool :=
  c.positions.all (fun p => !headSubstitutable sig p.head)

/-- The `congr_<ctor>` lemma for a non-leaf constructor (none for a leaf — nullary or all-`ext`).
The hypothesis variables `a_i`/`b_i` are auto-bound implicits, their (scope-indexed) types inferred
from the constructor application. A leaf constructor needs no congruence lemma: the tower closes its
cases by `rfl`, and an all-`ext` constructor's `congr` would carry an un-inferable result scope in
scoped mode (its fields pin no scope). -/
def genCongr (sc : Bool) (sig : Signature) (sort : SortId) (c : IR.Constructor) :
    CommandElabM (Option (TSyntax `command)) := do
  if ctorIsLeaf sig c then return none
  let n := c.positions.length
  let idents (pfx : String) : Array Ident :=
    (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"{pfx}{i}"))
  let as := idents "a"; let bs := idents "b"; let hs := idents "h"
  let ctor := mkIdent (sort ++ c.name)
  let ps := (c.params.map (fun (pn, _) => mkIdent pn)).toArray
  let lhs ← `($ctor $ps* $as*)
  let rhs ← `($ctor $ps* $bs*)
  if c.params.isEmpty then
    -- common path: field types inferred from the ctor application (autoImplicit).
    return some (← `(command|
      theorem $(mkIdent (congrName c.name)) $[($hs : $as = $bs)]* : $lhs = $rhs := by
        subst_vars; rfl))
  else
    -- Variadic ctor (`lam (p : nat) …`): the field types mention `p` (`tm (n + p)`), which
    -- autoImplicit binds *after* the fields and so cannot infer. Bind `{p : Nat}` first and give
    -- each field an explicit scope-typed binder so the `+ p` is in scope.
    let pbs ← c.params.toArray.mapM fun (pn, pty) =>
      `(Lean.Parser.Term.bracketedBinderF| { $(mkIdent pn) : $(paramTypeTerm pty) })
    let tys ← c.positions.toArray.mapM (fun pos => headToTerm sc sig pos.binders pos.head)
    let fbs ← (as.zip (bs.zip tys)).mapM fun (a, b, ty) =>
      `(Lean.Parser.Term.bracketedBinderF| { $a $b : $ty })
    return some (← `(command|
      theorem $(mkIdent (congrName c.name)) $pbs* $fbs* $[($hs : $as = $bs)]* : $lhs = $rhs := by
        subst_vars; rfl))

/-- All command syntax to generate the (de Bruijn) inductives + congruence lemmas, in order. -/
def genCommands (sc : Bool) (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let mut cmds : Array (TSyntax `command) := #[]
  for comp in sig.components do
    cmds := cmds.push (← genComponent sc sig comp)
    for n in comp do
      if let some si := sig.sorts.find? (·.name == n) then
        for c in si.ctors do
          if let some cg ← genCongr sc sig si.name c then
            cmds := cmds.push cg
  return cmds

/-- Best-effort `Repr`/`DecidableEq` deriving commands, one (pair) per component, to be elaborated
**after** the inductives and with failures suppressed (see `Frontend.Elab.bestEffortElab`): a foreign
field type (any external Lean type — lowercase or not) that lacks the instance is then simply skipped
rather than aborting the whole `autosubst`. Indexed (scoped) sorts get none; container sorts get
`Repr` only (nested-inductive `DecidableEq` is not derivable). Mutual SCCs are derived together. -/
def genDerivingCommands (sc : Bool) (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let mut cmds : Array (TSyntax `command) := #[]
  for comp in sig.components do
    let sis := comp.filterMap (fun n => sig.sorts.find? (·.name == n))
    let reprSorts := (sis.filter (fun si => !isIndexed sc sig si)).map (mkIdent ·.name) |>.toArray
    let deqSorts := (sis.filter (fun si => !isIndexed sc sig si && !siHasContainer si)).map
      (mkIdent ·.name) |>.toArray
    unless reprSorts.isEmpty do
      cmds := cmds.push (← `(command| deriving instance Repr for $reprSorts,*))
    unless deqSorts.isEmpty do
      cmds := cmds.push (← `(command| deriving instance DecidableEq for $deqSorts,*))
  return cmds

end Autosubst.Gen
