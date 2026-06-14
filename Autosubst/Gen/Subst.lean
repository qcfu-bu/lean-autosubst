/-
# Phase 4 — Substitution-operation generation (multi-map).

Generates the `upRen`/`up`/`ren`/`subst` operations from the analyzed `Signature`, with the
**parallel multi-map threading** the SysF golden file pinned down. For a sort `s` with
substitution vector `[v₁ … vₖ]`, `ren_s`/`subst_s` take one map per `vᵢ`; under a binder of
sort `b` each component map is lifted by `upRen_b_vᵢ` / `up_b_vᵢ`:

  • `upRen_b_v xi := if b == v then up_ren xi else xi`            (renamings need no codomain fix)
  • `up_b_v σ    := let r := ren_v [if w==b then shift else id | w ∈ vec v];`
                    `if b == v then var_v 0 .: (r >> σ) else r >> σ`

Emission order respects dependencies: all `upRen` → `ren` (per component, `mutual` for SCCs) →
all `up` → `subst` (per component). Container heads are threaded structurally via a mutual helper
(see the Containers section below); external heads are carried unchanged.
-/
import Lean
import Autosubst.Gen.Backend
import Autosubst.Gen.Inductive
import Autosubst.Gen.Container

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-! ## Names -/

def renName   (s : SortId) : Name := Name.mkSimple s!"ren_{s}"
def substName (s : SortId) : Name := Name.mkSimple s!"subst_{s}"
def opName    (forRen : Bool) (s : SortId) : Name := if forRen then renName s else substName s
def upRenName (b v : SortId) : Name := Name.mkSimple s!"upRen_{b}_{v}"
def upName    (b v : SortId) : Name := Name.mkSimple s!"up_{b}_{v}"
/-- The variadic (`bind ⟨p, b⟩`) lifting-helper names — the literal `list` tag mirrors the
reference (`coqNames.ml`). These take the runtime count `p` as a leading explicit argument. -/
def upRenListName (b v : SortId) : Name := Name.mkSimple s!"upRen_list_{b}_{v}"
def upListName    (b v : SortId) : Name := Name.mkSimple s!"up_list_{b}_{v}"

/-- The lifting-helper name for a binder `b` (single or variadic) at component `v`. -/
def upBinderName (forRen : Bool) (b : IR.Binder) (v : SortId) : Name :=
  match b with
  | .single s   => if forRen then upRenName s v else upName s v
  | .vector _ s => if forRen then upRenListName s v else upListName s v
/-! ## Containers (Phase 9 + §4a route (b), nested substitution).

A constructor position may nest substitution sorts in containers (`List tm`, `tm × tm`,
`List (tm × tm)`, …). Recursive containers (`List`/`Option`, **plus any user inductive recognised
on demand**) get a **mutual structural helper** `<op>_<s>_<shape>` (Lean can't recurse through an
opaque/`List.map`-style functor — see `memory/phase9-container-architecture.md`); the binary `Prod`
is handled **inline** by projections. Helpers compose so nestings work.

The generator threads `containers : Containers` — the polynomial container heads of this signature,
**each paired with its `ContainerShape`** (computed once by `Frontend.Elab`, so no re-analysis per
use site). `Prod` is recognised separately (inline), so it is not in this map. -/

/-- The container heads of a signature, each with its constructor classification. -/
abbrev Containers := List (Name × ContainerShape)

/-- The shape of head `f`, if it is one of this signature's containers. -/
def shapeOf (containers : Containers) (f : Name) : Option ContainerShape :=
  (containers.find? (·.1 == f)).map (·.2)

/-- The shape-suffix word of a recursive container head, or `none` if `f` is not one (`Prod` is
inline, not recursive). User containers contribute their name. -/
def recContainerWord (containers : Containers) : Name → Option String
  | `List => some "list"
  | `Option => some "option"
  | f => if f != `Prod && (shapeOf containers f).isSome then
      -- Full dotted name (`.`→`_`), not just the last component, so two distinct containers sharing
      -- a final name component (`A.Box`/`B.Box`) get distinct helper names instead of colliding.
      some (f.toString.replace "." "_")
    else none

/-- The binary product container — handled inline by projections, no helper. -/
def isProdHead (f : Name) : Bool := f == `Prod

/-- Does a head mention a declared sort anywhere inside it? Such heads need traversal when they sit
under a recognised container. -/
partial def headMentionsSort : IR.ArgHead → Bool
  | .sort _ _ => true
  | .ext _ | .opaque _ => false
  | .functor _ args => args.any headMentionsSort

/-- A readable word for a head in helper names when a multi-parameter container needs its arguments
spelled out to avoid collisions (`PairBox Ty Tm`, `PairBox Tm Nat`, …). -/
partial def headNameWord (containers : Containers) : IR.ArgHead → String
  | .sort s args =>
    let suffixes := args.map (headNameWord containers) |>.filter (· ≠ "ext")
    if suffixes.isEmpty then s.getString! else s!"{s.getString!}_{String.intercalate "_" suffixes}"
  | .ext e => e.getString!
  | .opaque _ => "opaque"
  | .functor f args =>
    if isProdHead f then
      let parts := args.map (headNameWord containers)
      "prod_" ++ String.intercalate "_" parts
    else
      let base := (recContainerWord containers f).getD f.getString!
      let parts := args.map (headNameWord containers)
      if parts.isEmpty then base else s!"{base}_{String.intercalate "_" parts}"

/-- A compact suffix encoding a head's container shape for helper naming, relative to the enclosing
sort `encl`. The element matching `encl` (the common `List tm`/`Tree tm`/`PBox Srt tm` case) stays
implicit so legacy names stay short; an element that is a *different* declared sort is spelled out
(`List ty` in sort `tm`→"list_ty") so two instantiations of one container in the same sort no longer
collide. Containers with multiple active or non-final active parameters spell out positionally
(`PairBox Ty tm`→"PairBox_Ty_tm"). -/
partial def shapeSuffix (containers : Containers) (encl : SortId) : IR.ArgHead → String
  | .sort s _ => if s == encl then "" else s.getString!
  | .ext _ | .opaque _ => "ext"
  | .functor f args =>
    match recContainerWord containers f with
    | some w =>
      let active := Id.run do
        let mut out : List Nat := []
        let mut i := 0
        for a in args do
          if headMentionsSort a then out := out ++ [i]
          i := i + 1
        out
      if active == [args.length - 1] then
        match args.getLast? with
        | some sub => let s := shapeSuffix containers encl sub; if s.isEmpty then w else s!"{w}_{s}"
        | none => w
      else
        let parts := args.map (headNameWord containers)
        if parts.isEmpty then w else s!"{w}_{String.intercalate "_" parts}"
    | none =>
      if isProdHead f then
        let parts := (args.map (shapeSuffix containers encl)).filter (· ≠ "")
        if parts.isEmpty then "prod" else "prod_" ++ String.intercalate "_" parts
      else "ext"

/-- Helper op name for a recursive-container head in sort `s`: `<op>_<s>_<shape>`. -/
def helperOpName (containers : Containers) (forRen : Bool) (s : SortId) (head : IR.ArgHead) : Name :=
  Name.mkSimple s!"{opName forRen s}_{shapeSuffix containers s head}"

/-- Map parameter name for component `v`: `xi_v` (renaming) or `sigma_v` (substitution). -/
def mapParam (forRen : Bool) (v : SortId) : Name := Name.mkSimple s!"{if forRen then "xi" else "sigma"}_{v}"

/-! ## up / upRen

(`funcompI`/`sconsI`/`varZeroI`/`shiftI`/`upRenI`/`idI` and the signature lookups
`vecOf`/`openSorts`/`substSortsOf` live in `Gen/Backend`, parameterized over the backend.) -/

def genUpRen (sc : Bool) (_sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let body ← if b == v then `($(upRenI sc) xi) else `(xi)
  if !sc then
    `(command| @[reducible] def $(mkIdent (upRenName b v)) (xi : Nat → Nat) : Nat → Nat := $body)
  else
    let inc := if b == v then 1 else 0
    let m := scopeVar "m" v; let n := scopeVar "n" v
    let domD ← addOnes m inc; let codD ← addOnes n inc
    `(command| @[reducible] def $(mkIdent (upRenName b v)) (xi : Fin $m → Fin $n) :
        Fin $domD → Fin $codD := $body)

def genUp (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  -- ren_v applied to: shift on the b-component, id elsewhere
  let mut renApp : Term := mkIdent (renName v)
  for w in vecOf sig v do
    renApp ← `($renApp $(if w == b then shiftI sc else idI))
  let composed ← `($funcompI $renApp sigma)
  let body ← if b == v then `($(sconsI sc) ($(mkIdent (v ++ varName v)) $(varZeroI sc)) $composed)
             else pure composed
  let pbs ← sigImplicitBinders sig
  if !sc then
    `(command| @[reducible] def $(mkIdent (upName b v)) $pbs* (sigma : Nat → $(← sortTyAt sc sig v "n")) :
        Nat → $(← sortTyAt sc sig v "n") := $body)
  else
    let m := scopeVar "m" v
    let domD ← addOnes m (if b == v then 1 else 0)
    let scopeArgs ← (vecOf sig v).mapM fun u =>
      addOnes (scopeVar "n" u) (if u == b then 1 else 0)
    let cod ← sortTyWithScopeArgs sig v scopeArgs
    let sigmaTy ← `(Fin $m → $(← sortTyAt sc sig v "n"))
    `(command| @[reducible] def $(mkIdent (upName b v)) $pbs* (sigma : $sigmaTy) :
        Fin $domD → $cod := $body)

/-! ## Variadic up-helpers (`bind ⟨p, b⟩`, scoped-only).

`upRen_list_b_v` / `up_list_b_v` are the runtime-`p` generalizations of `upRen_b_v` / `up_b_v`:
the body scope grows by `p` (via `Fin (… + p)`), the freshly bound `p` variables are spliced in by
`scons_p`/`zero_p`, and the original variables shift by `shift_p p`. Ground truth: `variadic.v`
(`up_list_tm_tm = scons_p p (var ∘ zero_p p) (ren_tm (shift_p p) ∘ σ)`). -/

def shiftPI : Ident := mkIdent ``Autosubst.Scoped.shift_p
def sconsPI : Ident := mkIdent ``Autosubst.Scoped.scons_p
def zeroPI  : Ident := mkIdent ``Autosubst.Scoped.zero_p
def upRenPI : Ident := mkIdent ``Autosubst.Scoped.upRen_p

/-- `upRen_list_b_v p xi` — lift a renaming under a variadic binder `⟨p, b⟩`. When `b == v` the
`v`-scope grows by `p` (`upRen_p p xi`); otherwise the binder adds no `v`-variables (`= xi`). -/
def genUpRenList (_sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let m := scopeVar "m" v; let n := scopeVar "n" v
  if b == v then
    `(command| @[reducible] def $(mkIdent (upRenListName b v)) (p : Nat) (xi : Fin $m → Fin $n) :
        Fin ($m + p) → Fin ($n + p) := $upRenPI p xi)
  else
    `(command| @[reducible] def $(mkIdent (upRenListName b v)) (p : Nat) (xi : Fin $m → Fin $n) :
        Fin $m → Fin $n := xi)

/-- `up_list_b_v p σ` — lift a substitution under a variadic binder `⟨p, b⟩`. -/
def genUpList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  -- ren_v applied to: `shift_p p` on the b-component, `id` elsewhere
  let mut renApp : Term := mkIdent (renName v)
  for w in vecOf sig v do
    renApp ← `($renApp $(← if w == b then `($shiftPI p) else pure idI))
  let composed ← `($funcompI $renApp sigma)
  let varV := mkIdent (v ++ varName v)
  let body ← if b == v then `($sconsPI p ($funcompI $varV ($zeroPI p)) $composed) else pure composed
  let m := scopeVar "m" v
  let domD ← if b == v then `($m + p) else pure (m : Term)
  let scopeArgs ← (vecOf sig v).mapM fun u =>
    if u == b then `($(scopeVar "n" u) + p) else pure (scopeVar "n" u : Term)
  let cod ← sortTyWithScopeArgs sig v scopeArgs
  let sigmaTy ← `(Fin $m → $(← sortTyAt true sig v "n"))
  let pbs ← sigImplicitBinders sig
  `(command| @[reducible] def $(mkIdent (upListName b v)) $pbs* (p : Nat) (sigma : $sigmaTy) :
      Fin $domD → $cod := $body)

/-! ## ren / subst -/

/-- The substitution map for component `v`, lifted under `binders`: `σ_v` ↦ `up_b_v … σ_v` for a
single binder, or `up_list_b_v p … σ_v` (threading the runtime count `p`) for a variadic one. -/
def mapUnder (forRen : Bool) (binders : List IR.Binder) (v : SortId) : CommandElabM Term := do
  let mut m : Term := mkIdent (mapParam forRen v)
  for b in binders do
    let nm := mkIdent (upBinderName forRen b v)
    m ← match b with
      | .single _    => `($nm $m)
      | .vector p _  => `($nm $(mkIdent p) $m)
  pure m

/-- The substituted/renamed value of `x : type(head)`, recursing through container heads:
`sort w` → `op_w maps x`; `Prod` → inline `(…x.1, …x.2)`; recursive containers (`List`/`Option`)
→ a call to their mutual structural helper `<op>_<s>_<shape>` (threading `s`'s full map vector,
lifted under `binders`). `s`/`vecS` are the enclosing sort and its substitution vector. -/
partial def genHeadValue (containers : Containers) (sig : Signature) (forRen : Bool) (s : SortId)
    (vecS : List SortId) (binders : List IR.Binder) (head : IR.ArgHead) (x : Term) :
    CommandElabM Term := do
  match head with
  | .sort w _ =>
    let vecW := vecOf sig w
    if vecW.isEmpty then return x
    let mut call : Term := mkIdent (opName forRen w)
    for v in vecW do call ← `($call $(← mapUnder forRen binders v))
    `($call $x)
  | .functor f args =>
    if isProdHead f then
      match args with
      | [a, b] =>
        let va ← genHeadValue containers sig forRen s vecS binders a (← `($x.1))
        let vb ← genHeadValue containers sig forRen s vecS binders b (← `($x.2))
        `(($va, $vb))
      | _ => return x
    -- A recognised container with a declared sort inside gets a mutual structural helper; one with
    -- no sort inside (`List Nat`, `MyBox Nat`) carries substitution nowhere — leave it unchanged
    -- (mirroring `collectHelperHeads`, which only emits a helper when `args.any headMentionsSort`).
    else if (recContainerWord containers f).isSome && headMentionsSort head then do
        let mut call : Term := mkIdent (helperOpName containers forRen s head)
        for v in vecS do call ← `($call $(← mapUnder forRen binders v))
        `($call $x)
    else return x
  | .ext _ | .opaque _ => return x

/-- Build the field expression for one constructor position of sort `s`. -/
def genField (containers : Containers) (sig : Signature) (forRen : Bool) (s : SortId)
    (pos : IR.Position) (x : Ident) : CommandElabM Term :=
  genHeadValue containers sig forRen s (vecOf sig s) pos.binders pos.head x

/-- Build the match arms for `ren_s` / `subst_s`. -/
def genArms (containers : Containers) (sig : Signature) (forRen : Bool) (si : SortInfo) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.matchAlt)) := do
  let s := si.name
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  -- variable constructor
  if si.isOpen then
    let x := mkIdent `x
    let pat ← `($(mkIdent (s ++ varName s)) $x)
    let rhs ← if forRen then `($(mkIdent (s ++ varName s)) ($(mkIdent (mapParam true s)) $x))
                        else `($(mkIdent (mapParam false s)) $x)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs))
  -- user constructors (variadic params `p` are bound in the pattern and re-applied unchanged)
  for c in si.ctors do
    let xs := (Array.range c.positions.length).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let ps := (c.params.map (fun (pn, _) => mkIdent pn)).toArray
    let ctorId := mkIdent (s ++ c.name)
    let pat ← `($ctorId $ps* $xs*)
    let fields ← (c.positions.toArray.zip xs).mapM fun (pos, x) => genField containers sig forRen s pos x
    let rhs ← `($ctorId $ps* $fields*)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs))
  return alts

/-- Map-parameter binders (`vec` of them) for a helper/op of `forRen` kind, stage `m → n`. -/
def mapParamBinders (sc : Bool) (sig : Signature) (forRen : Bool) (vec : List SortId) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :=
  vec.toArray.mapM fun v => mapBinder sc sig forRen v "m" "n" (mapParam forRen v)

/-- All sub-heads (incl. self) whose outermost is a recursive container (`List`/`Option`/user
container) — the heads that need a mutual structural helper. Nested containers contribute their
inner ones too. -/
partial def collectHelperHeads (containers : Containers) : IR.ArgHead → List IR.ArgHead
  | .sort _ args => args.flatMap (collectHelperHeads containers)
  | .ext _ | .opaque _ => []
  | .functor f args =>
    let subs := args.flatMap (collectHelperHeads containers)
    if (recContainerWord containers f).isSome && args.any headMentionsSort
    then (.functor f args) :: subs else subs

/-- The `(sort, head)` pairs needing a helper in this component (deduped). -/
def helperHeadsOf (containers : Containers) (sig : Signature) (comp : List SortId) :
    List (SortId × IR.ArgHead) := Id.run do
  let mut acc : List (SortId × IR.ArgHead) := []
  for si in comp.filterMap (fun n => sig.sorts.find? (·.name == n)) do
    for c in si.ctors do
      for pos in c.positions do
        for h in collectHelperHeads containers pos.head do
          let pair := (si.name, h)
          unless acc.contains pair do acc := acc ++ [pair]
  return acc

/-- The transformed value of one helper-element argument of `ArgKind` `k`: an element parameter
slot is substituted via `genHeadValue` on the matching applied argument head; a recursive occurrence
recurses through the helper (`tailCall`); an inert argument is carried unchanged. -/
def genHelperArg (containers : Containers) (sig : Signature) (forRen : Bool) (s : SortId)
    (vecS : List SortId) (args : List IR.ArgHead) (tailCall : Term) (k : ArgKind) (x : Ident) :
    CommandElabM Term := do
  match k with
  | .elem i  =>
      match args[i]? with
      | some sub => genHeadValue containers sig forRen s vecS [] sub x
      | none => pure x
  | .recurse => `($tailCall $x)
  | .inert   => pure x

/-- The mutual structural helper for a container head in sort `s` (threads `s`'s map vector; element
transforms via `genHeadValue`, so nestings compose). The container — `List`, `Option`, or any
recognised user inductive — is destructured per its constructors via the derived `ContainerShape`.
The binary `Prod` is handled inline by `genHeadValue` (no helper). -/
def genHelperDef (containers : Containers) (sc : Bool) (sig : Signature) (forRen : Bool) (s : SortId)
    (head : IR.ArgHead) : CommandElabM (TSyntax `command) := do
  let vecS := vecOf sig s
  let pbs ← sigImplicitBinders sig
  let params ← mapParamBinders sc sig forRen vecS
  let nmI := mkIdent (helperOpName containers forRen s head)
  let ty ← headToTerm sc sig [] head
  let mapArgs : Array Term := (vecS.map fun v => (mkIdent (mapParam forRen v) : Term)).toArray
  let mut tailCall : Term := nmI
  for m in mapArgs do tailCall ← `($tailCall $m)
  match head with
  | .functor f args =>
    match shapeOf containers f with
    | none => `(command| def $nmI $pbs* $params* : $ty → $ty := id)
    | some shape =>
      let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for (cName, kinds) in shape do
        let xs := (Array.range kinds.size).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
        let rhs ← (xs.zip kinds).mapM fun (x, k) => genHelperArg containers sig forRen s vecS args tailCall k x
        arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(mkIdent cName) $xs* => $(mkIdent cName) $rhs*))
      `(command| def $nmI $pbs* $params* : $ty → $ty $arms:matchAlt*)
  | _ => `(command| def $nmI $pbs* $params* : $ty → $ty := id)

/-- The `ren_s` or `subst_s` definition (without the surrounding `mutual`). Scoped: maps thread
`Fin m_v → Fin n_v` / `Fin m_v → v …` and the result is `s <m> → s <n>` (scope vars auto-bound). -/
def genOp (containers : Containers) (sc : Bool) (sig : Signature) (forRen : Bool) (si : SortInfo) :
    CommandElabM (TSyntax `command) := do
  let s := si.name
  let pbs ← sigImplicitBinders sig
  let params ← si.substVec.toArray.mapM fun v => mapBinder sc sig forRen v "m" "n" (mapParam forRen v)
  let alts ← genArms containers sig forRen si
  let dom ← sortTyAt sc sig s "m"; let cod ← sortTyAt sc sig s "n"
  `(command| def $(mkIdent ((if forRen then renName else substName) s)) $pbs* $params* :
      $dom → $cod $alts:matchAlt*)

/-- Generate `ren`/`subst` for a component: a `mutual` block iff >1 sort gets the operation. -/
def genOpComponent (containers : Containers) (sc : Bool) (sig : Signature) (forRen : Bool)
    (comp : List SortId) : CommandElabM (Option (TSyntax `command)) := do
  let sis := substSortsOf sig comp
  if sis.isEmpty then return none
  let mainDefs ← sis.toArray.mapM (genOp containers sc sig forRen)
  -- Phase 9: mutual structural helpers for every recursive-container position in the component.
  let helperDefs ← (helperHeadsOf containers sig comp).toArray.mapM
    (fun (s, h) => genHelperDef containers sc sig forRen s h)
  let defs := mainDefs ++ helperDefs
  if h : defs.size = 1 then return some defs[0]
  else return some (← `(command| mutual $defs* end))

/-! ## Orchestration -/

/-- All substitution-operation commands, in dependency order. The variadic `upRen_list`/`up_list`
helpers (scoped-only) are emitted alongside their single-binder counterparts. `containers` is the
set of recognised container heads (inferred on demand by the caller). -/
def genSubstCommands (containers : Containers) (sc : Bool) (sig : Signature) :
    CommandElabM (Array (TSyntax `command)) := do
  let opens := openSorts sig
  let vbs := variadicBoundSorts sig
  let mut cmds : Array (TSyntax `command) := #[]
  -- 1. upRen (all pairs) + variadic upRen_list
  for b in opens do for v in opens do cmds := cmds.push (← genUpRen sc sig b v)
  for b in vbs do for v in opens do cmds := cmds.push (← genUpRenList sig b v)
  -- 2. ren (per component)
  for comp in sig.components do
    if let some c ← genOpComponent containers sc sig true comp then cmds := cmds.push c
  -- 3. up (all pairs) + variadic up_list
  for b in opens do for v in opens do cmds := cmds.push (← genUp sc sig b v)
  for b in vbs do for v in opens do cmds := cmds.push (← genUpList sig b v)
  -- 4. subst (per component)
  for comp in sig.components do
    if let some c ← genOpComponent containers sc sig false comp then cmds := cmds.push c
  return cmds

end Autosubst.Gen
