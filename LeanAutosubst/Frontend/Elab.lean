/-
# Phase 2 — Lowering the HOAS block to the IR + running the analyzer.

The `autosubst` command elaborator. It walks the captured `Syntax` (never elaborating the
`bind`-annotated constructor types as real Lean terms — see plan.md §4), lowers it to an
`IR.Spec`, runs `IR.Signature.analyze`, and reports the analyzed signature. Later phases extend
this elaborator to also emit the de Bruijn inductives, substitution operations, lemma tower,
and tactics.
-/
import LeanAutosubst.Frontend.Syntax
import LeanAutosubst.IR.Signature
import LeanAutosubst.Gen.Inductive
import LeanAutosubst.Gen.Subst
import LeanAutosubst.Gen.Lemmas
import LeanAutosubst.Gen.Automation
import LeanAutosubst.Gen.Notation
import LeanAutosubst.Tactic.Asimp

open Lean Elab Command

namespace Autosubst.Frontend
open Autosubst.IR

partial def eraseIdentMacroScopes (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
    | Syntax.ident info rawVal val _ => Syntax.ident info rawVal val.eraseMacroScopes []
    | stx => stx

partial def syntaxIdents (stx : Syntax) : List Name :=
  if stx.isIdent then
    [stx.getId.eraseMacroScopes]
  else
    stx.getArgs.toList.flatMap syntaxIdents

/-- A head (`asHead`) or functor argument (`asHeadArg`) ⟶ `ArgHead`. An ident is a declared sort
(`.sort`) if known, else an external type (`.ext`); `F a b …` is a functor application; a
parenthesized head is unwrapped. -/
partial def parseHead (declared : List Name) (s : Syntax) : ArgHead :=
  let k := s.getKind
  if k == ``headApp then
    -- `ident asHeadArg+`: child 0 is the functor name, child 1 the argument group.
    let id := s[0].getId
    let args := s[1].getArgs.toList.map (parseHead declared)
    if declared.contains id then .sort id args else .functor id args
  else if k == ``headParen || k == ``headArgParen then
    parseHead declared s[1]   -- `( asHead )` — unwrap
  else if k == ``headOpaque || k == ``headArgOpaque then
    .opaque s[1]
  else -- headAtom / headArgAtom: a lone ident
    let id := s[0].getId
    if declared.contains id then .sort id [] else .ext id

/-- Deterministic local names for anonymous instance parameters (`[C α]`). They must be nameable
because generated code applies parameterized sorts explicitly via `@Sort ...`. -/
def anonInstName (idx : Nat) : Name := Name.mkSimple s!"autosubstInstParam{idx}"

def enumerateFrom {α : Type} (idx : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (idx, x) :: enumerateFrom (idx + 1) xs

def enumerate {α : Type} : List α → List (Nat × α) :=
  enumerateFrom 0

/-- A sort parameter declaration ⟶ `Param`. -/
def parseParam (idx : Nat) (s : Syntax) : Param :=
  let k := s.getKind
  if k == ``sortParamImplicit then
    { name := s[1].getId.eraseMacroScopes, type := s[3], kind := .implicit }
  else if k == ``sortParamStrictImplicit then
    { name := s[1].getId.eraseMacroScopes, type := s[3], kind := .strictImplicit }
  else if k == ``sortParamInstNamed then
    { name := s[1].getId.eraseMacroScopes, type := s[3], kind := .instImplicit }
  else if k == ``sortParamInstAnon then
    { name := anonInstName idx, type := s[1], kind := .instImplicit }
  else
    { name := s[1].getId.eraseMacroScopes, type := s[3], kind := .explicit }

open Lean.Parser.Term in
/-- Active section variables that can be promoted to sort parameters. -/
def parseSectionVarParamDecl (idx : Nat) (s : Syntax) : CommandElabM (List Param) := do
  let mkParams (ids : Array (TSyntax [`ident, `Lean.Parser.Term.hole])) (ty : Syntax)
      (kind : ParamKind) : List Param :=
    ids.toList.filterMap fun id =>
      if id.raw.isIdent then
        some { name := id.raw.getId.eraseMacroScopes, type := ty, kind := kind }
      else
        none
  match s with
  | `(bracketedBinderF|($ids* : $ty)) =>
      let ty := eraseIdentMacroScopes ty
      return mkParams ids ty .explicit
  | `(bracketedBinderF|{$ids* : $ty}) =>
      let ty := eraseIdentMacroScopes ty
      return mkParams ids ty .implicit
  | `(bracketedBinderF|⦃$ids* : $ty⦄) =>
      let ty := eraseIdentMacroScopes ty
      return mkParams ids ty .strictImplicit
  | `(bracketedBinderF|[$id : $ty]) =>
      let ty := eraseIdentMacroScopes ty
      return [{ name := id.getId.eraseMacroScopes, type := ty, kind := .instImplicit }]
  | `(bracketedBinderF|[$ty]) =>
      let ty := eraseIdentMacroScopes ty
      return [{ name := anonInstName idx, type := ty, kind := .instImplicit }]
  | _ => return []

/-- A binder annotation element ⟶ `Binder`. -/
def parseBinder (s : Syntax) : Binder :=
  if s.getKind == ``binderVector then .vector s[1].getId s[3].getId
  else .single s[0].getId

/-- Extract the binders from a `asBinder,+` separated list (skipping the `,` separators). -/
def parseBinders (s : Syntax) : List Binder :=
  s.getArgs.toList.filterMap fun b =>
    if b.getKind == ``binderSingle || b.getKind == ``binderVector then some (parseBinder b) else none

/-- A constructor argument ⟶ `Position` (binders + head). The `bind …` annotation comes either bare
(`argBind`) or parenthesized (`argBindParen`), which shifts the child indices by one (the leading
`(`). -/
partial def parseArg (declared : List Name) (s : Syntax) : IR.Position :=
  let k := s.getKind
  if k == ``argBind then
    { binders := parseBinders s[1], head := parseHead declared s[3] }
  else if k == ``argBindParen then
    { binders := parseBinders s[2], head := parseHead declared s[4] }
  else -- argHead
    { binders := [], head := parseHead declared s[0] }

/-- A constructor declaration ⟶ `Constructor`. Children: `1`=name, `2`=`(p : nat)` params,
`4`=first arg, `5`=the `→`-chain. The chain's last element is the result sort (dropped); the rest
are argument positions. -/
def parseCtor (declared : List Name) (s : Syntax) : IR.Constructor :=
  let params := s[2].getArgs.toList.map (fun p => (p[1].getId, p[3].getId))
  let rest := s[5].getArgs.toList.map (·[1])   -- each `group` is `(" → " asArg)`; the arg is child 1
  let positions := (s[4] :: rest).dropLast.map (parseArg declared)
  { name := s[1].getId, params := params, positions := positions }

/-- A sort declaration ⟶ `SortDecl`. -/
def parseSortDecl (declared : List Name) (s : Syntax) : SortDecl :=
  { name := s[0].getId
  , params := enumerate s[1].getArgs.toList |>.map (fun (idx, p) => parseParam idx p)
  , ctors := s[3].getArgs.toList.map (parseCtor declared) }

/-- The whole `autosubst` block ⟶ `Spec` (sorts in declaration order). The sort declarations are
at child `2` (child `1` is the optional `wellscoped` modifier). -/
def parseSpec (stx : Syntax) : Spec :=
  let sortDecls := stx[2].getArgs.toList
  let declared := sortDecls.map (·[0].getId)
  { sorts := sortDecls.map (parseSortDecl declared) }

partial def headIdents : ArgHead → List Name
  | .sort _ args => args.flatMap headIdents
  | .functor f args => f.eraseMacroScopes :: args.flatMap headIdents
  | .ext e => [e.eraseMacroScopes]
  | .opaque stx => syntaxIdents stx

def specMentionedIdents (sp : Spec) : List Name :=
  Id.run do
    let mut out : List Name := []
    for sd in sp.sorts do
      for p in sd.params do
        out := out ++ syntaxIdents p.type
      for c in sd.ctors do
        for (_, ty) in c.params do
          out := out ++ [ty.eraseMacroScopes]
        for pos in c.positions do
          out := out ++ headIdents pos.head
    out.eraseDups

def closeSectionParamNames (available : List Param) (initial : List Name) : List Name := Id.run do
  let availableNames := available.map (·.name.eraseMacroScopes)
  let mut selected := initial.map (·.eraseMacroScopes) |>.filter availableNames.contains |>.eraseDups
  let mut changed := true
  while changed do
    changed := false
    for p in available do
      let deps := syntaxIdents p.type |>.map (·.eraseMacroScopes)
      if selected.contains p.name then
        for n in deps do
          if availableNames.contains n && !selected.contains n then
            selected := selected ++ [n]
            changed := true
      else if p.kind == .instImplicit && deps.any selected.contains then
        selected := selected ++ [p.name]
        changed := true
  selected

def addSectionParams (sp : Spec) : CommandElabM Spec := do
  let scope ← getScope
  let available ← enumerate scope.varDecls.toList |>.flatMapM fun (idx, stx) =>
    parseSectionVarParamDecl idx stx.raw
  if available.isEmpty then
    return sp
  let selected := closeSectionParamNames available (specMentionedIdents sp)
  let autoParams := available.filter (fun p => selected.contains p.name)
  if autoParams.isEmpty then
    return sp
  let addToSort (sd : SortDecl) : SortDecl :=
    let existing := sd.params.map (fun p => p.name.eraseMacroScopes)
    let extra := autoParams.filter (fun p => !existing.contains p.name)
    { sd with params := extra ++ sd.params }
  return { sorts := sp.sorts.map addToSort }

/-- Render an analyzed signature compactly (one line per sort + the components). -/
def Signature.summary (sig : Signature) : MessageData :=
  let line (si : SortInfo) : MessageData :=
    m!"  {si.name}: isOpen={si.isOpen} substVec={si.substVec} args={si.args} \
       ctors={si.ctors.map (·.name)}"
  let body := sig.sorts.foldl (fun acc si => acc ++ line si ++ "\n") (m!"")
  body ++ m!"  components={sig.components}"

/-- Elaborate `cmd`, but if it produces new error messages, roll back the environment and discard
them. Used for the optional `Repr`/`DecidableEq` instances: deriving may fail for a foreign field
type that lacks the instance, and that should skip the instance — not abort the `autosubst` command. -/
def bestEffortElab (cmd : TSyntax `command) : CommandElabM Unit := do
  let s ← get
  let nOld := s.messages.toList.length
  try elabCommand cmd catch _ => pure ()
  let s' ← get
  if (s'.messages.toList.drop nOld).any (·.severity == .error) then
    set { s' with env := s.env, messages := s.messages }

@[command_elab autosubstCmd]
def elabAutosubst : CommandElab := fun stx => do
  -- `wellscoped` modifier (child 1) ⟹ the `Fin`-indexed backend (plan.md §8).
  let isScoped := !stx[1].isNone
  let spec ← addSectionParams (parseSpec stx)
  -- Recognise container heads **on demand**: which `(F …)` heads in this signature are functors we
  -- can thread substitution through (`Prod`, or a regular polynomial functor in its type parameters
  -- like `List`/a user `Tree`/a bifunctor). No registry, no required `deriving` — just the inductive declarations themselves.
  -- We compute each head's `ContainerShape` **once** here (`shapes`, keyed by head name) and thread
  -- it to the generator, so no datatype is re-analyzed per use site. `analyze` only needs the *names*
  -- of the recognised heads (`shapes` + `Prod` if used) for its `badFunctor` check.
  let heads := (spec.sorts.flatMap (·.ctors)).flatMap fun c => c.positions.flatMap (·.head.functorHeads)
  let shapes : Autosubst.Gen.Containers ← heads.eraseDups.filterMapM fun f => do
    return (← liftTermElabM (Autosubst.Gen.containerShape? f)).map (f, ·)
  let names := shapes.map (·.1) ++ (if heads.contains `Prod then [`Prod] else [])
  match Signature.analyze spec isScoped names with
  | .error e => throwError e
  | .ok sig =>
    -- Phase 3: emit the de Bruijn inductives + congruence lemmas.
    for cmd in (← Autosubst.Gen.genCommands isScoped sig) do
      elabCommand cmd
    -- Best-effort `Repr`/`DecidableEq` (skipped for foreign field types lacking the instances).
    for cmd in (← Autosubst.Gen.genDerivingCommands isScoped sig) do
      bestEffortElab cmd
    -- Phase 4: emit upRen / up / ren / subst.
    for cmd in (← Autosubst.Gen.genSubstCommands shapes isScoped sig) do
      elabCommand cmd
    -- Phase 5: emit the lemma tower.
    for cmd in (← Autosubst.Gen.genLemmaCommands shapes isScoped sig) do
      elabCommand cmd
    -- Phase 6: register the tactic-facing lemmas into the `@[asimp]` simp set.
    for cmd in (← Autosubst.Gen.genAutomationCommands sig) do
      elabCommand cmd
    -- Notation pass: per-sort `Subst*`/`Ren*`/`Var` instances backing the `s[σ]`/`s⟨ξ⟩`/`t..` notations.
    for cmd in (← Autosubst.Gen.genNotationCommands isScoped sig) do
      elabCommand cmd

end Autosubst.Frontend
