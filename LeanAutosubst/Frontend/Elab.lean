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

/-- A head (`asHead`) or functor argument (`asHeadArg`) ⟶ `ArgHead`. An ident is a declared sort
(`.sort`) if known, else an external type (`.ext`); `F a b …` is a functor application; a
parenthesized head is unwrapped. -/
partial def parseHead (declared : List Name) (s : Syntax) : ArgHead :=
  let k := s.getKind
  if k == ``headApp then
    -- `ident asHeadArg+`: child 0 is the functor name, child 1 the argument group.
    .functor s[0].getId (s[1].getArgs.toList.map (parseHead declared))
  else if k == ``headParen || k == ``headArgParen then
    parseHead declared s[1]   -- `( asHead )` — unwrap
  else -- headAtom / headArgAtom: a lone ident
    let id := s[0].getId
    if declared.contains id then .sort id else .ext id

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
  { name := s[0].getId, ctors := s[2].getArgs.toList.map (parseCtor declared) }

/-- The whole `autosubst` block ⟶ `Spec` (sorts in declaration order). The sort declarations are
at child `2` (child `1` is the optional `wellscoped` modifier). -/
def parseSpec (stx : Syntax) : Spec :=
  let sortDecls := stx[2].getArgs.toList
  let declared := sortDecls.map (·[0].getId)
  { sorts := sortDecls.map (parseSortDecl declared) }

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
  let spec := parseSpec stx
  -- Recognise container heads **on demand**: which `(F …)` heads in this signature are functors we
  -- can thread substitution through (`Prod`, or a unary regular polynomial functor like `List`/a
  -- user `Tree`). No registry, no required `deriving` — just the inductive declarations themselves.
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
