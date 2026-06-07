/-
# Phase 6 — Automation generation (`@[asimp]` registration).

Emits `attribute [asimp] …` commands that tag each signature's generated clean lemmas and
`up_*`/`upRen_*` functions into the `asimp` simp set, mirroring the reference `asimpl'` rewrite
list + `unfold`s (see [Tactic/Asimp.lean]).
-/
import Lean
import Autosubst.Gen.Lemmas
-- imported so the `renamify_lemmas` attribute's parser is available for the `[… ←]` quotation below
import Autosubst.Tactic.Attr

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-- `attribute [asimp] …` commands registering the tactic-facing lemmas of `sig`. -/
def genAutomationCommands (sc : Bool) (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let opens := openSorts sig
  let mut out : Array (TSyntax `command) := #[]
  -- unfold the lifting functions (Coq's `unfold up_* upRen_* up_list_* upRen_list_*`)
  let mut ups : Array Ident := #[]
  for b in opens do
    for v in opens do
      ups := ups.push (mkIdent (upName b v))
      ups := ups.push (mkIdent (upRenName b v))
  for b in variadicBoundSorts sig do
    for v in opens do
      ups := ups.push (mkIdent (upListName b v))
      ups := ups.push (mkIdent (upRenListName b v))
  if ups.size > 0 then
    out := out.push (← `(command| attribute [asimp_lemmas] $ups*))
    -- the same lifting helpers back the standalone `auto_unfold` tactic
    out := out.push (← `(command| attribute [auto_unfold_lemmas] $ups*))
  -- per-sort fusion / identity / variable lemmas (the `asimpl'` rewrite list)
  for comp in sig.components do
    for si in substSortsOf sig comp do
      let s := si.name
      -- `subst_s`/`ren_s` themselves (their generated equation lemmas) so `asimp` pushes a
      -- substitution/renaming through constructors, not only the σ-calculus fusion laws.
      let mut names : Array Ident := #[mkIdent (substName s), mkIdent (renName s),
        mkIdent (renRenName s), mkIdent (renSubstName s),
        mkIdent (substRenName s), mkIdent (substSubstName s),
        mkIdent (renRenName' s), mkIdent (renSubstName' s),
        mkIdent (substRenName' s), mkIdent (substSubstName' s),
        mkIdent (instIdPName s), mkIdent (rinstIdPName s),
        mkIdent (instIdName s), mkIdent (rinstIdName s)]
      if si.isOpen then
        names := names ++ #[mkIdent (varLName s), mkIdent (varLRenName s),
          mkIdent (varLPName s), mkIdent (varLRenPName s)]
      out := out.push (← `(command| attribute [asimp_lemmas] $names*))
      -- `substify` rewrites ren ⇒ subst via `rinstInst'_s`; `renamify` is the same lemma reversed
      -- (subst (var ∘ ξ) ⇒ ren), tagged with `←` into its own set.
      out := out.push (← `(command| attribute [substify_lemmas] $(mkIdent (rinstInstPName s))))
      out := out.push (← `(command| attribute [renamify_lemmas ←] $(mkIdent (rinstInstPName s))))
      -- Function-level (unapplied) ren⇒subst, mirroring Coq's `rinstInst'Fun`. Lets `substify`/
      -- `renamify` convert a bare `ren_s ξ` / `subst_s (var ∘ ξ)` sitting as a `funcomp` argument
      -- (where the applied `rinstInst'_s` cannot fire), keeping the two representations confluent.
      if si.isOpen then
        let pbs ← sigImplicitBinders sig
        let funName := mkIdent (Name.mkSimple s!"rinstInstFun'_{s}")
        let xiTy ← mapTy sc sig true s "m" "n"
        out := out.push (← `(command|
          theorem $funName $pbs* (ξ : $xiTy) :
            $(mkIdent (renName s)) ξ
              = $(mkIdent (substName s)) ($(mkIdent ``Autosubst.funcomp) $(mkIdent (s ++ varName s)) ξ) :=
            funext ($(mkIdent (rinstInstPName s)) ξ)))
        out := out.push (← `(command| attribute [substify_lemmas] $funName))
        out := out.push (← `(command| attribute [renamify_lemmas ←] $funName))
  return out

end Autosubst.Gen
