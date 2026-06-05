/-
# Phase 6 — Automation generation (`@[asimp]` registration).

Emits `attribute [asimp] …` commands that tag each signature's generated clean lemmas and
`up_*`/`upRen_*` functions into the `asimp` simp set, mirroring the reference `asimpl'` rewrite
list + `unfold`s (see [Tactic/Asimp.lean]).
-/
import Lean
import LeanAutosubst.Gen.Lemmas
-- imported so the `renamify_lemmas` attribute's parser is available for the `[… ←]` quotation below
import LeanAutosubst.Tactic.Attr

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-- `attribute [asimp] …` commands registering the tactic-facing lemmas of `sig`. -/
def genAutomationCommands (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
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
      let mut names : Array Ident := #[mkIdent (renRenName s), mkIdent (renSubstName s),
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
  return out

end Autosubst.Gen
