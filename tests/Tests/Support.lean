/-
# Test-suite support: the `#axiom_clean` assertion command.

The reference-signature tests (`Tests/*.lean`) each port a `rocq/.../signatures/*.sig` through the
`autosubst` command and assert three things:

  1. **the lemma tower typechecks** — the file builds at all;
  2. **it is axiom-clean** — every generated/derived lemma depends only on `{propext, Quot.sound}`,
     never `sorryAx`, `Classical.choice`, or anything else (`funext` is a *theorem* in Lean core, so
     it never shows up as an axiom). Checked here by `#axiom_clean`;
  3. **a representative `by asimp` goal closes** — identity, fusion, β-cancellation, and the
     substitution lemma, written as ordinary `example`/`theorem`s in each file.

`#axiom_clean foo` errors (failing the build) if `foo` transitively uses any axiom outside the
clean set — the same check `#print axioms foo` reports, but as a hard assertion.
-/
import Lean
import Autosubst

open Lean Elab Command

/-- The axioms a clean, `funext`/`propext`-based development is allowed to use. -/
def axiomCleanAllowed : List Name := [``propext, ``Quot.sound]

/-- `#axiom_clean foo` asserts `foo` depends only on `{propext, Quot.sound}` (no `sorryAx`,
`Classical.choice`, …); otherwise it errors, failing the build. -/
elab "#axiom_clean " id:ident : command => do
  let cs ← liftCoreM <| realizeGlobalConstWithInfos id
  for constName in cs do
    let axs ← collectAxioms constName
    let bad := axs.filter (fun a => !axiomCleanAllowed.contains a)
    unless bad.isEmpty do
      throwError m!"axiom_clean: '{constName}' depends on disallowed axioms: \
        {bad.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
