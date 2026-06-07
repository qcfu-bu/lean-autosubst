/-
Port of Autosubst 2's notation layer (`unscoped.v`'s `RenNotations`/`SubstNotations`/
`CombineNotations`/`UnscopedNotations`, and the `fintype.v` scoped analogues).

This is a **purely additive** readability layer over the generated `ren_*`/`subst_*`/`var_*` ops:
the application/function notations are **typeclass-dispatched** (mirroring Autosubst's
`Subst1`/`Subst2`, `Ren1`/`Ren2`, `Var`), so a single notation works across all sorts. The
generator emits one instance per sort (`Gen/Notation.lean`); nothing about the generated ops
themselves changes.

Notations live in **scoped namespaces** (`Autosubst.Notation`, `Autosubst.Scoped.Notation`) — the
analogue of Autosubst's `subst_scope`/`fscope` — so `↑`, `[…]`, `⟨…⟩` do not clash globally (they
overload Lean's coercion `↑`, `GetElem` `xs[i]`, list `[x]`, and anonymous-constructor `⟨…⟩`, and
disambiguate by elaboration). A user opts in with `open Autosubst.Notation` (unscoped) or
`open Autosubst.Scoped.Notation` (well-scoped).

Reference: rocq/autosubst2-ocaml/share/coq-autosubst-ocaml/unscoped.v
-/
import Autosubst.Prelude.Unscoped
import Autosubst.Prelude.Scoped

namespace Autosubst

/-! ## Type classes for notation dispatch (Autosubst's `Var`/`Subst*`/`Ren*`).

Resolution keys on the subject sort `Y` **together with the map type(s)** (all `inParam`s); only
the result `Z` is an `outParam`. Including `Y` is what lets renaming dispatch — the maps alone
share a type (`Nat → Nat`, or `Fin m → Fin n`) across sorts, so the subject is what selects the
sort. The substitution codomain scope is genuinely free of the subject in the well-scoped backend,
so it cannot be recovered from `Y` alone — hence the maps must be `inParam`s, and a *polymorphic*
scoped argument (`↑`, `var_tm`, whose scope is a metavar at the use site) needs a type ascription
there. In the unscoped backend every map type is closed, so no ascription is ever needed. -/

/-- Variable injection, Autosubst's `Var` (`ids : X → Y`). -/
class Var (Y : Type _) (X : Type _) where
  ids : X → Y

/-- Single-map substitution application (`subst1 σ s`). -/
class Subst1 (Y : Type _) (X1 : Type _) (Z : outParam (Type _)) where
  subst1 : X1 → Y → Z
/-- Two-map (parallel) substitution application (`subst2 σ τ s`). -/
class Subst2 (Y : Type _) (X1 X2 : Type _) (Z : outParam (Type _)) where
  subst2 : X1 → X2 → Y → Z
/-- Single-map renaming application (`ren1 ξ s`). -/
class Ren1 (Y : Type _) (X1 : Type _) (Z : outParam (Type _)) where
  ren1 : X1 → Y → Z
/-- Two-map (parallel) renaming application (`ren2 ξ ζ s`). -/
class Ren2 (Y : Type _) (X1 X2 : Type _) (Z : outParam (Type _)) where
  ren2 : X1 → X2 → Y → Z

/-- Lifting a substitution/renaming under one binder, Autosubst's `up_b_v` (`⇑`). The generator
emits an instance **only for single-open-sort signatures**, where the binder sort `b` and component
sort `v` are both forced — so `⇑σ` is unambiguous. In a genuinely multi-sort signature the same map
type is lifted by several binder sorts (e.g. System F's `up_tm_tm` and `up_ty_tm` are both
`(Nat → tm) → (Nat → tm)`), so no single dispatched `⇑` exists and the explicit `up_b_v` names are
used. `X'` is an `outParam` because in the scoped backend `up` increments the scope (`X ≠ X'`). -/
class Up (X : Type _) (X' : outParam (Type _)) where
  up : X → X'

/-! ## Unscoped notations (`Autosubst.Notation`, ≈ Autosubst's `UnscopedNotations`). -/

namespace Notation
open Lean

-- Applied forms use `noWs` before the opening bracket — mirroring Lean's `getElem` `xs[i]` — so
-- that `f [x]` / `g [] []` *with a space* still parse as application to list literals, while
-- `s[σ]` (no space) is substitution. (Without `noWs`, `s:max "["` greedily captures a following
-- `[…]`, so `[] []` failed to parse.)
/-- `s[σ]` — substitution application (one map). -/
scoped syntax:max (name := substApp1) (priority := high) term:max noWs "[" term "]" : term
/-- `s[σ;τ]` — parallel substitution application (two maps, for multi-sort vectors). -/
scoped syntax:max (name := substApp2) (priority := high) term:max noWs "[" term ";" term "]" : term
/-- `s⟨ξ⟩` — renaming application (one map). -/
scoped syntax:max (name := renApp1) (priority := high) term:max noWs "⟨" term "⟩" : term
/-- `s⟨ξ;ζ⟩` — parallel renaming application (two maps). -/
scoped syntax:max (name := renApp2) (priority := high) term:max noWs "⟨" term ";" term "⟩" : term
/-- `[σ]` — substitution as a function (`fscope` form). -/
scoped notation:max "[" σ "]" => Autosubst.Subst1.subst1 σ
/-- `⟨ξ⟩` — renaming as a function (`fscope` form). -/
scoped notation:max "⟨" ξ "⟩" => Autosubst.Ren1.ren1 ξ
/-- `t..` — the single-point substitution `t .: ids` (β-substitution of de Bruijn 0). -/
scoped notation:max t:max ".." => Autosubst.scons t Autosubst.Var.ids
/-- `↑` — the shift renaming. -/
scoped notation:max "↑" => Autosubst.shift
/-- `⇑σ` — lift the substitution/renaming `σ` under one binder (`up_b_v σ`; single-open-sort only). -/
scoped notation:max "⇑" σ:max => Autosubst.Up.up σ

/-- `[a, b, c/]` — the explicit finite substitution `a .: b .: c .: ids`: a prefix of terms with an
identity tail, the `/` marking it a substitution. `[a/]` is the basic single-variable substitution
`a .: ids` (= `a..`). (`/]` is one token, so the term before it is never read as a division.) -/
scoped syntax:max (name := substFin) "[" term,+ "/]" : term
/-- `s[a, b, c/]` — apply that explicit substitution to `s` (so `s[t/]` is the β-substitution). -/
scoped syntax:max (name := substAppFin) (priority := high) term:max noWs "[" term,+ "/]" : term
open Autosubst in
macro_rules (kind := substApp1) | `($s[$σ]) => `(Autosubst.Subst1.subst1 $σ $s)
open Autosubst in
macro_rules (kind := substApp2) | `($s[$σ ; $τ]) => `(Autosubst.Subst2.subst2 $σ $τ $s)
open Autosubst in
macro_rules (kind := renApp1) | `($s⟨$ξ⟩) => `(Autosubst.Ren1.ren1 $ξ $s)
open Autosubst in
macro_rules (kind := renApp2) | `($s⟨$ξ ; $ζ⟩) => `(Autosubst.Ren2.ren2 $ξ $ζ $s)
open Autosubst in
macro_rules (kind := substFin)
  | `([ $ts,* /]) => do
      let mut acc ← `(Var.ids)
      for t in ts.getElems.reverse do acc ← `(scons $t $acc)
      return acc
open Autosubst in
macro_rules (kind := substAppFin)
  | `($s[ $ts,* /]) => do
      let mut acc ← `(Var.ids)
      for t in ts.getElems.reverse do acc ← `(scons $t $acc)
      `(Subst1.subst1 $acc $s)

end Notation

/-! ## Well-scoped notations (`Autosubst.Scoped.Notation`). Same dispatch notations (the classes are
backend-agnostic), but `↑`/`t..` resolve to the `Fin`-indexed primitives. -/

namespace Scoped.Notation
open Autosubst (Subst1 Subst2 Ren1 Ren2 Var)
open Lean

-- Applied forms use `noWs` (see the unscoped namespace above) so `f [x]` / `f ⟨c⟩` with a space
-- stay application, while `s[σ]` / `s⟨ξ⟩` (no space) are substitution / renaming.
scoped syntax:max (name := substApp1) (priority := high) term:max noWs "[" term "]" : term
scoped syntax:max (name := substApp2) (priority := high) term:max noWs "[" term ";" term "]" : term
scoped syntax:max (name := renApp1) (priority := high) term:max noWs "⟨" term "⟩" : term
scoped syntax:max (name := renApp2) (priority := high) term:max noWs "⟨" term ";" term "⟩" : term
scoped notation:max "[" σ "]" => Subst1.subst1 σ
scoped notation:max "⟨" ξ "⟩" => Ren1.ren1 ξ
scoped notation:max t:max ".." => Autosubst.Scoped.scons t Var.ids
scoped notation:max "↑" => Autosubst.Scoped.shift
scoped notation:max "⇑" σ:max => Autosubst.Up.up σ

/-- `[a, b, c/]` — the explicit finite (well-scoped) substitution `a .: b .: c .: ids`. -/
scoped syntax:max (name := substFin) "[" term,+ "/]" : term
/-- `s[a, b, c/]` — apply that explicit substitution to `s`. -/
scoped syntax:max (name := substAppFin) (priority := high) term:max noWs "[" term,+ "/]" : term
macro_rules (kind := substApp1) | `($s[$σ]) => `(Subst1.subst1 $σ $s)
macro_rules (kind := substApp2) | `($s[$σ ; $τ]) => `(Subst2.subst2 $σ $τ $s)
macro_rules (kind := renApp1) | `($s⟨$ξ⟩) => `(Ren1.ren1 $ξ $s)
macro_rules (kind := renApp2) | `($s⟨$ξ ; $ζ⟩) => `(Ren2.ren2 $ξ $ζ $s)
macro_rules (kind := substFin)
  | `([ $ts,* /]) => do
      let mut acc ← `(Var.ids)
      for t in ts.getElems.reverse do acc ← `(Autosubst.Scoped.scons $t $acc)
      return acc
macro_rules (kind := substAppFin)
  | `($s[ $ts,* /]) => do
      let mut acc ← `(Var.ids)
      for t in ts.getElems.reverse do acc ← `(Autosubst.Scoped.scons $t $acc)
      `(Subst1.subst1 $acc $s)

end Scoped.Notation

end Autosubst
