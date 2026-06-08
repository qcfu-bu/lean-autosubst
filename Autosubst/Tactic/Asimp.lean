/-
# Phase 6 — the `asimp` tactic.

Lean's answer to Coq Autosubst's `asimpl`. Where the Coq tactic is a hand-tuned
`repeat (first […])` of `setoid_rewrite`s, Lean's `simp` already *is* a rewrite-until-fixpoint
engine that works under binders and uses `funext` — so `asimp` is just `simp only` over the
dedicated `asimp_lemmas` simp set (the tactic is named `asimp`, after Lean's `simp`, not Coq's
`simpl`; the set is named separately so the tactic name can't shadow it — see [Tactic/Attr.lean]).

The set is assembled from:
  • the **notation-native** σ-calculus lemmas — the per-constructor push laws, the fusion /
    identity / variable laws — stated over the typeclass-method / notation forms (`s[σ⃗]`, `s⟨ξ⃗⟩`,
    `.:`, `>>`, `var_s`) and each carrying its own `@[asimp_lemmas]` ([Gen/Laws.lean]);
    together with the **canon** lemmas ([Gen/Notation.lean]) that pull each construct toward the
    normal form — raw `subst_s`/`ren_s` ⟶ the `[σ]`/`⟨ξ⟩` method form (`substCanon{k}`/`renCanon{k}`),
    and the `ids`/`⇑` notations ⟶ the raw `var_s` ctor / `up_b_v` helper (`varIds`/`upLift`). So
    `asimp` *output* keeps subst/ren applications in notation (variables as the raw `var_s` ctor),
    mirroring Coq's `asimpl`;
  • the static σ-calculus laws below (the `scons` simplifications = Coq's `fsimpl`).
`asimp` additionally unfolds the per-sort lifting helpers `up_b_v`/`upRen_b_v` (tagged into the set
by [Gen/Automation.lean]) and the generic `up_ren` (Coq's `unfold up_* ; cbn`); `funcomp`/`scons`
are normalized algebraically by the static laws rather than unfolded.

`rinst_inst` (ren ⇒ subst) is deliberately *not* in the set — like Coq, that conversion belongs
to `substify`/`renamify`, keeping `asimp` from collapsing renamings into substitutions.

`asimp` is `simp only [asimp_lemmas]`, so on a term already in σ-normal form (nothing to rewrite)
it fails with "simp made no progress" — matching `simp only`. That is intentional: a bare `asimp`
reports when it had no effect. The `substify`/`renamify` wrappers, which must tolerate an
already-normal goal, call it as `try asimp` (see below).
-/
import Lean
import Autosubst.Prelude.Unscoped
import Autosubst.Prelude.Scoped
import Autosubst.Tactic.Attr

open Lean

-- Static σ-calculus simplification laws (Coq's `fsimpl` / `unscoped.v`): `scons`/`funcomp`
-- are normalized *algebraically* (associate left, cancel `id`, push through `scons`), and
-- `up_ren` is unfolded — rather than unfolding `funcomp`/`scons` to lambdas.
attribute [asimp_lemmas]
  Autosubst.scons_zero Autosubst.scons_succ
  Autosubst.scons_comp Autosubst.scons_eta Autosubst.scons_eta_id Autosubst.scons_shift
  Autosubst.funcomp_assoc Autosubst.funcomp_id_left Autosubst.funcomp_id_right
  Autosubst.up_ren

-- Well-scoped (`Fin`) analogues for `autosubst wellscoped` goals (plan.md §8).
attribute [asimp_lemmas]
  Autosubst.Scoped.scons_zero Autosubst.Scoped.scons_succ
  Autosubst.Scoped.scons_comp Autosubst.Scoped.scons_eta Autosubst.Scoped.scons_eta_id
  Autosubst.Scoped.scons_shift
  Autosubst.Scoped.up_ren

-- The generic `up_ren` (both backends) belongs to the `auto_unfold` set: unfolding it (after the
-- per-sort `upRen_b_v`, which the generator tags) exposes the underlying `scons`/`funcomp` form.
attribute [auto_unfold_lemmas] Autosubst.up_ren Autosubst.Scoped.up_ren

open Lean.Parser.Tactic in
/-- `asimp` / `asimp at h` / `asimp at *` — normalize substitution/renaming expressions to a
canonical form using the generated `asimp_lemmas` simp set. -/
syntax (name := asimpStx) "asimp" (location)? : tactic

macro_rules
  | `(tactic| asimp $[$loc]?) => `(tactic| simp only [asimp_lemmas] $[$loc]?)

open Lean.Parser.Tactic in
/-- `substify` — rewrite renamings into substitutions (`ren_s ξ ↦ subst_s (var ∘ ξ)`), then
normalize with `asimp`. -/
syntax (name := substifyStx) "substify" (location)? : tactic

macro_rules
  | `(tactic| substify $[$loc]?) =>
    -- the cleanup `asimp` is tolerant: like Coq's `repeat`-based `asimpl`, the trailing
    -- normalization must not fail when there is nothing left to simplify (e.g. the goal is a
    -- relation, not an equation). Mirrors `renamify` below.
    `(tactic| simp only [substify_lemmas] $[$loc]? <;> (try asimp $[$loc]?))

open Lean.Parser.Tactic in
/-- `renamify` — the reverse of `substify`: rewrite substitutions `subst_s (var ∘ ξ) ↦ ren_s ξ`
(via `rinstInst'_s` oriented right-to-left in the `renamify_lemmas` set), then normalize with
`asimp`. Mirrors the reference `renamify` (`setoid_rewrite_left rinstInst'`). -/
syntax (name := renamifyStx) "renamify" (location)? : tactic

macro_rules
  | `(tactic| renamify $[$loc]?) =>
    -- the directional rewrite is required; the cleanup `asimp` is tolerant (a bare `ren_s ξ` has
    -- nothing left to normalize, so `asimp` there would otherwise error "no progress").
    `(tactic| simp only [renamify_lemmas] $[$loc]? <;> (try asimp $[$loc]?))

open Lean.Parser.Tactic in
/-- `auto_unfold` / `auto_unfold at h` / `auto_unfold at *` — unfold the generated lifting helpers
(`up_<b>_<v>` / `upRen_<b>_<v>`) and the generic `up_ren`, exposing the `scons`/`funcomp`/`ren shift`
machinery. Mirrors the reference `auto_unfold` (a bare `unfold`, no σ-calculus rewriting). -/
syntax (name := autoUnfoldStx) "auto_unfold" (location)? : tactic

macro_rules
  | `(tactic| auto_unfold $[$loc]?) => `(tactic| simp only [auto_unfold_lemmas] $[$loc]?)
