# lean-autosubst

[![Lean](https://img.shields.io/badge/Lean-v4.30.0-blue)](lean-toolchain)

A Lean 4 port of [Autosubst 2](https://github.com/uds-psl/autosubst2) for de Bruijn substitution
boilerplate. Specify the syntax of your language using a HOAS-style DSL inside a `.lean` file. 
During elaboration, `autosubst` creates kernel-checked Lean declarations: the de Bruijn
inductive types, renaming/substitution operations, equational lemmas, and the `asimp` simp set for
substitution goals.

Unlike the Coq/OCaml Autosubst, this port has no external generator and does not write generated
source text. The `autosubst` command runs inside Lean; a generated lemma that fails to typecheck
surfaces as an elaboration error. No Mathlib dependency.

- Two backends from one spec: unscoped (`Nat`-indexed) and well-scoped (`Fin`-indexed).
- Multi-sorted, mutually-recursive syntax with parallel substitutions (System F, CBV, …).
- Nested containers (`List`, `Option`, `Prod`, or your own inductive), recognised on demand.
- Tactics: `asimp` / `substify` / `renamify` / `auto_unfold`.
- Autosubst-style notations: `s[σ]`, `s⟨ξ⟩`, `⇑σ`, `[t/]`, … (opt-in).
- Axiom-clean output: the generated tower uses only `propext` and `Quot.sound`.

```lean
import Autosubst
open Autosubst Autosubst.Notation

autosubst
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

-- Everything below `autosubst` is generated. The substitution lemma, proved automatically:
example (σ : Nat → tm) (t s : tm) :
    (s[t/])[σ] = (s[⇑σ])[t[σ]/] := by asimp
```

## Installation

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "lean-autosubst"
git  = "https://github.com/qcfu-bu/lean-autosubst.git"
rev  = "main"
```

or, with a Lean `lakefile.lean`:

```lean
require «lean-autosubst» from git
  "https://github.com/qcfu-bu/lean-autosubst.git" @ "main"
```

then `import Autosubst`. Your project's `lean-toolchain` must match the one pinned here
([`leanprover/lean4:v4.30.0`](lean-toolchain)).

## The DSL

### The command: `autosubst` and `autosubst wellscoped`

```lean
autosubst              -- unscoped: variables are `Nat`, `var_tm : Nat → tm`
autosubst wellscoped   -- well-scoped: variables are `Fin n`, `var_tm : Fin n → tm n`
  <sort> where
    | <ctor> : <arg> → … → <sort>
    | …
  <sort> where …       -- one block per syntactic sort; mutually-recursive sorts are detected
```

The block *reads* like (mutual) Lean `inductive`s, but it is never elaborated as one. It is captured
as syntax, lowered to a first-order de Bruijn inductive (binders erased), and only that
strictly-positive inductive reaches the kernel. `bind`-annotated "function arrows" never become real
function types, so positivity is a non-issue. Constructor arrows may be written with either the
unicode `→` or ASCII `->` (the two may be mixed), exactly as in Lean.

* Unscoped (default): `tm : Type`, `var_tm : Nat → tm`, `lam : ty → tm → tm`.
* Well-scoped (`wellscoped`): each substitution sort is indexed by one `Nat` per kind of
  variable it carries: `tm : Nat → Type`, `var_tm : Fin n → tm n`, `lam : ty → tm (n+1) → tm n`.
  Scope indices are auto-bound implicits.

Sort declarations may also carry ordinary Lean-style parameters. Explicit, implicit, strict
implicit, and instance binders are preserved on the generated inductive. Generated
operations/lemmas rebind ordinary parameters implicitly so calls stay compact, while instance
parameters stay instance-implicit:

```lean
universe u v

autosubst
  Ty {Srt : Type u} (Ann : Type v) [BEq Srt] where
    | base : Srt → Ty
    | tag  : Ann → Ty

  Tm {Srt : Type u} (Ann : Type v) [BEq Srt] where
    | ann   : Tm → Ty Srt Ann → Tm     -- explicit sort application
    | plain : Ty → Tm                  -- bare `Ty` means `Ty Srt Ann`
    | ext   : opaque(Thunk Srt Ann) → Tm
```

All sorts in one mutual `autosubst` block currently share the same parameter telescope. The
`opaque(e)` wrapper accepts an arbitrary Lean type expression and treats it as a foreign leaf field:
renaming/substitution carry it unchanged and do not inspect it for sort occurrences.

Ambient `section` variables mentioned in the DSL are captured automatically as sort parameters, along
with any section variables their types depend on. Instance section variables are captured when their
class type depends on an already-captured variable:

```lean
section
variable (Srt : Type u)
variable [BEq Srt]

autosubst
  Tm where
    | atom : Srt → Tm        -- elaborates as if `Tm (Srt : Type u) [BEq Srt]` had been written
    | lam  : (bind Tm in Tm) → Tm
end
```

### Binders: `bind a in h` and `bind a, b in h`

A constructor argument that binds variables wraps its head type in a `bind … in …` annotation:

```lean
| lam   : ty → (bind tm in tm) → tm          -- `lam`'s body binds one `tm` variable
| tlam  : (bind ty in tm) → tm               -- a *cross-sort* binder: binds a `ty` in a `tm`
| split : tm → (bind tm, tm in tm) → tm      -- simultaneous binding of TWO variables (Σ-/pair elim)
```

`bind a, b in h` binds several variables at once in the same position. Substitution lifts once per
binder (`up ∘ up …`); in well-scoped mode the body's scope jumps accordingly (`tm (n+1+1)`). See
[Autosubst/Examples/PairBindDsl.lean](Autosubst/Examples/PairBindDsl.lean).

### Container heads `F a` and external types

A substitutable sort may be nested inside a container such as `List`, `Option`, `Prod`, or an
inductive of your own. Substitution threads through the container automatically. Container
application is plain juxtaposition, exactly as in Lean. No parentheses are needed at the top level;
parentheses are needed only to *nest* one application inside another, just as `List (Option α)` needs
them in Lean:

```lean
| seq : List tm → tm                    -- substitution maps over the list
| opt : Option tm → tm
| pr  : Prod tm tm → tm                 -- i.e. `tm × tm`
| brs : List (Prod tm tm) → tm          -- nesting needs the inner parens
| lam : (bind tm in List tm) → tm       -- a binder *into* a container
```

`List`/`Option`/`Prod` use the same on-demand check as user-defined containers. When `autosubst`
meets a head `F …`, it reads `F`'s declaration: if `F` is a *regular polynomial functor* in its type
parameters (each constructor argument is a type parameter, a uniform recursive occurrence, or a
parameter-free/inert type), substitution threads through every applied argument that contains
substitutable syntax. Use the container directly; no registration or `deriving` is required:

```lean
inductive Tree (α : Type) | leaf : α → Tree α | node : Tree α → Tree α → Tree α

autosubst
  tm where
    | branch : Tree tm → tm            -- threads through `Tree` automatically; `Tree` needs no markup
    | …
```

Parameterized and multi-parameter containers are supported too. Substitution follows the roles of
the applied arguments: `PBox Srt Tm` changes only the `Tm` slot because `Srt` is external metadata,
while `PairBox Ty Tm` changes both syntactic slots and `PairBox Tm Nat` changes the non-final slot.

```lean
inductive PBox (Srt : Type u) (α : Type v) where
  | wrap : Srt → α → PBox Srt α

inductive PairBox (α : Type u) (β : Type v) where
  | both : α → β → PairBox α β
  | roll : PairBox α β → PairBox α β

autosubst
  Ty {Srt : Type u} where
    | marker : Srt → Ty
    | arr : Ty → Ty → Ty

  Tm {Srt : Type u} where
    | boxed : PBox Srt Tm → Tm
    | pair  : PairBox Ty Tm → Tm
    | left  : PairBox Tm Nat → Tm
```

A head that wraps a sort but *isn't* such a functor (a function space like `cod = fun α => Fin p →
α`, a non-regular type) is rejected with a clear error rather than being threaded incorrectly. See
[the capability matrix](#capability-matrix).

Any identifier that is not a declared sort is treated as an external (foreign) leaf type and carried
unchanged by `ren`/`subst`, regardless of case. This is how you reference ordinary Lean types
(`Nat`, `Bool`) and your own types (`mytype`, lowercase included):

```lean
| const : Nat → tm        -- `Nat` is foreign; `const c` is substitution-invariant
| lit   : mytoken → tm    -- a lowercase user type works just as well
```

The generated inductive's convenience `Repr`/`DecidableEq` instances are derived when possible. A
foreign field type that lacks them (say, one with a function field) does not block generation. You do
not get those two instances for that sort, but you can add them yourself afterwards
(`deriving instance Repr for tm`). Sorts with only ordinary fields keep them as before.

A sort with no constructors is a pure *variable/name* sort (only `var_<sort>`), e.g. channel names in
the π-calculus.

## Generated names (the contract)

For each substitution sort `s` (one carrying variables) with substitution vector `[v₁ … vₖ]` (the
kinds of variable `s` contains), `autosubst` emits, with these exact names:

| name                                                                           | meaning                                                   |
| ------------------------------------------------------------------------------ | --------------------------------------------------------- |
| `s`, `var_s`                                                                   | the de Bruijn inductive and its variable constructor      |
| `congr_<sort>_<ctor>`                                                          | congruence lemma, one per non-leaf constructor            |
| `ren_s`, `subst_s`                                                             | parallel renaming/substitution (one map per `vᵢ`)         |
| `upRen_b_v`, `up_b_v`                                                          | lift a renaming/substitution through a binder of sort `b` |
| `idSubst_s`, `extRen_s`, `ext_s`                                               | `subst id = id` and extensionality                        |
| `compRenRen_s`, `compRenSubst_s`, `compSubstRen_s`, `compSubstSubst_s`         | the four fusion laws                                      |
| `rinst_inst_s`                                                                 | renaming is a special case of substitution                |
| `renRen_s`, `renSubst_s`, `substRen_s`, `substSubst_s` (+ `'` map-level forms) | clean fusion wrappers                                     |
| `instId_s`, `rinstId_s`, `varL_s`, `varLRen_s`                                 | `subst var = id`, `ren id = id`, var laws                 |

These match the upstream Autosubst names; the non-primed `instId`/`compComp…`/`rinstInst` forms are
exactly what `asimp` rewrites with. Hand-written golden references live in
[Autosubst/Examples/](Autosubst/Examples/) (`Stlc`, `SysF`, `StlcScoped`, `SysFScoped`,
`Container`).

## Tactics

* **`asimp`**: normalize substitution/renaming expressions to a canonical form (the σ-calculus
  normal form). Closes the standard goals: substitution identity, `ren id = id`, the four fusions,
  β-cancellation (`(ren shift s)[t..] = s`), and the substitution lemma. Variants `asimp at h` and
  `asimp at *` are supported. Implemented as `simp only [asimp_lemmas]` over the generated lemmas
  plus the static σ-laws ([Autosubst/Tactic/Asimp.lean](Autosubst/Tactic/Asimp.lean)).
* **`substify`**: rewrite renamings into substitutions (`ren_s ξ ↦ subst_s (var ∘ ξ)`) and then
  `asimp`. Variants `substify at h` / `at *`.
* **`renamify`**: the inverse of `substify`: rewrite `subst_s (var ∘ ξ) ↦ ren_s ξ` (the same
  `rinstInst'_s` identity, oriented right-to-left) and then `asimp`. Variants `renamify at h` / `at *`.
* **`auto_unfold`**: unfold the lifting helpers (`up_*` / `upRen_*` / `up_ren`), exposing the
  underlying `scons`/`funcomp`/`ren shift` machinery (no σ-calculus rewriting). Variants `at h` / `at *`.

```lean
example (s : tm) : ren_tm id s = s := by asimp
example (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
example (ξ : Nat → Nat) (s : tm) : subst_tm (funcomp tm.var_tm ξ) s = ren_tm ξ s := by renamify
```

`@[asimp_lemmas]` / `@[substify_lemmas]` / `@[renamify_lemmas]` / `@[auto_unfold_lemmas]` are the
underlying simp sets, should you want to add your own lemmas.

## Notations

A purely additive, opt-in readability layer mirroring upstream Autosubst's notation set
([Autosubst/Prelude/Notation.lean](Autosubst/Prelude/Notation.lean)). Open
`Autosubst.Notation` (unscoped) or `Autosubst.Scoped.Notation` (well-scoped) to bring them into
scope:

| notation      | meaning                           | desugars to                        |
| ------------- | --------------------------------- | ---------------------------------- |
| `s[σ]`        | substitution application          | `subst_s σ s`                      |
| `s[σ;τ]`      | parallel (two-map) substitution   | `subst_s σ τ s`                    |
| `s⟨ξ⟩`        | renaming application              | `ren_s ξ s`                        |
| `s⟨ξ;ζ⟩`      | parallel (two-map) renaming       | `ren_s ξ ζ s`                      |
| `[σ]`, `⟨ξ⟩`  | the same as functions             | `subst_s σ`, `ren_s ξ`             |
| `[a, b, c/]`  | explicit finite substitution      | `a .: b .: c .: var_s`             |
| `s[a, b, c/]` | applied to `s`                    | `subst_s (a .: b .: c .: var_s) s` |
| `t..`         | single-point β-substitution       | `t .: var_s` (= `[t/]`)            |
| `↑`           | the shift renaming                | `shift`                            |
| `⇑σ`          | lift under one binder (see below) | `up_b_v σ`                         |
| `f >> g`      | forward composition (always on)   | `funcomp g f`                      |
| `s .: σ`      | cons onto a map (always on)       | `scons s σ`                        |

The `[a, b, c/]` form (the `/` marks it a *substitution*, distinct from a list literal `[a, b, c]`)
is the explicit finite substitution: a prefix of terms with an identity tail. The `s[t/]` form is
its single-variable application (β). It replaces the ad-hoc `inst`/`scons t var` aliases that
example files used to define by hand.

`⇑σ` is the lift of `σ` under one binder (`up_b_v σ`). It is emitted only for single-open-sort
signatures (STLC, the container example, the variadic test), where the binder sort `b` and component
sort `v` are both forced. In a multi-sort signature the same map type can be lifted by several binder
sorts. In System F, `up_tm_tm` and `up_ty_tm` are both `(Nat → tm) → (Nat → tm)`, so no single
dispatched `⇑` exists and the explicit `up_b_v` names are used. This is also why upstream Autosubst
gives `up` only a *printing* abbreviation. Parameterized sorts currently get the raw generated
operations and theorem tower, but not the notation instances; use names such as `subst_Tm`, `ren_Tm`,
and `up_Tm_Tm` directly for those signatures.

The application/function forms are typeclass-dispatched (`Subst1`/`Subst2`, `Ren1`/`Ren2`,
`Var`), so one notation works across all sorts; `autosubst` emits one instance per sort. Dispatch
keys on the subject sort and map type, and `asimp` is taught (via generated `rfl` bridge lemmas)
to normalize the notations away before rewriting, so `by asimp` closes notation'd goals unchanged.

```lean
open Autosubst Autosubst.Notation
example (t s : tm)           : (s⟨↑⟩)[t/] = s              := by asimp   -- β cancels a shift
example (σ : Nat → tm) (s : tm) : s[σ][σ] = s[σ >> [σ]]    := by asimp   -- fusion, notated
```

The notations live in scoped namespaces (Autosubst's `subst_scope`/`fscope`), so `↑`, `s[i]`,
`[x]`, `⟨x⟩` overload Lean's coercion / `GetElem` / list / anonymous-constructor syntax and
disambiguate by elaboration rather than clashing. In the well-scoped backend, a *polymorphic*
constant map (`↑`, `var_s`; its scope is a metavar at the use site) needs a one-off type
ascription, e.g. `(↑ : Fin n → Fin (n+1))`; concrete map variables never do, and the unscoped
backend never needs one. See [Autosubst/Examples/StlcDsl.lean](Autosubst/Examples/StlcDsl.lean)
(unscoped), [SysfDsl.lean](Autosubst/Examples/SysfDsl.lean) (two-map), and
[StlcScopedDsl.lean](Autosubst/Examples/StlcScopedDsl.lean) (scoped).

## Capability matrix

Verified by the test suite ([tests/](tests/), built with `lake build Tests`), which ports each
reference signature from the upstream
[Autosubst 2 OCaml port](https://github.com/uds-psl/autosubst-ocaml) and asserts the tower
typechecks, is axiom-clean (`{propext, Quot.sound}` only; no `sorryAx`/`Classical.choice`), and
that representative `by asimp` goals close.

| signature                        | feature exercised                                                |  unscoped   |  well-scoped   |
| -------------------------------- | ---------------------------------------------------------------- | :---------: | :------------: |
| `stlc` / `stlc-unicode`          | single sort; unicode names                                       |      ✅      |       ✅        |
| `sysf`                           | multi-sort, hierarchical; two parallel maps                      |      ✅      |       ✅        |
| `fcbv`                           | mutual sorts (`tm ↔ vl`), cross-sort binders                     |      ✅      |       ✅        |
| `pi`                             | pure name sort + nullary constructor                             |      ✅      |       ✅        |
| `num` / `prelude`                | external/foreign leaf types (`Nat`, `Bool`)                      |      ✅      |       ✅        |
| `logrel_coq`                     | `Option` functor + binder-into-`Option`                          |      ✅      |   ⛔ kernel¹    |
| `variadic` (container part)      | `List` functor                                                   |      ✅      |   ⛔ kernel¹    |
| `variadic` (binder `bind ⟨p,t⟩`) | variadic binding (runtime `p`)                                   | ⛔ unported² | ✅ single-sort² |
| (user)                           | own container, recognised on demand (a `Tree`)                   |     ✅³      |   ⛔ kernel¹    |
| `parameterized`                  | sort params, explicit sort refs, `opaque`, polynomial containers |     ✅⁴      |   ⛔ kernel¹    |

**¹** Nesting a container over a *scope-indexed* inductive is rejected by the Lean 4 kernel
(`invalid nested inductive datatype … parameters cannot contain local variables`). This is a
Lean-vs-Coq kernel difference: Coq's `-s coq` accepts the analogue. It is not an Autosubst/maths
limitation. Unscoped containers work.

**²** The variadic binder `bind ⟨p, t⟩` (a runtime count `p` of fresh variables; `lam (p : nat) :
(bind ⟨p, tm⟩ in tm) → tm` ⟶ `lam : (p : Nat) → tm (n + p) → tm n`) is supported in the
well-scoped backend for single-substitution-sort signatures
([tests/Tests/Variadic.lean](tests/Tests/Variadic.lean)), via `scons_p`/`shift_p`/`zero_p`/`upRen_p`
([Autosubst/Prelude/Scoped.lean](Autosubst/Prelude/Scoped.lean), index order `Fin (n + p)`).
The unscoped variadic form and the multi-open-sort scoped form are unported (explicit error).
The fixed-arity `bind a, b` multi-binder *is* supported in both backends.

**³** A user's own inductive can be used as a container without registration, attributes, or
`deriving`. When `autosubst` meets a head `F …` it reads `F`'s declaration on demand: if `F` is a
*regular polynomial functor* in its type parameters (constructor arguments use parameters only as
elements, uniform recursive `F ...` occurrences, or not at all), it derives a structural helper and a
`congrC_F_<ctor>` congruence directly from the constructors and threads substitution through
([tests/Tests/UserContainer.lean](tests/Tests/UserContainer.lean)). `List`/`Option` go through this
same check rather than a special case; `Prod` is the lone inline case (binary, threaded by
projections). A sort-wrapping head that *fails* the check is rejected with an explicit error. A
function-space "functor" like `fol`'s `cod = fun α => Fin p → α` has no constructors to recurse on
(asserted in `Tests/Unsupported.lean`), so it is not threaded.

**⁴** Parameterized sort declarations support multiple explicit/implicit Lean parameters and
explicit sort references such as `Ty Srt Ann`. Multi-parameter user containers are recognised when
they are regular polynomial functors in their type parameters; each applied argument is threaded
according to the syntax it contains, including non-final arguments. As with other containers, nesting
them over a well-scoped indexed family hits the Lean kernel limitation above. The generated raw
operations and lemmas are covered by
[tests/Tests/Parameterized.lean](tests/Tests/Parameterized.lean).

Each ⛔ above is asserted (with `#guard_msgs`) in
[tests/Tests/Unsupported.lean](tests/Tests/Unsupported.lean), so a regression to a silent success
breaks the build. The STLC progress and preservation case study built on the generated operations is
in [tests/Tests/CaseStudy.lean](tests/Tests/CaseStudy.lean).

### Not modelled

Custom variable-constructor renaming (`tm(tRel)` in `utlc.sig`) is not supported; `var_<sort>` is
fixed by the name contract. Constructor/sort names must be valid Lean identifiers, so reserved tokens
(`λ`) and non-letter unicode are unavailable (a Lean lexical constraint). Autosubst's *modular*
syntax feature is out of scope (as in the OCaml port). User-defined indexed sort families beyond the
well-scoped `Nat`/`Fin` backend are also not modelled: supporting arbitrary indices would require
dependent renaming/substitution maps indexed by the source family index, rather than the current
homogeneous map vector per open sort.

## Building

```sh
lake build          # the library: the `autosubst` command + tactics + notations
lake build Tests    # the reference-signature test suite
```

## References

- Kathrin Stark, Steven Schäfer, Jonas Kaiser. *Autosubst 2: Reasoning with Multi-Sorted de Bruijn
  Terms and Vector Substitutions* (CPP 2019).
- [Autosubst 2](https://github.com/uds-psl/autosubst2), the original Haskell generator (emits Coq).
- [autosubst-ocaml](https://github.com/uds-psl/autosubst-ocaml), the OCaml reimplementation this
  port follows; its `signatures/` are the test oracle here.

## License

Released under the [MIT License](LICENSE).
