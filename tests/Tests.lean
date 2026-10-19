/-
# Reference-signature test suite.

Ports the reference signatures from [rocq/autosubst2-ocaml/signatures](../rocq/autosubst2-ocaml/signatures)
through the `autosubst` command. Each module runs the generator (both backends where applicable),
and asserts the lemma tower typechecks, is axiom-clean (`#axiom_clean`, see `Tests/Support.lean`),
and that representative `by asimp` goals close. See `README.md` for the full capability matrix.

Build with `lake build Tests`.
-/
module

public import Tests.Support
public import Tests.Stlc          -- stlc.sig + stlc-unicode.sig  (single sort; both backends)
public import Tests.SysfSN        -- sysf.sig + Church-style System F strong normalisation (both backends)
public import Tests.Fcbv          -- fcbv.sig                      (genuinely mutual tm↔vl; both backends)
public import Tests.Pi            -- pi.sig                        (name sort + nullary ctor; both backends)
public import Tests.NumPrelude    -- num.sig + prelude.sig         (external/foreign leaf types; both backends)
public import Tests.Containers    -- logrel_coq.sig + variadic.sig (containers; UNSCOPED only)
public import Tests.Renamify      -- renamify + auto_unfold tactics (Phase 6 remnants; both backends)
public import Tests.Variadic      -- variadic.sig: scoped variadic binder `bind ⟨p, t⟩` (well-scoped only)
public import Tests.UserContainer  -- user containers recognised on demand (a `Tree`); no deriving
public import Tests.ContainerEdgeCases -- container edge cases: foreign-only / closed-sort / namespaced / Prod; clean declines
public import Tests.Notation      -- Autosubst-consistent notations (s[σ]/s⟨ξ⟩/↑/t..); both backends
public import Tests.Parameterized -- parameterized AST sorts, explicit sort refs, parameterized containers
public import Tests.Unsupported   -- explicit xfails: unscoped/multi-sort variadic, custom functor, scoped containers
public import Tests.CaseStudy     -- integration: STLC progress + preservation
