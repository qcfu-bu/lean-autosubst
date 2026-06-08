/-
Port of Autosubst 2's `core.v` runtime prelude.

Reference: rocq/autosubst2-ocaml/share/coq-autosubst-ocaml/core.v

This file provides the sort-independent building block used by all generated code: forward function
composition `funcomp` (Autosubst's `f >> g`) and its identity/associativity laws.

(Nested-container substitution is handled **structurally** by the generator — it reads a container's
constructors and emits a mutual helper + congruences directly; it needs no `list_map`/`option_map`/…
functor laws. See `Gen/Container.lean` for the on-demand shape inference.)
-/

namespace Autosubst

/-- Forward function composition. Matches Coq Autosubst's `funcomp g f = fun x => g (f x)`;
the notation `f >> g` applies `f` first, then `g`. -/
@[reducible] def funcomp {X Y Z : Sort _} (g : Y → Z) (f : X → Y) : X → Z :=
  fun x => g (f x)

/-- Forward composition notation: `f >> g` applies `f` first, then `g`. Higher parser priority than
core `>>` (`HAndThen`/seq) so composition is chosen for function arguments without an ambiguity
error; monadic `>>` still applies where `funcomp` does not typecheck. -/
scoped infixr:80 (priority := high) " >> " => fun f g => funcomp g f

-- Display `funcomp g f` back as the forward-composition notation `f >> g` (the `>>` notation expands
-- through a lambda wrapper, so it has no auto-generated unexpander). Matches the argument flip
-- `f >> g = funcomp g f`. Active wherever `Autosubst` is open, so it also renders generic
-- compositions as `>>`.
open Lean PrettyPrinter in
@[app_unexpander Autosubst.funcomp] def unexpFuncomp : Unexpander
  | `($_ $g $f) => `($f >> $g) | _ => throw ()

theorem funcomp_assoc {W X Y Z : Sort _} (g : Y → Z) (f : X → Y) (h : W → X) :
    funcomp g (funcomp f h) = funcomp (funcomp g f) h := rfl

theorem funcomp_id_left {X Y : Sort _} (f : X → Y) : funcomp id f = f := rfl

theorem funcomp_id_right {X Y : Sort _} (f : X → Y) : funcomp f id = f := rfl

end Autosubst
