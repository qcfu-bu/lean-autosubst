/-
# Unsupported features — asserted **explicitly** (never silent).

Three reference-signature features are out of reach; each fails with a clear, deliberate error
rather than silently miscompiling. We pin those errors with `#guard_msgs`, so the suite breaks if
the behavior ever regresses to a silent (wrong) success.

  1. `variadic.sig`'s variadic binder `lam (p) : (bind ⟨p, tm⟩ in tm)` — supported in the
     **well-scoped** backend (see `Tests/Variadic.lean`) but **unported unscoped** (as upstream;
     it would otherwise lower to a single lift, silently wrong). The unscoped rejection is pinned here.
  2. `fol.sig`'s custom/polyadic functor `Func : "cod (fin p)" (term) → term` — only `Prod`
     and regular inductive containers are threaded; a user `F : Functor` head is unported.
  3. **Scoped containers** — nesting a standard container over a *scope-indexed* inductive is
     rejected by the Lean 4 **kernel**. This is a Lean-vs-Coq kernel difference (Coq's `-s coq`
     accepts these), not an Autosubst limitation; demonstrated at its root below. Unscoped
     containers work — see `Tests/Containers.lean`.
-/
import Tests.Support

/-! ## 1. Variadic binder `bind ⟨p, t⟩` — rejected in **unscoped** mode (works `wellscoped`). -/
namespace XFail.VariadicBinder
open Autosubst

/-- error: Variadic binder 'bind ⟨_, tm⟩' in constructor 'lam' of sort 'tm' is not supported in unscoped mode (use `autosubst wellscoped`; the unscoped variadic form is unported, as upstream). -/
#guard_msgs in
autosubst
  tm where
    | app : tm → (List tm) → tm
    | lam (p : nat) : (bind ⟨p, tm⟩ in tm) → tm

end XFail.VariadicBinder

/-! ## 2. Function-space "functor" head (`fol.sig`'s `cod = fun α => Fin p → α`).

Container heads are recognised **on demand**: a head `(F …)` wrapping a sort is threaded iff `F` is a
regular polynomial functor in its type parameters (`Prod`, `List`/`Option`, or a user tree/box/
bifunctor). A function space has no constructors to recurse on (it is not a polynomial functor), so
it is rejected. -/
namespace XFail.CustomFunctor
open Autosubst

def cod (α : Type) := Nat → α     -- a function-space "functor", like `fol`'s `cod (fin p)`

/-- error: Cannot thread substitution through container head 'cod' in constructor 'Func' of sort 'term': 'cod' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  term where
    | Func : (cod term) → term

end XFail.CustomFunctor

/-! ## 3. Scoped containers are kernel-infeasible (the root cause).

A real substitution sort is genuinely `Nat`-indexed (a binder varies the index, `lam : tm (n+1) →
tm n`); the Lean 4 kernel then rejects nesting a container over it. Shown directly on the de Bruijn
inductive the scoped backend would emit. (Coq's nested-positivity check accepts the analogue.) -/
namespace XFail.ScopedContainer

set_option autoImplicit true in
/-- error: (kernel) invalid nested inductive datatype 'List', nested inductive datatypes parameters cannot contain local variables. -/
#guard_msgs in
inductive tm : Nat → Type
  | seq : List (tm n) → tm n
  | lam : tm (n + 1) → tm n

end XFail.ScopedContainer

/-! ## 4. Name hygiene failures are rejected before generated Lean code is elaborated. -/
namespace XFail.NameHygiene
open Autosubst

/-- error: Duplicate parameter name(s) on sort 'tm': Srt. -/
#guard_msgs in
autosubst
  tm (Srt : Type) {Srt : Type} where
    | lam : (bind tm in tm) → tm

/-- error: Constructor 'var_tm' of sort 'tm' conflicts with generated variable constructor 'var_tm'. -/
#guard_msgs in
autosubst
  tm where
    | var_tm : (bind tm in tm) → tm

end XFail.NameHygiene

/-! ## 5. Constructor result sort must match the enclosing sort. -/
namespace XFail.ResultSort
open Autosubst

/-- error: Constructor 'bad' of sort 'tm' must end in result sort 'tm', but the final component is 'Nat'. -/
#guard_msgs in
autosubst
  tm where
    | bad : tm → Nat

end XFail.ResultSort
