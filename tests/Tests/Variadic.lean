/-
# Reference signature: `variadic.sig` — the variadic binder `bind ⟨p, t⟩` (well-scoped only).

    tm : Type
    lam (p : nat) : (bind ⟨p, tm⟩ in tm) → tm     -- binds `p` fresh tm-variables at runtime

A variadic binder introduces `p` fresh variables *at runtime* (`p : Nat`), so the body scope grows
by `p`: `lam : (p : Nat) → tm (n + p) → tm n`. This is **scoped-only** — the unscoped/`Nat` variadic
form is unported (as upstream; rejected with an explicit error, see `Tests/Unsupported.lean`).

The reference `variadic.sig` also has a `list` container (`app : tm → "list"(tm) → tm`), which in
**scoped** mode is Lean-kernel-infeasible (nested container over an indexed family — see
`Tests/Unsupported.lean` §3). So we exercise the variadic *binder* on a container-free signature
(`app : tm → tm → tm`); the binder tower is independent of the container.

**Ground truth.** The `scons_p`/`shift_p`/`zero_p`/`upRen_p` prelude (`Prelude/Scoped.lean`) and the
generated `up_list_*` tower were validated against the reference's Coq output
(`dune exec -- bin/main.exe signatures/variadic.sig -s coq -fext`): the up-helper proofs are the
`scons_p`-calculus terms transcribed from `up_list_tm_tm`/`up_subst_subst_list_tm_tm`/…, adapted to
core `Fin` with the Lean-idiomatic index order `Fin (n + p)`.

Asserts: the tower typechecks, is axiom-clean (`{propext, Quot.sound}`), the generated ops are
defeq to the golden, and representative `by asimp` goals close.
-/
import Tests.Support

namespace Variadic.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  tm where
    | app : tm → tm → tm
    | lam (p : nat) : (bind ⟨p, tm⟩ in tm) → tm

-- Generated shapes match the golden (`tm.lam : (p : Nat) → tm (n + p) → tm n`).
example : ∀ {n} (p : Nat), tm (n + p) → tm n := tm.lam

-- Definitional sanity: `ren`/`subst` reduce through the variadic `lam` exactly as the golden does
-- (the `lam` case lifts via `upRen_list_tm_tm p` / `up_list_tm_tm p`).
example {m n} (σ : Fin m → tm n) (x : Fin m) : subst_tm σ (tm.var_tm x) = σ x := rfl
example {m n} (σ : Fin m → tm n) (p : Nat) (t : tm (m + p)) :
    subst_tm σ (tm.lam p t) = tm.lam p (subst_tm (up_list_tm_tm p σ) t) := rfl
example {m n} (ξ : Fin m → Fin n) (p : Nat) (t : tm (m + p)) :
    ren_tm ξ (tm.lam p t) = tm.lam p (ren_tm (upRen_list_tm_tm p ξ) t) := rfl

-- Representative `by asimp` goals — each routes through the variadic `lam` case of the tower
-- (`idSubst`/`compRenRen`/`compSubstSubst` ⇒ `upId_list`/`up_ren_ren_p`/`up_subst_subst_list`).
theorem identity {n} (s : tm n) : subst_tm tm.var_tm s = s := by asimp
theorem ren_fusion {m n k} (ξ : Fin m → Fin n) (ζ : Fin n → Fin k) (s : tm m) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp
theorem subst_fusion {m n k} (σ : Fin m → tm n) (τ : Fin n → tm k) (s : tm m) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem rinst_id {n} (s : tm n) : ren_tm id s = s := by asimp

-- Axiom-clean: the genuinely variadic up-helper lemmas + the recursive tower + the `asimp` goals.
#axiom_clean upId_list_tm_tm
#axiom_clean up_subst_subst_list_tm_tm
#axiom_clean up_subst_ren_list_tm_tm
#axiom_clean up_ren_subst_list_tm_tm
#axiom_clean rinstInst_up_list_tm_tm
#axiom_clean idSubst_tm
#axiom_clean compSubstSubst_tm
#axiom_clean instId_tm
#axiom_clean rinstId_tm
#axiom_clean identity
#axiom_clean subst_fusion
#axiom_clean rinst_id

end Variadic.Scoped

/-! ## Multi-open-sort variadic is unported (explicit error). -/
namespace Variadic.MultiSort
open Autosubst

/-- error: Variadic binders 'bind ⟨p, _⟩' are only supported for single-substitution-sort signatures (open sorts here: [ty, tm]); multi-sort variadic binding is unported. -/
#guard_msgs in
autosubst wellscoped
  ty where
    | arr : ty → ty → ty
    | all : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  (p : nat) : (bind ⟨p, tm⟩ in tm) → tm
    | tlam : (bind ty in tm) → tm

end Variadic.MultiSort
