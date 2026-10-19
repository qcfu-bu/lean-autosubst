/-
# Reference signatures with **nested containers** — `logrel_coq.sig` and `variadic.sig` (the
container part). UNSCOPED ONLY.

Container/functor positions (`Option term`, `List tm`, binders into them) are threaded through
the standard Lean containers `List`/`Option`/`Prod` via the generated mutual structural helpers
(Phase 9). These work in the **unscoped** backend only: nesting a container over a *scope-indexed*
inductive is rejected by the Lean 4 **kernel** ("invalid nested inductive datatype … parameters
cannot contain local variables"), a Lean-vs-Coq kernel difference — see `Tests/Unsupported.lean`,
which exhibits that kernel error explicitly. (The variadic *binder* `bind ⟨p, t⟩` of `variadic.sig`
is unported in both backends — also in `Tests/Unsupported.lean`.)
-/
module

public import Tests.Support

@[expose] public section

/-! ## `logrel_coq.sig` — `Option` functor + a binder into `Option` (`tPair`), `Nat`-as-foreign. -/
namespace Logrel
open Autosubst

-- `sort : Type` is foreign here (no `sort`-variables in the fragment we exercise) ⟶ `Nat`.
autosubst
  term where
    | tSort     : Nat → term
    | tProd     : term → (bind term in term) → term
    | tLambda   : (Option term) → (bind term in term) → term
    | tApp      : term → term → term
    | tNat      : term
    | tZero     : term
    | tSucc     : term → term
    | tNatElim  : (bind term in term) → term → term → term → term
    | tEmpty    : term
    | tEmptyElim : (bind term in term) → term → term
    | tSig      : term → (bind term in term) → term
    | tPair     : term → (bind term in (Option term)) → term → term → term
    | tFst      : term → term
    | tSnd      : term → term

@[reducible] def inst (t : term) : Nat → term := scons t term.var_term

theorem identity (s : term) : subst_term term.var_term s = s := by asimp
theorem subst_fusion (σ τ : Nat → term) (s : term) :
    subst_term τ (subst_term σ s) = subst_term (funcomp (subst_term τ) σ) s := by asimp
theorem ren_id (s : term) : ren_term id s = s := by asimp
theorem beta_cancel (t s : term) : subst_term (inst t) (ren_term shift s) = s := by asimp
-- The substitution lemma, threaded through `Option`/binder-into-`Option` positions.
theorem subst_lemma (σ : Nat → term) (t s : term) :
    subst_term σ (subst_term (inst t) s)
      = subst_term (inst (subst_term σ t)) (subst_term (up_term_term σ) s) := by asimp

#axiom_clean substSubst_term   -- covers nullary tNat/tZero/tEmpty, Option, binder-into-Option
#axiom_clean instId_term
#axiom_clean subst_lemma

end Logrel

/-! ## `variadic.sig` — the `List` container part (`app : tm → List tm → tm`).

The variadic *binder* `lam (p) : (bind ⟨p, tm⟩ in tm)` is unported (see `Tests/Unsupported.lean`);
the `List` functor in `app` works unscoped. -/
namespace Variadic
open Autosubst

autosubst
  tm where
    | app : tm → (List tm) → tm
    | lam : (bind tm in tm) → tm        -- ordinary single binder in place of the variadic one

@[reducible] def inst (t : tm) : Nat → tm := scons t tm.var_tm

theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem beta_cancel (t s : tm) : subst_tm (inst t) (ren_tm shift s) = s := by asimp
theorem subst_lemma (σ : Nat → tm) (t s : tm) :
    subst_tm σ (subst_tm (inst t) s)
      = subst_tm (inst (subst_tm σ t)) (subst_tm (up_tm_tm σ) s) := by asimp

#axiom_clean substSubst_tm     -- threaded through the `List` helper
#axiom_clean subst_lemma

end Variadic
