/-
# Reference signatures: `num.sig` and `prelude.sig` — **external (foreign) leaf types**.

`num.sig` carries a foreign `nat` and `prelude.sig` a foreign `test`. In the DSL a foreign type is
just a capitalized Lean type referenced directly (`Nat`, `Bool`): the parser records it as an
`ext` head, which `ren`/`subst` carry unchanged. The constructor `const : Nat → tm` is then an
**all-`ext` (leaf) constructor** — substitution-invariant — whose tower cases are `rfl` and which
gets no `congr` lemma; this also makes the *scoped* backend work (its result scope is left free,
not forced). Both backends.
-/
module

public import Tests.Support

@[expose] public section

/-! ## `num.sig` — unscoped -/
namespace Num.Unscoped
open Autosubst

autosubst
  tm where
    | app   : tm → tm → tm
    | lam   : (bind tm in tm) → tm
    | const : Nat → tm          -- foreign `nat` ⟶ external `Nat` leaf
    | Plus  : tm → tm → tm

example : Nat → tm := tm.const

theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem beta_cancel (t s : tm) : subst_tm (scons t tm.var_tm) (ren_tm shift s) = s := by asimp
-- A `const c` is unaffected by any substitution (leaf constructor).
theorem const_stable (σ : Nat → tm) (c : Nat) : subst_tm σ (tm.const c) = tm.const c := rfl

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean beta_cancel

end Num.Unscoped

/-! ## `num.sig` — well-scoped (the all-`ext` `const` must not break scope inference) -/
namespace Num.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  tm where
    | app   : tm → tm → tm
    | lam   : (bind tm in tm) → tm
    | const : Nat → tm
    | Plus  : tm → tm → tm

example {n} : Nat → tm n := tm.const

theorem identity {n} (s : tm n) : subst_tm tm.var_tm s = s := by asimp
theorem beta_cancel {n} (t s : tm n) :
    subst_tm (scons t tm.var_tm) (ren_tm shift s) = s := by asimp
theorem const_stable {m n} (σ : Fin m → tm n) (c : Nat) :
    subst_tm σ (tm.const c) = tm.const c := rfl

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean beta_cancel

end Num.Scoped

/-! ## `prelude.sig` — a foreign `test` type, both backends. -/
namespace Prelude.Unscoped
open Autosubst

autosubst
  term where
    | C   : Bool → term          -- foreign `test` ⟶ external `Bool` leaf
    | lam : (bind term in term) → term
    | app : term → term → term

theorem identity (s : term) : subst_term term.var_term s = s := by asimp
theorem beta_cancel (t s : term) :
    subst_term (scons t term.var_term) (ren_term shift s) = s := by asimp

#axiom_clean substSubst_term
#axiom_clean beta_cancel

end Prelude.Unscoped

namespace Prelude.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  term where
    | C   : Bool → term
    | lam : (bind term in term) → term
    | app : term → term → term

theorem identity {n} (s : term n) : subst_term term.var_term s = s := by asimp
theorem beta_cancel {n} (t s : term n) :
    subst_term (scons t term.var_term) (ren_term shift s) = s := by asimp

#axiom_clean substSubst_term
#axiom_clean beta_cancel

end Prelude.Scoped

/-! ## Lowercase / instance-less foreign types.

An external head can be **any** identifier that is not a declared sort (case-insensitive), including
a lowercase user type. And it need not have `Repr`/`DecidableEq`: those convenience instances are
derived best-effort, so a foreign field type that lacks them (here `tok`, which has a function
field) does not block generation. -/
namespace Foreign
open Autosubst

structure tok where mk :: (run : Nat → Nat)        -- lowercase, no Repr / no DecidableEq

autosubst
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm
    | lit : tok → tm                                -- lowercase, instance-less foreign field

example : tok → tm := tm.lit

theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem lit_stable (σ : Nat → tm) (c : tok) : subst_tm σ (tm.lit c) = tm.lit c := rfl
theorem beta_cancel (t s : tm) : subst_tm (scons t tm.var_tm) (ren_tm shift s) = s := by asimp

#axiom_clean substSubst_tm
#axiom_clean beta_cancel

end Foreign
