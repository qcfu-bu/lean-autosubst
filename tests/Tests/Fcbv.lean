/-
# Reference signature: `fcbv.sig` — call-by-value System F (genuinely **mutual** sorts).

    ty : Type ; tm : Type ; vl : Type
    arr  : ty → ty → ty ;            all  : (bind ty in ty) → ty
    app  : tm → tm → tm ;  tapp : tm → ty → tm ;  vt : vl → tm
    lam  : ty → (bind vl in tm) → vl ;            tlam : (bind ty in tm) → vl

`tm` and `vl` are **mutually recursive** (`tm` has `vt : vl → tm`; `vl`'s `lam` binds a `vl` in a
`tm` body), so they form one SCC `[tm, vl]` and the whole lemma tower for them is emitted as a
single `mutual … end` block — the case that distinguishes a real mutual signature from System F's
hierarchical one. `tm` is *not* open (no constructor binds `tm`); both `tm` and `vl` carry `ty`- and
`vl`-variables, so each threads two maps. Both backends.
-/
import Tests.Support

/-! ## Unscoped -/
namespace Fcbv.Unscoped
open Autosubst

autosubst
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | vt   : vl → tm
  vl where
    | lam  : ty → (bind vl in tm) → vl
    | tlam : (bind ty in tm) → vl

-- Substitution vectors: `tm`/`vl` thread `[ty, vl]` (no `tm`-variables); `tm` has no `var`.
example : (Nat → ty) → (Nat → vl) → tm → tm := subst_tm
example : (Nat → ty) → (Nat → vl) → vl → vl := subst_vl
example : Nat → vl := vl.var_vl

theorem tm_identity (s : tm) : subst_tm ty.var_ty vl.var_vl s = s := by asimp
theorem vl_identity (s : vl) : subst_vl ty.var_ty vl.var_vl s = s := by asimp
-- Mutual fusion — exercises `compSubstSubst_vl` mutually-recursive with `compSubstSubst_tm`.
theorem vl_fusion (σty τty : Nat → ty) (σvl τvl : Nat → vl) (s : vl) :
    subst_vl τty τvl (subst_vl σty σvl s)
      = subst_vl (funcomp (subst_ty τty) σty) (funcomp (subst_vl τty τvl) σvl) s := by asimp
theorem tm_fusion (σty τty : Nat → ty) (σvl τvl : Nat → vl) (s : tm) :
    subst_tm τty τvl (subst_tm σty σvl s)
      = subst_tm (funcomp (subst_ty τty) σty) (funcomp (subst_vl τty τvl) σvl) s := by asimp
-- `vl`-β (under `lam`, which binds a `vl`): weaken the `vl`-component, instantiate the fresh var.
theorem vl_beta (v s : vl) :
    subst_vl ty.var_ty (scons v vl.var_vl) (ren_vl id shift s) = s := by asimp
-- `ty`-β (under `tlam`, which binds a `ty`): weaken the `ty`-component, instantiate it.
theorem ty_beta (T : ty) (s : tm) :
    subst_tm (scons T ty.var_ty) vl.var_vl (ren_tm shift id s) = s := by asimp

#axiom_clean substSubst_tm
#axiom_clean substSubst_vl
#axiom_clean compSubstSubst_tm
#axiom_clean compSubstSubst_vl
#axiom_clean instId_vl
#axiom_clean vl_fusion
#axiom_clean vl_beta

end Fcbv.Unscoped

/-! ## Well-scoped — `tm`/`vl` are doubly scope-indexed (by `ty`- and `vl`-scopes). -/
namespace Fcbv.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | vt   : vl → tm
  vl where
    | lam  : ty → (bind vl in tm) → vl
    | tlam : (bind ty in tm) → vl

theorem tm_identity {n_ty n_vl} (s : tm n_ty n_vl) :
    subst_tm ty.var_ty vl.var_vl s = s := by asimp
theorem vl_identity {n_ty n_vl} (s : vl n_ty n_vl) :
    subst_vl ty.var_ty vl.var_vl s = s := by asimp
theorem vl_fusion (σty : Fin m_ty → ty n_ty) (σvl : Fin m_vl → vl n_ty n_vl)
    (τty : Fin n_ty → ty k_ty) (τvl : Fin n_vl → vl k_ty k_vl) (s : vl m_ty m_vl) :
    subst_vl τty τvl (subst_vl σty σvl s)
      = subst_vl (funcomp (subst_ty τty) σty) (funcomp (subst_vl τty τvl) σvl) s := by asimp

#axiom_clean substSubst_vl
#axiom_clean compSubstSubst_tm
#axiom_clean compSubstSubst_vl
#axiom_clean vl_fusion

end Fcbv.Scoped
