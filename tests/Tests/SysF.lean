/-
# Reference signature: `sysf.sig` — System F (multi-sorted, parallel substitution).

    ty : Type ; tm : Type
    arr  : ty → ty → ty ;          all  : (bind ty in ty) → ty
    app  : tm → tm → tm ;          tapp : tm → ty → tm
    lam  : ty → (bind tm in tm) → tm ;   tlam : (bind ty in tm) → tm

`tm` carries **both** `ty`- and `tm`-variables, so `subst_tm` threads two maps in parallel — the
central multi-sort case. Hierarchical (not mutual): `ty` is its own component, `tm` depends on it.
Both backends; scoped `tm` is doubly scope-indexed (`tm : Nat → Nat → Type`).
-/
import Tests.Support

/-! ## Unscoped -/
namespace SysF.Unscoped
open Autosubst

autosubst
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

@[reducible] def instTm (t : tm) : Nat → tm := scons t tm.var_tm
@[reducible] def instTy (T : ty) : Nat → ty := scons T ty.var_ty

-- `ty` substitution (single map).
theorem ty_identity (s : ty) : subst_ty ty.var_ty s = s := by asimp
theorem ty_fusion (σ τ : Nat → ty) (s : ty) :
    subst_ty τ (subst_ty σ s) = subst_ty (funcomp (subst_ty τ) σ) s := by asimp

-- `tm` substitution (two parallel maps).
theorem tm_identity (s : tm) : subst_tm ty.var_ty tm.var_tm s = s := by asimp
theorem tm_fusion (σty τty : Nat → ty) (σtm τtm : Nat → tm) (s : tm) :
    subst_tm τty τtm (subst_tm σty σtm s)
      = subst_tm (funcomp (subst_ty τty) σty) (funcomp (subst_tm τty τtm) σtm) s := by asimp
-- Type β and term β.
theorem ty_beta (T : ty) (s : tm) :
    subst_tm (instTy T) tm.var_tm (ren_tm shift id s) = s := by asimp
theorem tm_beta (t s : tm) :
    subst_tm ty.var_ty (instTm t) (ren_tm id shift s) = s := by asimp
-- Multi-sorted substitution lemma (parallel σ commutes past a term-variable instantiation).
theorem subst_lemma (σty : Nat → ty) (σtm : Nat → tm) (t s : tm) :
    subst_tm σty σtm (subst_tm ty.var_ty (instTm t) s)
      = subst_tm ty.var_ty (instTm (subst_tm σty σtm t))
          (subst_tm (up_tm_ty σty) (up_tm_tm σtm) s) := by asimp

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean tm_fusion
#axiom_clean subst_lemma

end SysF.Unscoped

/-! ## Well-scoped -/
namespace SysF.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

theorem tm_identity {m_ty m_tm} (s : tm m_ty m_tm) :
    subst_tm ty.var_ty tm.var_tm s = s := by asimp
theorem tm_fusion (στy : Fin m_ty → ty n_ty) (στm : Fin m_tm → tm n_ty n_tm)
    (τty : Fin n_ty → ty k_ty) (τtm : Fin n_tm → tm k_ty k_tm) (s : tm m_ty m_tm) :
    subst_tm τty τtm (subst_tm στy στm s)
      = subst_tm (funcomp (subst_ty τty) στy) (funcomp (subst_tm τty τtm) στm) s := by asimp
theorem ty_beta {n_ty n_tm} (s : tm n_ty n_tm) (T : ty n_ty) :
    subst_tm (scons T ty.var_ty) tm.var_tm (ren_tm shift id s) = s := by asimp
theorem tm_beta {n_ty n_tm} (s t : tm n_ty n_tm) :
    subst_tm ty.var_ty (scons t tm.var_tm) (ren_tm id shift s) = s := by asimp

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean tm_fusion
#axiom_clean tm_beta

end SysF.Scoped
