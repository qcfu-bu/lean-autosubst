/-
# Example: well-scoped System F via `autosubst wellscoped`, with `asimp`.

The multi-sort scoped counterpart of [SysfDsl.lean](SysfDsl.lean): `tm` carries both `ty`- and
`tm`-variables, so it is doubly scope-indexed (`tm : Nat → Nat → Type`) and `ren`/`subst` thread
two `Fin`-maps in parallel — matching [SysFScoped.lean](SysFScoped.lean).
-/
import LeanAutosubst

open Autosubst Autosubst.Scoped

namespace SysfScopedDsl

autosubst wellscoped
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

-- Generated scope-indexed signatures.
section
  variable {n_ty n_tm : Nat}
  example : Fin n_ty → ty n_ty := ty.var_ty
  example : Fin n_tm → tm n_ty n_tm := tm.var_tm
  example : tm (n_ty + 1) n_tm → tm n_ty n_tm := tm.tlam
  example : ty n_ty → tm n_ty (n_tm + 1) → tm n_ty n_tm := tm.lam
  example {m_ty m_tm : Nat} :
    (Fin m_ty → ty n_ty) → (Fin m_tm → tm n_ty n_tm) → tm m_ty m_tm → tm n_ty n_tm := subst_tm
end

/-! ## Parallel substitution algebra closes with `asimp`. -/

example {m_ty m_tm} (s : tm m_ty m_tm) :
    subst_tm ty.var_ty tm.var_tm s = s := by asimp

example (στy : Fin m_ty → ty n_ty) (στm : Fin m_tm → tm n_ty n_tm)
    (τty : Fin n_ty → ty k_ty) (τtm : Fin n_tm → tm k_ty k_tm) (s : tm m_ty m_tm) :
    subst_tm τty τtm (subst_tm στy στm s)
      = subst_tm (funcomp (subst_ty τty) στy) (funcomp (subst_tm τty τtm) στm) s := by asimp

-- A `ty`-substitution under `tlam` leaves a `ty`-shifted term untouched.
example {n_ty n_tm} (s : tm n_ty n_tm) (T : ty n_ty) :
    subst_tm (scons T ty.var_ty) tm.var_tm (ren_tm shift id s) = s := by asimp

-- A `tm`-substitution under `lam` leaves a `tm`-shifted term untouched.
example {n_ty n_tm} (s t : tm n_ty n_tm) :
    subst_tm ty.var_ty (scons t tm.var_tm) (ren_tm id shift s) = s := by asimp

-- Two parallel renamings fuse.
example (ξty : Fin m_ty → Fin n_ty) (ξtm : Fin m_tm → Fin n_tm)
    (ζty : Fin n_ty → Fin k_ty) (ζtm : Fin n_tm → Fin k_tm) (s : tm m_ty m_tm) :
    ren_tm ζty ζtm (ren_tm ξty ξtm s) = ren_tm (funcomp ζty ξty) (funcomp ζtm ξtm) s := by asimp

end SysfScopedDsl
