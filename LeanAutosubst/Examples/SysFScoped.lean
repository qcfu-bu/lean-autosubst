/-
# Phase 8 — Multi-sort well-scoped golden: System F, `Fin`-indexed, by hand.

The scoped analogue of [SysF.lean](SysF.lean), and the multi-sort companion to
[StlcScoped.lean](StlcScoped.lean). Same signature (rocq/autosubst2-ocaml/signatures/sysf.sig)
but every substitution sort is scope-indexed:

  • `ty : Nat → Type`      (one variable sort: `[ty]`)        — `ren_ty`/`subst_ty` take ONE map.
  • `tm : Nat → Nat → Type` (two variable sorts: `[ty, tm]`)  — `ren_tm`/`subst_tm` take TWO maps,
    threaded in parallel; the whole `up*`/`comp*` tower is indexed by (binder-sort, component-sort)
    pairs `up_ty_ty`/`up_ty_tm`/`up_tm_ty`/`up_tm_tm`.

The genuinely new scoped multi-sort phenomena validated here:
  • the double index `tm n_ty n_tm`;
  • cross-sort up-helpers whose *domain scope does not increment* — a `ty`-binder adds no
    `tm`-variable, so `up_ty_tm σ = (ren_tm shift id) ∘ σ : Fin m → tm (n_ty+1) n_tm` (no `scons`),
    and dually `up_tm_ty σ = (ren_ty id) ∘ σ`.

Variable backend: Lean's core `Fin n` (`Autosubst.Scoped`). The `Nat` `0`/`n+1` case split
becomes `Fin.cases` (which reduces definitionally on `0`/`Fin.succ i`). Done = typechecks; no
`sorry`; axioms ⊆ `{propext, Quot.sound}`.
-/
import LeanAutosubst.Prelude.Scoped

namespace Autosubst.SysFScoped
open Autosubst Autosubst.Scoped

/-! ## Sort `ty` (substitution vector `[ty]`) -/

inductive ty : Nat → Type where
  | var_ty : {n : Nat} → Fin n → ty n
  | arr    : {n : Nat} → ty n → ty n → ty n
  | all    : {n : Nat} → ty (n + 1) → ty n

open ty

theorem congr_arr {n} {s0 s1 t0 t1 : ty n} (h0 : s0 = t0) (h1 : s1 = t1) :
    arr s0 s1 = arr t0 t1 := by rw [h0, h1]

theorem congr_all {n} {s0 t0 : ty (n + 1)} (h0 : s0 = t0) : all s0 = all t0 := by rw [h0]

@[reducible] def upRen_ty_ty {m n} (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) := up_ren xi

def ren_ty {m n} (xi_ty : Fin m → Fin n) : ty m → ty n
  | var_ty s0 => var_ty (xi_ty s0)
  | arr s0 s1 => arr (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | all s0    => all (ren_ty (upRen_ty_ty xi_ty) s0)

@[reducible] def up_ty_ty {m n} (sigma : Fin m → ty n) : Fin (m + 1) → ty (n + 1) :=
  scons (var_ty var_zero) (funcomp (ren_ty shift) sigma)

def subst_ty {m n} (sigma_ty : Fin m → ty n) : ty m → ty n
  | var_ty s0 => sigma_ty s0
  | arr s0 s1 => arr (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | all s0    => all (subst_ty (up_ty_ty sigma_ty) s0)

theorem upId_ty_ty {m} (sigma : Fin m → ty m) (h : ∀ x, sigma x = var_ty x) :
    ∀ x, up_ty_ty sigma x = var_ty x :=
  Fin.cases rfl (fun i => congrArg (ren_ty shift) (h i))

theorem idSubst_ty {m} (sigma_ty : Fin m → ty m) (h : ∀ x, sigma_ty x = var_ty x) :
    ∀ s, subst_ty sigma_ty s = s
  | var_ty s0 => h s0
  | arr s0 s1 => congr_arr (idSubst_ty sigma_ty h s0) (idSubst_ty sigma_ty h s1)
  | all s0    => congr_all (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ h) s0)

theorem upExtRen_ty_ty {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_ty_ty xi x = upRen_ty_ty zeta x :=
  Fin.cases rfl (fun i => congrArg shift (h i))

theorem extRen_ty {m n} (xi_ty zeta_ty : Fin m → Fin n) (h : ∀ x, xi_ty x = zeta_ty x) :
    ∀ s, ren_ty xi_ty s = ren_ty zeta_ty s
  | var_ty s0 => congrArg var_ty (h s0)
  | arr s0 s1 => congr_arr (extRen_ty xi_ty zeta_ty h s0) (extRen_ty xi_ty zeta_ty h s1)
  | all s0    => congr_all (extRen_ty _ _ (upExtRen_ty_ty _ _ h) s0)

theorem upExt_ty_ty {m n} (sigma tau : Fin m → ty n) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_ty_ty sigma x = up_ty_ty tau x :=
  Fin.cases rfl (fun i => congrArg (ren_ty shift) (h i))

theorem ext_ty {m n} (sigma_ty tau_ty : Fin m → ty n) (h : ∀ x, sigma_ty x = tau_ty x) :
    ∀ s, subst_ty sigma_ty s = subst_ty tau_ty s
  | var_ty s0 => h s0
  | arr s0 s1 => congr_arr (ext_ty sigma_ty tau_ty h s0) (ext_ty sigma_ty tau_ty h s1)
  | all s0    => congr_all (ext_ty _ _ (upExt_ty_ty _ _ h) s0)

theorem up_ren_ren_ty_ty {k l m} (xi : Fin k → Fin l) (zeta : Fin l → Fin m)
    (rho : Fin k → Fin m) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x :=
  up_ren_ren xi zeta rho h

theorem compRenRen_ty {k l m} (xi_ty : Fin m → Fin k) (zeta_ty : Fin k → Fin l)
    (rho_ty : Fin m → Fin l) (h_ty : ∀ x, funcomp zeta_ty xi_ty x = rho_ty x) :
    ∀ s, ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s
  | var_ty s0 => congrArg var_ty (h_ty s0)
  | arr s0 s1 => congr_arr (compRenRen_ty xi_ty zeta_ty rho_ty h_ty s0)
                           (compRenRen_ty xi_ty zeta_ty rho_ty h_ty s1)
  | all s0    => congr_all (compRenRen_ty _ _ _ (up_ren_ren _ _ _ h_ty) s0)

theorem up_ren_subst_ty_ty {k l m} (xi : Fin k → Fin l) (tau : Fin l → ty m)
    (theta : Fin k → ty m) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x :=
  Fin.cases rfl (fun i => congrArg (ren_ty shift) (h i))

theorem compRenSubst_ty {k l m} (xi_ty : Fin m → Fin k) (tau_ty : Fin k → ty l)
    (theta_ty : Fin m → ty l) (h_ty : ∀ x, funcomp tau_ty xi_ty x = theta_ty x) :
    ∀ s, subst_ty tau_ty (ren_ty xi_ty s) = subst_ty theta_ty s
  | var_ty s0 => h_ty s0
  | arr s0 s1 => congr_arr (compRenSubst_ty xi_ty tau_ty theta_ty h_ty s0)
                           (compRenSubst_ty xi_ty tau_ty theta_ty h_ty s1)
  | all s0    => congr_all (compRenSubst_ty _ _ _ (up_ren_subst_ty_ty _ _ _ h_ty) s0)

theorem up_subst_ren_ty_ty {k l m} (sigma : Fin k → ty l) (zeta_ty : Fin l → Fin m)
    (theta : Fin k → ty m) (h : ∀ x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
    ∀ x, funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x = up_ty_ty theta x :=
  Fin.cases rfl (fun i =>
    (compRenRen_ty shift (upRen_ty_ty zeta_ty) (funcomp shift zeta_ty) (fun _ => rfl) (sigma i)).trans
      (((compRenRen_ty zeta_ty shift (funcomp shift zeta_ty) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_ty shift) (h i))))

theorem compSubstRen_ty {k l m} (sigma_ty : Fin m → ty k) (zeta_ty : Fin k → Fin l)
    (theta_ty : Fin m → ty l) (h_ty : ∀ x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x) :
    ∀ s, ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s
  | var_ty s0 => h_ty s0
  | arr s0 s1 => congr_arr (compSubstRen_ty sigma_ty zeta_ty theta_ty h_ty s0)
                           (compSubstRen_ty sigma_ty zeta_ty theta_ty h_ty s1)
  | all s0    => congr_all (compSubstRen_ty _ _ _ (up_subst_ren_ty_ty _ _ _ h_ty) s0)

theorem up_subst_subst_ty_ty {k l m} (sigma : Fin k → ty l) (tau_ty : Fin l → ty m)
    (theta : Fin k → ty m) (h : ∀ x, funcomp (subst_ty tau_ty) sigma x = theta x) :
    ∀ x, funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x :=
  Fin.cases rfl (fun i =>
    (compRenSubst_ty shift (up_ty_ty tau_ty) (funcomp (up_ty_ty tau_ty) shift) (fun _ => rfl) (sigma i)).trans
      (((compSubstRen_ty tau_ty shift (funcomp (ren_ty shift) tau_ty) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_ty shift) (h i))))

theorem compSubstSubst_ty {k l m} (sigma_ty : Fin m → ty k) (tau_ty : Fin k → ty l)
    (theta_ty : Fin m → ty l) (h_ty : ∀ x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x) :
    ∀ s, subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s
  | var_ty s0 => h_ty s0
  | arr s0 s1 => congr_arr (compSubstSubst_ty sigma_ty tau_ty theta_ty h_ty s0)
                           (compSubstSubst_ty sigma_ty tau_ty theta_ty h_ty s1)
  | all s0    => congr_all (compSubstSubst_ty _ _ _ (up_subst_subst_ty_ty _ _ _ h_ty) s0)

theorem rinstInst_up_ty_ty {m n} (xi : Fin m → Fin n) (sigma : Fin m → ty n)
    (h : ∀ x, funcomp var_ty xi x = sigma x) :
    ∀ x, funcomp var_ty (upRen_ty_ty xi) x = up_ty_ty sigma x :=
  Fin.cases rfl (fun i => congrArg (ren_ty shift) (h i))

theorem rinst_inst_ty {m n} (xi_ty : Fin m → Fin n) (sigma_ty : Fin m → ty n)
    (h_ty : ∀ x, funcomp var_ty xi_ty x = sigma_ty x) :
    ∀ s, ren_ty xi_ty s = subst_ty sigma_ty s
  | var_ty s0 => h_ty s0
  | arr s0 s1 => congr_arr (rinst_inst_ty xi_ty sigma_ty h_ty s0)
                           (rinst_inst_ty xi_ty sigma_ty h_ty s1)
  | all s0    => congr_all (rinst_inst_ty _ _ (rinstInst_up_ty_ty _ _ h_ty) s0)

/-! ### `ty` clean (funext-based) wrappers -/

theorem renRen_ty {k l m} (xi_ty : Fin m → Fin k) (zeta_ty : Fin k → Fin l) (s : ty m) :
    ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s :=
  compRenRen_ty xi_ty zeta_ty _ (fun _ => rfl) s

theorem renRen'_ty {k l m} (xi_ty : Fin m → Fin k) (zeta_ty : Fin k → Fin l) :
    funcomp (ren_ty zeta_ty) (ren_ty xi_ty) = ren_ty (funcomp zeta_ty xi_ty) :=
  funext (renRen_ty xi_ty zeta_ty)

theorem renSubst_ty {k l m} (xi_ty : Fin m → Fin k) (tau_ty : Fin k → ty l) (s : ty m) :
    subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s :=
  compRenSubst_ty xi_ty tau_ty _ (fun _ => rfl) s

theorem substRen_ty {k l m} (sigma_ty : Fin m → ty k) (zeta_ty : Fin k → Fin l) (s : ty m) :
    ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s :=
  compSubstRen_ty sigma_ty zeta_ty _ (fun _ => rfl) s

theorem substSubst_ty {k l m} (sigma_ty : Fin m → ty k) (tau_ty : Fin k → ty l) (s : ty m) :
    subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s :=
  compSubstSubst_ty sigma_ty tau_ty _ (fun _ => rfl) s

theorem substSubst'_ty {k l m} (sigma_ty : Fin m → ty k) (tau_ty : Fin k → ty l) :
    funcomp (subst_ty tau_ty) (subst_ty sigma_ty) = subst_ty (funcomp (subst_ty tau_ty) sigma_ty) :=
  funext (substSubst_ty sigma_ty tau_ty)

theorem rinstInst'_ty {m n} (xi_ty : Fin m → Fin n) (s : ty m) :
    ren_ty xi_ty s = subst_ty (funcomp var_ty xi_ty) s :=
  rinst_inst_ty xi_ty _ (fun _ => rfl) s

theorem rinstInst_ty {m n} (xi_ty : Fin m → Fin n) :
    ren_ty xi_ty = subst_ty (funcomp var_ty xi_ty) :=
  funext (rinstInst'_ty xi_ty)

theorem instId'_ty {m} (s : ty m) : subst_ty var_ty s = s :=
  idSubst_ty var_ty (fun _ => rfl) s

theorem instId_ty {m} : subst_ty (@var_ty m) = id := funext instId'_ty

theorem rinstId'_ty {m} (s : ty m) : ren_ty id s = s :=
  (rinstInst'_ty id s).trans (instId'_ty s)

theorem rinstId_ty {m} : @ren_ty m m id = id := funext rinstId'_ty

theorem varL_ty {m n} (sigma_ty : Fin m → ty n) :
    funcomp (subst_ty sigma_ty) var_ty = sigma_ty := rfl

theorem varLRen_ty {m n} (xi_ty : Fin m → Fin n) :
    funcomp (ren_ty xi_ty) var_ty = funcomp var_ty xi_ty := rfl

/-! ## Sort `tm` (substitution vector `[ty, tm]`) — the multi-sorted core -/

inductive tm : Nat → Nat → Type where
  | var_tm : {n_ty n_tm : Nat} → Fin n_tm → tm n_ty n_tm
  | app    : {n_ty n_tm : Nat} → tm n_ty n_tm → tm n_ty n_tm → tm n_ty n_tm
  | tapp   : {n_ty n_tm : Nat} → tm n_ty n_tm → ty n_ty → tm n_ty n_tm
  | lam    : {n_ty n_tm : Nat} → ty n_ty → tm n_ty (n_tm + 1) → tm n_ty n_tm
  | tlam   : {n_ty n_tm : Nat} → tm (n_ty + 1) n_tm → tm n_ty n_tm

open tm

theorem congr_app {n_ty n_tm} {s0 s1 t0 t1 : tm n_ty n_tm} (h0 : s0 = t0) (h1 : s1 = t1) :
    app s0 s1 = app t0 t1 := by rw [h0, h1]

theorem congr_tapp {n_ty n_tm} {s0 t0 : tm n_ty n_tm} {s1 t1 : ty n_ty}
    (h0 : s0 = t0) (h1 : s1 = t1) : tapp s0 s1 = tapp t0 t1 := by rw [h0, h1]

theorem congr_lam {n_ty n_tm} {s0 t0 : ty n_ty} {s1 t1 : tm n_ty (n_tm + 1)}
    (h0 : s0 = t0) (h1 : s1 = t1) : lam s0 s1 = lam t0 t1 := by rw [h0, h1]

theorem congr_tlam {n_ty n_tm} {s0 t0 : tm (n_ty + 1) n_tm} (h0 : s0 = t0) :
    tlam s0 = tlam t0 := by rw [h0]

/-- Lift a `tm`-renaming under a `ty`-binder: identity (a `ty`-binder adds no `tm`-variable). -/
@[reducible] def upRen_ty_tm {m n} (xi : Fin m → Fin n) : Fin m → Fin n := xi
/-- Lift a `ty`-renaming under a `tm`-binder: identity. -/
@[reducible] def upRen_tm_ty {m n} (xi : Fin m → Fin n) : Fin m → Fin n := xi
/-- Lift a `tm`-renaming under a `tm`-binder. -/
@[reducible] def upRen_tm_tm {m n} (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) := up_ren xi

def ren_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm) :
    tm m_ty m_tm → tm n_ty n_tm
  | var_tm s0  => var_tm (xi_tm s0)
  | app s0 s1  => app (ren_tm xi_ty xi_tm s0) (ren_tm xi_ty xi_tm s1)
  | tapp s0 s1 => tapp (ren_tm xi_ty xi_tm s0) (ren_ty xi_ty s1)
  | lam s0 s1  => lam (ren_ty xi_ty s0) (ren_tm (upRen_tm_ty xi_ty) (upRen_tm_tm xi_tm) s1)
  | tlam s0    => tlam (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_tm xi_tm) s0)

/-- Lift a `tm`-substitution under a `ty`-binder: rename codomain by `ren_tm shift id` (no `scons`). -/
@[reducible] def up_ty_tm {m n_ty n_tm} (sigma : Fin m → tm n_ty n_tm) :
    Fin m → tm (n_ty + 1) n_tm := funcomp (ren_tm shift id) sigma
/-- Lift a `ty`-substitution under a `tm`-binder: rename codomain by `ren_ty id`. -/
@[reducible] def up_tm_ty {m n_ty} (sigma : Fin m → ty n_ty) : Fin m → ty n_ty :=
  funcomp (ren_ty id) sigma
/-- Lift a `tm`-substitution under a `tm`-binder. -/
@[reducible] def up_tm_tm {m n_ty n_tm} (sigma : Fin m → tm n_ty n_tm) :
    Fin (m + 1) → tm n_ty (n_tm + 1) :=
  scons (var_tm var_zero) (funcomp (ren_tm id shift) sigma)

def subst_tm {m_ty m_tm n_ty n_tm} (sigma_ty : Fin m_ty → ty n_ty)
    (sigma_tm : Fin m_tm → tm n_ty n_tm) : tm m_ty m_tm → tm n_ty n_tm
  | var_tm s0  => sigma_tm s0
  | app s0 s1  => app (subst_tm sigma_ty sigma_tm s0) (subst_tm sigma_ty sigma_tm s1)
  | tapp s0 s1 => tapp (subst_tm sigma_ty sigma_tm s0) (subst_ty sigma_ty s1)
  | lam s0 s1  => lam (subst_ty sigma_ty s0) (subst_tm (up_tm_ty sigma_ty) (up_tm_tm sigma_tm) s1)
  | tlam s0    => tlam (subst_tm (up_ty_ty sigma_ty) (up_ty_tm sigma_tm) s0)

/-! ### `subst id = id` -/

theorem upId_ty_tm {m_ty m_tm} (sigma : Fin m_tm → tm m_ty m_tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ x, up_ty_tm sigma x = var_tm x :=
  fun x => congrArg (ren_tm shift id) (h x)

theorem upId_tm_ty {m_ty} (sigma : Fin m_ty → ty m_ty) (h : ∀ x, sigma x = var_ty x) :
    ∀ x, up_tm_ty sigma x = var_ty x :=
  fun x => congrArg (ren_ty id) (h x)

theorem upId_tm_tm {m_ty m_tm} (sigma : Fin m_tm → tm m_ty m_tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ x, up_tm_tm sigma x = var_tm x :=
  Fin.cases rfl (fun i => congrArg (ren_tm id shift) (h i))

theorem idSubst_tm {m_ty m_tm} (sigma_ty : Fin m_ty → ty m_ty) (sigma_tm : Fin m_tm → tm m_ty m_tm)
    (h_ty : ∀ x, sigma_ty x = var_ty x) (h_tm : ∀ x, sigma_tm x = var_tm x) :
    ∀ s, subst_tm sigma_ty sigma_tm s = s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (idSubst_tm sigma_ty sigma_tm h_ty h_tm s0)
                            (idSubst_tm sigma_ty sigma_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (idSubst_tm sigma_ty sigma_tm h_ty h_tm s0)
                             (idSubst_ty sigma_ty h_ty s1)
  | lam s0 s1  => congr_lam (idSubst_ty sigma_ty h_ty s0)
                            (idSubst_tm _ _ (upId_tm_ty _ h_ty) (upId_tm_tm _ h_tm) s1)
  | tlam s0    => congr_tlam (idSubst_tm _ _ (upId_ty_ty _ h_ty) (upId_ty_tm _ h_tm) s0)

/-! ### Extensionality -/

theorem upExtRen_ty_tm {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_ty_tm xi x = upRen_ty_tm zeta x := h

theorem upExtRen_tm_ty {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_tm_ty xi x = upRen_tm_ty zeta x := h

theorem upExtRen_tm_tm {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  Fin.cases rfl (fun i => congrArg shift (h i))

theorem extRen_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm)
    (zeta_ty : Fin m_ty → Fin n_ty) (zeta_tm : Fin m_tm → Fin n_tm)
    (h_ty : ∀ x, xi_ty x = zeta_ty x) (h_tm : ∀ x, xi_tm x = zeta_tm x) :
    ∀ s, ren_tm xi_ty xi_tm s = ren_tm zeta_ty zeta_tm s
  | var_tm s0  => congrArg var_tm (h_tm s0)
  | app s0 s1  => congr_app (extRen_tm xi_ty xi_tm zeta_ty zeta_tm h_ty h_tm s0)
                            (extRen_tm xi_ty xi_tm zeta_ty zeta_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (extRen_tm xi_ty xi_tm zeta_ty zeta_tm h_ty h_tm s0)
                             (extRen_ty xi_ty zeta_ty h_ty s1)
  | lam s0 s1  => congr_lam (extRen_ty xi_ty zeta_ty h_ty s0)
                            (extRen_tm _ _ _ _ (upExtRen_tm_ty _ _ h_ty) (upExtRen_tm_tm _ _ h_tm) s1)
  | tlam s0    => congr_tlam (extRen_tm _ _ _ _ (upExtRen_ty_ty _ _ h_ty) (upExtRen_ty_tm _ _ h_tm) s0)

theorem upExt_ty_tm {m n_ty n_tm} (sigma tau : Fin m → tm n_ty n_tm) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_ty_tm sigma x = up_ty_tm tau x :=
  fun x => congrArg (ren_tm shift id) (h x)

theorem upExt_tm_ty {m n_ty} (sigma tau : Fin m → ty n_ty) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_tm_ty sigma x = up_tm_ty tau x :=
  fun x => congrArg (ren_ty id) (h x)

theorem upExt_tm_tm {m n_ty n_tm} (sigma tau : Fin m → tm n_ty n_tm) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_tm_tm sigma x = up_tm_tm tau x :=
  Fin.cases rfl (fun i => congrArg (ren_tm id shift) (h i))

theorem ext_tm {m_ty m_tm n_ty n_tm} (sigma_ty : Fin m_ty → ty n_ty) (sigma_tm : Fin m_tm → tm n_ty n_tm)
    (tau_ty : Fin m_ty → ty n_ty) (tau_tm : Fin m_tm → tm n_ty n_tm)
    (h_ty : ∀ x, sigma_ty x = tau_ty x) (h_tm : ∀ x, sigma_tm x = tau_tm x) :
    ∀ s, subst_tm sigma_ty sigma_tm s = subst_tm tau_ty tau_tm s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (ext_tm sigma_ty sigma_tm tau_ty tau_tm h_ty h_tm s0)
                            (ext_tm sigma_ty sigma_tm tau_ty tau_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (ext_tm sigma_ty sigma_tm tau_ty tau_tm h_ty h_tm s0)
                             (ext_ty sigma_ty tau_ty h_ty s1)
  | lam s0 s1  => congr_lam (ext_ty sigma_ty tau_ty h_ty s0)
                            (ext_tm _ _ _ _ (upExt_tm_ty _ _ h_ty) (upExt_tm_tm _ _ h_tm) s1)
  | tlam s0    => congr_tlam (ext_tm _ _ _ _ (upExt_ty_ty _ _ h_ty) (upExt_ty_tm _ _ h_tm) s0)

/-! ### Compositionality: ren ∘ ren -/

theorem up_ren_ren_tm_tm {k l m} (xi : Fin k → Fin l) (zeta : Fin l → Fin m)
    (rho : Fin k → Fin m) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho h

theorem compRenRen_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (xi_ty : Fin m_ty → Fin k_ty) (xi_tm : Fin m_tm → Fin k_tm)
    (zeta_ty : Fin k_ty → Fin l_ty) (zeta_tm : Fin k_tm → Fin l_tm)
    (rho_ty : Fin m_ty → Fin l_ty) (rho_tm : Fin m_tm → Fin l_tm)
    (h_ty : ∀ x, funcomp zeta_ty xi_ty x = rho_ty x)
    (h_tm : ∀ x, funcomp zeta_tm xi_tm x = rho_tm x) :
    ∀ s, ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s) = ren_tm rho_ty rho_tm s
  | var_tm s0  => congrArg var_tm (h_tm s0)
  | app s0 s1  => congr_app (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm h_ty h_tm s0)
                            (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm rho_ty rho_tm h_ty h_tm s0)
                             (compRenRen_ty xi_ty zeta_ty rho_ty h_ty s1)
  | lam s0 s1  => congr_lam (compRenRen_ty xi_ty zeta_ty rho_ty h_ty s0)
                            (compRenRen_tm _ _ _ _ _ _ h_ty (up_ren_ren _ _ _ h_tm) s1)
  | tlam s0    => congr_tlam (compRenRen_tm _ _ _ _ _ _ (up_ren_ren _ _ _ h_ty) h_tm s0)

/-! ### Compositionality: subst ∘ ren -/

theorem up_ren_subst_ty_tm {k l m_ty m_tm} (xi : Fin k → Fin l) (tau : Fin l → tm m_ty m_tm)
    (theta : Fin k → tm m_ty m_tm) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_ty_tm tau) (upRen_ty_tm xi) x = up_ty_tm theta x :=
  fun x => congrArg (ren_tm shift id) (h x)

theorem up_ren_subst_tm_ty {k l m_ty} (xi : Fin k → Fin l) (tau : Fin l → ty m_ty)
    (theta : Fin k → ty m_ty) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_tm_ty tau) (upRen_tm_ty xi) x = up_tm_ty theta x :=
  fun x => congrArg (ren_ty id) (h x)

theorem up_ren_subst_tm_tm {k l m_ty m_tm} (xi : Fin k → Fin l) (tau : Fin l → tm m_ty m_tm)
    (theta : Fin k → tm m_ty m_tm) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  Fin.cases rfl (fun i => congrArg (ren_tm id shift) (h i))

theorem compRenSubst_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (xi_ty : Fin m_ty → Fin k_ty) (xi_tm : Fin m_tm → Fin k_tm)
    (tau_ty : Fin k_ty → ty l_ty) (tau_tm : Fin k_tm → tm l_ty l_tm)
    (theta_ty : Fin m_ty → ty l_ty) (theta_tm : Fin m_tm → tm l_ty l_tm)
    (h_ty : ∀ x, funcomp tau_ty xi_ty x = theta_ty x)
    (h_tm : ∀ x, funcomp tau_tm xi_tm x = theta_tm x) :
    ∀ s, subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s) = subst_tm theta_ty theta_tm s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s0)
                            (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (compRenSubst_tm xi_ty xi_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s0)
                             (compRenSubst_ty xi_ty tau_ty theta_ty h_ty s1)
  | lam s0 s1  => congr_lam (compRenSubst_ty xi_ty tau_ty theta_ty h_ty s0)
                            (compRenSubst_tm _ _ _ _ _ _
                              (up_ren_subst_tm_ty _ _ _ h_ty) (up_ren_subst_tm_tm _ _ _ h_tm) s1)
  | tlam s0    => congr_tlam (compRenSubst_tm _ _ _ _ _ _
                              (up_ren_subst_ty_ty _ _ _ h_ty) (up_ren_subst_ty_tm _ _ _ h_tm) s0)

/-! ### Compositionality: ren ∘ subst -/

theorem up_subst_ren_ty_tm {k l_ty l_tm m_ty m_tm} (sigma : Fin k → tm l_ty l_tm)
    (zeta_ty : Fin l_ty → Fin m_ty) (zeta_tm : Fin l_tm → Fin m_tm) (theta : Fin k → tm m_ty m_tm)
    (h : ∀ x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
    ∀ x, funcomp (ren_tm (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)) (up_ty_tm sigma) x
         = up_ty_tm theta x :=
  fun x =>
    (compRenRen_tm shift id (upRen_ty_ty zeta_ty) (upRen_ty_tm zeta_tm)
        (funcomp shift zeta_ty) (funcomp id zeta_tm) (fun _ => rfl) (fun _ => rfl) (sigma x)).trans
      (((compRenRen_tm zeta_ty zeta_tm shift id (funcomp shift zeta_ty) (funcomp id zeta_tm)
          (fun _ => rfl) (fun _ => rfl) (sigma x)).symm).trans
        (congrArg (ren_tm shift id) (h x)))

theorem up_subst_ren_tm_ty {k l_ty m_ty} (sigma : Fin k → ty l_ty) (zeta_ty : Fin l_ty → Fin m_ty)
    (theta : Fin k → ty m_ty) (h : ∀ x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
    ∀ x, funcomp (ren_ty (upRen_tm_ty zeta_ty)) (up_tm_ty sigma) x = up_tm_ty theta x :=
  fun x =>
    (compRenRen_ty id (upRen_tm_ty zeta_ty) (funcomp id zeta_ty) (fun _ => rfl) (sigma x)).trans
      (((compRenRen_ty zeta_ty id (funcomp id zeta_ty) (fun _ => rfl) (sigma x)).symm).trans
        (congrArg (ren_ty id) (h x)))

theorem up_subst_ren_tm_tm {k l_ty l_tm m_ty m_tm} (sigma : Fin k → tm l_ty l_tm)
    (zeta_ty : Fin l_ty → Fin m_ty) (zeta_tm : Fin l_tm → Fin m_tm) (theta : Fin k → tm m_ty m_tm)
    (h : ∀ x, funcomp (ren_tm zeta_ty zeta_tm) sigma x = theta x) :
    ∀ x, funcomp (ren_tm (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x
         = up_tm_tm theta x :=
  Fin.cases rfl (fun i =>
    (compRenRen_tm id shift (upRen_tm_ty zeta_ty) (upRen_tm_tm zeta_tm)
        (funcomp id zeta_ty) (funcomp shift zeta_tm) (fun _ => rfl) (fun _ => rfl) (sigma i)).trans
      (((compRenRen_tm zeta_ty zeta_tm id shift (funcomp id zeta_ty) (funcomp shift zeta_tm)
          (fun _ => rfl) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_tm id shift) (h i))))

theorem compSubstRen_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (sigma_ty : Fin m_ty → ty k_ty) (sigma_tm : Fin m_tm → tm k_ty k_tm)
    (zeta_ty : Fin k_ty → Fin l_ty) (zeta_tm : Fin k_tm → Fin l_tm)
    (theta_ty : Fin m_ty → ty l_ty) (theta_tm : Fin m_tm → tm l_ty l_tm)
    (h_ty : ∀ x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
    (h_tm : ∀ x, funcomp (ren_tm zeta_ty zeta_tm) sigma_tm x = theta_tm x) :
    ∀ s, ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s) = subst_tm theta_ty theta_tm s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm h_ty h_tm s0)
                            (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm theta_ty theta_tm h_ty h_tm s0)
                             (compSubstRen_ty sigma_ty zeta_ty theta_ty h_ty s1)
  | lam s0 s1  => congr_lam (compSubstRen_ty sigma_ty zeta_ty theta_ty h_ty s0)
                            (compSubstRen_tm _ _ _ _ _ _
                              (up_subst_ren_tm_ty _ _ _ h_ty) (up_subst_ren_tm_tm _ _ _ _ h_tm) s1)
  | tlam s0    => congr_tlam (compSubstRen_tm _ _ _ _ _ _
                              (up_subst_ren_ty_ty _ _ _ h_ty) (up_subst_ren_ty_tm _ _ _ _ h_tm) s0)

/-! ### Compositionality: subst ∘ subst -/

theorem up_subst_subst_ty_tm {k l_ty l_tm m_ty m_tm} (sigma : Fin k → tm l_ty l_tm)
    (tau_ty : Fin l_ty → ty m_ty) (tau_tm : Fin l_tm → tm m_ty m_tm) (theta : Fin k → tm m_ty m_tm)
    (h : ∀ x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
    ∀ x, funcomp (subst_tm (up_ty_ty tau_ty) (up_ty_tm tau_tm)) (up_ty_tm sigma) x
         = up_ty_tm theta x :=
  fun x =>
    (compRenSubst_tm shift id (up_ty_ty tau_ty) (up_ty_tm tau_tm)
        (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_tm tau_tm) id)
        (fun _ => rfl) (fun _ => rfl) (sigma x)).trans
      (((compSubstRen_tm tau_ty tau_tm shift id
          (funcomp (ren_ty shift) tau_ty) (funcomp (ren_tm shift id) tau_tm)
          (fun _ => rfl) (fun _ => rfl) (sigma x)).symm).trans
        (congrArg (ren_tm shift id) (h x)))

theorem up_subst_subst_tm_ty {k l_ty m_ty} (sigma : Fin k → ty l_ty) (tau_ty : Fin l_ty → ty m_ty)
    (theta : Fin k → ty m_ty) (h : ∀ x, funcomp (subst_ty tau_ty) sigma x = theta x) :
    ∀ x, funcomp (subst_ty (up_tm_ty tau_ty)) (up_tm_ty sigma) x = up_tm_ty theta x :=
  fun x =>
    (compRenSubst_ty id (up_tm_ty tau_ty) (funcomp (up_tm_ty tau_ty) id) (fun _ => rfl) (sigma x)).trans
      (((compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty) (fun _ => rfl) (sigma x)).symm).trans
        (congrArg (ren_ty id) (h x)))

theorem up_subst_subst_tm_tm {k l_ty l_tm m_ty m_tm} (sigma : Fin k → tm l_ty l_tm)
    (tau_ty : Fin l_ty → ty m_ty) (tau_tm : Fin l_tm → tm m_ty m_tm) (theta : Fin k → tm m_ty m_tm)
    (h : ∀ x, funcomp (subst_tm tau_ty tau_tm) sigma x = theta x) :
    ∀ x, funcomp (subst_tm (up_tm_ty tau_ty) (up_tm_tm tau_tm)) (up_tm_tm sigma) x
         = up_tm_tm theta x :=
  Fin.cases rfl (fun i =>
    (compRenSubst_tm id shift (up_tm_ty tau_ty) (up_tm_tm tau_tm)
        (funcomp (up_tm_ty tau_ty) id) (funcomp (up_tm_tm tau_tm) shift)
        (fun _ => rfl) (fun _ => rfl) (sigma i)).trans
      (((compSubstRen_tm tau_ty tau_tm id shift
          (funcomp (ren_ty id) tau_ty) (funcomp (ren_tm id shift) tau_tm)
          (fun _ => rfl) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_tm id shift) (h i))))

theorem compSubstSubst_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (sigma_ty : Fin m_ty → ty k_ty) (sigma_tm : Fin m_tm → tm k_ty k_tm)
    (tau_ty : Fin k_ty → ty l_ty) (tau_tm : Fin k_tm → tm l_ty l_tm)
    (theta_ty : Fin m_ty → ty l_ty) (theta_tm : Fin m_tm → tm l_ty l_tm)
    (h_ty : ∀ x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
    (h_tm : ∀ x, funcomp (subst_tm tau_ty tau_tm) sigma_tm x = theta_tm x) :
    ∀ s, subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s) = subst_tm theta_ty theta_tm s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s0)
                            (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm theta_ty theta_tm h_ty h_tm s0)
                             (compSubstSubst_ty sigma_ty tau_ty theta_ty h_ty s1)
  | lam s0 s1  => congr_lam (compSubstSubst_ty sigma_ty tau_ty theta_ty h_ty s0)
                            (compSubstSubst_tm _ _ _ _ _ _
                              (up_subst_subst_tm_ty _ _ _ h_ty) (up_subst_subst_tm_tm _ _ _ _ h_tm) s1)
  | tlam s0    => congr_tlam (compSubstSubst_tm _ _ _ _ _ _
                              (up_subst_subst_ty_ty _ _ _ h_ty) (up_subst_subst_ty_tm _ _ _ _ h_tm) s0)

/-! ### Renaming is a special case of substitution -/

theorem rinstInst_up_ty_tm {m n_ty n_tm} (xi : Fin m → Fin n_tm) (sigma : Fin m → tm n_ty n_tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ x, funcomp var_tm (upRen_ty_tm xi) x = up_ty_tm sigma x :=
  fun x => congrArg (ren_tm shift id) (h x)

theorem rinstInst_up_tm_ty {m n_ty} (xi : Fin m → Fin n_ty) (sigma : Fin m → ty n_ty)
    (h : ∀ x, funcomp var_ty xi x = sigma x) :
    ∀ x, funcomp var_ty (upRen_tm_ty xi) x = up_tm_ty sigma x :=
  fun x => congrArg (ren_ty id) (h x)

theorem rinstInst_up_tm_tm {m n_ty n_tm} (xi : Fin m → Fin n_tm) (sigma : Fin m → tm n_ty n_tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ x, funcomp var_tm (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  Fin.cases rfl (fun i => congrArg (ren_tm id shift) (h i))

theorem rinst_inst_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm)
    (sigma_ty : Fin m_ty → ty n_ty) (sigma_tm : Fin m_tm → tm n_ty n_tm)
    (h_ty : ∀ x, funcomp var_ty xi_ty x = sigma_ty x)
    (h_tm : ∀ x, funcomp var_tm xi_tm x = sigma_tm x) :
    ∀ s, ren_tm xi_ty xi_tm s = subst_tm sigma_ty sigma_tm s
  | var_tm s0  => h_tm s0
  | app s0 s1  => congr_app (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm h_ty h_tm s0)
                            (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm h_ty h_tm s1)
  | tapp s0 s1 => congr_tapp (rinst_inst_tm xi_ty xi_tm sigma_ty sigma_tm h_ty h_tm s0)
                             (rinst_inst_ty xi_ty sigma_ty h_ty s1)
  | lam s0 s1  => congr_lam (rinst_inst_ty xi_ty sigma_ty h_ty s0)
                            (rinst_inst_tm _ _ _ _
                              (rinstInst_up_tm_ty _ _ h_ty) (rinstInst_up_tm_tm _ _ h_tm) s1)
  | tlam s0    => congr_tlam (rinst_inst_tm _ _ _ _
                              (rinstInst_up_ty_ty _ _ h_ty) (rinstInst_up_ty_tm _ _ h_tm) s0)

/-! ### `tm` clean (funext-based) wrappers — the `asimp`-facing API -/

theorem renRen_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (xi_ty : Fin m_ty → Fin k_ty) (xi_tm : Fin m_tm → Fin k_tm)
    (zeta_ty : Fin k_ty → Fin l_ty) (zeta_tm : Fin k_tm → Fin l_tm) (s : tm m_ty m_tm) :
    ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s)
      = ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s :=
  compRenRen_tm xi_ty xi_tm zeta_ty zeta_tm _ _ (fun _ => rfl) (fun _ => rfl) s

theorem renSubst_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (xi_ty : Fin m_ty → Fin k_ty) (xi_tm : Fin m_tm → Fin k_tm)
    (tau_ty : Fin k_ty → ty l_ty) (tau_tm : Fin k_tm → tm l_ty l_tm) (s : tm m_ty m_tm) :
    subst_tm tau_ty tau_tm (ren_tm xi_ty xi_tm s)
      = subst_tm (funcomp tau_ty xi_ty) (funcomp tau_tm xi_tm) s :=
  compRenSubst_tm xi_ty xi_tm tau_ty tau_tm _ _ (fun _ => rfl) (fun _ => rfl) s

theorem substRen_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (sigma_ty : Fin m_ty → ty k_ty) (sigma_tm : Fin m_tm → tm k_ty k_tm)
    (zeta_ty : Fin k_ty → Fin l_ty) (zeta_tm : Fin k_tm → Fin l_tm) (s : tm m_ty m_tm) :
    ren_tm zeta_ty zeta_tm (subst_tm sigma_ty sigma_tm s)
      = subst_tm (funcomp (ren_ty zeta_ty) sigma_ty) (funcomp (ren_tm zeta_ty zeta_tm) sigma_tm) s :=
  compSubstRen_tm sigma_ty sigma_tm zeta_ty zeta_tm _ _ (fun _ => rfl) (fun _ => rfl) s

theorem substSubst_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (sigma_ty : Fin m_ty → ty k_ty) (sigma_tm : Fin m_tm → tm k_ty k_tm)
    (tau_ty : Fin k_ty → ty l_ty) (tau_tm : Fin k_tm → tm l_ty l_tm) (s : tm m_ty m_tm) :
    subst_tm tau_ty tau_tm (subst_tm sigma_ty sigma_tm s)
      = subst_tm (funcomp (subst_ty tau_ty) sigma_ty) (funcomp (subst_tm tau_ty tau_tm) sigma_tm) s :=
  compSubstSubst_tm sigma_ty sigma_tm tau_ty tau_tm _ _ (fun _ => rfl) (fun _ => rfl) s

theorem substSubst'_tm {k_ty k_tm l_ty l_tm m_ty m_tm}
    (sigma_ty : Fin m_ty → ty k_ty) (sigma_tm : Fin m_tm → tm k_ty k_tm)
    (tau_ty : Fin k_ty → ty l_ty) (tau_tm : Fin k_tm → tm l_ty l_tm) :
    funcomp (subst_tm tau_ty tau_tm) (subst_tm sigma_ty sigma_tm)
      = subst_tm (funcomp (subst_ty tau_ty) sigma_ty) (funcomp (subst_tm tau_ty tau_tm) sigma_tm) :=
  funext (substSubst_tm sigma_ty sigma_tm tau_ty tau_tm)

theorem rinstInst'_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm)
    (s : tm m_ty m_tm) :
    ren_tm xi_ty xi_tm s = subst_tm (funcomp var_ty xi_ty) (funcomp var_tm xi_tm) s :=
  rinst_inst_tm xi_ty xi_tm _ _ (fun _ => rfl) (fun _ => rfl) s

theorem rinstInst_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm) :
    ren_tm xi_ty xi_tm = subst_tm (funcomp var_ty xi_ty) (funcomp var_tm xi_tm) :=
  funext (rinstInst'_tm xi_ty xi_tm)

theorem instId'_tm {m_ty m_tm} (s : tm m_ty m_tm) : subst_tm var_ty var_tm s = s :=
  idSubst_tm var_ty var_tm (fun _ => rfl) (fun _ => rfl) s

theorem instId_tm {m_ty m_tm} : subst_tm (@var_ty m_ty) (@var_tm m_ty m_tm) = id := funext instId'_tm

theorem rinstId'_tm {m_ty m_tm} (s : tm m_ty m_tm) : ren_tm id id s = s :=
  (rinstInst'_tm id id s).trans (instId'_tm s)

theorem rinstId_tm {m_ty m_tm} : @ren_tm m_ty m_tm m_ty m_tm id id = id := funext rinstId'_tm

theorem varL_tm {m_ty m_tm n_ty n_tm} (sigma_ty : Fin m_ty → ty n_ty) (sigma_tm : Fin m_tm → tm n_ty n_tm) :
    funcomp (subst_tm sigma_ty sigma_tm) var_tm = sigma_tm := rfl

theorem varLRen_tm {m_ty m_tm n_ty n_tm} (xi_ty : Fin m_ty → Fin n_ty) (xi_tm : Fin m_tm → Fin n_tm) :
    funcomp (ren_tm xi_ty xi_tm) var_tm = funcomp var_tm xi_tm := rfl

/-! ## Sanity checks: the multi-sorted scoped substitution lemmas behave as intended. -/

/-- Term-level β substitution `s[t]` (substitute a `tm` for de Bruijn 0, leave `ty` fixed). -/
@[reducible] def beta_tm {n_ty n_tm} (t : tm n_ty n_tm) : Fin (n_tm + 1) → tm n_ty n_tm := scons t var_tm
/-- Type-level β substitution for `tapp (tlam s) T` (substitute a `ty` for de Bruijn 0). -/
@[reducible] def beta_ty {n} (T : ty n) : Fin (n + 1) → ty n := scons T var_ty

-- A `ty`-substitution under `tlam` leaves a `shift`ed term untouched.
example {n_ty n_tm} (s : tm n_ty n_tm) (T : ty n_ty) :
    subst_tm (beta_ty T) var_tm (ren_tm shift id s) = s := by
  rw [renSubst_tm]; exact idSubst_tm _ _ (fun _ => rfl) (fun _ => rfl) s

-- A `tm`-substitution under `lam` leaves a `shift`ed term untouched.
example {n_ty n_tm} (s t : tm n_ty n_tm) :
    subst_tm var_ty (beta_tm t) (ren_tm id shift s) = s := by
  rw [renSubst_tm]; exact idSubst_tm _ _ (fun _ => rfl) (fun _ => rfl) s

-- Two parallel renamings fuse.
example {k_ty k_tm l_ty l_tm m_ty m_tm}
    (xi_ty : Fin m_ty → Fin k_ty) (xi_tm : Fin m_tm → Fin k_tm)
    (zeta_ty : Fin k_ty → Fin l_ty) (zeta_tm : Fin k_tm → Fin l_tm) (s : tm m_ty m_tm) :
    ren_tm zeta_ty zeta_tm (ren_tm xi_ty xi_tm s)
      = ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_tm xi_tm) s :=
  renRen_tm xi_ty xi_tm zeta_ty zeta_tm s

end Autosubst.SysFScoped
