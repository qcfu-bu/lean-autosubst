/-
# Phase 8 — Golden target: well-scoped (`Fin`-indexed) de Bruijn STLC, by hand.

The scoped analogue of [Stlc.lean](Stlc.lean). Same signature
(rocq/autosubst2-ocaml/signatures/stlc.sig):

    ty : Type
    tm : Type
    Base : ty
    Fun  : ty -> ty -> ty
    app  : tm -> tm -> tm
    lam  : ty -> (bind tm in tm) -> tm

but the substitution sort `tm` is now **scope-indexed**: `tm : Nat → Type`,
`var_tm : Fin n → tm n`, `lam : ty → tm (n+1) → tm n`, and `ren`/`subst` thread
`Fin m → Fin n` / `Fin m → tm n` maps. `ty` carries no variables, so it stays unscoped.

Variable backend: Lean's core `Fin n` (`Autosubst.Scoped`, see plan.md §7/§4). The `Nat`
`0`/`n+1` case split becomes `Fin.cases`; because `Fin.cases` reduces definitionally on
`0`/`Fin.succ i`, every proof carries over from the unscoped golden. Names match the
Autosubst-2 scoped output exactly — this is the generator's scoped contract.

Done = typechecks; no `sorry`; axioms = `{propext, Quot.sound}` only.
-/
import Autosubst.Prelude.Scoped

namespace Autosubst.StlcScoped
open Autosubst Autosubst.Scoped

/-! ## Syntax (scoped de Bruijn) -/

/-- Types. No variables, no substitution — unscoped. -/
inductive ty where
  | Base : ty
  | Fun  : ty → ty → ty
  deriving Repr, DecidableEq

/-- Terms, scope-indexed. `var_tm` draws from `Fin n`; `lam` binds one `tm` variable. -/
inductive tm : Nat → Type where
  | var_tm : {n : Nat} → Fin n → tm n
  | app    : {n : Nat} → tm n → tm n → tm n
  | lam    : {n : Nat} → ty → tm (n + 1) → tm n

open tm

/-! ## Congruence lemmas -/

theorem congr_app {n} {s0 s1 t0 t1 : tm n} (h0 : s0 = t0) (h1 : s1 = t1) :
    app s0 s1 = app t0 t1 := by rw [h0, h1]

theorem congr_lam {n} {A0 A1 : ty} {s0 s1 : tm (n + 1)} (h0 : A0 = A1) (h1 : s0 = s1) :
    lam A0 s0 = lam A1 s1 := by rw [h0, h1]

/-! ## Renaming -/

/-- Lift a renaming under a `tm` binder. -/
@[reducible] def upRen_tm_tm {m n} (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) := up_ren xi

/-- Parallel renaming. -/
def ren_tm {m n} (xi : Fin m → Fin n) : tm m → tm n
  | var_tm i => var_tm (xi i)
  | app s t  => app (ren_tm xi s) (ren_tm xi t)
  | lam A s  => lam A (ren_tm (upRen_tm_tm xi) s)

/-! ## Substitution -/

/-- Lift a substitution under a `tm` binder. -/
@[reducible] def up_tm_tm {m n} (sigma : Fin m → tm n) : Fin (m + 1) → tm (n + 1) :=
  scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)

/-- Parallel substitution. -/
def subst_tm {m n} (sigma : Fin m → tm n) : tm m → tm n
  | var_tm i => sigma i
  | app s t  => app (subst_tm sigma s) (subst_tm sigma t)
  | lam A s  => lam A (subst_tm (up_tm_tm sigma) s)

/-! ## `subst id = id` -/

theorem upId_tm_tm {m} (sigma : Fin m → tm m) (h : ∀ x, sigma x = var_tm x) :
    ∀ x, up_tm_tm sigma x = var_tm x :=
  Fin.cases rfl (fun i => congrArg (ren_tm shift) (h i))

theorem idSubst_tm {m} (sigma : Fin m → tm m) (h : ∀ x, sigma x = var_tm x) :
    ∀ s, subst_tm sigma s = s
  | var_tm i => h i
  | app s t  => by simp [subst_tm, idSubst_tm sigma h s, idSubst_tm sigma h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl (idSubst_tm (up_tm_tm sigma) (upId_tm_tm sigma h) s)

/-! ## Extensionality -/

theorem upExtRen_tm_tm {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_tm_tm xi x = upRen_tm_tm zeta x :=
  Fin.cases rfl (fun i => congrArg shift (h i))

theorem extRen_tm {m n} (xi zeta : Fin m → Fin n) (h : ∀ x, xi x = zeta x) :
    ∀ s, ren_tm xi s = ren_tm zeta s
  | var_tm i => by simp [ren_tm, h i]
  | app s t  => by simp [ren_tm, extRen_tm xi zeta h s, extRen_tm xi zeta h t]
  | lam A s  => by
      simp only [ren_tm]
      exact congr_lam rfl
        (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm xi zeta h) s)

theorem upExt_tm_tm {m n} (sigma tau : Fin m → tm n) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_tm_tm sigma x = up_tm_tm tau x :=
  Fin.cases rfl (fun i => congrArg (ren_tm shift) (h i))

theorem ext_tm {m n} (sigma tau : Fin m → tm n) (h : ∀ x, sigma x = tau x) :
    ∀ s, subst_tm sigma s = subst_tm tau s
  | var_tm i => by simp [subst_tm, h i]
  | app s t  => by simp [subst_tm, ext_tm sigma tau h s, ext_tm sigma tau h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl (ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm sigma tau h) s)

/-! ## Compositionality: ren ∘ ren -/

theorem up_ren_ren_tm_tm {k l m} (xi : Fin k → Fin l) (zeta : Fin l → Fin m)
    (rho : Fin k → Fin m) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho h

theorem compRenRen_tm {k l m} (xi : Fin m → Fin k) (zeta : Fin k → Fin l)
    (rho : Fin m → Fin l) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ s, ren_tm zeta (ren_tm xi s) = ren_tm rho s
  | var_tm i => congrArg var_tm (h i)
  | app s t  => by
      simp [ren_tm, compRenRen_tm xi zeta rho h s, compRenRen_tm xi zeta rho h t]
  | lam A s  => by
      simp only [ren_tm]
      exact congr_lam rfl
        (compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho)
          (up_ren_ren_tm_tm xi zeta rho h) s)

/-! ## Compositionality: subst ∘ ren -/

theorem up_ren_subst_tm_tm {k l m} (xi : Fin k → Fin l) (tau : Fin l → tm m)
    (theta : Fin k → tm m) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x :=
  Fin.cases rfl (fun i => congrArg (ren_tm shift) (h i))

theorem compRenSubst_tm {k l m} (xi : Fin m → Fin k) (tau : Fin k → tm l)
    (theta : Fin m → tm l) (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ s, subst_tm tau (ren_tm xi s) = subst_tm theta s
  | var_tm i => h i
  | app s t  => by
      simp [ren_tm, subst_tm, compRenSubst_tm xi tau theta h s,
        compRenSubst_tm xi tau theta h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta)
          (up_ren_subst_tm_tm xi tau theta h) s)

/-! ## Compositionality: ren ∘ subst -/

theorem up_subst_ren_tm_tm {k l m} (sigma : Fin k → tm l) (zeta : Fin l → Fin m)
    (theta : Fin k → tm m) (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ x, funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  Fin.cases rfl (fun i =>
    (compRenRen_tm shift (upRen_tm_tm zeta) (funcomp shift zeta) (fun _ => rfl) (sigma i)).trans
      (((compRenRen_tm zeta shift (funcomp shift zeta) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_tm shift) (h i))))

theorem compSubstRen_tm {k l m} (sigma : Fin m → tm k) (zeta : Fin k → Fin l)
    (theta : Fin m → tm l) (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ s, ren_tm zeta (subst_tm sigma s) = subst_tm theta s
  | var_tm i => h i
  | app s t  => by
      simp [ren_tm, subst_tm, compSubstRen_tm sigma zeta theta h s,
        compSubstRen_tm sigma zeta theta h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta)
          (up_subst_ren_tm_tm sigma zeta theta h) s)

/-! ## Compositionality: subst ∘ subst -/

theorem up_subst_subst_tm_tm {k l m} (sigma : Fin k → tm l) (tau : Fin l → tm m)
    (theta : Fin k → tm m) (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ x, funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x :=
  Fin.cases rfl (fun i =>
    (compRenSubst_tm shift (up_tm_tm tau) (funcomp (up_tm_tm tau) shift) (fun _ => rfl) (sigma i)).trans
      (((compSubstRen_tm tau shift (funcomp (ren_tm shift) tau) (fun _ => rfl) (sigma i)).symm).trans
        (congrArg (ren_tm shift) (h i))))

theorem compSubstSubst_tm {k l m} (sigma : Fin m → tm k) (tau : Fin k → tm l)
    (theta : Fin m → tm l) (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ s, subst_tm tau (subst_tm sigma s) = subst_tm theta s
  | var_tm i => h i
  | app s t  => by
      simp [subst_tm, compSubstSubst_tm sigma tau theta h s,
        compSubstSubst_tm sigma tau theta h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl
        (compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta)
          (up_subst_subst_tm_tm sigma tau theta h) s)

/-! ## Renaming is a special case of substitution -/

theorem rinstInst_up_tm_tm {m n} (xi : Fin m → Fin n) (sigma : Fin m → tm n)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ x, funcomp var_tm (upRen_tm_tm xi) x = up_tm_tm sigma x :=
  Fin.cases rfl (fun i => congrArg (ren_tm shift) (h i))

theorem rinst_inst_tm {m n} (xi : Fin m → Fin n) (sigma : Fin m → tm n)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ s, ren_tm xi s = subst_tm sigma s
  | var_tm i => h i
  | app s t  => by
      simp [ren_tm, subst_tm, rinst_inst_tm xi sigma h s, rinst_inst_tm xi sigma h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm xi sigma h) s)

/-! ## Clean (funext-based) wrappers — the `asimp`-facing API -/

theorem rinstInst_tm {m n} (xi : Fin m → Fin n) : ren_tm xi = subst_tm (funcomp var_tm xi) :=
  funext (rinst_inst_tm xi (funcomp var_tm xi) (fun _ => rfl))

theorem instId_tm {m} : subst_tm (@var_tm m) = id :=
  funext (idSubst_tm var_tm (fun _ => rfl))

theorem rinstId_tm {m} : @ren_tm m m id = id := by
  rw [rinstInst_tm id]; exact instId_tm

theorem varL_tm {m n} (sigma : Fin m → tm n) : funcomp (subst_tm sigma) var_tm = sigma := rfl

theorem varLRen_tm {m n} (xi : Fin m → Fin n) :
    funcomp (ren_tm xi) var_tm = funcomp var_tm xi := rfl

theorem renRen_tm {k l m} (xi : Fin m → Fin k) (zeta : Fin k → Fin l) (s : tm m) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s :=
  compRenRen_tm xi zeta _ (fun _ => rfl) s

theorem renRen'_tm {k l m} (xi : Fin m → Fin k) (zeta : Fin k → Fin l) :
    funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi) :=
  funext (renRen_tm xi zeta)

theorem compRenSubst'_tm {k l m} (xi : Fin m → Fin k) (tau : Fin k → tm l) (s : tm m) :
    subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s :=
  compRenSubst_tm xi tau _ (fun _ => rfl) s

theorem renSubst'_tm {k l m} (xi : Fin m → Fin k) (tau : Fin k → tm l) :
    funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi) :=
  funext (compRenSubst'_tm xi tau)

theorem compSubstRen'_tm {k l m} (sigma : Fin m → tm k) (zeta : Fin k → Fin l) (s : tm m) :
    ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s :=
  compSubstRen_tm sigma zeta _ (fun _ => rfl) s

theorem substRen'_tm {k l m} (sigma : Fin m → tm k) (zeta : Fin k → Fin l) :
    funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma) :=
  funext (compSubstRen'_tm sigma zeta)

theorem compSubstSubst'_tm {k l m} (sigma : Fin m → tm k) (tau : Fin k → tm l) (s : tm m) :
    subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s :=
  compSubstSubst_tm sigma tau _ (fun _ => rfl) s

theorem substSubst'_tm {k l m} (sigma : Fin m → tm k) (tau : Fin k → tm l) :
    funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma) :=
  funext (compSubstSubst'_tm sigma tau)

/-! ## Sanity checks: the substitution lemmas behave as intended (cf. eventual `asimp` goals). -/

/-- Single-variable substitution `s[t]` used by β-reduction. -/
@[reducible] def beta {n} (t : tm n) : Fin (n + 1) → tm n := scons t var_tm

example {n} (s t : tm n) : subst_tm (beta t) (ren_tm shift s) = s := by
  rw [compRenSubst'_tm]
  exact idSubst_tm _ (fun _ => rfl) s

example {m} (s : tm m) : subst_tm var_tm s = s := congrFun instId_tm s

example {k l m} (xi : Fin m → Fin k) (zeta : Fin k → Fin l) (s : tm m) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s := renRen_tm xi zeta s

end Autosubst.StlcScoped
