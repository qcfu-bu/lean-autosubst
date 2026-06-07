/-
# Phase 0 — Golden target: unscoped de Bruijn STLC, by hand.

This file is the **specification** for the code/lemma generator. It is what
`autosubst in inductive Tm where …` must eventually emit for the signature
(rocq/autosubst2-ocaml/signatures/stlc.sig):

    ty : Type
    tm : Type
    Base : ty
    Fun  : ty -> ty -> ty
    app  : tm -> tm -> tm
    lam  : ty -> (bind tm in tm) -> tm

Only `tm` is a *substitution sort* (it has variables, since `tm` is bound by `lam`);
`ty` is an ordinary sort with no variables and no substitution. So the whole
substitution apparatus is generated for `tm` alone.

Every definition and lemma name below matches the Autosubst 2 (OCaml) generated
output exactly — these names are the contract the metaprogram must reproduce.
We write the funext-based ("clean") forms as the primary API, with the pointwise
forms as the inductive stepping stones, per plan.md §1.

Hand-proving this first validates the substitution mathematics in Lean
independently of any metaprogramming.
-/
import Autosubst.Prelude.Unscoped

namespace Autosubst.Stlc
open Autosubst

/-! ## Syntax (de Bruijn) -/

/-- Types. No variables, no substitution. -/
inductive ty where
  | Base : ty
  | Fun  : ty → ty → ty
  deriving Repr, DecidableEq

/-- Terms. `var_tm` is the variable constructor; `lam` binds one `tm` variable. -/
inductive tm where
  | var_tm : Nat → tm
  | app    : tm → tm → tm
  | lam    : ty → tm → tm
  deriving Repr, DecidableEq

open tm

/-! ## Congruence lemmas -/

theorem congr_app {s0 s1 t0 t1 : tm} (h0 : s0 = t0) (h1 : s1 = t1) :
    app s0 s1 = app t0 t1 := by rw [h0, h1]

theorem congr_lam {A0 A1 : ty} {s0 s1 : tm} (h0 : A0 = A1) (h1 : s0 = s1) :
    lam A0 s0 = lam A1 s1 := by rw [h0, h1]

/-! ## Renaming -/

/-- Lift a renaming under a `tm` binder. -/
@[reducible] def upRen_tm_tm (xi : Nat → Nat) : Nat → Nat := up_ren xi

/-- Parallel renaming. -/
def ren_tm (xi : Nat → Nat) : tm → tm
  | var_tm n => var_tm (xi n)
  | app s t  => app (ren_tm xi s) (ren_tm xi t)
  | lam A s  => lam A (ren_tm (upRen_tm_tm xi) s)

/-! ## Substitution -/

/-- Lift a substitution under a `tm` binder. -/
@[reducible] def up_tm_tm (sigma : Nat → tm) : Nat → tm :=
  scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)

/-- Parallel substitution. -/
def subst_tm (sigma : Nat → tm) : tm → tm
  | var_tm n => sigma n
  | app s t  => app (subst_tm sigma s) (subst_tm sigma t)
  | lam A s  => lam A (subst_tm (up_tm_tm sigma) s)

/-! ## `subst id = id` -/

theorem upId_tm_tm (sigma : Nat → tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ x, up_tm_tm sigma x = var_tm x
  | 0 => rfl
  | n + 1 => by simp [up_tm_tm, funcomp, h n, ren_tm, shift]

theorem idSubst_tm (sigma : Nat → tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ s, subst_tm sigma s = s
  | var_tm n => h n
  | app s t  => by simp [subst_tm, idSubst_tm sigma h s, idSubst_tm sigma h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl (idSubst_tm (up_tm_tm sigma) (upId_tm_tm sigma h) s)

/-! ## Extensionality -/

theorem upExtRen_tm_tm (xi zeta : Nat → Nat) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_tm_tm xi x = upRen_tm_tm zeta x
  | 0 => rfl
  | n + 1 => by simp [upRen_tm_tm, up_ren, funcomp, h n]

theorem extRen_tm (xi zeta : Nat → Nat) (h : ∀ x, xi x = zeta x) :
    ∀ s, ren_tm xi s = ren_tm zeta s
  | var_tm n => by simp [ren_tm, h n]
  | app s t  => by simp [ren_tm, extRen_tm xi zeta h s, extRen_tm xi zeta h t]
  | lam A s  => by
      simp only [ren_tm]
      exact congr_lam rfl
        (extRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm xi zeta h) s)

theorem upExt_tm_tm (sigma tau : Nat → tm) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_tm_tm sigma x = up_tm_tm tau x
  | 0 => rfl
  | n + 1 => by simp [up_tm_tm, funcomp, h n]

theorem ext_tm (sigma tau : Nat → tm) (h : ∀ x, sigma x = tau x) :
    ∀ s, subst_tm sigma s = subst_tm tau s
  | var_tm n => by simp [subst_tm, h n]
  | app s t  => by simp [subst_tm, ext_tm sigma tau h s, ext_tm sigma tau h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl (ext_tm (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm sigma tau h) s)

/-! ## Compositionality: ren ∘ ren -/

theorem up_ren_ren_tm_tm (xi zeta rho : Nat → Nat) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho h

theorem compRenRen_tm (xi zeta rho : Nat → Nat) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ s, ren_tm zeta (ren_tm xi s) = ren_tm rho s
  | var_tm n => congrArg var_tm (h n)
  | app s t  => by
      simp [ren_tm, compRenRen_tm xi zeta rho h s, compRenRen_tm xi zeta rho h t]
  | lam A s  => by
      simp only [ren_tm]
      exact congr_lam rfl
        (compRenRen_tm (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho)
          (up_ren_ren_tm_tm xi zeta rho h) s)

/-! ## Compositionality: subst ∘ ren -/

theorem up_ren_subst_tm_tm (xi : Nat → Nat) (tau : Nat → tm) (theta : Nat → tm)
    (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 => by
      simp only [funcomp, upRen_tm_tm, up_ren, up_tm_tm, scons_succ]
      exact congrArg (ren_tm shift) (h n)

theorem compRenSubst_tm (xi : Nat → Nat) (tau : Nat → tm) (theta : Nat → tm)
    (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ s, subst_tm tau (ren_tm xi s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => by
      simp [ren_tm, subst_tm, compRenSubst_tm xi tau theta h s,
        compRenSubst_tm xi tau theta h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (compRenSubst_tm (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta)
          (up_ren_subst_tm_tm xi tau theta h) s)

/-! ## Compositionality: ren ∘ subst -/

theorem up_subst_ren_tm_tm (sigma : Nat → tm) (zeta : Nat → Nat) (theta : Nat → tm)
    (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ x, funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 => by
      simp only [funcomp, up_tm_tm, scons_succ]
      rw [compRenRen_tm shift (upRen_tm_tm zeta) (funcomp (upRen_tm_tm zeta) shift)
            (fun _ => rfl) (sigma n),
          ← h n,
          compRenRen_tm zeta shift (funcomp shift zeta) (fun _ => rfl) (sigma n)]
      exact extRen_tm _ _ (fun _ => rfl) (sigma n)

theorem compSubstRen_tm (sigma : Nat → tm) (zeta : Nat → Nat) (theta : Nat → tm)
    (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ s, ren_tm zeta (subst_tm sigma s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => by
      simp [ren_tm, subst_tm, compSubstRen_tm sigma zeta theta h s,
        compSubstRen_tm sigma zeta theta h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (compSubstRen_tm (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta)
          (up_subst_ren_tm_tm sigma zeta theta h) s)

/-! ## Compositionality: subst ∘ subst -/

theorem up_subst_subst_tm_tm (sigma : Nat → tm) (tau : Nat → tm) (theta : Nat → tm)
    (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ x, funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 => by
      simp only [funcomp, up_tm_tm, scons_succ]
      rw [compRenSubst_tm shift (up_tm_tm tau) (funcomp (up_tm_tm tau) shift)
            (fun _ => rfl) (sigma n),
          ← h n,
          compSubstRen_tm tau shift (funcomp (ren_tm shift) tau) (fun _ => rfl) (sigma n)]
      exact ext_tm _ _ (fun _ => rfl) (sigma n)

theorem compSubstSubst_tm (sigma : Nat → tm) (tau : Nat → tm) (theta : Nat → tm)
    (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ s, subst_tm tau (subst_tm sigma s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => by
      simp [subst_tm, compSubstSubst_tm sigma tau theta h s,
        compSubstSubst_tm sigma tau theta h t]
  | lam A s  => by
      simp only [subst_tm]
      exact congr_lam rfl
        (compSubstSubst_tm (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta)
          (up_subst_subst_tm_tm sigma tau theta h) s)

/-! ## Renaming is a special case of substitution -/

theorem rinstInst_up_tm_tm (xi : Nat → Nat) (sigma : Nat → tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ x, funcomp var_tm (upRen_tm_tm xi) x = up_tm_tm sigma x
  | 0 => rfl
  | n + 1 => by
      simp only [funcomp, upRen_tm_tm, up_ren, up_tm_tm, scons_succ]
      rw [← h n]; rfl

theorem rinst_inst_tm (xi : Nat → Nat) (sigma : Nat → tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ s, ren_tm xi s = subst_tm sigma s
  | var_tm n => h n
  | app s t  => by
      simp [ren_tm, subst_tm, rinst_inst_tm xi sigma h s, rinst_inst_tm xi sigma h t]
  | lam A s  => by
      simp only [ren_tm, subst_tm]
      exact congr_lam rfl
        (rinst_inst_tm (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm xi sigma h) s)

/-! ## Clean (funext-based) wrappers — the `asimpl`-facing API -/

theorem rinstInst_tm (xi : Nat → Nat) : ren_tm xi = subst_tm (funcomp var_tm xi) :=
  funext (rinst_inst_tm xi (funcomp var_tm xi) (fun _ => rfl))

theorem instId_tm : subst_tm var_tm = id :=
  funext (idSubst_tm var_tm (fun _ => rfl))

theorem rinstId_tm : @ren_tm id = id := by
  rw [rinstInst_tm id]; exact instId_tm

theorem varL_tm (sigma : Nat → tm) : funcomp (subst_tm sigma) var_tm = sigma := rfl

theorem varLRen_tm (xi : Nat → Nat) : funcomp (ren_tm xi) var_tm = funcomp var_tm xi := rfl

theorem renRen_tm (xi zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s :=
  compRenRen_tm xi zeta _ (fun _ => rfl) s

theorem renRen'_tm (xi zeta : Nat → Nat) :
    funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi) :=
  funext (renRen_tm xi zeta)

theorem compRenSubst'_tm (xi : Nat → Nat) (tau : Nat → tm) (s : tm) :
    subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s :=
  compRenSubst_tm xi tau _ (fun _ => rfl) s

theorem renSubst'_tm (xi : Nat → Nat) (tau : Nat → tm) :
    funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi) :=
  funext (compRenSubst'_tm xi tau)

theorem compSubstRen'_tm (sigma : Nat → tm) (zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s :=
  compSubstRen_tm sigma zeta _ (fun _ => rfl) s

theorem substRen'_tm (sigma : Nat → tm) (zeta : Nat → Nat) :
    funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma) :=
  funext (compSubstRen'_tm sigma zeta)

theorem compSubstSubst'_tm (sigma tau : Nat → tm) (s : tm) :
    subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s :=
  compSubstSubst_tm sigma tau _ (fun _ => rfl) s

theorem substSubst'_tm (sigma tau : Nat → tm) :
    funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma) :=
  funext (compSubstSubst'_tm sigma tau)

/-! ## Sanity checks: the substitution lemmas behave as intended.

These stand in for the eventual `by asimpl` goals (Phase 6). For now we close them
with the clean lemmas directly to confirm the tower is internally consistent. -/

/-- Single-variable substitution `s[t]` used by β-reduction. -/
@[reducible] def beta (t : tm) : Nat → tm := scons t var_tm

example (s t : tm) : subst_tm (beta t) (ren_tm shift s) = s := by
  rw [compRenSubst'_tm]
  exact idSubst_tm _ (fun _ => rfl) s

example (s : tm) : subst_tm var_tm s = s := congrFun instId_tm s

example (xi zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s := renRen_tm xi zeta s

end Autosubst.Stlc
