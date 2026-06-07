/-
# Autosubst-consistent notations (the additive notation layer).

Exercises the generated per-sort `Subst*`/`Ren*`/`Var` instances and the scoped notations from
[Autosubst/Prelude/Notation.lean] — `s[σ]`/`s[σ;τ]` (substitution application), `s⟨ξ⟩`/`s⟨ξ;ζ⟩`
(renaming application), the function forms `[σ]`/`⟨ξ⟩`, `↑` (shift), and `t..` (single-point
β-substitution). Asserts: each notation reduces to the raw op by `rfl`, `by asimp` still closes
notation'd goals, and the proofs are axiom-clean.

Backend note: the notations dispatch on the subject sort + map type. In the **unscoped** backend
every map type is closed, so no ascription is ever needed. In the **well-scoped** backend a
*polymorphic* constant map (`↑`, `var_tm`, whose scope is a metavar at the use site) needs a one-off
type ascription; concrete map variables never do — see the scoped section below.
-/
import Tests.Support

/-! ## Unscoped, single sort (STLC) -/
namespace Notation.Stlc
open Autosubst Autosubst.Notation

autosubst
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

-- Each notation is *definitionally* the raw op.
theorem app_eq   (σ : Nat → tm) (s : tm) : s[σ] = subst_tm σ s := rfl
theorem ren_eq   (ξ : Nat → Nat) (s : tm) : s⟨ξ⟩ = ren_tm ξ s := rfl
theorem fn_eq    (σ : Nat → tm) : ([σ] : tm → tm) = subst_tm σ := rfl
theorem renfn_eq (ξ : Nat → Nat) : (⟨ξ⟩ : tm → tm) = ren_tm ξ := rfl
theorem beta_eq  (t : tm) : (t.. : Nat → tm) = scons t tm.var_tm := rfl
theorem shift_eq : (↑ : Nat → Nat) = shift := rfl

-- The explicit finite substitution `[a, b, c/]` (= `a .: b .: c .: var`) and its application form
-- `s[a, b, c/]`; `[a/]` / `s[a/]` are the single-variable (β) case.
theorem subList_eq (a b c : tm) : [a, b, c/] = scons a (scons b (scons c tm.var_tm)) := rfl
theorem subList_app (a b : tm) (s : tm) : s[a, b/] = subst_tm (scons a (scons b tm.var_tm)) s := rfl
theorem subOne_eq (a : tm) : [a/] = scons a tm.var_tm := rfl

-- `asimp` closes notation'd goals.
theorem identity (s : tm) : s[tm.var_tm] = s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) : s[σ][τ] = s[σ >> [τ]] := by asimp
theorem ren_fusion (ξ ζ : Nat → Nat) (s : tm) : s⟨ξ⟩⟨ζ⟩ = s⟨ξ >> ζ⟩ := by asimp
theorem beta_cancel (t s : tm) : (s⟨↑⟩)[t/] = s := by asimp
-- `⇑σ` is the binder lift (available because `tm` is the lone open sort).
theorem up_eq (σ : Nat → tm) : ⇑σ = up_tm_tm σ := rfl
theorem subst_lemma (σ : Nat → tm) (t s : tm) :
    (s[t/])[σ] = (s[⇑σ])[t[σ]/] := by asimp

#axiom_clean beta_cancel
#axiom_clean subst_lemma
#axiom_clean identity

end Notation.Stlc

/-! ## Unscoped, multi-sort (System F): the two-map forms `s[σ;τ]` / `s⟨ξ;ζ⟩` -/
namespace Notation.SysF
open Autosubst Autosubst.Notation

autosubst
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

theorem ty_app_eq  (σ : Nat → ty) (a : ty) : a[σ] = subst_ty σ a := rfl
theorem tm_app_eq  (στ : Nat → ty) (σm : Nat → tm) (t : tm) : t[στ;σm] = subst_tm στ σm t := rfl
theorem tm_ren_eq  (ξτ ξm : Nat → Nat) (t : tm) : t⟨ξτ;ξm⟩ = ren_tm ξτ ξm t := rfl

theorem identity (s : tm) : s[ty.var_ty;tm.var_tm] = s := by asimp
theorem term_fusion (στ τty : Nat → ty) (σm τm : Nat → tm) (s : tm) :
    s[στ;σm][τty;τm] = s[στ >> [τty]; funcomp (subst_tm τty τm) σm] := by asimp
theorem type_beta (T : ty) (s : tm) :
    (s⟨↑;(id : Nat → Nat)⟩)[T..;tm.var_tm] = s := by asimp
theorem term_beta (t s : tm) :
    (s⟨(id : Nat → Nat);↑⟩)[ty.var_ty;t..] = s := by asimp

#axiom_clean identity
#axiom_clean type_beta
#axiom_clean term_beta

end Notation.SysF

/-! ## Well-scoped (STLC): notations on concrete maps; polymorphic constants ascribed. -/
namespace Notation.Scoped
open Autosubst Autosubst.Scoped Autosubst.Scoped.Notation

autosubst wellscoped
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

-- Concrete map variables need no ascription.
theorem app_eq {m n} (σ : Fin m → tm n) (s : tm m) : s[σ] = subst_tm σ s := rfl
theorem ren_eq {m n} (ξ : Fin m → Fin n) (s : tm m) : s⟨ξ⟩ = ren_tm ξ s := rfl
theorem subst_fusion {m n k} (σ : Fin m → tm n) (τ : Fin n → tm k) (s : tm m) :
    s[σ][τ] = s[σ >> [τ]] := by asimp
theorem ren_fusion {m n k} (ξ : Fin m → Fin n) (ζ : Fin n → Fin k) (s : tm m) :
    s⟨ξ⟩⟨ζ⟩ = s⟨ξ >> ζ⟩ := by asimp

-- `⇑σ` (binder lift) dispatches on the concrete map `σ`, so it needs no ascription.
theorem up_eq {m n} (σ : Fin m → tm n) : ⇑σ = up_tm_tm σ := rfl
-- Polymorphic scoped constants (`↑`, `var_tm`) carry a one-off ascription.
theorem identity {n} (s : tm n) : s[(tm.var_tm : Fin n → tm n)] = s := by asimp
theorem beta_cancel {n} (t s : tm n) :
    (s⟨(↑ : Fin n → Fin (n+1))⟩)[([t/] : Fin (n+1) → tm n)] = s := by asimp
theorem subst_lemma {m n} (σ : Fin m → tm n) (t : tm m) (s : tm (m + 1)) :
    (s[([t/] : Fin (m+1) → tm m)])[σ] = (s[⇑σ])[([t[σ]/] : Fin (n+1) → tm n)] := by asimp

#axiom_clean subst_fusion
#axiom_clean beta_cancel
#axiom_clean identity

end Notation.Scoped
