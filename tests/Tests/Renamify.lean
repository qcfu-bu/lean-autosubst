/-
# The `substify` / `renamify` / `auto_unfold` tactics.

`substify` rewrites renamings into substitutions (`s⟨ξ⟩ ↦ s[var ∘ ξ]`); `renamify` is its
**inverse** — it rewrites `s[var ∘ ξ] ↦ s⟨ξ⟩` (the same `rinstInst'_s` identity, oriented
right-to-left in the `renamify_lemmas` set), mirroring the reference `renamify`'s
`setoid_rewrite_left rinstInst'`. Both are **notation-native**: their lemmas are stated over the
typeclass-method / notation forms (`s⟨ξ⟩` = `Ren{k}.ren{k} ξ s`, `s[σ⃗]` = `Subst{k}.subst{k} σ⃗ s`),
not the raw `ren_s`/`subst_s` ops — there is no raw `rinstInst` lemma. The notation-form tests live in
the `Renamify.Notation*` sections below (single-sort + multi-sort, both backends); each asserts the
output is *syntactically* notation via `guard_hyp … :ₛ`. `auto_unfold` unfolds the lifting helpers
(`up_<b>_<v>` / `upRen_<b>_<v>` / `up_ren`) — that is tested in the two sections immediately below.
-/
import Tests.Support

/-! ## `auto_unfold` (unscoped) -/
namespace Renamify.Unscoped
open Autosubst

autosubst
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

-- `auto_unfold` exposes the lifting helper's body (no σ-calculus rewriting), incl. `at h`:
example (σ : Nat → tm) :
    up_tm_tm σ = scons (tm.var_tm var_zero) (funcomp (ren_tm shift) σ) := by rfl
example (σ : Nat → tm) (n : Nat) : up_tm_tm σ (n + 1) = ren_tm shift (σ n) := by rfl

end Renamify.Unscoped

/-! ## `auto_unfold` (well-scoped) -/
namespace Renamify.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

example {m n} (σ : Fin m → tm n) :
    up_tm_tm σ = scons (tm.var_tm var_zero) (funcomp (ren_tm shift) σ) := by rfl

end Renamify.Scoped

/-! ## Notation-native `substify` / `renamify`

`substify`/`renamify` must operate in the same typeclass-method / notation vocabulary as `asimp`
(`s⟨ξ⟩` = `Ren{k}.ren{k} ξ s`, `s[σ⃗]` = `Subst{k}.subst{k} σ⃗ s`), not only over the raw
`ren_s`/`subst_s` ops — otherwise they find nothing on a notation goal and error "no progress".

The `guard_hyp h :ₛ …` checks use the **syntactic** matcher (`:ₛ`, not `:`): since the raw and method
forms are defeq, only a syntactic guard actually witnesses that the output is in notation form
(`s⟨ξ⟩`), not raw `ren_tm`. Exercised on a single-sort and a multi-sort (vector-2) signature, both
backends. -/

/-! ### Unscoped, single sort -/
namespace Renamify.NotationStlc
open Autosubst Autosubst.Notation

autosubst
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

-- notation goal in/out (using the raw `var_tm` ctor — `asimp`'s normal form):
theorem n_renamify (ξ : Nat → Nat) (s : tm) : s[funcomp tm.var_tm ξ] = s⟨ξ⟩ := by renamify
theorem n_substify (ξ : Nat → Nat) (s : tm) : s⟨ξ⟩ = s[funcomp tm.var_tm ξ] := by substify
-- the `Var.ids` spelling (ascribed) also works, normalized to the ctor form by `varIds`:
theorem n_renamify_ids (ξ : Nat → Nat) (s : tm) :
    s[funcomp (Var.ids : Nat → tm) ξ] = s⟨ξ⟩ := by renamify
-- output is *syntactically* notation, not raw `ren_tm`/`subst_tm`:
theorem n_renamify_form (ξ : Nat → Nat) (s t : tm) (h : s[funcomp tm.var_tm ξ] = t) :
    s⟨ξ⟩ = t := by renamify at h; guard_hyp h :ₛ s⟨ξ⟩ = t; exact h
theorem n_substify_form (ξ : Nat → Nat) (s t : tm) (h : s⟨ξ⟩ = t) :
    s[funcomp tm.var_tm ξ] = t := by substify at h; guard_hyp h :ₛ s[funcomp tm.var_tm ξ] = t; exact h

#axiom_clean n_renamify
#axiom_clean n_substify
end Renamify.NotationStlc

/-! ### Well-scoped, single sort -/
namespace Renamify.NotationStlcS
open Autosubst Autosubst.Scoped Autosubst.Notation

autosubst wellscoped
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

theorem n_renamify {m n} (ξ : Fin m → Fin n) (s : tm m) : s[funcomp tm.var_tm ξ] = s⟨ξ⟩ := by renamify
theorem n_substify {m n} (ξ : Fin m → Fin n) (s : tm m) : s⟨ξ⟩ = s[funcomp tm.var_tm ξ] := by substify
theorem n_renamify_form {m n} (ξ : Fin m → Fin n) (s : tm m) (t : tm n)
    (h : s[funcomp tm.var_tm ξ] = t) : s⟨ξ⟩ = t := by
  renamify at h; guard_hyp h :ₛ s⟨ξ⟩ = t; exact h

#axiom_clean n_renamify
#axiom_clean n_substify
end Renamify.NotationStlcS

/-! ### Unscoped, multi-sort (vector-2: `tm` over `[ty, tm]`) -/
namespace Renamify.NotationSysF
open Autosubst Autosubst.Notation

autosubst
  ty where | arr : ty → ty → ty
  tm where
    | app  : tm → tm → tm
    | tlam : (bind ty in tm) → tm
    | lam  : ty → (bind tm in tm) → tm

theorem n_renamify (a b : Nat → Nat) (s : tm) :
    s[funcomp ty.var_ty a ; funcomp tm.var_tm b] = s⟨a ; b⟩ := by renamify
theorem n_substify (a b : Nat → Nat) (s : tm) :
    s⟨a ; b⟩ = s[funcomp ty.var_ty a ; funcomp tm.var_tm b] := by substify
theorem n_renamify_form (a b : Nat → Nat) (s t : tm)
    (h : s[funcomp ty.var_ty a ; funcomp tm.var_tm b] = t) : s⟨a ; b⟩ = t := by
  renamify at h; guard_hyp h :ₛ s⟨a ; b⟩ = t; exact h

#axiom_clean n_renamify
#axiom_clean n_substify
end Renamify.NotationSysF

/-! ### Well-scoped, multi-sort (vector-2) -/
namespace Renamify.NotationSysFS
open Autosubst Autosubst.Scoped Autosubst.Notation

autosubst wellscoped
  ty where | arr : ty → ty → ty
  tm where
    | app  : tm → tm → tm
    | tlam : (bind ty in tm) → tm
    | lam  : ty → (bind tm in tm) → tm

-- the scope-polymorphic var ctors need ascription to pin the codomain scopes (per the report note);
-- concrete map variables (`a`, `b`) never do.
theorem n_renamify {m_ty m_tm n_ty n_tm} (a : Fin m_ty → Fin n_ty) (b : Fin m_tm → Fin n_tm)
    (s : tm m_ty m_tm) :
    s[(funcomp ty.var_ty a : Fin m_ty → ty n_ty) ; (funcomp tm.var_tm b : Fin m_tm → tm n_ty n_tm)]
      = s⟨a ; b⟩ := by renamify
theorem n_substify {m_ty m_tm n_ty n_tm} (a : Fin m_ty → Fin n_ty) (b : Fin m_tm → Fin n_tm)
    (s : tm m_ty m_tm) :
    s⟨a ; b⟩
      = s[(funcomp ty.var_ty a : Fin m_ty → ty n_ty) ; (funcomp tm.var_tm b : Fin m_tm → tm n_ty n_tm)]
      := by substify

#axiom_clean n_renamify
#axiom_clean n_substify
end Renamify.NotationSysFS
