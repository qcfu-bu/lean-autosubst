/-
# Phase 6 remnants — the `renamify` and `auto_unfold` tactics.

`substify` rewrites renamings into substitutions (`ren_s ξ ↦ subst_s (var ∘ ξ)`); `renamify` is its
**inverse** — it rewrites `subst_s (var ∘ ξ) ↦ ren_s ξ` (the same `rinstInst'_s` identity, oriented
right-to-left in the `renamify_lemmas` set), mirroring the reference `renamify`'s
`setoid_rewrite_left rinstInst'`. `auto_unfold` unfolds the lifting helpers (`up_<b>_<v>` /
`upRen_<b>_<v>` / `up_ren`), exposing the underlying `scons`/`funcomp`/`ren shift` machinery.

Tested on **both** backends. Each direction is asserted axiom-clean; `renamify`/`substify` proving
the two mirror statements `subst_s (var ∘ ξ) s = ren_s ξ s` and `ren_s ξ s = subst_s (var ∘ ξ) s`
witnesses that they invert one another.
-/
import Tests.Support

/-! ## Unscoped (`Nat`) -/
namespace Renamify.Unscoped
open Autosubst

autosubst
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

-- `substify` and `renamify` are inverse rewrites of the one `rinstInst'_tm` identity:
theorem substify_dir (ξ : Nat → Nat) (s : tm) :
    ren_tm ξ s = subst_tm (funcomp tm.var_tm ξ) s := by substify
theorem renamify_dir (ξ : Nat → Nat) (s : tm) :
    subst_tm (funcomp tm.var_tm ξ) s = ren_tm ξ s := by renamify

-- `renamify` turns a subst-of-var-composition back into a renaming, which `asimp` then fuses:
theorem renamify_fuse (ξ ζ : Nat → Nat) (s : tm) :
    subst_tm (funcomp tm.var_tm ζ) (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by renamify

-- `auto_unfold` exposes the lifting helper's body (no σ-calculus rewriting):
example (σ : Nat → tm) :
    up_tm_tm σ = scons (tm.var_tm var_zero) (funcomp (ren_tm shift) σ) := by auto_unfold
example (σ : Nat → tm) (n : Nat) : up_tm_tm σ (n + 1) = ren_tm shift (σ n) := by auto_unfold; rfl

-- `renamify at h` / `auto_unfold at h` work on hypotheses too (free from `simp at`):
theorem renamify_at (ξ : Nat → Nat) (s t : tm) (h : subst_tm (funcomp tm.var_tm ξ) s = t) :
    ren_tm ξ s = t := by renamify at h; exact h

#axiom_clean substify_dir
#axiom_clean renamify_dir
#axiom_clean renamify_fuse
#axiom_clean renamify_at

end Renamify.Unscoped

/-! ## Well-scoped (`Fin`) -/
namespace Renamify.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  tm where
    | app : tm → tm → tm
    | lam : (bind tm in tm) → tm

theorem substify_dir {m n} (ξ : Fin m → Fin n) (s : tm m) :
    ren_tm ξ s = subst_tm (funcomp tm.var_tm ξ) s := by substify
theorem renamify_dir {m n} (ξ : Fin m → Fin n) (s : tm m) :
    subst_tm (funcomp tm.var_tm ξ) s = ren_tm ξ s := by renamify
theorem renamify_fuse {m n k} (ξ : Fin m → Fin n) (ζ : Fin n → Fin k) (s : tm m) :
    subst_tm (funcomp tm.var_tm ζ) (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by renamify

example {m n} (σ : Fin m → tm n) :
    up_tm_tm σ = scons (tm.var_tm var_zero) (funcomp (ren_tm shift) σ) := by auto_unfold

#axiom_clean substify_dir
#axiom_clean renamify_dir
#axiom_clean renamify_fuse

end Renamify.Scoped
