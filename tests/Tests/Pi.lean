/-
# Reference signature: `pi.sig` — the π-calculus (a pure **name** sort + a **nullary** constructor).

    chan : Type ; proc : Type
    Nil  : proc                          -- nullary
    Bang : proc → proc
    Res  : (bind chan in proc) → proc
    Par  : proc → proc → proc
    In   : chan → (bind chan in proc) → proc
    Out  : chan → chan → proc → proc

Exercises two edge cases at once: `chan` is a **variable-only sort** (no user constructors — only
`var_chan`; it is bound by `Res`/`In`), and `proc` is a sort that *substitutes* (`chan`-variables)
yet is **not open** (no `var_proc`) and has a **nullary** constructor `Nil`. Both backends.
-/
module

public import Tests.Support

@[expose] public section

/-! ## Unscoped -/
namespace Pi.Unscoped
open Autosubst

autosubst
  chan where
  proc where
    | Nil  : proc
    | Bang : proc → proc
    | Res  : (bind chan in proc) → proc
    | Par  : proc → proc → proc
    | In   : chan → (bind chan in proc) → proc
    | Out  : chan → chan → proc → proc

-- `chan` has only `var_chan`; `proc` substitutes a `chan`-map but has no `var_proc`.
example : Nat → chan := chan.var_chan
example : proc := proc.Nil
example : (Nat → chan) → proc → proc := subst_proc

theorem proc_identity (s : proc) : subst_proc chan.var_chan s = s := by asimp
theorem proc_fusion (σ τ : Nat → chan) (s : proc) :
    subst_proc τ (subst_proc σ s) = subst_proc (funcomp (subst_chan τ) σ) s := by asimp
-- β through `Res` (which binds a `chan`): weaken the channel, then instantiate the fresh one.
theorem proc_beta (c : chan) (s : proc) :
    subst_proc (scons c chan.var_chan) (ren_proc shift s) = s := by asimp

#axiom_clean substSubst_proc   -- covers the nullary `Nil` case
#axiom_clean instId_proc
#axiom_clean proc_fusion
#axiom_clean proc_beta

end Pi.Unscoped

/-! ## Well-scoped -/
namespace Pi.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  chan where
  proc where
    | Nil  : proc
    | Bang : proc → proc
    | Res  : (bind chan in proc) → proc
    | Par  : proc → proc → proc
    | In   : chan → (bind chan in proc) → proc
    | Out  : chan → chan → proc → proc

theorem proc_identity {n} (s : proc n) : subst_proc chan.var_chan s = s := by asimp
theorem proc_fusion {m n k} (σ : Fin m → chan n) (τ : Fin n → chan k) (s : proc m) :
    subst_proc τ (subst_proc σ s) = subst_proc (funcomp (subst_chan τ) σ) s := by asimp
theorem proc_beta {n} (c : chan n) (s : proc n) :
    subst_proc (scons c chan.var_chan) (ren_proc shift s) = s := by asimp

#axiom_clean substSubst_proc
#axiom_clean instId_proc
#axiom_clean proc_beta

end Pi.Scoped
