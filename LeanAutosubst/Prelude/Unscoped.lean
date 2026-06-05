/-
Port of Autosubst 2's `unscoped.v` runtime prelude (the `Nat`-variable backend).

Reference: rocq/autosubst2-ocaml/share/coq-autosubst-ocaml/unscoped.v

Primitives of the sigma calculus over `Nat` de Bruijn indices: `var_zero`, `shift`,
`scons` (cons onto a substitution/renaming), generic lifting `up_ren`, and the
`scons` eta / composition laws that the `asimpl` normal form relies on.

We give the laws in both pointwise and funext-based extensional forms; the
extensional forms are what the generated "clean" lemmas and `asimpl` consume.
-/
import LeanAutosubst.Prelude.Core

namespace Autosubst

/-- The freshly bound variable. -/
@[reducible] def var_zero : Nat := 0

/-- The shift renaming `n ↦ n+1`. -/
@[reducible] def shift : Nat → Nat := Nat.succ

/-- Extend a map `Nat → X` with a new value at index `0`, shifting the rest up.
Autosubst notation `x .: f`. -/
def scons {X : Sort _} (x : X) (f : Nat → X) : Nat → X
  | 0 => x
  | n + 1 => f n

@[inherit_doc] scoped infixr:55 " .: " => scons

@[simp] theorem scons_zero {X : Sort _} (x : X) (f : Nat → X) : (x .: f) 0 = x := rfl
@[simp] theorem scons_succ {X : Sort _} (x : X) (f : Nat → X) (n : Nat) :
    (x .: f) (n + 1) = f n := rfl

/-- Generic lifting of a renaming under one binder. -/
@[reducible] def up_ren (xi : Nat → Nat) : Nat → Nat :=
  scons var_zero (funcomp shift xi)

/-- Lifting of renamings composes (pointwise). -/
theorem up_ren_ren (xi zeta rho : Nat → Nat) (e : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (up_ren zeta) (up_ren xi) x = up_ren rho x
  | 0 => rfl
  | n + 1 => by simp [up_ren, funcomp, scons, ← e n]

/-! ## scons eta and composition laws -/

theorem scons_eta_pointwise {T : Sort _} (f : Nat → T) :
    ∀ x, (scons (f var_zero) (funcomp f shift)) x = f x
  | 0 => rfl
  | _ + 1 => rfl

theorem scons_eta {T : Sort _} (f : Nat → T) :
    scons (f var_zero) (funcomp f shift) = f :=
  funext (scons_eta_pointwise f)

theorem scons_eta_id_pointwise : ∀ x, (scons var_zero shift) x = id x
  | 0 => rfl
  | _ + 1 => rfl

theorem scons_eta_id : scons var_zero shift = id :=
  funext scons_eta_id_pointwise

theorem scons_comp_pointwise {T : Sort _} {U : Sort _} (s : T) (sigma : Nat → T) (tau : T → U) :
    ∀ x, funcomp tau (scons s sigma) x = (scons (tau s) (funcomp tau sigma)) x
  | 0 => rfl
  | _ + 1 => rfl

theorem scons_comp {T : Sort _} {U : Sort _} (s : T) (sigma : Nat → T) (tau : T → U) :
    funcomp tau (scons s sigma) = scons (tau s) (funcomp tau sigma) :=
  funext (scons_comp_pointwise s sigma tau)

/-- `(x .: f) ∘ shift = f` (Coq's `shift >> (x .: g) = g`). -/
theorem scons_shift {X : Sort _} (x : X) (f : Nat → X) : funcomp (scons x f) shift = f := rfl

end Autosubst
