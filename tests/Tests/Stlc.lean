/-
# Reference signature: `stlc.sig` — simply-typed λ-calculus (single substitution sort).

    ty : Type ; tm : Type
    Base : ty ; Fun : ty → ty → ty
    app  : tm → tm → tm
    lam  : ty → (bind tm in tm) → tm

Runs **both** backends (`autosubst` and `autosubst wellscoped`) and asserts: the lemma tower
typechecks, is axiom-clean (`{propext, Quot.sound}`), and the four representative `by asimp` goals
(identity, fusion, β-cancellation, substitution lemma) close.
-/
import Tests.Support

/-! ## Unscoped (`Nat`) -/
namespace Stlc.Unscoped
open Autosubst

autosubst
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

@[reducible] def inst (t : tm) : Nat → tm := scons t tm.var_tm

theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem ren_fusion (ξ ζ : Nat → Nat) (s : tm) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp
theorem beta_cancel (t s : tm) : subst_tm (inst t) (ren_tm shift s) = s := by asimp
theorem subst_lemma (σ : Nat → tm) (t s : tm) :
    subst_tm σ (subst_tm (inst t) s)
      = subst_tm (inst (subst_tm σ t)) (subst_tm (up_tm_tm σ) s) := by asimp

-- Axiom-clean: representative generated tower lemmas + the `asimp`-proved goals above.
#axiom_clean substSubst_tm   -- propext
#axiom_clean instId_tm       -- Quot.sound
#axiom_clean compSubstSubst_tm
#axiom_clean beta_cancel
#axiom_clean subst_lemma

end Stlc.Unscoped

/-! ## Well-scoped (`Fin`) -/
namespace Stlc.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

@[reducible] def inst {n} (t : tm n) : Fin (n + 1) → tm n := scons t tm.var_tm

theorem identity {n} (s : tm n) : subst_tm tm.var_tm s = s := by asimp
theorem subst_fusion {m n k} (σ : Fin m → tm n) (τ : Fin n → tm k) (s : tm m) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem ren_fusion {m n k} (ξ : Fin m → Fin n) (ζ : Fin n → Fin k) (s : tm m) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp
theorem beta_cancel {n} (t s : tm n) : subst_tm (inst t) (ren_tm shift s) = s := by asimp
theorem subst_lemma {m n} (σ : Fin m → tm n) (t : tm m) (s : tm (m + 1)) :
    subst_tm σ (subst_tm (inst t) s)
      = subst_tm (inst (subst_tm σ t)) (subst_tm (up_tm_tm σ) s) := by asimp

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean beta_cancel
#axiom_clean subst_lemma

end Stlc.Scoped

/-! ## `stlc-unicode.sig` — unicode identifiers.

DSL identifiers are exactly **Lean identifiers**: any unicode Lean's lexer accepts (Greek `φ`,
subscripts, primes, …) works as a sort/constructor name. The reference signature's specific names
can't be ported verbatim, though — both are Lean lexical limitations, not `autosubst` ones:
`λ` is a **reserved token** (the lambda binder), and katakana `アップ` is **not a Lean letter**.
We use a Greek `φ` constructor to show unicode names work; generated names (`subst_tm`, …) are
ASCII per the §3 contract regardless. -/
namespace Stlc.Unicode
open Autosubst

autosubst
  tm where
    | φ   : tm → tm → tm
    | lam : (bind tm in tm) → tm

example : tm → tm → tm := tm.φ

theorem beta_cancel (t s : tm) :
    subst_tm (scons t tm.var_tm) (ren_tm shift s) = s := by asimp

#axiom_clean substSubst_tm
#axiom_clean beta_cancel

end Stlc.Unicode
