/-
# Example: well-scoped STLC via `autosubst wellscoped`, with `asimp`.

The scoped counterpart of [StlcDsl.lean](StlcDsl.lean): the same HOAS spec, but the
`wellscoped` modifier makes the generator emit `Fin`-indexed de Bruijn syntax
(`tm : Nat → Type`, `var_tm : Fin n → tm n`, `lam : ty → tm (n+1) → tm n`) with `ren`/`subst`
threading `Fin m → Fin n` / `Fin m → tm n` maps — matching [StlcScoped.lean](StlcScoped.lean).
-/
import LeanAutosubst

open Autosubst Autosubst.Scoped Autosubst.Scoped.Notation

namespace StlcScopedDsl

autosubst wellscoped
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

-- The generated syntax is scope-indexed, exactly as in the golden.
section
  variable {n : Nat}
  example : Fin n → tm n := tm.var_tm
  example : tm n → tm n → tm n := tm.app
  example : ty → tm (n + 1) → tm n := tm.lam
  example {m : Nat} : (Fin m → Fin n) → tm m → tm n := ren_tm
  example {m : Nat} : (Fin m → tm n) → tm m → tm n := subst_tm
end

-- **Generated ≡ golden by `rfl`**: the emitted `ren`/`subst`/`up` reduce *definitionally* exactly
-- as the hand-written golden ([StlcScoped.lean]) — the de Bruijn equations hold by `rfl`.
section
  variable {m n : Nat} (xi : Fin m → Fin n) (σ : Fin m → tm n) (x : Fin m)
           (A : ty) (s t : tm m) (b : tm (m + 1))
  example : ren_tm xi (tm.var_tm x) = tm.var_tm (xi x) := rfl
  example : ren_tm xi (tm.app s t) = tm.app (ren_tm xi s) (ren_tm xi t) := rfl
  example : ren_tm xi (tm.lam A b) = tm.lam A (ren_tm (upRen_tm_tm xi) b) := rfl
  example : subst_tm σ (tm.var_tm x) = σ x := rfl
  example : subst_tm σ (tm.app s t) = tm.app (subst_tm σ s) (subst_tm σ t) := rfl
  example : subst_tm σ (tm.lam A b) = tm.lam A (subst_tm (up_tm_tm σ) b) := rfl
  example : up_tm_tm σ = scons (tm.var_tm var_zero) (funcomp (ren_tm shift) σ) := rfl
end

/-! ## Basic substitution algebra — in the Autosubst-consistent **notations** (`s[σ]`/`s⟨ξ⟩`/`↑`/
`t..`), every goal closing with `asimp`.

Well-scoped caveat: the dispatch notations key on the subject sort *and the map type*; a
*polymorphic* scoped constant (`↑`, `tm.var_tm`, whose scope is a metavar at the use site) therefore
needs a one-off type ascription — concrete map variables (`σ`, `ξ`) never do. (In the unscoped
backend no ascription is ever needed; see [StlcDsl.lean].) -/

example {n} (s : tm n) : s[(tm.var_tm : Fin n → tm n)] = s := by asimp

example {m n k} (σ : Fin m → tm n) (τ : Fin n → tm k) (s : tm m) :
    s[σ][τ] = s[σ >> [τ]] := by asimp

example {m n k} (ξ : Fin m → Fin n) (ζ : Fin n → Fin k) (s : tm m) :
    s⟨ξ⟩⟨ζ⟩ = s⟨ξ >> ζ⟩ := by asimp

example {n} (s : tm n) : s⟨(id : Fin n → Fin n)⟩ = s := by asimp

/-- **β cancels a shift**: weakening then instantiating the fresh variable is the identity. The
explicit substitution `[t/]` (`= t .: var`) is the well-scoped β-substitution; its `var`-tail scope
is ascribed (the scoped polymorphic-constant caveat). -/
example {n} (t s : tm n) :
    (s⟨(↑ : Fin n → Fin (n+1))⟩)[([t/] : Fin (n+1) → tm n)] = s := by asimp

/-- **The substitution lemma** `(s[t/])[σ] = (s[⇑σ])[t[σ]/]`. `⇑σ` is the binder lift `up_tm_tm σ`
(the lone open sort `tm` forces the binder sort). -/
example {m n} (σ : Fin m → tm n) (t : tm m) (s : tm (m + 1)) :
    (s[([t/] : Fin (m+1) → tm m)])[σ]
      = (s[⇑σ])[([t[σ]/] : Fin (n+1) → tm n)] := by asimp

/-! ## β-reduction stable under substitution (uses the substitution lemma). -/

inductive Step : {n : Nat} → tm n → tm n → Prop
  | beta {n} (A : ty) (s : tm (n + 1)) (t : tm n) :
      Step (tm.app (tm.lam A s) t) (s[([t/] : Fin (n+1) → tm n)])
  | appL {n} {s s' t : tm n} : Step s s' → Step (tm.app s t) (tm.app s' t)
  | appR {n} {s t t' : tm n} : Step t t' → Step (tm.app s t) (tm.app s t')
  | lam  {n} {A} {s s' : tm (n + 1)} : Step s s' → Step (tm.lam A s) (tm.lam A s')

theorem Step.subst {m n} {s s' : tm m} (σ : Fin m → tm n) (h : Step s s') :
    Step (s[σ]) (s'[σ]) := by
  induction h generalizing n with
  | @beta k A s t =>
      have e : (s[([t/] : Fin (k+1) → tm k)])[σ]
             = (s[⇑σ])[([t[σ]/] : Fin (n+1) → tm n)] := by asimp
      rw [e]
      exact Step.beta A (s[up_tm_tm σ]) (t[σ])
  | appL _ ih => exact Step.appL (ih σ)
  | appR _ ih => exact Step.appR (ih σ)
  | lam _ ih  => exact Step.lam (ih (up_tm_tm σ))

end StlcScopedDsl
