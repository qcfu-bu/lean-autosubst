/-
# Example: STLC via the `autosubst` DSL, with `asimp`.

Unlike `Examples/Stlc.lean` (which hand-writes the de Bruijn syntax and its whole lemma tower
as the generator's *golden target*), this file uses the actual `autosubst` command to *generate*
everything from a native-Lean HOAS spec, then proves substitution metatheory with `by asimp`.
-/
import Autosubst

open Autosubst Autosubst.Notation

namespace StlcDsl

-- The signature. `lam` binds a `tm` variable in its body — that's the whole HOAS spec.
autosubst
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

/-! ## Basic substitution algebra — written in the Autosubst-consistent **notations**
(`s[σ]` substitution, `s⟨ξ⟩` renaming, `↑` shift), every goal closing with `asimp`. The explicit
finite substitution `[a, b, …/]` (`= a .: b .: … .: var_tm`, the `/` marking it a substitution)
replaces the old ad-hoc `inst` alias; `s[t/]` is the β-instantiation. The application notations
dispatch through the generated `Subst1`/`Ren1`/`Var` instances. -/

/-- The identity substitution does nothing. -/
example (s : tm) : s[tm.var_tm] = s := by asimp

/-- Substitutions compose. -/
example (σ τ : Nat → tm) (s : tm) : s[σ][τ] = s[σ >> [τ]] := by asimp

/-- Renamings compose. -/
example (ξ ζ : Nat → Nat) (s : tm) : s⟨ξ⟩⟨ζ⟩ = s⟨ξ >> ζ⟩ := by asimp

/-- A renaming by the identity is the identity. (`id` needs its type pinned for the `Ren1`
dispatch — it is the one map whose type `Nat → Nat` is not fixed by a prior occurrence.) -/
example (s : tm) : s⟨(id : Nat → Nat)⟩ = s := by asimp

/-- **β cancels a shift**: weakening then instantiating the fresh variable is the identity.
This is the workhorse equation behind `(λ. s) t → s[t/]` reasoning. -/
example (t s : tm) : (s⟨↑⟩)[t/] = s := by asimp

/-- **The substitution lemma** (the key step in preservation): pushing a substitution `σ` past a
single-variable instantiation — `(s[t/])[σ] = (s[⇑σ])[t[σ]/]`. `⇑σ` is the binder lift `up_tm_tm σ`
(available as `⇑` here because `tm` is the lone open sort, so the binder sort is forced). -/
example (σ : Nat → tm) (t s : tm) :
    (s[t/])[σ] = (s[⇑σ])[t[σ]/] := by asimp

/-! ## A small reduction relation, to show the generated lemmas are usable. -/

/-- One-step (full) β-reduction. -/
inductive Step : tm → tm → Prop
  | beta (A : ty) (s t : tm) : Step (tm.app (tm.lam A s) t) (s[t..])
  | appL {s s' t} : Step s s' → Step (tm.app s t) (tm.app s' t)
  | appR {s t t'} : Step t t' → Step (tm.app s t) (tm.app s t')
  | lam  {A s s'} : Step s s' → Step (tm.lam A s) (tm.lam A s')

/-- β-reduction is stable under substitution. The `beta` case is exactly the substitution lemma
above — `asimp` discharges the de Bruijn bookkeeping; the rest is congruence. -/
theorem Step.subst {s s'} (σ : Nat → tm) (h : Step s s') :
    Step (s[σ]) (s'[σ]) := by
  induction h generalizing σ with
  | beta A s t =>
      have e : (s[t..])[σ] = (s[up_tm_tm σ])[(t[σ])..] := by asimp
      rw [e]
      exact Step.beta A (s[up_tm_tm σ]) (t[σ])
  | appL _ ih => exact Step.appL (ih σ)
  | appR _ ih => exact Step.appR (ih σ)
  | lam _ ih  => exact Step.lam (ih (up_tm_tm σ))

end StlcDsl
