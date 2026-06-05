/-
# Integration case study: STLC **progress + preservation**.

A full type-soundness proof for the call-by-value simply-typed λ-calculus, built on the de Bruijn
syntax and substitution operations that `autosubst` generates from the `stlc.sig` spec. This is the
"is the generated output actually usable for real metatheory?" test: the renaming and substitution
typing lemmas, and the β case of preservation, are discharged using the generated
`ren_tm`/`subst_tm`/`up_tm_tm`/`upRen_tm_tm` (and their definitional `scons`/`shift` behavior) —
exactly as a user would. It extends the `Step.subst` snippet of `Examples/StlcDsl.lean` to the
standard soundness pair.

Contexts are `List ty`; a de Bruijn index `x` looks up `Γ[x]?`.
-/
import Tests.Support

namespace CaseStudy
open Autosubst

autosubst
  ty where
    | Base : ty
    | Fun  : ty → ty → ty
  tm where
    | app : tm → tm → tm
    | lam : ty → (bind tm in tm) → tm

/-! ## Reduction (call-by-value) and values. -/

/-- Values: λ-abstractions. -/
inductive Value : tm → Prop
  | lam (A s) : Value (tm.lam A s)

/-- Single-step call-by-value β-reduction. -/
inductive Step : tm → tm → Prop
  | beta (A s v) : Value v → Step (tm.app (tm.lam A s) v) (subst_tm (scons v tm.var_tm) s)
  | appL {s s' t} : Step s s' → Step (tm.app s t) (tm.app s' t)
  | appR {v t t'} : Value v → Step t t' → Step (tm.app v t) (tm.app v t')

/-! ## Typing. -/

/-- `HasType Γ e T`: term `e` has type `T` under context `Γ : List ty` (de Bruijn lookup `Γ[x]?`). -/
inductive HasType : List ty → tm → ty → Prop
  | var {Γ x A} : Γ[x]? = some A → HasType Γ (tm.var_tm x) A
  | app {Γ s t A B} : HasType Γ s (ty.Fun A B) → HasType Γ t A → HasType Γ (tm.app s t) B
  | lam {Γ A B s} : HasType (A :: Γ) s B → HasType Γ (tm.lam A s) (ty.Fun A B)

/-! ## Renaming preserves typing.

A renaming `ξ` carrying `Γ`-indices into `Δ` type-preservingly extends through a binder via the
generated `upRen_tm_tm`; the obligation on the extended contexts is pure `scons`/`shift` bookkeeping. -/

/-- `upRen_tm_tm` threads a type-preserving renaming through one extra binder. -/
theorem upRen_ok {Γ Δ : List ty} {ξ : Nat → Nat} {A : ty}
    (h : ∀ x B, Γ[x]? = some B → Δ[ξ x]? = some B) :
    ∀ x B, (A :: Γ)[x]? = some B → (A :: Δ)[upRen_tm_tm ξ x]? = some B := by
  intro x B hx
  cases x with
  | zero =>                       -- `upRen_tm_tm ξ 0 ≡ 0`
      show (A :: Δ)[0]? = some B
      simpa using hx
  | succ n =>                     -- `upRen_tm_tm ξ (n+1) ≡ ξ n + 1`
      show (A :: Δ)[ξ n + 1]? = some B
      simpa using h n B (by simpa using hx)

theorem ren_typing {Γ : List ty} {s : tm} {A : ty} (ht : HasType Γ s A) :
    ∀ {Δ : List ty} {ξ : Nat → Nat},
      (∀ x B, Γ[x]? = some B → Δ[ξ x]? = some B) → HasType Δ (ren_tm ξ s) A := by
  induction ht with
  | var hx => intro Δ ξ h; exact .var (h _ _ hx)
  | app _ _ ihs iht => intro Δ ξ h; exact .app (ihs h) (iht h)
  | lam _ ih => intro Δ ξ h; exact .lam (ih (upRen_ok h))

/-- Weakening: a well-typed term stays well-typed under one extra binder (`ren_tm shift`). -/
theorem weaken {Γ : List ty} {s : tm} {A B : ty} (ht : HasType Γ s A) :
    HasType (B :: Γ) (ren_tm shift s) A :=
  ren_typing ht (fun x C hx => by show (B :: Γ)[x + 1]? = some C; simpa using hx)

/-! ## Substitution preserves typing — built on weakening. -/

/-- `up_tm_tm` threads a type-preserving substitution through one extra binder. -/
theorem up_ok {Γ Δ : List ty} {σ : Nat → tm} {A : ty}
    (h : ∀ x B, Γ[x]? = some B → HasType Δ (σ x) B) :
    ∀ x B, (A :: Γ)[x]? = some B → HasType (A :: Δ) (up_tm_tm σ x) B := by
  intro x B hx
  cases x with
  | zero =>                       -- `up_tm_tm σ 0 ≡ var_tm 0`, looked up at the fresh `A`
      show HasType (A :: Δ) (tm.var_tm 0) B
      exact .var (by simpa using hx)
  | succ n =>                     -- `up_tm_tm σ (n+1) ≡ ren_tm shift (σ n)` — weaken the substitute
      show HasType (A :: Δ) (ren_tm shift (σ n)) B
      exact weaken (h n B (by simpa using hx))

theorem subst_typing {Γ : List ty} {s : tm} {A : ty} (ht : HasType Γ s A) :
    ∀ {Δ : List ty} {σ : Nat → tm},
      (∀ x B, Γ[x]? = some B → HasType Δ (σ x) B) → HasType Δ (subst_tm σ s) A := by
  induction ht with
  | var hx => intro Δ σ h; exact h _ _ hx
  | app _ _ ihs iht => intro Δ σ h; exact .app (ihs h) (iht h)
  | lam _ ih => intro Δ σ h; exact .lam (ih (up_ok h))

/-- The β-substitution lemma: substituting a `B`-typed term for de Bruijn 0. -/
theorem subst_zero {Γ : List ty} {s t : tm} {A B : ty}
    (hs : HasType (B :: Γ) s A) (ht : HasType Γ t B) :
    HasType Γ (subst_tm (scons t tm.var_tm) s) A := by
  refine subst_typing hs (fun x C hx => ?_)
  cases x with
  | zero =>                       -- `(t .: var) 0 ≡ t`
      have hBC : B = C := by simpa using hx
      subst hBC
      exact ht
  | succ n =>                     -- `(t .: var) (n+1) ≡ var n`
      show HasType Γ (tm.var_tm n) C
      exact .var (by simpa using hx)

/-! ## Soundness: preservation + progress. -/

/-- **Preservation** (subject reduction). The β case is exactly `subst_zero` on the generated
`subst_tm (v .: var_tm) s`. -/
theorem preservation {Γ : List ty} {e e' : tm} {T : ty}
    (ht : HasType Γ e T) (st : Step e e') : HasType Γ e' T := by
  induction ht generalizing e' with
  | var _ => cases st
  | app hs htt ihs iht =>
      cases st with
      | beta A s v _ => cases hs with | lam hb => exact subst_zero hb htt
      | appL h => exact .app (ihs h) htt
      | appR _ h => exact .app hs (iht h)
  | lam _ _ => cases st

/-- **Progress**: a well-typed term in the **empty** context is a value or can step. -/
theorem progress {e : tm} {T : ty} (ht : HasType [] e T) :
    Value e ∨ ∃ e', Step e e' := by
  generalize hΓ : ([] : List ty) = Γ at ht
  induction ht with
  | var hx => subst hΓ; simp at hx          -- no variables in the empty context
  | lam _ _ => exact .inl (.lam _ _)
  | app hs htt ihs iht =>
      subst hΓ
      rcases ihs rfl with hsv | ⟨s', hs'⟩
      · rcases iht rfl with htv | ⟨t', ht'⟩
        · cases hsv with | lam A u => exact .inr ⟨_, .beta A u _ htv⟩
        · exact .inr ⟨_, .appR hsv ht'⟩
      · exact .inr ⟨_, .appL hs'⟩

#axiom_clean ren_typing
#axiom_clean subst_typing
#axiom_clean preservation
#axiom_clean progress

end CaseStudy
