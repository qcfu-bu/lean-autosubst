/-
# Example: System F via the `autosubst` DSL, with `asimp`.

The multi-sorted counterpart of `StlcDsl.lean`: two substitution sorts (`ty`, `tm`) where `tm`
carries **both** type- and term-variables, so `subst_tm` threads two maps in parallel. Generated
from the HOAS spec by `autosubst`; metatheory proved by `by asimp`.
-/
import LeanAutosubst

open Autosubst Autosubst.Notation

namespace SysfDsl

autosubst
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

/-! ## Type-level substitution (single map) — written in the **notations**, closing with `asimp`.
`a[σ]` is type substitution; `t[σty;σtm]` is the genuine two-map term substitution; `[T/]` is the
explicit single-point β-substitution `T .: var` (replacing the old `instTy`/`instTm` aliases) — used
here as one component map of the two-map application. -/

example (s : ty) : s[ty.var_ty] = s := by asimp
example (σ τ : Nat → ty) (s : ty) : s[σ][τ] = s[σ >> [τ]] := by asimp

/-! ## Term-level substitution (two maps in parallel) — closes with `asimp`. -/

/-- Both component maps being the identity is the identity. -/
example (s : tm) : s[ty.var_ty;tm.var_tm] = s := by asimp

/-- Two parallel term-substitutions compose (the genuine two-map fusion). The composed term-map
has no single-symbol form (there is no two-map *function* notation `[σ;τ]`, only the subject form),
so it is written with `funcomp`. -/
example (σty τty : Nat → ty) (σtm τtm : Nat → tm) (s : tm) :
    s[σty;σtm][τty;τtm]
      = s[σty >> [τty]; funcomp (subst_tm τty τtm) σtm] := by asimp

/-! ## β-reduction identities for both binders. -/

/-- **Type β** (`tapp (tlam s) T`): `tlam` shifts the type index, then `[T/]` cancels it. -/
example (T : ty) (s : tm) : (s⟨↑;(id : Nat → Nat)⟩)[ [T/]; tm.var_tm] = s := by asimp

/-- **Term β** (`app (lam A s) t`): `lam` shifts the term index, then `[t/]` cancels it. -/
example (t s : tm) : (s⟨(id : Nat → Nat);↑⟩)[ty.var_ty; [t/] ] = s := by asimp

/-- The multi-sorted substitution lemma: a parallel substitution `(σty, σtm)` commutes past a
single term-variable instantiation. -/
example (σty : Nat → ty) (σtm : Nat → tm) (t s : tm) :
    (s[ty.var_ty; [t/] ])[σty;σtm]
      = (s[up_tm_ty σty;up_tm_tm σtm])[ty.var_ty; [t[σty;σtm]/] ] := by asimp

end SysfDsl
