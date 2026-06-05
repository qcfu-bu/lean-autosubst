/-
# Example: Option / Prod / nested containers via `autosubst` (Phase 9).

Exercises the full container repertoire in one sort: `Option tm`, `tm × tm` (binary `Prod`,
handled inline), a `List (tm × tm)` nesting, and a binder into a container. `autosubst` generates
the mutual structural helpers (none/some for `Option`, nil/cons for `List`, projections for
`Prod`) and the whole lemma tower; `by asimp` closes the substitution metatheory.
-/
import LeanAutosubst

open Autosubst

namespace ContainerMix

autosubst
  tm where
    | app : tm → tm → tm
    | opt : (Option tm) → tm
    | pr  : (Prod tm tm) → tm
    | brs : (List (Prod tm tm)) → tm
    | bnd : (bind tm in (Option tm)) → tm

@[reducible] def inst (t : tm) : Nat → tm := scons t tm.var_tm

/-! ## Substitution algebra through Option / Prod / nested containers — all close with `asimp`. -/

example (s : tm) : subst_tm tm.var_tm s = s := by asimp

example (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp

example (ξ ζ : Nat → Nat) (s : tm) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp

example (s : tm) : ren_tm id s = s := by asimp

example (t s : tm) : subst_tm (inst t) (ren_tm shift s) = s := by asimp

/-- The substitution lemma, through the `bnd` binder-into-`Option`. -/
example (σ : Nat → tm) (t s : tm) :
    subst_tm σ (subst_tm (inst t) s)
      = subst_tm (inst (subst_tm σ t)) (subst_tm (up_tm_tm σ) s) := by asimp

end ContainerMix
