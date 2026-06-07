/-
# Example: a nested-container binder via the `autosubst` DSL (Phase 9).

The generated counterpart of the hand-written golden [Examples/Container.lean]: a sort `tm`
whose `seq`/`lam` constructors carry a `List tm` (a container, with `lam` binding into it).
`autosubst` generates the mutual `ren`/`subst` + `*_list` helpers and the whole lemma tower;
substitution metatheory is proved by `by asimp`.
-/
import Autosubst

open Autosubst

namespace ContainerDsl

autosubst
  tm where
    | app : tm → tm → tm
    | seq : (List tm) → tm
    | lam : (bind tm in (List tm)) → tm

/-- Single-variable instantiation `s[t]`. -/
@[reducible] def inst (t : tm) : Nat → tm := scons t tm.var_tm

/-! ## Substitution algebra — closes with `asimp`. -/

example (s : tm) : subst_tm tm.var_tm s = s := by asimp

example (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp

example (ξ ζ : Nat → Nat) (s : tm) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp

example (s : tm) : ren_tm id s = s := by asimp

/-- β cancels a shift, threaded through the `lam`/`seq` containers. -/
example (t s : tm) : subst_tm (inst t) (ren_tm shift s) = s := by asimp

/-- The substitution lemma. -/
example (σ : Nat → tm) (t s : tm) :
    subst_tm σ (subst_tm (inst t) s)
      = subst_tm (inst (subst_tm σ t)) (subst_tm (up_tm_tm σ) s) := by asimp

end ContainerDsl
