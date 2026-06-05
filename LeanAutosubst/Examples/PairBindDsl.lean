/-
# Example: simultaneous binding of two variables (pair / Σ-type elimination).

Tuple/record pattern matching and Σ-type elimination bind **two variables at once**:
`split p t` ≡ `let (x, y) = p in t` makes both projections of `p` available in the body `t`,
so `t` lives under *two* binders simultaneously. In the `autosubst` DSL this is a single
constructor position carrying two binders — `(bind tm, tm in tm)` — and substitution therefore
lifts **twice** (`up ∘ up`) when it descends into `t`.

We show it in both backends: unscoped (`Nat`) and well-scoped (`Fin`, where the body's scope
visibly jumps by two: `tm n → tm (n+2) → tm n`). In each, the de Bruijn equation holds by `rfl`
and the β / substitution-lemma bookkeeping clears with `asimp`.
-/
import LeanAutosubst

open Autosubst

/-! ## Unscoped -/

namespace PairBind
open scoped Autosubst  -- for `.:`

autosubst
  tm where
    | pair  : tm → tm → tm
    | fst   : tm → tm
    | snd   : tm → tm
    | split : tm → (bind tm, tm in tm) → tm   -- `let (x, y) = · in ·`

-- Binders are erased in the de Bruijn image: `split`'s body is a plain `tm` (two extra slots).
example : tm → tm → tm := tm.split

/-- Instantiate the two simultaneously-bound variables: `x ↦ a`, `y ↦ b`. -/
@[reducible] def inst2 (a b : tm) : Nat → tm := a .: b .: tm.var_tm

/-- Substitution descends into `split`'s body with a **double lift** — definitionally. -/
example (σ : Nat → tm) (e t : tm) :
    subst_tm σ (tm.split e t) = tm.split (subst_tm σ e) (subst_tm (up_tm_tm (up_tm_tm σ)) t) := rfl

/-- β for pair elimination, `split (pair a b) t ↦ t[x:=a, y:=b]`: weakening the body past the two
fresh binders and then instantiating both is the identity. -/
example (a b t : tm) :
    subst_tm (inst2 a b) (ren_tm shift (ren_tm shift t)) = t := by asimp

/-- The substitution lemma pushed past a two-variable instantiation. -/
example (σ : Nat → tm) (a b t : tm) :
    subst_tm σ (subst_tm (inst2 a b) t)
      = subst_tm (inst2 (subst_tm σ a) (subst_tm σ b)) (subst_tm (up_tm_tm (up_tm_tm σ)) t) := by
  asimp

end PairBind

/-! ## Well-scoped — the body's scope visibly increases by two. -/

namespace PairBindScoped
open Autosubst.Scoped

autosubst wellscoped
  tm where
    | pair  : tm → tm → tm
    | fst   : tm → tm
    | snd   : tm → tm
    | split : tm → (bind tm, tm in tm) → tm

-- The two simultaneous binders bump the body's scope by two: `tm (n+1+1)`.
example {n} : tm n → tm (n + 1 + 1) → tm n := tm.split

/-- Instantiate the two bound variables (scoped). -/
@[reducible] def inst2 {n} (a b : tm n) : Fin (n + 1 + 1) → tm n := scons a (scons b tm.var_tm)

/-- Double lift, definitionally. -/
example {m n} (σ : Fin m → tm n) (e : tm m) (t : tm (m + 1 + 1)) :
    subst_tm σ (tm.split e t) = tm.split (subst_tm σ e) (subst_tm (up_tm_tm (up_tm_tm σ)) t) := rfl

/-- β cancels a double weakening. -/
example {n} (a b t : tm n) :
    subst_tm (inst2 a b) (ren_tm shift (ren_tm shift t)) = t := by asimp

/-- The substitution lemma, scoped. -/
example {m n} (σ : Fin m → tm n) (a b : tm m) (t : tm (m + 1 + 1)) :
    subst_tm σ (subst_tm (inst2 a b) t)
      = subst_tm (inst2 (subst_tm σ a) (subst_tm σ b)) (subst_tm (up_tm_tm (up_tm_tm σ)) t) := by
  asimp

end PairBindScoped
