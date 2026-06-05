/-
# User containers, recognised **on demand** (plan.md §4a).

A user nests their **own inductive** in a constructor position and substitution threads through it —
with **nothing to write**: no registration, no attribute, no `deriving`. When `autosubst` sees a head
`(F …)` whose `F` is a regular polynomial functor (each constructor argument is the type parameter, a
recursive occurrence, or a parameter-free type), it reads `F`'s constructors directly and emits a
structural helper `subst_tm_F` + a derived congruence `congrC_F_<ctor>`. `List`/`Option`/`Prod` are
not special — they are recognised by the same on-demand check (`Prod` threaded inline; see
`Tests/Containers.lean`); a non-functor head like `cod` is rejected with a clear error
(`Tests/Unsupported.lean`).

Asserts: the generated tower (through a user container) is axiom-clean and defeq to the structural
golden ([Examples/Container.lean]); `by asimp` goals close.
-/
import Tests.Support

/-! ## A user container: a binary tree, used as a container with no markup at all. -/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

namespace UserContainer.Basic
open Autosubst

autosubst
  tm where
    | app    : tm → tm → tm
    | branch : (Tree tm) → tm           -- substitution threads through `Tree` — on demand
    | lam    : (bind tm in tm) → tm

-- defeq to the structural golden (the helper recurses leaf/node as a hand write would):
example (σ : Nat → tm) (l r : tm) :
    subst_tm σ (tm.branch (Tree.node (Tree.leaf l) (Tree.leaf r)))
      = tm.branch (Tree.node (Tree.leaf (subst_tm σ l)) (Tree.leaf (subst_tm σ r))) := rfl
example (σ : Nat → tm) (t : Tree tm) :
    subst_tm σ (tm.branch t) = tm.branch (subst_tm_Tree σ t) := rfl

theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem ren_fusion (ξ ζ : Nat → Nat) (s : tm) :
    ren_tm ζ (ren_tm ξ s) = ren_tm (funcomp ζ ξ) s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
theorem beta_cancel (t s : tm) : subst_tm (scons t tm.var_tm) (ren_tm shift s) = s := by asimp

#axiom_clean subst_tm_Tree
#axiom_clean idSubst_tm_Tree
#axiom_clean compSubstSubst_tm_Tree
#axiom_clean substSubst_tm
#axiom_clean identity
#axiom_clean subst_fusion
#axiom_clean beta_cancel

end UserContainer.Basic

/-! ## A nested user container (`Tree (Prod tm tm)`) — composes with the inline `Prod`. -/
namespace UserContainer.Nested
open Autosubst

autosubst
  tm where
    | app   : tm → tm → tm
    | pairs : (Tree (Prod tm tm)) → tm
    | lam   : (bind tm in tm) → tm

example (σ : Nat → tm) (a b : tm) :
    subst_tm σ (tm.pairs (Tree.leaf (a, b))) = tm.pairs (Tree.leaf (subst_tm σ a, subst_tm σ b)) := rfl

theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
#axiom_clean subst_fusion

end UserContainer.Nested
