/-
# Container edge cases — regression tests for the generic-container substitution generator.

These pin the behavior of an audit's worth of edge cases in container recognition / lemma
generation. Each was previously broken (a `sorryAx`-tainted tower, a kernel error, a duplicate
declaration, a wrong-shape mismatch, or a misleading decline); they are pinned here so the suite
breaks if any regresses. Two groups:

* **Positive** — inputs that must generate a *correct, axiom-clean* tower (asserted via the user
  theorems being `#axiom_clean`, which transitively covers the whole generated tower).
* **Declines** — out-of-scope inputs that must fail with one *clean, deliberate* error (pinned with
  `#guard_msgs`), never a kernel error / `sorry` / cascade.
-/
import Tests.Support

namespace ContainerEdgeCases
open Autosubst

/-! ## Positive: inputs that must produce a correct, axiom-clean tower. -/

/-! Bare `Prod` constructor position: `asimp` must push through it (the push lemma no longer
references a nonexistent `subst_<s>_prod` helper). -/
namespace BareProd
autosubst
  tm where
    | pr  : (Prod tm tm) → tm
    | lam : (bind tm in tm) → tm
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem subst_fusion (σ τ : Nat → tm) (s : tm) :
    subst_tm τ (subst_tm σ s) = subst_tm (funcomp (subst_tm τ) σ) s := by asimp
example (σ : Nat → tm) (a b : tm) :
    subst_tm σ (tm.pr (a, b)) = tm.pr (subst_tm σ a, subst_tm σ b) := by asimp
#axiom_clean identity
#axiom_clean subst_fusion
end BareProd

/-! A recognised container at a foreign-only instantiation (`List Nat`, `MyBox Nat`): substitution
carries it unchanged (no call to an undefined helper, no `sorry`). -/
namespace ForeignOnly
inductive MyBox (α : Type) where | mk : α → MyBox α
autosubst
  tm where
    | ns  : (MyBox Nat) → tm
    | lst : (List Nat) → tm
    | lam : (bind tm in tm) → tm
example (σ : Nat → tm) (b : MyBox Nat) : subst_tm σ (tm.ns b) = tm.ns b := rfl
example (σ : Nat → tm) (l : List Nat) : subst_tm σ (tm.lst l) = tm.lst l := rfl
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end ForeignOnly

/-! The same container at two different element sorts in one enclosing sort (`List ty` + `List tm`):
distinct helper names, no collision. -/
namespace SameContainerTwoSorts
autosubst
  ty where
    | base : ty
    | tarr : ty → ty → ty
  tm where
    | mix  : (List ty) → (List tm) → tm
    | lam  : (bind tm in tm) → tm
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end SameContainerTwoSorts

/-! Two distinct containers sharing a final name component (`A.Box`, `B.Box`): distinct helper
names, no duplicate declarations. -/
namespace DistinctNamespaces
namespace A
inductive Box (α : Type) where | mk : α → Box α
end A
namespace B
inductive Box (α : Type) where | wrap : α → Box α → Box α | nil : Box α
end B
autosubst
  tm where
    | boxa : (A.Box tm) → tm
    | boxb : (B.Box tm) → tm
    | lam  : (bind tm in tm) → tm
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end DistinctNamespaces

/-! A container reached through `open` is recognised, not declined. -/
namespace OpenedContainer
namespace Lib
inductive MyBox (α : Type) where | mk : α → MyBox α
end Lib
open Lib
autosubst
  tm where
    | box : (MyBox tm) → tm
    | lam : (bind tm in tm) → tm
example (σ : Nat → tm) (s : tm) :
    subst_tm σ (tm.box (MyBox.mk s)) = tm.box (MyBox.mk (subst_tm σ s)) := rfl
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end OpenedContainer

/-! Two `autosubst` commands in one namespace both using `List`: the (signature-independent)
container congruence is emitted once and reused, not re-declared. -/
namespace TwoCommands
autosubst
  tm where
    | seq : (List tm) → tm
    | lam : (bind tm in tm) → tm
autosubst
  ty where
    | tseq : (List ty) → ty
    | tall : (bind ty in ty) → ty
theorem tm_id (s : tm) : subst_tm tm.var_tm s = s := by asimp
theorem ty_id (s : ty) : subst_ty ty.var_ty s = s := by asimp
#axiom_clean tm_id
#axiom_clean ty_id
end TwoCommands

/-! `set_option autoImplicit false` (mathlib's default) must not break the container congruence. -/
namespace AutoImplicitFalse
set_option autoImplicit false
inductive MyBox (α : Type) where | mk : α → MyBox α
autosubst
  tm where
    | box : (MyBox tm) → tm
    | lam : (bind tm in tm) → tm
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end AutoImplicitFalse

/-! A container whose elements are a *closed* (non-substitutable) sort: the helper lemmas must not
over-solve (no spurious "No goals to be solved"). -/
namespace ContainerOverClosedSort
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
autosubst
  ty where
    | base : ty
    | arr  : ty → ty → ty
  tm where
    | ann  : (Tree ty) → tm → tm
    | lam  : (bind tm in tm) → tm
theorem identity (s : tm) : subst_tm tm.var_tm s = s := by asimp
#axiom_clean identity
end ContainerOverClosedSort

/-! ## Declines: out-of-scope inputs that must fail with one clean, deliberate error. -/

namespace DeclineProp
inductive PropBox (α : Type) : Prop | mk : α → PropBox α
/-- error: Cannot thread substitution through container head 'PropBox' in constructor 'box' of sort 'tm': 'PropBox' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (PropBox tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineProp

namespace DeclineIndexed
inductive Idx (α : Type) : Bool → Type | yes : α → Idx α true | no : Nat → Idx α false
/-- error: Cannot thread substitution through container head 'Idx' in constructor 'box' of sort 'tm': 'Idx' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (Idx tm b) → tm
    | lam : (bind tm in tm) → tm
end DeclineIndexed

namespace DeclineZeroCtor
inductive VoidBox (α : Type) : Type
/-- error: Cannot thread substitution through container head 'VoidBox' in constructor 'box' of sort 'tm': 'VoidBox' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (VoidBox tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineZeroCtor

namespace DeclineImplicitArg
inductive IBox (α : Type) where | mk : {_n : Nat} → α → IBox α
/-- error: Cannot thread substitution through container head 'IBox' in constructor 'box' of sort 'tm': 'IBox' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (IBox tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineImplicitArg

namespace DeclineDependentArg
inductive Dep (α : Type) where | mk : (n : Nat) → (Fin n) → α → Dep α
/-- error: Cannot thread substitution through container head 'Dep' in constructor 'box' of sort 'tm': 'Dep' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (Dep tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineDependentArg

namespace DeclinePhantomParam
inductive Ph (α β : Type) where | mk : α → Ph α β
/-- error: Cannot thread substitution through container head 'Ph' in constructor 'box' of sort 'tm': 'Ph' must be `Prod` or an inductive regular in its type parameters, whose constructor arguments use parameters only as elements, uniform recursive occurrences, or not at all (a List/Option/Tree/PairBox-like regular functor). Function-space or non-regular types (like `cod`) are unsupported. -/
#guard_msgs in
autosubst
  tm where
    | box : (Ph tm Nat) → tm
    | lam : (bind tm in tm) → tm
end DeclinePhantomParam

namespace DeclineUnderApplied
inductive P2 (α β : Type) where | mk : α → β → P2 α β
/-- error: Container head 'P2' in constructor 'box' of sort 'tm' is applied to 1 argument(s), but 'P2' takes 2 type parameter(s); a container must be fully applied to its parameters. -/
#guard_msgs in
autosubst
  tm where
    | box : (P2 tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineUnderApplied

namespace DeclineSortAsHead
/-- error: Sort 'ty' is applied to 1 argument(s) in constructor 'bad' of sort 'tm', but 'ty' declares only 0 parameter(s). A declared sort cannot be used as a container head; only `Prod` or an inductive regular in its type parameters can. -/
#guard_msgs in
autosubst
  ty where
    | base : ty
  tm where
    | bad : (ty tm) → tm
    | lam : (bind tm in tm) → tm
end DeclineSortAsHead

namespace DeclineScopedContainer
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α
/-- error: Cannot thread substitution through container head 'Tree' in constructor 'branch' of sort 'tm': in well-scoped mode a container wrapping a scope-indexed sort lowers to a kernel-rejected nested inductive. Use unscoped mode for container positions over open sorts, or keep the container's elements in a closed (variable-free) sort. -/
#guard_msgs in
autosubst wellscoped
  tm where
    | branch : (Tree tm) → tm
    | lam    : (bind tm in tm) → tm
end DeclineScopedContainer

end ContainerEdgeCases
