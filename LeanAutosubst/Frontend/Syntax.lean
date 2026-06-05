/-
# Phase 2 — Native-inductive HOAS surface syntax.

The user writes what *reads* like (mutual) Lean inductives, with binders marked by a
`bind … in …` annotation. The whole block is captured as `Syntax` and intercepted
([Frontend/Elab.lean]) — it is **never** elaborated as an inductive, so strict positivity is
never invoked on the HOAS form; only the lowered de Bruijn inductive reaches the kernel
(see plan.md §4).

Surface (System F):

    autosubst
      ty where
        | arr  : ty → ty → ty
        | all  : (bind ty in ty) → ty
      tm where
        | app  : tm → tm → tm
        | tapp : tm → ty → tm
        | lam  : ty → (bind tm in tm) → tm
        | tlam : (bind ty in tm) → tm

The grammar lives in dedicated syntax categories so the `bind` keyword is scoped to the DSL.
Functor application `(F a b …)` and the variadic binder `⟨p, s⟩` are modelled now (Scope §4a)
though the analyzer/codegen exercise them later (Phase 9).
-/
import Lean

open Lean

namespace Autosubst.Frontend

/-- A binder: `s` (single, `bind s in _`) or `⟨p, s⟩` (variadic, `bind ⟨p,s⟩ in _`). -/
declare_syntax_cat asBinder
syntax (name := binderSingle) ident : asBinder
syntax (name := binderVector) "⟨" ident ", " ident "⟩" : asBinder

/-- A head type: a sort/atom ident, or a parenthesized functor application `(F a b …)`. -/
declare_syntax_cat asHead
syntax (name := headAtom) ident : asHead
syntax (name := headApp) "(" ident asHead+ ")" : asHead

/-- A constructor argument: a head, or a binder annotation over a head, optionally parenthesized. -/
declare_syntax_cat asArg
syntax (name := argHead) asHead : asArg
syntax (name := argBind) "bind " asBinder,+ " in " asHead : asArg
syntax (name := argParen) "(" asArg ")" : asArg

/-- A constructor: `| name (p : nat) … : arg → arg → … → resultSort`. The optional `(p : nat)`
parameters are the runtime counts referenced by variadic binders `⟨p, _⟩` (scoped-only). -/
declare_syntax_cat asCtorParam
syntax (name := ctorParam) "(" ident " : " ident ")" : asCtorParam
declare_syntax_cat asCtor
syntax (name := ctorDecl) "| " ident asCtorParam* " : " asArg (" → " asArg)* : asCtor

/-- A sort declaration: `name where | … | …`. -/
declare_syntax_cat asSortDecl
syntax (name := sortDecl) ident " where " asCtor* : asSortDecl

/-- The top-level command capturing the whole HOAS block. The optional `wellscoped` modifier
selects the `Fin`-indexed (well-scoped) backend instead of the default unscoped `Nat` one
(plan.md §8). It sits *after* the `autosubst` keyword (so the keyword unambiguously selects this
command) and is matched as a non-reserved symbol via `&"wellscoped"`. -/
syntax (name := autosubstCmd) "autosubst " (&"wellscoped")? asSortDecl* : command

end Autosubst.Frontend
