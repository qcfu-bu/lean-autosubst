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

/-- `asHead` is a head type; `asHeadArg` is an *atomic* functor argument. They are mutually
recursive (a parenthesized head is an argument; a head applies to arguments), so both categories
are declared before either's rules. -/
declare_syntax_cat asHead
declare_syntax_cat asHeadArg

/-- A functor argument: atomic, mirroring Lean application arguments parsed at `maxPrec` — a bare
ident or a parenthesized head. Nesting a functor application therefore *requires* the parens
(`List (Option tm)`), exactly as `List (Option α)` does in Lean. -/
syntax (name := headArgAtom) ident : asHeadArg
syntax (name := headArgParen) "(" asHead ")" : asHeadArg
syntax (name := headArgOpaque) "opaque(" term ")" : asHeadArg

/-- A head type: a sort/ext ident, a functor application `F a b …` (juxtaposition, like Lean — the
top-level application needs no parens), or a redundantly-parenthesized head `(…)`. Application binds
tighter than the constructor-argument `→` separator, so `F a b → c` reads as `(F a b) → c`. -/
syntax (name := headAtom) ident : asHead
-- `withPosition`/`colGt` mirror Lean's `app` parser (`argument := checkColGt …`): an argument must be
-- indented past the functor head. Without this guard the juxtaposition would greedily absorb the
-- following line — e.g. a constructor's result sort `… → ty` would swallow the next sort's `tm` (or
-- the next `| ctor`) as `ty tm`. This is what the old mandatory `( … )` delimiter bought us.
syntax (name := headApp) withPosition(ident (colGt asHeadArg)+) : asHead
syntax (name := headParen) "(" asHead ")" : asHead
syntax (name := headOpaque) "opaque(" term ")" : asHead

/-- A constructor argument: a head, or a `bind … in head` binder annotation. The binder annotation
may be written parenthesized (`(bind tm in tm)`) or bare (`bind tm in tm`). A parenthesized *head*
goes through `asHead`'s own paren form, so `(List tm)` and `List tm` are interchangeable as in Lean.
The two leading-`(` forms diverge on the next token (`bind` keyword vs an ident), so they never
clash. -/
declare_syntax_cat asArg
syntax (name := argHead) asHead : asArg
syntax (name := argBind) "bind " asBinder,+ " in " asHead : asArg
syntax (name := argBindParen) "(" "bind " asBinder,+ " in " asHead ")" : asArg

/-- A constructor: `| name (p : nat) … : arg → arg → … → resultSort`. The optional `(p : nat)`
parameters are the runtime counts referenced by variadic binders `⟨p, _⟩` (scoped-only). -/
declare_syntax_cat asCtorParam
syntax (name := ctorParam) "(" ident " : " ident ")" : asCtorParam
declare_syntax_cat asCtor
-- The separator accepts either the unicode `→` or the ASCII `->`, like Lean's own arrow. The
-- elaborator reads child 1 (the `asArg`) of each `(sep asArg)` group, so the separator shape is
-- irrelevant to it.
syntax (name := ctorDecl) "| " ident asCtorParam* " : " asArg ((" → " <|> " -> ") asArg)* : asCtor

/-- A sort declaration: `name {α : Type u} (β : Type v) [inst : C α] where | … | …`.
The parameter binders are preserved in the generated inductive. Generated renaming/substitution
declarations thread ordinary parameters implicitly and instance parameters as instance implicits. -/
declare_syntax_cat asSortDecl
declare_syntax_cat asSortParam
syntax (name := sortParamExplicit) "(" ident " : " term ")" : asSortParam
syntax (name := sortParamImplicit) "{" ident " : " term "}" : asSortParam
syntax (name := sortParamStrictImplicit) "⦃" ident " : " term "⦄" : asSortParam
syntax (name := sortParamInstNamed) "[" ident " : " term "]" : asSortParam
syntax (name := sortParamInstAnon) "[" term "]" : asSortParam
syntax (name := sortDecl) ident asSortParam* " where " asCtor* : asSortDecl

/-- The top-level command capturing the whole HOAS block. The optional `wellscoped` modifier
selects the `Fin`-indexed (well-scoped) backend instead of the default unscoped `Nat` one
(plan.md §8). It sits *after* the `autosubst` keyword (so the keyword unambiguously selects this
command) and is matched as a non-reserved symbol via `&"wellscoped"`. -/
syntax (name := autosubstCmd) "autosubst " (&"wellscoped")? asSortDecl* : command

end Autosubst.Frontend
