import Tests.Support

universe u v w

inductive PBox (Srt : Type u) (α : Type v) where
  | wrap : Srt → α → PBox Srt α
  deriving Repr

inductive PairBox (α : Type u) (β : Type v) where
  | both : α → β → PairBox α β
  | roll : PairBox α β → PairBox α β
  deriving Repr

namespace Parameterized
open Autosubst Autosubst.Notation

inductive Rlv where
  | im | ex
  deriving Repr, DecidableEq

def Thunk (_Srt : Type u) (_Ann : Type v) := Unit

/-! Parameterized sort declarations: mixed implicit/explicit parameters, universe-polymorphic
foreign fields, parameterized containers, and an explicitly opaque external type expression. -/
autosubst
  Tm {Srt : Type u} (Ann : Type v) {Tok : Type w} where
    | srt    : Srt → Nat → Tm
    | ann    : Ann → Tm → Tm
    | lit    : Tok → Tm
    | boxed  : PBox Srt Tm → Tm
    | thunk  : opaque(Thunk Srt Ann) → Tm
    | pi     : Tm → (bind Tm in Tm) → Rlv → Srt → Tm
    | lam    : Tm → (bind Tm in Tm) → Rlv → Srt → Tm
    | app    : Tm → Tm → Tm

namespace Tm
@[match_pattern] abbrev var {Srt : Type u} {Ann : Type v} {Tok : Type w} :=
  @Tm.var_Tm Srt Ann Tok
end Tm

example {Srt : Type u} {Ann : Type v} {Tok : Type w}
    (σ : Nat → @Tm Srt Ann Tok) (A B : @Tm Srt Ann Tok) (r : Rlv) (s : Srt) :
    subst_Tm σ (Tm.pi A B r s)
      = Tm.pi (subst_Tm σ A) (subst_Tm (up_Tm_Tm σ) B) r s := by
  rfl

example {Srt : Type u} {Ann : Type v} {Tok : Type w}
    (σ τ : Nat → @Tm Srt Ann Tok) (m : @Tm Srt Ann Tok) :
    subst_Tm τ (subst_Tm σ m)
      = subst_Tm (funcomp (subst_Tm τ) σ) m := by
  asimp

example {Srt : Type u} {Ann : Type v} {Tok : Type w}
    (σ : Nat → @Tm Srt Ann Tok) (xs : PBox Srt (@Tm Srt Ann Tok)) :
    subst_Tm σ (Tm.boxed xs) = Tm.boxed (subst_Tm_PBox σ xs) := by
  rfl

namespace ExplicitRefs

/-! Explicit sort applications in references. Bare `Ty` in `Tm2` also means `Ty` applied to the
current telescope; `Ty Srt` exercises the explicit spelling. -/
autosubst
  Ty {Srt : Type u} where
    | base : Srt → Ty
    | arr  : Ty → Ty → Ty

  Tm2 {Srt : Type u} where
    | ann : Tm2 → Ty Srt → Tm2
    | lam : Ty → (bind Tm2 in Tm2) → Tm2
    | app : Tm2 → Tm2 → Tm2

example {Srt : Type u} (σ : Nat → @Tm2 Srt) (A : @Ty Srt) (m : @Tm2 Srt) :
    subst_Tm2 σ (Tm2.ann m A) = Tm2.ann (subst_Tm2 σ m) A := by
  rfl

example {Srt : Type u} (σ τ : Nat → @Tm2 Srt) (m : @Tm2 Srt) :
    subst_Tm2 τ (subst_Tm2 σ m)
      = subst_Tm2 (funcomp (subst_Tm2 τ) σ) m := by
  asimp

end ExplicitRefs

namespace Polynomial

/-! Multi-parameter polynomial containers: `PairBox TyP TmP` threads both parameters, and
`PairBox TmP Nat` threads a non-final parameter. -/
autosubst
  TyP where
    | all : (bind TyP in TyP) → TyP
    | arr : TyP → TyP → TyP

  TmP where
    | box   : PairBox TyP TmP → TmP
    | left  : PairBox TmP Nat → TmP
    | lam   : (bind TmP in TmP) → TmP
    | tlam  : (bind TyP in TmP) → TmP
    | app   : TmP → TmP → TmP

example (σTy : Nat → TyP) (σTm : Nat → TmP) (A : TyP) (t : TmP) :
    subst_TmP σTy σTm (TmP.box (PairBox.both A t))
      = TmP.box (PairBox.both (subst_TyP σTy A) (subst_TmP σTy σTm t)) := by
  rfl

example (σTy : Nat → TyP) (σTm : Nat → TmP) (t : TmP) (n : Nat) :
    subst_TmP σTy σTm (TmP.left (PairBox.both t n))
      = TmP.left (PairBox.both (subst_TmP σTy σTm t) n) := by
  rfl

example (σTy : Nat → TyP) (σTm : Nat → TmP) (A : TyP) (t : TmP) :
    subst_TmP σTy σTm (TmP.box (PairBox.roll (PairBox.both A t)))
      = TmP.box (PairBox.roll
          (PairBox.both (subst_TyP σTy A) (subst_TmP σTy σTm t))) := by
  rfl

example (σTy τTy : Nat → TyP) (σTm τTm : Nat → TmP) (t : TmP) :
    subst_TmP τTy τTm (subst_TmP σTy σTm t)
      = subst_TmP (funcomp (subst_TyP τTy) σTy)
          (funcomp (subst_TmP τTy τTm) σTm) t := by
  asimp

end Polynomial

namespace InstanceParams

class Flavor (α : Type u) where
  flavor : α → Nat

/-! Instance parameters may be written directly in the sort telescope. Anonymous instance binders
are given generated local names internally so explicit applications such as `@TmInst ...` can be
emitted by the backend. -/
autosubst
  TmInst (Srt : Type u) [BEq Srt] [flv : Flavor Srt] where
    | atom : Srt → TmInst
    | lam  : (bind TmInst in TmInst) → TmInst
    | app  : TmInst → TmInst → TmInst

example {Srt : Type u} [BEq Srt] [Flavor Srt]
    (σ τ : Nat → TmInst Srt) (t : TmInst Srt) :
    subst_TmInst τ (subst_TmInst σ t)
      = subst_TmInst (funcomp (subst_TmInst τ) σ) t := by
  asimp

#axiom_clean substSubst_TmInst

end InstanceParams

namespace SectionVars

section
variable (Srt : Type u)

/-! Section variables mentioned in the DSL are promoted to sort parameters automatically. -/
autosubst
  TmSec where
    | atom : Srt → TmSec
    | lam  : (bind TmSec in TmSec) → TmSec
    | app  : TmSec → TmSec → TmSec

example (σ τ : Nat → TmSec Srt) (t : TmSec Srt) :
    subst_TmSec τ (subst_TmSec σ t)
      = subst_TmSec (funcomp (subst_TmSec τ) σ) t := by
  asimp

#axiom_clean substSubst_TmSec

end

inductive Mark (Srt : Type u) (tok : Srt) where
  | mk : Mark Srt tok

section
variable {Srt : Type u} (tok : Srt)

/-! Dependency closure: capturing `tok` also captures the `Srt` it depends on. -/
autosubst
  TmDep where
    | mark : Mark Srt tok → TmDep
    | dlam : (bind TmDep in TmDep) → TmDep
    | dapp : TmDep → TmDep → TmDep

example (σ τ : Nat → @TmDep Srt tok) (t : @TmDep Srt tok) :
    subst_TmDep τ (subst_TmDep σ t)
      = subst_TmDep (funcomp (subst_TmDep τ) σ) t := by
  asimp

#axiom_clean substSubst_TmDep

end

section
variable (Srt : Type u) [BEq Srt]

/-! Instance section variables whose class type depends on captured variables are promoted too. -/
autosubst
  TmSecInst where
    | atom : Srt → TmSecInst
    | ilam : (bind TmSecInst in TmSecInst) → TmSecInst
    | iapp : TmSecInst → TmSecInst → TmSecInst

example (σ τ : Nat → TmSecInst Srt) (t : TmSecInst Srt) :
    subst_TmSecInst τ (subst_TmSecInst σ t)
      = subst_TmSecInst (funcomp (subst_TmSecInst τ) σ) t := by
  asimp

#axiom_clean substSubst_TmSecInst

end

end SectionVars

namespace Scoped

/-! Parameterized sorts also work in the well-scoped backend when no nested container over the
indexed family is involved. -/
autosubst wellscoped
  TmS {Srt : Type u} (Ann : Type v) where
    | atom : Srt → TmS
    | ann  : Ann → TmS → TmS
    | lam  : (bind TmS in TmS) → TmS
    | app  : TmS → TmS → TmS

example {Srt : Type u} {Ann : Type v}
    (σ : Fin m → @TmS Srt Ann n) (b : @TmS Srt Ann (m + 1)) :
    subst_TmS σ (TmS.lam b) = TmS.lam (subst_TmS (up_TmS_TmS σ) b) := by
  rfl

example {Srt : Type u} {Ann : Type v}
    (σ : Fin m → @TmS Srt Ann n) (τ : Fin n → @TmS Srt Ann k)
    (t : @TmS Srt Ann m) :
    subst_TmS τ (subst_TmS σ t)
      = subst_TmS (funcomp (subst_TmS τ) σ) t := by
  asimp

end Scoped

#axiom_clean substSubst_Tm
#axiom_clean ExplicitRefs.substSubst_Tm2
#axiom_clean Polynomial.substSubst_TmP
#axiom_clean InstanceParams.substSubst_TmInst
#axiom_clean Scoped.substSubst_TmS

end Parameterized
