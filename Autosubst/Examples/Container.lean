/-
# Phase 9 — Golden target: a sort with **nested-container binders**, by hand.

The container analogue of `Stlc.lean`. Signature:

    tm : Type
    app : tm -> tm -> tm
    seq : "list"(tm) -> tm                  -- a container WITHOUT a binder
    lam : (bind tm in "list"(tm)) -> tm     -- a binder INTO a container

`tm` is the sole substitution sort (vector `[tm]`). The new ingredient is the `List tm` field:
substitution must thread through it, lifting the map under the `lam` binder first.

## Why a mutual `*_list` helper (not `List.map` directly)

Routing the recursion through `List.map` makes Lean compile `ren_tm`/`subst_tm` by well-founded
recursion (the opaque map hides that it only touches sub-terms), which (a) leaves the defining
equations only *propositional* and (b) blocks the lemma tower's recursion entirely. So we thread the
container with a **mutual structural helper** `ren_tm_list`/`subst_tm_list`: ordinary mutual
structural recursion, so the equations stay (mostly) definitional and every tower lemma is a natural
mutual structural recursion with its `*_list` partner. Each helper provably equals the concrete
`List.map` (`ren_tm_list_eq`/`subst_tm_list_eq`), so the contract is functor-generic, not
list-specific. Every name matches the Autosubst-2 generated output; `*_list` helpers are the
Lean-specific glue. (The generator reproduces this tower for any registered container — see
`Gen/Container.lean`.)
-/
import Autosubst.Prelude.Unscoped

namespace Autosubst.Container
open Autosubst

/-! ## Syntax (de Bruijn) -/

/-- Terms. `lam`'s body is a *list* of terms, each under one fresh `tm` binder. -/
inductive tm where
  | var_tm : Nat → tm
  | app    : tm → tm → tm
  | seq    : List tm → tm
  | lam    : List tm → tm
  deriving Repr

open tm

/-! ## Congruence lemmas -/

theorem congr_app {s0 s1 t0 t1 : tm} (h0 : s0 = t0) (h1 : s1 = t1) :
    app s0 s1 = app t0 t1 := by rw [h0, h1]

theorem congr_seq {s0 t0 : List tm} (h0 : s0 = t0) : seq s0 = seq t0 := by rw [h0]

theorem congr_lam {s0 t0 : List tm} (h0 : s0 = t0) : lam s0 = lam t0 := by rw [h0]

/-! ## Renaming -/

@[reducible] def upRen_tm_tm (xi : Nat → Nat) : Nat → Nat := up_ren xi

-- Parallel renaming, with a structural list helper for the container fields.
mutual
def ren_tm (xi : Nat → Nat) : tm → tm
  | var_tm n => var_tm (xi n)
  | app s t  => app (ren_tm xi s) (ren_tm xi t)
  | seq xs   => seq (ren_tm_list xi xs)
  | lam xs   => lam (ren_tm_list (upRen_tm_tm xi) xs)
def ren_tm_list (xi : Nat → Nat) : List tm → List tm
  | []      => []
  | x :: xs => ren_tm xi x :: ren_tm_list xi xs
end

/-! ## Substitution -/

@[reducible] def up_tm_tm (sigma : Nat → tm) : Nat → tm :=
  scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)

-- Parallel substitution, with a structural list helper for the container fields.
mutual
def subst_tm (sigma : Nat → tm) : tm → tm
  | var_tm n => sigma n
  | app s t  => app (subst_tm sigma s) (subst_tm sigma t)
  | seq xs   => seq (subst_tm_list sigma xs)
  | lam xs   => lam (subst_tm_list (up_tm_tm sigma) xs)
def subst_tm_list (sigma : Nat → tm) : List tm → List tm
  | []      => []
  | x :: xs => subst_tm sigma x :: subst_tm_list sigma xs
end

/-! ## Helpers ≡ the concrete `List.map` (the functor-generic bridge) -/

theorem ren_tm_list_eq (xi : Nat → Nat) (xs : List tm) :
    ren_tm_list xi xs = List.map (ren_tm xi) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [ren_tm_list, List.map, ih]

theorem subst_tm_list_eq (sigma : Nat → tm) (xs : List tm) :
    subst_tm_list sigma xs = List.map (subst_tm sigma) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [subst_tm_list, List.map, ih]

/-! ## `subst id = id` -/

theorem upId_tm_tm (sigma : Nat → tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ x, up_tm_tm sigma x = var_tm x
  | 0 => rfl
  | n + 1 => congrArg (ren_tm shift) (h n)

mutual
theorem idSubst_tm (sigma : Nat → tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ s, subst_tm sigma s = s
  | var_tm n => h n
  | app s t  => congr_app (idSubst_tm sigma h s) (idSubst_tm sigma h t)
  | seq xs   => by simp only [subst_tm]; exact congr_seq (idSubst_tm_list sigma h xs)
  | lam xs   => by
      simp only [subst_tm]
      exact congr_lam (idSubst_tm_list (up_tm_tm sigma) (upId_tm_tm sigma h) xs)
theorem idSubst_tm_list (sigma : Nat → tm) (h : ∀ x, sigma x = var_tm x) :
    ∀ xs, subst_tm_list sigma xs = xs
  | []      => rfl
  | x :: xs => by
      simp only [subst_tm_list]; rw [idSubst_tm sigma h x, idSubst_tm_list sigma h xs]
end

/-! ## Extensionality -/

theorem upExtRen_tm_tm (xi zeta : Nat → Nat) (h : ∀ x, xi x = zeta x) :
    ∀ x, upRen_tm_tm xi x = upRen_tm_tm zeta x
  | 0 => rfl
  | n + 1 => congrArg shift (h n)

mutual
theorem extRen_tm (xi zeta : Nat → Nat) (h : ∀ x, xi x = zeta x) :
    ∀ s, ren_tm xi s = ren_tm zeta s
  | var_tm n => congrArg var_tm (h n)
  | app s t  => congr_app (extRen_tm xi zeta h s) (extRen_tm xi zeta h t)
  | seq xs   => by simp only [ren_tm]; exact congr_seq (extRen_tm_list xi zeta h xs)
  | lam xs   => by
      simp only [ren_tm]
      exact congr_lam (extRen_tm_list (upRen_tm_tm xi) (upRen_tm_tm zeta) (upExtRen_tm_tm xi zeta h) xs)
theorem extRen_tm_list (xi zeta : Nat → Nat) (h : ∀ x, xi x = zeta x) :
    ∀ xs, ren_tm_list xi xs = ren_tm_list zeta xs
  | []      => rfl
  | x :: xs => by simp only [ren_tm_list]; rw [extRen_tm xi zeta h x, extRen_tm_list xi zeta h xs]
end

theorem upExt_tm_tm (sigma tau : Nat → tm) (h : ∀ x, sigma x = tau x) :
    ∀ x, up_tm_tm sigma x = up_tm_tm tau x
  | 0 => rfl
  | n + 1 => congrArg (ren_tm shift) (h n)

mutual
theorem ext_tm (sigma tau : Nat → tm) (h : ∀ x, sigma x = tau x) :
    ∀ s, subst_tm sigma s = subst_tm tau s
  | var_tm n => h n
  | app s t  => congr_app (ext_tm sigma tau h s) (ext_tm sigma tau h t)
  | seq xs   => by simp only [subst_tm]; exact congr_seq (ext_tm_list sigma tau h xs)
  | lam xs   => by
      simp only [subst_tm]
      exact congr_lam (ext_tm_list (up_tm_tm sigma) (up_tm_tm tau) (upExt_tm_tm sigma tau h) xs)
theorem ext_tm_list (sigma tau : Nat → tm) (h : ∀ x, sigma x = tau x) :
    ∀ xs, subst_tm_list sigma xs = subst_tm_list tau xs
  | []      => rfl
  | x :: xs => by simp only [subst_tm_list]; rw [ext_tm sigma tau h x, ext_tm_list sigma tau h xs]
end

/-! ## Compositionality: ren ∘ ren -/

theorem up_ren_ren_tm_tm (xi zeta rho : Nat → Nat) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x :=
  up_ren_ren xi zeta rho h

mutual
theorem compRenRen_tm (xi zeta rho : Nat → Nat) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ s, ren_tm zeta (ren_tm xi s) = ren_tm rho s
  | var_tm n => congrArg var_tm (h n)
  | app s t  => congr_app (compRenRen_tm xi zeta rho h s) (compRenRen_tm xi zeta rho h t)
  | seq xs   => by simp only [ren_tm]; exact congr_seq (compRenRen_tm_list xi zeta rho h xs)
  | lam xs   => by
      simp only [ren_tm]
      exact congr_lam (compRenRen_tm_list (upRen_tm_tm xi) (upRen_tm_tm zeta) (upRen_tm_tm rho)
        (up_ren_ren_tm_tm xi zeta rho h) xs)
theorem compRenRen_tm_list (xi zeta rho : Nat → Nat) (h : ∀ x, funcomp zeta xi x = rho x) :
    ∀ xs, ren_tm_list zeta (ren_tm_list xi xs) = ren_tm_list rho xs
  | []      => rfl
  | x :: xs => by
      simp only [ren_tm_list]; rw [compRenRen_tm xi zeta rho h x, compRenRen_tm_list xi zeta rho h xs]
end

/-! ## Compositionality: subst ∘ ren -/

theorem up_ren_subst_tm_tm (xi : Nat → Nat) (tau theta : Nat → tm)
    (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 => congrArg (ren_tm shift) (h n)

mutual
theorem compRenSubst_tm (xi : Nat → Nat) (tau theta : Nat → tm)
    (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ s, subst_tm tau (ren_tm xi s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => congr_app (compRenSubst_tm xi tau theta h s) (compRenSubst_tm xi tau theta h t)
  | seq xs   => by simp only [ren_tm, subst_tm]; exact congr_seq (compRenSubst_tm_list xi tau theta h xs)
  | lam xs   => by
      simp only [ren_tm, subst_tm]
      exact congr_lam (compRenSubst_tm_list (upRen_tm_tm xi) (up_tm_tm tau) (up_tm_tm theta)
        (up_ren_subst_tm_tm xi tau theta h) xs)
theorem compRenSubst_tm_list (xi : Nat → Nat) (tau theta : Nat → tm)
    (h : ∀ x, funcomp tau xi x = theta x) :
    ∀ xs, subst_tm_list tau (ren_tm_list xi xs) = subst_tm_list theta xs
  | []      => rfl
  | x :: xs => by
      simp only [ren_tm_list, subst_tm_list]
      rw [compRenSubst_tm xi tau theta h x, compRenSubst_tm_list xi tau theta h xs]
end

/-! ## Compositionality: ren ∘ subst (eq_trans-chain up-helper) -/

theorem up_subst_ren_tm_tm (sigma : Nat → tm) (zeta : Nat → Nat) (theta : Nat → tm)
    (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ x, funcomp (ren_tm (upRen_tm_tm zeta)) (up_tm_tm sigma) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 =>
      (compRenRen_tm shift (upRen_tm_tm zeta) (funcomp shift zeta) (fun _ => rfl) (sigma n)).trans
        (((compRenRen_tm zeta shift (funcomp shift zeta) (fun _ => rfl) (sigma n)).symm).trans
          (congrArg (ren_tm shift) (h n)))

mutual
theorem compSubstRen_tm (sigma : Nat → tm) (zeta : Nat → Nat) (theta : Nat → tm)
    (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ s, ren_tm zeta (subst_tm sigma s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => congr_app (compSubstRen_tm sigma zeta theta h s) (compSubstRen_tm sigma zeta theta h t)
  | seq xs   => by simp only [subst_tm, ren_tm]; exact congr_seq (compSubstRen_tm_list sigma zeta theta h xs)
  | lam xs   => by
      simp only [subst_tm, ren_tm]
      exact congr_lam (compSubstRen_tm_list (up_tm_tm sigma) (upRen_tm_tm zeta) (up_tm_tm theta)
        (up_subst_ren_tm_tm sigma zeta theta h) xs)
theorem compSubstRen_tm_list (sigma : Nat → tm) (zeta : Nat → Nat) (theta : Nat → tm)
    (h : ∀ x, funcomp (ren_tm zeta) sigma x = theta x) :
    ∀ xs, ren_tm_list zeta (subst_tm_list sigma xs) = subst_tm_list theta xs
  | []      => rfl
  | x :: xs => by
      simp only [subst_tm_list, ren_tm_list]
      rw [compSubstRen_tm sigma zeta theta h x, compSubstRen_tm_list sigma zeta theta h xs]
end

/-! ## Compositionality: subst ∘ subst (eq_trans-chain up-helper) -/

theorem up_subst_subst_tm_tm (sigma tau theta : Nat → tm)
    (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ x, funcomp (subst_tm (up_tm_tm tau)) (up_tm_tm sigma) x = up_tm_tm theta x
  | 0 => rfl
  | n + 1 =>
      (compRenSubst_tm shift (up_tm_tm tau) (funcomp (up_tm_tm tau) shift) (fun _ => rfl) (sigma n)).trans
        (((compSubstRen_tm tau shift (funcomp (ren_tm shift) tau) (fun _ => rfl) (sigma n)).symm).trans
          (congrArg (ren_tm shift) (h n)))

mutual
theorem compSubstSubst_tm (sigma tau theta : Nat → tm)
    (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ s, subst_tm tau (subst_tm sigma s) = subst_tm theta s
  | var_tm n => h n
  | app s t  => congr_app (compSubstSubst_tm sigma tau theta h s) (compSubstSubst_tm sigma tau theta h t)
  | seq xs   => by simp only [subst_tm]; exact congr_seq (compSubstSubst_tm_list sigma tau theta h xs)
  | lam xs   => by
      simp only [subst_tm]
      exact congr_lam (compSubstSubst_tm_list (up_tm_tm sigma) (up_tm_tm tau) (up_tm_tm theta)
        (up_subst_subst_tm_tm sigma tau theta h) xs)
theorem compSubstSubst_tm_list (sigma tau theta : Nat → tm)
    (h : ∀ x, funcomp (subst_tm tau) sigma x = theta x) :
    ∀ xs, subst_tm_list tau (subst_tm_list sigma xs) = subst_tm_list theta xs
  | []      => rfl
  | x :: xs => by
      simp only [subst_tm_list]
      rw [compSubstSubst_tm sigma tau theta h x, compSubstSubst_tm_list sigma tau theta h xs]
end

/-! ## Renaming is a special case of substitution -/

theorem rinstInst_up_tm_tm (xi : Nat → Nat) (sigma : Nat → tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ x, funcomp var_tm (upRen_tm_tm xi) x = up_tm_tm sigma x
  | 0 => rfl
  | n + 1 => congrArg (ren_tm shift) (h n)

mutual
theorem rinst_inst_tm (xi : Nat → Nat) (sigma : Nat → tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ s, ren_tm xi s = subst_tm sigma s
  | var_tm n => h n
  | app s t  => congr_app (rinst_inst_tm xi sigma h s) (rinst_inst_tm xi sigma h t)
  | seq xs   => by simp only [ren_tm, subst_tm]; exact congr_seq (rinst_inst_tm_list xi sigma h xs)
  | lam xs   => by
      simp only [ren_tm, subst_tm]
      exact congr_lam (rinst_inst_tm_list (upRen_tm_tm xi) (up_tm_tm sigma) (rinstInst_up_tm_tm xi sigma h) xs)
theorem rinst_inst_tm_list (xi : Nat → Nat) (sigma : Nat → tm)
    (h : ∀ x, funcomp var_tm xi x = sigma x) :
    ∀ xs, ren_tm_list xi xs = subst_tm_list sigma xs
  | []      => rfl
  | x :: xs => by
      simp only [ren_tm_list, subst_tm_list]
      rw [rinst_inst_tm xi sigma h x, rinst_inst_tm_list xi sigma h xs]
end

/-! ## Clean (funext-based) wrappers — the `asimp`-facing API -/

theorem rinstInst'_tm (xi : Nat → Nat) (s : tm) :
    ren_tm xi s = subst_tm (funcomp var_tm xi) s :=
  rinst_inst_tm xi _ (fun _ => rfl) s

theorem rinstInst_tm (xi : Nat → Nat) : ren_tm xi = subst_tm (funcomp var_tm xi) :=
  funext (rinstInst'_tm xi)

theorem instId'_tm (s : tm) : subst_tm var_tm s = s :=
  idSubst_tm var_tm (fun _ => rfl) s

theorem instId_tm : subst_tm var_tm = id := funext instId'_tm

theorem rinstId'_tm (s : tm) : ren_tm id s = s :=
  (rinstInst'_tm id s).trans (instId'_tm s)

theorem rinstId_tm : @ren_tm id = id := funext rinstId'_tm

theorem varL_tm (sigma : Nat → tm) : funcomp (subst_tm sigma) var_tm = sigma := rfl

theorem varLRen_tm (xi : Nat → Nat) : funcomp (ren_tm xi) var_tm = funcomp var_tm xi := rfl

theorem varL'_tm (sigma : Nat → tm) (x : Nat) : subst_tm sigma (var_tm x) = sigma x := rfl

theorem varLRen'_tm (xi : Nat → Nat) (x : Nat) : ren_tm xi (var_tm x) = var_tm (xi x) := rfl

theorem renRen_tm (xi zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s :=
  compRenRen_tm xi zeta _ (fun _ => rfl) s

theorem renRen'_tm (xi zeta : Nat → Nat) :
    funcomp (ren_tm zeta) (ren_tm xi) = ren_tm (funcomp zeta xi) :=
  funext (renRen_tm xi zeta)

theorem renSubst_tm (xi : Nat → Nat) (tau : Nat → tm) (s : tm) :
    subst_tm tau (ren_tm xi s) = subst_tm (funcomp tau xi) s :=
  compRenSubst_tm xi tau _ (fun _ => rfl) s

theorem renSubst'_tm (xi : Nat → Nat) (tau : Nat → tm) :
    funcomp (subst_tm tau) (ren_tm xi) = subst_tm (funcomp tau xi) :=
  funext (renSubst_tm xi tau)

theorem substRen_tm (sigma : Nat → tm) (zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (subst_tm sigma s) = subst_tm (funcomp (ren_tm zeta) sigma) s :=
  compSubstRen_tm sigma zeta _ (fun _ => rfl) s

theorem substRen'_tm (sigma : Nat → tm) (zeta : Nat → Nat) :
    funcomp (ren_tm zeta) (subst_tm sigma) = subst_tm (funcomp (ren_tm zeta) sigma) :=
  funext (substRen_tm sigma zeta)

theorem substSubst_tm (sigma tau : Nat → tm) (s : tm) :
    subst_tm tau (subst_tm sigma s) = subst_tm (funcomp (subst_tm tau) sigma) s :=
  compSubstSubst_tm sigma tau _ (fun _ => rfl) s

theorem substSubst'_tm (sigma tau : Nat → tm) :
    funcomp (subst_tm tau) (subst_tm sigma) = subst_tm (funcomp (subst_tm tau) sigma) :=
  funext (substSubst_tm sigma tau)

/-! ## Verification: the tower is internally consistent and the helpers are the container `map`.

`subst_tm_list`/`ren_tm_list` ARE the concrete `List.map` (`subst_tm_list_eq` above), so the contract
is functor-generic, not list-specific. -/

example (s : tm) : subst_tm var_tm s = s := instId'_tm s

example (xi zeta : Nat → Nat) (s : tm) :
    ren_tm zeta (ren_tm xi s) = ren_tm (funcomp zeta xi) s := renRen_tm xi zeta s

/-- β cancels a shift, threaded through the `lam` container. -/
example (t : tm) (s : tm) :
    subst_tm (scons t var_tm) (ren_tm shift s) = s := by
  rw [renSubst_tm]; exact idSubst_tm _ (fun _ => rfl) s

end Autosubst.Container
