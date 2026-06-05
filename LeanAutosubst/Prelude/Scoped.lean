/-
Port of Autosubst 2's `fintype.v` runtime prelude (the well-scoped variable backend).

Reference: rocq/autosubst2-ocaml/share/coq-autosubst-ocaml/fintype.v

Well-scoped de Bruijn syntax draws variables from a finite type. The reference uses the
`n`-fold iteration of `Option`; we use Lean's **core `Fin n`** instead (the idiomatic choice).
`var_zero`/`shift`/`scons` are the `Fin` analogues of `0`/`Fin.succ`/`Fin.cons`:

  • `var_zero : Fin (n+1)`         — the freshly bound variable (`0`);
  • `shift    : Fin n → Fin (n+1)` — weakening (`Fin.succ`);
  • `scons x f : Fin (n+1) → X`    — extend a map at `0` (`Fin.cases x f`).

Crucially, `Fin.cases` reduces **definitionally** on `0` / `Fin.succ i`, so `scons` behaves like
its `Nat` counterpart: `scons x f var_zero = x` and `scons x f (shift i) = f i` hold by `rfl`,
and the whole proof tower carries over (the `Nat` `0`/`n+1` case split becomes `Fin.cases`).

Everything lives in `Autosubst.Scoped`, parallel to the unscoped names in `Autosubst`, so the
generator selects a backend by namespace prefix and the two can coexist. Laws are given in both
pointwise and funext-based forms; the extensional forms feed the generated clean lemmas / `asimp`.
-/
import LeanAutosubst.Prelude.Core

namespace Autosubst.Scoped

/-- Elimination out of the empty finite type `Fin 0`. -/
@[reducible] def fin0_elim {T : Sort _} (i : Fin 0) : T := i.elim0

/-- The freshly bound variable: the newest element of a non-empty finite type. -/
@[reducible] def var_zero {n : Nat} : Fin (n + 1) := 0

/-- The shift renaming `Fin n → Fin (n+1)`. -/
@[reducible] def shift {n : Nat} : Fin n → Fin (n + 1) := Fin.succ

/-- Extend a map `Fin n → X` with a new value at `var_zero`, shifting the rest up.
Autosubst notation `x .: f`. -/
@[reducible] def scons {X : Sort _} {n : Nat} (x : X) (f : Fin n → X) : Fin (n + 1) → X :=
  Fin.cases x f

@[inherit_doc] scoped infixr:55 " .: " => scons

@[simp] theorem scons_zero {X : Sort _} {n} (x : X) (f : Fin n → X) :
    scons x f var_zero = x := rfl
@[simp] theorem scons_succ {X : Sort _} {n} (x : X) (f : Fin n → X) (i : Fin n) :
    scons x f (shift i) = f i := rfl

/-- Generic lifting of a renaming under one binder. -/
@[reducible] def up_ren {m n : Nat} (xi : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  scons var_zero (funcomp shift xi)

/-- Lifting of renamings composes (pointwise). -/
theorem up_ren_ren {k l m : Nat} (xi : Fin k → Fin l) (zeta : Fin l → Fin m)
    (rho : Fin k → Fin m) (e : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (up_ren zeta) (up_ren xi) x = up_ren rho x :=
  Fin.cases rfl (fun i => by simp [up_ren, funcomp, shift, ← e i])

/-! ## scons eta and composition laws -/

theorem scons_eta_pointwise {T : Sort _} {n} (f : Fin (n + 1) → T) :
    ∀ x, (scons (f var_zero) (funcomp f shift)) x = f x :=
  Fin.cases rfl (fun _ => rfl)

theorem scons_eta {T : Sort _} {n} (f : Fin (n + 1) → T) :
    scons (f var_zero) (funcomp f shift) = f :=
  funext (scons_eta_pointwise f)

theorem scons_eta_id_pointwise {n} : ∀ x, (scons var_zero shift) x = @id (Fin (n + 1)) x :=
  Fin.cases rfl (fun _ => rfl)

theorem scons_eta_id {n} : scons (@var_zero n) shift = id :=
  funext scons_eta_id_pointwise

theorem scons_comp_pointwise {T : Sort _} {U : Sort _} {n} (s : T) (sigma : Fin n → T)
    (tau : T → U) :
    ∀ x, funcomp tau (scons s sigma) x = (scons (tau s) (funcomp tau sigma)) x :=
  Fin.cases rfl (fun _ => rfl)

theorem scons_comp {T : Sort _} {U : Sort _} {n} (s : T) (sigma : Fin n → T) (tau : T → U) :
    funcomp tau (scons s sigma) = scons (tau s) (funcomp tau sigma) :=
  funext (scons_comp_pointwise s sigma tau)

/-- `(x .: f) ∘ shift = f` (Coq's `shift >> (x .: g) = g`). -/
theorem scons_shift {X : Sort _} {n} (x : X) (f : Fin n → X) :
    funcomp (scons x f) shift = f := rfl

/-! ## Variadic (`bind ⟨p, _⟩`) primitives — `fintype.v`'s `scons_p`/`shift_p`/`zero_p`/`upRen_p`.

A variadic binder `bind ⟨p, b⟩` introduces `p` fresh `b`-variables *at runtime* (`p : Nat`), so the
body scope grows by `p`. The reference (`fintype.v`) encodes this with `fin (p + n)`; we use the
**Lean-idiomatic order `Fin (n + p)`** instead, because `Nat.add` recurses on its *second* argument,
so `Fin (n + p)` reduces on `p` (whereas `Fin (p + n)` would be stuck for a variable `n`). The fresh
variables sit at the low indices `0 … p-1` (de Bruijn-correct); the original `n` variables shift up
to `p … p+n-1`. These primitives are scoped-only (the unscoped/`Nat` variadic form is unported, as
upstream — see plan.md §9/§10). -/

/-- Weaken past `p` freshly bound variables: the original `Fin n` lands at the high indices. -/
def shift_p {n : Nat} : (p : Nat) → Fin n → Fin (n + p)
  | 0,     x => x
  | p + 1, x => Fin.succ (shift_p p x)

/-- The `p` freshly bound variables (the low indices `0 … p-1`). -/
def zero_p {n : Nat} : (p : Nat) → Fin p → Fin (n + p)
  | 0,     i => i.elim0
  | p + 1, i => Fin.cases 0 (fun (j : Fin p) => Fin.succ (zero_p p j)) i

/-- Split a map over `Fin (n + p)`: the first `p` variables use `f`, the rest use `g`. The variadic
analogue of `scons` (which is the `p = 1` case). -/
def scons_p {X : Sort _} {n : Nat} : (p : Nat) → (Fin p → X) → (Fin n → X) → Fin (n + p) → X
  | 0,     _, g => g
  | p + 1, f, g => Fin.cases (f 0) (fun y => scons_p p (fun j => f j.succ) g y)

/-- Lifting of a renaming under a variadic binder (`fintype.v`'s `upRen_p`). -/
@[reducible] def upRen_p (p : Nat) {m n : Nat} (xi : Fin m → Fin n) : Fin (m + p) → Fin (n + p) :=
  scons_p p (zero_p p) (funcomp (shift_p p) xi)

/-- `scons_p` on a fresh variable (`zero_p`) hits `f`. -/
theorem scons_p_head' {X} {n} : ∀ (p) (f : Fin p → X) (g : Fin n → X) (z : Fin p),
    scons_p p f g (zero_p p z) = f z
  | 0,     _, _, z => z.elim0
  | p + 1, f, g, z => by
      refine Fin.cases ?_ ?_ z
      · rfl
      · intro j
        show scons_p p (fun j => f j.succ) g (zero_p p j) = f j.succ
        exact scons_p_head' p (fun j => f j.succ) g j

/-- `scons_p` on a shifted original variable (`shift_p`) hits `g`. -/
theorem scons_p_tail' {X} {n} : ∀ (p) (f : Fin p → X) (g : Fin n → X) (z : Fin n),
    scons_p p f g (shift_p p z) = g z
  | 0,     _, _, _ => rfl
  | p + 1, f, g, z => by
      show scons_p p (fun j => f j.succ) g (shift_p p z) = g z
      exact scons_p_tail' p (fun j => f j.succ) g z

/-- `scons_p` respects pointwise equality of its two branches. -/
theorem scons_p_congr {X} {n} : ∀ (p) {f f' : Fin p → X} {g g' : Fin n → X}
    (_ : ∀ x, f x = f' x) (_ : ∀ x, g x = g' x) (z : Fin (n + p)),
    scons_p p f g z = scons_p p f' g' z
  | 0,     _, _, _, _, _, hg, z => hg z
  | p + 1, f, f', g, g', hf, hg, z => by
      refine Fin.cases ?_ ?_ z
      · exact hf 0
      · intro y
        show scons_p p (fun j => f j.succ) g y = scons_p p (fun j => f' j.succ) g' y
        exact scons_p_congr p (fun j => hf j.succ) hg y

/-- Postcomposition distributes over `scons_p` (pointwise). -/
theorem scons_p_comp {X Y} {n} : ∀ (p) (f : Fin p → X) (g : Fin n → X) (h : X → Y) (z : Fin (n + p)),
    funcomp h (scons_p p f g) z = scons_p p (funcomp h f) (funcomp h g) z
  | 0,     _, _, _, _ => rfl
  | p + 1, f, g, h, z => by
      refine Fin.cases ?_ ?_ z
      · rfl
      · intro y
        show h (scons_p p (fun j => f j.succ) g y)
           = scons_p p (funcomp h (fun j => f j.succ)) (funcomp h g) y
        exact scons_p_comp p (fun j => f j.succ) g h y

/-- `scons_p`-eta: `scons_p f g = h` when `f`/`g` agree with `h` on the `zero_p`/`shift_p` ranges. -/
theorem scons_p_eta {X} {n} : ∀ (p) {f : Fin p → X} {g : Fin n → X} (h : Fin (n + p) → X)
    (_ : ∀ x, g x = h (shift_p p x)) (_ : ∀ x, f x = h (zero_p p x)) (z : Fin (n + p)),
    scons_p p f g z = h z
  | 0,     _, _, h, hg, _, z => hg z
  | p + 1, f, g, h, hg, hf, z => by
      refine Fin.cases ?_ ?_ z
      · exact hf 0
      · intro y
        show scons_p p (fun j => f j.succ) g y = h (Fin.succ y)
        exact scons_p_eta p (fun w => h (Fin.succ w)) (fun x => hg x) (fun x => hf x.succ) y

/-- Every `Fin (n + p)` is in the image of `zero_p` (fresh) or `shift_p` (original). -/
theorem fin_p_cases {n} : ∀ (p) (z : Fin (n + p)),
    (∃ j : Fin p, z = zero_p p j) ∨ (∃ j : Fin n, z = shift_p p j)
  | 0,     z => Or.inr ⟨z, rfl⟩
  | p + 1, z => by
      refine Fin.cases ?_ ?_ z
      · exact Or.inl ⟨0, rfl⟩
      · intro y
        rcases fin_p_cases p y with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact Or.inl ⟨j.succ, rfl⟩
        · exact Or.inr ⟨j, rfl⟩

/-- Lifting of renamings composes under a variadic binder (`fintype.v`'s `up_ren_ren_p`). -/
theorem up_ren_ren_p (p : Nat) {k l m} {xi : Fin k → Fin l} {zeta : Fin l → Fin m}
    {rho : Fin k → Fin m} (e : ∀ x, funcomp zeta xi x = rho x) :
    ∀ x, funcomp (upRen_p p zeta) (upRen_p p xi) x = upRen_p p rho x := by
  intro x
  rcases fin_p_cases p x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · show upRen_p p zeta (upRen_p p xi (zero_p p j)) = upRen_p p rho (zero_p p j)
    simp only [upRen_p, scons_p_head']
  · show upRen_p p zeta (upRen_p p xi (shift_p p j)) = upRen_p p rho (shift_p p j)
    simp only [upRen_p, scons_p_tail']
    exact congrArg (shift_p p) (e j)

end Autosubst.Scoped
