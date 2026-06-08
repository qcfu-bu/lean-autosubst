/-
# Notation-instance generation (the Autosubst-consistent notation pass).

Emits, per substitution sort, the typeclass instances that back the scoped notations in
`Prelude/Notation.lean` (`s[σ]`/`s⟨ξ⟩` and the two-map `s[σ;τ]`/`s⟨ξ;ζ⟩`, the function forms,
and `t..` via `Var`/`ids`). Mirrors the reference's per-sort `Subst_s`/`Ren_s`/`VarInstance_s`
instances (`unscoped.v`'s commented block + `codeGenerator.ml`). **No change** to the generated
`subst_s`/`ren_s`/`var_s`/tower — this is the pure additive layer.

The notations are arity-dispatched: a sort whose substitution vector has length `k` gets a
`Subst{k}`/`Ren{k}` instance. We emit instances for `k ∈ {1,…,5}` (matching the reference's class
set and our notation set); vectors longer than 5 simply get no notation (raw ops still apply).

`asimp` is **notation-native**: its σ-calculus rewrite set is stated over the class methods /
notations ([Gen/Laws.lean]). So this module emits, per sort/arity, the `@[asimp_lemmas]` **canon**
lemmas that rewrite each construct *toward* `asimp`'s normal form:

* `substCanon{k}`/`renCanon{k}` (`subst_s σ⃗ = subst{k} σ⃗`, …) — raw op ⟶ the `[σ⃗]`/`⟨ξ⃗⟩` method
  form, so subst/ren applications display in notation;
* `varIds` (`ids = var_s`) and `upLift` (`up = up_s_s`) — the `ids`/`⇑` notations ⟶ the *raw*
  `var_s` ctor / `up_b_v` helper (the forms the push laws use and that the up-unfolds then expand).

Each is stated in the orientation it should rewrite and tagged plainly forward (inline `←` would not
reverse it for this custom set — see [Tactic/Attr.lean]). The opposite, *untagged* `rfl` bridges
`substApp{k}`/`renApp{k}` (`subst{k} σ⃗ = subst_s σ⃗`, …) are kept as the user-facing escape hatch for
unfolding a notation form back to the raw op in a bespoke `simp only` (e.g. the SysfSN regression
uses `renApp2_tm`).
-/
import Autosubst.Gen.Subst
import Autosubst.Prelude.Notation
import Autosubst.Tactic.Attr

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-- Apply term `f` to a list of argument terms (left-associated). -/
private def appT (f : Term) (args : List Term) : CommandElabM Term := do
  let mut t := f
  for a in args do t ← `($t $a)
  pure t

/-- Coerce an identifier into a `term` syntax. -/
private def idT (i : Ident) : Term := ⟨i.raw⟩

/-- The `Subst{k}`/`Ren{k}` class and projection names for vector length `k` (1 ≤ k ≤ 5). -/
def substClsP (k : Nat) : Option (Name × Name) :=
  match k with
  | 1 => some (``Autosubst.Subst1, ``Autosubst.Subst1.subst1)
  | 2 => some (``Autosubst.Subst2, ``Autosubst.Subst2.subst2)
  | 3 => some (``Autosubst.Subst3, ``Autosubst.Subst3.subst3)
  | 4 => some (``Autosubst.Subst4, ``Autosubst.Subst4.subst4)
  | 5 => some (``Autosubst.Subst5, ``Autosubst.Subst5.subst5)
  | _ => none

def renClsP (k : Nat) : Option (Name × Name) :=
  match k with
  | 1 => some (``Autosubst.Ren1, ``Autosubst.Ren1.ren1)
  | 2 => some (``Autosubst.Ren2, ``Autosubst.Ren2.ren2)
  | 3 => some (``Autosubst.Ren3, ``Autosubst.Ren3.ren3)
  | 4 => some (``Autosubst.Ren4, ``Autosubst.Ren4.ren4)
  | 5 => some (``Autosubst.Ren5, ``Autosubst.Ren5.ren5)
  | _ => none

/-- Per-sort notation-dispatch instances (`Subst{k}`/`Ren{k}` + `Var`), the `@[asimp_lemmas]`
**canon** lemmas (raw ⟶ method: `substCanon{k}`/`renCanon{k}`/`varIds`/`upLift`), and the untagged
reverse `rfl` bridges (method ⟶ raw: `substApp{k}`/`renApp{k}`) for every substitution sort of `sig`,
in both backends. Emits a class for every vector length `1 ≤ k ≤ 5`; longer vectors (no
class/notation) get only the `Var` instance. -/
def genNotationCommands (sc : Bool) (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let mut out : Array (TSyntax `command) := #[]
  let varCls  := mkIdent ``Autosubst.Var
  let idsP    := mkIdent ``Autosubst.Var.ids
  -- Bind the signature's sort parameters (e.g. `{Srt : Type}`) on every emitted instance/bridge,
  -- so parameterized sorts get the same notation-dispatch layer as non-parameterized ones.
  let pbs ← sigImplicitBinders sig
  -- map-binder idents σ₁ … σₖ for a bridge over `k` maps.
  let mapNames (pfx : String) (k : Nat) : Array Ident :=
    (Array.range k).map fun i => mkIdent (Name.mkSimple s!"{pfx}{i+1}")
  for comp in sig.components do
    for si in substSortsOf sig comp do
      let s := si.name
      let vec := si.substVec
      let k := vec.length
      -- subject `s<m>` / result `s<n>`, and one map per vector component (stage m ⟶ n).
      let dom ← sortTyAt sc sig s "m"
      let cod ← sortTyAt sc sig s "n"
      let substMaps ← vec.mapM (fun v => mapTy sc sig false v "m" "n")
      let renMaps   ← vec.mapM (fun v => mapTy sc sig true  v "m" "n")
      let substId := mkIdent (substName s)
      let renId   := mkIdent (renName s)
      -- `Subst{k}`/`Ren{k}` instances + their canon lemmas and reverse bridges, generated uniformly
      -- for any vector length 1 ≤ k ≤ 5 (the arities for which a class/notation exists; longer
      -- vectors simply get no notation). All four are stated **unapplied** (`subst{k} σ⃗` vs
      -- `subst_s σ⃗`) so they normalize both the function-level forms (`[σ]`/`⟨ξ⟩` in `funcomp`) and,
      -- since simp rewrites subterms, the applied forms.
      if let (some (sCls, sProj), some (rCls, rProj)) := (substClsP k, renClsP k) then
        let sClsI := mkIdent sCls; let sProjI := mkIdent sProj
        let rClsI := mkIdent rCls; let rProjI := mkIdent rProj
        let iSubst := mkIdent (Name.mkSimple s!"instSubst{k}_{s}")
        let iRen   := mkIdent (Name.mkSimple s!"instRen{k}_{s}")
        let bSubst := mkIdent (Name.mkSimple s!"substApp{k}_{s}")
        let bRen   := mkIdent (Name.mkSimple s!"renApp{k}_{s}")
        -- instance types: `Subst{k} dom sm₁ … smₖ cod`, `Ren{k} dom rm₁ … rmₖ cod`.
        let sInstTy ← appT sClsI ([dom] ++ substMaps ++ [cod])
        let rInstTy ← appT rClsI ([dom] ++ renMaps ++ [cod])
        out := out.push (← `(command| instance $iSubst:ident $pbs* : $sInstTy := ⟨$substId⟩))
        out := out.push (← `(command| instance $iRen:ident $pbs* : $rInstTy := ⟨$renId⟩))
        -- **canon** lemmas (tagged `@[asimp_lemmas]`, oriented raw ⟶ method): rewrite a raw
        -- `subst_s σ⃗`/`ren_s ξ⃗` *into* the notation method form, so `asimp` output stays in notation.
        -- (Stated raw-LHS = method-RHS so a plain forward tag does the canon; the reverse-oriented
        -- `bridge` lemmas below stay untagged, available as defeq rewrites for other code.)
        let sBinders ← (mapNames "σ" k |>.zip substMaps.toArray).mapM fun (nm, ty) =>
          `(Lean.Parser.Term.bracketedBinderF| ($nm : $ty))
        let sLhs ← appT sProjI ((mapNames "σ" k).toList.map idT)
        let sRhs ← appT substId ((mapNames "σ" k).toList.map idT)
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"substCanon{k}_{s}")) $pbs* $sBinders* :
            $sRhs = $sLhs := rfl))
        out := out.push (← `(command| theorem $bSubst $pbs* $sBinders* : $sLhs = $sRhs := rfl))
        -- ren: renaming maps (`Nat → Nat`) carry no sort, so for parameterized sorts the unapplied
        -- `ren{k} ξ⃗` form cannot infer the sort — ascribe both sides to `dom → cod`.
        let rBinders ← (mapNames "ξ" k |>.zip renMaps.toArray).mapM fun (nm, ty) =>
          `(Lean.Parser.Term.bracketedBinderF| ($nm : $ty))
        let rLhs0 ← appT rProjI ((mapNames "ξ" k).toList.map idT)
        let rRhs0 ← appT renId ((mapNames "ξ" k).toList.map idT)
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"renCanon{k}_{s}")) $pbs* $rBinders* :
            ($rRhs0 : $dom → $cod) = ($rLhs0 : $dom → $cod) := rfl))
        out := out.push (← `(command| theorem $bRen $pbs* $rBinders* :
            ($rLhs0 : $dom → $cod) = ($rRhs0 : $dom → $cod) := rfl))
      -- `Var` (for `t..`): the variable injection, index type ⟶ the sort, + its unfold bridge.
      if si.isOpen then
        let varCtor := mkIdent (s ++ varName s)
        let idxTy ← if sc then `(Fin $(scopeVar "m" s)) else `(Nat)
        let bVar := mkIdent (Name.mkSimple s!"varIds_{s}")
        let iVar := mkIdent (Name.mkSimple s!"instVar_{s}")
        out := out.push (← `(command| instance $iVar:ident $pbs* : $varCls $dom $idxTy := ⟨$varCtor⟩))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bVar) $pbs* : ($idsP : $idxTy → $dom) = $varCtor := rfl))
  -- `⇑` (the binder lift) is dispatched only when **a single open sort** makes the binder sort `b`
  -- and component sort `v` both forced (b = v = the lone open sort `s`, lift `up_s_s`). With ≥2 open
  -- sorts the same map type is lifted by several binder sorts (no unique `⇑`), so it is omitted and
  -- the explicit `up_b_v` names stand.
  match openSorts sig with
  | [s] =>
    let upI    := mkIdent ``Autosubst.Up
    let upP    := mkIdent ``Autosubst.Up.up
    let upId   := mkIdent (upName s s)
    let bUp    := mkIdent (Name.mkSimple s!"upLift_{s}")
    let iUp    := mkIdent (Name.mkSimple s!"instUp_{s}")
    -- `X` = a `(m ⟶ n)` substitution map for `s`; `X'` = the lifted `(m+1 ⟶ n+1)` map.
    let dom ← mapTy sc sig false s "m" "n"
    let cod ← if sc then `(Fin ($(scopeVar "m" s) + 1) → $(← sortTyAt false sig s "n") ($(scopeVar "n" s) + 1))
              else `(Nat → $(← sortTyAt false sig s "n"))
    out := out.push (← `(command| instance $iUp:ident $pbs* : $upI $dom $cod := ⟨$upId⟩))
    out := out.push (← `(command|
      @[asimp_lemmas] theorem $(bUp) $pbs* : ($upP : $dom → $cod) = $upId := rfl))
  | _ => pure ()
  return out

end Autosubst.Gen
