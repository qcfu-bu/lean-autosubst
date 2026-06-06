/-
# Notation-instance generation (the Autosubst-consistent notation pass).

Emits, per substitution sort, the typeclass instances that back the scoped notations in
`Prelude/Notation.lean` (`s[σ]`/`s⟨ξ⟩` and the two-map `s[σ;τ]`/`s⟨ξ;ζ⟩`, the function forms,
and `t..` via `Var`/`ids`). Mirrors the reference's per-sort `Subst_s`/`Ren_s`/`VarInstance_s`
instances (`unscoped.v`'s commented block + `codeGenerator.ml`). **No change** to the generated
`subst_s`/`ren_s`/`var_s`/tower — this is the pure additive layer.

The notations are arity-dispatched: a sort whose substitution vector has length `k` gets a
`Subst{k}`/`Ren{k}` instance. We emit instances for `k ∈ {1, 2}` (matching the notation set; the
reference goes to 5, but our examples never exceed 2 and higher arities simply get no notation).

Because the application notations expand to **class projections** (`Subst1.subst1 σ s`, not the raw
`subst_s σ s`), the `asimp`/`substify`/`renamify` simp lemmas — all phrased over the raw ops —
would not fire on a notation'd goal. So, mirroring the reference `asimpl`'s `unfold … subst1 ren1
ids …`, we also emit per-sort **`rfl` bridge lemmas** (`Subst1.subst1 σ s = subst_s σ s`, …) tagged
into the `asimp` set, which normalize the notation away before the tower lemmas rewrite.
-/
import LeanAutosubst.Gen.Subst
import LeanAutosubst.Prelude.Notation
import LeanAutosubst.Tactic.Attr

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-- Per-sort notation-dispatch instances (`Subst{k}`/`Ren{k}` + `Var`) and their `rfl` bridge
lemmas (`@[asimp_lemmas]`, unfolding the notation back to the raw op) for every substitution sort
of `sig`, in both backends. Skips sorts whose vector length is outside `{1,2}` (no notation). -/
def genNotationCommands (sc : Bool) (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let mut out : Array (TSyntax `command) := #[]
  let subst1I := mkIdent ``Autosubst.Subst1
  let subst2I := mkIdent ``Autosubst.Subst2
  let ren1I   := mkIdent ``Autosubst.Ren1
  let ren2I   := mkIdent ``Autosubst.Ren2
  let varCls  := mkIdent ``Autosubst.Var
  let subst1P := mkIdent ``Autosubst.Subst1.subst1
  let subst2P := mkIdent ``Autosubst.Subst2.subst2
  let ren1P   := mkIdent ``Autosubst.Ren1.ren1
  let ren2P   := mkIdent ``Autosubst.Ren2.ren2
  let idsP    := mkIdent ``Autosubst.Var.ids
  for comp in sig.components do
    for si in substSortsOf sig comp do
      unless si.params.isEmpty do
        continue
      let s := si.name
      let vec := si.substVec
      -- subject `s<m>` / result `s<n>`, and one map per vector component (stage m ⟶ n).
      let dom ← sortTyAt sc sig s "m"
      let cod ← sortTyAt sc sig s "n"
      let substMaps ← vec.mapM (fun v => mapTy sc sig false v "m" "n")
      let renMaps   ← vec.mapM (fun v => mapTy sc sig true  v "m" "n")
      let substId := mkIdent (substName s)
      let renId   := mkIdent (renName s)
      let bSubst1 := mkIdent (Name.mkSimple s!"substApp1_{s}")
      let bSubst2 := mkIdent (Name.mkSimple s!"substApp2_{s}")
      let bRen1   := mkIdent (Name.mkSimple s!"renApp1_{s}")
      let bRen2   := mkIdent (Name.mkSimple s!"renApp2_{s}")
      let iSubst1 := mkIdent (Name.mkSimple s!"instSubst1_{s}")
      let iSubst2 := mkIdent (Name.mkSimple s!"instSubst2_{s}")
      let iRen1   := mkIdent (Name.mkSimple s!"instRen1_{s}")
      let iRen2   := mkIdent (Name.mkSimple s!"instRen2_{s}")
      let iVar    := mkIdent (Name.mkSimple s!"instVar_{s}")
      -- The bridge lemmas are stated **unapplied** (`subst1 σ = subst_s σ`, not `subst1 σ s = …`)
      -- so they also normalize the function-level forms `[σ]`/`⟨ξ⟩` inside `funcomp`, and (since
      -- simp rewrites subterms) the applied forms `s[σ]`/`s⟨ξ⟩` as well.
      match vec, substMaps, renMaps with
      | [_], [sm], [rm] =>
        out := out.push (← `(command| instance $iSubst1:ident : $subst1I $dom $sm $cod := ⟨$substId⟩))
        out := out.push (← `(command| instance $iRen1:ident : $ren1I $dom $rm $cod := ⟨$renId⟩))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bSubst1) (σ : $sm) : $subst1P σ = $substId σ := rfl))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bRen1) (ξ : $rm) : $ren1P ξ = $renId ξ := rfl))
      | [_, _], [sm1, sm2], [rm1, rm2] =>
        out := out.push (← `(command| instance $iSubst2:ident : $subst2I $dom $sm1 $sm2 $cod := ⟨$substId⟩))
        out := out.push (← `(command| instance $iRen2:ident : $ren2I $dom $rm1 $rm2 $cod := ⟨$renId⟩))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bSubst2) (σ : $sm1) (τ : $sm2) : $subst2P σ τ = $substId σ τ := rfl))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bRen2) (ξ : $rm1) (ζ : $rm2) : $ren2P ξ ζ = $renId ξ ζ := rfl))
      | _, _, _ => pure ()
      -- `Var` (for `t..`): the variable injection, index type ⟶ the sort, + its unfold bridge.
      if si.isOpen then
        let varCtor := mkIdent (s ++ varName s)
        let idxTy ← if sc then `(Fin $(scopeVar "m" s)) else `(Nat)
        let bVar := mkIdent (Name.mkSimple s!"varIds_{s}")
        out := out.push (← `(command| instance $iVar:ident : $varCls $dom $idxTy := ⟨$varCtor⟩))
        out := out.push (← `(command|
          @[asimp_lemmas] theorem $(bVar) : ($idsP : $idxTy → $dom) = $varCtor := rfl))
  -- `⇑` (the binder lift) is dispatched only when **a single open sort** makes the binder sort `b`
  -- and component sort `v` both forced (b = v = the lone open sort `s`, lift `up_s_s`). With ≥2 open
  -- sorts the same map type is lifted by several binder sorts (no unique `⇑`), so it is omitted and
  -- the explicit `up_b_v` names stand.
  match openSorts sig with
  | [s] =>
    if !(sigParams sig).isEmpty then
      return out
    let upI    := mkIdent ``Autosubst.Up
    let upP    := mkIdent ``Autosubst.Up.up
    let upId   := mkIdent (upName s s)
    let bUp    := mkIdent (Name.mkSimple s!"upLift_{s}")
    let iUp    := mkIdent (Name.mkSimple s!"instUp_{s}")
    -- `X` = a `(m ⟶ n)` substitution map for `s`; `X'` = the lifted `(m+1 ⟶ n+1)` map.
    let dom ← mapTy sc sig false s "m" "n"
    let cod ← if sc then `(Fin ($(scopeVar "m" s) + 1) → $(← sortTyAt false sig s "n") ($(scopeVar "n" s) + 1))
              else `(Nat → $(← sortTyAt false sig s "n"))
    out := out.push (← `(command| instance $iUp:ident : $upI $dom $cod := ⟨$upId⟩))
    out := out.push (← `(command|
      @[asimp_lemmas] theorem $(bUp) : ($upP : $dom → $cod) = $upId := rfl))
  | _ => pure ()
  return out

end Autosubst.Gen
