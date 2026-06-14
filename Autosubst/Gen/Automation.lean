/-
# σ-calculus law generation + simp-set registration (the `asimp` automation).

Two jobs, both run after the notation instances ([Gen/Notation.lean]): `genLawCommands` emits the
σ-calculus rewrite set, and `genAutomationCommands` (at the end) registers the `up_*` lifting-helper
unfolds. Together they are everything `autosubst` adds for the `asimp`/`substify`/`renamify` tactics.

The rewrite set is **stated over the typeclass-method / notation forms**
(`s[σ⃗]`, `s⟨ξ⃗⟩`, `.:`, `>>`, `var_s`) rather than the raw `subst_s`/`ren_s` ops — so `asimp`
*output* is in notation, mirroring Coq's `asimpl`. Design:

* **Method heads.** Subst/ren applications use `Subst{k}.subst{k}`/`Ren{k}.ren{k}` for vector length
  `1 ≤ k ≤ 5` (the notation arities), falling back to the raw op for longer vectors.
* **`up` is unfolded**, per the Coq reference (`asimpl`'s `unfold up_*`): the generated `up_b_v`
  equation lemmas (tagged in `Gen/Automation.lean`) expand a lift to its `scons`/`funcomp`/`ren shift`
  form, which the static `scons`/`funcomp` laws then close. There is therefore *no* fold/unfold
  split and no fold-back pass — every lemma here keeps the calculus in method form throughout.
* **Canon.** The canon lemmas (in `Gen/Notation.lean`) rewrite each construct *toward* `asimp`'s
  normal form: a raw `subst_s`/`ren_s` arriving from outside `asimp` ⟶ the `[σ⃗]`/`⟨ξ⃗⟩` method form
  (`substCanon{k}`/`renCanon{k}`); the `ids` and `⇑` notations ⟶ the raw `var_s` ctor / `up_b_v`
  helper (`varIds`/`upLift`) — i.e. the very forms the push laws are stated in (`var_s`) and that the
  up-unfolds then expand (`up_b_v`). So variables stay as the raw `var_s` ctor while subst/ren
  applications stay in notation.

These are the **single, canonical** σ-calculus lemma suite — there is no separate raw-op wrapper
layer. Each is proved directly from the recursive tower (`compRenRen_s`, `idSubst_s`,
`rinst_inst_s`, …) and is definitionally equal to the raw statement, so it is sound by construction.
Each carries its own `@[asimp_lemmas]`. (The only raw-op equational lemmas that survive are the
recursive tower itself — the structural-recursion foundation, which cannot be method form for
container positions or `k > 5` vectors anyway — and the `rinstInst'_s`/`rinstInst_s` bridge in
[Gen/Lemmas.lean], used by `substify`/`renamify`.)

## Naming convention

The lemmas keep Coq Autosubst's canonical names, now stated in method/notation form:

* `…_<s>`  — the **applied** form (a subject term is present): `renRen_<s>`, `renSubst_<s>`,
  `substRen_<s>`, `substSubst_<s>`; and the identity `instId'_<s>` / `rinstId'_<s>`.
* `…'_<s>` — the **map-level / funext** form (an equation between unapplied `[σ⃗]`/`⟨ξ⃗⟩` functions,
  fired when a fusion sits as a `funcomp` argument): `renRen'_<s>`, …, `substSubst'_<s>`. For the
  identity laws the polarity is the Coq one — `instId_<s>` / `rinstId_<s>` are the funext forms,
  `instId'_<s>` / `rinstId'_<s>` the applied ones.
* `varL_<s>` / `varLRen_<s>` — the variable laws (`[σ⃗] >> var = σ`, …); inherently map-level
  (`funcomp`-shaped), so no separate applied/primed split.
* `<pfx>_push_<s>_<ctor>` — the per-constructor push laws, `pfx ∈ {sigma, xi}` (subst / ren); the
  variable case is `<pfx>_push_<s>_var`.

The raw⟶method **canon** lemmas in [Gen/Notation.lean] follow `substCanon{k}_<s>` /
`renCanon{k}_<s>` / `varIds_<s>` / `upLift_<s>`; their untagged reverse bridges are
`substApp{k}_<s>` / `renApp{k}_<s>`.
-/
import Autosubst.Gen.Lemmas
import Autosubst.Gen.Notation
import Autosubst.Gen.Inductive

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-! ## Method-form heads -/

/-- The op application `op_w maps… arg`, stated with the **method head** `Subst{k}.subst{k}` /
`Ren{k}.ren{k}` (= the `s[σ⃗]`/`s⟨ξ⃗⟩` notation) when `k = |vec w|` is in `1…5`, else the raw op. -/
def methodOpApp (forRen : Bool) (sig : Signature) (w : SortId) (maps : List Term) (arg : Term) :
    CommandElabM Term := do
  let k := (vecOf sig w).length
  let clsP := if forRen then renClsP k else substClsP k
  match clsP with
  | some (_, proj) => appAll (mkIdent proj) (maps ++ [arg])
  | none => appAll (mkIdent ((if forRen then renName else substName) w)) (maps ++ [arg])

/-- The op as an unapplied **function** (`[σ⃗]`/`⟨ξ⃗⟩` notation = `Subst{k}.subst{k} σ⃗`), method head
when `k ∈ 1…5`, else raw. -/
def methodOpFun (forRen : Bool) (sig : Signature) (w : SortId) (maps : List Term) :
    CommandElabM Term := do
  let k := (vecOf sig w).length
  let clsP := if forRen then renClsP k else substClsP k
  match clsP with
  | some (_, proj) => appAll (mkIdent proj) maps
  | none => appAll (mkIdent ((if forRen then renName else substName) w)) maps

/-- Lift map `m` (component `u`) under a *list* of binders (outermost first), in **folded** form:
each binder wraps `m` in the explicit generated lift helper `up_b_u`/`upRen_b_u` (or `up_list_b_u`
for a variadic binder), scope-correct in both backends. The push lemmas thus state the lift in the
same `up_b_v` form the raw equation lemmas compute to; `asimp` later *unfolds* those helpers (per the
Coq reference) and the static `scons`/`funcomp` laws close the calculus — there are no `up`-fusion
laws. -/
def liftMapMethod (forRen : Bool) (binders : List Binder) (u : SortId) (m : Term) :
    CommandElabM Term := do
  let mut m := m
  for bd in binders do
    m ← liftMapUnder forRen bd u m
  pure m

/-! ## Push lemmas (`(c …)[σ⃗] = c …`, folded, method form) -/

/-- The pushed form of one constructor-argument *head*, applied to the field variable `x`. A
substitutable sort position becomes `x[lifted σ⃗]` (method head); a recursive container (`List`,
`Option`, a user inductive) becomes its helper op over the lifted maps; the binary `Prod` is pushed
inline (`(push x.1, push x.2)`) exactly as `genHeadValue`/`genHeadProof` handle it — there is no
`Prod` helper; an `ext`/`opaque`/no-sort-inside position is unchanged. -/
partial def pushHeadTerm (containers : Containers) (forRen : Bool) (sig : Signature) (s : SortId)
    (pfx : String) (binders : List Binder) (head : IR.ArgHead) (x : Term) : CommandElabM Term := do
  match head with
  | .sort w _ =>
    let vecW := vecOf sig w
    if vecW.isEmpty then pure x
    else do
      let maps ← vecW.mapM fun u => liftMapMethod forRen binders u (idTm (mapIdent pfx u))
      methodOpApp forRen sig w maps x
  | .functor f args =>
    if isProdHead f then
      match args with
      | [a, b] =>
        let va ← pushHeadTerm containers forRen sig s pfx binders a (← `($x.1))
        let vb ← pushHeadTerm containers forRen sig s pfx binders b (← `($x.2))
        `(($va, $vb))
      | _ => pure x
    else if (args.flatMap ArgHead.argSorts).isEmpty then pure x
    else if (recContainerWord containers f).isSome then do
      let vecS := vecOf sig s
      let maps ← vecS.mapM fun u => liftMapMethod forRen binders u (idTm (mapIdent pfx u))
      appAll (mkIdent (helperOpName containers forRen s head)) (maps ++ [x])
    else pure x
  | .ext _ | .opaque _ => pure x

/-- The pushed form of one constructor argument at `pos`, applied to the field variable `x`. -/
def pushArgTerm (containers : Containers) (forRen : Bool) (sig : Signature) (s : SortId)
    (pfx : String) (pos : IR.Position) (x : Term) : CommandElabM Term :=
  pushHeadTerm containers forRen sig s pfx pos.binders pos.head x

/-- The push lemmas for sort `s`: one per constructor (and the variable law), for both families.
`(c x⃗)[σ⃗] = c (push x⃗)` — proved by `rfl` (the method heads are defeq to the raw ops, on which
`subst_s`/`ren_s` compute through the constructor). -/
def genPushLemmas (containers : Containers) (sc : Bool) (sig : Signature) (si : SortInfo) :
    CommandElabM (Array (TSyntax `command)) := do
  let s := si.name
  let vec := si.substVec
  let pbs ← sigImplicitBinders sig
  let mut out : Array (TSyntax `command) := #[]
  -- the subject's domain type `s<m>`; ascribed onto every subject so the `Subst{k}`/`Ren{k}`
  -- subject inParam is pinned (essential in the well-scoped multi-sort backend, where it would
  -- otherwise be left a metavar and stall instance resolution).
  let domTy ← sortTyAt sc sig s "m"
  for forRen in [false, true] do
    let pfx := if forRen then "xi" else "sigma"
    let mapBs ← mapBindersFor sc sig pfx forRen "m" "n" vec
    let mapTms := vec.map fun v => idTm (mapIdent pfx v)
    -- variable law (open sorts): `(var_s x)[σ⃗] = σ_s x` (subst) / `var_s (ξ_s x)` (ren).
    if si.isOpen then
      let xN := mkIdent `x
      let xTy ← if sc then `(Fin $(scopeVar "m" s)) else `(Nat)
      let lhs ← methodOpApp forRen sig s mapTms (← `(($(varCtorI s) $xN : $domTy)))
      let rhs ← if forRen then `($(varCtorI s) ($(mapIdent pfx s) $xN))
                else `($(mapIdent pfx s) $xN)
      out := out.push (← `(command|
        @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"{pfx}_push_{s}_var")) $pbs* $mapBs* ($xN : $xTy) :
          $lhs = $rhs := rfl))
    -- one lemma per user constructor.
    for c in si.ctors do
      let xs := (Array.range c.positions.length).map fun i => mkIdent (Name.mkSimple s!"x{i}")
      let ps := (c.params.map fun (pn, _) => mkIdent pn).toArray
      -- typed binders for the params and the field variables.
      let mut argBs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      for (pn, pty) in c.params do
        argBs := argBs.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent pn) : $(paramTypeTerm pty))))
      for (pos, x) in c.positions.toArray.zip xs do
        -- field variables live at the **domain** scope `"m"` (the input of the push), not the
        -- inductive's `"n"` — so the subject `c x⃗ : s<m>` matches `subst_s`'s `m ⟶ n` map vector.
        let fty ← headToTermAt sc sig "m" pos.binders pos.head
        argBs := argBs.push (← `(Lean.Parser.Term.bracketedBinderF| ($x : $fty)))
      let ctorHead := mkIdent (s ++ c.name)
      let ctorApp0 ← appAll ctorHead ((ps.map idTm).toList ++ (xs.map idTm).toList)
      let ctorApp ← `(($ctorApp0 : $domTy))
      let lhs ← methodOpApp forRen sig s mapTms ctorApp
      let pushed ← (c.positions.toArray.zip xs).mapM fun (pos, x) =>
        pushArgTerm containers forRen sig s pfx pos (idTm x)
      let rhs ← appAll ctorHead ((ps.map idTm).toList ++ pushed.toList)
      out := out.push (← `(command|
        @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"{pfx}_push_{s}_{c.name}")) $pbs* $mapBs* $argBs* :
          $lhs = $rhs := rfl))
  return out

/-! ## Fusion + identity + variable laws (method form, proved from the raw tower) -/

/-- One applied fusion law in method form, e.g. `(s⟨ξ⃗⟩)[τ⃗] = s[ξ⃗ >> τ⃗]`. `pfx1`/`isRen1` is the
inner op, `pfx2`/`isRen2` the outer; `mkTheta v` builds the `v`-component of the fused map. Proved by
the raw recursive `comp*` lemma (`mapArgs`, then per-component `fun _ => rfl` hypotheses) — defeq to
the method statement. -/
def genMethodComp (sc : Bool) (sig : Signature) (si : SortInfo) (nm nmF : Name) (compNm : SortId → Name)
    (pfx1 : String) (isRen1 : Bool) (pfx2 : String) (isRen2 : Bool)
    (mkTheta : SortId → CommandElabM Term) : CommandElabM (Array (TSyntax `command)) := do
  let s := si.name; let vec := si.substVec; let tI := mkIdent `t
  let pbs ← sigImplicitBinders sig
  let resultRen := isRen1 && isRen2
  let b1 ← mapBindersFor sc sig pfx1 isRen1 "m" "k" vec
  let b2 ← mapBindersFor sc sig pfx2 isRen2 "k" "l" vec
  let tTy ← sortTyAt sc sig s "m"
  let tTyK ← sortTyAt sc sig s "k"
  let tTyL ← sortTyAt sc sig s "l"
  let thetas ← vec.mapM mkTheta
  let mapArgs := (vec.map fun v => idTm (mapIdent pfx1 v)) ++ (vec.map fun v => idTm (mapIdent pfx2 v))
  let inner ← methodOpApp isRen1 sig s (vec.map fun v => idTm (mapIdent pfx1 v)) (← `(($tI : $tTy)))
  let lhs ← methodOpApp isRen2 sig s (vec.map fun v => idTm (mapIdent pfx2 v)) inner
  let rhs ← methodOpApp resultRen sig s thetas (idTm tI)
  let proof ← appAll (mkIdent (compNm s))
    (mapArgs ++ (← unders vec.length) ++ (← vec.mapM fun _ => `(fun _ => rfl)) ++ [idTm tI])
  let applied ← `(command| @[asimp_lemmas] theorem $(mkIdent nm) $pbs* $b1* $b2* ($tI : $tTy) :
      $lhs = $rhs := $proof)
  -- map-level (funext) form `op2 ∘ op1 = result` — fires when a fusion appears as a `funcomp` at the
  -- map level (e.g. inside an unfolded `up`, `σ >> ⟨↑⟩ >> [τ]`). Ascribe both sides to pin the
  -- `Subst{k}`/`Ren{k}` subjects of the unapplied function forms.
  let op1Fun0 ← methodOpFun isRen1 sig s (vec.map fun v => idTm (mapIdent pfx1 v))
  let op2Fun0 ← methodOpFun isRen2 sig s (vec.map fun v => idTm (mapIdent pfx2 v))
  let op1Fun ← `(($op1Fun0 : $tTy → $tTyK))
  let op2Fun ← `(($op2Fun0 : $tTyK → $tTyL))
  let lhsF ← `($funcompI $op2Fun $op1Fun)
  let rhsF0 ← methodOpFun resultRen sig s thetas
  let rhsF ← `(($rhsF0 : $tTy → $tTyL))
  let funextForm ← `(command| @[asimp_lemmas] theorem $(mkIdent nmF) $pbs* $b1* $b2* :
      $lhsF = $rhsF := $funextI $(← appAll (mkIdent nm) mapArgs))
  return #[applied, funextForm]

/-- The asimp-facing **method-form** σ-calculus laws for sort `s`, emitted under the **canonical**
lemma names (`renRen_s`/`substSubst_s`/`instId_s`/`rinstId_s`/`varL_s`/…). These are the single
public σ-calculus suite — there is no separate raw-op wrapper layer; they are proved directly from
the recursive tower (`compRenRen_s`/`idSubst_s`/`rinst_inst_s`), to which they are definitionally
equal. Convention (see the module header): `…_s` = applied form, `…'_s` = map-level (funext) form;
the identity laws follow the Coq-Autosubst polarity (`instId'_s` applied, `instId_s` funext). -/
def genMethodWrappers (sc : Bool) (sig : Signature) (si : SortInfo) :
    CommandElabM (Array (TSyntax `command)) := do
  let s := si.name; let vec := si.substVec; let tI := mkIdent `t
  let pbs ← sigImplicitBinders sig
  let fc (g f : Term) : CommandElabM Term := `($funcompI $g $f)
  let tTy ← sortTyAt sc sig s "m"
  let mut out : Array (TSyntax `command) := #[]
  -- fusion (applied + map-level): renRen / renSubst / substRen / substSubst.
  out := out ++ (← genMethodComp sc sig si (Name.mkSimple s!"renRen_{s}") (Name.mkSimple s!"renRen'_{s}") compRenRenName "xi" true "zeta" true
    (fun v => fc (mapIdent "zeta" v) (mapIdent "xi" v)))
  out := out ++ (← genMethodComp sc sig si (Name.mkSimple s!"renSubst_{s}") (Name.mkSimple s!"renSubst'_{s}") compRenSubstName "xi" true "tau" false
    (fun v => fc (mapIdent "tau" v) (mapIdent "xi" v)))
  out := out ++ (← genMethodComp sc sig si (Name.mkSimple s!"substRen_{s}") (Name.mkSimple s!"substRen'_{s}") compSubstRenName "sigma" false "zeta" true
    (fun v => do fc (← methodOpFun true sig v ((vecOf sig v).map fun w => idTm (mapIdent "zeta" w))) (mapIdent "sigma" v)))
  out := out ++ (← genMethodComp sc sig si (Name.mkSimple s!"substSubst_{s}") (Name.mkSimple s!"substSubst'_{s}") compSubstSubstName "sigma" false "tau" false
    (fun v => do fc (← methodOpFun false sig v ((vecOf sig v).map fun w => idTm (mapIdent "tau" w))) (mapIdent "sigma" v)))
  -- identity: `s[var⃗] = s` (`instId'`), `[var⃗] = id` (`instId`), `s⟨id⃗⟩ = s` (`rinstId'`),
  -- `⟨id⃗⟩ = id` (`rinstId`). The `var`/`id` maps are ascribed to their (identity, `m ⟶ m`) map
  -- types — a class method, unlike the raw op, does not pin its inParam map type from its signature,
  -- so an unascribed `var_v`/`id` leaves the scope a metavar and stalls instance resolution.
  -- Proved from the recursive tower: `idSubst_s` (with `σ⃗ := var⃗`) and `rinst_inst_s`
  -- (with `ξ⃗ := id⃗`, `σ⃗ := var⃗`), discharging each pointwise hypothesis with `fun _ => rfl`.
  let varVec ← vec.mapM fun v => do `(($(varCtorI v) : $(← mapTy sc sig false v "m" "m")))
  let idVec ← vec.mapM fun v => do `((id : $(← mapTy sc sig true v "m" "m")))
  let rflHyps ← vec.mapM fun _ => `(fun _ => rfl)
  let idSubstApp ← appAll (mkIdent (idSubstName s)) (varVec ++ rflHyps ++ [idTm tI])
  let substVarApp ← methodOpApp false sig s varVec (← `(($tI : $tTy)))
  out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"instId'_{s}")) $pbs* ($tI : $tTy) :
      $substVarApp = $tI := $idSubstApp))
  let substVarFun ← methodOpFun false sig s varVec
  out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"instId_{s}")) $pbs* :
      ($substVarFun : $tTy → $tTy) = id := $funextI (fun $tI => $idSubstApp)))
  let rinstApp ← appAll (mkIdent (rinstInstName s)) (idVec ++ varVec ++ rflHyps ++ [idTm tI])
  let rinstIdProof ← `(($rinstApp).trans $idSubstApp)
  let renIdApp ← methodOpApp true sig s idVec (← `(($tI : $tTy)))
  out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"rinstId'_{s}")) $pbs* ($tI : $tTy) :
      $renIdApp = $tI := $rinstIdProof))
  let renIdFun ← methodOpFun true sig s idVec
  out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"rinstId_{s}")) $pbs* :
      ($renIdFun : $tTy → $tTy) = id := $funextI (fun $tI => $rinstIdProof)))
  -- variable laws (open sorts): `[σ⃗] >> var_s = σ_s`, `⟨ξ⃗⟩ >> var_s = var_s >> ξ_s`. These hold
  -- definitionally (the method head `[σ⃗]`/`⟨ξ⃗⟩` is defeq to the raw op, which computes on `var_s`),
  -- so the proof is `rfl`. The unapplied function forms `[σ⃗]`/`⟨ξ⃗⟩` carry no subject, so the
  -- `Subst{k}`/`Ren{k}` subject inParam must be ascribed or instance resolution stalls.
  if si.isOpen then
    let tTyN ← sortTyAt sc sig s "n"
    let bsig ← mapBindersFor sc sig "sigma" false "m" "n" vec
    let bxi  ← mapBindersFor sc sig "xi" true "m" "n" vec
    let substFun0 ← methodOpFun false sig s (vec.map fun v => idTm (mapIdent "sigma" v))
    let substFun ← `(($substFun0 : $tTy → $tTyN))
    let lhsL ← fc substFun (idTm (varCtorI s))
    out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"varL_{s}")) $pbs* $bsig* :
        $lhsL = $(mapIdent "sigma" s) := rfl))
    let renFun0 ← methodOpFun true sig s (vec.map fun v => idTm (mapIdent "xi" v))
    let renFun ← `(($renFun0 : $tTy → $tTyN))
    let lhsLR ← fc renFun (idTm (varCtorI s))
    let rhsLR ← fc (idTm (varCtorI s)) (mapIdent "xi" s)
    out := out.push (← `(command| @[asimp_lemmas] theorem $(mkIdent (Name.mkSimple s!"varLRen_{s}")) $pbs* $bxi* :
        $lhsLR = $rhsLR := rfl))
  return out

/-! ## Method-form `substify` / `renamify` bridge -/

/-- The **notation-native** ren⇒subst bridge for `substify`/`renamify` — the *only* `rinstInst`
lemmas (there is no raw-op wrapper). For any sort with a `Ren{k}`/`Subst{k}` class (`1 ≤ k ≤ 5`),
all backends, multi-sort and parameterized, under the canonical names:

* `rinstInst'_s : s⟨ξ⃗⟩ = s[var⃗ ∘ ξ⃗]` (applied) and
* `rinstInst_s  : (⟨ξ⃗⟩ : s<m> → s<n>) = ([var⃗ ∘ ξ⃗] : …)` (funext/map-level),

both proved from the recursive `rinst_inst_s` tower (defeq). They are tagged `@[substify_lemmas]`
forward (`s⟨ξ⃗⟩ ⟶ s[var⃗ ∘ ξ⃗]`) and, via the standalone `attribute … ←` command (inline `←` would
not reverse — see [Tactic/Attr.lean]), `[renamify_lemmas ←]` (`s[var⃗ ∘ ξ⃗] ⟶ s⟨ξ⃗⟩`).

The subst maps use the **raw `var_s` ctor** (`funcomp var_s ξ`), matching `asimp`'s normal form (where
`varIds` has already pushed `Var.ids` to the ctor); `varIds_s` is additionally tagged into both sets
so a goal written with the `Var.ids` notation is first normalized to the same ctor form. Sorts with
`k > 5` have no notation/class, so they get no `rinstInst` lemma — `substify`/`renamify` are
notation-only and do not apply there. -/
def genRinstInstMethod (sc : Bool) (sig : Signature) (si : SortInfo) :
    CommandElabM (Array (TSyntax `command)) := do
  let s := si.name; let vec := si.substVec; let tI := mkIdent `t
  if (renClsP vec.length).isNone then return #[]   -- k > 5: no notation, raw bridge suffices
  let pbs ← sigImplicitBinders sig
  let tTy ← sortTyAt sc sig s "m"
  let tTyN ← sortTyAt sc sig s "n"
  let bxi ← mapBindersFor sc sig "xi" true "m" "n" vec
  let xiMaps := vec.map fun v => idTm (mapIdent "xi" v)
  -- the subst maps `funcomp var_v ξ_v`, **ascribed** to their (m ⟶ n) map type so the `Subst{k}`
  -- inParam is pinned (else the var ctor's scope/param is left a metavar and instance resolution
  -- stalls — scoped / parameterized / multi-sort), exactly as `genMethodWrappers` ascribes `var⃗`.
  let varXiMaps ← vec.mapM fun v => do
    `((($funcompI $(varCtorI v) $(mapIdent "xi" v)) : $(← mapTy sc sig false v "m" "n")))
  let rflHyps ← vec.mapM fun _ => `(fun _ => rfl)
  let appNm := rinstInstPName s    -- canonical `rinstInst'_s` (applied)
  let funNm := rinstInstWName s    -- canonical `rinstInst_s`  (funext)
  let mut out : Array (TSyntax `command) := #[]
  -- applied: `s⟨ξ⃗⟩ = s[var⃗ ∘ ξ⃗]`, proved from the recursive `rinst_inst_s` tower (with `σ⃗ := var⃗ ∘ ξ⃗`,
  -- each pointwise hypothesis `fun _ => rfl`); defeq to the method statement.
  let lhsApp ← methodOpApp true sig s xiMaps (← `(($tI : $tTy)))
  let rhsApp ← methodOpApp false sig s varXiMaps (idTm tI)
  let proofApp ← appAll (mkIdent (rinstInstName s)) (xiMaps ++ varXiMaps ++ rflHyps ++ [idTm tI])
  out := out.push (← `(command| @[substify_lemmas] theorem $(mkIdent appNm) $pbs* $bxi* ($tI : $tTy) :
      $lhsApp = $rhsApp := $proofApp))
  -- funext: `(⟨ξ⃗⟩ : s<m> → s<n>) = ([var⃗ ∘ ξ⃗] : …)`, by `funext` of the applied lemma.
  let lhsFun0 ← methodOpFun true sig s xiMaps
  let rhsFun0 ← methodOpFun false sig s varXiMaps
  let appFn ← appAll (mkIdent appNm) xiMaps
  out := out.push (← `(command| @[substify_lemmas] theorem $(mkIdent funNm) $pbs* $bxi* :
      ($lhsFun0 : $tTy → $tTyN) = ($rhsFun0 : $tTy → $tTyN) := $funextI $appFn))
  -- reverse-orient both into `renamify_lemmas` (standalone `attribute … ←` honours the direction)
  out := out.push (← `(command| attribute [renamify_lemmas ←] $(mkIdent appNm) $(mkIdent funNm)))
  -- normalize the `Var.ids` notation to the raw `var_s` ctor in both sets, so either spelling matches
  if si.isOpen then
    let vids := mkIdent (Name.mkSimple s!"varIds_{s}")
    out := out.push (← `(command| attribute [substify_lemmas] $vids))
    out := out.push (← `(command| attribute [renamify_lemmas] $vids))
  return out

/-! ## Orchestration -/

/-- All notation-native `asimp` lemmas for `sig`: the per-constructor push laws, the method-form
fusion / identity / variable laws, and the method-form `substify`/`renamify` bridge. (Per the Coq
reference, `up` is *unfolded* by `asimp` rather than kept folded, so there are no extra up-fusion
laws — the static `scons`/`funcomp` laws close the calculus after the generated `up_b_v` equation
lemmas fire.) Emitted after the notation instances so the `Subst{k}`/`Var` methods resolve. -/
def genLawCommands (containers : Containers) (sc : Bool) (sig : Signature) :
    CommandElabM (Array (TSyntax `command)) := do
  let mut out : Array (TSyntax `command) := #[]
  for comp in sig.components do
    for si in substSortsOf sig comp do
      out := out ++ (← genPushLemmas containers sc sig si)
      out := out ++ (← genMethodWrappers sc sig si)
      out := out ++ (← genRinstInstMethod sc sig si)
  return out

/-! ## Lifting-helper registration (the `up_*` unfolds)

The σ-calculus rewrite set, the canon lemmas, and the `substify`/`renamify` bridge all carry their
own inline tags (above, and in [Gen/Notation.lean]). The one thing left to register by a standalone
`attribute` command is the per-sort lifting helpers `up_b_v`/`upRen_b_v` (and the variadic
`up_list_b_v`/`upRen_list_b_v`): they go into `asimp_lemmas` **and** `auto_unfold_lemmas`, so
`asimp`/`auto_unfold` unfold a lift to its `scons`/`funcomp`/`ren shift` body — mirroring the Coq
reference's `asimpl`'s `unfold up_*`. No raw `subst_s`/`ren_s` op is ever tagged into any set. -/
def genAutomationCommands (sig : Signature) : CommandElabM (Array (TSyntax `command)) := do
  let opens := openSorts sig
  let mut out : Array (TSyntax `command) := #[]
  -- unfold the lifting functions (Coq's `unfold up_* upRen_* up_list_* upRen_list_*`)
  let mut ups : Array Ident := #[]
  for b in opens do
    for v in opens do
      ups := ups.push (mkIdent (upName b v))
      ups := ups.push (mkIdent (upRenName b v))
  for b in variadicBoundSorts sig do
    for v in opens do
      ups := ups.push (mkIdent (upListName b v))
      ups := ups.push (mkIdent (upRenListName b v))
  if ups.size > 0 then
    out := out.push (← `(command| attribute [asimp_lemmas] $ups*))
    -- the same lifting helpers back the standalone `auto_unfold` tactic
    out := out.push (← `(command| attribute [auto_unfold_lemmas] $ups*))
  return out

end Autosubst.Gen
