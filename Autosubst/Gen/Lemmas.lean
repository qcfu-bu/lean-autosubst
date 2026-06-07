/-
# Phase 5/8 — Lemma-tower generation.

Generates the rewriting tower from the analyzed `Signature`, as proof *terms* templated on the
golden files (Coq `ap`↦`congrArg`, `eq_trans`↦`.trans`, `eq_sym`↦`.symm`), verified defeq /
provable against the hand-written golden tower (unscoped *and* well-scoped).

A recursive lemma (`idSubst`, `ext*`, `comp*`, `rinst_inst`) shares one skeleton: a structural
recursion on the term whose constructor cases apply `congr_<sort>_<ctor>` to per-position sub-proofs
(a recursive call at *lifted* maps under binders, or `rfl` for non-substitutable positions),
and whose variable case is family-specific. The per-family data is captured in `Family`;
`genRecLemma` is the shared emitter. The non-recursive `up_*` helper lemmas are emitted
separately.

Backend (plan.md §4/§8) via `sc : Bool`: only *types* change between unscoped and well-scoped
(maps `Nat → …` vs `Fin … → …`, results scope-indexed). Proof terms are shared, with one
exception — the `Nat` `0`/`n+1` case split in the `up_*` helpers becomes `Fin.cases` in scoped
mode (`Fin.cases` reduces definitionally on `0`/`Fin.succ`). Scope variables are free
identifiers Lean auto-binds (`autoImplicit`).
-/
import Lean
import Autosubst.Gen.Subst

open Lean Elab Command

namespace Autosubst.Gen
open Autosubst.IR

/-! ## Names & shared builders -/

def idSubstName       (s : SortId) : Name := Name.mkSimple s!"idSubst_{s}"
def extRenName        (s : SortId) : Name := Name.mkSimple s!"extRen_{s}"
def extName           (s : SortId) : Name := Name.mkSimple s!"ext_{s}"
def compRenRenName    (s : SortId) : Name := Name.mkSimple s!"compRenRen_{s}"
def compRenSubstName  (s : SortId) : Name := Name.mkSimple s!"compRenSubst_{s}"
def compSubstRenName   (s : SortId) : Name := Name.mkSimple s!"compSubstRen_{s}"
def compSubstSubstName (s : SortId) : Name := Name.mkSimple s!"compSubstSubst_{s}"
def rinstInstName     (s : SortId) : Name := Name.mkSimple s!"rinst_inst_{s}"

def upIdName        (b v : SortId) : Name := Name.mkSimple s!"upId_{b}_{v}"
def upExtRenName    (b v : SortId) : Name := Name.mkSimple s!"upExtRen_{b}_{v}"
def upExtName       (b v : SortId) : Name := Name.mkSimple s!"upExt_{b}_{v}"
def upRenSubstName  (b v : SortId) : Name := Name.mkSimple s!"up_ren_subst_{b}_{v}"
def rinstInstUpName (b v : SortId) : Name := Name.mkSimple s!"rinstInst_up_{b}_{v}"

def mapIdent (pfx : String) (v : SortId) : Ident := mkIdent (Name.mkSimple s!"{pfx}_{v}")
def hypIdent (v : SortId) : Ident := mkIdent (Name.mkSimple s!"h_{v}")
def varCtorI (v : SortId) : Ident := mkIdent (v ++ varName v)
def congrArgI : Ident := mkIdent ``congrArg

/-- The `_list` infix for a variadic binder's up-helper names (empty for a single binder). -/
def listInfix : IR.Binder → String
  | .single _ => ""
  | .vector _ _ => "_list"

/-- Binder-aware up-helper *lemma* name: `<base>_<b>_<v>` (single) or `<base>_list_<b>_<v>`
(variadic). -/
def upLemmaNameB (base : String) (bd : IR.Binder) (v : SortId) : Name :=
  Name.mkSimple s!"{base}{listInfix bd}_{bd.boundSort}_{v}"

/-- Lift map `m` for component `u` under binder `bd` (`up_b_u m` / `up_list_b_u p m`), reusing the
backend-side `upBinderName`. -/
def liftMapUnder (isRen : Bool) (bd : IR.Binder) (u : SortId) (m : Term) : CommandElabM Term := do
  let nm := mkIdent (upBinderName isRen bd u)
  match bd with
  | .single _   => `($nm $m)
  | .vector p _ => `($nm $(mkIdent p) $m)

/-- Apply `f` to a list of arguments. -/
def appAll (f : Term) (args : List Term) : CommandElabM Term := do
  let mut t := f
  for a in args do
    t ← `($t $a)
  pure t

/-- Coerce an identifier into a `term` syntax. -/
def idTm (i : Ident) : Term := ⟨i.raw⟩

/-- `op_s` (a `ren`/`subst`) applied to its component maps then `arg`. -/
def opApp (opNm : Name) (maps : List Ident) (arg : Term) : CommandElabM Term :=
  appAll (mkIdent opNm) ((maps.map idTm) ++ [arg])

/-- `ren_v` applied with `shift` on the `b`-component and `id` elsewhere. -/
def renShiftApp (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM Term :=
  appAll (mkIdent (renName v)) ((vecOf sig v).map fun w => if w == b then (shiftI sc : Term) else idI)

/-- `op_v` (`ren`/`subst`) applied to the maps `<pfx>_w` for `w ∈ vec v` — used in the `comp*`
hypotheses (e.g. `ren_v zeta_…`, `subst_v tau_…`). -/
def opOfVec (opNm : SortId → Name) (sig : Signature) (pfx : String) (v : SortId) : CommandElabM Term :=
  appAll (mkIdent (opNm v)) ((vecOf sig v).map fun w => idTm (mapIdent pfx w))

/-! ## Family descriptor + shared recursive emitter -/

/-- A map set in a recursive lemma: name prefix, renaming?, and the **scope stages** its maps
go from / to (used only in scoped mode to thread `Fin`-scopes; ignored when unscoped). -/
structure MapSet where
  pfx : String
  isRen : Bool
  domSt : String
  codSt : String

/-- Everything that distinguishes one recursive lemma family. -/
structure Family where
  /-- lemma name per sort. -/
  lemmaName : SortId → Name
  /-- the map-parameter sets. -/
  mapSets : List MapSet
  /-- per-component hypothesis type for component `v`. -/
  mkHyp : Signature → SortId → CommandElabM Term
  /-- the conclusion's two sides, given the sort and the bound term variable. -/
  mkConcl : Signature → SortId → Ident → CommandElabM (Term × Term)
  /-- the **container-helper** conclusion (Phase 9). -/
  mkConclList : Signature → (vec : List SortId) → (ho : Bool → Name) → Ident → CommandElabM (Term × Term)
  /-- variable-case proof, given the sort and the bound variable. -/
  varProof : SortId → Ident → CommandElabM Term
  /-- lifted hypothesis for the recursive call under `binders`, at component `u` (`sc`-aware
  because `compRenRen` lifts via the prelude `up_ren_ren`, which differs per backend). -/
  liftedHyp : Bool → Signature → List Binder → SortId → CommandElabM Term

/-- Map-parameter binders for a recursive lemma of `fam` over substitution vector `vec`. -/
def famMapBinders (sc : Bool) (sig : Signature) (fam : Family) (vec : List SortId) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for ms in fam.mapSets do
    for v in vec do
      params := params.push (← mapBinder sc sig ms.isRen v ms.domSt ms.codSt (Name.mkSimple s!"{ms.pfx}_{v}"))
  return params

/-- All parameter binders (maps + hypotheses) for a recursive lemma of `fam` over `vec`. -/
def recLemmaParams (sc : Bool) (sig : Signature) (fam : Family) (vec : List SortId) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut params ← famMapBinders sc sig fam vec
  for v in vec do
    params := params.push (← `(Lean.Parser.Term.bracketedBinderF| ($(hypIdent v) : $(← fam.mkHyp sig v))))
  return params

/-- The container-helper lemma name for `fam` at sort `s` and container head: `<lemma>_<shape>`. -/
def helperLemmaName (containers : Containers) (fam : Family) (s : SortId) (head : IR.ArgHead) : Name :=
  Name.mkSimple s!"{fam.lemmaName s}_{shapeSuffix containers head}"

/-- The congruence lemma name for a (real Lean) container constructor, e.g. `Tree.node` ↦
`congrC_Tree_node`. Used by the generic container-helper lemmas (the analogue of `cons_congr`). -/
def ctorCongrName (ctorName : Name) : Name :=
  Name.mkSimple s!"congrC_{ctorName.toString.replace "." "_"}"

/-- A congruence for a registered container's constructor `c` of `arity` arguments (after type
params): `c a₀ … = c b₀ …` from `hᵢ : aᵢ = bᵢ`. Field types are auto-bound implicits (`subst_vars`
discharges it), exactly like `genCongr` for sort constructors. -/
def genCtorCongr (ctorName : Name) (arity : Nat) : CommandElabM (TSyntax `command) := do
  let idents (pfx : String) : Array Ident :=
    (Array.range arity).map (fun i => mkIdent (Name.mkSimple s!"{pfx}{i}"))
  let as := idents "a"; let bs := idents "b"; let hs := idents "h"
  let cI := mkIdent ctorName
  `(command| theorem $(mkIdent (ctorCongrName ctorName)) $[($hs : $as = $bs)]* :
      $cI $as* = $cI $bs* := by subst_vars; rfl)

/-- The sub-proof for one constructor position of a recursive lemma. -/
partial def genRecPos (sc : Bool) (fam : Family) (sig : Signature) (pos : IR.Position) (x : Ident) :
    CommandElabM Term := do
  match pos.head with
  | .sort w _ =>
    let vecW := vecOf sig w
    if vecW.isEmpty then return (← `(rfl))
    -- map arguments: each set, lifted under binders, over w's components
    let mut mapArgs : List Term := []
    for ms in fam.mapSets do
      for u in vecW do
        let mut m : Term := mapIdent ms.pfx u
        for b in pos.binders do
          m ← liftMapUnder ms.isRen b u m
        mapArgs := mapArgs ++ [m]
    let hypArgs ← vecW.mapM (fun u => fam.liftedHyp sc sig pos.binders u)
    appAll (← appAll (mkIdent (fam.lemmaName w)) mapArgs) (hypArgs ++ [(x : Term)])
  | _ => `(rfl)

/-- Emit a recursive lemma for sort `si` in family `fam`. -/
def genRecLemma (sc : Bool) (fam : Family) (sig : Signature) (si : SortInfo) : CommandElabM (TSyntax `command) := do
  let s := si.name
  let vec := si.substVec
  let pbs ← sigImplicitBinders sig
  let params ← recLemmaParams sc sig fam vec
  let tId := mkIdent `t
  let (lhs, rhs) ← fam.mkConcl sig s tId
  let tTy ← sortTyAt sc sig s "m"
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  if si.isOpen then
    let x := mkIdent `x
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(varCtorI s) $x => $(← fam.varProof s x)))
  for c in si.ctors do
    let xs := (Array.range c.positions.length).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let ps := (c.params.map (fun (pn, _) => mkIdent pn)).toArray   -- variadic params bound in the pattern
    let pat ← `($(mkIdent (s ++ c.name)) $ps* $xs*)
    -- A leaf constructor (nullary, or all-`ext` like `const : Nat → tm`) is left unchanged by
    -- `ren`/`subst`, so its case is `rfl` — no `congr_<c>` needed (and for an all-`ext` ctor in
    -- scoped mode, `congr_<c>` would otherwise be the one with an un-inferable result scope).
    let rhs2 ← if ctorIsLeaf sig c then `(rfl) else do
      let proofs ← (c.positions.toArray.zip xs).mapM fun (pos, x) => genRecPos sc fam sig pos x
      appAll (mkIdent (congrName s c.name)) proofs.toList
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $rhs2))
  `(command| theorem $(mkIdent (fam.lemmaName s)) $pbs* $params* : ∀ ($tId : $tTy), $lhs = $rhs
      $alts:matchAlt*)

/-! ## Phase 9 — container sorts: the mutual lemma + `*_list` helper lemma. -/

/-- Does this sort have any container (functor) constructor position (⇒ container code path)? -/
def sortHasFunctor (_sig : Signature) (si : SortInfo) : Bool :=
  si.ctors.any (fun c => c.positions.any (fun p =>
    match p.head with | .functor _ _ => true | _ => false))

/-- The (maps then hyps) argument idents passed to a recursive-lemma call over `vec`. -/
def recLemmaArgs (fam : Family) (vec : List SortId) : List Term := Id.run do
  let mut a : List Term := []
  for ms in fam.mapSets do for v in vec do a := a ++ [idTm (mapIdent ms.pfx v)]
  for v in vec do a := a ++ [idTm (hypIdent v)]
  return a

/-- The proof of one position's field equation, recursing through container heads. -/
partial def genHeadProof (containers : Containers) (sc : Bool) (fam : Family) (sig : Signature)
    (s : SortId) (vecS : List SortId) (binders : List Binder) (head : IR.ArgHead) (x : Term) :
    CommandElabM Term := do
  let applyLemma (lemmaNm : Name) (vec : List SortId) (arg : Term) : CommandElabM Term := do
    let mut mapArgs : List Term := []
    for ms in fam.mapSets do
      for u in vec do
        let mut m : Term := mapIdent ms.pfx u
        for b in binders do
          m ← liftMapUnder ms.isRen b u m
        mapArgs := mapArgs ++ [m]
    let hypArgs ← vec.mapM (fun u => fam.liftedHyp sc sig binders u)
    appAll (← appAll (mkIdent lemmaNm) mapArgs) (hypArgs ++ [arg])
  match head with
  | .sort w _ => if (vecOf sig w).isEmpty then `(rfl) else applyLemma (fam.lemmaName w) (vecOf sig w) x
  | .functor f args =>
    if isProdHead f then
      match args with
      | [a, b] =>
        let pa ← genHeadProof containers sc fam sig s vecS binders a (← `($x.1))
        let pb ← genHeadProof containers sc fam sig s vecS binders b (← `($x.2))
        `($(mkIdent ``Prod.ext) $pa $pb)
      | _ => `(rfl)
    else match recContainerWord containers f with
      | some _ => applyLemma (helperLemmaName containers fam s head) vecS x
      | none => `(rfl)
  | .ext _ | .opaque _ => `(rfl)

/-- The proof of one container-constructor argument of `ArgKind` `k` (the lemma-side analogue of
`genHelperArg`): an element subproof via `genHeadProof` for the matching applied argument, a
recursive subproof via the helper lemma (`tailProof x`), or `rfl` for an inert argument. -/
def genHelperProofArg (containers : Containers) (sc : Bool) (fam : Family) (sig : Signature)
    (s : SortId) (vecS : List SortId) (args : List IR.ArgHead) (tailProof : Term) (k : ArgKind) (x : Ident) :
    CommandElabM Term := do
  match k with
  | .elem i  =>
      match args[i]? with
      | some sub => genHeadProof containers sc fam sig s vecS [] sub x
      | none => `(rfl)
  | .recurse => `($tailProof $x)
  | .inert   => `(rfl)

/-- The container-helper lemma: maps the main recursive lemma over a container — `List`, `Option`,
or any registered user inductive — structurally. The arms are derived from the
`ContainerShape`, discharging each constructor with the generated `congrC_<ctor>` congruence (the
generic analogue of `cons_congr`/`some_congr`). -/
def genHelperLemma (containers : Containers) (sc : Bool) (fam : Family) (sig : Signature) (s : SortId)
    (head : IR.ArgHead) : CommandElabM (TSyntax `command) := do
  let vecS := vecOf sig s
  let pbs ← sigImplicitBinders sig
  let params ← recLemmaParams sc sig fam vecS
  let xsId := mkIdent `xs
  let ho : Bool → Name := fun isRen => helperOpName containers isRen s head
  let (lhsL, rhsL) ← fam.mkConclList sig vecS ho xsId
  let ty ← headToTerm sc sig [] head
  let nm := helperLemmaName containers fam s head
  let renH := mkIdent (helperOpName containers true s head)
  let substH := mkIdent (helperOpName containers false s head)
  let recArgs := recLemmaArgs fam vecS
  match head with
  | .functor f args =>
    match shapeOf containers f with
    | none => `(command| theorem $(mkIdent nm) $pbs* $params* : ∀ ($xsId : $ty), $lhsL = $rhsL := fun _ => rfl)
    | some shape =>
      let tailProof ← appAll (mkIdent nm) recArgs   -- the helper lemma applied to its map/hyp args
      let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      for (cName, kinds) in shape do
        let xs := (Array.range kinds.size).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
        -- A leaf container ctor (nullary or all-inert, e.g. `List.nil`/`Option.none`) is left
        -- unchanged by the helper, so it reduces to `rfl`; a trailing `exact congrC` would over-solve.
        let arm ← if kinds.all (· == ArgKind.inert) then
            `(Lean.Parser.Term.matchAltExpr| | $(mkIdent cName) $xs* => rfl)
          else do
            let proofs ← (xs.zip kinds).mapM fun (x, k) =>
              genHelperProofArg containers sc fam sig s vecS args tailProof k x
            let term ← appAll (mkIdent (ctorCongrName cName)) proofs.toList
            `(Lean.Parser.Term.matchAltExpr|
              | $(mkIdent cName) $xs* => by simp only [$renH:ident, $substH:ident]; exact $term)
        arms := arms.push arm
      `(command| theorem $(mkIdent nm) $pbs* $params* : ∀ ($xsId : $ty), $lhsL = $rhsL $arms:matchAlt*)
  | _ => `(command| theorem $(mkIdent nm) $pbs* $params* : ∀ ($xsId : $ty), $lhsL = $rhsL := fun _ => rfl)

/-- The **unwrapped** theorem bodies of a recursive lemma for sort `si`: the main lemma, plus the
container `*_list`/`*_option` helper lemmas when `si` nests a functor (Phase 9). The caller groups
a whole component's bodies into a single `mutual … end` whenever there is more than one — which
happens both for container sorts (main + helpers) and for genuine multi-sort SCCs (one main per
mutually-recursive sort, e.g. `fcbv`'s `tm`/`vl`). -/
def genRecBodies (containers : Containers) (sc : Bool) (fam : Family) (sig : Signature)
    (si : SortInfo) : CommandElabM (Array (TSyntax `command)) := do
  if !sortHasFunctor sig si then
    return #[← genRecLemma sc fam sig si]
  let s := si.name
  let vec := si.substVec
  let pbs ← sigImplicitBinders sig
  let params ← recLemmaParams sc sig fam vec
  let tId := mkIdent `t
  let (lhs, rhs) ← fam.mkConcl sig s tId
  let tTy ← sortTyAt sc sig s "m"
  let renE := mkIdent (renName s); let substE := mkIdent (substName s)
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  if si.isOpen then
    let x := mkIdent `x
    let vp ← fam.varProof s x
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(varCtorI s) $x => by simp only [$renE:ident, $substE:ident]; exact $vp))
  for c in si.ctors do
    let xs := (Array.range c.positions.length).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let ps := (c.params.map (fun (pn, _) => mkIdent pn)).toArray   -- variadic params bound in the pattern
    let pat ← `($(mkIdent (s ++ c.name)) $ps* $xs*)
    -- A leaf constructor (nullary, or all-`ext`) reduces under `simp only [subst]` to `rfl`
    -- (and has no `congr_<c>` when nullary); a non-trivial `exact` would over-solve.
    let arm ← if ctorIsLeaf sig c then
        `(Lean.Parser.Term.matchAltExpr| | $pat => rfl)
      else do
        let proofs ← (c.positions.toArray.zip xs).mapM fun (pos, x) =>
          genHeadProof containers sc fam sig s vec pos.binders pos.head x
        let term ← appAll (mkIdent (congrName s c.name)) proofs.toList
        `(Lean.Parser.Term.matchAltExpr|
          | $pat => by simp only [$renE:ident, $substE:ident]; exact $term)
    alts := alts.push arm
  let mainLemma ← `(command| theorem $(mkIdent (fam.lemmaName s)) $pbs* $params* : ∀ ($tId : $tTy), $lhs = $rhs
      $alts:matchAlt*)
  let helpers ← (helperHeadsOf containers sig [s]).toArray.mapM
    (fun (s', h) => genHelperLemma containers sc fam sig s' h)
  return #[mainLemma] ++ helpers

/-! ## Simple `up_*` helpers (`congrArg`-shaped) -/

/-- Emit a simple up-helper. `b==v` splits on the freshly bound variable — `| 0 | n+1` (unscoped)
or `Fin.cases` (scoped, definitionally reducing); `b≠v` is uniform `fun n => …`. `mkHyp`/`mkConcl`
build the statement; `renApp` is the `congrArg` head. -/
def genSimpleUp (sc : Bool) (sig : Signature) (nm : Name) (b v : SortId)
    (mapBinders : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)))
    (hty concl renApp : CommandElabM Term) : CommandElabM (TSyntax `command) := do
  let nmI := mkIdent nm
  let pbs ← sigImplicitBinders sig
  let bs ← mapBinders
  let h ← `(Lean.Parser.Term.bracketedBinderF| (h : $(← hty)))
  let cc ← concl
  let ra ← renApp
  if b == v then
    if sc then
      `(command| theorem $nmI $pbs* $bs* $h : $cc := Fin.cases rfl (fun n => $congrArgI $ra (h n)))
    else
      `(command| theorem $nmI $pbs* $bs* $h : $cc
          | 0 => rfl
          | n + 1 => $congrArgI $ra (h n))
  else
    `(command| theorem $nmI $pbs* $bs* $h : $cc := fun n => $congrArgI $ra (h n))

/-- `upId_b_v`. (The map binders use **quotation-literal** names so they share hygiene with the
`sigma`/`xi`/… referenced in the `hty`/`concl` quotations below — only the *type* is interpolated.) -/
def genUpId (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) :=
  genSimpleUp sc sig (upIdName b v) b v
    (do pure #[← `(Lean.Parser.Term.bracketedBinderF| (sigma : $(← mapTy sc sig false v "m" "m")))])
    (`(∀ x, sigma x = $(varCtorI v) x))
    (`(∀ x, $(mkIdent (upName b v)) sigma x = $(varCtorI v) x))
    (renShiftApp sc sig b v)

/-- `upExtRen_b_v` (renamings — `b==v` uses `shift`, `b≠v` is the identity `:= h`). -/
def genUpExtRen (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let nmI := mkIdent (upExtRenName b v)
  let renTy ← mapTy sc sig true v "m" "n"
  let bxi ← `(Lean.Parser.Term.bracketedBinderF| (xi : $renTy))
  let bzeta ← `(Lean.Parser.Term.bracketedBinderF| (zeta : $renTy))
  let hty ← `(∀ x, xi x = zeta x)
  let concl ← `(∀ x, $(mkIdent (upRenName b v)) xi x = $(mkIdent (upRenName b v)) zeta x)
  if b == v then
    if sc then
      `(command| theorem $nmI $bxi $bzeta (h : $hty) : $concl :=
          Fin.cases rfl (fun n => $congrArgI $(shiftI sc) (h n)))
    else
      `(command| theorem $nmI $bxi $bzeta (h : $hty) : $concl
          | 0 => rfl
          | n + 1 => $congrArgI $(shiftI sc) (h n))
  else
    `(command| theorem $nmI $bxi $bzeta (h : $hty) : $concl := h)

/-- `upExt_b_v` (substitutions). -/
def genUpExt (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let subTy ← mapTy sc sig false v "m" "n"
  genSimpleUp sc sig (upExtName b v) b v
    (do pure #[← `(Lean.Parser.Term.bracketedBinderF| (sigma : $subTy)),
               ← `(Lean.Parser.Term.bracketedBinderF| (tau : $subTy))])
    (`(∀ x, sigma x = tau x))
    (`(∀ x, $(mkIdent (upName b v)) sigma x = $(mkIdent (upName b v)) tau x))
    (renShiftApp sc sig b v)

/-- `up_ren_subst_b_v`. -/
def genUpRenSubst (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) :=
  genSimpleUp sc sig (upRenSubstName b v) b v
    (do pure #[ ← `(Lean.Parser.Term.bracketedBinderF| (xi : $(← mapTy sc sig true v "k" "l"))),
                ← `(Lean.Parser.Term.bracketedBinderF| (tau : $(← mapTy sc sig false v "l" "m"))),
                ← `(Lean.Parser.Term.bracketedBinderF| (theta : $(← mapTy sc sig false v "k" "m")))])
    (`(∀ x, $funcompI tau xi x = theta x))
    (`(∀ x, $funcompI ($(mkIdent (upName b v)) tau) ($(mkIdent (upRenName b v)) xi) x
        = $(mkIdent (upName b v)) theta x))
    (renShiftApp sc sig b v)

/-- `rinstInst_up_b_v`. -/
def genRinstInstUp (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) :=
  genSimpleUp sc sig (rinstInstUpName b v) b v
    (do pure #[ ← `(Lean.Parser.Term.bracketedBinderF| (xi : $(← mapTy sc sig true v "m" "n"))),
                ← `(Lean.Parser.Term.bracketedBinderF| (sigma : $(← mapTy sc sig false v "m" "n")))])
    (`(∀ x, $funcompI $(varCtorI v) xi x = sigma x))
    (`(∀ x, $funcompI $(varCtorI v) ($(mkIdent (upRenName b v)) xi) x
        = $(mkIdent (upName b v)) sigma x))
    (renShiftApp sc sig b v)

/-! ## Variadic (`bind ⟨p, b⟩`) up-helper lemmas (scoped-only, single open sort ⇒ `b == v`).

The runtime-`p` analogues of the simple up-helpers above. Their proofs are the `scons_p`-calculus
versions transcribed from the reference (`variadic.v`): the freshly bound `p` variables (`zero_p`)
and the shifted originals (`shift_p p`) are handled by `scons_p_head'`/`scons_p_tail'`/`scons_p_eta`/
`scons_p_congr`/`scons_p_comp`. Map binders use `mkIdent` consistently (binders *and* references),
matching the hard up-helpers (`genUpSubstRen`). -/

def upIdListName        (b v : SortId) : Name := Name.mkSimple s!"upId_list_{b}_{v}"
def upExtRenListName    (b v : SortId) : Name := Name.mkSimple s!"upExtRen_list_{b}_{v}"
def upExtListName       (b v : SortId) : Name := Name.mkSimple s!"upExt_list_{b}_{v}"
def upRenSubstListName  (b v : SortId) : Name := Name.mkSimple s!"up_ren_subst_list_{b}_{v}"
def upSubstRenListName  (b v : SortId) : Name := Name.mkSimple s!"up_subst_ren_list_{b}_{v}"
def upSubstSubstListName(b v : SortId) : Name := Name.mkSimple s!"up_subst_subst_list_{b}_{v}"
def rinstInstUpListName (b v : SortId) : Name := Name.mkSimple s!"rinstInst_up_list_{b}_{v}"

def pI : Ident := mkIdent `p
def sconsPEtaI   : Ident := mkIdent ``Autosubst.Scoped.scons_p_eta
def sconsPCongrI : Ident := mkIdent ``Autosubst.Scoped.scons_p_congr
def sconsPCompI  : Ident := mkIdent ``Autosubst.Scoped.scons_p_comp
def sconsPHeadI  : Ident := mkIdent ``Autosubst.Scoped.scons_p_head'
def sconsPTailI  : Ident := mkIdent ``Autosubst.Scoped.scons_p_tail'

/-- The `{p : Nat}` binder shared by every variadic up-helper lemma. `p` is **implicit** so these
lemmas have the same explicit arity as their single-binder counterparts — the recursive tower calls
them uniformly (`upId_list_b_v _ h`), with `p` inferred from the lifted map (`up_list_b_v p σ`). -/
def pBinder : CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
  `(Lean.Parser.Term.bracketedBinderF| { $pI : Nat })

/-- `ren_v` with `shift_p p` on the `b`-component and `id` elsewhere (variadic `renShiftApp`). -/
def renShiftPApp (sig : Signature) (b v : SortId) : CommandElabM Term := do
  let args ← (vecOf sig v).mapM fun w =>
    if w == b then (`($shiftPI $pI) : CommandElabM Term) else pure idI
  appAll (mkIdent (renName v)) args

/-- `upId_list_b_v` — `scons_p_eta` discharges the two branches (fresh ↦ `rfl`, shifted ↦ `ren`). -/
def genUpIdList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let sg := mkIdent `sigma; let hh := mkIdent `h; let varV := varCtorI v
  let pbs ← sigImplicitBinders sig
  let sgB ← mapBinder true sig false v "m" "m" `sigma
  let renSh ← renShiftPApp sig b v
  `(command| theorem $(mkIdent (upIdListName b v)) $pbs* $(← pBinder) $sgB ($hh : ∀ x, $sg x = $varV x) :
      ∀ x, $(mkIdent (upListName b v)) $pI $sg x = $varV x :=
    fun z => $sconsPEtaI $pI $varV (fun x => $congrArgI $renSh ($hh x)) (fun _ => rfl) z)

/-- `upExtRen_list_b_v` — `scons_p_congr` (`zero_p` branch `rfl`, `shift_p` branch via `shift_p`). -/
def genUpExtRenList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let xi := mkIdent `xi; let zeta := mkIdent `zeta; let hh := mkIdent `h
  let xiB ← mapBinder true sig true v "m" "n" `xi; let zetaB ← mapBinder true sig true v "m" "n" `zeta
  `(command| theorem $(mkIdent (upExtRenListName b v)) $(← pBinder) $xiB $zetaB
      ($hh : ∀ x, $xi x = $zeta x) :
      ∀ x, $(mkIdent (upRenListName b v)) $pI $xi x = $(mkIdent (upRenListName b v)) $pI $zeta x :=
    fun z => $sconsPCongrI $pI (fun _ => rfl) (fun x => $congrArgI ($shiftPI $pI) ($hh x)) z)

/-- `upExt_list_b_v` — `scons_p_congr` (shifted branch via `ren_v (shift_p p)`). -/
def genUpExtList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let sg := mkIdent `sigma; let tau := mkIdent `tau; let hh := mkIdent `h
  let pbs ← sigImplicitBinders sig
  let sgB ← mapBinder true sig false v "m" "n" `sigma; let tauB ← mapBinder true sig false v "m" "n" `tau
  let renSh ← renShiftPApp sig b v
  `(command| theorem $(mkIdent (upExtListName b v)) $pbs* $(← pBinder) $sgB $tauB
      ($hh : ∀ x, $sg x = $tau x) :
      ∀ x, $(mkIdent (upListName b v)) $pI $sg x = $(mkIdent (upListName b v)) $pI $tau x :=
    fun z => $sconsPCongrI $pI (fun _ => rfl) (fun x => $congrArgI $renSh ($hh x)) z)

/-- `up_ren_subst_list_b_v` — `scons_p_comp` then `scons_p_congr` (head'/tail' on the branches).
The proof is assembled from shallow sub-quotations (`hf`/`hg`/`body`) to keep parenthesization
manageable, mirroring `genUpSubstRen`. -/
def genUpRenSubstList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let xi := mkIdent `xi; let tau := mkIdent `tau; let theta := mkIdent `theta; let hh := mkIdent `h
  let pbs ← sigImplicitBinders sig
  let xiB ← mapBinder true sig true v "k" "l" `xi
  let tauB ← mapBinder true sig false v "l" "m" `tau
  let thB ← mapBinder true sig false v "k" "m" `theta
  let renSh ← renShiftPApp sig b v
  let hf ← `(fun z => $sconsPHeadI $pI _ _ z)
  let hg ← `(fun z => ($sconsPTailI $pI _ _ ($xi z)).trans ($congrArgI $renSh ($hh z)))
  let proof ← `(fun n => ($sconsPCompI $pI _ _ _ n).trans ($sconsPCongrI $pI $hf $hg n))
  `(command| theorem $(mkIdent (upRenSubstListName b v)) $pbs* $(← pBinder) $xiB $tauB $thB
      ($hh : ∀ x, $funcompI $tau $xi x = $theta x) :
      ∀ x, $funcompI ($(mkIdent (upListName b v)) $pI $tau) ($(mkIdent (upRenListName b v)) $pI $xi) x
         = $(mkIdent (upListName b v)) $pI $theta x := $proof)

/-- `up_subst_ren_list_b_v` — the `eq_trans` chain (`compRenRen_v` ×2 + `scons_p` laws). -/
def genUpSubstRenList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let sg := mkIdent `sigma; let zeta := mkIdent `zeta; let theta := mkIdent `theta; let hh := mkIdent `h
  let pbs ← sigImplicitBinders sig
  let sgB ← mapBinder true sig false v "k" "l" `sigma
  let zetaB ← mapBinder true sig true v "l" "m" `zeta
  let thB ← mapBinder true sig false v "k" "m" `theta
  let renSh ← renShiftPApp sig b v
  let crr := mkIdent (compRenRenName v)
  let upRenL := mkIdent (upRenListName b v); let varV := varCtorI v
  let shp ← `($shiftPI $pI)
  let combo ← `($funcompI $shp $zeta)
  let hf ← `(fun x => $congrArgI $varV ($sconsPHeadI $pI _ _ x))
  let c1 ← `($crr $shp ($upRenL $pI $zeta) $combo (fun x => $sconsPTailI $pI _ _ x) ($sg n))
  let c2 ← `($crr $zeta $shp $combo (fun _ => rfl) ($sg n))
  let hgBody ← `(($c1).trans ((($c2).symm).trans ($congrArgI $renSh ($hh n))))
  let hg ← `(fun n => $hgBody)
  let proof ← `(fun n => ($sconsPCompI $pI _ _ _ n).trans ($sconsPCongrI $pI $hf $hg n))
  `(command| theorem $(mkIdent (upSubstRenListName b v)) $pbs* $(← pBinder) $sgB $zetaB $thB
      ($hh : ∀ x, $funcompI ($(mkIdent (renName v)) $zeta) $sg x = $theta x) :
      ∀ x, $funcompI ($(mkIdent (renName v)) ($upRenL $pI $zeta)) ($(mkIdent (upListName b v)) $pI $sg) x
         = $(mkIdent (upListName b v)) $pI $theta x := $proof)

/-- `up_subst_subst_list_b_v` — the `eq_trans` chain (`compRenSubst_v` + `compSubstRen_v` + `scons_p`). -/
def genUpSubstSubstList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let sg := mkIdent `sigma; let tau := mkIdent `tau; let theta := mkIdent `theta; let hh := mkIdent `h
  let pbs ← sigImplicitBinders sig
  let sgB ← mapBinder true sig false v "k" "l" `sigma
  let tauB ← mapBinder true sig false v "l" "m" `tau
  let thB ← mapBinder true sig false v "k" "m" `theta
  let renSh ← renShiftPApp sig b v
  let crs := mkIdent (compRenSubstName v); let csr := mkIdent (compSubstRenName v)
  let upL := mkIdent (upListName b v); let varV := varCtorI v
  let zeroPI := mkIdent ``Autosubst.Scoped.zero_p
  let shp ← `($shiftPI $pI)
  let upTau ← `($upL $pI $tau)
  let hf ← `(fun x => $sconsPHeadI $pI _ (fun z => $(mkIdent (renName v)) $shp ($tau z)) x)
  let c1 ← `($crs $shp $upTau ($funcompI $upTau $shp) (fun _ => rfl) ($sg n))
  let c2 ← `($csr $tau $shp _ (fun x => ($sconsPTailI $pI _ _ x).symm) ($sg n))
  let hgBody ← `(($c1).trans ((($c2).symm).trans ($congrArgI $renSh ($hh n))))
  let hg ← `(fun n => $hgBody)
  let proof ← `(fun n => ($sconsPCompI $pI ($funcompI $varV ($zeroPI $pI)) _ _ n).trans
      ($sconsPCongrI $pI $hf $hg n))
  `(command| theorem $(mkIdent (upSubstSubstListName b v)) $pbs* $(← pBinder) $sgB $tauB $thB
      ($hh : ∀ x, $funcompI ($(mkIdent (substName v)) $tau) $sg x = $theta x) :
      ∀ x, $funcompI ($(mkIdent (substName v)) ($upL $pI $tau)) ($upL $pI $sg) x
         = $upL $pI $theta x := $proof)

/-- `rinstInst_up_list_b_v` — `scons_p_comp` + `scons_p_congr` (postcompose with `var_v`). -/
def genRinstInstUpList (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let xi := mkIdent `xi; let sg := mkIdent `sigma; let hh := mkIdent `h; let varV := varCtorI v
  let pbs ← sigImplicitBinders sig
  let xiB ← mapBinder true sig true v "m" "n" `xi; let sgB ← mapBinder true sig false v "m" "n" `sigma
  let renSh ← renShiftPApp sig b v
  let hg ← `(fun x => $congrArgI $renSh ($hh x))
  let proof ← `(fun n => ($sconsPCompI $pI _ _ $varV n).trans
      ($sconsPCongrI $pI (fun _ => rfl) $hg n))
  `(command| theorem $(mkIdent (rinstInstUpListName b v)) $pbs* $(← pBinder) $xiB $sgB
      ($hh : ∀ x, $funcompI $varV $xi x = $sg x) :
      ∀ x, $funcompI $varV ($(mkIdent (upRenListName b v)) $pI $xi) x
         = $(mkIdent (upListName b v)) $pI $sg x := $proof)

/-! ## The families -/

def funcompApp (g f : Term) : CommandElabM Term := `($funcompI $g $f)

def famIdSubst : Family where
  lemmaName := idSubstName
  mapSets := [⟨"sigma", false, "m", "m"⟩]
  mkHyp := fun _ v => `(∀ x, $(mapIdent "sigma" v) x = $(varCtorI v) x)
  mkConcl := fun sig s t => do
    return (← opApp (substName s) ((vecOf sig s).map (mapIdent "sigma")) t, t)
  mkConclList := fun _ vec ho xs => do
    return (← opApp (ho false) (vec.map (mapIdent "sigma")) xs, xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do hh ← `($(mkIdent (upLemmaNameB "upId" b u)) _ $hh)
    pure hh

def famExtRen : Family where
  lemmaName := extRenName
  mapSets := [⟨"xi", true, "m", "n"⟩, ⟨"zeta", true, "m", "n"⟩]
  mkHyp := fun _ v => `(∀ x, $(mapIdent "xi" v) x = $(mapIdent "zeta" v) x)
  mkConcl := fun sig s t => do
    return (← opApp (renName s) ((vecOf sig s).map (mapIdent "xi")) t,
            ← opApp (renName s) ((vecOf sig s).map (mapIdent "zeta")) t)
  mkConclList := fun _ vec ho xs => do
    return (← opApp (ho true) (vec.map (mapIdent "xi")) xs,
            ← opApp (ho true) (vec.map (mapIdent "zeta")) xs)
  varProof := fun s x => `($congrArgI $(varCtorI s) ($(hypIdent s) $x))
  liftedHyp := fun _ _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do hh ← `($(mkIdent (upLemmaNameB "upExtRen" b u)) _ _ $hh)
    pure hh

def famExt : Family where
  lemmaName := extName
  mapSets := [⟨"sigma", false, "m", "n"⟩, ⟨"tau", false, "m", "n"⟩]
  mkHyp := fun _ v => `(∀ x, $(mapIdent "sigma" v) x = $(mapIdent "tau" v) x)
  mkConcl := fun sig s t => do
    return (← opApp (substName s) ((vecOf sig s).map (mapIdent "sigma")) t,
            ← opApp (substName s) ((vecOf sig s).map (mapIdent "tau")) t)
  mkConclList := fun _ vec ho xs => do
    return (← opApp (ho false) (vec.map (mapIdent "sigma")) xs,
            ← opApp (ho false) (vec.map (mapIdent "tau")) xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do hh ← `($(mkIdent (upLemmaNameB "upExt" b u)) _ _ $hh)
    pure hh

def famCompRenRen : Family where
  lemmaName := compRenRenName
  mapSets := [⟨"xi", true, "m", "k"⟩, ⟨"zeta", true, "k", "l"⟩, ⟨"rho", true, "m", "l"⟩]
  mkHyp := fun _ v => do `(∀ x, $(← funcompApp (mapIdent "zeta" v) (mapIdent "xi" v)) x = $(mapIdent "rho" v) x)
  mkConcl := fun sig s t => do
    let inner ← opApp (renName s) ((vecOf sig s).map (mapIdent "xi")) t
    return (← opApp (renName s) ((vecOf sig s).map (mapIdent "zeta")) inner,
            ← opApp (renName s) ((vecOf sig s).map (mapIdent "rho")) t)
  mkConclList := fun _ vec ho xs => do
    let inner ← opApp (ho true) (vec.map (mapIdent "xi")) xs
    return (← opApp (ho true) (vec.map (mapIdent "zeta")) inner,
            ← opApp (ho true) (vec.map (mapIdent "rho")) xs)
  varProof := fun s x => `($congrArgI $(varCtorI s) ($(hypIdent s) $x))
  liftedHyp := fun sc _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do
      if b.boundSort == u then
        hh ← match b with
          | .single _   => `($(upRenRenI sc) _ _ _ $hh)
          | .vector p _ => `($(mkIdent ``Autosubst.Scoped.up_ren_ren_p) $(mkIdent p) $hh)
    pure hh

def famCompRenSubst : Family where
  lemmaName := compRenSubstName
  mapSets := [⟨"xi", true, "m", "k"⟩, ⟨"tau", false, "k", "l"⟩, ⟨"theta", false, "m", "l"⟩]
  mkHyp := fun _ v => do `(∀ x, $(← funcompApp (mapIdent "tau" v) (mapIdent "xi" v)) x = $(mapIdent "theta" v) x)
  mkConcl := fun sig s t => do
    let inner ← opApp (renName s) ((vecOf sig s).map (mapIdent "xi")) t
    return (← opApp (substName s) ((vecOf sig s).map (mapIdent "tau")) inner,
            ← opApp (substName s) ((vecOf sig s).map (mapIdent "theta")) t)
  mkConclList := fun _ vec ho xs => do
    let inner ← opApp (ho true) (vec.map (mapIdent "xi")) xs
    return (← opApp (ho false) (vec.map (mapIdent "tau")) inner,
            ← opApp (ho false) (vec.map (mapIdent "theta")) xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do hh ← `($(mkIdent (upLemmaNameB "up_ren_subst" b u)) _ _ _ $hh)
    pure hh

def famRinstInst : Family where
  lemmaName := rinstInstName
  mapSets := [⟨"xi", true, "m", "n"⟩, ⟨"sigma", false, "m", "n"⟩]
  mkHyp := fun _ v => do `(∀ x, $(← funcompApp (varCtorI v) (mapIdent "xi" v)) x = $(mapIdent "sigma" v) x)
  mkConcl := fun sig s t => do
    return (← opApp (renName s) ((vecOf sig s).map (mapIdent "xi")) t,
            ← opApp (substName s) ((vecOf sig s).map (mapIdent "sigma")) t)
  mkConclList := fun _ vec ho xs => do
    return (← opApp (ho true) (vec.map (mapIdent "xi")) xs,
            ← opApp (ho false) (vec.map (mapIdent "sigma")) xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ _ bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do hh ← `($(mkIdent (upLemmaNameB "rinstInst_up" b u)) _ _ $hh)
    pure hh

/-! ## Hard families: `compSubstRen` / `compSubstSubst` (eq_trans-chain up-helpers)
(`compSubstRenName`/`compSubstSubstName` are declared with the other comp names above.) -/

def upSubstRenName     (b v : SortId) : Name := Name.mkSimple s!"up_subst_ren_{b}_{v}"
def upSubstSubstName   (b v : SortId) : Name := Name.mkSimple s!"up_subst_subst_{b}_{v}"

/-- `a.trans (b.symm.trans c)`. -/
def hardChain (a b c : Term) : CommandElabM Term := `(($a).trans ((($b).symm).trans $c))

/-- `n` underscore placeholders. -/
def unders (n : Nat) : CommandElabM (List Term) := (List.range n).mapM fun _ => `(_)

/-- `[shift if w==b else id | w ∈ vec v]`. -/
def shiftArgsOf (sc : Bool) (sig : Signature) (b v : SortId) : List Term :=
  (vecOf sig v).map fun w => if w == b then (shiftI sc : Term) else idI

/-- The body of the hard up-helpers (`up_subst_ren` / `up_subst_subst`), with the `0`/`n+1`
(unscoped) or `Fin.cases` (scoped) wrapper for the `b==v` case. -/
def emitHardUp (sc : Bool) (nm : Name) (b v : SortId)
    (params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (concl body : Term) :
    CommandElabM (TSyntax `command) := do
  let nn := mkIdent `n
  if b == v then
    if sc then
      `(command| theorem $(mkIdent nm) $params* : $concl := Fin.cases rfl (fun $nn => $body))
    else
      `(command| theorem $(mkIdent nm) $params* : $concl
          | 0 => rfl
          | $nn + 1 => $body)
  else
    `(command| theorem $(mkIdent nm) $params* : $concl := fun $nn => $body)

/-- `up_subst_ren_b_v` — `ren ∘ subst` commutes the lift (proven via two `compRenRen_v`). -/
def genUpSubstRen (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let vec := vecOf sig v
  let sg := mkIdent `sigma; let th := mkIdent `theta; let hh := mkIdent `h; let nn := mkIdent `n
  let shiftArgs := shiftArgsOf sc sig b v
  let zetas : List Term := vec.map fun w => idTm (mapIdent "zeta" w)
  let upRenLifted ← vec.mapM fun w => (`($(mkIdent (upRenName b w)) $(mapIdent "zeta" w)) : CommandElabM Term)
  let combos ← vec.mapM fun w =>
    (`($funcompI $(if w == b then shiftI sc else idI) $(mapIdent "zeta" w)) : CommandElabM Term)
  let rfls ← vec.mapM fun _ => (`(fun _ => rfl) : CommandElabM Term)
  let renShift ← renShiftApp sc sig b v
  let mut params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
    #[← mapBinder sc sig false v "k" "l" `sigma]
  for w in vec do
    params := params.push (← mapBinder sc sig true w "l" "m" (Name.mkSimple s!"zeta_{w}"))
  params := params.push (← mapBinder sc sig false v "k" "m" `theta)
  let renVzetas ← appAll (mkIdent (renName v)) zetas
  params := params.push (← `(Lean.Parser.Term.bracketedBinderF|
    ($hh : ∀ x, $funcompI $renVzetas $sg x = $th x)))
  params := (← sigImplicitBinders sig) ++ params
  let renVupRen ← appAll (mkIdent (renName v)) upRenLifted
  let concl ← `(∀ x, $funcompI $renVupRen ($(mkIdent (upName b v)) $sg) x
      = $(mkIdent (upName b v)) $th x)
  let sigmaN ← `($sg $nn); let hN ← `($hh $nn)
  let first ← appAll (mkIdent (compRenRenName v)) (shiftArgs ++ upRenLifted ++ combos ++ rfls ++ [sigmaN])
  let second ← appAll (mkIdent (compRenRenName v)) (zetas ++ shiftArgs ++ combos ++ rfls ++ [sigmaN])
  let body ← hardChain first second (← `($congrArgI $renShift $hN))
  emitHardUp sc (upSubstRenName b v) b v params concl body

/-- `up_subst_subst_b_v` — `subst ∘ subst` commutes the lift (via `compRenSubst_v` + `compSubstRen_v`). -/
def genUpSubstSubst (sc : Bool) (sig : Signature) (b v : SortId) : CommandElabM (TSyntax `command) := do
  let vec := vecOf sig v
  let sg := mkIdent `sigma; let th := mkIdent `theta; let hh := mkIdent `h; let nn := mkIdent `n
  let shiftArgs := shiftArgsOf sc sig b v
  let taus : List Term := vec.map fun w => idTm (mapIdent "tau" w)
  let upLifted ← vec.mapM fun w => (`($(mkIdent (upName b w)) $(mapIdent "tau" w)) : CommandElabM Term)
  let combosA ← vec.mapM fun w =>
    (`($funcompI ($(mkIdent (upName b w)) $(mapIdent "tau" w)) $(if w == b then shiftI sc else idI))
      : CommandElabM Term)
  let combosB ← vec.mapM fun w => do
    let rs ← renShiftApp sc sig b w
    `($funcompI $rs $(mapIdent "tau" w))
  let rfls ← vec.mapM fun _ => (`(fun _ => rfl) : CommandElabM Term)
  let renShift ← renShiftApp sc sig b v
  let mut params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) :=
    #[← mapBinder sc sig false v "k" "l" `sigma]
  for w in vec do
    params := params.push (← mapBinder sc sig false w "l" "m" (Name.mkSimple s!"tau_{w}"))
  params := params.push (← mapBinder sc sig false v "k" "m" `theta)
  let substVtaus ← appAll (mkIdent (substName v)) taus
  params := params.push (← `(Lean.Parser.Term.bracketedBinderF|
    ($hh : ∀ x, $funcompI $substVtaus $sg x = $th x)))
  params := (← sigImplicitBinders sig) ++ params
  let substVup ← appAll (mkIdent (substName v)) upLifted
  let concl ← `(∀ x, $funcompI $substVup ($(mkIdent (upName b v)) $sg) x
      = $(mkIdent (upName b v)) $th x)
  let sigmaN ← `($sg $nn); let hN ← `($hh $nn)
  let first ← appAll (mkIdent (compRenSubstName v)) (shiftArgs ++ upLifted ++ combosA ++ rfls ++ [sigmaN])
  let second ← appAll (mkIdent (compSubstRenName v)) (taus ++ shiftArgs ++ combosB ++ rfls ++ [sigmaN])
  let body ← hardChain first second (← `($congrArgI $renShift $hN))
  emitHardUp sc (upSubstSubstName b v) b v params concl body

def famCompSubstRen : Family where
  lemmaName := compSubstRenName
  mapSets := [⟨"sigma", false, "m", "k"⟩, ⟨"zeta", true, "k", "l"⟩, ⟨"theta", false, "m", "l"⟩]
  mkHyp := fun sig v => do
    let rv ← opOfVec renName sig "zeta" v
    `(∀ x, $funcompI $rv $(mapIdent "sigma" v) x = $(mapIdent "theta" v) x)
  mkConcl := fun sig s t => do
    let inner ← opApp (substName s) ((vecOf sig s).map (mapIdent "sigma")) t
    return (← opApp (renName s) ((vecOf sig s).map (mapIdent "zeta")) inner,
            ← opApp (substName s) ((vecOf sig s).map (mapIdent "theta")) t)
  mkConclList := fun _ vec ho xs => do
    let inner ← opApp (ho false) (vec.map (mapIdent "sigma")) xs
    return (← opApp (ho true) (vec.map (mapIdent "zeta")) inner,
            ← opApp (ho false) (vec.map (mapIdent "theta")) xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ sig bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do
      hh ← appAll (mkIdent (upLemmaNameB "up_subst_ren" b u)) ((← unders ((vecOf sig u).length + 2)) ++ [hh])
    pure hh

def famCompSubstSubst : Family where
  lemmaName := compSubstSubstName
  mapSets := [⟨"sigma", false, "m", "k"⟩, ⟨"tau", false, "k", "l"⟩, ⟨"theta", false, "m", "l"⟩]
  mkHyp := fun sig v => do
    let sv ← opOfVec substName sig "tau" v
    `(∀ x, $funcompI $sv $(mapIdent "sigma" v) x = $(mapIdent "theta" v) x)
  mkConcl := fun sig s t => do
    let inner ← opApp (substName s) ((vecOf sig s).map (mapIdent "sigma")) t
    return (← opApp (substName s) ((vecOf sig s).map (mapIdent "tau")) inner,
            ← opApp (substName s) ((vecOf sig s).map (mapIdent "theta")) t)
  mkConclList := fun _ vec ho xs => do
    let inner ← opApp (ho false) (vec.map (mapIdent "sigma")) xs
    return (← opApp (ho false) (vec.map (mapIdent "tau")) inner,
            ← opApp (ho false) (vec.map (mapIdent "theta")) xs)
  varProof := fun s x => `($(hypIdent s) $x)
  liftedHyp := fun _ sig bs u => do
    let mut hh : Term := hypIdent u
    for b in bs do
      hh ← appAll (mkIdent (upLemmaNameB "up_subst_subst" b u)) ((← unders ((vecOf sig u).length + 2)) ++ [hh])
    pure hh

/-! ## Clean (funext-based) wrappers — the `asimpl`-facing API -/

def renRenName      (s : SortId) : Name := Name.mkSimple s!"renRen_{s}"
def renSubstName    (s : SortId) : Name := Name.mkSimple s!"renSubst_{s}"
def substRenName    (s : SortId) : Name := Name.mkSimple s!"substRen_{s}"
def substSubstName  (s : SortId) : Name := Name.mkSimple s!"substSubst_{s}"
def renRenName'     (s : SortId) : Name := Name.mkSimple s!"renRen'_{s}"
def renSubstName'   (s : SortId) : Name := Name.mkSimple s!"renSubst'_{s}"
def substRenName'   (s : SortId) : Name := Name.mkSimple s!"substRen'_{s}"
def substSubstName' (s : SortId) : Name := Name.mkSimple s!"substSubst'_{s}"
def rinstInstPName (s : SortId) : Name := Name.mkSimple s!"rinstInst'_{s}"
def rinstInstWName (s : SortId) : Name := Name.mkSimple s!"rinstInst_{s}"
def instIdPName    (s : SortId) : Name := Name.mkSimple s!"instId'_{s}"
def instIdName     (s : SortId) : Name := Name.mkSimple s!"instId_{s}"
def rinstIdPName   (s : SortId) : Name := Name.mkSimple s!"rinstId'_{s}"
def rinstIdName    (s : SortId) : Name := Name.mkSimple s!"rinstId_{s}"
def varLName       (s : SortId) : Name := Name.mkSimple s!"varL_{s}"
def varLRenName    (s : SortId) : Name := Name.mkSimple s!"varLRen_{s}"
def varLPName      (s : SortId) : Name := Name.mkSimple s!"varL'_{s}"
def varLRenPName   (s : SortId) : Name := Name.mkSimple s!"varLRen'_{s}"
def funextI : Ident := mkIdent ``funext

/-- Parameter binders for one map-set over `vec`, stage `domSt → codSt`. -/
def mapBindersFor (sc : Bool) (sig : Signature) (pfx : String) (isRen : Bool) (domSt codSt : String)
    (vec : List SortId) : CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  vec.toArray.mapM fun v => mapBinder sc sig isRen v domSt codSt (Name.mkSimple s!"{pfx}_{v}")

/-- A fusion wrapper, applied + funext forms. -/
def genCompWrapper (sc : Bool) (sig : Signature) (si : SortInfo) (nm nmF : Name) (compNm : SortId → Name)
    (pfx1 : String) (isRen1 : Bool) (pfx2 : String) (isRen2 : Bool)
    (mkTheta : SortId → CommandElabM Term) : CommandElabM (Array (TSyntax `command)) := do
  let s := si.name; let vec := si.substVec; let tI := mkIdent `t
  let pbs ← sigImplicitBinders sig
  let innerOp := if isRen1 then renName else substName
  let outerOp := if isRen2 then renName else substName
  let resultOp := if isRen1 && isRen2 then renName else substName
  let b1 ← mapBindersFor sc sig pfx1 isRen1 "m" "k" vec
  let b2 ← mapBindersFor sc sig pfx2 isRen2 "k" "l" vec
  let tTy ← sortTyAt sc sig s "m"
  let thetas ← vec.mapM mkTheta
  let mapArgs := (vec.map fun v => idTm (mapIdent pfx1 v)) ++ (vec.map fun v => idTm (mapIdent pfx2 v))
  -- applied form
  let inner ← opApp (innerOp s) (vec.map (mapIdent pfx1)) tI
  let lhs ← appAll (mkIdent (outerOp s)) ((vec.map fun v => idTm (mapIdent pfx2 v)) ++ [inner])
  let rhs ← appAll (mkIdent (resultOp s)) (thetas ++ [idTm tI])
  let proof ← appAll (mkIdent (compNm s))
    (mapArgs ++ (← unders vec.length) ++ (← vec.mapM fun _ => `(fun _ => rfl)) ++ [idTm tI])
  let applied ← `(command| theorem $(mkIdent nm) $pbs* $b1* $b2* ($tI : $tTy) : $lhs = $rhs := $proof)
  -- funext (map-level) form
  let op1App ← appAll (mkIdent (innerOp s)) (vec.map fun v => idTm (mapIdent pfx1 v))
  let op2App ← appAll (mkIdent (outerOp s)) (vec.map fun v => idTm (mapIdent pfx2 v))
  let tyM ← sortTyAt sc sig s "m"
  let tyK ← sortTyAt sc sig s "k"
  let tyL ← sortTyAt sc sig s "l"
  let op1App ← `(($op1App : $tyM → $tyK))
  let op2App ← `(($op2App : $tyK → $tyL))
  let lhsF ← `($funcompI $op2App $op1App)
  let rhsF0 ← appAll (mkIdent (resultOp s)) thetas
  let rhsF ← `(($rhsF0 : $tyM → $tyL))
  let funextForm ← `(command| theorem $(mkIdent nmF) $pbs* $b1* $b2* :
      $lhsF = $rhsF := $funextI $(← appAll (mkIdent nm) mapArgs))
  return #[applied, funextForm]

/-- All clean wrappers for one substitution sort. -/
def genWrappers (sc : Bool) (sig : Signature) (si : SortInfo) : CommandElabM (Array (TSyntax `command)) := do
  let s := si.name; let vec := si.substVec; let tI := mkIdent `t
  let pbs ← sigImplicitBinders sig
  let mut out : Array (TSyntax `command) := #[]
  let fc (g f : Term) : CommandElabM Term := `($funcompI $g $f)
  let tTy ← sortTyAt sc sig s "m"
  let tTyN ← sortTyAt sc sig s "n"
  let idxTyAt (st : String) (v : SortId) : CommandElabM Term :=
    if sc then `(Fin $(scopeVar st v)) else `(Nat)
  let varAt (st : String) (v : SortId) : CommandElabM Term := do
    let idx ← idxTyAt st v
    let ty ← sortTyAt sc sig v st
    `(($(varCtorI v) : $idx → $ty))
  -- fusion laws (each produces the applied form + the funext/map-level form)
  out := out ++ (← genCompWrapper sc sig si (renRenName s) (renRenName' s) compRenRenName "xi" true "zeta" true
    (fun v => fc (mapIdent "zeta" v) (mapIdent "xi" v)))
  out := out ++ (← genCompWrapper sc sig si (renSubstName s) (renSubstName' s) compRenSubstName "xi" true "tau" false
    (fun v => fc (mapIdent "tau" v) (mapIdent "xi" v)))
  out := out ++ (← genCompWrapper sc sig si (substRenName s) (substRenName' s) compSubstRenName "sigma" false "zeta" true
    (fun v => do fc (← opOfVec renName sig "zeta" v) (mapIdent "sigma" v)))
  out := out ++ (← genCompWrapper sc sig si (substSubstName s) (substSubstName' s) compSubstSubstName "sigma" false "tau" false
    (fun v => do fc (← opOfVec substName sig "tau" v) (mapIdent "sigma" v)))
  -- rinstInst' / rinstInst
  let bxi ← mapBindersFor sc sig "xi" true "m" "n" vec
  let renApp ← opApp (renName s) (vec.map (mapIdent "xi")) tI
  let varXiMaps ← vec.mapM fun v => do fc (← varAt "n" v) (mapIdent "xi" v)
  let substVarXi ← appAll (mkIdent (substName s))
    (varXiMaps ++ [idTm tI])
  let rinstProof ← appAll (mkIdent (rinstInstName s))
    ((vec.map fun v => idTm (mapIdent "xi" v)) ++ (← unders vec.length)
      ++ (← vec.mapM fun _ => `(fun _ => rfl)) ++ [idTm tI])
  out := out.push (← `(command| theorem $(mkIdent (rinstInstPName s)) $pbs* $bxi* ($tI : $tTy) :
      $renApp = $substVarXi := $rinstProof))
  let rinstApplied ← appAll (mkIdent (rinstInstPName s)) (vec.map fun v => idTm (mapIdent "xi" v))
  let renPart0 ← appAll (mkIdent (renName s)) (vec.map fun v => idTm (mapIdent "xi" v))
  let substPart0 ← appAll (mkIdent (substName s)) varXiMaps
  let renPart ← `(($renPart0 : $tTy → $tTyN))
  let substPart ← `(($substPart0 : $tTy → $tTyN))
  out := out.push (← `(command| theorem $(mkIdent (rinstInstWName s)) $pbs* $bxi* :
      $renPart = $substPart := $funextI $rinstApplied))
  -- instId' / instId
  let idSubstVar ← appAll (mkIdent (idSubstName s))
    ((← vec.mapM (varAt "m")) ++ (← vec.mapM fun _ => `(fun _ => rfl)) ++ [idTm tI])
  -- The `= id` forms (`instId`/`rinstId`) leave the scope ambiguous; we pin it with a **type
  -- ascription** `(subst_s var… : s<m> → s<m>)` rather than explicit `@`-scope-args, since
  -- `autoImplicit` orders the scope implicits by first appearance (not in substitution-vector
  -- order), so positional `@`-args would mis-assign them.
  let asc (e : Term) : CommandElabM Term := `(($e : $tTy → $tTy))
  let substVarM ← asc (← appAll (mkIdent (substName s)) (← vec.mapM (varAt "m")))
  out := out.push (← `(command| theorem $(mkIdent (instIdPName s)) $pbs* ($tI : $tTy) :
      $(← appAll (mkIdent (substName s)) (← vec.mapM (varAt "m"))) $tI = $tI := $idSubstVar))
  let instIdApplied ← appAll (mkIdent (instIdPName s)) []
  out := out.push (← `(command| theorem $(mkIdent (instIdName s)) $pbs* :
      $substVarM = id := $funextI $instIdApplied))
  -- rinstId' / rinstId
  let renId ← appAll (mkIdent (renName s)) ((vec.map fun _ => (idI : Term)) ++ [idTm tI])
  let rinstInstId ← appAll (mkIdent (rinstInstPName s)) ((vec.map fun _ => (idI : Term)) ++ [idTm tI])
  let instIdT ← appAll (mkIdent (instIdPName s)) [idTm tI]
  out := out.push (← `(command| theorem $(mkIdent (rinstIdPName s)) $pbs* ($tI : $tTy) :
      $renId = $tI := ($rinstInstId).trans $instIdT))
  let renIdFn ← asc (← appAll (mkIdent (renName s)) (vec.map fun _ => (idI : Term)))
  let rinstIdApplied ← `(fun $tI => $(← appAll (mkIdent (rinstIdPName s)) [idTm tI]))
  out := out.push (← `(command| theorem $(mkIdent (rinstIdName s)) $pbs* :
      $renIdFn = id := $funextI $rinstIdApplied))
  -- varL / varLRen (open sorts only)
  if si.isOpen then
    let bsig ← mapBindersFor sc sig "sigma" false "m" "n" vec
    let xTyM ← idxTyAt "m" s
    let substFn0 ← appAll (mkIdent (substName s)) (vec.map fun v => idTm (mapIdent "sigma" v))
    let substFn ← `(($substFn0 : $tTy → $tTyN))
    let varM ← varAt "m" s
    let varN ← varAt "n" s
    let lhsL ← `($funcompI $substFn $varM)
    out := out.push (← `(command| theorem $(mkIdent (varLName s)) $pbs* $bsig* :
        $lhsL = $(mapIdent "sigma" s) := rfl))
    let bxi2 ← mapBindersFor sc sig "xi" true "m" "n" vec
    let renFn0 ← appAll (mkIdent (renName s)) (vec.map fun v => idTm (mapIdent "xi" v))
    let renFn ← `(($renFn0 : $tTy → $tTyN))
    let lhsLR ← `($funcompI $renFn $varM)
    let rhsLR ← `($funcompI $varN $(mapIdent "xi" s))
    out := out.push (← `(command| theorem $(mkIdent (varLRenName s)) $pbs* $bxi2* :
        $lhsLR = $rhsLR := rfl))
    -- the *applied* var laws — these fire inside `subst`/`ren` expressions during `asimp`
    let xN := mkIdent `x
    let xTy := xTyM
    let substApp := substFn
    out := out.push (← `(command| theorem $(mkIdent (varLPName s)) $pbs* $bsig* ($xN : $xTy) :
        $substApp ($(varCtorI s) $xN) = $(mapIdent "sigma" s) $xN := rfl))
    let renApp3 := renFn
    out := out.push (← `(command| theorem $(mkIdent (varLRenPName s)) $pbs* $bxi2* ($xN : $xTy) :
        $renApp3 ($(varCtorI s) $xN) = $(varCtorI s) ($(mapIdent "xi" s) $xN) := rfl))
  return out

/-! ## Orchestration (incremental) -/

def genLemmaCommands (containers : Containers) (sc : Bool) (sig : Signature) :
    CommandElabM (Array (TSyntax `command)) := do
  let opens := openSorts sig
  -- The recursive lemmas of a family, grouped by component. A component's bodies (one main lemma
  -- per substitution sort, plus any container helpers) are wrapped in a single `mutual … end`
  -- whenever there is more than one — so genuine SCCs (`tm`/`vl`) recurse mutually.
  let recLemmas (fam : Family) : CommandElabM (Array (TSyntax `command)) := do
    let mut acc : Array (TSyntax `command) := #[]
    for comp in sig.components do
      let mut bodies : Array (TSyntax `command) := #[]
      for si in substSortsOf sig comp do
        bodies := bodies ++ (← genRecBodies containers sc fam sig si)
      if h : bodies.size = 1 then acc := acc.push bodies[0]
      else if bodies.size > 1 then acc := acc.push (← `(command| mutual $bodies* end))
    return acc
  -- an up-helper over all (binder, component) pairs
  let ups (g : Bool → Signature → SortId → SortId → CommandElabM (TSyntax `command)) :
      CommandElabM (Array (TSyntax `command)) := do
    let mut acc : Array (TSyntax `command) := #[]
    for b in opens do for v in opens do acc := acc.push (← g sc sig b v)
    return acc
  -- the variadic (`_list`) up-helper *lemmas* over (variadic-bound sort, component) pairs (scoped
  -- only; emitted in the same slot as their single-binder counterparts so dependencies line up).
  let vbs := variadicBoundSorts sig
  let vups (g : Signature → SortId → SortId → CommandElabM (TSyntax `command)) :
      CommandElabM (Array (TSyntax `command)) := do
    let mut acc : Array (TSyntax `command) := #[]
    if sc then for b in vbs do for v in opens do acc := acc.push (← g sig b v)
    return acc
  let mut cmds : Array (TSyntax `command) := #[]
  -- constructor congruences for every recognised container used (`List.cons`, `Option.some`, `Tree.node`,
  -- …) — emitted once per ctor, the generic analogue of `cons_congr`/`some_congr` used by the
  -- container-helper lemmas. (`helperHeadsOf` already excludes the binary `Prod`, which is inline.)
  let mut seenCtors : List Name := []
  for comp in sig.components do
    for (_, h) in helperHeadsOf containers sig comp do
      if let .functor f args := h then
      if !args.isEmpty then
        if let some shape := shapeOf containers f then
          for (cName, kinds) in shape do
            -- leaf ctors (nullary/all-inert) use a `rfl` arm, not `congrC`, so skip their congruence
            -- (which for a nullary ctor would also have an un-inferable element type).
            unless seenCtors.contains cName || kinds.all (· == ArgKind.inert) do
              seenCtors := cName :: seenCtors
              cmds := cmds.push (← genCtorCongr cName kinds.size)
  cmds := cmds ++ (← ups genUpId) ++ (← vups genUpIdList) ++ (← recLemmas famIdSubst)
  cmds := cmds ++ (← ups genUpExtRen) ++ (← vups genUpExtRenList) ++ (← recLemmas famExtRen)
  cmds := cmds ++ (← ups genUpExt) ++ (← vups genUpExtList) ++ (← recLemmas famExt)
  cmds := cmds ++ (← recLemmas famCompRenRen)          -- uses prelude `up_ren_ren`/`up_ren_ren_p`
  cmds := cmds ++ (← ups genUpRenSubst) ++ (← vups genUpRenSubstList) ++ (← recLemmas famCompRenSubst)
  cmds := cmds ++ (← ups genUpSubstRen) ++ (← vups genUpSubstRenList) ++ (← recLemmas famCompSubstRen)
  cmds := cmds ++ (← ups genUpSubstSubst) ++ (← vups genUpSubstSubstList) ++ (← recLemmas famCompSubstSubst)
  cmds := cmds ++ (← ups genRinstInstUp) ++ (← vups genRinstInstUpList) ++ (← recLemmas famRinstInst)
  -- clean wrappers (per substitution sort)
  for comp in sig.components do
    for si in substSortsOf sig comp do
      cmds := cmds ++ (← genWrappers sc sig si)
  return cmds

end Autosubst.Gen
