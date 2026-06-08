/-
# Strong normalisation for (Church-style) System F, via the `autosubst` DSL.

Girard's reducibility-candidates proof, in the **Church** presentation: terms carry their type
information (`lam` is annotated, `tapp`/`tlam` are explicit), so `tm` ranges over *both* type- and
term-variables and `subst_tm` threads **two** parallel maps. This exercises the genuinely
multi-sorted side of Autosubst2: type-into-term substitution, the type-β redex
`tapp (tlam s) B`, and the lifting tower `up_tm_tm`/`up_tm_ty`/`up_ty_tm`/`up_ty_ty`. Every
de-Bruijn equation below is discharged by `asimp`.

The key de-Bruijn design point (which makes the impredicative ∀ go through): the candidate
interpretation `interp A ρ` depends **only** on the candidate assignment `ρ`, never on a syntactic
type substitution. The syntactic type substitution `δ` rides along on the *term* in the
fundamental theorem; the `tlam` case is reconciled by the renaming-naturality of `interp`
(`interp_ren`) and the `tapp` case by its substitution lemma (`interp_subst`).

Layers:
1. reduction `step` (term-β + type-β), `sn`, `sn_preimage`;
2. (anti)stability of reduction under substitution/renaming, `sn` closure facts;
3. reducibility candidates, β- and type-β-expansion;
4. the Kripke interpretation `interp`, its naturality, and `interp_reducible`;
5. Church-style typing and the fundamental theorem ⟹ every typed term is `sn`.

This doubles as the `sysf.sig` reference test, superseding the old `Tests/SysF.lean`: the unscoped
backend is exercised throughout the SN development below, and the well-scoped backend is checked at
the end. Both are `#axiom_clean`.
-/
import Tests.Support
open Autosubst Autosubst.Notation

namespace SysfSN

-- F-types and Church-style terms. `tm` carries both `ty`- and `tm`-variables, so `subst_tm`/`ren_tm`
-- are two-map and the substitution tower is genuinely multi-sorted.
autosubst
  ty where
    | arr : ty → ty → ty
    | all : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

/-! ## 1. Reduction, strong normalisation -/

/-- Full one-step reduction: term-β (`s[ty.var_ty; [t/]]` substitutes the argument for term-var 0,
types untouched) and type-β (`s[ [B/]; tm.var_tm]` substitutes `B` for type-var 0, terms untouched),
plus congruences. Types never reduce. -/
inductive step : tm → tm → Prop
  | beta  {A s t} : step (.app (.lam A s) t) (s[ty.var_ty; [t/]])
  | tbeta {s B}   : step (.tapp (.tlam s) B) (s[ [B/]; tm.var_tm])
  | appL  {s s' t} : step s s' → step (.app s t) (.app s' t)
  | appR  {s t t'} : step t t' → step (.app s t) (.app s t')
  | lam   {A s s'} : step s s' → step (.lam A s) (.lam A s')
  | tapp  {s s' B} : step s s' → step (.tapp s B) (.tapp s' B)
  | tlam  {s s'}   : step s s' → step (.tlam s) (.tlam s')

/-- Strong normalisation as accessibility of `step`. -/
inductive sn : tm → Prop
  | intro {s} : (∀ t, step s t → sn t) → sn s

/-- Neutral = not an introduction form (`app`, `tapp`, variables — but not `lam`/`tlam`). -/
def neutral : tm → Prop
  | tm.lam _ _ => False
  | tm.tlam _  => False
  | _ => True

/-- If `f` maps steps to steps, `sn (f s)` forces `sn s`. -/
theorem sn_preimage (f : tm → tm) (hf : ∀ {a b}, step a b → step (f a) (f b))
    {s} (h : sn (f s)) : sn s := by
  have gen : ∀ fs, sn fs → ∀ s, f s = fs → sn s := by
    intro fs hfs
    induction hfs with
    | intro _ ih => intro s e; exact sn.intro fun t hst => ih (f t) (e ▸ hf hst) t rfl
  exact gen (f s) h s rfl

/-! ## 2. Reduction is (anti)stable under substitution and renaming -/

/-- β-reduction is preserved by substitution; the redex cases are the substitution lemmas (`asimp`). -/
theorem step_subst {s t} (σty : Nat → ty) (σtm : Nat → tm) (h : step s t) :
    step (s[σty;σtm]) (t[σty;σtm]) := by
  induction h generalizing σty σtm with
  | @beta A s t =>
      have e : (s[ty.var_ty; [t/]])[σty;σtm]
             = (s[up_tm_ty σty; up_tm_tm σtm])[ty.var_ty; [t[σty;σtm]/]] := by asimp
      rw [e]; exact step.beta
  | @tbeta s B =>
      have e : (s[ [B/]; tm.var_tm])[σty;σtm]
             = (s[up_ty_ty σty; up_ty_tm σtm])[ [B[σty]/]; tm.var_tm] := by asimp
      rw [e]; exact step.tbeta
  | appL _ ih => exact step.appL (ih σty σtm)
  | appR _ ih => exact step.appR (ih σty σtm)
  | lam _ ih  => exact step.lam (ih (up_tm_ty σty) (up_tm_tm σtm))
  | tapp _ ih => exact step.tapp (ih σty σtm)
  | tlam _ ih => exact step.tlam (ih (up_ty_ty σty) (up_ty_tm σtm))

/-- β-reduction is preserved by renaming (renaming is a special case of substitution). -/
theorem step_ren {s t} (ξty ξtm : Nat → Nat) (h : step s t) :
    step (s⟨ξty;ξtm⟩) (t⟨ξty;ξtm⟩) := by
  have e : ∀ r : tm, r⟨ξty;ξtm⟩ = r[funcomp ty.var_ty ξty; funcomp tm.var_tm ξtm] :=
    fun r => rinstInst'_tm ξty ξtm r
  rw [e s, e t]; exact step_subst _ _ h

/-- Anti-renaming: a step out of `s⟨ξty;ξtm⟩` comes from a step out of `s`. -/
theorem step_antiren {s : tm} : ∀ {ξty ξtm : Nat → Nat} {u : tm},
    step (s⟨ξty;ξtm⟩) u → ∃ s', u = s'⟨ξty;ξtm⟩ ∧ step s s' := by
  induction s with
  | var_tm n => intro ξty ξtm u h; simp only [renApp2_tm, ren_tm] at h; cases h
  | app s1 s2 ih1 ih2 =>
      intro ξty ξtm u h
      cases s1 with
      | lam A1 b1 =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | beta => exact ⟨b1[ty.var_ty; [s2/]], by asimp, step.beta⟩
          | appL hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.app s' s2, by subst e'; simp only [renApp2_tm, ren_tm], step.appL st'⟩
          | appR hc => obtain ⟨t', e', st'⟩ := ih2 hc
                       exact ⟨tm.app (tm.lam A1 b1) t', by subst e'; simp only [renApp2_tm, ren_tm], step.appR st'⟩
      | var_tm n =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | appL hc => cases hc
          | appR hc => obtain ⟨t', e', st'⟩ := ih2 hc
                       exact ⟨tm.app (tm.var_tm n) t', by subst e'; simp only [renApp2_tm, ren_tm], step.appR st'⟩
      | app a b =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | appL hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.app s' s2, by subst e'; simp only [renApp2_tm, ren_tm], step.appL st'⟩
          | appR hc => obtain ⟨t', e', st'⟩ := ih2 hc
                       exact ⟨tm.app (tm.app a b) t', by subst e'; simp only [renApp2_tm, ren_tm], step.appR st'⟩
      | tapp a B =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | appL hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.app s' s2, by subst e'; simp only [renApp2_tm, ren_tm], step.appL st'⟩
          | appR hc => obtain ⟨t', e', st'⟩ := ih2 hc
                       exact ⟨tm.app (tm.tapp a B) t', by subst e'; simp only [renApp2_tm, ren_tm], step.appR st'⟩
      | tlam a =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | appL hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.app s' s2, by subst e'; simp only [renApp2_tm, ren_tm], step.appL st'⟩
          | appR hc => obtain ⟨t', e', st'⟩ := ih2 hc
                       exact ⟨tm.app (tm.tlam a) t', by subst e'; simp only [renApp2_tm, ren_tm], step.appR st'⟩
  | tapp s1 B ih1 =>
      intro ξty ξtm u h
      cases s1 with
      | tlam b1 =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | tbeta => exact ⟨b1[ [B/]; tm.var_tm], by asimp, step.tbeta⟩
          | tapp hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.tapp s' B, by subst e'; simp only [renApp2_tm, ren_tm], step.tapp st'⟩
      | var_tm n =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | tapp hc => cases hc
      | app a b =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | tapp hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.tapp s' B, by subst e'; simp only [renApp2_tm, ren_tm], step.tapp st'⟩
      | tapp a C =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | tapp hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.tapp s' B, by subst e'; simp only [renApp2_tm, ren_tm], step.tapp st'⟩
      | lam A a =>
          simp only [renApp2_tm, ren_tm] at h
          cases h with
          | tapp hc => obtain ⟨s', e', st'⟩ := ih1 hc
                       exact ⟨tm.tapp s' B, by subst e'; simp only [renApp2_tm, ren_tm], step.tapp st'⟩
  | lam A s1 ih =>
      intro ξty ξtm u h
      simp only [renApp2_tm, ren_tm] at h
      cases h with
      | lam hc => obtain ⟨s', e', st'⟩ := ih hc
                  exact ⟨tm.lam A s', by subst e'; simp only [renApp2_tm, ren_tm], step.lam st'⟩
  | tlam s1 ih =>
      intro ξty ξtm u h
      simp only [renApp2_tm, ren_tm] at h
      cases h with
      | tlam hc => obtain ⟨s', e', st'⟩ := ih hc
                   exact ⟨tm.tlam s', by subst e'; simp only [renApp2_tm, ren_tm], step.tlam st'⟩

/-! ## 3. Closure facts for `sn` -/

theorem sn_appL {s t} (h : sn (tm.app s t)) : sn s :=
  sn_preimage (fun x => tm.app x t) (fun st => step.appL st) h
theorem sn_appR {s t} (h : sn (tm.app s t)) : sn t :=
  sn_preimage (fun x => tm.app s x) (fun st => step.appR st) h
theorem sn_tapp_inv {s B} (h : sn (tm.tapp s B)) : sn s :=
  sn_preimage (fun x => tm.tapp x B) (fun st => step.tapp st) h
theorem sn_subst_inv {s : tm} (σty : Nat → ty) (σtm : Nat → tm) (h : sn (s[σty;σtm])) : sn s :=
  sn_preimage (fun x => x[σty;σtm]) (fun st => step_subst σty σtm st) h

/-- `sn` is preserved by renaming (uses anti-renaming). -/
theorem sn_ren {s} (ξty ξtm : Nat → Nat) (h : sn s) : sn (s⟨ξty;ξtm⟩) := by
  induction h generalizing ξty ξtm with
  | intro _ ih =>
      refine sn.intro fun u hu => ?_
      obtain ⟨s', e, st⟩ := step_antiren hu
      subst e; exact ih s' st ξty ξtm

theorem neutral_app (s t : tm) : neutral (tm.app s t) := by simp [neutral]
theorem neutral_tapp (s : tm) (B : ty) : neutral (tm.tapp s B) := by simp [neutral]
theorem neutral_var (n : Nat) : neutral (tm.var_tm n) := by simp [neutral]

/-- Renaming preserves neutrality. -/
theorem neutral_ren {s : tm} (hne : neutral s) (ξty ξtm : Nat → Nat) : neutral (s⟨ξty;ξtm⟩) := by
  cases s with
  | lam A b => simp [neutral] at hne
  | tlam b => simp [neutral] at hne
  | var_tm n => simp [renApp2_tm, ren_tm, neutral]
  | app a b => simp [renApp2_tm, ren_tm, neutral]
  | tapp a B => simp [renApp2_tm, ren_tm, neutral]

/-! ## 4. Reducibility candidates -/

/-- A reducibility candidate: `sn` members, forward-closed, neutral-closed (CR3), and closed under
(two-map) renaming. -/
structure reducible (P : tm → Prop) : Prop where
  cr_sn   : ∀ {s}, P s → sn s
  cr_step : ∀ {s t}, P s → step s t → P t
  cr_ne   : ∀ {s}, neutral s → (∀ t, step s t → P t) → P s
  cr_ren  : ∀ {s : tm} (ξty ξtm : Nat → Nat), P s → P (s⟨ξty;ξtm⟩)

theorem reducible_sn : reducible sn := by
  constructor
  · exact fun h => h
  · intro s t h st; cases h with | intro f => exact f t st
  · intro s _ h; exact sn.intro h
  · intro s ξty ξtm h; exact sn_ren ξty ξtm h

theorem reducible_var (P : tm → Prop) (rP : reducible P) (n : Nat) : P (tm.var_tm n) :=
  rP.cr_ne (neutral_var n) (fun t ht => by cases ht)

/-- Inverting a step from an application with a **neutral** function: no β. -/
theorem step_app_neutral {a u w : tm} (hne : neutral a) (hw : step (tm.app a u) w) :
    (∃ a', step a a' ∧ w = tm.app a' u) ∨ (∃ u', step u u' ∧ w = tm.app a u') := by
  cases hw with
  | beta => simp [neutral] at hne
  | appL h => exact Or.inl ⟨_, h, rfl⟩
  | appR h => exact Or.inr ⟨_, h, rfl⟩

/-- Inverting a step from a type application with a **neutral** function: no type-β. -/
theorem step_tapp_neutral {a : tm} {B : ty} {w : tm} (hne : neutral a) (hw : step (tm.tapp a B) w) :
    ∃ a', step a a' ∧ w = tm.tapp a' B := by
  cases hw with
  | tbeta => simp [neutral] at hne
  | tapp h => exact ⟨_, h, rfl⟩

/-- Term β-expansion closure (analogue of CR3 for the application redex). -/
theorem beta_exp {P Q : tm → Prop} (rP : reducible P) (rQ : reducible Q) :
    ∀ {A : ty} {s : tm}, (∀ u, Q u → P (s[ty.var_ty; [u/]])) →
      ∀ {u}, sn u → Q u → P (tm.app (tm.lam A s) u) := by
  intro A s hb
  have hsns : sn s := sn_subst_inv _ _ (rP.cr_sn (hb _ (reducible_var Q rQ 0)))
  induction hsns with
  | @intro s _ ihs =>
      intro u hsnu
      induction hsnu with
      | @intro u husf ihu =>
          intro hu
          apply rP.cr_ne (neutral_app _ _)
          intro w hw
          cases hw with
          | beta => exact hb u hu
          | appL hL =>
              cases hL with
              | lam hs' =>
                  exact ihs _ hs'
                    (fun u' hu' => rP.cr_step (hb u' hu') (step_subst _ _ hs'))
                    (sn.intro husf) hu
          | appR hR => exact ihu _ hR (rQ.cr_step hu hR)

/-- Type β-expansion closure. -/
theorem tbeta_exp {P : tm → Prop} (rP : reducible P) {B : ty} :
    ∀ {s : tm}, P (s[ [B/]; tm.var_tm]) → P (tm.tapp (tm.tlam s) B) := by
  intro s hb
  have hsns : sn s := sn_subst_inv _ _ (rP.cr_sn hb)
  induction hsns with
  | @intro s _ ihs =>
      apply rP.cr_ne (neutral_tapp _ _)
      intro w hw
      cases hw with
      | tbeta => exact hb
      | tapp hc =>
          cases hc with
          | tlam hs' => exact ihs _ hs' (rP.cr_step hb (step_subst _ _ hs'))

theorem reducible_scons {P : tm → Prop} {ρ : Nat → tm → Prop}
    (rP : reducible P) (hρ : ∀ x, reducible (ρ x)) : ∀ x, reducible ((P .: ρ) x)
  | 0 => rP
  | _ + 1 => hρ _

/-! ## 5. The Kripke interpretation of types -/

/-- `interp A ρ` is the candidate denoting `A`. Both the arrow and the ∀ are **Kripke** (quantify
over a renaming `ξty ξtm`), which makes the interpretation closed under renaming; the ∀ is
**impredicative** (quantifies over all candidates `P`). It depends only on `ρ`, not on any syntactic
type substitution. -/
def interp : ty → (Nat → tm → Prop) → tm → Prop
  | ty.var_ty x, ρ => ρ x
  | ty.arr A B, ρ => fun s =>
      ∀ (ξty ξtm : Nat → Nat) (u : tm), interp A ρ u → interp B ρ (tm.app (s⟨ξty;ξtm⟩) u)
  | ty.all A, ρ => fun s =>
      ∀ (ξty ξtm : Nat → Nat) (B : ty) (P : tm → Prop), reducible P →
        interp A (P .: ρ) (tm.tapp (s⟨ξty;ξtm⟩) B)

/-- `interp` depends on the assignment only pointwise. -/
theorem interp_env : ∀ {A : ty} {ρ₁ ρ₂ : Nat → tm → Prop} {s : tm},
    (∀ x, ρ₁ x = ρ₂ x) → (interp A ρ₁ s ↔ interp A ρ₂ s)
  | ty.var_ty x, _, _, _, h => by simp only [interp, h x]
  | ty.arr A B, _, _, s, h => by
      simp only [interp]
      constructor <;> intro hs ξty ξtm u hu
      · exact (interp_env (A := B) h).1 (hs ξty ξtm u ((interp_env (A := A) h).2 hu))
      · exact (interp_env (A := B) h).2 (hs ξty ξtm u ((interp_env (A := A) h).1 hu))
  | ty.all A, _, _, s, h => by
      simp only [interp]
      constructor <;> intro hs ξty ξtm B P rP
      · exact (interp_env (A := A) (by intro x; cases x with | zero => rfl | succ n => exact h n)).1 (hs ξty ξtm B P rP)
      · exact (interp_env (A := A) (by intro x; cases x with | zero => rfl | succ n => exact h n)).2 (hs ξty ξtm B P rP)

/-- Renaming naturality of the interpretation: renaming a *type* reindexes the assignment. -/
theorem interp_ren : ∀ {A : ty} {ξ : Nat → Nat} {ρ : Nat → tm → Prop} {s : tm},
    (interp (ren_ty ξ A) ρ s ↔ interp A (fun x => ρ (ξ x)) s)
  | ty.var_ty x, ξ, ρ, s => by simp only [ren_ty, interp]
  | ty.arr A B, ξ, ρ, s => by
      simp only [ren_ty, interp]
      constructor <;> intro hs ξty ξtm u hu
      · exact (interp_ren (A := B)).1 (hs ξty ξtm u ((interp_ren (A := A)).2 hu))
      · exact (interp_ren (A := B)).2 (hs ξty ξtm u ((interp_ren (A := A)).1 hu))
  | ty.all A, ξ, ρ, s => by
      simp only [ren_ty, interp]
      constructor <;> intro hs ξty ξtm B P rP
      · refine (interp_env (A := A) ?_).1 ((interp_ren (A := A)).1 (hs ξty ξtm B P rP))
        intro x; cases x with | zero => rfl | succ n => simp [upRen_ty_ty, up_ren, funcomp, scons]
      · refine (interp_ren (A := A)).2 ((interp_env (A := A) ?_).1 (hs ξty ξtm B P rP))
        intro x; cases x with | zero => rfl | succ n => simp [upRen_ty_ty, up_ren, funcomp, scons]

/-- Shifting a type by one and interpreting under an extended assignment cancels. -/
theorem interp_shift {C : ty} {P : tm → Prop} {ρ : Nat → tm → Prop} {s : tm} :
    interp (ren_ty shift C) (P .: ρ) s ↔ interp C ρ s :=
  (interp_ren (A := C)).trans (interp_env (A := C) (fun _ => rfl))

/-- The environment produced by lifting a type substitution equals extending the semantic
environment with the new candidate. -/
theorem interp_up_env {σ : Nat → ty} {ρ : Nat → tm → Prop} {P : tm → Prop} :
    ∀ x, interp ((up_ty_ty σ) x) (P .: ρ) = (P .: fun y => interp (σ y) ρ) x
  | 0 => rfl
  | _ + 1 => funext fun _ => propext interp_shift

/-- **Substitution lemma.** Substituting a type and interpreting equals interpreting under the
substituted assignment. -/
theorem interp_subst : ∀ {A : ty} {σ : Nat → ty} {ρ : Nat → tm → Prop} {s : tm},
    interp (subst_ty σ A) ρ s ↔ interp A (fun x => interp (σ x) ρ) s
  | ty.var_ty x, _, _, _ => by simp only [subst_ty, interp]
  | ty.arr A B, _, _, s => by
      simp only [subst_ty, interp]
      constructor <;> intro hs ξty ξtm u hu
      · exact (interp_subst (A := B)).1 (hs ξty ξtm u ((interp_subst (A := A)).2 hu))
      · exact (interp_subst (A := B)).2 (hs ξty ξtm u ((interp_subst (A := A)).1 hu))
  | ty.all A, _, _, s => by
      simp only [subst_ty, interp]
      constructor <;> intro hs ξty ξtm B P rP
      · exact (interp_env (A := A) interp_up_env).1 ((interp_subst (A := A)).1 (hs ξty ξtm B P rP))
      · exact (interp_subst (A := A)).2 ((interp_env (A := A) interp_up_env).2 (hs ξty ξtm B P rP))

/-! ## CR3 for the arrow and ∀ candidates -/

/-- CR3 for the arrow: a neutral `s` whose reducts are all in `interp (arr A B) ρ` yields
`app (s⟨ξ⟩) u ∈ interp B ρ` for `u ∈ interp A ρ`. -/
theorem interp_ne_arr {A B : ty} {ρ : Nat → tm → Prop}
    (rA : reducible (interp A ρ)) (rB : reducible (interp B ρ))
    {s : tm} (hne : neutral s) (hcl : ∀ t, step s t → interp (ty.arr A B) ρ t)
    (ξty ξtm : Nat → Nat) :
    ∀ {u}, interp A ρ u → interp B ρ (tm.app (s⟨ξty;ξtm⟩) u) := by
  have hneξ : neutral (s⟨ξty;ξtm⟩) := neutral_ren hne ξty ξtm
  suffices h : ∀ {u}, sn u → interp A ρ u → interp B ρ (tm.app (s⟨ξty;ξtm⟩) u) by
    intro u hu; exact h (rA.cr_sn hu) hu
  intro u hsnu
  induction hsnu with
  | @intro u _ ihu =>
      intro hu
      apply rB.cr_ne (neutral_app _ _)
      intro w hw
      rcases step_app_neutral hneξ hw with ⟨w', hw', e⟩ | ⟨u', hu', e⟩
      · obtain ⟨s', e', st'⟩ := step_antiren hw'
        subst e; subst e'
        exact hcl s' st' ξty ξtm u hu
      · subst e
        exact ihu _ hu' (rA.cr_step hu hu')

/-- CR3 for the ∀: a neutral `s` whose reducts are all in `interp (all A) ρ` yields
`tapp (s⟨ξ⟩) B ∈ interp A (P .: ρ)`. -/
theorem interp_ne_all {A : ty} {ρ : Nat → tm → Prop}
    (rA : ∀ P, reducible P → reducible (interp A (P .: ρ)))
    {s : tm} (hne : neutral s) (hcl : ∀ t, step s t → interp (ty.all A) ρ t)
    (ξty ξtm : Nat → Nat) (B : ty) (P : tm → Prop) (rP : reducible P) :
    interp A (P .: ρ) (tm.tapp (s⟨ξty;ξtm⟩) B) := by
  have hneξ : neutral (s⟨ξty;ξtm⟩) := neutral_ren hne ξty ξtm
  apply (rA P rP).cr_ne (neutral_tapp _ _)
  intro w hw
  obtain ⟨a', st', e⟩ := step_tapp_neutral hneξ hw
  obtain ⟨s', e', st''⟩ := step_antiren st'
  subst e; subst e'
  exact hcl s' st'' ξty ξtm B P rP

/-- **Every type denotes a candidate.** -/
theorem interp_reducible : ∀ (A : ty) (ρ : Nat → tm → Prop),
    (∀ x, reducible (ρ x)) → reducible (interp A ρ) := by
  intro A
  induction A with
  | var_ty x => intro ρ hρ; simpa only [interp] using hρ x
  | arr A B ihA ihB =>
      intro ρ hρ
      have rA := ihA ρ hρ
      have rB := ihB ρ hρ
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [interp] at hs
        have hv : interp A ρ (tm.var_tm 0) := reducible_var _ rA 0
        have h2 : sn (s⟨id;id⟩) := sn_appL (rB.cr_sn (hs id id (tm.var_tm 0) hv))
        have e : s⟨(id:Nat→Nat);(id:Nat→Nat)⟩ = s := by asimp
        rwa [e] at h2
      · intro s t hs hst
        simp only [interp] at hs ⊢
        intro ξty ξtm u hu
        exact rB.cr_step (hs ξty ξtm u hu) (step.appL (step_ren ξty ξtm hst))
      · intro s hne hcl
        simp only [interp]
        intro ξty ξtm u hu
        exact interp_ne_arr rA rB hne hcl ξty ξtm hu
      · intro s ξty ξtm hs
        simp only [interp] at hs ⊢
        intro ζty ζtm u hu
        have e : (s⟨ξty;ξtm⟩)⟨ζty;ζtm⟩ = s⟨funcomp ζty ξty; funcomp ζtm ξtm⟩ := by asimp
        rw [e]; exact hs (funcomp ζty ξty) (funcomp ζtm ξtm) u hu
  | all A ihA =>
      intro ρ hρ
      have rA : ∀ P, reducible P → reducible (interp A (P .: ρ)) :=
        fun P rP => ihA (P .: ρ) (reducible_scons rP hρ)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro s hs
        simp only [interp] at hs
        have h2 : sn (s⟨id;id⟩) :=
          sn_tapp_inv ((rA sn reducible_sn).cr_sn (hs id id (ty.var_ty 0) sn reducible_sn))
        have e : s⟨(id:Nat→Nat);(id:Nat→Nat)⟩ = s := by asimp
        rwa [e] at h2
      · intro s t hs hst
        simp only [interp] at hs ⊢
        intro ξty ξtm B P rP
        exact (rA P rP).cr_step (hs ξty ξtm B P rP) (step.tapp (step_ren ξty ξtm hst))
      · intro s hne hcl
        simp only [interp]
        intro ξty ξtm B P rP
        exact interp_ne_all rA hne hcl ξty ξtm B P rP
      · intro s ξty ξtm hs
        simp only [interp] at hs ⊢
        intro ζty ζtm B P rP
        have e : (s⟨ξty;ξtm⟩)⟨ζty;ζtm⟩ = s⟨funcomp ζty ξty; funcomp ζtm ξtm⟩ := by asimp
        rw [e]; exact hs (funcomp ζty ξty) (funcomp ζtm ξtm) B P rP

/-- Renaming closure of `interp`, restated as a *substitution-by-variables* (the form `asimp`
produces when pushing a renaming through a substitution). -/
theorem interp_cr_ren {C : ty} {ρ : Nat → tm → Prop} (rC : reducible (interp C ρ))
    (ξty ξtm : Nat → Nat) {s : tm} (h : interp C ρ s) :
    interp C ρ (s[funcomp ty.var_ty ξty; funcomp tm.var_tm ξtm]) := by
  rw [← rinstInst'_tm]; exact rC.cr_ren ξty ξtm h

/-! ## 6. Church-style typing and the fundamental theorem -/

/-- Church-style System-F typing. `Γ : Nat → ty` is the term-variable context; the type-variable
context is de Bruijn (implicit), and `tlam` shifts it (`ren_ty shift`). -/
inductive HasType : (Nat → ty) → tm → ty → Prop
  | var {Γ x} : HasType Γ (tm.var_tm x) (Γ x)
  | app {Γ s t A B} : HasType Γ s (ty.arr A B) → HasType Γ t A → HasType Γ (tm.app s t) B
  | lam {Γ A s B} : HasType (A .: Γ) s B → HasType Γ (tm.lam A s) (ty.arr A B)
  | tapp {Γ s A} (B : ty) :
      HasType Γ s (ty.all A) → HasType Γ (tm.tapp s B) (subst_ty (B .: ty.var_ty) A)
  | tlam {Γ s A} : HasType (funcomp (ren_ty shift) Γ) s A → HasType Γ (tm.tlam s) (ty.all A)

/-- **Fundamental theorem.** A well-typed term, with a type substitution `δ` on its annotations and
a reducible term substitution `σtm`, lands in the interpretation of its type. -/
theorem fundamental {Γ s A} (h : HasType Γ s A) :
    ∀ (δ : Nat → ty) (σtm : Nat → tm) (ρ : Nat → tm → Prop), (∀ x, reducible (ρ x)) →
      (∀ x, interp (Γ x) ρ (σtm x)) → interp A ρ (s[δ;σtm]) := by
  induction h with
  | @var Γ x => intro δ σtm ρ _ hσ; exact hσ x
  | @app Γ s t A B _ _ ihs iht =>
      intro δ σtm ρ hρ hσ
      have h1 := ihs δ σtm ρ hρ hσ
      have h2 := iht δ σtm ρ hρ hσ
      simp only [interp] at h1
      have h3 := h1 id id (t[δ;σtm]) h2
      have e : (s[δ;σtm])⟨(id:Nat→Nat);(id:Nat→Nat)⟩ = s[δ;σtm] := by asimp
      rw [e] at h3
      exact h3
  | @lam Γ A s B _ ihs =>
      intro δ σtm ρ hρ hσ
      simp only [interp]
      intro ξty ξtm u hu
      have hr : (tm.lam (subst_ty δ A) (subst_tm (up_tm_ty δ) (up_tm_tm σtm) s))⟨ξty;ξtm⟩
              = tm.lam ((subst_ty δ A)⟨ξty⟩)
                  ((subst_tm (up_tm_ty δ) (up_tm_tm σtm) s)⟨ξty; up_ren ξtm⟩) := by
        simp only [renApp1_ty, renApp2_tm, ren_tm, upRen_tm_ty, upRen_tm_tm]
      show interp B ρ (tm.app ((tm.lam (subst_ty δ A) _)⟨ξty;ξtm⟩) u)
      rw [hr]
      refine beta_exp (interp_reducible B ρ hρ) (interp_reducible A ρ hρ) ?_
        ((interp_reducible A ρ hρ).cr_sn hu) hu
      intro u' hu'
      have key : ((subst_tm (up_tm_ty δ) (up_tm_tm σtm) s)⟨ξty; up_ren ξtm⟩)[ty.var_ty; [u'/]]
               = subst_tm (funcomp (ren_ty ξty) δ)
                   (scons u' (funcomp (subst_tm (funcomp ty.var_ty ξty) (funcomp tm.var_tm ξtm)) σtm)) s := by
        asimp
      rw [key]
      refine ihs (funcomp (ren_ty ξty) δ)
        (scons u' (funcomp (subst_tm (funcomp ty.var_ty ξty) (funcomp tm.var_tm ξtm)) σtm)) ρ hρ ?_
      intro x
      cases x with
      | zero => exact hu'
      | succ n => exact interp_cr_ren (interp_reducible (Γ n) ρ hρ) ξty ξtm (hσ n)
  | @tapp Γ s A B _ ihs =>
      intro δ σtm ρ hρ hσ
      have h1 := ihs δ σtm ρ hρ hσ
      simp only [interp] at h1
      have h2 := h1 id id (subst_ty δ B) (interp B ρ) (interp_reducible B ρ hρ)
      have e : (s[δ;σtm])⟨(id:Nat→Nat);(id:Nat→Nat)⟩ = s[δ;σtm] := by asimp
      rw [e] at h2
      refine (interp_subst (A := A)).2 ((interp_env (A := A) ?_).2 h2)
      intro x; cases x with | zero => rfl | succ n => rfl
  | @tlam Γ s A _ ihs =>
      intro δ σtm ρ hρ hσ
      simp only [interp]
      intro ξty ξtm B P rP
      have hr : (tm.tlam (subst_tm (up_ty_ty δ) (up_ty_tm σtm) s))⟨ξty;ξtm⟩
              = tm.tlam ((subst_tm (up_ty_ty δ) (up_ty_tm σtm) s)⟨up_ren ξty; ξtm⟩) := by
        simp only [renApp2_tm, ren_tm, upRen_ty_ty, upRen_ty_tm]
      show interp A (P .: ρ) (tm.tapp ((tm.tlam _)⟨ξty;ξtm⟩) B)
      rw [hr]
      refine tbeta_exp (interp_reducible A (P .: ρ) (reducible_scons rP hρ)) ?_
      have key : ((subst_tm (up_ty_ty δ) (up_ty_tm σtm) s)⟨up_ren ξty; ξtm⟩)[ [B/]; tm.var_tm]
               = subst_tm (scons B (funcomp (subst_ty (funcomp ty.var_ty ξty)) δ))
                   (funcomp (subst_tm (funcomp ty.var_ty ξty) (funcomp tm.var_tm ξtm)) σtm) s := by
        asimp
      rw [key]
      refine ihs (scons B (funcomp (subst_ty (funcomp ty.var_ty ξty)) δ))
        (funcomp (subst_tm (funcomp ty.var_ty ξty) (funcomp tm.var_tm ξtm)) σtm)
        (P .: ρ) (reducible_scons rP hρ) ?_
      intro x
      show interp (ren_ty shift (Γ x)) (P .: ρ) _
      exact interp_shift.2 (interp_cr_ren (interp_reducible (Γ x) ρ hρ) ξty ξtm (hσ x))

/-- **Strong normalisation:** every well-typed Church-style System-F term is `sn`. -/
theorem strong_normalization {Γ s A} (h : HasType Γ s A) : sn s := by
  have hρ : ∀ x, reducible ((fun _ : Nat => sn) x) := fun _ => reducible_sn
  have hσ : ∀ x, interp (Γ x) (fun _ : Nat => sn) (tm.var_tm x) := by
    intro x; exact reducible_var _ (interp_reducible (Γ x) (fun _ : Nat => sn) hρ) x
  have hmain := fundamental h ty.var_ty tm.var_tm (fun _ : Nat => sn) hρ hσ
  have e : s[ty.var_ty; tm.var_tm] = s := by asimp
  rw [e] at hmain
  exact (interp_reducible A _ hρ).cr_sn hmain

/-! ## Demonstration -/

/-- The polymorphic identity `Λ. λ(0:#0). #0 : ∀. #0 → #0` is strongly normalising. -/
example : sn (tm.tlam (tm.lam (ty.var_ty 0) (tm.var_tm 0))) :=
  strong_normalization (Γ := fun _ => ty.var_ty 0) (HasType.tlam (HasType.lam HasType.var))

/-! ## Axiom-cleanliness — the generated tower and the SN development. -/

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean interp_reducible
#axiom_clean fundamental
#axiom_clean strong_normalization

end SysfSN

/-! ## Well-scoped backend of `sysf.sig` (carried over from the old reference test).

`SN` itself is developed only for the unscoped backend above; this section keeps the well-scoped
generator coverage of `sysf.sig` (the doubly scope-indexed `tm : Nat → Nat → Type`). -/
namespace SysfSN.Scoped
open Autosubst Autosubst.Scoped

autosubst wellscoped
  ty where
    | arr  : ty → ty → ty
    | all  : (bind ty in ty) → ty
  tm where
    | app  : tm → tm → tm
    | tapp : tm → ty → tm
    | lam  : ty → (bind tm in tm) → tm
    | tlam : (bind ty in tm) → tm

theorem tm_identity {m_ty m_tm} (s : tm m_ty m_tm) :
    subst_tm ty.var_ty tm.var_tm s = s := by asimp
theorem tm_fusion (στy : Fin m_ty → ty n_ty) (στm : Fin m_tm → tm n_ty n_tm)
    (τty : Fin n_ty → ty k_ty) (τtm : Fin n_tm → tm k_ty k_tm) (s : tm m_ty m_tm) :
    subst_tm τty τtm (subst_tm στy στm s)
      = subst_tm (funcomp (subst_ty τty) στy) (funcomp (subst_tm τty τtm) στm) s := by asimp
theorem ty_beta {n_ty n_tm} (s : tm n_ty n_tm) (T : ty n_ty) :
    subst_tm (scons T ty.var_ty) tm.var_tm (ren_tm shift id s) = s := by asimp
theorem tm_beta {n_ty n_tm} (s t : tm n_ty n_tm) :
    subst_tm ty.var_ty (scons t tm.var_tm) (ren_tm id shift s) = s := by asimp

#axiom_clean substSubst_tm
#axiom_clean instId_tm
#axiom_clean tm_fusion
#axiom_clean tm_beta

end SysfSN.Scoped
