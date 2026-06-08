import Lean

/-- The simp set backing the `asimp` tactic. Registered in its own module because a
`register_simp_attr` attribute is only usable in modules that *import* this one (not the one
that declares it).

The set is named `asimp_lemmas`, **distinct** from the `asimp` tactic: if they shared a name,
`open`ing the tactic's namespace (or both living at root) would shadow the set name inside
`simp only [asimp]` and silently empty it. The notation-native σ-calculus lemmas
([Gen/Laws.lean]) and the raw⟶method canon lemmas ([Gen/Notation.lean]) each carry their
own inline `@[asimp_lemmas]`; the per-sort `up_b_v`/`upRen_b_v` unfolds are tagged by
[Gen/Automation.lean]; the static σ-calculus laws are tagged in [Tactic/Asimp.lean].

**Orientation gotcha.** An *inline* `@[asimp_lemmas ←]` on a declaration does **not** reverse the
rewrite for this custom (`register_simp_attr`) set — it tags the lemma *forward* regardless. So
every lemma fed into `asimp_lemmas` is stated in the orientation it should rewrite in (e.g. the
`substCanon`/`renCanon` lemmas state `raw = method` and are tagged plainly forward, so they rewrite
raw ⟶ method; `varIds`/`upLift` are likewise stated in their own rewrite direction).
The standalone `attribute [set ←] foo` *command* form does honour `←` correctly — that is how
`renamify_lemmas ←` is applied below ([Gen/Automation.lean]). -/
register_simp_attr asimp_lemmas

/-- The simp set backing `substify` (rewrites renamings into substitutions via `rinstInst'`).
The generator tags each sort's `rinstInst'_<s>` lemma into it. -/
register_simp_attr substify_lemmas

/-- The simp set backing `renamify` — the **reverse** of `substify`: it rewrites substitutions of
the form `subst_s (var ∘ ξ)` back into renamings `ren_s ξ`. The generator tags each sort's
`rinstInst'_<s>` lemma into it **with reversed orientation** (`@[renamify_lemmas ←]`), mirroring the
reference `renamify`'s `setoid_rewrite_left rinstInst'`. -/
register_simp_attr renamify_lemmas

/-- The simp set backing the standalone `auto_unfold` tactic. The generator tags each signature's
lifting helpers (`up_<b>_<v>` / `upRen_<b>_<v>`) into it; the static generic `up_ren` is tagged in
[Tactic/Asimp.lean]. Unfolding these exposes the underlying `scons`/`funcomp`/`ren shift` machinery,
mirroring the reference `auto_unfold`'s `unfold up_* upRen_* up_ren`. -/
register_simp_attr auto_unfold_lemmas
