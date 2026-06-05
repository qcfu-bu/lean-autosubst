import Lean

/-- The simp set backing the `asimp` tactic. Registered in its own module because a
`register_simp_attr` attribute is only usable in modules that *import* this one (not the one
that declares it).

The set is named `asimp_lemmas`, **distinct** from the `asimp` tactic: if they shared a name,
`open`ing the tactic's namespace (or both living at root) would shadow the set name inside
`simp only [asimp]` and silently empty it. The generator ([Gen/Automation.lean]) tags each
signature's clean lemmas into this set; the static σ-calculus laws are tagged in
[Tactic/Asimp.lean]. -/
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
