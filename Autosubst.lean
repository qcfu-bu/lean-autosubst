-- This module serves as the root of the `Autosubst` library.
-- Importing this brings the `autosubst` command, the `asimp` / `substify` / `renamify` /
-- `auto_unfold` tactics, and the notation classes into scope. The Autosubst-consistent notations
-- (`s[σ]`, `s⟨ξ⟩`, `t..`, `[a, b, c/]`, `⇑`, `↑`, …) are opt-in: `open Autosubst.Notation`
-- (unscoped) or `open Autosubst.Scoped.Notation` (well-scoped).
module

public import Autosubst.Prelude.Core
public import Autosubst.Prelude.Unscoped
public import Autosubst.Prelude.Notation
public import Autosubst.IR.Language
public import Autosubst.IR.Signature
public import Autosubst.Frontend.Syntax
public import Autosubst.Frontend.Elab
public import Autosubst.Tactic.Asimp
