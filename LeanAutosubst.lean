-- This module serves as the root of the `LeanAutosubst` library.
-- Importing this brings the `autosubst` command, the `asimp` / `substify` / `renamify` /
-- `auto_unfold` tactics, and the notation classes into scope. The Autosubst-consistent notations
-- (`s[σ]`, `s⟨ξ⟩`, `t..`, `[a, b, c/]`, `⇑`, `↑`, …) are opt-in: `open Autosubst.Notation`
-- (unscoped) or `open Autosubst.Scoped.Notation` (well-scoped).
import LeanAutosubst.Prelude.Core
import LeanAutosubst.Prelude.Unscoped
import LeanAutosubst.Prelude.Notation
import LeanAutosubst.IR.Language
import LeanAutosubst.IR.Signature
import LeanAutosubst.Frontend.Syntax
import LeanAutosubst.Frontend.Elab
import LeanAutosubst.Tactic.Asimp
