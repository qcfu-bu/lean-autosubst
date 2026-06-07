-- This module serves as the root of the `Autosubst` library.
-- Importing this brings the `autosubst` command, the `asimp` / `substify` / `renamify` /
-- `auto_unfold` tactics, and the notation classes into scope. The Autosubst-consistent notations
-- (`s[σ]`, `s⟨ξ⟩`, `t..`, `[a, b, c/]`, `⇑`, `↑`, …) are opt-in: `open Autosubst.Notation`
-- (unscoped) or `open Autosubst.Scoped.Notation` (well-scoped).
import Autosubst.Prelude.Core
import Autosubst.Prelude.Unscoped
import Autosubst.Prelude.Notation
import Autosubst.IR.Language
import Autosubst.IR.Signature
import Autosubst.Frontend.Syntax
import Autosubst.Frontend.Elab
import Autosubst.Tactic.Asimp
