/-
Copyright (c) 2024 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/
import Batteries.Tactic.Lint.Basic
import Batteries.Tactic.OpenPrivate
import Batteries.Util.LibraryNote
open Lean Meta

namespace Std.Tactic.Lint


open DiscrTree in
open private mkInstanceKey from Lean.Meta.Instances in
/--
Checks whether instances have weak keys, which are most `.star`'s and `.other`'s.
-/
@[env_linter] def instanceKeys : Linter where
  noErrorsFound := "No instances have weak keys."
  errorsFound := "Some instances have weak keys."
  test := fun declName => withReducible do
    unless ← isInstance declName do return none
    let info ← getConstInfo declName
    let keys ← mkInstanceKey info.type
    return some m!"{info.type} has weak keys: {keys}"
    -- if (keys.filter (fun key => !key == .star && !key == .other) |>.size) ≤ 2 then
    --   return some m!"has weak keys: {keys}"
    -- else
    --   return none
