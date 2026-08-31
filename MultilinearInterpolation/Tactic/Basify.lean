/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import MultilinearInterpolation.Tactic.Basify.Core
public import MultilinearInterpolation.Tactic.Basify.ENNReal

-- Verso doc-comment checking is on for this project; the tactic's docs are plain markdown.
set_option doc.verso false
set_option doc.verso.module false

/-!
# The `basify` tactic

This file bundles the `basify` tactic together with the types Mathlib registers with it. See
`MultilinearInterpolation/Tactic/Basify/Core.lean` for what the tactic does and how to teach it a new type.
-/
