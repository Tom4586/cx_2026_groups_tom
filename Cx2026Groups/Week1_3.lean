/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Linter.MinImports

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Introducing hypotheses with have

Another way to prove a theorem is by introducing and using auxiliary results.

Consider again a situation where we have the hypotheses `h1`:$`x = 5y`, `h2`:$`y = 2` and we wish to
prove $`3x - 4y = 22`. We can reason as follows:

We have `h3`:$`4y = 8`, from `h2`. We have `h4`:$`3x = 30` from `h1` and `h2`. Combining `h1` and
`h2` gives $`3x - 4y = 22`.
-/

#import_bumps

set_option linter.unusedTactic false

variable (x y z : ℤ)

/-!
The same proof can be written in Lean as follows. The {tactic}`have` tactic is explained below. 
-/

example (h1 : x = 5 * y) (h2 : y = 2) : 3 * x - 4 * y = 22 := by
  have h3 : 4 * y = 8 := by
    rw [h2]
    norm_num
  have h4 : 3 * x = 30 := by
    rw [h1, h2]
    norm_num
  rw [h3, h4]
  norm_num

/-!
The {tactic}`have` tactic allows you to introduce a new hypothesis into the context. The line
```
have  h3 : 4 * y = 8 := by
```
introduces a proof of `4 * y = 8` into the context and calls that proof `h3`. The proof itself
follows the word `by`. In our case, we used `rw [h2]` to rewrite `4 * y = 8` as `4 * 2 = 8`. Then we
use {tactic}`norm_num` to perform the arithmetic.
-/
