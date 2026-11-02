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
# Rewriting

In this file, you will learn how to use the {tactic}`rw` (rewrite) tactic to change the target of a
proof goal.
-/

#import_bumps

set_option linter.unusedTactic false

/-!
The `variable` command introduces variables that may be used in subsequent definitions,
examples and theorems. 
-/

variable (x y : ℤ)

/-!
## Rewriting the target

In this example, we prove that if $`x = 5y` and $`y = 2`, then $`3x - 4y = 22`.

The *target* at the start of the proof is to demonstrate that $`3x - 4y = 22`. We begin with the
named *hypotheses* `h1 : x = 5 * y` and `h2 : y =  2`.

At every stage in the proof, the *goal* consists of the target and the set of hypotheses.
-/

example (h1 : x = 5 * y) (h2 : y = 2) : 3 * x - 4 * y = 22 := by
  rw [h1]
  rw [h2]
  norm_num
  done

/-!
The first line of the tactic block is `rw [h1]`. It rewrites the target by replacing every
occurrence of the left-hand side of `h1` with the right-hand side of `h1`.

In this case, `h1 : x = 5 * y`. So `rw [h1]` replaces each occurrence of `x` in the target with `5 *
y`

That is `rw [h1]` has the effect of changing the target to `3 * (5 * y) - 4 * y = 22`.

Then `rw [h2]` changes the target to `3 * (5 * 2) - 4 * 2 = 22`

The tactic {tactic}`norm_num` is used to prove arithmetic goals. 
-/

/-!

## Exercise 1.1

What happens if you change the order of `rw [h1]` and `rw [h2]`? What is the target after `rw [h2]`?
What about after `rw [h1]`? Test your conjecture by editing the code above (in Visual Studio Code)
and reading the messages in the InfoView window.
-/

/-!

## Exercise 1.2

In the examples below, replace the {tactic}`sorry` with {tactic}`rw` tactics and a final `norm_num`.
Before you start, think about how each {tactic}`rw` line will change the target.
-/

variable (z : ℤ)

example (h1 : x = 3 * z) (h2 : y = 9) (h3 : z = 8 - y) : 8 * x + 4 *y + 2 * z = 10 := by
  sorry
  done

example (h1 : x = 3) (h2 : y = 4 * x ^ 2) : y = 36 := by
  sorry
  done
