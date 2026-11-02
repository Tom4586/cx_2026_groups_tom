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
# Calculation-style proofs

Proofs can be laid out as a series of equations, each with a justification or reason. We'll see how
to do this in Lean.
-/

#import_bumps

set_option linter.unusedTactic false

variable (x y z : ℤ)

/-!
Suppose we have the hypotheses `h1 : x = 5 * y` and `h2 : y = 2` and we wish to prove `3 * x - 4 * y
= 22`. In traditional mathematics, we might write this as:

$$`\begin{aligned}
3 x - 4y &= 3(5y) - 4y && \text{by h1}\\
& = 3(5 \cdot 2)  - 4 \cdot 2 && \text{by h2}  \\
&= 22 && \text{by arithmetic} 
\end{aligned}`

Though you might not typically give a justification of each line in a handwritten proof.

Here is the same proof written as a Lean {tactic}`calc` block.
-/

example (h1 : x = 5 * y) (h2 : y = 2) : 3 * x - 4 * y = 22 := by
  calc
    3 * x - 4 * y = 3 * (5 * y) - 4 * y := by rw [h1]
    _ = 3 * (5 * 2) - 4 * 2 := by rw [h2]
    _ = 22 := by norm_num

/-!
## Exercise 2.1 

Interact with the proof above by examining the goal immediately after each `by` command. How does
the goal relate to the code? Can you see how each tactic following the `by` command proves the goal?
-/

/-!
## Exercise 2.2

Complete the {tactic}`calc` proof below, replacing each {tactic}`sorry` with a tactic.
-/

example (h1 : x = 4) (h2 : y = 2 * x - 1) : 5 * x - 3 * y = -1 := by
  calc
    5 * x - 3 * y = 5 * x - 3 * (2 * x - 1) := by sorry
    _ = 5 * 4 - 3 * (2 * 4 - 1) := by sorry
    _ = -1 := by sorry

/-!
## Exercise 2.3

Complete the {tactic}`calc` proof below. This time, you'll need to supply the intermediate lines of
proof and the justification for each line.

Ensure you follow the syntax closely. Each `calc` line except the first begins with an `_`
(underscore) character and an equals sign. The justification for each line follows `:= by`.  

-/

example (h1 : x = 3) (h2 : x + y = 5) (h3 : y = 2 * z) : (x + 2 * z) + 2 * x = 11  := by
  calc
     x + 2 * z + 2 * x = sorry := by sorry
     _ = 11 := by sorry
  done
