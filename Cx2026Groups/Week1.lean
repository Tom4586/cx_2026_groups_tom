/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

import Mathlib.Tactic.Ring

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Rewriting

In this file, you will learn how to use the {tactic}`rw` (rewrite) tactic to change the target of a
proof goal.
-/

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

## Exercise 1

What happens if you change the order of `rw [h1]` and `rw [h2]`? What is the target after `rw [h2]`?
What about after `rw [h1]`? Test your conjecture by editing the code above (in Visual Studio Code)
and reading the messages in the InfoView window.
-/

/-!

## Exercise 2

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

/-!

## Calculation-style proofs

Another approach is to chain equations together, giving a justification for each equation. Suppose
we have the hypotheses `h1 : x = 5 * y` and `h2 : y = 2` and we wish to prove `3 * x - 4 * y = 22`.
In traditional mathematics, we might write this as:

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
## Exercise 3

Interact with the proof above by examining the goal immediately after each `by` command. How does
the goal relate to the code? Can you see how each tactic following the `by` command proves the goal?
-/

/-!
## Exercise 4

Complete the {tactic}`calc` proof below, replacing each {tactic}`sorry` with a tactic.
-/

example (h1 : x = 4) (h2 : y = 2 * x - 1) : 5 * x - 3 * y = -1 := by
  calc
    5 * x - 3 * y = 5 * x - 3 * (2 * x - 1) := by sorry
    _ = 5 * 4 - 3 * (2 * 4 - 1) := by sorry
    _ = -1 := by sorry

/-!
## Exercise 5

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

#min_imports
