/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
import Cx2026GroupsTeacher.Week2.Week2_1
meta import Cx2026GroupsTools
meta import Cx2026GroupsAuthoring

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Subgroups and membership

A subgroup of a group $`G` is a subset that contains the identity and is closed
under multiplication and inverses. It is a group under the operations inherited
from $`G`. In Lean, if `H : Subgroup G`, the statement `x ∈ H` says that the element
`x : G` belongs to `H`.

## A running example

In the additive group of integers modulo 12, let $`H=\{0,3,6,9\}`. The identity is
$`0`, products become sums, and inverses become negatives. The sum of two
multiples of 3 is a multiple of 3, and the negative of a multiple of 3 is also a
multiple of 3. Reducing modulo 12 preserves divisibility by 3, since 12 itself is
a multiple of 3. This gives a subgroup of order 4.

## Using closure in Lean

The proof `H.one_mem` says that `1 ∈ H`. If `hx : x ∈ H`, then `H.inv_mem hx`
proves `x⁻¹ ∈ H`. Given `hx : x ∈ H` and `hy : y ∈ H`, `H.mul_mem hx hy` proves
`x * y ∈ H`.

When the target is an implication, use {tactic}`intro` to name its hypothesis.
When the target says that a product is in `H`, `apply H.mul_mem` changes the
problem into two goals, one for each factor. A `·` starts the proof of one goal.
-/

namespace cx_2026

variable {G : Type*} [Group G] (H : Subgroup G)

NewTactic intro apply exact rw sorry "·"
NewTheorem Subgroup.one_mem Subgroup.inv_mem Subgroup.mul_mem one_mem inv_mem mul_mem mul_one

section

set_option course.checkProofs true

example (x : G) : x ∈ H → x * 1 ∈ H := by
  intro hx
  apply H.mul_mem
  · exact hx
  · exact H.one_mem

/-!
## Exercise 0.1

Show that the inverse of any member of `H` is in `H`. Try `intro` followed by
`exact` with the inverse closure proof.
-/

example (x : G) : x ∈ H → x⁻¹ ∈ H := by
  intro hx
  sorry

teacher_only in
example (x : G) : x ∈ H → x⁻¹ ∈ H := by
  intro hx
  exact H.inv_mem hx

/-!
## Exercise 0.2

Show that if two elements belong to `H`, the inverse of the first multiplied by
the second also belongs to `H`. In Week 4, an expression of this form will tell
us whether two elements belong to the same coset.
-/

example (x y : G) (hx : x ∈ H) (hy : y ∈ H) : x⁻¹ * y ∈ H := by
  apply H.mul_mem
  · sorry
  · sorry

teacher_only in
example (x y : G) (hx : x ∈ H) (hy : y ∈ H) : x⁻¹ * y ∈ H := by
  apply H.mul_mem
  · exact H.inv_mem hx
  · exact hy

/-!
## Exercise 0.3

Suppose `x ∈ H` and `x * y ∈ H`. Recover `y ∈ H` by first showing that
`x⁻¹ * (x * y) ∈ H`, then simplifying.
-/

example (x y : G) (hx : x ∈ H) (hxy : x * y ∈ H) : y ∈ H := by
  have h : x⁻¹ * (x * y) ∈ H := by
    sorry
  sorry

teacher_only in
example (x y : G) (hx : x ∈ H) (hxy : x * y ∈ H) : y ∈ H := by
  have h : x⁻¹ * (x * y) ∈ H := by
    exact H.mul_mem (H.inv_mem hx) hxy
  rw [inv_mul_cancel_left] at h
  exact h

end

end cx_2026
