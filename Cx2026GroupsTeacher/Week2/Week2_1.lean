/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

public import Cx2026GroupsTeacher.Week2.Week2_0
meta import Cx2026GroupsTools
meta import Cx2026GroupsAuthoring
import Mathlib.Tactic.Linter.MinImports

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Further group results

Multiplying on the left by a fixed element $`g` is called left translation.
You can undo it by multiplying on the left by $`g^{-1}`. In Week 4, you will
use these two operations to match the elements of a subgroup with the elements
of a coset.
-/

teacher_only in
#import_bumps

namespace cx_2026

variable {G : Type*} [Group G] (g x y : G)

public section

set_option course.checkProofs true

NewTactic have

/-!
## Exercise 1.1

Prove that translation by $`g^{-1}` undoes translation by $`g`. Start by
regrouping the product, then simplify the inverse pair and the identity.
-/

lemma inv_mul_cancel_left : g⁻¹ * (g * x) = x := by
  sorry

teacher_only in
example : g⁻¹ * (g * x) = x := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

NewTheorem cx_2026.inv_mul_cancel_left

/-!
## Exercise 1.2

Now compose the two translations in the opposite order. Use the right inverse
identity you proved in Exercise 0.4.
-/

lemma mul_inv_cancel_left : g * (g⁻¹ * x) = x := by
  sorry

NewTheorem cx_2026.mul_inv_cancel_left

teacher_only in
example : g * (g⁻¹ * x) = x := by
  rw [← mul_assoc, cx_2026.mul_inv_cancel, one_mul]

/-!
## Exercise 1.3

If $`gx=gy`, multiply both sides on the left by $`g^{-1}` and use
{name}`inv_mul_cancel_left`. This proves left cancellation.
-/

example (h : g * x = g * y) : x = y := by
  calc
    x = g⁻¹ * (g * x) := by sorry
    _ = g⁻¹ * (g * y) := by sorry
    _ = y := by sorry

teacher_only in
example (h : g * x = g * y) : x = y := by
  calc
    x = g⁻¹ * (g * x) := by rw [inv_mul_cancel_left]
    _ = g⁻¹ * (g * y) := by rw [h]
    _ = y := by rw [inv_mul_cancel_left]

/-!
## Exercise 1.4

Prove the formula for the inverse of a product. In Exercise 0.1, you showed that
$`(y^{-1}x^{-1})(xy)=1`. Multiply that equation on the right by $`(xy)^{-1}`
and simplify. Notice the order of the factors in the result.
-/

lemma mul_inv_rev : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  calc
    (x * y)⁻¹ = 1 * (x * y)⁻¹ := by sorry
    _ = ((y⁻¹ * x⁻¹) * (x * y)) * (x * y)⁻¹ := by sorry
    _ = y⁻¹ * x⁻¹ := by sorry

NewTheorem cx_2026.mul_inv_rev

teacher_only in
example : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  calc
    (x * y)⁻¹ = 1 * (x * y)⁻¹ := by rw [one_mul]
    _ = ((y⁻¹ * x⁻¹) * (x * y)) * (x * y)⁻¹ := by rw [inv_mul_inv_mul_mul_cancel]
    _ = y⁻¹ * x⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]

/-!
## Exercise 1.5

Let's prove the right cancelling versions of our previous results.
-/

lemma mul_inv_cancel_right : (x * g) * g⁻¹ = x := by 
  calc
    (x * g) * g⁻¹ = sorry := by sorry
    _ = x := by sorry
  done

NewTheorem cx_2026.mul_inv_cancel_right

teacher_only in
example : (x * g) * g⁻¹ = x := by 
  calc
    (x * g) * g⁻¹ = x * (g * g⁻¹) := by rw [mul_assoc]
    _ = x * 1 := by rw [mul_inv_cancel]
    _ = x := by rw [mul_one]
  done

lemma inv_mul_cancel_right : (x * g⁻¹) * g = x := by
  calc
    (x * g⁻¹) * g = sorry := by sorry
    _ = x  := by sorry
  done

NewTheorem cx_2026.inv_mul_cancel_right

teacher_only in
example : (x * g⁻¹) * g = x := by
  calc
    (x * g⁻¹) * g = x * (g⁻¹ * g) := by rw [mul_assoc]
    _ = x * 1 := by rw [inv_mul_cancel]
    _ = x := by rw [mul_one]

end

end cx_2026
