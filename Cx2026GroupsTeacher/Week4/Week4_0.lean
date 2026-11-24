/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

public import Mathlib.GroupTheory.Coset.Basic
public import Cx2026GroupsTeacher.Week2.Week2_2
import Mathlib.Tactic.Use
meta import Cx2026GroupsTools
meta import Cx2026GroupsAuthoring

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Left cosets and the partition

Fix a subgroup $`H` of a group $`G`. The left coset $`gH` is the set of elements
$`gh` with $`h\in H`. Lean writes this as `g • (H : Set G)`. The type annotation
tells Lean to treat the subgroup as a set. The word *left* refers to where we
put the translating element $`g`.

In the integers modulo 12, translating the subgroup from Week 3 gives these sets.

* $`0+H=\{0,3,6,9\}`
* $`1+H=\{1,4,7,10\}`
* $`2+H=\{2,5,8,11\}`

Which of these sets is $`8+H`? Each residue belongs to exactly one of the three
sets. We will prove the corresponding statement for every group and subgroup.
-/

open scoped Pointwise

namespace cx_2026

variable {G : Type*} [Group G] (H : Subgroup G)

NewTactic constructor intro exact apply rcases use change rfl "·"
NewTheorem Subgroup.one_mem Subgroup.mul_mem Subgroup.inv_mem one_mem mul_mem inv_mem
NewTheorem Iff.intro Iff.mp Iff.mpr Exists.intro And.intro Exists.casesOn And.casesOn
NewTheorem cx_2026.inv_inv

public section

set_option course.checkProofs true

/-!
## Exercise 0.1

Show that `y ∈ g • (H : Set G)` if and only if `g⁻¹ * y ∈ H`.
{tactic}`constructor` creates a goal for each direction of the equivalence.

* In the forward direction, `change` displays the membership hypothesis as
  `∃ h ∈ H, g * h = y`. Then `rcases hy with ⟨h, hh, heq⟩` extracts the witness
  `h`, its membership proof `hh`, and the equation `heq`.
* In the backward direction, `use` supplies an element of `H` to translate by
  `g`. Choose `g⁻¹ * y` and use the two translation identities from Week 2.
-/

lemma left_coset_membership (g y : G) : y ∈ g • (H : Set G) ↔ g⁻¹ * y ∈ H := by
  constructor
  · intro hy
    change ∃ h ∈ H, g * h = y at hy
    rcases hy with ⟨h, hh, heq⟩
    sorry
  · intro hy
    change ∃ h ∈ H, g * h = y
    sorry

teacher_only in
example (g y : G) : y ∈ g • (H : Set G) ↔ g⁻¹ * y ∈ H := by
  constructor
  · intro hy
    change ∃ h ∈ H, g * h = y at hy
    rcases hy with ⟨h, hh, heq⟩
    rw [← heq, inv_mul_cancel_left]
    exact hh
  · intro hy
    change ∃ h ∈ H, g * h = y
    use g⁻¹ * y, hy
    exact mul_inv_cancel_left g y

/-!
## Exercise 0.2

Show that the relation $`x\sim y` defined by `x⁻¹ * y ∈ H` is an equivalence
relation. Lean's `Equivalence` asks for reflexivity, symmetry, and transitivity
in that order. The first case is worked out below.

For symmetry, take the inverse of `x⁻¹ * y` and use the inverse-of-a-product
formula. For transitivity, multiply `x⁻¹ * y` by `y⁻¹ * z` and simplify with
associativity and the right inverse identity.
-/

example : Equivalence (fun x y : G => x⁻¹ * y ∈ H) := by
  constructor
  · intro x
    rw [inv_mul_cancel]
    exact H.one_mem
  · intro x y hxy
    sorry
  · intro x y z hxy hyz
    sorry

teacher_only in
example : Equivalence (fun x y : G => x⁻¹ * y ∈ H) := by
  constructor
  · intro x
    rw [inv_mul_cancel]
    exact H.one_mem
  · intro x y hxy
    change x⁻¹ * y ∈ H at hxy
    have hinv := H.inv_mem hxy
    rw [mul_inv_rev, cx_2026.inv_inv] at hinv
    exact hinv
  · intro x y z hxy hyz
    change x⁻¹ * y ∈ H at hxy
    change y⁻¹ * z ∈ H at hyz
    have hprod := H.mul_mem hxy hyz
    rw [mul_assoc, mul_inv_cancel_left] at hprod
    exact hprod

/-!
## From the relation to a partition

Exercise 0.1 identifies the equivalence class of $`g` with $`gH`. Reflexivity
puts every element in its own class. If two classes contain the same element
$`z`, symmetry and transitivity show that their representatives are related.
Transitivity then puts every element of either class in the other class.
So distinct left cosets are disjoint, and together they cover $`G`.

In Mathlib, {name}`QuotientGroup.leftRel` packages this equivalence relation.
The type `G ⧸ H` has one element for each class. We will count its elements
in Week 5.
-/

end

end cx_2026
