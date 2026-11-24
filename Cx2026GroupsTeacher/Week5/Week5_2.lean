/-
Copyright (c) 2026 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/

module

public import Cx2026GroupsTeacher.Week4.Week4_1
public import Mathlib.SetTheory.Cardinal.Finite

set_option doc.verso.module true
set_option doc.verso.suggestions false

/-!
# Lagrange's theorem: assembling the coset argument

This is a worked alternative to Week 5.0, following its “MY THOUGHTS”.
The mathematical work is organised as follows.

1. Use Week 4's membership criterion to finish the partition argument:
   every element belongs to a coset, and two cosets which meet are equal.
2. Count a partition by adding the sizes of its parts.
3. Apply Week 4's result that every coset has the same size as the subgroup.
4. Deduce Lagrange's theorem by supplying the number of distinct cosets as
   the witness for divisibility.

We index the partition by the actual cosets, regarded as sets. In particular,
we do not sum over all elements of the group: that would count each coset
repeatedly. No normality assumption is needed.

The proofs below are complete; the earlier exercise statements are used as
lemmas. As in the rest of the teacher source, those imported statements still
have exercise holes alongside their teacher solutions.
-/

open scoped Pointwise

namespace cx_2026.Week5_2

public section

variable {G : Type*} [Group G] (H : Subgroup G)

/-!
## 1. Make the partition argument precise

Week 4 proved the equivalence-relation laws in an unnamed example. We give
that argument a name here so that its symmetry and transitivity can be used.
The group identities in this proof are the ones from Week 2.
-/

lemma coset_relation_equivalence : Equivalence (fun x y : G => x⁻¹ * y ∈ H) := by
  constructor
  · intro x
    rw [inv_mul_cancel]
    exact H.one_mem
  · intro x y hxy
    have hinv := H.inv_mem hxy
    rw [cx_2026.mul_inv_rev, cx_2026.inv_inv] at hinv
    exact hinv
  · intro x y z hxy hyz
    have hprod := H.mul_mem hxy hyz
    rw [mul_assoc, cx_2026.mul_inv_cancel_left] at hprod
    exact hprod

lemma mem_own_coset (x : G) : x ∈ x • (H : Set G) := by
  apply (cx_2026.left_coset_membership H x x).mpr
  rw [inv_mul_cancel]
  exact H.one_mem

/-- If two cosets share an element, they are the same set. -/
lemma cosets_eq_of_common_member (g k x : G)
    (hg : x ∈ g • (H : Set G)) (hk : x ∈ k • (H : Set G)) :
    g • (H : Set G) = k • (H : Set G) := by
  have he := coset_relation_equivalence H
  have hgx := (cx_2026.left_coset_membership H g x).mp hg
  have hkx := (cx_2026.left_coset_membership H k x).mp hk
  have hgk := he.trans hgx (he.symm hkx)
  apply Set.ext
  intro y
  constructor
  · intro hy
    apply (cx_2026.left_coset_membership H k y).mpr
    exact he.trans (he.symm hgk) ((cx_2026.left_coset_membership H g y).mp hy)
  · intro hy
    apply (cx_2026.left_coset_membership H g y).mpr
    exact he.trans hgk ((cx_2026.left_coset_membership H k y).mp hy)

/-- The type of distinct left cosets: equal sets give the same index. -/
def LeftCosets : Set (Set G) := Set.range (fun g : G => g • (H : Set G))

/-- The coset containing a given element. -/
def cosetOf (x : G) : LeftCosets H := ⟨x • (H : Set G), ⟨x, rfl⟩⟩

lemma coset_unique (C : LeftCosets H) (x : G) (hx : x ∈ C.val) :
    C = cosetOf H x := by
  apply Subtype.ext
  rcases C.property with ⟨g, hg⟩
  change C.val = x • (H : Set G)
  rw [← hg] at hx ⊢
  exact cosets_eq_of_common_member H g x x hx (mem_own_coset H x)

/-- Distinct cosets are disjoint. Together with `mem_own_coset`, this is a partition. -/
lemma distinct_cosets_disjoint (C D : LeftCosets H) (hCD : C ≠ D) :
    Disjoint C.val D.val := by
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  apply hCD
  exact (coset_unique H C x hxC).trans (coset_unique H D x hxD).symm

/-!
## 2. Why the cardinality of the group is a sum

`Σ C : LeftCosets H, C.val` is the type of pairs consisting of a coset `C`
and an element of that coset. It is a *disjoint union*: the coset is recorded
as part of each pair. Its cardinality is the sum of the coset cardinalities,
by the general finite-counting lemma {name}`Nat.card_sigma`.

Forgetting the coset sends such a pair to an element of `G`. Conversely,
assign `x` to its own coset. Coverage makes this assignment possible;
uniqueness makes the two maps inverse. This is precisely where we prove
that every element is counted exactly once.
-/

/-- The partition gives a bijection with the disjoint union of its parts. -/
def groupEquivCosetUnion : G ≃ (Σ C : LeftCosets H, C.val) where
  toFun x := ⟨cosetOf H x, ⟨x, mem_own_coset H x⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨C, x, hx⟩
    have hC := coset_unique H C x hx
    subst C
    rfl

instance [Finite G] : Finite (LeftCosets H) :=
  (Set.finite_range (fun g : G => g • (H : Set G))).to_subtype

noncomputable instance [Finite G] : Fintype (LeftCosets H) := Fintype.ofFinite _

lemma card_eq_sum_coset_cards [Finite G] :
    Nat.card G = ∑ C : LeftCosets H, Nat.card C.val := by
  calc
    Nat.card G = Nat.card (Σ C : LeftCosets H, C.val) :=
      Nat.card_congr (groupEquivCosetUnion H)
    _ = ∑ C : LeftCosets H, Nat.card C.val := Nat.card_sigma

/-!
## 3. All the summands are equal

Week 4's {name}`cx_2026.left_coset_card` says that translation gives each
coset the same cardinality as `H`. We apply it to a representative of `C`.
Choosing a representative here is only a way to use that earlier lemma;
we still count each distinct coset once.
-/

lemma coset_card (C : LeftCosets H) : Nat.card C.val = Nat.card H := by
  rcases C.property with ⟨g, hg⟩
  rw [← hg]
  exact cx_2026.left_coset_card H g

/-- The number of distinct left cosets is the index of the subgroup. -/
noncomputable def cosetIndex : ℕ := Nat.card (LeftCosets H)

lemma card_eq_index_mul_subgroup [Finite G] :
    Nat.card G = cosetIndex H * Nat.card H := by
  calc
    Nat.card G = ∑ C : LeftCosets H, Nat.card C.val := card_eq_sum_coset_cards H
    _ = ∑ _C : LeftCosets H, Nat.card H := by
      apply Finset.sum_congr rfl
      intro C _
      exact coset_card H C
    _ = cosetIndex H * Nat.card H := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl

/-!
## 4. Lagrange's theorem

The order of `H` divides the order of `G`. The witness is the number of
cosets, and the preceding equality supplies the required factorisation.
-/

theorem lagrange [Finite G] : Nat.card H ∣ Nat.card G := by
  refine ⟨cosetIndex H, ?_⟩
  rw [card_eq_index_mul_subgroup H, Nat.mul_comm]

/-!
For the subgroup $`\{0,3,6,9\}` of the additive group modulo 12, the sum in
Section 2 is $`4+4+4`, and Section 3 turns it into $`3\cdot4`.
Which lemma prevents counting a residue twice? Which earlier result makes
each summand equal to four? Could a group of order 12 have a subgroup of
order 5?
-/

end

end cx_2026.Week5_2
