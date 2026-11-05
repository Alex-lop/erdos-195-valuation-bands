module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

/-!
# Advertised statements

Partial progress on Erdős Problem #195 (<https://www.erdosproblems.com/195>).

A *permutation of `ℤ`* is a bijection `f : ℕ ≃ ℤ`, read as the sequence `f 0, f 1, f 2, …`.
A *monotone 4-term arithmetic progression* in it is a choice of indices `i < j < k < l` with
`(f i, f j, f k, f l) = (a, a + d, a + 2d, a + 3d)` for some `d ≠ 0`; a negative `d` gives a
decreasing progression. Such a progression is determined by the pair `(a, d)` of its first term
(in the order of the indices) and its difference.

* `Erdos195Bands.main_result`: one permutation of `ℤ` in which, for every `v`, only finitely
  many monotone 4-term progressions have a difference `d` with 2-adic valuation `ν₂(d) = v`.
* `Erdos195Bands.finite_depth`: for every `t ≥ 1`, some permutation of `ℤ` has no monotone
  4-term progression whose difference is not divisible by `2 ^ t`.

Erdős #195 asks for the largest `k` such that every permutation of `ℤ` has a monotone `k`-term
progression; the answer is known to be 3 or 4. These theorems do not decide it: the permutations
constructed in their proofs contain infinitely many monotone 4-term progressions
(`docs/proof.md`, Prop. 2).
-/

/-- One permutation of `ℤ` has, for every `v : ℕ`, only finitely many monotone 4-term arithmetic
progressions `(a, a + d, a + 2d, a + 3d)` (increasing or decreasing) with `ν₂(d) = v`. -/
theorem Erdos195Bands.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ v : ℕ, Set.Finite {p : ℤ × ℤ | p.2 ≠ 0 ∧ padicValInt 2 p.2 = v ∧
      ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ f i = p.1 ∧ f j = p.1 + p.2 ∧
        f k = p.1 + 2 * p.2 ∧ f l = p.1 + 3 * p.2} := by
  sorry

/-- For every `t ≥ 1` some permutation of `ℤ` has no monotone 4-term arithmetic progression,
increasing or decreasing, whose common difference is not divisible by `2 ^ t`. -/
theorem Erdos195Bands.finite_depth :
    ∀ t : ℕ, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ,
      ¬ ((2 : ℤ) ^ t ∣ d) → ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) := by
  sorry
