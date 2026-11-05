module

public import Erdos195Bands

public section

/-!
# Proved solution

Comparator checks that each declaration below has exactly the statement of its counterpart in
`Challenge.lean` and uses only the permitted axioms. The proofs live in
`Erdos195Bands/Basic.lean` (the construction and Theorems G and H), on top of the binary digits
and bit-reversed residues of `Erdos195Bands/Digits.lean`.
-/

theorem Erdos195Bands.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ v : ℕ, Set.Finite {p : ℤ × ℤ | p.2 ≠ 0 ∧ padicValInt 2 p.2 = v ∧
      ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ f i = p.1 ∧ f j = p.1 + p.2 ∧
        f k = p.1 + 2 * p.2 ∧ f l = p.1 + 3 * p.2} :=
  Erdos195Bands.exists_enum_finite

theorem Erdos195Bands.finite_depth :
    ∀ t : ℕ, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ,
      ¬ ((2 : ℤ) ^ t ∣ d) → ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) :=
  Erdos195Bands.exists_enum_no_ap
