module

public import Solution
public import Mathlib.Logic.Equiv.Nat

/-!
# Independent fidelity audit of `Erdos195Bands.finite_depth` and `Erdos195Bands.main_result` (audit file, not part of the formalization)

The three definitions in the public section below are verbatim copies (docstrings included) of
formal-conjectures commit 5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`, pasted at the root namespace exactly as
there (formal-conjectures is not imported, so nothing clashes). `HasMonotoneAPNotDvd f k t` is FC's
`HasMonotoneAP f k` with `IsAPOfLength` inlined and the single conjunct `¬ (2 : ℤ) ^ t ∣ d` added.
-/

@[expose] public section

variable {α : Type*} [AddCommMonoid α]

/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/--
A function `f : β → α` has a monotone `k`-term arithmetic progression if there exists a choice
of indices `b 1 < b 2 < ... < b k` such that the subsequence `f (b i)` forms an increasing or
decreasing arithmetic progression of length `k`.
-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

end

public section

/-- FC's `HasMonotoneAP f k`, restricted to common differences not divisible by `2 ^ t`. -/
def HasMonotoneAPNotDvd {β : Type*} [Preorder β] (f : β → ℤ) (k t : ℕ) : Prop :=
  ∃ l : List β, (∃ a d : ℤ, ¬ (2 : ℤ) ^ t ∣ d ∧ (l.map f).IsAPOfLengthWith k a d) ∧
    l.Pairwise (· < ·)

/-- (1) For every `f` and `t`, the four-index body of `finite_depth` is exactly
`¬ HasMonotoneAPNotDvd f 4 t`. -/
theorem index_iff (f : ℕ → ℤ) (t : ℕ) :
    (∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ ((2 : ℤ) ^ t ∣ d) →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d)) ↔
    ¬ HasMonotoneAPNotDvd f 4 t := by
  constructor
  · rintro H ⟨l, ⟨a, d, hd, hAP⟩, hl⟩
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp [List.IsAPOfLengthWith, List.range_succ] at hAP
    simp at hl
    rcases hAP with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact H i j k m hl.1.1 hl.2.1.1 hl.2.2 a d hd ⟨h1, h2, h3, h4⟩
    · refine H i j k m hl.1.1 hl.2.1.1 hl.2.2 _ (-d) (by rwa [dvd_neg]) ⟨h1, ?_, ?_, ?_⟩ <;> omega
  · rintro H i j k l hij hjk hkl a d hd ⟨h1, h2, h3, h4⟩
    refine H ⟨[i, j, k, l], ⟨a, d, hd, Or.inl ?_⟩, ?_⟩
    · simp [List.range_succ, h1, h2, h3, h4]
    · simp
      omega

/-- (2) Theorem G in formal-conjectures' vocabulary, from `finite_depth` by term-mode unfolding
through `index_iff`. -/
theorem fc_form : ∀ t : ℕ, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAPNotDvd f 4 t :=
  fun t ht => (Erdos195Bands.finite_depth t ht).imp fun f hf => (index_iff f t).mp hf

/-- (3) It is a genuine restriction of FC's predicate, and the two pieces cover it. -/
theorem restrict_split {β : Type*} [Preorder β] (f : β → ℤ) (k t : ℕ) :
    HasMonotoneAP f k ↔ HasMonotoneAPNotDvd f k t ∨
      ∃ l : List β, (∃ a d : ℤ, (2 : ℤ) ^ t ∣ d ∧ (l.map f).IsAPOfLengthWith k a d) ∧
        l.Pairwise (· < ·) := by
  constructor
  · rintro ⟨l, ⟨a, d, h⟩, hl⟩
    by_cases hd : (2 : ℤ) ^ t ∣ d
    · exact Or.inr ⟨l, ⟨a, d, hd, h⟩, hl⟩
    · exact Or.inl ⟨l, ⟨a, d, hd, h⟩, hl⟩
  · rintro (⟨l, ⟨a, d, _, h⟩, hl⟩ | ⟨l, ⟨a, d, _, h⟩, hl⟩) <;> exact ⟨l, ⟨a, d, h⟩, hl⟩

/-- (4) The restriction is well defined on the list: the difference is determined up to sign,
so `¬ 2 ^ t ∣ d` does not depend on which witness `(a, d)` is chosen. -/
theorem diff_determined (s : List ℤ) (a d a' d' : ℤ) (h : s.IsAPOfLengthWith 4 a d)
    (h' : s.IsAPOfLengthWith 4 a' d') : d' = d ∨ d' = -d := by
  unfold List.IsAPOfLengthWith at h h'
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> simp [List.range_succ] at h' <;> omega

/-- (5) `main_result` in FC's vocabulary: the index-ordered progression `(a, a + d, a + 2d,
a + 3d)` of `main_result` is the first disjunct of `List.IsAPOfLengthWith 4 a d` for the list of
its indices. -/
theorem pair_iff (f : ℕ → ℤ) (a d : ℤ) :
    (∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧
      f l = a + 3 * d) ↔
    ∃ l : List ℕ, l.map f = (List.range 4).map (fun n ↦ a + n • d) ∧ l.Pairwise (· < ·) := by
  constructor
  · rintro ⟨i, j, k, l, hij, hjk, hkl, h1, h2, h3, h4⟩
    refine ⟨[i, j, k, l], ?_, ?_⟩
    · simp [List.range_succ, h1, h2, h3, h4]
    · simp
      omega
  · rintro ⟨l, hAP, hl⟩
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp [List.range_succ] at hAP
    simp at hl
    exact ⟨i, j, k, m, hl.1.1, hl.2.1.1, hl.2.2, hAP⟩

/-- (6) `main_result` restated with the list form of (5), from `main_result` and `pair_iff`. -/
theorem fc_form_main : ∃ f : ℕ ≃ ℤ, ∀ v : ℕ, Set.Finite {p : ℤ × ℤ | p.2 ≠ 0 ∧
    padicValInt 2 p.2 = v ∧
      ∃ l : List ℕ, l.map f = (List.range 4).map (fun n ↦ p.1 + n • p.2) ∧ l.Pairwise (· < ·)} :=
  Erdos195Bands.main_result.imp fun f hf v =>
    (hf v).subset fun p ⟨h0, hv, h⟩ => ⟨h0, hv, (pair_iff f p.1 p.2).mpr h⟩

/-- (7) Non-vacuity of the restricted predicate: some permutation of `ℤ` does have a monotone
4-term progression with difference not divisible by `2 ^ t` (Mathlib's `intEquivNat.symm` sends
`0, 2, 4, 6` to `0, 1, 2, 3`, difference `1`), so `fc_form` is not trivially true. -/
theorem nonvacuous (t : ℕ) (ht : 1 ≤ t) : ∃ f : ℕ ≃ ℤ, HasMonotoneAPNotDvd f 4 t := by
  refine ⟨Equiv.intEquivNat.symm, [0, 2, 4, 6], ⟨0, 1, ?_, Or.inl (by decide)⟩, by decide⟩
  intro h
  have h1 := Int.eq_one_of_dvd_one (by positivity) h
  have h2 : (2 : ℤ) ^ 1 ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) ht
  omega

/-- (8) The theorems are partial: the enumeration `E (fun _ => 1)` that proves `finite_depth 1`
(see `Erdos195Bands.exists_enum_no_ap`) does have a monotone 4-term progression, namely
`0, -6, -12, -18` (difference divisible by `2`). -/
theorem seam_ap_depth : HasMonotoneAP (Erdos195Bands.E (fun _ => 1)) 4 := by
  obtain ⟨h1, h2, h3⟩ := Erdos195Bands.seam_example
  have a := Erdos195Bands.symm_lt_of_rank_lt _ h1
  have b := Erdos195Bands.symm_lt_of_rank_lt _ h2
  have c := Erdos195Bands.symm_lt_of_rank_lt _ h3
  refine ⟨[(Erdos195Bands.E (fun _ => 1)).symm 0, (Erdos195Bands.E (fun _ => 1)).symm (-6),
    (Erdos195Bands.E (fun _ => 1)).symm (-12), (Erdos195Bands.E (fun _ => 1)).symm (-18)],
    ⟨0, -6, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ]
  · simp
    omega

/-- (9) Likewise the enumeration `E (fun s => s + 1)` that proves `main_result` (see
`Erdos195Bands.exists_enum_finite`) has the monotone 4-term progression `0, -44, -88, -132`
(`ν₂(-44) = 2`): `main_result` bounds the progressions of each valuation, it does not exclude
them. -/
theorem seam_ap_main : HasMonotoneAP (Erdos195Bands.E (fun s => s + 1)) 4 := by
  obtain ⟨h1, h2, h3⟩ := Erdos195Bands.seam_example_main
  have a := Erdos195Bands.symm_lt_of_rank_lt _ h1
  have b := Erdos195Bands.symm_lt_of_rank_lt _ h2
  have c := Erdos195Bands.symm_lt_of_rank_lt _ h3
  refine ⟨[(Erdos195Bands.E (fun s => s + 1)).symm 0, (Erdos195Bands.E (fun s => s + 1)).symm (-44),
    (Erdos195Bands.E (fun s => s + 1)).symm (-88), (Erdos195Bands.E (fun s => s + 1)).symm (-132)],
    ⟨0, -44, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ]
  · simp
    omega

end

#print axioms index_iff
#print axioms fc_form
#print axioms restrict_split
#print axioms diff_determined
#print axioms pair_iff
#print axioms fc_form_main
#print axioms nonvacuous
#print axioms seam_ap_depth
#print axioms seam_ap_main
