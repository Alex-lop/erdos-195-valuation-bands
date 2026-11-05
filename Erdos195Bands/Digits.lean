module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-!
# Binary digits and bit-reversed residues

For `x : ℤ` and `j : ℕ`, `bit j x` is the `j`-th binary digit of `x`, read in two's complement
for negative `x` (the `j`-th digit of the 2-adic expansion). It is computed with `Int.ediv` and
`Int.emod`, so a negative number gets its true residue, not the residue of its absolute value.
`rho n x` is the bit reversal of the residue of `x` mod `2 ^ n`: digit `0` of `x` is the most
significant digit of `rho n x`.

The two facts used later (`docs/proof.md`, §1):

* `bit_flip`: adding `2 ^ j * u` with `u` odd flips digit `j` (Lemma 1, alternation);
* `rho_cmp`: if `j < n`, then `rho n x < rho n (x + 2 ^ j * u)` exactly when digit `j` of `x`
  is `0`. So `rho n` lists the residues mod `2 ^ n` in the 2-adic (lexicographic) order.
-/

namespace Erdos195Bands

/-- The `j`-th binary digit `⌊x / 2 ^ j⌋ mod 2` of `x` (two's complement for negative `x`). -/
@[expose] def bit : ℕ → ℤ → ℤ
  | 0, x => x % 2
  | j + 1, x => bit j (x / 2)

/-- The bit-reversed residue `ρ_n(x) = ∑_{i < n} d_i(x) 2 ^ (n - 1 - i)` of `x` mod `2 ^ n`,
where `d_i(x)` is digit `i` of `x`. -/
@[expose] def rho : ℕ → ℤ → ℕ
  | 0, _ => 0
  | n + 1, x => 2 ^ n * (x % 2).toNat + rho n (x / 2)

theorem bit_cases (j : ℕ) (x : ℤ) : bit j x = 0 ∨ bit j x = 1 := by
  induction j generalizing x with
  | zero => simp only [bit]; omega
  | succ j ih => exact ih _

theorem two_pow_succ_mul (j : ℕ) (u : ℤ) : (2 : ℤ) ^ (j + 1) * u = 2 * (2 ^ j * u) := by
  ring

theorem half_add (j : ℕ) (x u : ℤ) : (x + 2 ^ (j + 1) * u) / 2 = x / 2 + 2 ^ j * u := by
  rw [two_pow_succ_mul, Int.add_mul_ediv_left _ _ (by norm_num)]

theorem mod_two_add (j : ℕ) (x u : ℤ) : (x + 2 ^ (j + 1) * u) % 2 = x % 2 := by
  rw [two_pow_succ_mul, Int.add_mul_emod_self_left]

/-- Lemma 1 (alternation): adding `2 ^ j * u` with `u` odd flips digit `j`. -/
theorem bit_flip (j : ℕ) (x u : ℤ) (hu : u % 2 = 1) : bit j (x + 2 ^ j * u) = 1 - bit j x := by
  induction j generalizing x with
  | zero => simp only [bit, pow_zero, one_mul]; omega
  | succ j ih => simp only [bit]; rw [half_add, ih]

theorem rho_lt (n : ℕ) (x : ℤ) : rho n x < 2 ^ n := by
  induction n generalizing x with
  | zero => simp [rho]
  | succ n ih =>
    have h := ih (x / 2)
    simp only [rho, pow_succ]
    rcases Int.emod_two_eq_zero_or_one x with hx | hx <;> simp only [hx] <;> norm_num <;> omega

/-- The bit-reversed residues of `x` and `x + 2 ^ j * u` (`u` odd, `j < n`) compare as digit `j`
of `x` says: `x` gets the smaller value iff its digit `j` is `0`. -/
theorem rho_cmp (n j : ℕ) (hj : j < n) (x u : ℤ) (hu : u % 2 = 1) :
    (bit j x = 0 → rho n x < rho n (x + 2 ^ j * u)) ∧
      (bit j x = 1 → rho n (x + 2 ^ j * u) < rho n x) := by
  induction n generalizing j x with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      have h1 := rho_lt n (x / 2)
      have h2 := rho_lt n ((x + u) / 2)
      simp only [bit, rho, pow_zero, one_mul]
      rcases Int.emod_two_eq_zero_or_one x with hx | hx
      · have hx' : (x + u) % 2 = 1 := by omega
        simp only [hx, hx']
        norm_num
        omega
      · have hx' : (x + u) % 2 = 0 := by omega
        simp only [hx, hx']
        norm_num
        omega
    | succ j =>
      have := ih j (by omega) (x / 2)
      simp only [bit, rho, half_add, mod_two_add]
      omega

/-- Equal residues mod `2 ^ n` have equal bit-reversed residues. -/
theorem rho_eq_of_dvd (n : ℕ) (x y : ℤ) (h : (2 : ℤ) ^ n ∣ y - x) : rho n x = rho n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    obtain ⟨c, hc⟩ := h
    have hy : y = x + 2 ^ (n + 1) * c := by linarith
    have e1 : x % 2 = y % 2 := by rw [hy, mod_two_add]
    have e2 : y / 2 - x / 2 = 2 ^ n * c := by rw [hy, half_add]; ring
    simp only [rho]
    rw [e1, ih (x / 2) (y / 2) ⟨c, e2⟩]

/-- Every nonzero integer is `2 ^ j * u` with `u` odd. -/
theorem exists_two_pow_mul_odd {d : ℤ} (hd : d ≠ 0) :
    ∃ (j : ℕ) (u : ℤ), u % 2 = 1 ∧ d = 2 ^ j * u := by
  obtain ⟨k, m, ⟨r, hr⟩, hk⟩ := Nat.exists_eq_two_pow_mul_odd (Int.natAbs_ne_zero.mpr hd)
  rcases Int.natAbs_eq d with h | h
  · exact ⟨k, m, by omega, by rw [h, hk]; push_cast; ring⟩
  · exact ⟨k, -(m : ℤ), by omega, by rw [h, hk]; push_cast; ring⟩

/-- Equal bit-reversed residues mod `2 ^ n` come from equal residues mod `2 ^ n`. -/
theorem dvd_of_rho_eq (n : ℕ) (x y : ℤ) (h : rho n x = rho n y) : (2 : ℤ) ^ n ∣ y - x := by
  rcases eq_or_ne (y - x) 0 with h0 | h0
  · rw [h0]
    exact dvd_zero _
  obtain ⟨j, u, hu, hd⟩ := exists_two_pow_mul_odd h0
  have hy : y = x + 2 ^ j * u := by linarith
  by_cases hj : j < n
  · have hc := rho_cmp n j hj x u hu
    rw [← hy] at hc
    rcases bit_cases j x with hb | hb
    · exact absurd h (hc.1 hb).ne
    · exact absurd h (hc.2 hb).ne'
  · rw [hd]
    exact (pow_dvd_pow 2 (not_lt.mp hj)).mul_right _

end Erdos195Bands
