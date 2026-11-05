module

public import Erdos195Bands.Digits
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

public section

/-!
# Geneson-type bands with a stage-dependent modulus

This file follows `docs/proof.md`. Fix `t : ℕ → ℕ` and the base `a = 3`; put `m_k = 2 ^ t k`.

* `L t k = 2 m_1 + ⋯ + 2 m_k`. The *top exponent* of `x` in stage `k` is
  `top t k x = L t k + m_{k+1} - ρ(x)` for `x < 0` and `L t k + m_{k+1} + 1 + ρ(x)` for `x > 0`,
  where `ρ = rho (t (k+1))` is the bit-reversed residue mod `m_{k+1}`. It lies in
  `(L t k, L t (k+1)]` (`top_bounds`), so it increases strictly with `k`.
* The *stage* of `x` is the least `k` with `|x| < 3 ^ top t k x` (`stage`). So `x` lies in the band
  `B_k` of the write-up: `3 ^ top t (k-1) x ≤ |x| < 3 ^ top t k x`.
* The enumeration `E t` lists `0` first, then for `k = 0, 1, 2, …` the negative elements of stage
  `k` in increasing 2-adic order, then the positive ones in decreasing 2-adic order. It is built
  from an injective rank `rank t : ℤ → ℕ` (`rank_injective`) and lists ℤ by increasing rank.
* `core`: every monotone 4-term AP of `E t` has a *seam step* (`Seam`): a stage `s` with
  `2 ^ t (s+1) ∣ d` and both `|x_i|` and `|d|` bounded in terms of `s`.

With `t` constant this gives Theorem G (`exists_enum_no_ap`), and with `t s = s + 1` it gives
Theorem H, the finiteness of the monotone 4-APs with any fixed 2-adic valuation of `d`
(`exists_enum_finite`).
-/

namespace Erdos195Bands

variable (t : ℕ → ℕ)

/-! ### Exponents, stages and bands -/

/-- `L t k = 2 m_1 + ⋯ + 2 m_k` with `m_σ = 2 ^ t σ` (this is `A_k + m_k` of the write-up). -/
def L : ℕ → ℕ
  | 0 => 0
  | k + 1 => L k + 2 * 2 ^ t (k + 1)

/-- The top exponent `β_{k+1}(x)` of `x` in stage `k`. -/
def top (k : ℕ) (x : ℤ) : ℕ :=
  if x < 0 then L t k + 2 ^ t (k + 1) - rho (t (k + 1)) x
  else L t k + 2 ^ t (k + 1) + 1 + rho (t (k + 1)) x

theorem L_succ (k : ℕ) : L t (k + 1) = L t k + 2 * 2 ^ t (k + 1) := by simp only [L]

theorem L_mono {k k' : ℕ} (h : k ≤ k') : L t k ≤ L t k' := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [L_succ]; omega

theorem le_L (k : ℕ) : 2 * k ≤ L t k := by
  induction k with
  | zero => simp [L]
  | succ k ih =>
    have := Nat.one_le_two_pow (n := t (k + 1))
    rw [L_succ]
    omega

theorem top_neg {k : ℕ} {x : ℤ} (hx : x < 0) :
    top t k x + rho (t (k + 1)) x = L t k + 2 ^ t (k + 1) := by
  have := rho_lt (t (k + 1)) x
  simp only [top, hx, ↓reduceIte]
  omega

theorem top_pos {k : ℕ} {x : ℤ} (hx : 0 ≤ x) :
    top t k x = L t k + 2 ^ t (k + 1) + 1 + rho (t (k + 1)) x := by
  simp only [top, not_lt.mpr hx, ↓reduceIte]

/-- Lemma 2 (tiling): the top exponent of stage `k` lies in `(L t k, L t (k+1)]`. -/
theorem top_bounds (k : ℕ) (x : ℤ) : L t k < top t k x ∧ top t k x ≤ L t (k + 1) := by
  have h := rho_lt (t (k + 1)) x
  rw [L_succ]
  rcases lt_or_ge x 0 with hx | hx
  · have := top_neg t (k := k) hx
    omega
  · have := top_pos t (k := k) hx
    omega

theorem exists_stage (x : ℤ) : ∃ k, |x| < (3 : ℤ) ^ top t k x := by
  refine ⟨x.natAbs, ?_⟩
  have h1 : x.natAbs < 3 ^ x.natAbs := Nat.lt_pow_self (by norm_num)
  have h2 : 3 ^ x.natAbs ≤ 3 ^ top t x.natAbs x := by
    apply Nat.pow_le_pow_right (by norm_num)
    have := le_L t x.natAbs
    have := (top_bounds t x.natAbs x).1
    omega
  have h3 : ((x.natAbs : ℕ) : ℤ) < ((3 ^ top t x.natAbs x : ℕ) : ℤ) := by
    exact_mod_cast h1.trans_le h2
  push_cast at h3
  exact h3

/-- The stage of `x`: the least `k` with `|x| < 3 ^ top t k x`. -/
noncomputable def stage (x : ℤ) : ℕ := Nat.find (exists_stage t x)

/-- Upper end of the band of `x`. -/
theorem abs_lt_stage (x : ℤ) : |x| < (3 : ℤ) ^ top t (stage t x) x :=
  Nat.find_spec (exists_stage t x)

/-- Lower end of the band of `x`: `x` is not in any earlier stage. -/
theorem le_abs_of_lt_stage {x : ℤ} {k : ℕ} (h : k < stage t x) : (3 : ℤ) ^ top t k x ≤ |x| :=
  not_lt.mp (Nat.find_min (exists_stage t x) h)

theorem stage_bound (x : ℤ) :
    -(3 : ℤ) ^ top t (stage t x) x < x ∧ x < 3 ^ top t (stage t x) x :=
  abs_lt.mp (abs_lt_stage t x)

theorem abs_lt_L (x : ℤ) : |x| < (3 : ℤ) ^ L t (stage t x + 1) :=
  (abs_lt_stage t x).trans_le (pow_le_pow_right₀ (by norm_num) (top_bounds t _ x).2)

/-! ### The rank and the enumeration -/

/-- Inside stage `s` the 2-adic order is read off `rho (NN t s)`; `2 ^ NN t s` exceeds the
diameter of each half of the band. -/
def NN (s : ℕ) : ℕ := 2 * L t (s + 1)

theorem NN_lt {s s' : ℕ} (h : s < s') : NN t s < NN t s' := by
  have h1 := L_mono t (show s + 1 + 1 ≤ s' + 1 by omega)
  have h2 := L_succ t (s + 1)
  have h3 := Nat.one_le_two_pow (n := t (s + 1 + 1))
  unfold NN
  omega

/-- The rank of `x`: `0` for `x = 0`; for `x` in stage `s`, with `K = 2 ^ NN t s`, a negative `x`
gets `2K + ρ(x)` and a positive `x` gets `4K - 1 - ρ(x)`, where `ρ = rho (NN t s)`. -/
noncomputable def rank (x : ℤ) : ℕ :=
  if x = 0 then 0
  else if x < 0 then 2 ^ (NN t (stage t x) + 1) + rho (NN t (stage t x)) x
  else 2 ^ (NN t (stage t x) + 2) - 1 - rho (NN t (stage t x)) x

theorem rank_zero : rank t 0 = 0 := by simp [rank]

theorem rank_of_neg {x : ℤ} (hx : x < 0) :
    rank t x = 2 * 2 ^ NN t (stage t x) + rho (NN t (stage t x)) x := by
  simp only [rank, hx.ne, hx, ↓reduceIte, pow_succ]
  ring

theorem rank_of_pos {x : ℤ} (hx : 0 < x) :
    rank t x + 1 + rho (NN t (stage t x)) x = 4 * 2 ^ NN t (stage t x) := by
  have := rho_lt (NN t (stage t x)) x
  simp only [rank, hx.ne', not_lt.mpr hx.le, ↓reduceIte]
  rw [show 2 ^ (NN t (stage t x) + 2) = 4 * 2 ^ NN t (stage t x) by ring]
  omega

theorem rank_bounds_neg {x : ℤ} (hx : x < 0) :
    2 * 2 ^ NN t (stage t x) ≤ rank t x ∧ rank t x < 3 * 2 ^ NN t (stage t x) := by
  have := rho_lt (NN t (stage t x)) x
  rw [rank_of_neg t hx]
  omega

theorem rank_bounds_pos {x : ℤ} (hx : 0 < x) :
    3 * 2 ^ NN t (stage t x) ≤ rank t x ∧ rank t x < 4 * 2 ^ NN t (stage t x) := by
  have := rho_lt (NN t (stage t x)) x
  have := rank_of_pos t hx
  omega

theorem rank_bounds {x : ℤ} (hx : x ≠ 0) :
    2 * 2 ^ NN t (stage t x) ≤ rank t x ∧ rank t x < 4 * 2 ^ NN t (stage t x) := by
  rcases lt_or_gt_of_ne hx with h | h
  · have := rank_bounds_neg t h
    omega
  · have := rank_bounds_pos t h
    omega

theorem four_mul_le {s s' : ℕ} (h : s < s') : 4 * 2 ^ NN t s ≤ 2 * 2 ^ NN t s' := by
  have h1 : 2 ^ (NN t s + 1) ≤ 2 ^ NN t s' := Nat.pow_le_pow_right (by norm_num) (NN_lt t h)
  rw [pow_succ] at h1
  omega

/-- Earlier stages come first. -/
theorem rank_lt_of_stage_lt {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (h : stage t x < stage t y) :
    rank t x < rank t y := by
  have := four_mul_le t h
  have := rank_bounds t hx
  have := rank_bounds t hy
  omega

theorem stage_le_of_rank_lt {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (h : rank t x < rank t y) :
    stage t x ≤ stage t y :=
  not_lt.mp fun hc => lt_asymm h (rank_lt_of_stage_lt t hy hx hc)

theorem ne_zero_of_rank_lt {x y : ℤ} (h : rank t x < rank t y) : y ≠ 0 := by
  rintro rfl
  rw [rank_zero] at h
  omega

/-- Inside a stage, the negatives come before the positives. -/
theorem stage_lt_of_rank_lt_pos_neg {y u : ℤ} (hy : 0 < y) (hu : u < 0)
    (h : rank t y < rank t u) : stage t y < stage t u := by
  rcases (stage_le_of_rank_lt t hy.ne' hu.ne h).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have h1 := rank_bounds_pos t hy
    have h2 := rank_bounds_neg t hu
    rw [heq] at h1
    omega

/-- Inside a stage, the negatives are listed by increasing `rho`, i.e. increasing 2-adic order. -/
theorem rho_lt_of_rank_lt_neg {x y : ℤ} (hx : x < 0) (hy : y < 0) (hs : stage t x = stage t y)
    (h : rank t x < rank t y) : rho (NN t (stage t x)) x < rho (NN t (stage t x)) y := by
  rw [rank_of_neg t hx, rank_of_neg t hy, ← hs] at h
  omega

/-- Inside a stage, the positives are listed by decreasing `rho`, i.e. decreasing 2-adic order. -/
theorem rho_lt_of_rank_lt_pos {x y : ℤ} (hx : 0 < x) (hy : 0 < y) (hs : stage t x = stage t y)
    (h : rank t x < rank t y) : rho (NN t (stage t x)) y < rho (NN t (stage t x)) x := by
  have h1 := rank_of_pos t hx
  have h2 := rank_of_pos t hy
  rw [← hs] at h2
  omega

theorem three_pow_le (n : ℕ) : (3 : ℤ) ^ n ≤ 2 ^ (2 * n) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- Two integers of one sign and one stage with the same `rho (NN t s)` are equal. -/
theorem eq_of_rho_eq {x y : ℤ} (hs : stage t x = stage t y)
    (hsgn : (x < 0 ∧ y < 0) ∨ (0 < x ∧ 0 < y))
    (h : rho (NN t (stage t x)) x = rho (NN t (stage t x)) y) : x = y := by
  have hd := dvd_of_rho_eq _ _ _ h
  have hx := abs_lt_L t x
  have hy := abs_lt_L t y
  have hb := three_pow_le (L t (stage t x + 1))
  rw [hs] at hx hb hd
  have hlt : |y - x| < (2 : ℤ) ^ NN t (stage t y) := by
    unfold NN
    rw [abs_lt] at hx hy ⊢
    constructor <;> rcases hsgn with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  linarith

theorem rank_injective : Function.Injective (rank t) := by
  intro x y h
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne y 0 with rfl | hy
    · rfl
    · have := rank_bounds t hy
      rw [rank_zero] at h
      omega
  rcases eq_or_ne y 0 with rfl | hy
  · have := rank_bounds t hx
    rw [rank_zero] at h
    omega
  have hs : stage t x = stage t y := by
    rcases lt_trichotomy (stage t x) (stage t y) with hc | hc | hc
    · exact absurd h (rank_lt_of_stage_lt t hx hy hc).ne
    · exact hc
    · exact absurd h (rank_lt_of_stage_lt t hy hx hc).ne'
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [rank_of_neg t hx', rank_of_neg t hy', ← hs] at h
    exact eq_of_rho_eq t hs (Or.inl ⟨hx', hy'⟩) (by omega)
  · have h1 := rank_bounds_neg t hx'
    have h2 := rank_bounds_pos t hy'
    rw [hs] at h1
    omega
  · have h1 := rank_bounds_pos t hx'
    have h2 := rank_bounds_neg t hy'
    rw [hs] at h1
    omega
  · have h1 := rank_of_pos t hx'
    have h2 := rank_of_pos t hy'
    rw [← hs] at h2
    exact eq_of_rho_eq t hs (Or.inr ⟨hx', hy'⟩) (by omega)

instance : Infinite (Set.range (rank t)) :=
  (Set.infinite_range_of_injective (rank_injective t)).to_subtype

/-- The enumeration of ℤ: list the integers by increasing rank. -/
noncomputable def E : ℕ ≃ ℤ :=
  (Nat.Subtype.orderIsoOfNat (Set.range (rank t))).toEquiv.trans
    (Equiv.ofInjective (rank t) (rank_injective t)).symm

theorem rank_E (n : ℕ) :
    rank t (E t n) = (Nat.Subtype.orderIsoOfNat (Set.range (rank t)) n : ℕ) :=
  Equiv.apply_ofInjective_symm (rank_injective t) _

theorem rank_E_lt {i j : ℕ} (h : i < j) : rank t (E t i) < rank t (E t j) := by
  rw [rank_E, rank_E]
  exact (Nat.Subtype.orderIsoOfNat (Set.range (rank t))).strictMono h

/-- Positions in `E t` are ordered as ranks. -/
theorem symm_lt_of_rank_lt {x y : ℤ} (h : rank t x < rank t y) : (E t).symm x < (E t).symm y := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hc | hc
  · have := rank_E_lt t hc
    simp only [Equiv.apply_symm_apply] at this
    omega
  · rw [(E t).symm.injective hc] at h
    omega

/-! ### Separation lemmas -/

/-- (L2), first case: a negative `y` listed before a positive `u` satisfies `3|y| < U(u)`. -/
theorem opp_neg_pos {y u : ℤ} (hy : y < 0) (hu : 0 < u) (h : rank t y < rank t u) :
    -3 * y < 3 ^ top t (stage t u) u := by
  have hs := stage_le_of_rank_lt t hy.ne hu.ne' h
  have h1 := (stage_bound t y).1
  have h2 : top t (stage t y) y + 1 ≤ top t (stage t u) u := by
    rcases hs.lt_or_eq with hlt | heq
    · have a1 := (top_bounds t (stage t y) y).2
      have a2 := (top_bounds t (stage t u) u).1
      have b1 := L_mono t (show stage t y + 1 ≤ stage t u by omega)
      omega
    · have a1 := top_neg t (k := stage t u) hy
      have a2 := top_pos t (k := stage t u) hu.le
      rw [heq]
      omega
  calc -3 * y < 3 * 3 ^ top t (stage t y) y := by linarith
    _ = 3 ^ (top t (stage t y) y + 1) := by ring
    _ ≤ 3 ^ top t (stage t u) u := pow_le_pow_right₀ (by norm_num) h2

/-- (L2), second case: a positive `y` listed before a negative `u` satisfies `3|y| < U(u)`. -/
theorem opp_pos_neg {y u : ℤ} (hy : 0 < y) (hu : u < 0) (h : rank t y < rank t u) :
    3 * y < 3 ^ top t (stage t u) u := by
  have hs := stage_lt_of_rank_lt_pos_neg t hy hu h
  have h1 := (stage_bound t y).2
  have h2 : top t (stage t y) y + 1 ≤ top t (stage t u) u := by
    have a1 := (top_bounds t (stage t y) y).2
    have a2 := (top_bounds t (stage t u) u).1
    have b1 := L_mono t (show stage t y + 1 ≤ stage t u by omega)
    omega
  calc 3 * y < 3 * 3 ^ top t (stage t y) y := by linarith
    _ = 3 ^ (top t (stage t y) y + 1) := by ring
    _ ≤ 3 ^ top t (stage t u) u := pow_le_pow_right₀ (by norm_num) h2

/-! ### Step rules -/

/-- A *seam* at `x` for the difference `d`: a stage `s` with `2 ^ t (s+1) ∣ d`,
`|x| < 3 ^ L t (s+1)` and `|d| < 4 · 3 ^ L t (s+1)`. -/
def Seam (x d : ℤ) : Prop :=
  ∃ s : ℕ, (2 : ℤ) ^ t (s + 1) ∣ d ∧ |x| < 3 ^ L t (s + 1) ∧ |d| < 4 * 3 ^ L t (s + 1)

theorem dvd_of_le {j n : ℕ} {d u : ℤ} (hd : d = 2 ^ j * u) (h : n ≤ j) : (2 : ℤ) ^ n ∣ d := by
  rw [hd]
  exact (pow_dvd_pow 2 h).mul_right _

/-- Step rules (a)–(c) for negative terms. Let `x → x + d` be a step between two negative terms
of an AP, `x` listed first, with `d = 2 ^ j u`, `u` odd. If the step shrinks, or grows with
`|x + d| < (7/3) U(x)`, then it is *appropriate* (digit `j` of `x` is `0`) or it is a seam. -/
theorem step_neg {x d u : ℤ} {j : ℕ} (hu : u % 2 = 1) (hd : d = 2 ^ j * u)
    (hx : x < 0) (hx' : x + d < 0) (hr : rank t x < rank t (x + d))
    (hmag : 0 < d ∨ -3 * (x + d) < 7 * 3 ^ top t (stage t x) x) :
    bit j x = 0 ∨ Seam t x d := by
  rcases (stage_le_of_rank_lt t hx.ne hx'.ne hr).lt_or_eq with hlt | heq
  · have hlow := le_abs_of_lt_stage t hlt
    have hup := abs_lt_stage t x
    have a1 := top_neg t (k := stage t x) hx
    have a2 := top_neg t (k := stage t x) hx'
    have hV : (0 : ℤ) < 3 ^ top t (stage t x) x := by positivity
    rw [abs_of_neg hx'] at hlow
    rcases lt_trichotomy (rho (t (stage t x + 1)) x) (rho (t (stage t x + 1)) (x + d))
      with hc | hc | hc
    · -- appropriate
      left
      have hj : j < t (stage t x + 1) := by
        by_contra hj
        have := rho_eq_of_dvd _ x (x + d) (by rw [add_sub_cancel_left]; exact dvd_of_le hd (not_lt.mp hj))
        omega
      rcases bit_cases j x with hb | hb
      · exact hb
      · have := (rho_cmp _ j hj x u hu).2 hb
        rw [← hd] at this
        omega
    · -- seam
      right
      have hT : (3 : ℤ) ^ top t (stage t x) x ≤ 3 ^ L t (stage t x + 1) :=
        pow_le_pow_right₀ (by norm_num) (top_bounds t _ x).2
      refine ⟨stage t x, ?_, hup.trans_le hT, ?_⟩
      · have := dvd_of_rho_eq _ x (x + d) hc
        rwa [add_sub_cancel_left] at this
      · rw [abs_of_neg hx] at hup
        rw [abs_lt]
        constructor <;> rcases hmag with hm | hm <;> linarith
    · -- impossible: `x + d` would lie above `3 U(x)`
      exfalso
      have h3 : top t (stage t x) x + 1 ≤ top t (stage t x) (x + d) := by omega
      have h4 : (3 : ℤ) ^ (top t (stage t x) x + 1) ≤ 3 ^ top t (stage t x) (x + d) :=
        pow_le_pow_right₀ (by norm_num) h3
      rw [pow_succ] at h4
      rw [abs_of_neg hx] at hup
      rcases hmag with hm | hm <;> linarith
  · left
    have hc := rho_lt_of_rank_lt_neg t hx hx' heq hr
    have hj : j < NN t (stage t x) := by
      by_contra hj
      have := rho_eq_of_dvd _ x (x + d) (by rw [add_sub_cancel_left]; exact dvd_of_le hd (not_lt.mp hj))
      omega
    rcases bit_cases j x with hb | hb
    · exact hb
    · have := (rho_cmp _ j hj x u hu).2 hb
      rw [← hd] at this
      omega

/-- Step rules (a)–(c) for positive terms: the mirror image of `step_neg`; appropriate now means
that digit `j` of `x` is `1`. -/
theorem step_pos {x d u : ℤ} {j : ℕ} (hu : u % 2 = 1) (hd : d = 2 ^ j * u)
    (hx : 0 < x) (hx' : 0 < x + d) (hr : rank t x < rank t (x + d))
    (hmag : d < 0 ∨ 3 * (x + d) < 7 * 3 ^ top t (stage t x) x) :
    bit j x = 1 ∨ Seam t x d := by
  rcases (stage_le_of_rank_lt t hx.ne' hx'.ne' hr).lt_or_eq with hlt | heq
  · have hlow := le_abs_of_lt_stage t hlt
    have hup := abs_lt_stage t x
    have a1 := top_pos t (k := stage t x) hx.le
    have a2 := top_pos t (k := stage t x) hx'.le
    have hV : (0 : ℤ) < 3 ^ top t (stage t x) x := by positivity
    rw [abs_of_pos hx'] at hlow
    rcases lt_trichotomy (rho (t (stage t x + 1)) (x + d)) (rho (t (stage t x + 1)) x)
      with hc | hc | hc
    · -- appropriate
      left
      have hj : j < t (stage t x + 1) := by
        by_contra hj
        have := rho_eq_of_dvd _ x (x + d) (by rw [add_sub_cancel_left]; exact dvd_of_le hd (not_lt.mp hj))
        omega
      rcases bit_cases j x with hb | hb
      · have := (rho_cmp _ j hj x u hu).1 hb
        rw [← hd] at this
        omega
      · exact hb
    · -- seam
      right
      have hT : (3 : ℤ) ^ top t (stage t x) x ≤ 3 ^ L t (stage t x + 1) :=
        pow_le_pow_right₀ (by norm_num) (top_bounds t _ x).2
      refine ⟨stage t x, ?_, hup.trans_le hT, ?_⟩
      · have := dvd_of_rho_eq _ x (x + d) hc.symm
        rwa [add_sub_cancel_left] at this
      · rw [abs_of_pos hx] at hup
        rw [abs_lt]
        constructor <;> rcases hmag with hm | hm <;> linarith
    · -- impossible
      exfalso
      have h3 : top t (stage t x) x + 1 ≤ top t (stage t x) (x + d) := by omega
      have h4 : (3 : ℤ) ^ (top t (stage t x) x + 1) ≤ 3 ^ top t (stage t x) (x + d) :=
        pow_le_pow_right₀ (by norm_num) h3
      rw [pow_succ] at h4
      rw [abs_of_pos hx] at hup
      rcases hmag with hm | hm <;> linarith
  · left
    have hc := rho_lt_of_rank_lt_pos t hx hx' heq hr
    have hj : j < NN t (stage t x) := by
      by_contra hj
      have := rho_eq_of_dvd _ x (x + d) (by rw [add_sub_cancel_left]; exact dvd_of_le hd (not_lt.mp hj))
      omega
    rcases bit_cases j x with hb | hb
    · have := (rho_cmp _ j hj x u hu).1 hb
      rw [← hd] at this
      omega
    · exact hb

/-! ### The case analysis -/

/-- Theorem H (seam steps): if `a, a + d, a + 2d, a + 3d` (`d ≠ 0`) appear in this order in `E t`,
one of the steps from `a`, `a + d`, `a + 2d` is a seam. -/
theorem core {a d : ℤ} (hd0 : d ≠ 0) (h1 : rank t a < rank t (a + d))
    (h2 : rank t (a + d) < rank t (a + d + d)) (h3 : rank t (a + d + d) < rank t (a + d + d + d)) :
    Seam t a d ∨ Seam t (a + d) d ∨ Seam t (a + d + d) d := by
  have n1 := ne_zero_of_rank_lt t h1
  have n2 := ne_zero_of_rank_lt t h2
  have n3 := ne_zero_of_rank_lt t h3
  obtain ⟨j, u, hu, hd⟩ := exists_two_pow_mul_odd hd0
  by_contra hns
  simp only [not_or] at hns
  obtain ⟨ns0, ns1, ns2⟩ := hns
  -- the digits `j` of consecutive terms alternate (Lemma 1)
  have c0 := bit_cases j a
  have f0 : bit j (a + d) = 1 - bit j a := by rw [hd]; exact bit_flip j a u hu
  have f1 : bit j (a + d + d) = 1 - bit j (a + d) := by rw [hd]; exact bit_flip j _ u hu
  -- the bands of the two middle terms
  have B1 := stage_bound t (a + d)
  have B2 := stage_bound t (a + d + d)
  rcases lt_or_gt_of_ne hd0 with hdn | hdp
  · -- decreasing progression
    rcases lt_or_ge 0 (a + d + d) with hA | hA
    · -- `a, a + d, a + 2d` positive: two shrinking steps (one sign, or 3 + 1)
      have e0 := (step_pos t hu hd (by linarith) (by linarith) h1 (Or.inl hdn)).resolve_right ns0
      have e1 := (step_pos t hu hd (by linarith) hA h2 (Or.inl hdn)).resolve_right ns1
      omega
    have hA' : a + d + d < 0 := lt_of_le_of_ne hA n2
    rcases lt_or_ge 0 (a + d) with hB | hB
    · -- 2 + 2
      have e0 := (step_pos t hu hd (by linarith) hB h1 (Or.inl hdn)).resolve_right ns0
      have o := opp_pos_neg t hB hA' h2
      have e2 := (step_neg t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega
    have hB' : a + d < 0 := lt_of_le_of_ne hB n1
    rcases lt_or_ge 0 a with hC | hC
    · -- 1 + 3
      have o := opp_pos_neg t hC hB' h1
      have e1 := (step_neg t hu hd hB' hA' h2 (Or.inr (by linarith))).resolve_right ns1
      have e2 := (step_neg t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega
    · -- `a ≤ 0`: one sign growing, or `a = 0`
      have e1 := (step_neg t hu hd hB' hA' h2 (Or.inr (by linarith))).resolve_right ns1
      have e2 := (step_neg t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega
  · -- increasing progression: the mirror image
    rcases lt_or_ge (a + d + d) 0 with hA | hA
    · have e0 := (step_neg t hu hd (by linarith) (by linarith) h1 (Or.inl hdp)).resolve_right ns0
      have e1 := (step_neg t hu hd (by linarith) hA h2 (Or.inl hdp)).resolve_right ns1
      omega
    have hA' : 0 < a + d + d := lt_of_le_of_ne hA n2.symm
    rcases lt_or_ge (a + d) 0 with hB | hB
    · have e0 := (step_neg t hu hd (by linarith) hB h1 (Or.inl hdp)).resolve_right ns0
      have o := opp_neg_pos t hB hA' h2
      have e2 := (step_pos t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega
    have hB' : 0 < a + d := lt_of_le_of_ne hB n1.symm
    rcases lt_or_ge a 0 with hC | hC
    · have o := opp_neg_pos t hC hB' h1
      have e1 := (step_pos t hu hd hB' hA' h2 (Or.inr (by linarith))).resolve_right ns1
      have e2 := (step_pos t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega
    · have e1 := (step_pos t hu hd hB' hA' h2 (Or.inr (by linarith))).resolve_right ns1
      have e2 := (step_pos t hu hd hA' (by linarith) h3 (Or.inr (by linarith))).resolve_right ns2
      omega

/-- Every monotone 4-term AP of `E t` has a seam: some stage `s` with `2 ^ t (s+1) ∣ d`, and
the first term and the difference are bounded in terms of `s`. -/
theorem exists_seam {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l) {a d : ℤ}
    (hd : d ≠ 0) (h : E t i = a ∧ E t j = a + d ∧ E t k = a + 2 * d ∧ E t l = a + 3 * d) :
    ∃ s : ℕ, (2 : ℤ) ^ t (s + 1) ∣ d ∧ |a| < 9 * 3 ^ L t (s + 1) ∧
      |d| < 4 * 3 ^ L t (s + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have c1 := rank_E_lt t hij
  have c2 := rank_E_lt t hjk
  have c3 := rank_E_lt t hkl
  rw [h1, h2] at c1
  rw [h2, h3, show a + 2 * d = a + d + d by ring] at c2
  rw [h3, h4, show a + 2 * d = a + d + d by ring, show a + 3 * d = a + d + d + d by ring] at c3
  rcases core t hd c1 c2 c3 with ⟨s, hs, hx, hdd⟩ | ⟨s, hs, hx, hdd⟩ | ⟨s, hs, hx, hdd⟩ <;>
  · refine ⟨s, hs, ?_, hdd⟩
    rw [abs_lt] at hx hdd ⊢
    constructor <;> linarith

/-! ### The two theorems -/

/-- Theorem G: for constant `t` there is no monotone 4-term AP with `2 ^ t ∤ d`. -/
theorem exists_enum_no_ap :
    ∀ t : ℕ, 1 ≤ t → ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ,
      ¬ ((2 : ℤ) ^ t ∣ d) → ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) := by
  intro t0 _
  refine ⟨E (fun _ => t0), fun i j k l hij hjk hkl a d hd h => ?_⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (dvd_zero _)
  obtain ⟨s, hs, -, -⟩ := exists_seam (fun _ => t0) hij hjk hkl hd0 h
  exact hd hs

/-- Theorem H with `t s = s + 1`: for every `v`, only finitely many monotone 4-term APs
`(a, a + d, a + 2d, a + 3d)` of one enumeration have `ν₂(d) = v`. -/
theorem exists_enum_finite :
    ∃ f : ℕ ≃ ℤ, ∀ v : ℕ, Set.Finite {p : ℤ × ℤ | p.2 ≠ 0 ∧ padicValInt 2 p.2 = v ∧
      ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ f i = p.1 ∧ f j = p.1 + p.2 ∧
        f k = p.1 + 2 * p.2 ∧ f l = p.1 + 3 * p.2} := by
  refine ⟨E (fun s => s + 1), fun v => ?_⟩
  refine (Set.Finite.prod (Set.finite_Icc (-(9 * 3 ^ L (fun s => s + 1) v))
    (9 * 3 ^ L (fun s => s + 1) v)) (Set.finite_Icc (-(9 * 3 ^ L (fun s => s + 1) v))
    (9 * 3 ^ L (fun s => s + 1) v))).subset ?_
  rintro ⟨a, d⟩ ⟨hd0, hv, i, j, k, l, hij, hjk, hkl, h⟩
  obtain ⟨s, hs, ha, hdd⟩ := exists_seam (fun s => s + 1) hij hjk hkl hd0 h
  have hsv : s + 2 ≤ v := by
    have hs' : ((2 : ℕ) : ℤ) ^ (s + 2) ∣ d := by exact_mod_cast hs
    rcases (padicValInt_dvd_iff (p := 2) (s + 2) d).mp hs' with h0 | h0
    · exact absurd h0 hd0
    · rw [← hv]
      exact h0
  have hL : (3 : ℤ) ^ L (fun s => s + 1) (s + 1) ≤ 3 ^ L (fun s => s + 1) v :=
    pow_le_pow_right₀ (by norm_num) (L_mono _ (by omega))
  simp only [Set.mem_prod, Set.mem_Icc]
  rw [abs_lt] at ha hdd
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The permutation `E (fun s => s + 1)` of Theorem H has no monotone 4-term AP with `4 ∤ d`:
every seam there has `2 ^ (s + 2) ∣ d`. -/
theorem E_main_four_dvd {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l) {a d : ℤ}
    (hd : ¬ (4 : ℤ) ∣ d) :
    ¬ (E (fun s => s + 1) i = a ∧ E (fun s => s + 1) j = a + d ∧
      E (fun s => s + 1) k = a + 2 * d ∧ E (fun s => s + 1) l = a + 3 * d) := by
  intro h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (dvd_zero _)
  obtain ⟨s, hs, -, -⟩ := exists_seam (fun s => s + 1) hij hjk hkl hd0 h
  exact hd ((pow_dvd_pow 2 (show 2 ≤ s + 1 + 1 by omega)).trans hs)

/-! ### A seam progression (non-vacuity) -/

/-- In the enumeration `E (fun _ => 1)` of Theorem G with `t = 1`, the progression
`0, -6, -12, -18` (difference `-6`, divisible by `2`) appears in this order: a seam progression,
as predicted by Prop. 2 of the write-up. -/
theorem seam_example :
    rank (fun _ => 1) 0 < rank (fun _ => 1) (-6) ∧
      rank (fun _ => 1) (-6) < rank (fun _ => 1) (-12) ∧
      rank (fun _ => 1) (-12) < rank (fun _ => 1) (-18) := by
  have hL0 : L (fun _ => 1) 0 = 0 := by simp [L]
  have hL1 : L (fun _ => 1) 1 = 4 := by simp [L]
  have hr6 : rho 1 (-6) = 0 := by simp [rho]
  have hr12 : rho 1 (-12) = 0 := by simp [rho]
  have hr18 : rho 1 (-18) = 0 := by simp [rho]
  have t6 : top (fun _ => 1) 0 (-6) = 2 := by
    simp only [top, show (-6 : ℤ) < 0 by norm_num, ↓reduceIte, hL0, hr6]
    norm_num
  have t12 : top (fun _ => 1) 0 (-12) = 2 := by
    simp only [top, show (-12 : ℤ) < 0 by norm_num, ↓reduceIte, hL0, hr12]
    norm_num
  have t12' : top (fun _ => 1) 1 (-12) = 6 := by
    simp only [top, show (-12 : ℤ) < 0 by norm_num, ↓reduceIte, hL1, hr12]
    norm_num
  have t18 : top (fun _ => 1) 0 (-18) = 2 := by
    simp only [top, show (-18 : ℤ) < 0 by norm_num, ↓reduceIte, hL0, hr18]
    norm_num
  have t18' : top (fun _ => 1) 1 (-18) = 6 := by
    simp only [top, show (-18 : ℤ) < 0 by norm_num, ↓reduceIte, hL1, hr18]
    norm_num
  have s6 : stage (fun _ => 1) (-6) = 0 := by
    rw [stage, Nat.find_eq_zero, t6]
    norm_num
  have s12 : stage (fun _ => 1) (-12) = 1 := by
    rw [stage, Nat.find_eq_iff]
    refine ⟨by rw [t12']; norm_num, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [t12]
    norm_num
  have s18 : stage (fun _ => 1) (-18) = 1 := by
    rw [stage, Nat.find_eq_iff]
    refine ⟨by rw [t18']; norm_num, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [t18]
    norm_num
  refine ⟨?_, rank_lt_of_stage_lt _ (by norm_num) (by norm_num) (by rw [s6, s12]; norm_num), ?_⟩
  · rw [rank_zero]
    exact Nat.pos_of_ne_zero fun h => by
      have := rank_bounds (fun _ => 1) (x := -6) (by norm_num)
      omega
  · rw [rank_of_neg _ (by norm_num : (-12 : ℤ) < 0), rank_of_neg _ (by norm_num : (-18 : ℤ) < 0),
      s12, s18]
    have hN : NN (fun _ => 1) 1 = 16 := by simp [NN, L]
    have hb : bit 1 (-12) = 0 := by simp [bit]
    have := (rho_cmp (NN (fun _ => 1) 1) 1 (by rw [hN]; norm_num) (-12) (-3) (by norm_num)).1 hb
    norm_num at this
    omega

/-- In the enumeration `E (fun s => s + 1)` of Theorem H, the progression `0, -44, -88, -132`
(difference `-44`, `ν₂ = 2`) appears in this order: the enumeration of `exists_enum_finite` is not
free of monotone 4-term progressions. -/
theorem seam_example_main :
    rank (fun s => s + 1) 0 < rank (fun s => s + 1) (-44) ∧
      rank (fun s => s + 1) (-44) < rank (fun s => s + 1) (-88) ∧
      rank (fun s => s + 1) (-88) < rank (fun s => s + 1) (-132) := by
  have hL0 : L (fun s => s + 1) 0 = 0 := by simp [L]
  have hL1 : L (fun s => s + 1) 1 = 8 := by simp [L]
  have r44 : rho 2 (-44) = 0 := by simp [rho]
  have r88 : rho 2 (-88) = 0 := by simp [rho]
  have r132 : rho 2 (-132) = 0 := by simp [rho]
  have r88' : rho 3 (-88) = 0 := by simp [rho]
  have r132' : rho 3 (-132) = 1 := by simp [rho]
  have t44 : top (fun s => s + 1) 0 (-44) = 4 := by simp [top, hL0, r44]
  have t88 : top (fun s => s + 1) 0 (-88) = 4 := by simp [top, hL0, r88]
  have t88' : top (fun s => s + 1) 1 (-88) = 16 := by simp [top, hL1, r88']
  have t132 : top (fun s => s + 1) 0 (-132) = 4 := by simp [top, hL0, r132]
  have t132' : top (fun s => s + 1) 1 (-132) = 15 := by simp [top, hL1, r132']
  have s44 : stage (fun s => s + 1) (-44) = 0 := by
    rw [stage, Nat.find_eq_zero, t44]
    norm_num
  have s88 : stage (fun s => s + 1) (-88) = 1 := by
    rw [stage, Nat.find_eq_iff]
    refine ⟨by rw [t88']; norm_num, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [t88]
    norm_num
  have s132 : stage (fun s => s + 1) (-132) = 1 := by
    rw [stage, Nat.find_eq_iff]
    refine ⟨by rw [t132']; norm_num, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [t132]
    norm_num
  refine ⟨?_, rank_lt_of_stage_lt _ (by norm_num) (by norm_num) (by rw [s44, s88]; norm_num), ?_⟩
  · rw [rank_zero]
    exact Nat.pos_of_ne_zero fun h => by
      have := rank_bounds (fun s => s + 1) (x := -44) (by norm_num)
      omega
  · rw [rank_of_neg _ (by norm_num : (-88 : ℤ) < 0), rank_of_neg _ (by norm_num : (-132 : ℤ) < 0),
      s88, s132]
    have hN : NN (fun s => s + 1) 1 = 48 := by simp [NN, L]
    have hb : bit 2 (-88) = 0 := by simp [bit]
    have := (rho_cmp (NN (fun s => s + 1) 1) 2 (by rw [hN]; norm_num) (-88) (-11) (by norm_num)).1 hb
    norm_num at this
    omega

end Erdos195Bands
