import HighamTridiagonal.Inverse

/-!
# Theorem 3.3

*If the nonsingular tridiagonal matrix `A ∈ ℝ^{n×n}` has the LU factorization `A = LU` and
`|L||U| = |A|`, then `|U⁻¹||L⁻¹| = |A⁻¹|`.*

Here `|·|` is the entrywise absolute value (`M.map abs`).
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- If the terms of a finite sum all have the same sign, the absolute value of the sum is the
sum of the absolute values. -/
lemma abs_sum_eq_sum_abs_of_sign {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (h : (∀ k ∈ s, 0 ≤ t k) ∨ (∀ k ∈ s, t k ≤ 0)) : |∑ k ∈ s, t k| = ∑ k ∈ s, |t k| := by
  rcases h with h | h
  · rw [abs_of_nonneg (Finset.sum_nonneg h)]
    exact Finset.sum_congr rfl fun k hk => (abs_of_nonneg (h k hk)).symm
  · rw [abs_of_nonpos (Finset.sum_nonpos h), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k hk => (abs_of_nonpos (h k hk)).symm

/-- The key computation in the proof of Theorem 3.3: under the sign condition (3.5), for fixed
`i, j` the terms `(U⁻¹)_{ik} (L⁻¹)_{kj}` all have the same sign. -/
lemma inv_terms_same_sign (l p e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0)
    (hs : ∀ i, i + 1 < n → 0 ≤ l (i + 1) * e i * p (i + 1)) (i j : ℕ) (hi : i < n) (hj : j < n) :
    (∀ k, 0 ≤ ent (upperBidiag (n := n) p e)⁻¹ i k * ent (lowerBidiag (n := n) l)⁻¹ k j) ∨
      (∀ k, ent (upperBidiag (n := n) p e)⁻¹ i k * ent (lowerBidiag (n := n) l)⁻¹ k j ≤ 0) := by
  set T : ℕ → ℝ := fun k => ent (upperBidiag (n := n) p e)⁻¹ i k *
    ent (lowerBidiag (n := n) l)⁻¹ k j with hT
  set m := max i j with hm
  -- terms before `max i j` vanish
  have hzero : ∀ k, k < m → T k = 0 := by
    intro k hk
    simp only [hT]
    rcases lt_max_iff.mp hk with h | h
    · rw [ent_inv_upperBidiag_of_lt e hp h, zero_mul]
    · rw [ent_inv_lowerBidiag_of_lt l h, mul_zero]
  -- terms after `n` vanish
  have hbig : ∀ k, n ≤ k → T k = 0 := by
    intro k hk
    simp only [hT]
    rw [ent_of_not_lt_right _ (by omega), zero_mul]
  -- the ratio of consecutive terms is nonnegative
  have hstep : ∀ k, m ≤ k → k + 1 < n →
      T (k + 1) = T k * (e k * l (k + 1) / p (k + 1)) := by
    intro k hk hk1
    simp only [hT]
    rw [ent_inv_upperBidiag_succ e hp (le_of_max_le_left hk) hk1,
      ent_inv_lowerBidiag_succ l (le_of_max_le_right hk) hk1]
    have := hp (k + 1) hk1
    field_simp
  have hratio : ∀ k, k + 1 < n → 0 ≤ e k * l (k + 1) / p (k + 1) := by
    intro k hk
    have h1 := hs k hk
    have h2 : e k * l (k + 1) / p (k + 1) = l (k + 1) * e k * p (k + 1) / p (k + 1) ^ 2 := by
      have := hp (k + 1) hk
      field_simp
    rw [h2]
    exact div_nonneg h1 (sq_nonneg _)
  have hmn : m < n := max_lt hi hj
  rcases le_total 0 (T m) with h0 | h0
  · left
    intro k
    show 0 ≤ T k
    rcases lt_or_ge k m with hk | hk
    · rw [hzero k hk]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction d with
    | zero => simpa using h0
    | succ d ih =>
      by_cases hd : m + d + 1 < n
      · rw [← add_assoc, hstep (m + d) (by omega) hd]
        exact mul_nonneg (ih (by omega)) (hratio _ hd)
      · rw [hbig _ (by omega)]
  · right
    intro k
    show T k ≤ 0
    rcases lt_or_ge k m with hk | hk
    · rw [hzero k hk]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction d with
    | zero => simpa using h0
    | succ d ih =>
      by_cases hd : m + d + 1 < n
      · rw [← add_assoc, hstep (m + d) (by omega) hd]
        exact mul_nonpos_of_nonpos_of_nonneg (ih (by omega)) (hratio _ hd)
      · rw [hbig _ (by omega)]

/-- **Theorem 3.3.** If the nonsingular tridiagonal matrix `A` has the LU factorization `A = LU`
and `|L||U| = |A|`, then `|U⁻¹||L⁻¹| = |A⁻¹|`. -/
theorem theorem_3_3 (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (habs : L.map abs * U.map abs = A.map abs) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  -- the sign condition (3.5)
  have hs : ∀ i, i + 1 < n → 0 ≤ mult A (i + 1) * supd A i * piv A (i + 1) := by
    rw [← abs_mul_abs_eq_abs_mul_iff, ← hL, ← hU, ← hLU.eq]
    exact habs
  have hAinv : A⁻¹ = U⁻¹ * L⁻¹ := by rw [hLU.eq, Matrix.mul_inv_rev]
  ext i j
  rw [hAinv, map_apply, mul_apply, mul_apply]
  simp only [map_apply, ← abs_mul]
  symm
  apply abs_sum_eq_sum_abs_of_sign
  rcases inv_terms_same_sign (mult A) (piv A) (supd A) hp hs i j i.2 j.2 with h | h
  · left
    intro k _
    have := h k
    rw [hL, hU]
    simpa using this
  · right
    intro k _
    have := h k
    rw [hL, hU]
    simpa using this

end Higham
