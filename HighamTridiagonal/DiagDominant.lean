import HighamTridiagonal.Inverse

/-!
# Section 4: diagonally dominant tridiagonal matrices

* **Theorem 4.1.** If `A` is nonsingular, tridiagonal and diagonally dominant by rows or columns,
  and `A = LU`, then `|L||U| ≤ 3|A|`.
* **Theorem 4.2.** If `A` is nonsingular, row diagonally dominant and tridiagonal with
  `A = LU`, then for `y ≥ 0`, `‖ |U⁻¹||L⁻¹| y ‖_∞ ≤ (2n-1) ‖ |A⁻¹| y ‖_∞`.

The `∞`-norm of a vector `v : Fin n → ℝ` is Mathlib's sup norm `‖v‖ = max_i |v_i|`.
We also formalize the (unnumbered) column-dominant analogue of Theorem 4.2 stated after it.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- `A` is diagonally dominant by rows: `|a_ii| ≥ ∑_{j ≠ i} |a_ij|` for every `i`.
(For tridiagonal `A` this is the paper's condition `|d_i| ≥ |c_i| + |e_i|`, see
`isRowDiagDominant_iff_of_isTridiagonal`.) -/
def IsRowDiagDominant (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i|

/-- `A` is diagonally dominant by columns if `Aᵀ` is diagonally dominant by rows. -/
def IsColDiagDominant (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRowDiagDominant Aᵀ

/-- From row diagonal dominance: two distinct off-diagonal entries of row `i` are dominated by
the diagonal entry. -/
lemma IsRowDiagDominant.two_le {A : Matrix (Fin n) (Fin n) ℝ} (h : IsRowDiagDominant A)
    {i j₁ j₂ : ℕ} (hi : i < n) (h₁ : j₁ ≠ i) (h₂ : j₂ ≠ i) (h₁₂ : j₁ ≠ j₂) :
    |ent A i j₁| + |ent A i j₂| ≤ |ent A i i| := by
  have hrow := h ⟨i, hi⟩
  rw [ent_of_lt A hi hi]
  have hnn : ∀ j ∈ Finset.univ.erase (⟨i, hi⟩ : Fin n), 0 ≤ |A ⟨i, hi⟩ j| :=
    fun _ _ => abs_nonneg _
  by_cases hj₁ : j₁ < n <;> by_cases hj₂ : j₂ < n
  · rw [ent_of_lt A hi hj₁, ent_of_lt A hi hj₂]
    have hsub : ({⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩} : Finset (Fin n)) ⊆ Finset.univ.erase ⟨i, hi⟩ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [Fin.ext_iff, h₁, h₂]
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnn j hj)
    rw [Finset.sum_pair (by simp [Fin.ext_iff, h₁₂])] at this
    linarith
  · rw [ent_of_lt A hi hj₁, ent_of_not_lt_right A hj₂, abs_zero, add_zero]
    exact le_trans (Finset.single_le_sum hnn (by simp [Fin.ext_iff, h₁])) hrow
  · rw [ent_of_not_lt_right A hj₁, ent_of_lt A hi hj₂, abs_zero, zero_add]
    exact le_trans (Finset.single_le_sum hnn (by simp [Fin.ext_iff, h₂])) hrow
  · rw [ent_of_not_lt_right A hj₁, ent_of_not_lt_right A hj₂, abs_zero, add_zero]
    exact abs_nonneg _

/-- Sanity check: for tridiagonal matrices, row diagonal dominance is exactly the paper's
condition `|d_i| ≥ |c_i| + |e_i|` (with `c_1 = e_n = 0`). -/
theorem isRowDiagDominant_iff_of_isTridiagonal {A : Matrix (Fin n) (Fin n) ℝ}
    (hT : IsTridiagonal A) :
    IsRowDiagDominant A ↔ ∀ i, i < n →
      (if i = 0 then 0 else |ent A i (i - 1)|) + |ent A i (i + 1)| ≤ |ent A i i| := by
  constructor
  · intro h i hi
    split_ifs with h0
    · subst h0
      have := h.two_le (j₁ := 1) (j₂ := 2) hi (by omega) (by omega) (by omega)
      have h2 : ent A 0 2 = 0 := hT.ent_eq_zero (by omega)
      rw [h2, abs_zero, add_zero] at this
      simpa using this
    · exact h.two_le hi (by omega) (by omega) (by omega)
  · intro h i
    have hi := h i i.2
    have hsum : ∑ j ∈ Finset.univ.erase i, |A i j| =
        ∑ j ∈ Finset.univ.erase i, (if (j : ℕ) + 1 = i ∨ (j : ℕ) = i + 1 then |A i j| else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      split_ifs with hc
      · rfl
      · have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i := by
          have : (j : ℕ) ≠ i := fun h' => hji (Fin.ext h')
          omega
        rw [hT i j this, abs_zero]
    rw [hsum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    calc ∑ j ∈ (Finset.univ.erase i).filter (fun j : Fin n => (j : ℕ) + 1 = i ∨ (j : ℕ) = i + 1),
          |A i j|
        ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin n => (j : ℕ) + 1 = i)) ∪
            (Finset.univ.filter (fun j : Fin n => (j : ℕ) = i + 1)), |A i j| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ] at hj
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hj.2
          · intro _ _ _; exact abs_nonneg _
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) + 1 = i), |A i j| +
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) = i + 1), |A i j| := by
          apply Finset.sum_union
          rw [Finset.disjoint_filter]
          intro j _ h1 h2
          omega
      _ ≤ (if (i : ℕ) = 0 then 0 else |ent A i (i - 1)|) + |ent A i (i + 1)| := by
          gcongr
          · split_ifs with h0
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              omega
            · apply le_of_eq
              rw [Finset.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩]
              · rw [ent_of_lt A i.2 (by omega)]
              · intro j hj hne
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                exact absurd (Fin.ext (by simp; omega)) hne
              · intro hnot
                exact absurd (by simp; omega) hnot
          · by_cases hi1 : (i : ℕ) + 1 < n
            · apply le_of_eq
              rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, hi1⟩]
              · rw [ent_of_lt A i.2 hi1]
              · intro j hj hne
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
                exact absurd (Fin.ext hj) hne
              · intro hnot
                exact absurd (by simp) hnot
            · apply le_of_eq
              rw [ent_of_not_lt_right A hi1, abs_zero]
              apply Finset.sum_eq_zero
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              omega
      _ ≤ |A i i| := by simpa using hi

/-! ### Bounds on the LU factors -/

section Factors

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- Row diagonal dominance: `|e_k| ≤ |u_k|` for all `k`, as claimed in the proof of
Theorem 4.1 (with the convention `e_{n} = 0`). -/
lemma rowDD_abs_supd_le_abs_piv (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A)
    (hp : ∀ i, i < n → piv A i ≠ 0) : ∀ k, k < n → |supd A k| ≤ |piv A k| := by
  intro k
  induction k with
  | zero =>
    intro hk
    have := hDD.two_le (j₁ := 1) (j₂ := 2) hk (by omega) (by omega) (by omega)
    have h2 : ent A 0 2 = 0 := hT.ent_eq_zero (by omega)
    rw [h2, abs_zero, add_zero] at this
    simpa [supd] using this
  | succ k ih =>
    intro hk
    have hk' := ih (by omega)
    have hpk := hp k (by omega)
    have hdd := hDD.two_le (j₁ := k) (j₂ := k + 2) hk (by omega) (by omega) (by omega)
    -- `|l_{k+1} e_k| ≤ |c_{k+1}|`
    have hle : |mult A (k + 1) * ent A k (k + 1)| ≤ |ent A (k + 1) k| := by
      rw [mult_succ, abs_mul, abs_div]
      have hpos : 0 < |piv A k| := abs_pos.mpr hpk
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left (by simpa [supd] using hk') (abs_nonneg _)
    have : |piv A (k + 1)| ≥ |ent A (k + 1) (k + 1)| - |mult A (k + 1) * ent A k (k + 1)| := by
      rw [piv_succ]
      have := abs_sub_abs_le_abs_sub (ent A (k + 1) (k + 1)) (mult A (k + 1) * ent A k (k + 1))
      linarith
    simp only [supd]
    linarith

/-- Column diagonal dominance: `|c_{k+1}| ≤ |u_k|`, i.e. `|l_{k+1}| ≤ 1`. -/
lemma colDD_abs_sub_le_abs_piv (hT : IsTridiagonal A) (hDD : IsColDiagDominant A)
    (hp : ∀ i, i < n → piv A i ≠ 0) : ∀ k, k + 1 < n → |ent A (k + 1) k| ≤ |piv A k| := by
  intro k
  induction k with
  | zero =>
    intro hk
    have := hDD.two_le (j₁ := 1) (j₂ := 2) (by omega : 0 < n) (by omega) (by omega) (by omega)
    simp only [ent_transpose] at this
    have h2 : ent A 2 0 = 0 := hT.ent_eq_zero (by omega)
    rw [h2, abs_zero, add_zero] at this
    simpa using this
  | succ k ih =>
    intro hk
    have hk' := ih (by omega)
    have hpk := hp k (by omega)
    have hdd := hDD.two_le (j₁ := k) (j₂ := k + 2) (by omega : k + 1 < n) (by omega) (by omega)
      (by omega)
    simp only [ent_transpose] at hdd
    have hle : |mult A (k + 1) * ent A k (k + 1)| ≤ |ent A k (k + 1)| := by
      rw [mult_succ, abs_mul, abs_div]
      have hpos : 0 < |piv A k| := abs_pos.mpr hpk
      have : |ent A (k + 1) k| / |piv A k| ≤ 1 := (div_le_one hpos).mpr hk'
      calc |ent A (k + 1) k| / |piv A k| * |ent A k (k + 1)| ≤ 1 * |ent A k (k + 1)| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = _ := one_mul _
    have : |piv A (k + 1)| ≥ |ent A (k + 1) (k + 1)| - |mult A (k + 1) * ent A k (k + 1)| := by
      rw [piv_succ]
      have := abs_sub_abs_le_abs_sub (ent A (k + 1) (k + 1)) (mult A (k + 1) * ent A k (k + 1))
      linarith
    linarith

/-- The diagonal bound `|l_{k+1} e_k| + |u_{k+1}| ≤ 3 |d_{k+1}|` from the proof of Theorem 4.1. -/
lemma diag_bound (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A ∨ IsColDiagDominant A)
    (hp : ∀ i, i < n → piv A i ≠ 0) {k : ℕ} (hk : k + 1 < n) :
    |mult A (k + 1)| * |supd A k| + |piv A (k + 1)| ≤ 3 * |ent A (k + 1) (k + 1)| := by
  have hpk := hp k (by omega)
  have hpos : 0 < |piv A k| := abs_pos.mpr hpk
  have hup : |piv A (k + 1)| ≤ |ent A (k + 1) (k + 1)| + |mult A (k + 1) * ent A k (k + 1)| := by
    rw [piv_succ]; exact abs_sub _ _
  rw [← abs_mul]
  rcases hDD with hR | hC
  · have hk' := rowDD_abs_supd_le_abs_piv hT hR hp k (by omega)
    have hdd := hR.two_le (j₁ := k) (j₂ := k + 2) hk (by omega) (by omega) (by omega)
    have hle : |mult A (k + 1) * ent A k (k + 1)| ≤ |ent A (k + 1) k| := by
      rw [mult_succ, abs_mul, abs_div, div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left (by simpa [supd] using hk') (abs_nonneg _)
    have h0 : 0 ≤ |ent A (k + 1) (k + 2)| := abs_nonneg _
    simp only [supd] at *
    linarith
  · have hk' := colDD_abs_sub_le_abs_piv hT hC hp k hk
    have hdd := hC.two_le (j₁ := k) (j₂ := k + 2) (by omega : k + 1 < n) (by omega) (by omega)
      (by omega)
    simp only [ent_transpose] at hdd
    have hle : |mult A (k + 1) * ent A k (k + 1)| ≤ |ent A k (k + 1)| := by
      rw [mult_succ, abs_mul, abs_div]
      have : |ent A (k + 1) k| / |piv A k| ≤ 1 := (div_le_one hpos).mpr hk'
      calc |ent A (k + 1) k| / |piv A k| * |ent A k (k + 1)| ≤ 1 * |ent A k (k + 1)| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = _ := one_mul _
    have h0 : 0 ≤ |ent A (k + 2) (k + 1)| := abs_nonneg _
    simp only [supd] at *
    linarith

end Factors

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1.** Suppose `A ∈ ℝ^{n×n}` is nonsingular, tridiagonal, and diagonally dominant
by rows or columns, and let `A` have the LU factorization `A = LU`. Then `|L||U| ≤ 3|A|`
(entrywise). -/
theorem theorem_4_1 (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A ∨ IsColDiagDominant A)
    (hLU : IsLU A L U) :
    ∀ i j, (L.map abs * U.map abs) i j ≤ 3 * |A i j| := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  have hAeq : A = lowerBidiag (mult A) * upperBidiag (piv A) (supd A) := by
    rw [← hL, ← hU]; exact hLU.eq
  rw [hL, hU, lowerBidiag_map_abs, upperBidiag_map_abs]
  intro i j
  suffices h : ent (lowerBidiag (n := n) (fun i => |mult A i|) *
      upperBidiag (fun i => |piv A i|) (fun i => |supd A i|)) i j ≤ 3 * |ent A i j| by
    simpa using h
  have hi := i.2
  have hj := j.2
  rcases lt_trichotomy ((i : ℕ) + 1) j with h | h | h
  · rw [(isTridiagonal_LU _ _ _).ent_eq_zero (Or.inl h)]
    positivity
  · rw [← h, ent_LU_sup _ _ _ (by omega)]
    simp only [supd]
    linarith [abs_nonneg (ent A i (i + 1))]
  rcases lt_trichotomy ((j : ℕ) + 1) i with h' | h' | h'
  · rw [(isTridiagonal_LU _ _ _).ent_eq_zero (Or.inr h')]
    positivity
  · rw [← h', ent_LU_sub _ _ _ (by omega), ← abs_mul,
      show mult A (j + 1) * piv A j = ent A (j + 1) j by
        rw [mult_succ, div_mul_cancel₀ _ (hp j hj)]]
    linarith [abs_nonneg (ent A (j + 1) j)]
  · have hij : (i : ℕ) = j := by omega
    rw [← hij]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, ent_LU_zero_zero _ _ _ (by omega), piv_zero]
      linarith [abs_nonneg (ent A 0 0)]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h0
      simp only [zero_add] at hk
      rw [hk, ent_LU_diag_succ _ _ _ (by omega)]
      have := diag_bound hT hDD hp (k := k) (by omega)
      simpa [supd] using this

/-! ### Theorem 4.2 -/

lemma mulVec_mono_of_nonneg {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {v w : Fin n → ℝ} (hvw : ∀ i, v i ≤ w i) (i : Fin n) : (M *ᵥ v) i ≤ (M *ᵥ w) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvw j) (hM i j)

lemma mulVec_nonneg_of_nonneg {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j)
    {v : Fin n → ℝ} (hv : ∀ i, 0 ≤ v i) (i : Fin n) : 0 ≤ (M *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hM i j) (hv j)

lemma sum_ite_one_two (i : Fin n) :
    ∑ q : Fin n, (if q = i then (1 : ℝ) else 2) = 2 * n - 1 := by
  have : ∀ q : Fin n, (if q = i then (1 : ℝ) else 2) = 2 - (if q = i then 1 else 0) := by
    intro q; split_ifs <;> norm_num
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, nsmul_eq_mul]
  ring

/-- Bound on `|U⁻¹||U|` used in the proof of Theorem 4.2 (equivalently `|V⁻¹||V|` with
`V = diag(u_ii)⁻¹ U`). -/
lemma abs_inv_U_mul_abs_U_le {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hDD : IsRowDiagDominant A) (hp : ∀ i, i < n → piv A i ≠ 0) (i q : Fin n) :
    ((upperBidiag (n := n) (piv A) (supd A))⁻¹.map abs *
      (upperBidiag (n := n) (piv A) (supd A)).map abs : Matrix (Fin n) (Fin n) ℝ)
      i q ≤ if q = i then 1 else 2 := by
  have hed := rowDD_abs_supd_le_abs_piv hT hDD hp
  -- `|(U⁻¹)_{ik}| |u_k| ≤ 1`
  have hkey : ∀ k, k < n →
      |ent (upperBidiag (n := n) (piv A) (supd A))⁻¹ i k| * |piv A k| ≤ 1 := by
    intro k hk
    rcases lt_or_ge k i with hki | hki
    · rw [ent_inv_upperBidiag_of_lt _ hp hki]; simp
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
    induction d with
    | zero =>
      simp only [add_zero] at hk ⊢
      rw [ent_inv_upperBidiag_diag _ hp hk, abs_inv,
        inv_mul_cancel₀ (abs_pos.mpr (hp i hk)).ne']
    | succ d ih =>
      rw [← add_assoc] at hk ⊢
      rw [ent_inv_upperBidiag_succ _ hp (by omega) hk, abs_div, abs_neg, abs_mul,
        div_mul_cancel₀ _ (abs_pos.mpr (hp _ hk)).ne']
      calc |ent (upperBidiag (n := n) (piv A) (supd A))⁻¹ i (i + d)| * |supd A (i + d)|
          ≤ |ent (upperBidiag (n := n) (piv A) (supd A))⁻¹ i (i + d)| * |piv A (i + d)| :=
            mul_le_mul_of_nonneg_left (hed _ (by omega)) (abs_nonneg _)
        _ ≤ 1 := ih (by omega) (by omega)
  rw [upperBidiag_map_abs]
  suffices h : ent ((upperBidiag (n := n) (piv A) (supd A))⁻¹.map abs *
      upperBidiag (fun i => |piv A i|) (fun i => |supd A i|)) i q ≤ if q = i then 1 else 2 by
    simpa using h
  have hq := q.2
  rcases Nat.eq_zero_or_pos (q : ℕ) with h0 | h0
  · rw [h0, ent_mul_upperBidiag_zero, ent_abs]
    split_ifs with hqi
    · exact hkey 0 (by omega)
    · exact (hkey 0 (by omega)).trans (by norm_num)
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h0
    simp only [zero_add] at hk
    rw [hk, ent_mul_upperBidiag_succ _ _ _ i.2 (by omega), ent_abs, ent_abs]
    have h1 : |ent (upperBidiag (n := n) (piv A) (supd A))⁻¹ i k| * |supd A k| ≤
        |ent (upperBidiag (n := n) (piv A) (supd A))⁻¹ i k| * |piv A k| :=
      mul_le_mul_of_nonneg_left (hed _ (by omega)) (abs_nonneg _)
    have h2 := hkey k (by omega)
    have h3 := hkey (k + 1) (by omega)
    split_ifs with hqi
    · have hki : k < i := by
        have : (q : ℕ) = i := by rw [hqi]
        omega
      rw [ent_inv_upperBidiag_of_lt _ hp hki, abs_zero, zero_mul, zero_add]
      exact h3
    · linarith

/-- **Theorem 4.2.** Suppose the nonsingular, row diagonally dominant, tridiagonal matrix
`A ∈ ℝ^{n×n}` has the LU factorization `A = LU`. Then, if `y ≥ 0`,
`‖ |U⁻¹||L⁻¹| y ‖_∞ ≤ (2n - 1) ‖ |A⁻¹| y ‖_∞`. -/
theorem theorem_4_2 (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hLU : IsLU A L U)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    ‖(U⁻¹.map abs * L⁻¹.map abs) *ᵥ y‖ ≤ (2 * n - 1) * ‖A⁻¹.map abs *ᵥ y‖ := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  set z := A⁻¹.map abs *ᵥ y with hz
  have hz0 : ∀ i, 0 ≤ z i := mulVec_nonneg_of_nonneg (fun _ _ => abs_nonneg _) hy
  -- `L⁻¹ = U A⁻¹`
  have hLinv : L⁻¹ = U * A⁻¹ := by
    rw [hLU.eq, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
      mul_nonsing_inv _ (hLU.isUnit_det_U hA), Matrix.one_mul]
  -- `|U⁻¹||L⁻¹| y ≤ (|U⁻¹||U|) (|A⁻¹| y)`
  have hstep : ∀ i, ((U⁻¹.map abs * L⁻¹.map abs) *ᵥ y) i ≤
      ((U⁻¹.map abs * U.map abs) *ᵥ z) i := by
    intro i
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    apply mulVec_mono_of_nonneg (fun _ _ => abs_nonneg _)
    intro k
    rw [hz, mulVec_mulVec]
    simp only [mulVec, dotProduct]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (hy j)
    rw [map_apply, hLinv]
    exact abs_mul_le_abs_mul_abs U A⁻¹ k j
  have hW := abs_inv_U_mul_abs_U_le hT hDD hp
  rw [← hU] at hW
  have hbound : ∀ i, ((U⁻¹.map abs * U.map abs) *ᵥ z) i ≤ (2 * n - 1) * ‖z‖ := by
    intro i
    simp only [mulVec, dotProduct]
    calc ∑ q, (U⁻¹.map abs * U.map abs) i q * z q
        ≤ ∑ q : Fin n, (if q = i then (1 : ℝ) else 2) * ‖z‖ := by
          apply Finset.sum_le_sum
          intro q _
          have hzq : z q ≤ ‖z‖ := (le_abs_self _).trans (by simpa using norm_le_pi_norm z q)
          have hWnn : 0 ≤ (U⁻¹.map abs * U.map abs) i q := by
            rw [mul_apply]
            exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
          calc (U⁻¹.map abs * U.map abs) i q * z q ≤ (U⁻¹.map abs * U.map abs) i q * ‖z‖ :=
                mul_le_mul_of_nonneg_left hzq hWnn
            _ ≤ (if q = i then (1 : ℝ) else 2) * ‖z‖ :=
                mul_le_mul_of_nonneg_right (hW i q) (norm_nonneg _)
      _ = (2 * n - 1) * ‖z‖ := by rw [← Finset.sum_mul, sum_ite_one_two]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim ((U⁻¹.map abs * L⁻¹.map abs) *ᵥ y) 0, Subsingleton.elim z 0]
    simp
  have hr : 0 ≤ (2 * (n : ℝ) - 1) * ‖z‖ := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_nonneg (by linarith) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  have hnn : 0 ≤ ((U⁻¹.map abs * L⁻¹.map abs) *ᵥ y) i :=
    mulVec_nonneg_of_nonneg (fun a b => by
      rw [mul_apply]; exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      hy i
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact (hstep i).trans (hbound i)

end Higham
