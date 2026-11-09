import HighamTridiagonal.Remarks

/-!
# Section 4: unnumbered claims about diagonally dominant tridiagonal matrices

This file formalizes two unnumbered claims of Section 4 of

  N. J. Higham, *Bounding the error in Gaussian elimination for tridiagonal systems*,
  SIAM J. Matrix Anal. Appl. 11 (1990), 521–530.

## Existence of the LU factorization (p. 526)

*"`A` in (2.1) is diagonally dominant by rows if `|d_i| ≥ |c_i| + |e_i|` for all `i`
(`c_1 = e_n = 0`), and diagonally dominant by columns if `Aᵀ` is diagonally dominant by rows.
Such `A` have an LU factorization."*

For a nonsingular tridiagonal `A` that is diagonally dominant by rows or by columns:
* `leadMinor_ne_zero_of_diagDominant`: all leading principal minors `D_0, …, D_n` are nonzero;
* `piv_ne_zero_of_diagDominant`: all pivots `u_0, …, u_{n-1}` of the recurrence (2.3) are
  nonzero;
* `exists_LU_of_diagDominant`: `A` has an LU factorization.

Proof: let `D_m` be the first vanishing leading principal minor. Then `1 ≤ m < n`, the pivots
`u_0, …, u_{m-2}` are nonzero and `u_{m-1} = 0`. Diagonal dominance gives `|e_{m-1}| ≤ |u_{m-1}|`
(rows) or `|c_m| ≤ |u_{m-1}|` (columns) as soon as the *previous* pivots are nonzero
(`rowDD_abs_supd_le_abs_piv_of_prev`, `colDD_abs_sub_le_abs_piv_of_prev`), hence `c_m e_{m-1} = 0`
and `D_{m+1} = d_m D_m - c_m e_{m-1} D_{m-1} = 0`. Two consecutive zeros propagate through the
three-term recurrence to `D_n = det A` (`leadMinor_eq_zero_of_consecutive`), a contradiction.

Nonsingularity, a standing hypothesis of Section 4 (Theorems 4.1 and 4.2), cannot be dropped:
`[1 1; 1 1]` is diagonally dominant by rows and by columns but has the zero pivot `u_1 = 0`
(`diagDominant_singular_piv_eq_zero_example`; it does have an LU factorization), and
`[0 0; 1 1]` is diagonally dominant by rows but has no LU factorization at all
(`rowDD_singular_no_LU_example`).

## Exactness of the bound of Theorem 4.2 (p. 527)

*"Moreover, the bound is exact if the row diagonally dominant `A` happens to be symmetric (so
that it is positive definite), nonnegative (that is, `A ≥ 0`, which implies it is totally
nonnegative), or an M-matrix."*

"The bound" is `|A⁻¹| y ≤ |U⁻¹||L⁻¹| y` (with `y = |A||x|`); it is exact for every `y` iff
`|U⁻¹||L⁻¹| = |A⁻¹|`. For a nonsingular, tridiagonal, row diagonally dominant `A`:
* `rowDD_nonneg_isTotallyNonneg`: if `A ≥ 0` then `A` is totally nonnegative. (Nonsingularity is
  not needed here: `isTotallyNonneg_of_rowDD_nonneg`.)
* `rowDD_symm_posDef`: if `A` is symmetric **with positive diagonal**, then `A` is positive
  definite. The paper's parenthetical "symmetric (so that it is positive definite)" tacitly
  assumes a positive diagonal: `rowDD_symm_not_posDef_example` shows that the symmetric, row
  diagonally dominant, nonsingular, tridiagonal matrix `[2 1; 1 -2]` is not positive definite
  and that the bound is *not* exact for it. (With a negative diagonal `-A` is positive definite
  and the bound is again exact: `rowDD_symm_neg_bound_exact`.) Nonsingularity is needed too:
  `rowDD_symm_singular_not_posDef_example`.
* `rowDD_symm_bound_exact`, `rowDD_nonneg_bound_exact`, `mMatrix_bound_exact`, and the combined
  statement `rowDD_bound_exact`: in each of the three cases every LU factorization `A = LU`
  satisfies `|U⁻¹||L⁻¹| = |A⁻¹|`, hence `|U⁻¹||L⁻¹| y = |A⁻¹| y` for every `y`. (For an M-matrix
  row diagonal dominance is not needed: this is Theorem 3.1 (c) combined with Theorem 3.3.)

As elsewhere in the project, `|M|` is `M.map abs`, indices are `0`-based, the subdiagonal,
diagonal and superdiagonal of `A` are `c_{i+1} = ent A (i+1) i`, `d_i = ent A i i` and
`e_i = ent A i (i+1) = supd A i`, and the pivots and multipliers are `piv A` and `mult A`.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-! ### Existence of the LU factorization of a diagonally dominant matrix -/

section Existence

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- Row diagonal dominance gives `|e_k| ≤ |u_k|` as soon as the *previous* pivots
`u_0, …, u_{k-1}` are nonzero (compare `rowDD_abs_supd_le_abs_piv`, which assumes all pivots
nonzero). -/
lemma rowDD_abs_supd_le_abs_piv_of_prev (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) :
    ∀ k, k < n → (∀ i, i < k → piv A i ≠ 0) → |supd A k| ≤ |piv A k| := by
  intro k
  induction k with
  | zero =>
    intro hk _
    have := hDD.two_le (j₁ := 1) (j₂ := 2) hk (by omega) (by omega) (by omega)
    have h2 : ent A 0 2 = 0 := hT.ent_eq_zero (by omega)
    rw [h2, abs_zero, add_zero] at this
    simpa [supd] using this
  | succ k ih =>
    intro hk hp
    have hk' := ih (by omega) fun i hi => hp i (by omega)
    have hpk := hp k (by omega)
    have hdd := hDD.two_le (j₁ := k) (j₂ := k + 2) hk (by omega) (by omega) (by omega)
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

/-- Column diagonal dominance gives `|c_{k+1}| ≤ |u_k|` as soon as the *previous* pivots
`u_0, …, u_{k-1}` are nonzero (compare `colDD_abs_sub_le_abs_piv`, which assumes all pivots
nonzero). -/
lemma colDD_abs_sub_le_abs_piv_of_prev (hT : IsTridiagonal A) (hDD : IsColDiagDominant A) :
    ∀ k, k + 1 < n → (∀ i, i < k → piv A i ≠ 0) → |ent A (k + 1) k| ≤ |piv A k| := by
  intro k
  induction k with
  | zero =>
    intro hk _
    have := hDD.two_le (j₁ := 1) (j₂ := 2) (by omega : 0 < n) (by omega) (by omega) (by omega)
    simp only [ent_transpose] at this
    have h2 : ent A 2 0 = 0 := hT.ent_eq_zero (by omega)
    rw [h2, abs_zero, add_zero] at this
    simpa using this
  | succ k ih =>
    intro hk hp
    have hk' := ih (by omega) fun i hi => hp i (by omega)
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

/-- For a tridiagonal matrix, two consecutive vanishing leading principal minors
`D_m = D_{m+1} = 0` force `D_k = 0` for all `k ≥ m` (three-term recurrence `leadMinor_succ_succ`;
compare the proof of `IsTotallyNonneg.leadMinor_pos`). -/
lemma leadMinor_eq_zero_of_consecutive (hT : IsTridiagonal A) {m : ℕ}
    (h0 : leadMinor A m = 0) (h1 : leadMinor A (m + 1) = 0) :
    ∀ k, m ≤ k → leadMinor A k = 0 := by
  have hprop : ∀ d, leadMinor A (m + d) = 0 ∧ leadMinor A (m + d + 1) = 0 := by
    intro d
    induction d with
    | zero => exact ⟨h0, h1⟩
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      rw [show m + (d + 1) + 1 = m + d + 2 by ring, leadMinor_succ_succ hT (m + d), ih.1, ih.2]
      ring
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (hprop d).1

/-- All leading principal minors `D_0, …, D_n` of a nonsingular tridiagonal matrix that is
diagonally dominant by rows or by columns are nonzero. -/
theorem leadMinor_ne_zero_of_diagDominant (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (hDD : IsRowDiagDominant A ∨ IsColDiagDominant A) : ∀ m, m ≤ n → leadMinor A m ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_forall, not_not] at hcon
  have hex : ∃ m, m ≤ n ∧ leadMinor A m = 0 := by
    obtain ⟨m, hm, h⟩ := hcon
    exact ⟨m, hm, h⟩
  -- the smallest `m` with `D_m = 0`
  obtain ⟨hmn, hm0⟩ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → leadMinor A j ≠ 0 := fun j hj h0 =>
    Nat.find_min hex hj ⟨by omega, h0⟩
  set m := Nat.find hex with hmdef
  have hm_ne0 : m ≠ 0 := by
    intro h; rw [h, leadMinor_zero] at hm0; exact one_ne_zero hm0
  have hm_nen : m ≠ n := by
    intro h; rw [h, leadMinor_self] at hm0; exact hA.ne_zero hm0
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_lt (Nat.pos_of_ne_zero hm_ne0)
  simp only [zero_add] at hm'
  rw [hm'] at hm0 hmn hm_nen hmin
  have hmn' : m' + 1 < n := lt_of_le_of_ne hmn hm_nen
  -- the pivots `u_0, …, u_{m'-1}` are nonzero and `u_{m'} = 0`
  have hprev : ∀ i, i < m' → piv A i ≠ 0 := by
    intro i hi h0
    have := piv_mul_leadMinor hT i fun j hj => hmin j (by omega)
    rw [h0, zero_mul] at this
    exact hmin (i + 1) (by omega) this.symm
  have hpm : piv A m' = 0 := by
    have := piv_mul_leadMinor hT m' fun j hj => hmin j (by omega)
    rw [hm0] at this
    exact (mul_eq_zero.mp this).resolve_right (hmin m' (by omega))
  -- hence `c_{m'+1} e_{m'} = 0`
  have hce : ent A (m' + 1) m' * ent A m' (m' + 1) = 0 := by
    rcases hDD with hR | hC
    · have := rowDD_abs_supd_le_abs_piv_of_prev hT hR m' (by omega) hprev
      rw [hpm, abs_zero, supd] at this
      rw [abs_nonpos_iff.mp this, mul_zero]
    · have := colDD_abs_sub_le_abs_piv_of_prev hT hC m' hmn' hprev
      rw [hpm, abs_zero] at this
      rw [abs_nonpos_iff.mp this, zero_mul]
  -- so `D_{m'+2} = 0` as well, and the zeros propagate to `D_n = det A`
  have hm2 : leadMinor A (m' + 1 + 1) = 0 := by
    rw [leadMinor_succ_succ hT m', hm0, hce]; ring
  have := leadMinor_eq_zero_of_consecutive hT hm0 hm2 n hmn
  rw [leadMinor_self] at this
  exact hA.ne_zero this

/-- **Section 4 (p. 526).** *A nonsingular tridiagonal matrix `A` that is diagonally dominant by
rows or by columns has nonzero pivots* `u_0, …, u_{n-1}` (recurrence (2.3)), so Gaussian
elimination without pivoting runs to completion.

Nonsingularity cannot be dropped: `[1 1; 1 1]` is tridiagonal and diagonally dominant by rows
and by columns, but its pivot `u_1` vanishes (`diagDominant_singular_piv_eq_zero_example`). -/
theorem piv_ne_zero_of_diagDominant (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A ∨ IsColDiagDominant A) :
    ∀ k, k < n → piv A k ≠ 0 := by
  intro k hk h0
  have hD := leadMinor_ne_zero_of_diagDominant hA hT hDD
  have := piv_mul_leadMinor hT k fun j hj => hD j (by omega)
  rw [h0, zero_mul] at this
  exact hD (k + 1) hk this.symm

/-- **Section 4 (p. 526).** *"`A` in (2.1) is diagonally dominant by rows if
`|d_i| ≥ |c_i| + |e_i|` … and diagonally dominant by columns if `Aᵀ` is diagonally dominant by
rows. Such `A` have an LU factorization."* As everywhere in Section 4 (Theorems 4.1 and 4.2),
`A` is nonsingular; the factorization is the one produced by the recurrence (2.3)
(`isLU_recurrence`), and it is the only one (`IsLU.unique`).

Nonsingularity cannot be dropped: `[0 0; 1 1]` is tridiagonal, singular and diagonally dominant
by rows, but has no LU factorization (`rowDD_singular_no_LU_example`). -/
theorem exists_LU_of_diagDominant (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A ∨ IsColDiagDominant A) :
    ∃ L U, IsLU A L U :=
  ⟨_, _, isLU_recurrence hT fun i hi => piv_ne_zero_of_diagDominant A hA hT hDD i (by omega)⟩

end Existence

/-! ### Singular diagonally dominant matrices: nonsingularity cannot be dropped -/

section SingularExamples

/-- The singular matrix `[1 1; 1 1]`, diagonally dominant by rows and by columns. -/
def ddOnes : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- The singular matrix `[0 0; 1 1]`, diagonally dominant by rows. -/
def ddNoLU : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 1]

/-- `[1 1; 1 1]` is tridiagonal (as is every `2 × 2` matrix). -/
lemma ddOnes_isTridiagonal : IsTridiagonal ddOnes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h

/-- `[1 1; 1 1]` is diagonally dominant by rows. -/
lemma ddOnes_rowDD : IsRowDiagDominant ddOnes := by
  intro i
  fin_cases i <;> simp [ddOnes, Finset.sum_erase_eq_sub, Fin.sum_univ_two]

/-- `[1 1; 1 1]` is singular. -/
lemma ddOnes_det : ddOnes.det = 0 := by
  simp [ddOnes, det_fin_two]

/-- `[1 1; 1 1] = [1 0; 1 1] [1 1; 0 0]`. -/
lemma ddOnes_isLU : IsLU ddOnes !![1, 0; 1, 1] !![1, 1; 0, 0] where
  lower i j h := by fin_cases i <;> fin_cases j <;> simp_all
  unit_diag i := by fin_cases i <;> simp
  upper i j h := by fin_cases i <;> fin_cases j <;> simp_all
  eq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ddOnes, mul_apply, Fin.sum_univ_two]

/-- Nonsingularity is needed in `piv_ne_zero_of_diagDominant`: `A = [1 1; 1 1]` is tridiagonal,
diagonally dominant by rows and by columns, and singular, and its pivot `u_1 = 1 - 1·1/1`
vanishes. (This `A` still has an LU factorization, `ddOnes_isLU`; for the failure of
`exists_LU_of_diagDominant` without nonsingularity see `rowDD_singular_no_LU_example`.) -/
theorem diagDominant_singular_piv_eq_zero_example :
    IsTridiagonal ddOnes ∧ IsRowDiagDominant ddOnes ∧ IsColDiagDominant ddOnes ∧
      ddOnes.det = 0 ∧ piv ddOnes 1 = 0 ∧ ∃ L U, IsLU ddOnes L U := by
  refine ⟨ddOnes_isTridiagonal, ddOnes_rowDD, ?_, ddOnes_det, ?_, ⟨_, _, ddOnes_isLU⟩⟩
  · intro i
    fin_cases i <;> simp [ddOnes, Finset.sum_erase_eq_sub, Fin.sum_univ_two]
  · simp [piv, ent, ddOnes]

/-- Nonsingularity is needed in `exists_LU_of_diagDominant`: `A = [0 0; 1 1]` is tridiagonal,
diagonally dominant by rows and singular, but has no LU factorization (comparing first columns
in `A = LU` gives `U 0 0 = A 0 0 = 0` and then `A 1 0 = L 1 0 * U 0 0 = 0`, but `A 1 0 = 1`). -/
theorem rowDD_singular_no_LU_example :
    IsTridiagonal ddNoLU ∧ IsRowDiagDominant ddNoLU ∧ ddNoLU.det = 0 ∧
      ¬ ∃ L U, IsLU ddNoLU L U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h
  · intro i
    fin_cases i <;> simp [ddNoLU, Finset.sum_erase_eq_sub, Fin.sum_univ_two]
  · simp [ddNoLU, det_fin_two]
  · rintro ⟨L, U, hLU⟩
    have h00 := congrFun (congrFun hLU.eq 0) 0
    have h10 := congrFun (congrFun hLU.eq 1) 0
    simp [ddNoLU, mul_apply, Fin.sum_univ_two, hLU.unit_diag, hLU.lower 0 1 (by decide),
      hLU.upper 1 0 (by decide)] at h00 h10
    rw [← h00] at h10
    simp at h10

/-- Nonsingularity is needed in `rowDD_symm_posDef`: `A = [1 1; 1 1]` is tridiagonal, row
diagonally dominant, symmetric, with positive diagonal, but singular and hence not positive
definite. -/
theorem rowDD_symm_singular_not_posDef_example :
    IsTridiagonal ddOnes ∧ IsRowDiagDominant ddOnes ∧ ddOnesᵀ = ddOnes ∧
      (∀ i, 0 < ddOnes i i) ∧ ddOnes.det = 0 ∧ ¬ ddOnes.PosDef := by
  refine ⟨ddOnes_isTridiagonal, ddOnes_rowDD, ?_, ?_, ddOnes_det, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ddOnes]
  · intro i
    fin_cases i <;> simp [ddOnes]
  · intro h
    exact h.det_pos.ne' ddOnes_det

end SingularExamples

/-! ### Row diagonally dominant matrices that are nonnegative or symmetric -/

section NonnegSymm

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- If `A ≥ 0` entrywise, all `ent`-entries of `A` are nonnegative. -/
lemma ent_nonneg_of_entrywise_nonneg (h0 : ∀ i j, 0 ≤ A i j) (i j : ℕ) : 0 ≤ ent A i j := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt A h.1 h.2]; exact h0 _ _
  · simp [ent, h]

/-- If `Aᵀ = A`, then `ent A i j = ent A j i`. -/
lemma ent_symm_of_transpose_eq (hS : Aᵀ = A) (i j : ℕ) : ent A i j = ent A j i := by
  rw [← ent_transpose, hS]

/-- The pivots of a nonsingular, tridiagonal, row diagonally dominant matrix `A ≥ 0` are positive
(indeed `u_k ≥ e_k ≥ 0`: `u_{k+1} = d_{k+1} - c_{k+1} e_k / u_k ≥ d_{k+1} - c_{k+1} ≥ e_{k+1}`). -/
lemma rowDD_nonneg_piv_pos (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (hDD : IsRowDiagDominant A) (h0 : ∀ i j, 0 ≤ A i j) : ∀ k, k < n → 0 < piv A k := by
  have hp := piv_ne_zero_of_diagDominant A hA hT (Or.inl hDD)
  have hed := rowDD_abs_supd_le_abs_piv hT hDD hp
  have hent := ent_nonneg_of_entrywise_nonneg h0
  intro k
  induction k with
  | zero =>
    intro hk
    exact lt_of_le_of_ne (by rw [piv_zero]; exact hent 0 0) (hp 0 hk).symm
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    have hek := hed k (by omega)
    have hdd := hDD.two_le (j₁ := k) (j₂ := k + 2) hk (by omega) (by omega) (by omega)
    have hc := hent (k + 1) k
    have he := hent k (k + 1)
    rw [abs_of_nonneg hc, abs_of_nonneg (hent _ _), abs_of_nonneg (hent _ _)] at hdd
    simp only [supd] at hek
    rw [abs_of_nonneg he, abs_of_pos hpk] at hek
    have h1 : ent A (k + 1) k / piv A k * ent A k (k + 1) ≤ ent A (k + 1) k := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpk]
      exact mul_le_mul_of_nonneg_left hek hc
    have hnn : 0 ≤ piv A (k + 1) := by
      rw [piv_succ, mult_succ]
      have := hent (k + 1) (k + 2)
      linarith
    exact lt_of_le_of_ne hnn (hp (k + 1) hk).symm

/-- **Section 4 (p. 527).** *A nonsingular, tridiagonal, row diagonally dominant matrix that is
nonnegative (`A ≥ 0`) is totally nonnegative.* (The pivots are positive and the multipliers
nonnegative, so `A = LU` with `L ≥ 0`, `U ≥ 0`; compare Theorem 3.1 (b).)

Nonsingularity is part of the standing hypotheses of Theorem 4.2; it is not needed for this
implication, see `isTotallyNonneg_of_rowDD_nonneg`. -/
theorem rowDD_nonneg_isTotallyNonneg (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (h0 : ∀ i j, 0 ≤ A i j) :
    IsTotallyNonneg A := by
  have hpos := rowDD_nonneg_piv_pos hA hT hDD h0
  have hent := ent_nonneg_of_entrywise_nonneg h0
  have h := isTotallyNonneg_lowerBidiag_mul_upperBidiag (n := n) (l := mult A) (p := piv A)
    (e := supd A) ?_ hpos fun i _ => hent _ _
  · rwa [← eq_lowerBidiag_mul_upperBidiag hT fun i hi => (hpos i (by omega)).ne'] at h
  · intro i hi0 hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi0
    rw [zero_add, mult_succ]
    exact div_nonneg (hent _ _) (hpos k (by omega)).le

/-- A tridiagonal, row diagonally dominant matrix `A ≥ 0` is totally nonnegative even if it is
singular: for `ε > 0`, `A + εI` is strictly diagonally dominant, hence nonsingular, and totally
nonnegative by `rowDD_nonneg_isTotallyNonneg`; let `ε → 0⁺`. -/
theorem isTotallyNonneg_of_rowDD_nonneg (A : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (h0 : ∀ i j, 0 ≤ A i j) :
    IsTotallyNonneg A := by
  have hent : ∀ (ε : ℝ) (i j : Fin n),
      (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) i j = A i j + if i = j then ε else 0 := by
    intro ε i j
    simp [one_apply]
  -- `A + εI` is totally nonnegative for every `ε > 0`
  have hTN : ∀ ε : ℝ, 0 < ε → IsTotallyNonneg (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    intro ε hε
    have hoff : ∀ i j : Fin n, i ≠ j → (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) i j = A i j :=
      fun i j hij => by rw [hent, ite_eq_right hij, add_zero]
    have hsum : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        |(A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) i j| = ∑ j ∈ Finset.univ.erase i, |A i j| :=
      fun i => Finset.sum_congr rfl fun j hj => by
        rw [hoff i j (Finset.ne_of_mem_erase hj).symm]
    have hdiag : ∀ i : Fin n, |(A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)) i i| = |A i i| + ε := by
      intro i
      rw [hent, ite_eq_left rfl, abs_of_nonneg (by linarith [h0 i i]), abs_of_nonneg (h0 i i)]
    refine rowDD_nonneg_isTotallyNonneg _ ?_ ?_ ?_ ?_
    · rw [isUnit_iff_ne_zero]
      refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
      simp only [Real.norm_eq_abs]
      rw [hsum, hdiag]
      linarith [hDD k]
    · intro i j hij
      rw [hoff i j (fun h => by subst h; omega), hT i j hij]
    · intro i
      rw [hsum, hdiag]
      linarith [hDD i]
    · intro i j
      rw [hent]
      split_ifs <;> linarith [h0 i j]
  -- pass to the limit `ε → 0⁺`
  intro k I J
  have hcont : Continuous fun ε : ℝ =>
      ((A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix I J).det :=
    ((continuous_const.add (continuous_id.smul continuous_const)).matrix_submatrix _ _).matrix_det
  have hlim : Filter.Tendsto (fun ε : ℝ =>
      ((A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix I J).det)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (A.submatrix I J).det) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hTN ε hε k I J)

/-- The pivots of a nonsingular, tridiagonal, row diagonally dominant, symmetric matrix with
positive diagonal are positive (indeed `u_k ≥ |e_k|`:
`u_{k+1} = d_{k+1} - e_k² / u_k ≥ d_{k+1} - |e_k| = d_{k+1} - |c_{k+1}| ≥ |e_{k+1}|`). -/
lemma rowDD_symm_piv_pos (hA : IsUnit A.det) (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A)
    (hS : Aᵀ = A) (hd : ∀ i, 0 < A i i) : ∀ k, k < n → 0 < piv A k := by
  have hp := piv_ne_zero_of_diagDominant A hA hT (Or.inl hDD)
  have hed := rowDD_abs_supd_le_abs_piv hT hDD hp
  have hdpos : ∀ i, i < n → 0 < ent A i i := fun i hi => by rw [ent_of_lt A hi hi]; exact hd _
  intro k
  induction k with
  | zero => intro hk; rw [piv_zero]; exact hdpos 0 hk
  | succ k ih =>
    intro hk
    have hpk := ih (by omega)
    have hek := hed k (by omega)
    have hdd := hDD.two_le (j₁ := k) (j₂ := k + 2) hk (by omega) (by omega) (by omega)
    rw [abs_of_pos (hdpos (k + 1) hk)] at hdd
    simp only [supd] at hek
    rw [abs_of_pos hpk] at hek
    -- `l_{k+1} e_k = e_k² / u_k ≤ |e_k| = |c_{k+1}|`
    have h1 : ent A (k + 1) k / piv A k * ent A k (k + 1) ≤ |ent A (k + 1) k| := by
      rw [ent_symm_of_transpose_eq hS (k + 1) k, div_mul_eq_mul_div, div_le_iff₀ hpk]
      calc ent A k (k + 1) * ent A k (k + 1) = |ent A k (k + 1)| * |ent A k (k + 1)| :=
            (abs_mul_abs_self _).symm
        _ ≤ |ent A k (k + 1)| * piv A k := mul_le_mul_of_nonneg_left hek (abs_nonneg _)
    have hnn : 0 ≤ piv A (k + 1) := by
      rw [piv_succ, mult_succ]
      have := abs_nonneg (ent A (k + 1) (k + 2))
      linarith
    exact lt_of_le_of_ne hnn (hp (k + 1) hk).symm

/-- **Section 4 (p. 527).** *A nonsingular, tridiagonal, row diagonally dominant matrix that is
symmetric with positive diagonal is positive definite.* (The pivots `u_k` are positive and
`A = L D Lᵀ` with `D = diag(u_k)`.)

The paper says "symmetric (so that it is positive definite)"; the positivity of the diagonal is
tacit there and cannot be dropped: `[2 1; 1 -2]` is symmetric, tridiagonal, row diagonally
dominant and nonsingular, but not positive definite (`rowDD_symm_not_posDef_example`).
Nonsingularity cannot be dropped either (`rowDD_symm_singular_not_posDef_example`). -/
theorem rowDD_symm_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hS : Aᵀ = A) (hd : ∀ i, 0 < A i i) :
    A.PosDef := by
  have hpos := rowDD_symm_piv_pos hA hT hDD hS hd
  -- `U = D Lᵀ` with `D = diag(u_i)`, hence `A = L D Lᵀ`
  have hU : upperBidiag (n := n) (piv A) (supd A) =
      diagonal (fun i : Fin n => piv A i) * (lowerBidiag (n := n) (mult A))ᵀ := by
    ext i j
    simp only [upperBidiag, of_apply, diagonal_mul, transpose_apply, lowerBidiag]
    split_ifs with h1 h2 h3 h4 h5 <;> try first | ring1 | (exfalso; omega)
    rw [h4, mult_succ, mul_div_cancel₀ _ (hpos i i.2).ne', supd,
      ent_symm_of_transpose_eq hS]
  have hAeq : A = (lowerBidiag (n := n) (mult A))ᵀᴴ * diagonal (fun i : Fin n => piv A i) *
      (lowerBidiag (n := n) (mult A))ᵀ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, Matrix.mul_assoc, ← hU]
    exact eq_lowerBidiag_mul_upperBidiag hT fun i hi => (hpos i (by omega)).ne'
  have hD : (diagonal (fun i : Fin n => piv A i)).PosDef :=
    posDef_diagonal_iff.mpr fun i => hpos i i.2
  have hinj : Function.Injective (lowerBidiag (n := n) (mult A))ᵀ.mulVec := by
    rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, det_transpose]
    exact isUnit_det_lowerBidiag _
  have := hD.conjTranspose_mul_mul_same hinj
  rwa [← hAeq] at this

end NonnegSymm

/-! ### A symmetric row diagonally dominant matrix with mixed diagonal signs -/

section IndefiniteExample

/-- The symmetric, row diagonally dominant, indefinite matrix `[2 1; 1 -2]`. -/
def ddIndef : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, -2]

/-- The unit lower triangular LU factor of `ddIndef`. -/
def ddIndefL : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1 / 2, 1]

/-- The upper triangular LU factor of `ddIndef`. -/
def ddIndefU : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 0, -5 / 2]

/-- `[2 1; 1 -2] = [1 0; 1/2 1] [2 1; 0 -5/2]`. -/
lemma ddIndef_isLU : IsLU ddIndef ddIndefL ddIndefU where
  lower i j h := by fin_cases i <;> fin_cases j <;> simp_all [ddIndefL]
  unit_diag i := by fin_cases i <;> simp [ddIndefL]
  upper i j h := by fin_cases i <;> fin_cases j <;> simp_all [ddIndefU]
  eq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ddIndef, ddIndefL, ddIndefU, mul_apply, Fin.sum_univ_two]
    norm_num

/-- `[1 0; 1/2 1]⁻¹ = [1 0; -1/2 1]`. -/
lemma ddIndefL_inv : ddIndefL⁻¹ = !![1, 0; -1 / 2, 1] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddIndefL, mul_apply, Fin.sum_univ_two]
  norm_num

/-- `[2 1; 0 -5/2]⁻¹ = [1/2 1/5; 0 -2/5]`. -/
lemma ddIndefU_inv : ddIndefU⁻¹ = !![1 / 2, 1 / 5; 0, -2 / 5] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddIndefU, mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `[2 1; 1 -2]⁻¹ = [2/5 1/5; 1/5 -2/5]`. -/
lemma ddIndef_inv : ddIndef⁻¹ = !![2 / 5, 1 / 5; 1 / 5, -2 / 5] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddIndef, mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **The positive diagonal is needed in `rowDD_symm_posDef` and `rowDD_symm_bound_exact`.**
`A = [2 1; 1 -2]` is symmetric, tridiagonal, row diagonally dominant and nonsingular
(`det A = -5`), but not positive definite. Its LU factors are `L = [1 0; 1/2 1]`,
`U = [2 1; 0 -5/2]`, and the bound of Section 4 is not exact for it:
`|U⁻¹||L⁻¹| = [3/5 1/5; 1/5 2/5] ≠ [2/5 1/5; 1/5 2/5] = |A⁻¹|`; already for `y = e`,
`|U⁻¹||L⁻¹| e ≠ |A⁻¹| e`. -/
theorem rowDD_symm_not_posDef_example :
    ddIndefᵀ = ddIndef ∧ IsTridiagonal ddIndef ∧ IsRowDiagDominant ddIndef ∧
      IsUnit ddIndef.det ∧ ¬ ddIndef.PosDef ∧ IsLU ddIndef ddIndefL ddIndefU ∧
      ddIndefU⁻¹.map abs * ddIndefL⁻¹.map abs ≠ ddIndef⁻¹.map abs ∧
      (ddIndefU⁻¹.map abs * ddIndefL⁻¹.map abs) *ᵥ (fun _ => (1 : ℝ)) ≠
        ddIndef⁻¹.map abs *ᵥ (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ddIndef_isLU, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ddIndef]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h
  · intro i
    fin_cases i <;> simp [ddIndef, Finset.sum_erase_eq_sub, Fin.sum_univ_two]
  · rw [isUnit_iff_ne_zero, det_fin_two]
    simp [ddIndef]
    norm_num
  · intro h
    have := h.diag_pos (i := 1)
    simp [ddIndef] at this
    linarith
  · intro h
    have := congrFun (congrFun h 0) 0
    rw [ddIndefL_inv, ddIndefU_inv, ddIndef_inv] at this
    simp [mul_apply, Fin.sum_univ_two, abs_div] at this
    norm_num at this
  · intro h
    have := congrFun h 0
    rw [ddIndefL_inv, ddIndefU_inv, ddIndef_inv] at this
    simp [mulVec, dotProduct, mul_apply, Fin.sum_univ_two, abs_div] at this
    norm_num at this

end IndefiniteExample

/-! ### Exactness of the bound of Theorem 4.2 -/

section Exactness

/-- For a nonsingular tridiagonal matrix of one of the types (a)–(d) of Theorem 3.1, every LU
factorization satisfies `|U⁻¹||L⁻¹| = |A⁻¹|` (Theorem 3.1 and Theorem 3.3; the matrix form of
`bound_exact_of_type`). -/
lemma abs_inv_factors_eq_of_type (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs := by
  have habs := (theorem_3_1' A hA hT h).2 L U hLU
  rw [← hLU.eq] at habs
  exact theorem_3_3 A L U hA hT hLU habs

/-- **Section 4 (p. 527), symmetric case.** If the nonsingular, tridiagonal, row diagonally
dominant matrix `A = LU` is symmetric with positive diagonal (so that it is positive definite,
`rowDD_symm_posDef`), then `|U⁻¹||L⁻¹| = |A⁻¹|`: the bound `|A⁻¹| y ≤ |U⁻¹||L⁻¹| y` is exact.

The positive diagonal cannot be dropped (`rowDD_symm_not_posDef_example`). -/
theorem rowDD_symm_bound_exact (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hLU : IsLU A L U)
    (hS : Aᵀ = A) (hd : ∀ i, 0 < A i i) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs :=
  abs_inv_factors_eq_of_type A L U hA hT hLU (Or.inl (rowDD_symm_posDef A hA hT hDD hS hd))

/-- The symmetric case with negative diagonal: then `-A` is positive definite and `A` is sign
equivalent to it (Theorem 3.1 (d)), so again `|U⁻¹||L⁻¹| = |A⁻¹|`. Together with
`rowDD_symm_not_posDef_example` this shows that for symmetric `A` a common sign of the diagonal
entries is sufficient for exactness, while mixed signs can destroy it.  (A common sign is not
necessary in general: e.g. for the reducible matrix `diag(1, -1)` the bound is exact.) -/
theorem rowDD_symm_neg_bound_exact (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hLU : IsLU A L U)
    (hS : Aᵀ = A) (hd : ∀ i, A i i < 0) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs := by
  have hA' : IsUnit (-A).det := by
    rw [isUnit_iff_ne_zero, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hA.ne_zero
  have hT' : IsTridiagonal (-A) := fun i j h => by simp [hT i j h]
  have hDD' : IsRowDiagDominant (-A) := fun i => by simpa using hDD i
  have hS' : (-A)ᵀ = -A := by rw [transpose_neg, hS]
  have hd' : ∀ i, 0 < (-A) i i := fun i => by simpa using hd i
  have hP := rowDD_symm_posDef (-A) hA' hT' hDD' hS' hd'
  refine abs_inv_factors_eq_of_type A L U hA hT hLU
    (Or.inr (Or.inr (Or.inr ⟨-1, 1, -A, ?_, ?_, ?_, Or.inl hP⟩)))
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_ne h]
  · ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_ne h]
  · simp

/-- **Section 4 (p. 527), nonnegative case.** If the nonsingular, tridiagonal, row diagonally
dominant matrix `A = LU` is nonnegative (so that it is totally nonnegative,
`rowDD_nonneg_isTotallyNonneg`), then `|U⁻¹||L⁻¹| = |A⁻¹|`: the bound is exact. -/
theorem rowDD_nonneg_bound_exact (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hLU : IsLU A L U)
    (h0 : ∀ i j, 0 ≤ A i j) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs :=
  abs_inv_factors_eq_of_type A L U hA hT hLU
    (Or.inr (Or.inl (rowDD_nonneg_isTotallyNonneg A hA hT hDD h0)))

/-- **Section 4 (p. 527), M-matrix case.** If the tridiagonal M-matrix `A` has the LU
factorization `A = LU`, then `|U⁻¹||L⁻¹| = |A⁻¹|`: the bound is exact. (An M-matrix is
nonsingular by definition, and row diagonal dominance is not needed: Theorem 3.1 (c) and
Theorem 3.3.) -/
theorem mMatrix_bound_exact (A L U : Matrix (Fin n) (Fin n) ℝ) (hT : IsTridiagonal A)
    (hLU : IsLU A L U) (hM : IsMMatrix A) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs :=
  abs_inv_factors_eq_of_type A L U hM.1 hT hLU (Or.inr (Or.inr (Or.inl hM)))

/-- **Section 4 (p. 527).** *"Moreover, the bound is exact if the row diagonally dominant `A`
happens to be symmetric (so that it is positive definite), nonnegative (that is, `A ≥ 0`, which
implies it is totally nonnegative), or an M-matrix."*

Let the nonsingular, tridiagonal, row diagonally dominant matrix `A` have the LU factorization
`A = LU` (it exists by `exists_LU_of_diagDominant`). If `A` is symmetric with positive diagonal,
or `A ≥ 0`, or `A` is an M-matrix, then `|U⁻¹||L⁻¹| = |A⁻¹|`, so the upper bound
`|U⁻¹||L⁻¹| y` for `|A⁻¹| y` is exact for every `y`.

The positive diagonal in the symmetric case is tacit in the paper and cannot be dropped
(`rowDD_symm_not_posDef_example`). -/
theorem rowDD_bound_exact (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hDD : IsRowDiagDominant A) (hLU : IsLU A L U)
    (h : (Aᵀ = A ∧ ∀ i, 0 < A i i) ∨ (∀ i j, 0 ≤ A i j) ∨ IsMMatrix A) :
    U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs ∧
      ∀ y : Fin n → ℝ, (U⁻¹.map abs * L⁻¹.map abs) *ᵥ y = A⁻¹.map abs *ᵥ y := by
  have hEq : U⁻¹.map abs * L⁻¹.map abs = A⁻¹.map abs := by
    rcases h with ⟨hS, hd⟩ | h0 | hM
    · exact rowDD_symm_bound_exact A L U hA hT hDD hLU hS hd
    · exact rowDD_nonneg_bound_exact A L U hA hT hDD hLU h0
    · exact mMatrix_bound_exact A L U hT hLU hM
  exact ⟨hEq, fun y => by rw [hEq]⟩

end Exactness

end Higham
