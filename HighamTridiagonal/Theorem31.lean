import HighamTridiagonal.TotallyNonneg

/-!
# Theorem 3.1

*Let `A ∈ ℝ^{n×n}` be nonsingular and tridiagonal. If any of the following conditions hold then
`A` has an LU factorization and `|L||U| = |LU|`:*
* *(a) `A` is symmetric positive definite;*
* *(b) `A` is totally nonnegative, or equivalently, `L ≥ 0` and `U ≥ 0`;*
* *(c) `A` is an M-matrix, or equivalently, `L` and `U` have positive diagonal elements and
  nonpositive off-diagonal elements;*
* *(d) `A` is sign equivalent to a matrix `B` of type (a)–(c); that is, `A = D₁ B D₂`, where
  `|D₁| = |D₂| = I`.*

The main statement is `theorem_3_1`; the two equivalences claimed in (b) and (c) are
`theorem_3_1_b_equiv` and `theorem_3_1_c_equiv`.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- A nonsingular `A ∈ ℝ^{n×n}` is an *M-matrix* if `a_ij ≤ 0` for all `i ≠ j` and `A⁻¹ ≥ 0`. -/
def IsMMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsUnit A.det ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∀ i j, 0 ≤ A⁻¹ i j

/-- `B` is of type (a)–(c) of Theorem 3.1: symmetric positive definite, totally nonnegative, or
an M-matrix.  (For real matrices Mathlib's `PosDef` includes symmetry: `Bᴴ = Bᵀ = B`.) -/
def IsTypeABC (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B

/-- `A` is of type (d) of Theorem 3.1: `A = D₁ B D₂` with `|D₁| = |D₂| = I` and `B` of type
(a)–(c). -/
def IsSignEquivTypeABC (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
    IsTypeABC B

/-! ### From positive pivots and the sign condition to `|L||U| = |LU|` -/

lemma exists_LU_of_piv_pos {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hp : ∀ k, k < n → 0 < piv A k)
    (hs : ∀ k, k + 1 < n → 0 ≤ mult A (k + 1) * supd A k * piv A (k + 1)) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs :=
  ⟨_, _, isLU_recurrence hT fun i hi => (hp i (by omega)).ne',
    (abs_mul_abs_eq_abs_mul_iff _ _ _).mpr hs⟩

/-! ### (a) Symmetric positive definite matrices -/

lemma posDef_leadMinor_pos {A : Matrix (Fin n) (Fin n) ℝ} (hP : A.PosDef) :
    ∀ m, m ≤ n → 0 < leadMinor A m := by
  intro m hm
  rw [leadMinor_eq_det_submatrix A hm]
  exact (hP.submatrix (Fin.castLE_injective hm)).det_pos

lemma posDef_ent_symm {A : Matrix (Fin n) (Fin n) ℝ} (hP : A.PosDef) (i j : ℕ) :
    ent A i j = ent A j i := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt A h.1 h.2, ent_of_lt A h.2 h.1, ← hP.1.apply]
    simp
  · rw [ent, dite_eq_right h, ent, dite_eq_right (by tauto)]

theorem theorem_3_1_a {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) (hP : A.PosDef) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs := by
  have hp := piv_pos_of_leadMinor_pos hT (posDef_leadMinor_pos hP)
  refine exists_LU_of_piv_pos hT hp fun k hk => ?_
  have hpk := hp k (by omega)
  have : mult A (k + 1) * supd A k = ent A k (k + 1) ^ 2 / piv A k := by
    rw [mult_succ, posDef_ent_symm hP (k + 1) k, supd]; ring
  rw [this]
  exact mul_nonneg (div_nonneg (sq_nonneg _) hpk.le) (hp (k + 1) hk).le

/-! ### (b) Totally nonnegative matrices -/

theorem IsTotallyNonneg.piv_pos {A : Matrix (Fin n) (Fin n) ℝ} (hTN : IsTotallyNonneg A)
    (hA : IsUnit A.det) (hT : IsTridiagonal A) : ∀ k, k < n → 0 < piv A k :=
  piv_pos_of_leadMinor_pos hT (hTN.leadMinor_pos hA hT)

theorem theorem_3_1_b {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hTN : IsTotallyNonneg A) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs := by
  have hp := hTN.piv_pos hA hT
  refine exists_LU_of_piv_pos hT hp fun k hk => ?_
  rw [mult_succ, supd]
  exact mul_nonneg (mul_nonneg (div_nonneg (hTN.ent_nonneg _ _) (hp k (by omega)).le)
    (hTN.ent_nonneg _ _)) (hp (k + 1) hk).le

/-- **Theorem 3.1 (b), "or equivalently".** For nonsingular tridiagonal `A`: `A` is totally
nonnegative iff `A` has an LU factorization with `L ≥ 0` and `U ≥ 0`. -/
theorem theorem_3_1_b_equiv (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) :
    IsTotallyNonneg A ↔ ∃ L U, IsLU A L U ∧ (∀ i j, 0 ≤ L i j) ∧ (∀ i j, 0 ≤ U i j) := by
  constructor
  · intro hTN
    have hp := hTN.piv_pos hA hT
    refine ⟨_, _, isLU_recurrence hT fun i hi => (hp i (by omega)).ne', ?_, ?_⟩
    · intro i j
      simp only [lowerBidiag, of_apply]
      split_ifs with h1 h2
      · exact zero_le_one
      · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨j, h2⟩
        rw [hk, mult_succ]
        exact div_nonneg (hTN.ent_nonneg _ _) (hp k (by omega)).le
      · exact le_rfl
    · intro i j
      simp only [upperBidiag, of_apply]
      split_ifs with h1 h2
      · exact (hp i i.2).le
      · exact hTN.ent_nonneg _ _
      · exact le_rfl
  · rintro ⟨L, U, hLU, hL0, hU0⟩
    obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
    have hpos : ∀ i, i < n → 0 < piv A i := by
      intro i hi
      have := hU0 ⟨i, hi⟩ ⟨i, hi⟩
      rw [hU] at this
      simp only [upperBidiag, of_apply, ite_true] at this
      exact lt_of_le_of_ne this (hp i hi).symm
    have he : ∀ i, i + 1 < n → 0 ≤ supd A i := by
      intro i hi
      have := hU0 ⟨i, by omega⟩ ⟨i + 1, hi⟩
      rw [hU] at this
      simpa [upperBidiag] using this
    have hl : ∀ i, 0 < i → i < n → 0 ≤ mult A i := by
      intro i hi0 hi
      have := hL0 ⟨i, hi⟩ ⟨i - 1, by omega⟩
      rw [hL] at this
      simp only [lowerBidiag, of_apply] at this
      rwa [ite_eq_right (by omega), ite_eq_left (by omega)] at this
    rw [hLU.eq, hL, hU]
    exact isTotallyNonneg_lowerBidiag_mul_upperBidiag hl hpos he

/-! ### (c) M-matrices -/

/-- For a tridiagonal M-matrix all pivots are positive (Gaussian elimination applied to
`A x = e` with `x = A⁻¹ e > 0`). -/
theorem IsMMatrix.piv_pos {A : Matrix (Fin n) (Fin n) ℝ} (hM : IsMMatrix A)
    (hT : IsTridiagonal A) : ∀ k, k < n → 0 < piv A k := by
  obtain ⟨hA, hoff, hinv⟩ := hM
  set x : Fin n → ℝ := A⁻¹ *ᵥ (fun _ => 1) with hx
  have hAx : A *ᵥ x = fun _ => 1 := by
    rw [hx, mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  -- `x > 0`
  have hxpos : ∀ j, 0 < x j := by
    intro j
    have hnn : ∀ k, 0 ≤ A⁻¹ j k * 1 := fun k => by rw [mul_one]; exact hinv j k
    have hsum : x j = ∑ k, A⁻¹ j k * 1 := rfl
    rcases (Finset.sum_nonneg fun k _ => hnn k).lt_or_eq with h | h
    · rwa [hsum]
    · exfalso
      have hz : ∀ k, A⁻¹ j k = 0 := fun k => by
        have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnn k).mp h.symm k
          (Finset.mem_univ _)
        rwa [mul_one] at this
      have h1 : (A⁻¹ * A) j j = 1 := by rw [nonsing_inv_mul _ hA]; simp
      rw [mul_apply, Finset.sum_eq_zero fun k _ => by rw [hz k, zero_mul]] at h1
      exact zero_ne_one h1
  have hxe : ∀ j, 0 ≤ vext x j := by
    intro j; unfold vext; split_ifs <;> first | exact (hxpos _).le | exact le_rfl
  have hxe' : ∀ j (hj : j < n), 0 < vext x j := by
    intro j hj; rw [vext, dite_eq_left hj]; exact hxpos _
  have hrow : ∀ j (hj : j < n), (A *ᵥ x) ⟨j, hj⟩ = 1 := by intro j hj; rw [hAx]
  -- off-diagonal entries are nonpositive
  have hsub : ∀ k, ent A (k + 1) k ≤ 0 := by
    intro k
    by_cases h : k + 1 < n
    · rw [ent_of_lt A h (by omega)]
      exact hoff _ _ (by simp [Fin.ext_iff])
    · rw [ent_of_not_lt_left A h]
  have hsup : ∀ k, ent A k (k + 1) ≤ 0 := by
    intro k
    by_cases h : k + 1 < n
    · rw [ent_of_lt A (by omega) h]
      exact hoff _ _ (by simp [Fin.ext_iff])
    · rw [ent_of_not_lt_right A h]
  -- the induction: `u_k > 0` and `u_k x_k + e_k x_{k+1} > 0`
  have key : ∀ k, k < n → 0 < piv A k ∧ 0 < piv A k * vext x k + ent A k (k + 1) * vext x (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := hrow 0 hk
      rw [mulVec_tridiag_zero hT x hk] at h0
      have hw : 0 < piv A 0 * vext x 0 + ent A 0 1 * vext x 1 := by
        rw [piv_zero, h0]; exact one_pos
      refine ⟨?_, hw⟩
      have : 0 < piv A 0 * vext x 0 := by
        have := mul_nonpos_of_nonpos_of_nonneg (hsup 0) (hxe 1)
        linarith
      exact pos_of_mul_pos_left this (hxe' 0 hk).le
    | succ k ih =>
      intro hk
      obtain ⟨hpk, hwk⟩ := ih (by omega)
      have h1 := hrow (k + 1) hk
      rw [mulVec_tridiag_succ hT x hk] at h1
      have hl : mult A (k + 1) ≤ 0 := by
        rw [mult_succ]; exact div_nonpos_of_nonpos_of_nonneg (hsub k) hpk.le
      have hc : ent A (k + 1) k = mult A (k + 1) * piv A k := by
        rw [mult_succ, div_mul_cancel₀ _ hpk.ne']
      have hw : piv A (k + 1) * vext x (k + 1) + ent A (k + 1) (k + 2) * vext x (k + 2) =
          1 - mult A (k + 1) * (piv A k * vext x k + ent A k (k + 1) * vext x (k + 1)) := by
        rw [piv_succ, ← h1, hc]; ring
      have hw' : 0 < piv A (k + 1) * vext x (k + 1) + ent A (k + 1) (k + 2) * vext x (k + 2) := by
        rw [hw]
        have := mul_nonpos_of_nonpos_of_nonneg hl hwk.le
        linarith
      refine ⟨?_, hw'⟩
      have : 0 < piv A (k + 1) * vext x (k + 1) := by
        have := mul_nonpos_of_nonpos_of_nonneg (hsup (k + 1)) (hxe (k + 2))
        linarith
      exact pos_of_mul_pos_left this (hxe' (k + 1) hk).le
  exact fun k hk => (key k hk).1

lemma IsMMatrix.ent_offdiag_nonpos {A : Matrix (Fin n) (Fin n) ℝ} (hM : IsMMatrix A) {i j : ℕ}
    (hij : i ≠ j) : ent A i j ≤ 0 := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt A h.1 h.2]; exact hM.2.1 _ _ (by simp [Fin.ext_iff, hij])
  · simp [ent, h]

theorem theorem_3_1_c {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hM : IsMMatrix A) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs := by
  have hp := hM.piv_pos hT
  refine exists_LU_of_piv_pos hT hp fun k hk => ?_
  rw [mult_succ, supd]
  have h1 : ent A (k + 1) k / piv A k ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hM.ent_offdiag_nonpos (by omega)) (hp k (by omega)).le
  have h2 : ent A k (k + 1) ≤ 0 := hM.ent_offdiag_nonpos (by omega)
  exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos h1 h2) (hp (k + 1) hk).le

/-- **Theorem 3.1 (c), "or equivalently".** For nonsingular tridiagonal `A`: `A` is an M-matrix
iff `A` has an LU factorization in which `L` and `U` have positive diagonal elements and
nonpositive off-diagonal elements. -/
theorem theorem_3_1_c_equiv (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) :
    IsMMatrix A ↔ ∃ L U, IsLU A L U ∧ (∀ i, 0 < L i i) ∧ (∀ i, 0 < U i i) ∧
      (∀ i j, i ≠ j → L i j ≤ 0) ∧ (∀ i j, i ≠ j → U i j ≤ 0) := by
  constructor
  · intro hM
    have hp := hM.piv_pos hT
    refine ⟨_, _, isLU_recurrence hT fun i hi => (hp i (by omega)).ne', ?_, ?_, ?_, ?_⟩
    · intro i; simp [lowerBidiag]
    · intro i; simpa [upperBidiag] using hp i i.2
    · intro i j hij
      have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [lowerBidiag, of_apply, hij', ite_false]
      split_ifs with h2
      · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨j, h2⟩
        rw [hk, mult_succ]
        exact div_nonpos_of_nonpos_of_nonneg (hM.ent_offdiag_nonpos (by omega)) (hp k (by omega)).le
      · exact le_rfl
    · intro i j hij
      have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp only [upperBidiag, of_apply, hij', ite_false]
      split_ifs with h2
      · exact hM.ent_offdiag_nonpos (by omega)
      · exact le_rfl
  · rintro ⟨L, U, hLU, -, hUd, hLo, hUo⟩
    obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
    have hpos : ∀ i, i < n → 0 < piv A i := by
      intro i hi
      have := hUd ⟨i, hi⟩
      rw [hU] at this
      simpa [upperBidiag] using this
    have he : ∀ i, i + 1 < n → supd A i ≤ 0 := by
      intro i hi
      have := hUo ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.ext_iff])
      rw [hU] at this
      simpa [upperBidiag] using this
    have hl : ∀ i, i + 1 < n → mult A (i + 1) ≤ 0 := by
      intro i hi
      have := hLo ⟨i + 1, hi⟩ ⟨i, by omega⟩ (by simp [Fin.ext_iff])
      rw [hL] at this
      simpa [lowerBidiag] using this
    refine ⟨hA, ?_, ?_⟩
    · -- off-diagonal entries of `A = LU`
      intro i j hij
      suffices h : ent A i j ≤ 0 by simpa using h
      have hi := i.2
      have hj := j.2
      have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      rcases lt_trichotomy ((i : ℕ) + 1) j with h | h | h
      · rw [hT.ent_eq_zero (Or.inl h)]
      · rw [← h]; exact he i (by omega)
      rcases lt_trichotomy ((j : ℕ) + 1) i with h' | h' | h'
      · rw [hT.ent_eq_zero (Or.inr h')]
      · rw [← h', show ent A (j + 1) j = mult A (j + 1) * piv A j by
          rw [mult_succ, div_mul_cancel₀ _ (hp j hj)]]
        exact mul_nonpos_of_nonpos_of_nonneg (hl j (by omega)) (hpos j hj).le
      · omega
    · -- `A⁻¹ = U⁻¹ L⁻¹ ≥ 0`
      intro i j
      rw [hLU.eq, Matrix.mul_inv_rev, mul_apply]
      refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ ?_
      · rw [hU]; simpa using ent_inv_upperBidiag_nonneg (n := n) hpos he i k
      · rw [hL]; simpa using ent_inv_lowerBidiag_nonneg (n := n) hl k j

/-! ### (d) Sign equivalence -/

/-- A matrix with `|D| = I` is diagonal with diagonal entries `±1`. -/
lemma eq_diagonal_of_map_abs_eq_one {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.map abs = 1) :
    D = diagonal (fun i => D i i) ∧ ∀ i, D i i * D i i = 1 := by
  have h : ∀ i j, |D i j| = (1 : Matrix (Fin n) (Fin n) ℝ) i j := fun i j => by
    rw [← hD]; rfl
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have := h i j
      rw [one_apply_ne hij, abs_eq_zero] at this
      rw [this, diagonal_apply_ne _ hij]
  · have := h i i
    rw [one_apply_eq] at this
    rw [← abs_mul_abs_self, this, one_mul]

lemma diagonal_mul_mul_diagonal_apply (s t : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : (diagonal s * M * diagonal t) i j = s i * M i j * t j := by
  simp [diagonal_mul, mul_diagonal]

theorem theorem_3_1_d {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (hd : ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧
      A = D₁ * B * D₂ ∧ (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs := by
  obtain ⟨D₁, D₂, B, hD₁, hD₂, hAeq, hB⟩ := hd
  obtain ⟨hD₁d, hs⟩ := eq_diagonal_of_map_abs_eq_one hD₁
  obtain ⟨hD₂d, ht⟩ := eq_diagonal_of_map_abs_eq_one hD₂
  set s : Fin n → ℝ := fun i => D₁ i i with hsdef
  set t : Fin n → ℝ := fun i => D₂ i i with htdef
  have hss : ∀ i, s i * s i = 1 := hs
  have htt : ∀ i, t i * t i = 1 := ht
  have hsabs : ∀ i, |s i| = 1 := fun i => by
    have := hss i; rw [← abs_mul_abs_self, ← abs_mul] at this
    nlinarith [abs_nonneg (s i), abs_mul_abs_self (s i), abs_mul (s i) (s i)]
  have htabs : ∀ i, |t i| = 1 := fun i => by
    have := htt i; rw [← abs_mul_abs_self, ← abs_mul] at this
    nlinarith [abs_nonneg (t i), abs_mul_abs_self (t i), abs_mul (t i) (t i)]
  rw [hD₁d, hD₂d] at hAeq
  have hA_apply : ∀ i j, A i j = s i * B i j * t j := fun i j => by
    rw [hAeq, diagonal_mul_mul_diagonal_apply]
  have hB_apply : ∀ i j, B i j = s i * A i j * t j := fun i j => by
    rw [hA_apply]
    calc B i j = (s i * s i) * B i j * (t j * t j) := by rw [hss, htt]; ring
      _ = _ := by ring
  -- `B` is nonsingular and tridiagonal
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hA.ne_zero
    rw [hAeq, det_mul, det_mul, h0, mul_zero, zero_mul]
  have hBT : IsTridiagonal B := fun i j hij => by rw [hB_apply, hT i j hij]; ring
  -- an LU factorization of `B` with `|L_B||U_B| = |L_B U_B|`
  obtain ⟨LB, UB, hLUB, habsB⟩ : ∃ L U, IsLU B L U ∧ L.map abs * U.map abs = (L * U).map abs := by
    rcases hB with hB | hB | hB
    · exact theorem_3_1_a hBT hB
    · exact theorem_3_1_b hBdet hBT hB
    · exact theorem_3_1_c hBT hB
  have hdd : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hss]
    exact diagonal_one
  refine ⟨diagonal s * LB * diagonal s, diagonal s * UB * diagonal t, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [diagonal_mul_mul_diagonal_apply, hLUB.lower i j hij]; ring
  · intro i
    rw [diagonal_mul_mul_diagonal_apply, hLUB.unit_diag i, mul_one, hss]
  · intro i j hij
    rw [diagonal_mul_mul_diagonal_apply, hLUB.upper i j hij]; ring
  · calc A = diagonal s * B * diagonal t := hAeq
      _ = diagonal s * (LB * UB) * diagonal t := by rw [← hLUB.eq]
      _ = diagonal s * LB * (diagonal s * diagonal s) * UB * diagonal t := by
          rw [hdd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = diagonal s * LB * diagonal s * (diagonal s * UB * diagonal t) := by
          simp only [Matrix.mul_assoc]
  · have hL : (diagonal s * LB * diagonal s).map abs = LB.map abs := by
      ext i j; simp [abs_mul, hsabs]
    have hU : (diagonal s * UB * diagonal t).map abs = UB.map abs := by
      ext i j; simp [abs_mul, hsabs, htabs]
    have hprod : diagonal s * LB * diagonal s * (diagonal s * UB * diagonal t) =
        diagonal s * (LB * UB) * diagonal t := by
      calc diagonal s * LB * diagonal s * (diagonal s * UB * diagonal t)
          = diagonal s * LB * (diagonal s * diagonal s) * UB * diagonal t := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hdd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [hL, hU, habsB, hprod]
    ext i j
    simp [abs_mul, hsabs, htabs]

/-! ### Theorem 3.1 -/

/-- **Theorem 3.1.** Let `A ∈ ℝ^{n×n}` be nonsingular and tridiagonal. If any of the following
conditions hold then `A` has an LU factorization and `|L||U| = |LU|`:
(a) `A` is symmetric positive definite;
(b) `A` is totally nonnegative;
(c) `A` is an M-matrix;
(d) `A` is sign equivalent to a matrix `B` of type (a)–(c), that is, `A = D₁ B D₂` with
`|D₁| = |D₂| = I`.
(The equivalent reformulations of (b) and (c) are `theorem_3_1_b_equiv` and
`theorem_3_1_c_equiv`.) -/
theorem theorem_3_1 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    ∃ L U, IsLU A L U ∧ L.map abs * U.map abs = (L * U).map abs := by
  rcases h with h | h | h | h
  · exact theorem_3_1_a hT h
  · exact theorem_3_1_b hA hT h
  · exact theorem_3_1_c hT h
  · exact theorem_3_1_d hA hT h

/-! ### Versions for every LU factorization

Since the LU factorization of a nonsingular matrix is unique (`IsLU.eq_recurrence`), the
conclusions of Theorem 3.1 hold for *the* LU factors of `A`, i.e. for every LU factorization. -/

lemma IsLU.unique {A L U L' U' : Matrix (Fin n) (Fin n) ℝ} (h : IsLU A L U) (h' : IsLU A L' U')
    (hA : IsUnit A.det) (hT : IsTridiagonal A) : L = L' ∧ U = U' := by
  obtain ⟨-, hL, hU⟩ := h.eq_recurrence hA hT
  obtain ⟨-, hL', hU'⟩ := h'.eq_recurrence hA hT
  exact ⟨hL.trans hL'.symm, hU.trans hU'.symm⟩

/-- **Theorem 3.1**, "the LU factors" form: under the hypotheses of Theorem 3.1, `A` has an LU
factorization, and every LU factorization `A = LU` satisfies `|L||U| = |LU|`. -/
theorem theorem_3_1' (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    (∃ L U, IsLU A L U) ∧ ∀ L U, IsLU A L U → L.map abs * U.map abs = (L * U).map abs := by
  obtain ⟨L₀, U₀, hLU₀, habs₀⟩ := theorem_3_1 A hA hT h
  refine ⟨⟨L₀, U₀, hLU₀⟩, fun L U hLU => ?_⟩
  obtain ⟨rfl, rfl⟩ := hLU.unique hLU₀ hA hT
  exact habs₀

/-- **Theorem 3.1 (b)**, "the LU factors" form: if `A = LU`, then `A` is totally nonnegative iff
`L ≥ 0` and `U ≥ 0`. -/
theorem theorem_3_1_b_equiv' (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) :
    IsTotallyNonneg A ↔ (∀ i j, 0 ≤ L i j) ∧ (∀ i j, 0 ≤ U i j) := by
  rw [theorem_3_1_b_equiv A hA hT]
  constructor
  · rintro ⟨L', U', hLU', hL', hU'⟩
    obtain ⟨rfl, rfl⟩ := hLU.unique hLU' hA hT
    exact ⟨hL', hU'⟩
  · rintro ⟨hL, hU⟩
    exact ⟨L, U, hLU, hL, hU⟩

/-- **Theorem 3.1 (c)**, "the LU factors" form: if `A = LU`, then `A` is an M-matrix iff `L`
and `U` have positive diagonal elements and nonpositive off-diagonal elements. -/
theorem theorem_3_1_c_equiv' (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) :
    IsMMatrix A ↔ (∀ i, 0 < L i i) ∧ (∀ i, 0 < U i i) ∧
      (∀ i j, i ≠ j → L i j ≤ 0) ∧ (∀ i j, i ≠ j → U i j ≤ 0) := by
  rw [theorem_3_1_c_equiv A hA hT]
  constructor
  · rintro ⟨L', U', hLU', h⟩
    obtain ⟨rfl, rfl⟩ := hLU.unique hLU' hA hT
    exact h
  · intro h
    exact ⟨L, U, hLU, h⟩

end Higham
