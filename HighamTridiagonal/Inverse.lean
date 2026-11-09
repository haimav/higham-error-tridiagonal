import HighamTridiagonal.Basic

/-!
# Inverses of bidiagonal matrices

For the bidiagonal factors `L`, `U` of (2.2) we derive the recurrences satisfied by the entries
of `U⁻¹` and `L⁻¹`, and the closed forms (3.6) and (3.7) of the paper:

* (3.6) `(U⁻¹)_{ij} = (1/u_j) ∏_{p=i}^{j-1} (-e_p / u_p)` for `j ≥ i`;
* (3.7) `(L⁻¹)_{ij} = ∏_{p=j}^{i-1} (-l_{p+1})` for `i ≥ j`.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

lemma ent_one {i j : ℕ} (hi : i < n) (hj : j < n) :
    ent (1 : Matrix (Fin n) (Fin n) ℝ) i j = if i = j then 1 else 0 := by
  rw [ent_of_lt _ hi hj, one_apply]
  simp [Fin.ext_iff]

lemma upperBidiag_isUpperTriangular (p e : ℕ → ℝ) :
    (upperBidiag (n := n) p e).IsUpperTriangular := by
  intro i j hij
  have : (j : ℕ) < i := hij
  simp only [upperBidiag, of_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma lowerBidiag_isLowerTriangular (l : ℕ → ℝ) :
    (lowerBidiag (n := n) l).IsLowerTriangular := by
  intro i j hij
  have : (i : ℕ) < j := by simpa using hij
  simp only [lowerBidiag, of_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma det_upperBidiag (p e : ℕ → ℝ) : (upperBidiag (n := n) p e).det = ∏ i : Fin n, p i := by
  rw [det_of_isUpperTriangular (upperBidiag_isUpperTriangular p e)]
  simp [upperBidiag]

lemma det_lowerBidiag (l : ℕ → ℝ) : (lowerBidiag (n := n) l).det = 1 := by
  rw [det_of_isLowerTriangular _ (lowerBidiag_isLowerTriangular l)]
  simp [lowerBidiag]

lemma isUnit_det_upperBidiag {p : ℕ → ℝ} (e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0) :
    IsUnit (upperBidiag (n := n) p e).det := by
  rw [det_upperBidiag, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hp i i.2

lemma isUnit_det_lowerBidiag (l : ℕ → ℝ) : IsUnit (lowerBidiag (n := n) l).det := by
  rw [det_lowerBidiag]; exact isUnit_one

/-! ### `U⁻¹` -/

section UpperInverse

variable {p : ℕ → ℝ} (e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0)
include hp

/-- `U⁻¹` is upper triangular. -/
lemma ent_inv_upperBidiag_of_lt {i j : ℕ} (hij : j < i) :
    ent (upperBidiag (n := n) p e)⁻¹ i j = 0 := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt _ h.1 h.2]
    have := (upperBidiag (n := n) p e).invertibleOfIsUnitDet (isUnit_det_upperBidiag e hp)
    exact blockTriangular_inv_of_blockTriangular (upperBidiag_isUpperTriangular p e)
      (show (⟨j, h.2⟩ : Fin n) < ⟨i, h.1⟩ from hij)
  · simp [ent, h]

lemma inv_upperBidiag_mul : (upperBidiag (n := n) p e)⁻¹ * upperBidiag p e = 1 :=
  nonsing_inv_mul _ (isUnit_det_upperBidiag e hp)

/-- The diagonal of `U⁻¹`: `(U⁻¹)_{ii} = 1 / u_i`. -/
lemma ent_inv_upperBidiag_diag {i : ℕ} (hi : i < n) :
    ent (upperBidiag (n := n) p e)⁻¹ i i = (p i)⁻¹ := by
  have h1 : ent ((upperBidiag (n := n) p e)⁻¹ * upperBidiag p e) i i = ent 1 i i :=
    congrArg (fun M => ent M i i) (inv_upperBidiag_mul e hp)
  rw [ent_one hi hi, ite_eq_left rfl] at h1
  cases i with
  | zero =>
    rw [ent_mul_upperBidiag_zero] at h1
    exact eq_inv_of_mul_eq_one_left h1
  | succ k =>
    rw [ent_mul_upperBidiag_succ _ _ _ hi hi, ent_inv_upperBidiag_of_lt e hp (by omega),
      zero_mul, zero_add] at h1
    exact eq_inv_of_mul_eq_one_left h1

/-- The recurrence for the rows of `U⁻¹`: `(U⁻¹)_{i,k+1} = -(U⁻¹)_{ik} e_k / u_{k+1}` for
`i ≤ k`. -/
lemma ent_inv_upperBidiag_succ {i k : ℕ} (hik : i ≤ k) (hk : k + 1 < n) :
    ent (upperBidiag (n := n) p e)⁻¹ i (k + 1) =
      -(ent (upperBidiag (n := n) p e)⁻¹ i k * e k) / p (k + 1) := by
  have h1 : ent ((upperBidiag (n := n) p e)⁻¹ * upperBidiag p e) i (k + 1) = ent 1 i (k + 1) :=
    congrArg (fun M => ent M i (k + 1)) (inv_upperBidiag_mul e hp)
  rw [ent_one (by omega) hk, ite_eq_right (by omega), ent_mul_upperBidiag_succ _ _ _ (by omega) hk]
    at h1
  have hpk := hp (k + 1) hk
  field_simp
  linarith

/-- Closed form (3.6) for the entries of `U⁻¹`. -/
theorem ent_inv_upperBidiag_eq_prod {i j : ℕ} (hij : i ≤ j) (hj : j < n) :
    ent (upperBidiag (n := n) p e)⁻¹ i j = (p j)⁻¹ * ∏ q ∈ Finset.Ico i j, (-e q / p q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simpa using ent_inv_upperBidiag_diag e hp (i := i) (by simpa using hj)
  | succ d ih =>
    rw [← add_assoc, ent_inv_upperBidiag_succ e hp (by omega) (by omega),
      ih (by omega) (by omega), Finset.prod_Ico_succ_top (by omega)]
    have h1 := hp (i + d) (by omega)
    have h2 := hp (i + d + 1) (by omega)
    field_simp

end UpperInverse

/-! ### `L⁻¹` -/

section LowerInverse

variable (l : ℕ → ℝ)

/-- `L⁻¹` is lower triangular. -/
lemma ent_inv_lowerBidiag_of_lt {i j : ℕ} (hij : i < j) :
    ent (lowerBidiag (n := n) l)⁻¹ i j = 0 := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt _ h.1 h.2]
    have := (lowerBidiag (n := n) l).invertibleOfIsUnitDet (isUnit_det_lowerBidiag l)
    exact blockTriangular_inv_of_blockTriangular (lowerBidiag_isLowerTriangular l)
      (show OrderDual.toDual (⟨j, h.2⟩ : Fin n) < OrderDual.toDual ⟨i, h.1⟩ from hij)
  · simp [ent, h]

lemma lowerBidiag_mul_inv : lowerBidiag (n := n) l * (lowerBidiag l)⁻¹ = 1 :=
  mul_nonsing_inv _ (isUnit_det_lowerBidiag l)

/-- The diagonal of `L⁻¹` consists of ones. -/
lemma ent_inv_lowerBidiag_diag {i : ℕ} (hi : i < n) :
    ent (lowerBidiag (n := n) l)⁻¹ i i = 1 := by
  have h1 : ent (lowerBidiag (n := n) l * (lowerBidiag l)⁻¹) i i = ent 1 i i :=
    congrArg (fun M => ent M i i) (lowerBidiag_mul_inv (n := n) l)
  rw [ent_one hi hi, ite_eq_left rfl] at h1
  cases i with
  | zero => rwa [ent_lowerBidiag_mul_zero] at h1
  | succ k =>
    rwa [ent_lowerBidiag_mul_succ _ _ hi hi, ent_inv_lowerBidiag_of_lt l (by omega), mul_zero,
      zero_add] at h1

/-- The recurrence for the columns of `L⁻¹`: `(L⁻¹)_{k+1,j} = -l_{k+1} (L⁻¹)_{kj}` for
`j ≤ k`. -/
lemma ent_inv_lowerBidiag_succ {j k : ℕ} (hjk : j ≤ k) (hk : k + 1 < n) :
    ent (lowerBidiag (n := n) l)⁻¹ (k + 1) j = -(l (k + 1) * ent (lowerBidiag (n := n) l)⁻¹ k j) := by
  have h1 : ent (lowerBidiag (n := n) l * (lowerBidiag l)⁻¹) (k + 1) j = ent 1 (k + 1) j :=
    congrArg (fun M => ent M (k + 1) j) (lowerBidiag_mul_inv (n := n) l)
  rw [ent_one hk (by omega), ite_eq_right (by omega), ent_lowerBidiag_mul_succ _ _ hk (by omega)] at h1
  linarith

/-- Closed form (3.7) for the entries of `L⁻¹`. -/
theorem ent_inv_lowerBidiag_eq_prod {i j : ℕ} (hji : j ≤ i) (hi : i < n) :
    ent (lowerBidiag (n := n) l)⁻¹ i j = ∏ q ∈ Finset.Ico j i, (-l (q + 1)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
  induction d with
  | zero => simpa using ent_inv_lowerBidiag_diag (n := n) l (i := j) (by simpa using hi)
  | succ d ih =>
    rw [← add_assoc, ent_inv_lowerBidiag_succ l (by omega) (by omega), ih (by omega) (by omega),
      Finset.prod_Ico_succ_top (by omega)]
    ring

end LowerInverse

/-! ### Sign patterns of the inverses -/

/-- If `u_i > 0` and `e_i ≤ 0` then `U⁻¹ ≥ 0`. -/
lemma ent_inv_upperBidiag_nonneg {p e : ℕ → ℝ} (hp : ∀ i, i < n → 0 < p i)
    (he : ∀ i, i + 1 < n → e i ≤ 0) (i j : ℕ) : 0 ≤ ent (upperBidiag (n := n) p e)⁻¹ i j := by
  have hp' : ∀ i, i < n → p i ≠ 0 := fun i hi => (hp i hi).ne'
  rcases lt_or_ge j i with hji | hij
  · rw [ent_inv_upperBidiag_of_lt e hp' hji]
  by_cases hj : j < n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction d with
    | zero => rw [add_zero, ent_inv_upperBidiag_diag e hp' (by omega)]; exact (inv_pos.mpr (hp i (by omega))).le
    | succ d ih =>
      rw [← add_assoc, ent_inv_upperBidiag_succ e hp' (by omega) (by omega)]
      apply div_nonneg _ (hp _ (by omega)).le
      have := mul_nonpos_of_nonneg_of_nonpos (ih (by omega) (by omega)) (he (i + d) (by omega))
      linarith
  · rw [ent_of_not_lt_right _ hj]

/-- If `l_i ≤ 0` then `L⁻¹ ≥ 0`. -/
lemma ent_inv_lowerBidiag_nonneg {l : ℕ → ℝ} (hl : ∀ i, i + 1 < n → l (i + 1) ≤ 0) (i j : ℕ) :
    0 ≤ ent (lowerBidiag (n := n) l)⁻¹ i j := by
  rcases lt_or_ge i j with hij | hji
  · rw [ent_inv_lowerBidiag_of_lt l hij]
  by_cases hi : i < n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hji
    induction d with
    | zero => rw [add_zero, ent_inv_lowerBidiag_diag l (by omega)]; exact zero_le_one
    | succ d ih =>
      rw [← add_assoc, ent_inv_lowerBidiag_succ l (by omega) (by omega)]
      have := mul_nonpos_of_nonpos_of_nonneg (hl (j + d) (by omega)) (ih (by omega) (by omega))
      linarith
  · rw [ent_of_not_lt_left _ hi]

end Higham
