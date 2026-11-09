import Mathlib

/-!
# Tridiagonal matrices and their LU factorization: basic definitions

This file sets up the objects used throughout the formalization of

  N. J. Higham, *Bounding the error in Gaussian elimination for tridiagonal systems*,
  SIAM J. Matrix Anal. Appl. 11 (1990), 521–530.

We work with real `n × n` matrices `Matrix (Fin n) (Fin n) ℝ`.  Indices are `0`-based (the
paper is `1`-based).  In the paper's notation (2.1) a tridiagonal matrix has subdiagonal
`c_i = a_{i,i-1}`, diagonal `d_i = a_{ii}` and superdiagonal `e_i = a_{i,i+1}`; with `0`-based
natural-number indices these are `ent A (i+1) i`, `ent A i i` and `ent A i (i+1)`.

Main definitions:
* `Higham.IsTridiagonal A`
* `Higham.IsLU A L U` : `A = L U` with `L` unit lower triangular and `U` upper triangular.
* `Higham.ent A i j` : the entry `a_{ij}` addressed by natural numbers (zero out of range).
* `Higham.piv A`, `Higham.mult A` : the pivots `u_i` and multipliers `l_i` of the recurrence (2.3).
* `Higham.lowerBidiag l`, `Higham.upperBidiag p e` : the bidiagonal matrices of (2.2).
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-! ### Basic predicates -/

/-- `A` is tridiagonal: `a_{ij} = 0` whenever `|i - j| > 1`. -/
def IsTridiagonal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → A i j = 0

/-- `A = L U` is an LU factorization of `A`: `L` is unit lower triangular and `U` is upper
triangular. -/
structure IsLU (A L U : Matrix (Fin n) (Fin n) ℝ) : Prop where
  lower : ∀ i j : Fin n, i < j → L i j = 0
  unit_diag : ∀ i : Fin n, L i i = 1
  upper : ∀ i j : Fin n, j < i → U i j = 0
  eq : A = L * U

/-! ### Entries addressed by natural numbers -/

/-- The entry `a_{ij}` of `A`, addressed by natural numbers; it is `0` outside the matrix. -/
def ent (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) : ℝ :=
  if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

@[simp] lemma ent_coe (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ent A i j = A i j := by
  simp [ent]

lemma ent_of_lt (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ent A i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [ent, hi, hj]

lemma ent_of_not_lt_left (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hi : ¬ i < n) :
    ent A i j = 0 := by
  simp [ent, hi]

lemma ent_of_not_lt_right (A : Matrix (Fin n) (Fin n) ℝ) {i j : ℕ} (hj : ¬ j < n) :
    ent A i j = 0 := by
  simp [ent, hj]

lemma ent_map (A : Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) (i j : ℕ) :
    ent (A.map f) i j = f (ent A i j) := by
  by_cases h : i < n ∧ j < n
  · simp [ent, h]
  · simp [ent, h, hf]

lemma ent_abs (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    ent (A.map abs) i j = |ent A i j| := ent_map A abs abs_zero i j

lemma ent_add (A B : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    ent (A + B) i j = ent A i j + ent B i j := by
  by_cases h : i < n ∧ j < n
  · simp [ent, h]
  · simp [ent, h]

lemma ent_sub (A B : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    ent (A - B) i j = ent A i j - ent B i j := by
  by_cases h : i < n ∧ j < n
  · simp [ent, h]
  · simp [ent, h]

lemma ent_neg (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    ent (-A) i j = -ent A i j := by
  by_cases h : i < n ∧ j < n
  · simp [ent, h]
  · simp [ent, h]

lemma ent_transpose (A : Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) :
    ent Aᵀ i j = ent A j i := by
  by_cases h : i < n ∧ j < n
  · simp [ent, h]
  · rw [ent, dite_eq_right h, ent, dite_eq_right (by tauto)]

/-- Two matrices are equal iff all their `ent`-entries agree. -/
lemma ext_ent {A B : Matrix (Fin n) (Fin n) ℝ} (h : ∀ i j, i < n → j < n → ent A i j = ent B i j) :
    A = B := by
  ext i j
  simpa using h i j i.2 j.2

lemma IsTridiagonal.ent_eq_zero {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) {i j : ℕ}
    (hij : i + 1 < j ∨ j + 1 < i) : ent A i j = 0 := by
  by_cases h : i < n ∧ j < n
  · rw [ent_of_lt A h.1 h.2]
    exact hT ⟨i, h.1⟩ ⟨j, h.2⟩ hij
  · simp [ent, h]

lemma isTridiagonal_iff_ent (A : Matrix (Fin n) (Fin n) ℝ) :
    IsTridiagonal A ↔ ∀ i j : ℕ, i + 1 < j ∨ j + 1 < i → ent A i j = 0 := by
  refine ⟨fun h i j hij => h.ent_eq_zero hij, fun h i j hij => ?_⟩
  simpa using h i j hij

/-- Tridiagonal matrices are determined by their three diagonals. -/
lemma IsTridiagonal.ext {A B : Matrix (Fin n) (Fin n) ℝ} (hA : IsTridiagonal A)
    (hB : IsTridiagonal B) (hd : ∀ i, i < n → ent A i i = ent B i i)
    (hl : ∀ i, i + 1 < n → ent A (i + 1) i = ent B (i + 1) i)
    (hu : ∀ i, i + 1 < n → ent A i (i + 1) = ent B i (i + 1)) : A = B := by
  apply ext_ent
  intro i j hi hj
  rcases lt_trichotomy (i + 1) j with h | h | h
  · rw [hA.ent_eq_zero (Or.inl h), hB.ent_eq_zero (Or.inl h)]
  · subst h; exact hu i hj
  rcases lt_trichotomy (j + 1) i with h' | h' | h'
  · rw [hA.ent_eq_zero (Or.inr h'), hB.ent_eq_zero (Or.inr h')]
  · subst h'; exact hl j hi
  · have : i = j := by omega
    subst this; exact hd i hi

/-! ### The recurrence (2.3) -/

/-- The pivots `u_i` produced by Gaussian elimination on a tridiagonal matrix, recurrence (2.3):
`u_0 = d_0`, `u_{i+1} = d_{i+1} - l_{i+1} e_i` with `l_{i+1} = c_{i+1} / u_i`. -/
def piv (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℝ
  | 0 => ent A 0 0
  | i + 1 => ent A (i + 1) (i + 1) - ent A (i + 1) i / piv A i * ent A i (i + 1)

/-- The multipliers `l_i` of the recurrence (2.3): `l_{i+1} = c_{i+1} / u_i` (and `l_0 = 0`, a
dummy value). -/
def mult (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => ent A (i + 1) i / piv A i

/-- The superdiagonal `e_i = a_{i,i+1}` of `A`. -/
def supd (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ := ent A i (i + 1)

@[simp] lemma piv_zero (A : Matrix (Fin n) (Fin n) ℝ) : piv A 0 = ent A 0 0 := rfl

lemma piv_succ (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    piv A (i + 1) = ent A (i + 1) (i + 1) - mult A (i + 1) * ent A i (i + 1) := rfl

@[simp] lemma mult_succ (A : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    mult A (i + 1) = ent A (i + 1) i / piv A i := rfl

/-! ### Bidiagonal matrices (2.2) -/

/-- The unit lower bidiagonal matrix with subdiagonal entries `l`: the `(i+1, i)` entry is
`l (i+1)`. -/
def lowerBidiag (l : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else if (i : ℕ) = j + 1 then l i else 0

/-- The upper bidiagonal matrix with diagonal `p` and superdiagonal `e`: the `(i, i)` entry is
`p i` and the `(i, i+1)` entry is `e i`. -/
def upperBidiag (p e : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then p i else if (j : ℕ) = i + 1 then e i else 0

lemma ent_lowerBidiag (l : ℕ → ℝ) (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (lowerBidiag (n := n) l) i j = if i = j then 1 else if i = j + 1 then l i else 0 := by
  simp [ent, hi, hj, lowerBidiag]

lemma ent_upperBidiag (p e : ℕ → ℝ) (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (upperBidiag (n := n) p e) i j = if i = j then p i else if j = i + 1 then e i else 0 := by
  simp [ent, hi, hj, upperBidiag]

lemma lowerBidiag_map_abs (l : ℕ → ℝ) :
    (lowerBidiag (n := n) l).map abs = lowerBidiag (fun i => |l i|) := by
  ext i j
  simp only [lowerBidiag, map_apply, of_apply]
  split_ifs <;> simp

lemma upperBidiag_map_abs (p e : ℕ → ℝ) :
    (upperBidiag (n := n) p e).map abs = upperBidiag (fun i => |p i|) (fun i => |e i|) := by
  ext i j
  simp only [upperBidiag, map_apply, of_apply]
  split_ifs <;> simp

lemma lowerBidiag_isTridiagonal (l : ℕ → ℝ) : IsTridiagonal (lowerBidiag (n := n) l) := by
  intro i j h
  simp only [lowerBidiag, of_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma upperBidiag_isTridiagonal (p e : ℕ → ℝ) : IsTridiagonal (upperBidiag (n := n) p e) := by
  intro i j h
  simp only [upperBidiag, of_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ### Products with bidiagonal matrices -/

/-- Row `0` of `lowerBidiag l * M`. -/
lemma ent_lowerBidiag_mul_zero (l : ℕ → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) :
    ent (lowerBidiag l * M) 0 j = ent M 0 j := by
  by_cases h : 0 < n ∧ j < n
  · rw [ent_of_lt _ h.1 h.2, ent_of_lt _ h.1 h.2, mul_apply,
      Finset.sum_eq_single ⟨0, h.1⟩]
    · simp [lowerBidiag]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h' => hk (Fin.ext h')
      simp only [lowerBidiag, of_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]
    · simp
  · simp [ent, h]

/-- Row `k+1` of `lowerBidiag l * M`: `(L M)_{k+1, j} = l_{k+1} m_{k j} + m_{k+1, j}`. -/
lemma ent_lowerBidiag_mul_succ (l : ℕ → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) {k j : ℕ}
    (hk : k + 1 < n) (hj : j < n) :
    ent (lowerBidiag l * M) (k + 1) j = l (k + 1) * ent M k j + ent M (k + 1) j := by
  rw [ent_of_lt _ hk hj, ent_of_lt _ hk hj, ent_of_lt _ (by omega) hj, mul_apply,
    Fintype.sum_eq_add (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩]
  · simp [lowerBidiag]
  · simp [Fin.ext_iff]
  · rintro x ⟨hx1, hx2⟩
    have h1 : (x : ℕ) ≠ k := fun h' => hx1 (Fin.ext h')
    have h2 : (x : ℕ) ≠ k + 1 := fun h' => hx2 (Fin.ext h')
    simp only [lowerBidiag, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]

/-- Column `0` of `M * upperBidiag p e`. -/
lemma ent_mul_upperBidiag_zero (p e : ℕ → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) :
    ent (M * upperBidiag p e) i 0 = ent M i 0 * p 0 := by
  by_cases h : i < n ∧ 0 < n
  · rw [ent_of_lt _ h.1 h.2, ent_of_lt _ h.1 h.2, mul_apply,
      Finset.sum_eq_single ⟨0, h.2⟩]
    · simp [upperBidiag]
    · intro k _ hk
      have hk' : (k : ℕ) ≠ 0 := fun h' => hk (Fin.ext h')
      simp only [upperBidiag, of_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
    · simp
  · simp [ent, h]

/-- Column `k+1` of `M * upperBidiag p e`: `(M U)_{i, k+1} = m_{i k} e_k + m_{i, k+1} p_{k+1}`. -/
lemma ent_mul_upperBidiag_succ (p e : ℕ → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) {i k : ℕ}
    (hi : i < n) (hk : k + 1 < n) :
    ent (M * upperBidiag p e) i (k + 1) = ent M i k * e k + ent M i (k + 1) * p (k + 1) := by
  rw [ent_of_lt _ hi hk, ent_of_lt _ hi hk, ent_of_lt _ hi (by omega), mul_apply,
    Fintype.sum_eq_add (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩]
  · simp [upperBidiag]
  · simp [Fin.ext_iff]
  · rintro x ⟨hx1, hx2⟩
    have h1 : (x : ℕ) ≠ k := fun h' => hx1 (Fin.ext h')
    have h2 : (x : ℕ) ≠ k + 1 := fun h' => hx2 (Fin.ext h')
    simp only [upperBidiag, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]


/-! ### Products of the two bidiagonal factors -/

section LUProduct

variable (l p e : ℕ → ℝ)

lemma ent_LU_zero_zero (hn : 0 < n) :
    ent (lowerBidiag (n := n) l * upperBidiag p e) 0 0 = p 0 := by
  rw [ent_lowerBidiag_mul_zero, ent_upperBidiag _ _ _ _ hn hn]; simp

lemma ent_LU_diag_succ {i : ℕ} (hi : i + 1 < n) :
    ent (lowerBidiag (n := n) l * upperBidiag p e) (i + 1) (i + 1) = l (i + 1) * e i + p (i + 1) := by
  rw [ent_lowerBidiag_mul_succ _ _ hi hi, ent_upperBidiag _ _ _ _ (by omega) hi,
    ent_upperBidiag _ _ _ _ hi hi]
  simp

lemma ent_LU_sub {i : ℕ} (hi : i + 1 < n) :
    ent (lowerBidiag (n := n) l * upperBidiag p e) (i + 1) i = l (i + 1) * p i := by
  rw [ent_lowerBidiag_mul_succ _ _ hi (by omega), ent_upperBidiag _ _ _ _ (by omega) (by omega),
    ent_upperBidiag _ _ _ _ hi (by omega)]
  simp [show i ≠ i + 1 + 1 by omega]

lemma ent_LU_sup {i : ℕ} (hi : i + 1 < n) :
    ent (lowerBidiag (n := n) l * upperBidiag p e) i (i + 1) = e i := by
  cases i with
  | zero => rw [ent_lowerBidiag_mul_zero, ent_upperBidiag _ _ _ _ (by omega) hi]; simp
  | succ k =>
    rw [ent_lowerBidiag_mul_succ _ _ (by omega) hi, ent_upperBidiag _ _ _ _ (by omega) hi,
      ent_upperBidiag _ _ _ _ (by omega) hi]
    simp [show k ≠ k + 1 + 1 by omega]

lemma isTridiagonal_LU : IsTridiagonal (lowerBidiag (n := n) l * upperBidiag p e) := by
  rw [isTridiagonal_iff_ent]
  intro i j hij
  by_cases hi : i < n
  · by_cases hj : j < n
    · cases i with
      | zero =>
        rw [ent_lowerBidiag_mul_zero, ent_upperBidiag _ _ _ _ hi hj, ite_eq_right (by omega),
          ite_eq_right (by omega)]
      | succ k =>
        rw [ent_lowerBidiag_mul_succ _ _ hi hj, ent_upperBidiag _ _ _ _ (by omega) hj,
          ent_upperBidiag _ _ _ _ hi hj, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega)]
        ring
    · exact ent_of_not_lt_right _ hj
  · exact ent_of_not_lt_left _ hi

end LUProduct

/-! ### The LU factorization produced by the recurrence (2.3) -/

/-- If the pivots `u_0, …, u_{n-2}` are nonzero, the recurrence (2.3) produces an LU
factorization `A = L U` of the tridiagonal matrix `A`. -/
theorem eq_lowerBidiag_mul_upperBidiag {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hp : ∀ i, i + 1 < n → piv A i ≠ 0) :
    A = lowerBidiag (mult A) * upperBidiag (piv A) (supd A) := by
  refine hT.ext (isTridiagonal_LU _ _ _) ?_ ?_ ?_
  · intro i hi
    cases i with
    | zero => rw [ent_LU_zero_zero _ _ _ hi]; rfl
    | succ k => rw [ent_LU_diag_succ _ _ _ hi, piv_succ]; simp [supd]
  · intro i hi
    rw [ent_LU_sub _ _ _ hi, mult_succ, div_mul_cancel₀ _ (hp i hi)]
  · intro i hi
    rw [ent_LU_sup _ _ _ hi]; rfl

theorem isLU_recurrence {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hp : ∀ i, i + 1 < n → piv A i ≠ 0) :
    IsLU A (lowerBidiag (mult A)) (upperBidiag (piv A) (supd A)) where
  lower i j hij := by
    have : (i : ℕ) < j := hij
    simp only [lowerBidiag, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  unit_diag i := by simp [lowerBidiag]
  upper i j hij := by
    have : (j : ℕ) < i := hij
    simp only [upperBidiag, of_apply]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  eq := eq_lowerBidiag_mul_upperBidiag hT hp

lemma lowerBidiag_congr {l l' : ℕ → ℝ} (h : ∀ i, 0 < i → i < n → l i = l' i) :
    lowerBidiag (n := n) l = lowerBidiag l' := by
  ext i j
  simp only [lowerBidiag, of_apply]
  split_ifs with h1 h2
  · rfl
  · exact h i (by omega) i.2
  · rfl

lemma upperBidiag_congr {p p' e e' : ℕ → ℝ} (hp : ∀ i, i < n → p i = p' i)
    (he : ∀ i, i + 1 < n → e i = e' i) :
    upperBidiag (n := n) p e = upperBidiag p' e' := by
  ext i j
  simp only [upperBidiag, of_apply]
  split_ifs with h1 h2
  · exact hp i i.2
  · exact he i (by omega)
  · rfl

/-! ### Structure of an arbitrary LU factorization of a nonsingular tridiagonal matrix -/

namespace IsLU

variable {A L U : Matrix (Fin n) (Fin n) ℝ}

lemma isLowerTriangular (h : IsLU A L U) : L.IsLowerTriangular := by
  intro i j hij
  exact h.lower i j (by simpa using hij)

lemma isUpperTriangular (h : IsLU A L U) : U.IsUpperTriangular := by
  intro i j hij
  exact h.upper i j hij

lemma det_L (h : IsLU A L U) : L.det = 1 := by
  rw [det_of_isLowerTriangular L h.isLowerTriangular]
  simp [h.unit_diag]

lemma det_eq (h : IsLU A L U) : A.det = U.det := by
  rw [h.eq, det_mul, h.det_L, one_mul]

lemma isUnit_det_U (h : IsLU A L U) (hA : IsUnit A.det) : IsUnit U.det := by
  rwa [← h.det_eq]

lemma isUnit_det_L (h : IsLU A L U) : IsUnit L.det := by
  rw [h.det_L]; exact isUnit_one

lemma diag_U_ne_zero (h : IsLU A L U) (hA : IsUnit A.det) (i : Fin n) : U i i ≠ 0 := by
  have h1 : U.det ≠ 0 := (h.isUnit_det_U hA).ne_zero
  rw [det_of_isUpperTriangular h.isUpperTriangular] at h1
  exact Finset.prod_ne_zero_iff.mp h1 i (Finset.mem_univ _)

/-- `U⁻¹` is upper triangular. -/
lemma inv_U_upper (h : IsLU A L U) (hA : IsUnit A.det) {i j : Fin n} (hij : j < i) :
    U⁻¹ i j = 0 := by
  have := U.invertibleOfIsUnitDet (h.isUnit_det_U hA)
  exact blockTriangular_inv_of_blockTriangular h.isUpperTriangular hij

/-- `L⁻¹` is lower triangular. -/
lemma inv_L_lower (h : IsLU A L U) {i j : Fin n} (hij : i < j) : L⁻¹ i j = 0 := by
  have := L.invertibleOfIsUnitDet h.isUnit_det_L
  exact blockTriangular_inv_of_blockTriangular h.isLowerTriangular (by simpa using hij)

/-- In an LU factorization of a nonsingular tridiagonal matrix, `U` is upper bidiagonal. -/
lemma U_band (h : IsLU A L U) (hT : IsTridiagonal A) {i j : Fin n}
    (hij : (i : ℕ) + 1 < j) : U i j = 0 := by
  have hU : U = L⁻¹ * A := by
    rw [h.eq, ← Matrix.mul_assoc, nonsing_inv_mul _ h.isUnit_det_L, Matrix.one_mul]
  rw [hU, mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ i
  · rw [hT k j (Or.inl (by have : (k : ℕ) ≤ i := hk; omega)), mul_zero]
  · rw [h.inv_L_lower (not_le.mp hk), zero_mul]

/-- In an LU factorization of a nonsingular tridiagonal matrix, `L` is lower bidiagonal. -/
lemma L_band (h : IsLU A L U) (hA : IsUnit A.det) (hT : IsTridiagonal A) {i j : Fin n}
    (hij : (j : ℕ) + 1 < i) : L i j = 0 := by
  have hL : L = A * U⁻¹ := by
    rw [h.eq, Matrix.mul_assoc, mul_nonsing_inv _ (h.isUnit_det_U hA), Matrix.mul_one]
  rw [hL, mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ j
  · rw [hT i k (Or.inr (by have : (k : ℕ) ≤ j := hk; omega)), zero_mul]
  · rw [h.inv_U_upper hA (not_le.mp hk), mul_zero]

/-- **Uniqueness.** Any LU factorization of a nonsingular tridiagonal matrix is the one produced
by the recurrence (2.3); in particular `L` and `U` have the bidiagonal form (2.2) and all pivots
are nonzero. -/
theorem eq_recurrence (h : IsLU A L U) (hA : IsUnit A.det) (hT : IsTridiagonal A) :
    (∀ i, i < n → piv A i ≠ 0) ∧ L = lowerBidiag (mult A) ∧
      U = upperBidiag (piv A) (supd A) := by
  set l' : ℕ → ℝ := fun i => ent L i (i - 1) with hl'
  set p' : ℕ → ℝ := fun i => ent U i i with hp'
  set e' : ℕ → ℝ := fun i => ent U i (i + 1) with he'
  have hL : L = lowerBidiag l' := by
    ext i j
    simp only [lowerBidiag, of_apply, hl']
    split_ifs with h1 h2
    · have : i = j := Fin.ext h1
      subst this; exact h.unit_diag i
    · have : (j : ℕ) = i - 1 := by omega
      rw [← this]; simp
    · rcases lt_or_gt_of_ne (fun h' : i = j => h1 (congrArg _ h')) with h3 | h3
      · exact h.lower i j h3
      · exact h.L_band hA hT (by have : (j : ℕ) < i := h3; omega)
  have hU : U = upperBidiag p' e' := by
    ext i j
    simp only [upperBidiag, of_apply, hp', he']
    split_ifs with h1 h2
    · have : i = j := Fin.ext h1
      subst this; simp
    · rw [← h2]; simp
    · rcases lt_or_gt_of_ne (fun h' : i = j => h1 (congrArg _ h')) with h3 | h3
      · exact h.U_band hT (by have : (i : ℕ) < j := h3; omega)
      · exact h.upper i j h3
  have hAeq : A = lowerBidiag l' * upperBidiag p' e' := by rw [← hL, ← hU]; exact h.eq
  have hp'ne : ∀ i, i < n → p' i ≠ 0 := by
    intro i hi
    simpa [hp', ent_of_lt U hi hi] using h.diag_U_ne_zero hA ⟨i, hi⟩
  -- the recurrence relations satisfied by `l'`, `p'`
  have key : ∀ i, i < n → p' i = piv A i ∧ (0 < i → l' i = mult A i) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨?_, fun h0 => absurd h0 (lt_irrefl 0)⟩
      rw [piv_zero, hAeq, ent_LU_zero_zero _ _ _ hi]
    | succ k ih =>
      intro hk
      obtain ⟨ih1, -⟩ := ih (by omega)
      have hsub : ent A (k + 1) k = l' (k + 1) * p' k := by rw [hAeq, ent_LU_sub _ _ _ hk]
      have hdiag : ent A (k + 1) (k + 1) = l' (k + 1) * e' k + p' (k + 1) := by
        rw [hAeq, ent_LU_diag_succ _ _ _ hk]
      have hsup : ent A k (k + 1) = e' k := by rw [hAeq, ent_LU_sup _ _ _ hk]
      have hl : l' (k + 1) = mult A (k + 1) := by
        rw [mult_succ, ← ih1, hsub, mul_div_cancel_right₀ _ (hp'ne k (by omega))]
      refine ⟨?_, fun _ => hl⟩
      rw [piv_succ, ← hl, hsup, hdiag]; ring
  refine ⟨fun i hi => (key i hi).1 ▸ hp'ne i hi, ?_, ?_⟩
  · rw [hL]; exact lowerBidiag_congr fun i h0 hi => (key i hi).2 h0
  · rw [hU]
    refine upperBidiag_congr (fun i hi => (key i hi).1) fun i hi => ?_
    simp only [he', supd]
    rw [hAeq, ent_LU_sup _ _ _ hi]

end IsLU

/-! ### The sign condition for `|L||U| = |LU|` -/

lemma abs_add_eq_iff_mul_nonneg (a b : ℝ) : |a + b| = |a| + |b| ↔ 0 ≤ a * b := by
  rw [abs_add_eq_add_abs_iff, mul_nonneg_iff]

/-- For bidiagonal factors (2.2), `|L||U| = |LU|` holds iff, for every `i`, `l_{i+1} e_i` and
`u_{i+1}` do not have opposite signs (compare (3.5)). -/
theorem abs_mul_abs_eq_abs_mul_iff (l p e : ℕ → ℝ) :
    (lowerBidiag (n := n) l).map abs * (upperBidiag p e).map abs =
        (lowerBidiag l * upperBidiag p e).map abs ↔
      ∀ i, i + 1 < n → 0 ≤ l (i + 1) * e i * p (i + 1) := by
  rw [lowerBidiag_map_abs, upperBidiag_map_abs]
  constructor
  · intro hEq i hi
    have := congrArg (fun M => ent M (i + 1) (i + 1)) hEq
    rw [ent_LU_diag_succ _ _ _ hi, ent_abs, ent_LU_diag_succ _ _ _ hi, ← abs_mul] at this
    exact (abs_add_eq_iff_mul_nonneg _ _).mp this.symm
  · intro hs
    have hT2 : IsTridiagonal ((lowerBidiag (n := n) l * upperBidiag p e).map abs) := by
      intro i j hij
      simp [isTridiagonal_LU l p e i j hij]
    refine (isTridiagonal_LU _ _ _).ext hT2 ?_ ?_ ?_
    · intro i hi
      rw [ent_abs]
      cases i with
      | zero => rw [ent_LU_zero_zero _ _ _ hi, ent_LU_zero_zero _ _ _ hi]
      | succ k =>
        rw [ent_LU_diag_succ _ _ _ hi, ent_LU_diag_succ _ _ _ hi, ← abs_mul,
          (abs_add_eq_iff_mul_nonneg _ _).mpr (hs k hi)]
    · intro i hi
      rw [ent_abs, ent_LU_sub _ _ _ hi, ent_LU_sub _ _ _ hi, abs_mul]
    · intro i hi
      rw [ent_abs, ent_LU_sup _ _ _ hi, ent_LU_sup _ _ _ hi]

end Higham
