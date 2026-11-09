import HighamTridiagonal.Basic

/-!
# Leading principal minors of tridiagonal matrices

For a tridiagonal matrix the leading principal minors `D_m` satisfy the three-term recurrence
`D_{m+2} = d_{m+1} D_{m+1} - c_{m+1} e_m D_m`, and the pivots of Gaussian elimination are the
ratios `u_k = D_{k+1} / D_k`.  These facts are used to prove positivity of the pivots for the
matrix classes of Theorem 3.1.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- The determinant of the leading `m × m` block of the "matrix" `T : ℕ → ℕ → ℝ`. -/
def detBlock (T : ℕ → ℕ → ℝ) (m : ℕ) : ℝ := (Matrix.of fun i j : Fin m => T i j).det

lemma detBlock_zero (T : ℕ → ℕ → ℝ) : detBlock T 0 = 1 := by
  simp [detBlock]

lemma detBlock_one (T : ℕ → ℕ → ℝ) : detBlock T 1 = T 0 0 := by
  simp [detBlock]

/-- The three-term recurrence for the leading principal minors of a tridiagonal matrix. -/
theorem detBlock_succ_succ (T : ℕ → ℕ → ℝ) (hT : ∀ i j, i + 1 < j ∨ j + 1 < i → T i j = 0)
    (m : ℕ) :
    detBlock T (m + 2) = T (m + 1) (m + 1) * detBlock T (m + 1) -
      T (m + 1) m * T m (m + 1) * detBlock T m := by
  unfold detBlock
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := Matrix.of fun i j : Fin (m + 2) => T i j
    with hM
  rw [det_succ_row M (Fin.last (m + 1)), Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  -- the terms with column index `< m` vanish
  have hzero : ∀ j : Fin m, (-1 : ℝ) ^ ((Fin.last (m + 1) : ℕ) + (j.castSucc.castSucc : ℕ)) *
      M (Fin.last (m + 1)) j.castSucc.castSucc *
      (M.submatrix (Fin.last (m + 1)).succAbove j.castSucc.castSucc.succAbove).det = 0 := by
    intro j
    have : M (Fin.last (m + 1)) j.castSucc.castSucc = 0 := by
      simp only [hM, of_apply, Fin.val_last, Fin.val_castSucc]
      exact hT _ _ (Or.inr (by omega))
    rw [this, mul_zero, zero_mul]
  rw [Finset.sum_eq_zero (fun j _ => hzero j), zero_add]
  -- the last term
  have hlast : M.submatrix (Fin.last (m + 1)).succAbove (Fin.last (m + 1)).succAbove =
      Matrix.of fun i j : Fin (m + 1) => T i j := by
    ext i j
    simp [hM, Fin.succAbove_last]
  -- the term with column index `m`
  have hmid : (M.submatrix (Fin.last (m + 1)).succAbove (Fin.last m).castSucc.succAbove).det =
      T m (m + 1) * (Matrix.of fun i j : Fin m => T i j).det := by
    set N := M.submatrix (Fin.last (m + 1)).succAbove (Fin.last m).castSucc.succAbove with hN
    rw [det_succ_column N (Fin.last m), Fin.sum_univ_castSucc]
    have hz : ∀ a : Fin m, (-1 : ℝ) ^ ((a.castSucc : ℕ) + (Fin.last m : ℕ)) *
        N a.castSucc (Fin.last m) *
        (N.submatrix a.castSucc.succAbove (Fin.last m).succAbove).det = 0 := by
      intro a
      have : N a.castSucc (Fin.last m) = 0 := by
        simp only [hN, submatrix_apply, Fin.succAbove_last, Fin.succAbove_castSucc_self, hM,
          of_apply, Fin.val_castSucc, Fin.val_succ, Fin.val_last]
        exact hT _ _ (Or.inl (by omega))
      rw [this, mul_zero, zero_mul]
    rw [Finset.sum_eq_zero (fun a _ => hz a), zero_add]
    have hsub : N.submatrix (Fin.last m).succAbove (Fin.last m).succAbove =
        Matrix.of fun i j : Fin m => T i j := by
      ext i j
      simp only [hN, submatrix_apply, Fin.succAbove_last, hM, of_apply]
      rw [Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last j)]
      simp
    have hentry : N (Fin.last m) (Fin.last m) = T m (m + 1) := by
      simp [hN, hM, Fin.succAbove_last]
    rw [hsub, hentry, Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hlast, hmid]
  simp only [Fin.val_last, Fin.val_castSucc, hM, of_apply]
  have h1 : ((-1 : ℝ) ^ (m + 1 + m)) = -1 := by
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; simp
  have h2 : ((-1 : ℝ) ^ (m + 1 + (m + 1))) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [h1, h2]
  ring

/-- The leading principal minor `D_m` of order `m` of `A`. -/
def leadMinor (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ := detBlock (ent A) m

lemma leadMinor_zero (A : Matrix (Fin n) (Fin n) ℝ) : leadMinor A 0 = 1 := detBlock_zero _

lemma leadMinor_one (A : Matrix (Fin n) (Fin n) ℝ) : leadMinor A 1 = ent A 0 0 :=
  detBlock_one _

lemma leadMinor_eq_det_submatrix (A : Matrix (Fin n) (Fin n) ℝ) {m : ℕ} (hm : m ≤ n) :
    leadMinor A m = (A.submatrix (Fin.castLE hm) (Fin.castLE hm)).det := by
  unfold leadMinor detBlock
  congr 1
  ext i j
  simp [ent_of_lt A (lt_of_lt_of_le i.2 hm) (lt_of_lt_of_le j.2 hm)]
  rfl

lemma leadMinor_self (A : Matrix (Fin n) (Fin n) ℝ) : leadMinor A n = A.det := by
  unfold leadMinor detBlock
  congr 1
  ext i j
  simp

theorem leadMinor_succ_succ {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) (m : ℕ) :
    leadMinor A (m + 2) = ent A (m + 1) (m + 1) * leadMinor A (m + 1) -
      ent A (m + 1) m * ent A m (m + 1) * leadMinor A m :=
  detBlock_succ_succ _ (fun _ _ h => hT.ent_eq_zero h) m

/-- The pivots are ratios of consecutive leading principal minors: `u_k D_k = D_{k+1}` as long
as `D_0, …, D_k` are nonzero. -/
theorem piv_mul_leadMinor {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) :
    ∀ k, (∀ j, j ≤ k → leadMinor A j ≠ 0) → piv A k * leadMinor A k = leadMinor A (k + 1) := by
  intro k
  induction k with
  | zero => intro _; simp [leadMinor_zero, leadMinor_one]
  | succ k ih =>
    intro hD
    have ih' := ih fun j hj => hD j (by omega)
    have hDk := hD k (by omega)
    have hDk1 := hD (k + 1) le_rfl
    have hpk : piv A k ≠ 0 := by
      intro h0; rw [h0, zero_mul] at ih'; exact hDk1 ih'.symm
    rw [leadMinor_succ_succ hT k, piv_succ, mult_succ, ← ih']
    field_simp

/-- If all leading principal minors `D_0, …, D_n` are positive, all pivots are positive. -/
theorem piv_pos_of_leadMinor_pos {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (hD : ∀ m, m ≤ n → 0 < leadMinor A m) : ∀ k, k < n → 0 < piv A k := by
  intro k hk
  have h := piv_mul_leadMinor hT k fun j hj => (hD j (by omega)).ne'
  have hk0 := hD k (by omega)
  have hk1 := hD (k + 1) hk
  by_contra hneg
  replace hneg := not_lt.mp hneg
  have : piv A k * leadMinor A k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hk0.le
  linarith

end Higham
