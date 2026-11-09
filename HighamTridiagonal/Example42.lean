import HighamTridiagonal.DiagDominant

/-!
# Sharpness of Theorem 4.2 for `n = 2`

Section 4 of the paper: "For `n = 2` the bound in Theorem 4.2 is attained as `α → ∞` in the
example `A = [1 1; -α α+1]`, `y = e`."

We show that for every `α ≥ 0` this `A` satisfies the hypotheses of Theorem 4.2, with LU factors
`L = [1 0; -α 1]`, `U = [1 1; 0 2α+1]`, and that
`‖ |U⁻¹||L⁻¹| e ‖∞ / ‖ |A⁻¹| e ‖∞ = (3α + 2)/(α + 2) → 3 = 2n - 1` as `α → ∞`.
-/

open Matrix Finset Filter Topology

noncomputable section

namespace Higham

/-- The matrix of the example. -/
def exA (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -α, α + 1]

/-- Its unit lower triangular factor. -/
def exL (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -α, 1]

/-- Its upper triangular factor. -/
def exU (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 2 * α + 1]

lemma exA_isTridiagonal (α : ℝ) : IsTridiagonal (exA α) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h

lemma exA_rowDD {α : ℝ} (hα : 0 ≤ α) : IsRowDiagDominant (exA α) := by
  intro i
  fin_cases i
  · simp [exA, Finset.sum_erase_eq_sub, Fin.sum_univ_two]
  · have h1 : |α + 1| = α + 1 := abs_of_nonneg (by linarith)
    simp [exA, Finset.sum_erase_eq_sub, Fin.sum_univ_two, abs_of_nonneg hα, h1]

lemma exA_det (α : ℝ) : (exA α).det = 2 * α + 1 := by
  simp [exA, det_fin_two]; ring

lemma exA_isUnit_det {α : ℝ} (hα : 0 ≤ α) : IsUnit (exA α).det := by
  rw [exA_det, isUnit_iff_ne_zero]; linarith

lemma exA_isLU (α : ℝ) : IsLU (exA α) (exL α) (exU α) where
  lower i j h := by fin_cases i <;> fin_cases j <;> simp_all [exL]
  unit_diag i := by fin_cases i <;> simp [exL]
  upper i j h := by fin_cases i <;> fin_cases j <;> simp_all [exU]
  eq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [exA, exL, exU, mul_apply, Fin.sum_univ_two]
    ring

lemma exL_inv (α : ℝ) : (exL α)⁻¹ = !![1, 0; α, 1] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exL, mul_apply, Fin.sum_univ_two]

lemma exU_inv {α : ℝ} (hα : 0 ≤ α) :
    (exU α)⁻¹ = !![1, -1 / (2 * α + 1); 0, 1 / (2 * α + 1)] := by
  have hs : 2 * α + 1 ≠ 0 := by linarith
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exU, mul_apply, Fin.sum_univ_two] <;> field_simp
  ring

lemma exA_inv {α : ℝ} (hα : 0 ≤ α) :
    (exA α)⁻¹ = !![(α + 1) / (2 * α + 1), -1 / (2 * α + 1); α / (2 * α + 1), 1 / (2 * α + 1)] := by
  have hs : 2 * α + 1 ≠ 0 := by linarith
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exA, mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

lemma norm_fin_two_of_le {v : Fin 2 → ℝ} (h0 : 0 ≤ v 1) (h1 : v 1 ≤ v 0) : ‖v‖ = v 0 := by
  have hv0 : 0 ≤ v 0 := h0.trans h1
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg hv0).mpr fun i => ?_
    fin_cases i
    · simp [abs_of_nonneg hv0]
    · simp [abs_of_nonneg h0, h1]
  · have := norm_le_pi_norm v 0
    rwa [Real.norm_eq_abs, abs_of_nonneg hv0] at this

lemma ex_upper_norm {α : ℝ} (hα : 0 ≤ α) :
    ‖((exU α)⁻¹.map abs * (exL α)⁻¹.map abs) *ᵥ (fun _ => (1 : ℝ))‖ =
      (3 * α + 2) / (2 * α + 1) := by
  have hs : 0 < 2 * α + 1 := by linarith
  rw [exU_inv hα, exL_inv]
  rw [norm_fin_two_of_le]
  · simp [mulVec, dotProduct, mul_apply, Fin.sum_univ_two, abs_of_nonneg hα,
      abs_div, abs_of_pos hs]
    field_simp
    ring
  · simp [mulVec, dotProduct, mul_apply, Fin.sum_univ_two, abs_of_nonneg hα, abs_of_pos hs]
    positivity
  · simp [mulVec, dotProduct, mul_apply, Fin.sum_univ_two, abs_of_nonneg hα, abs_div,
      abs_of_pos hs]

lemma ex_inv_norm {α : ℝ} (hα : 0 ≤ α) :
    ‖(exA α)⁻¹.map abs *ᵥ (fun _ => (1 : ℝ))‖ = (α + 2) / (2 * α + 1) := by
  have hs : 0 < 2 * α + 1 := by linarith
  rw [exA_inv hα]
  rw [norm_fin_two_of_le]
  · simp [mulVec, dotProduct, Fin.sum_univ_two, abs_div, abs_of_pos hs,
      abs_of_nonneg (show 0 ≤ α + 1 by linarith)]
    field_simp
    ring
  · simp [mulVec, dotProduct, Fin.sum_univ_two, abs_div, abs_of_pos hs]
    positivity
  · simp [mulVec, dotProduct, Fin.sum_univ_two, abs_of_nonneg hα, abs_div, abs_of_pos hs,
      abs_of_nonneg (show 0 ≤ α + 1 by linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- **Sharpness of Theorem 4.2 for `n = 2`.** For every `α ≥ 0` the matrix `A = [1 1; -α α+1]`
satisfies the hypotheses of Theorem 4.2 (with LU factors `L`, `U`), and the ratio
`‖ |U⁻¹||L⁻¹| e ‖∞ / ‖ |A⁻¹| e ‖∞` tends to `2n - 1 = 3` as `α → ∞`. -/
theorem theorem_4_2_sharp_n2 :
    (∀ α : ℝ, 0 ≤ α → IsUnit (exA α).det ∧ IsTridiagonal (exA α) ∧ IsRowDiagDominant (exA α) ∧
      IsLU (exA α) (exL α) (exU α)) ∧
    Tendsto (fun α : ℝ => ‖((exU α)⁻¹.map abs * (exL α)⁻¹.map abs) *ᵥ (fun _ => (1 : ℝ))‖ /
        ‖(exA α)⁻¹.map abs *ᵥ (fun _ => (1 : ℝ))‖) atTop (𝓝 (2 * (2 : ℕ) - 1)) := by
  refine ⟨fun α hα => ⟨exA_isUnit_det hα, exA_isTridiagonal α, exA_rowDD hα, exA_isLU α⟩, ?_⟩
  have heq : ∀ᶠ α : ℝ in atTop, (3 : ℝ) - 4 / (α + 2) =
      ‖((exU α)⁻¹.map abs * (exL α)⁻¹.map abs) *ᵥ (fun _ => (1 : ℝ))‖ /
        ‖(exA α)⁻¹.map abs *ᵥ (fun _ => (1 : ℝ))‖ := by
    filter_upwards [eventually_ge_atTop 0] with α hα
    rw [ex_upper_norm hα, ex_inv_norm hα]
    have h1 : 0 < 2 * α + 1 := by linarith
    have h2 : 0 < α + 2 := by linarith
    field_simp
    ring
  have hlim : Tendsto (fun α : ℝ => (3 : ℝ) - 4 / (α + 2)) atTop (𝓝 3) := by
    have : Tendsto (fun α : ℝ => 4 / (α + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_id)
    simpa using (tendsto_const_nhds (x := (3 : ℝ))).sub this
  have h3 : (2 * ((2 : ℕ) : ℝ) - 1) = 3 := by norm_num
  rw [h3]
  exact hlim.congr' heq

end Higham
