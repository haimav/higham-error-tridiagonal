import HighamTridiagonal.Theorem32
import HighamTridiagonal.Theorem33
import HighamTridiagonal.Condition
import HighamTridiagonal.DiagDominant

/-!
# Further statements of the paper

* (1.2): the normwise forward error bound obtained from a normwise backward error by standard
  perturbation theory (`eq_1_2`), with `κ∞(A) = ‖A‖∞ ‖A⁻¹‖∞` (`∞`-operator norm, i.e. maximal row
  sum, Mathlib's `Matrix.linftyOpNormedAddCommGroup`).
* Section 1: `cond(A, x) ≤ κ∞(A)` (`condSkeel_le_kappa`) and `cond(A, x)` is invariant under row
  scaling (`condSkeel_diagonal_mul`).
* (6.1): the forward error bound obtained from (1.5) and (3.4) for the matrices of Theorem 3.2
  (`forward_error_bound`), and the numerical value of its constant for the test problem
  (`constant_6_1`).
* Section 4: the bound of Theorem 4.2 is exact for the matrices of Theorem 3.1
  (`bound_exact_of_type`).
-/

open Matrix Finset Filter

noncomputable section

namespace Higham

variable {n : ℕ}

section OperatorNorm

open scoped Matrix.Norms.Operator

/-- The `∞`-norm condition number `κ∞(A) = ‖A‖∞ ‖A⁻¹‖∞`. -/
def kappaInf (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ‖A‖ * ‖A⁻¹‖

lemma linfty_norm_map_abs (A : Matrix (Fin n) (Fin n) ℝ) : ‖A.map abs‖ = ‖A‖ := by
  rw [linfty_opNorm_def, linfty_opNorm_def]
  simp

/-- **(1.2)** Standard (normwise) perturbation theory: if `A x = b`, `(A + F) x̂ = b`,
`‖F‖∞ ≤ ε ‖A‖∞` (in the paper `ε = ρ_n p(n) u`, from (1.1)) and `κ∞(A) ε < 1`, then
`‖x - x̂‖∞ / ‖x‖∞ ≤ κ∞(A) ε / (1 - κ∞(A) ε)`. -/
theorem eq_1_2 (A F : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (x xhat b : Fin n → ℝ)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hxhat : (A + F) *ᵥ xhat = b) {ε : ℝ} (hε : 0 ≤ ε)
    (hF : ‖F‖ ≤ ε * ‖A‖) (hκ : kappaInf A * ε < 1) :
    ‖x - xhat‖ / ‖x‖ ≤ kappaInf A * ε / (1 - kappaInf A * ε) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set d := x - xhat with hd
  have hdeq : d = A⁻¹ *ᵥ (F *ᵥ xhat) := by
    have h1 : A *ᵥ d = F *ᵥ xhat := by
      rw [hd, mulVec_sub, hx, ← hxhat, add_mulVec]; abel
    rw [← h1, mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
  have hxhat_le : ‖xhat‖ ≤ ‖x‖ + ‖d‖ := by
    have : xhat = x - d := by rw [hd]; abel
    rw [this]; exact norm_sub_le _ _
  have hκ0 : 0 ≤ kappaInf A := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ‖d‖ ≤ kappaInf A * ε * (‖x‖ + ‖d‖) := by
    calc ‖d‖ = ‖A⁻¹ *ᵥ (F *ᵥ xhat)‖ := by rw [hdeq]
      _ ≤ ‖A⁻¹‖ * ‖F *ᵥ xhat‖ := linfty_opNorm_mulVec _ _
      _ ≤ ‖A⁻¹‖ * (‖F‖ * ‖xhat‖) :=
          mul_le_mul_of_nonneg_left (linfty_opNorm_mulVec _ _) (norm_nonneg _)
      _ ≤ ‖A⁻¹‖ * ((ε * ‖A‖) * (‖x‖ + ‖d‖)) := by
          gcongr
      _ = kappaInf A * ε * (‖x‖ + ‖d‖) := by rw [kappaInf]; ring
  have hpos : 0 < 1 - kappaInf A * ε := by linarith
  rw [div_le_div_iff₀ hxpos hpos]
  nlinarith [norm_nonneg d]

/-- `cond(A, x) ≤ κ∞(A)` (Section 1). -/
theorem condSkeel_le_kappa (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ≠ 0) :
    condSkeel A x ≤ kappaInf A := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [condSkeel, div_le_iff₀ hxpos, kappaInf]
  calc ‖(A⁻¹.map abs * A.map abs) *ᵥ (fun i => |x i|)‖
      ≤ ‖A⁻¹.map abs * A.map abs‖ * ‖fun i => |x i|‖ := linfty_opNorm_mulVec _ _
    _ ≤ ‖A⁻¹.map abs‖ * ‖A.map abs‖ * ‖fun i => |x i|‖ :=
        mul_le_mul_of_nonneg_right (linfty_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖A‖ * ‖A⁻¹‖ * ‖x‖ := by
        rw [linfty_norm_map_abs, linfty_norm_map_abs]
        have : ‖fun i => |x i|‖ = ‖x‖ := by
          simp only [Pi.norm_def]
          congr 2
          ext i
          simp
        rw [this]; ring

end OperatorNorm

/-- `cond(A, x)` is invariant under row scaling of `A` (Section 1). -/
theorem condSkeel_diagonal_mul (A : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (x : Fin n → ℝ) :
    condSkeel (diagonal d * A) x = condSkeel A x := by
  have hD : IsUnit (diagonal d).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hDinv : (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    convert diagonal_one with i
    exact inv_mul_cancel₀ (hd i)
  have key : ((diagonal d * A)⁻¹).map abs * (diagonal d * A).map abs = A⁻¹.map abs * A.map abs := by
    rw [Matrix.mul_inv_rev, hDinv]
    ext i j
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_apply, mul_diagonal, diagonal_mul, abs_mul, abs_inv]
    field_simp [abs_ne_zero.mpr (hd k)]
  rw [condSkeel, condSkeel, key]

/-- **(1.4)** If a backward error satisfies `|E| ≤ c_n u |L̂||Û|` (as in (1.3)) and
`|L̂||Û| ≤ c'_n |A|`, then `|E| ≤ c''_n u |A|` with `c''_n = c_n c'_n`. -/
theorem eq_1_4 (A E Lh Uh : Matrix (Fin n) (Fin n) ℝ) {c c' u : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hE : ∀ i j, |E i j| ≤ c * u * (Lh.map abs * Uh.map abs) i j)
    (hLU : ∀ i j, (Lh.map abs * Uh.map abs) i j ≤ c' * |A i j|) :
    ∀ i j, |E i j| ≤ (c * c') * u * |A i j| := by
  intro i j
  calc |E i j| ≤ c * u * (Lh.map abs * Uh.map abs) i j := hE i j
    _ ≤ c * u * (c' * |A i j|) := mul_le_mul_of_nonneg_left (hLU i j) (mul_nonneg hc hu)
    _ = (c * c') * u * |A i j| := by ring

/-! ### The forward error bound (6.1) -/

/-- **(6.1)**, general form: for the matrices of Theorem 3.2 and `u` small enough, combining (1.5)
with the componentwise backward error bound (3.4) gives
`‖x - x̂‖∞ / ‖x‖∞ ≤ cond(A, x) h(u) / (1 - cond(A) h(u))`, `h(u) = (4u + 3u² + u³)/(1 - u)`.
(For the paper's test problem `h(u)/(1 - cond(A) h(u)) ≈ 10.9 u`, see `constant_6_1`.) -/
theorem forward_error_bound (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ (u : ℝ) (fp : FPModel u), u < u₀ → ∀ x : Fin n → ℝ, x ≠ 0 →
      condSkeelA A * ((4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u)) < 1 →
      ‖x - fp.solve A (A *ᵥ x)‖ / ‖x‖ ≤
        condSkeel A x * ((4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u)) /
          (1 - condSkeelA A * ((4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u))) := by
  obtain ⟨u₀, hu₀, hgood⟩ := theorem_3_2 A hA hT h
  refine ⟨min u₀ 1, lt_min hu₀ one_pos, fun u fp hu x hx hc => ?_⟩
  obtain ⟨-, F, hF, hFb⟩ := hgood u fp (lt_of_lt_of_le hu (min_le_left _ _)) (A *ᵥ x)
  have hu0 := fp.u_nonneg
  have hu1 : u < 1 := lt_of_lt_of_le hu (min_le_right _ _)
  have hh : 0 ≤ (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) :=
    div_nonneg (by positivity) (by linarith)
  exact eq_1_5 A F hA x (fp.solve A (A *ᵥ x)) (A *ᵥ x) rfl hx hF hh hFb hc

/-- The constant in (6.1): for the test problem (`u = 2⁻²³`, `cond(A) = 1.33·10⁶`) the factor
`h(u) / (1 - cond(A) h(u))` equals `10.93…·u`, which the paper reports as `10.9 u`. -/
theorem constant_6_1 :
    let u : ℝ := 2⁻¹ ^ 23
    let h : ℝ := (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u)
    10.93 * u ≤ h / (1 - 1.33e6 * h) ∧ h / (1 - 1.33e6 * h) ≤ 10.94 * u := by
  norm_num

/-! ### Exactness of the bound of Theorem 4.2 for the matrices of Theorem 3.1 -/

/-- For the matrices of Theorem 3.1 (types (a)–(d)), `|U⁻¹||L⁻¹| = |A⁻¹|`, so the upper bound
`|U⁻¹||L⁻¹| y` of Section 4 equals `|A⁻¹| y` ("the bound is exact"). -/
theorem bound_exact_of_type (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) (y : Fin n → ℝ) :
    (U⁻¹.map abs * L⁻¹.map abs) *ᵥ y = A⁻¹.map abs *ᵥ y := by
  obtain ⟨L', U', hLU', habs'⟩ := theorem_3_1 A hA hT h
  -- the LU factorization is unique
  obtain ⟨-, hL, hU⟩ := hLU.eq_recurrence hA hT
  obtain ⟨-, hL', hU'⟩ := hLU'.eq_recurrence hA hT
  have habs : L.map abs * U.map abs = A.map abs := by
    rw [hL, hU, ← hL', ← hU', habs', ← hLU'.eq]
  rw [theorem_3_3 A L U hA hT hLU habs]

/-- §6: for any LU factorization `|A| ≤ |L||U|`; hence `|A| = |L||U|` for the matrices of
Theorem 3.1 and `|A| ≤ |L||U| ≤ 3|A|` for those of Theorem 4.1. -/
theorem abs_le_abs_mul_abs_of_isLU {A L U : Matrix (Fin n) (Fin n) ℝ} (hLU : IsLU A L U)
    (i j : Fin n) : |A i j| ≤ (L.map abs * U.map abs) i j := by
  rw [hLU.eq]; exact abs_mul_le_abs_mul_abs L U i j

end Higham
