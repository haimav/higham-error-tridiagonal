import HighamTridiagonal.Theorem33
import HighamTridiagonal.Condition
import HighamTridiagonal.FloatingPoint

/-!
# Comparison matrices, the condition (3.5), and the `O(n)` algorithm (3.8)

* For bidiagonal factors, `|U⁻¹| = M(U)⁻¹` and `|L⁻¹| = M(L)⁻¹`, where `M(B)` is the comparison
  matrix (`m_ii = |b_ii|`, `m_ij = -|b_ij|`).
* (3.5): the condition `|L||U| = |LU|`, i.e. `|l_i e_{i-1} + u_i| = |l_i||e_{i-1}| + |u_i|` for
  all `i`.  The paper writes it as `sign(l_i e_{i-1} / u_i) = 1`; that literal form is sufficient
  but not necessary (it fails when `l_i e_{i-1} = 0`, e.g. for diagonal `A`); the exact condition
  is `l_i e_{i-1} / u_i ≥ 0`.  Both facts are proved below.
* (3.8): if `|A⁻¹| = |U⁻¹||L⁻¹|` (e.g. under the hypotheses of Theorem 3.3), then
  `cond(A, x) = ‖w‖_∞ / ‖x‖_∞` where `y = |A||x|`, `M(L) v = y`, `M(U) w = v`; the two bidiagonal
  solves are explicit `O(n)` recurrences.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- The comparison matrix `M(B)`: `(M(B))_{ii} = |b_ii|`, `(M(B))_{ij} = -|b_ij|` for `i ≠ j`. -/
def comparison (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then |B i i| else -|B i j|

lemma comparison_upperBidiag (p e : ℕ → ℝ) :
    comparison (upperBidiag (n := n) p e) = upperBidiag (fun i => |p i|) (fun i => -|e i|) := by
  ext i j
  simp only [comparison, upperBidiag, of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun h'' => h (Fin.ext h'')
    simp only [h, h', ite_false]
    split_ifs <;> simp

lemma comparison_lowerBidiag (l : ℕ → ℝ) :
    comparison (lowerBidiag (n := n) l) = lowerBidiag (fun i => -|l i|) := by
  ext i j
  simp only [comparison, lowerBidiag, of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun h'' => h (Fin.ext h'')
    simp only [h, h', ite_false]
    split_ifs <;> simp

/-- `|U⁻¹| = M(U)⁻¹` for an upper bidiagonal `U` with nonzero diagonal (from (3.6)). -/
theorem abs_inv_upperBidiag {p : ℕ → ℝ} (e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0) :
    (upperBidiag (n := n) p e)⁻¹.map abs = (comparison (upperBidiag (n := n) p e))⁻¹ := by
  have hp' : ∀ i, i < n → |p i| ≠ 0 := fun i hi => abs_ne_zero.mpr (hp i hi)
  rw [comparison_upperBidiag]
  apply ext_ent
  intro i j hi hj
  rw [ent_abs]
  rcases lt_or_ge j i with h | h
  · rw [ent_inv_upperBidiag_of_lt _ hp h, ent_inv_upperBidiag_of_lt _ hp' h, abs_zero]
  · rw [ent_inv_upperBidiag_eq_prod _ hp h hj, ent_inv_upperBidiag_eq_prod _ hp' h hj, abs_mul,
      abs_inv, Finset.abs_prod]
    congr 1
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [abs_div, abs_neg, neg_neg]

/-- `|L⁻¹| = M(L)⁻¹` for a unit lower bidiagonal `L` (from (3.7)). -/
theorem abs_inv_lowerBidiag (l : ℕ → ℝ) :
    (lowerBidiag (n := n) l)⁻¹.map abs = (comparison (lowerBidiag (n := n) l))⁻¹ := by
  rw [comparison_lowerBidiag]
  apply ext_ent
  intro i j hi hj
  rw [ent_abs]
  rcases lt_or_ge i j with h | h
  · rw [ent_inv_lowerBidiag_of_lt _ h, ent_inv_lowerBidiag_of_lt _ h, abs_zero]
  · rw [ent_inv_lowerBidiag_eq_prod _ h hi, ent_inv_lowerBidiag_eq_prod _ h hi, Finset.abs_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [abs_neg, neg_neg]

/-- For the LU factors of a nonsingular tridiagonal matrix, `|U⁻¹| = M(U)⁻¹` and
`|L⁻¹| = M(L)⁻¹`. -/
theorem abs_inv_factors_eq_inv_comparison (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) :
    U⁻¹.map abs = (comparison U)⁻¹ ∧ L⁻¹.map abs = (comparison L)⁻¹ := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  subst hL hU
  exact ⟨abs_inv_upperBidiag _ hp, abs_inv_lowerBidiag _⟩

/-- If `|A⁻¹| = |U⁻¹||L⁻¹|` then `|A⁻¹| y = M(U)⁻¹ M(L)⁻¹ y` (displayed before (3.8)). -/
theorem abs_inv_mulVec_eq_comparison (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) (y : Fin n → ℝ) :
    A⁻¹.map abs *ᵥ y = (comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ y) := by
  obtain ⟨hU, hL⟩ := abs_inv_factors_eq_inv_comparison A L U hA hT hLU
  rw [hinv, hU, hL, mulVec_mulVec]

/-! ### The `O(n)` recurrences for the bidiagonal comparison systems -/

/-- Forward substitution for `M(L) v = y` with `L = lowerBidiag l`:
`v_0 = y_0`, `v_{i+1} = y_{i+1} + |l_{i+1}| v_i`. -/
def solveCompL (l : ℕ → ℝ) (y : Fin n → ℝ) : ℕ → ℝ
  | 0 => vext y 0
  | i + 1 => vext y (i + 1) + |l (i + 1)| * solveCompL l y i

/-- Back substitution for `M(U) w = v` with `U = upperBidiag p e`:
`w_{n-1} = v_{n-1} / |u_{n-1}|`, `w_i = (v_i + |e_i| w_{i+1}) / |u_i|`. -/
def solveCompU (p e : ℕ → ℝ) (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  if _h : i + 1 < n then (v i + |e i| * solveCompU p e v (i + 1)) / |p i| else v i / |p i|
termination_by n - i

lemma lowerBidiag_eq_lowerBidiagG (l : ℕ → ℝ) :
    lowerBidiag (n := n) l = lowerBidiagG (fun _ => 1) l := rfl

theorem comparison_lowerBidiag_mulVec_solveCompL (l : ℕ → ℝ) (y : Fin n → ℝ) :
    comparison (lowerBidiag (n := n) l) *ᵥ (fun i : Fin n => solveCompL l y i) = y := by
  funext ⟨i, hi⟩
  rw [comparison_lowerBidiag, lowerBidiag_eq_lowerBidiagG]
  have hv : ∀ k, k < n → vext (fun i : Fin n => solveCompL l y i) k = solveCompL l y k :=
    fun k hk => by simp [vext, hk]
  cases i with
  | zero =>
    rw [mulVec_lowerBidiagG_zero _ _ _ hi, hv 0 hi]
    simp [solveCompL, vext, hi]
  | succ k =>
    rw [mulVec_lowerBidiagG_succ _ _ _ hi, hv k (by omega), hv (k + 1) hi]
    simp only [solveCompL, vext, dite_eq_left hi]
    ring

theorem comparison_upperBidiag_mulVec_solveCompU {p : ℕ → ℝ} (e : ℕ → ℝ)
    (hp : ∀ i, i < n → p i ≠ 0) (v : ℕ → ℝ) :
    comparison (upperBidiag (n := n) p e) *ᵥ (fun i : Fin n => solveCompU (n := n) p e v i) =
      fun i : Fin n => v i := by
  funext ⟨i, hi⟩
  rw [comparison_upperBidiag, mulVec_upperBidiag _ _ _ hi]
  have hpi : |p i| ≠ 0 := abs_ne_zero.mpr (hp i hi)
  have hw : vext (fun i : Fin n => solveCompU (n := n) p e v i) i = solveCompU (n := n) p e v i := by
    simp [vext, hi]
  rw [hw]
  by_cases h1 : i + 1 < n
  · have hw1 : vext (fun i : Fin n => solveCompU (n := n) p e v i) (i + 1) =
        solveCompU (n := n) p e v (i + 1) := by simp [vext, h1]
    rw [hw1]
    conv_lhs => rw [solveCompU, dite_eq_left h1]
    field_simp
    ring
  · have hw1 : vext (fun i : Fin n => solveCompU (n := n) p e v i) (i + 1) = 0 := by
      simp [vext, h1]
    rw [hw1, solveCompU, dite_eq_right h1]
    field_simp
    ring

/-- The algorithm (3.8) for `cond(A, x)`: form `y = |A||x|`, solve `M(L) v = y` and
`M(U) w = v` by the recurrences above (with the LU factors given by (2.3)), and return
`‖w‖_∞ / ‖x‖_∞`.  Each step of the recurrences costs `O(1)` operations, so `O(n)` in total. -/
def condAlg (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ‖(fun i : Fin n => solveCompU (n := n) (piv A) (supd A)
      (solveCompL (mult A) (A.map abs *ᵥ fun j => |x j|)) i)‖ / ‖x‖

/-- **(3.8)** If the nonsingular tridiagonal matrix `A = LU` satisfies `|L||U| = |A|` (so that
`|A⁻¹| = |U⁻¹||L⁻¹|` by Theorem 3.3), then for any solutions `v`, `w` of `M(L) v = |A||x|` and
`M(U) w = v` we have `cond(A, x) = ‖w‖_∞ / ‖x‖_∞`. -/
theorem eq_3_8 (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (hLU : IsLU A L U) (habs : L.map abs * U.map abs = A.map abs) (x v w : Fin n → ℝ)
    (hv : comparison L *ᵥ v = A.map abs *ᵥ fun i => |x i|) (hw : comparison U *ᵥ w = v) :
    ‖w‖ / ‖x‖ = condSkeel A x := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  have hdetL : IsUnit (comparison L).det := by
    rw [hL, comparison_lowerBidiag]; exact isUnit_det_lowerBidiag _
  have hdetU : IsUnit (comparison U).det := by
    rw [hU, comparison_upperBidiag]
    exact isUnit_det_upperBidiag _ fun i hi => abs_ne_zero.mpr (hp i hi)
  have hv' : v = (comparison L)⁻¹ *ᵥ (A.map abs *ᵥ fun i => |x i|) := by
    rw [← hv, mulVec_mulVec, nonsing_inv_mul _ hdetL, one_mulVec]
  have hw' : w = (comparison U)⁻¹ *ᵥ v := by
    rw [← hw, mulVec_mulVec, nonsing_inv_mul _ hdetU, one_mulVec]
  have hinv := theorem_3_3 A L U hA hT hLU habs
  have : w = (A⁻¹.map abs * A.map abs) *ᵥ fun i => |x i| := by
    rw [hw', hv', ← abs_inv_mulVec_eq_comparison A L U hA hT hLU hinv.symm, mulVec_mulVec]
  rw [this, condSkeel]

/-- **(3.8), algorithmic form.** Under the hypotheses of Theorem 3.3 the `O(n)` algorithm
`condAlg` computes `cond(A, x)` exactly. -/
theorem condAlg_eq_condSkeel (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (habs : L.map abs * U.map abs = A.map abs)
    (x : Fin n → ℝ) : condAlg A x = condSkeel A x := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  apply eq_3_8 A L U hA hT hLU habs x (fun i => solveCompL (mult A) (A.map abs *ᵥ fun j => |x j|) i)
  · rw [hL]; exact comparison_lowerBidiag_mulVec_solveCompL _ _
  · rw [hU]; exact comparison_upperBidiag_mulVec_solveCompU _ hp _

/-! ### The condition (3.5) -/

/-- **(3.5)**, first equivalence in the proof of Theorem 3.3: for the bidiagonal factors (2.2),
`|L||U| = |LU|` iff `|l_i e_{i-1} + u_i| = |l_i||e_{i-1}| + |u_i|` for all `i`, iff
`l_i e_{i-1} / u_i ≥ 0` for all `i` (when the `u_i` are nonzero). -/
theorem eq_3_5 (l p e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0) :
    ((lowerBidiag (n := n) l).map abs * (upperBidiag p e).map abs =
        (lowerBidiag l * upperBidiag p e).map abs ↔
      ∀ i, i + 1 < n → |l (i + 1) * e i + p (i + 1)| = |l (i + 1)| * |e i| + |p (i + 1)|) ∧
    ((lowerBidiag (n := n) l).map abs * (upperBidiag p e).map abs =
        (lowerBidiag l * upperBidiag p e).map abs ↔
      ∀ i, i + 1 < n → 0 ≤ l (i + 1) * e i / p (i + 1)) := by
  rw [abs_mul_abs_eq_abs_mul_iff]
  constructor
  · refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [← abs_mul, abs_add_eq_iff_mul_nonneg]
  · refine forall_congr' fun i => forall_congr' fun hi => ?_
    have hpi := hp (i + 1) hi
    constructor
    · intro h
      rw [show l (i + 1) * e i / p (i + 1) = l (i + 1) * e i * p (i + 1) / p (i + 1) ^ 2 by
        field_simp]
      positivity
    · intro h
      rw [show l (i + 1) * e i * p (i + 1) = l (i + 1) * e i / p (i + 1) * p (i + 1) ^ 2 by
        field_simp]
      positivity

lemma real_sign_eq_one_iff (x : ℝ) : Real.sign x = 1 ↔ 0 < x := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [Real.sign_of_neg hx] at h; norm_num at h
    · rw [hx, Real.sign_zero] at h; norm_num at h
    · exact hx
  · exact Real.sign_of_pos

/-- The literal form of (3.5), `sign(l_i e_{i-1} / u_i) = 1` for all `i`, is sufficient for
`|L||U| = |LU|`. -/
theorem eq_3_5_sign_sufficient (l p e : ℕ → ℝ) (hp : ∀ i, i < n → p i ≠ 0)
    (h : ∀ i, i + 1 < n → Real.sign (l (i + 1) * e i / p (i + 1)) = 1) :
    (lowerBidiag (n := n) l).map abs * (upperBidiag p e).map abs =
      (lowerBidiag l * upperBidiag p e).map abs :=
  ((eq_3_5 l p e hp).2).mpr fun i hi => ((real_sign_eq_one_iff _).mp (h i hi)).le

/-- ... but it is not necessary: for the `2 × 2` identity matrix (`l_1 = 0`) we have
`|L||U| = |LU|` while `sign(l_1 e_0 / u_1) = 0 ≠ 1`. -/
theorem eq_3_5_sign_not_necessary :
    (lowerBidiag (n := 2) (fun _ => 0)).map abs * (upperBidiag (fun _ => 1) (fun _ => 0)).map abs =
        (lowerBidiag (n := 2) (fun _ => 0) * upperBidiag (fun _ => 1) (fun _ => 0)).map abs ∧
      Real.sign ((fun _ : ℕ => (0 : ℝ)) 1 * (fun _ : ℕ => (0 : ℝ)) 0 / (fun _ : ℕ => (1 : ℝ)) 1) ≠ 1 := by
  refine ⟨((eq_3_5 _ _ _ (fun _ _ => one_ne_zero)).2).mpr fun i _ => by simp, ?_⟩
  simp [Real.sign_zero]

end Higham
