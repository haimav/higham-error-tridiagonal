import HighamTridiagonal.Theorem32

/-!
# Harrod's example: large multipliers do not affect the stability

The paper, §3, top of p. 525 (after the proof of Theorem 3.2 and the paragraph following it):

> "A corollary of Theorem 3.2 is that it is not necessary to pivot for the matrices specified in
> the theorem (and, indeed, pivoting could vitiate the bound (3.4)). Note that large multipliers
> may occur under the conditions of Theorem 3.2, but they do not affect the stability. [...]
> We also mention that the example given by Harrod [14] of the M-matrix
> ```
>     [ 2    -2   0 ]   [ 1          0     0 ] [ 2   -2   0 ]
> A = [ ε-2   2   0 ] = [ (ε-2)/2    1     0 ] [ 0    ε   0 ] = LU,
>     [ 0    -1   3 ]   [ 0        -1/ε    1 ] [ 0    0   3 ]
> ```
> for which the multiplier `l₃₂` is unbounded as `ε → 0`, is an example where Gaussian
> elimination performs very stably, as Theorem 3.2 shows."

## Main results

* `harrodA ε`, `harrodL ε`, `harrodU ε`: the three matrices of the display.
* `harrodA_isMMatrix_iff`: `A` is an M-matrix iff `0 < ε ≤ 2`.
* `harrod_isLU`, `harrod_LU_unique`: for `ε ≠ 0`, `A = LU` is an LU factorization, and it is
  *the* LU factorization of `A`.
* `harrodL_two_one`, `mult_harrodA_two`: the multiplier `l₃₂` (the `(3,2)` entry of `L`,
  equivalently `l₃ = c₃ / u₂` of the recurrence (2.3)) equals `-1/ε`;
  `harrod_multiplier_unbounded`: `|l₃₂| → ∞` as `ε → 0⁺`.
* `harrod_abs_LU`: nevertheless `|L||U| = |A|` (Theorem 3.1 at work).
* `harrod_stable`: for every `0 < ε ≤ 2` the conclusion of Theorem 3.2 holds for `A`
  (an instance of `theorem_3_2`, case (c) "M-matrix").
* `harrod_example`: the summary.

## The range of `ε`

The paper fixes no range for `ε`; "unbounded as `ε → 0`" refers to small `ε > 0`. We work with
`0 < ε ≤ 2`, which is exactly the range in which the claims hold:
* `ε ≤ 2` is needed for the off-diagonal entry `a₂₁ = ε - 2` to be `≤ 0`; `ε ≠ 0` is needed for
  nonsingularity (`det A = 6ε`, `harrodA_det`), and then `ε > 0` for `(A⁻¹)₁₁ = 1/ε ≥ 0`;
  together: `A` is an M-matrix iff `0 < ε ≤ 2` (`harrodA_isMMatrix_iff`).
* `L` exists only for `ε ≠ 0`: `A = LU` holds iff `ε ≠ 0` (`harrod_isLU_iff`), and for `ε = 0`
  the matrix `A` has no LU factorization at all (`harrodA_zero_not_exists_LU`).
* For `ε ≠ 0` (i.e. `A` nonsingular), `A` is of one of the types (a)–(d) of Theorem 3.1 — the
  hypothesis of Theorem 3.2 — iff `0 < ε ≤ 2` (`harrodA_type_iff`); outside this range
  `|L||U| ≠ |A|` (`harrod_abs_LU_iff`), so Theorem 3.2 does not apply.

## Indexing

Lean indices are `0`-based, the paper's are `1`-based: the paper's `l₃₂` is `harrodL ε 2 1`,
and the paper's `a₂₁` is `harrodA ε 1 0`. In the notation of the recurrence (2.3), `l₃₂` is the
multiplier `mult (harrodA ε) 2`, and the pivots `u₁, u₂, u₃ = 2, ε, 3` are
`piv (harrodA ε) 0`, `piv (harrodA ε) 1`, `piv (harrodA ε) 2`.

## A remark that is not in the paper: the threshold on `u` depends on `ε`

Theorem 3.2 gives its bound for "`u` sufficiently small", with a threshold `u₀` depending on
`A`. In the bound `|F| ≤ h(u)|A|`, the factor `h(u) = (4u + 3u² + u³)/(1 - u)` (the
componentwise relative backward error) involves neither `ε` nor the multipliers (only `|A|`
itself depends, boundedly, on `ε`); this is the sense in which Gaussian elimination "performs
very stably".
The threshold, however, cannot be chosen independently of `ε`. For `0 < ε ≤ 1` and every
`u ≥ ε` there is an arithmetic satisfying the model (2.4) with unit roundoff `u` (exact, except
that it rounds `fl(l₂₁ a₁₂) = fl(((ε-2)/2)·(-2))` to `2` instead of `2 - ε`) in which the
computed pivot `û₂ = fl(2 - 2)` is `0`, so Gaussian elimination breaks down
(`harrod_breakdown`). Hence every admissible threshold satisfies `u₀ ≤ ε`
(`harrod_threshold_le`), and no single `u₀ > 0` works for all `ε ∈ (0, 2]`
(`harrod_no_uniform_threshold`).
-/

open Matrix Finset Filter Topology

noncomputable section

namespace Higham

/-! ### The matrices -/

/-- Harrod's matrix `A = [2 -2 0; ε-2 2 0; 0 -1 3]`. -/
def harrodA (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![2, -2, 0; ε - 2, 2, 0; 0, -1, 3]

/-- The unit lower triangular LU factor `L = [1 0 0; (ε-2)/2 1 0; 0 -1/ε 1]` of Harrod's
matrix. -/
def harrodL (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; (ε - 2) / 2, 1, 0; 0, -1 / ε, 1]

/-- The upper triangular LU factor `U = [2 -2 0; 0 ε 0; 0 0 3]` of Harrod's matrix. -/
def harrodU (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![2, -2, 0; 0, ε, 0; 0, 0, 3]

/-- The inverse of Harrod's matrix (for `ε ≠ 0`, see `harrodA_inv`). -/
def harrodAinv (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / ε, 1 / ε, 0; (2 - ε) / (2 * ε), 1 / ε, 0; (2 - ε) / (6 * ε), 1 / (3 * ε), 1 / 3]

/-! ### Tridiagonality, determinant, inverse -/

lemma harrodA_isTridiagonal (ε : ℝ) : IsTridiagonal (harrodA ε) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [harrodA]

lemma harrodA_det (ε : ℝ) : (harrodA ε).det = 6 * ε := by
  simp [harrodA, det_fin_three]; ring

/-- Harrod's matrix is nonsingular iff `ε ≠ 0`. -/
lemma harrodA_isUnit_det_iff (ε : ℝ) : IsUnit (harrodA ε).det ↔ ε ≠ 0 := by
  simp [harrodA_det]

lemma harrodA_inv {ε : ℝ} (hε : ε ≠ 0) : (harrodA ε)⁻¹ = harrodAinv ε := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [harrodA, harrodAinv, mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-! ### The LU factorization -/

/-- For `ε ≠ 0`, `A = LU` with the factors displayed in the paper. -/
theorem harrod_isLU {ε : ℝ} (hε : ε ≠ 0) : IsLU (harrodA ε) (harrodL ε) (harrodU ε) where
  lower i j h := by fin_cases i <;> fin_cases j <;> simp_all [harrodL]
  unit_diag i := by fin_cases i <;> simp [harrodL]
  upper i j h := by fin_cases i <;> fin_cases j <;> simp_all [harrodU]
  eq := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [harrodA, harrodL, harrodU, mul_apply, Fin.sum_univ_three]
    rw [div_mul_cancel₀ _ hε]

/-- For `ε = 0` Harrod's matrix has no LU factorization at all. -/
theorem harrodA_zero_not_exists_LU :
    ¬ ∃ L U : Matrix (Fin 3) (Fin 3) ℝ, IsLU (harrodA 0) L U := by
  rintro ⟨L, U, h⟩
  have e00 := congrFun (congrFun h.eq 0) 0
  have e01 := congrFun (congrFun h.eq 0) 1
  have e10 := congrFun (congrFun h.eq 1) 0
  have e11 := congrFun (congrFun h.eq 1) 1
  have e20 := congrFun (congrFun h.eq 2) 0
  have e21 := congrFun (congrFun h.eq 2) 1
  simp [harrodA, mul_apply, Fin.sum_univ_three, h.unit_diag, h.lower 0 1 (by decide),
    h.lower 0 2 (by decide), h.lower 1 2 (by decide), h.upper 1 0 (by decide),
    h.upper 2 0 (by decide), h.upper 2 1 (by decide)] at e00 e01 e10 e11 e20 e21
  -- `u₁₁ = 2`, `u₁₂ = -2`, `l₂₁ = -1`, `u₂₂ = 0`, `l₃₁ = 0`, and then `a₃₂ = -1 = 0`
  rw [← e00] at e10 e20
  rw [← e01] at e11 e21
  have hL10 : L 1 0 = -1 := by linarith
  have hU11 : U 1 1 = 0 := by rw [hL10] at e11; linarith
  have hL20 : L 2 0 = 0 := e20.resolve_right two_ne_zero
  rw [hL20, hU11] at e21
  norm_num at e21

/-- The displayed factorization is an LU factorization iff `ε ≠ 0`. -/
theorem harrod_isLU_iff (ε : ℝ) : IsLU (harrodA ε) (harrodL ε) (harrodU ε) ↔ ε ≠ 0 :=
  ⟨fun h hε => by subst hε; exact harrodA_zero_not_exists_LU ⟨_, _, h⟩, harrod_isLU⟩

/-- For `ε ≠ 0`, `L` and `U` are *the* LU factors of `A` (uniqueness of the LU factorization of
a nonsingular matrix, `IsLU.unique`). -/
theorem harrod_LU_unique {ε : ℝ} (hε : ε ≠ 0) {L U : Matrix (Fin 3) (Fin 3) ℝ}
    (h : IsLU (harrodA ε) L U) : L = harrodL ε ∧ U = harrodU ε :=
  h.unique (harrod_isLU hε) ((harrodA_isUnit_det_iff ε).mpr hε) (harrodA_isTridiagonal ε)

/-- The pivots `u₁, u₂, u₃ = 2, ε, 3` of the recurrence (2.3) (the diagonal of `U`). -/
lemma piv_harrodA (ε : ℝ) :
    piv (harrodA ε) 0 = 2 ∧ piv (harrodA ε) 1 = ε ∧ piv (harrodA ε) 2 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [piv, harrodA, ent]

/-- The multiplier `l₂₁ = c₂ / u₁ = (ε - 2)/2` of the recurrence (2.3). -/
lemma mult_harrodA_one (ε : ℝ) : mult (harrodA ε) 1 = (ε - 2) / 2 := by
  simp [mult, piv, harrodA, ent]

/-- The multiplier `l₃₂ = c₃ / u₂ = -1/ε` of the recurrence (2.3). -/
lemma mult_harrodA_two (ε : ℝ) : mult (harrodA ε) 2 = -1 / ε := by
  simp [mult, piv, harrodA, ent]

/-! ### The M-matrix property -/

/-- Harrod's matrix is an M-matrix (nonsingular, nonpositive off-diagonal entries, `A⁻¹ ≥ 0`)
iff `0 < ε ≤ 2`. -/
theorem harrodA_isMMatrix_iff (ε : ℝ) : IsMMatrix (harrodA ε) ↔ 0 < ε ∧ ε ≤ 2 := by
  constructor
  · rintro ⟨hdet, hoff, hinv⟩
    have hε : ε ≠ 0 := (harrodA_isUnit_det_iff ε).mp hdet
    -- `a₂₁ = ε - 2 ≤ 0` and `(A⁻¹)₁₁ = 1/ε ≥ 0`
    have h1 := hoff 1 0 (by decide)
    have h2 := hinv 0 0
    rw [harrodA_inv hε] at h2
    simp [harrodA] at h1
    simp [harrodAinv] at h2
    exact ⟨lt_of_le_of_ne h2 (Ne.symm hε), h1⟩
  · rintro ⟨h0, h2⟩
    refine ⟨(harrodA_isUnit_det_iff ε).mpr h0.ne', ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [harrodA]
    · intro i j
      rw [harrodA_inv h0.ne']
      fin_cases i <;> fin_cases j <;> simp [harrodAinv] <;>
        first | exact h0.le | exact div_nonneg (by linarith) (by positivity)

theorem harrodA_isMMatrix {ε : ℝ} (h0 : 0 < ε) (h2 : ε ≤ 2) : IsMMatrix (harrodA ε) :=
  (harrodA_isMMatrix_iff ε).mpr ⟨h0, h2⟩

/-- Consistently with Theorem 3.1 (c) (`theorem_3_1_c_equiv'`), for `0 < ε ≤ 2` the factors
`L` and `U` have positive diagonal elements and nonpositive off-diagonal elements. -/
theorem harrod_factors_signPattern {ε : ℝ} (h0 : 0 < ε) (h2 : ε ≤ 2) :
    (∀ i, 0 < harrodL ε i i) ∧ (∀ i, 0 < harrodU ε i i) ∧
      (∀ i j, i ≠ j → harrodL ε i j ≤ 0) ∧ (∀ i j, i ≠ j → harrodU ε i j ≤ 0) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp [harrodL]
  · fin_cases i <;> simp [harrodU, h0]
  · fin_cases i <;> fin_cases j <;> simp_all [harrodL] <;>
      first | linarith | exact div_nonpos_of_nonpos_of_nonneg (by norm_num) h0.le
  · fin_cases i <;> fin_cases j <;> simp_all [harrodU]

/-! ### The multiplier `l₃₂` is unbounded -/

/-- The multiplier `l₃₂` (the paper's `1`-based `(3,2)` entry of `L`) equals `-1/ε`. -/
lemma harrodL_two_one (ε : ℝ) : harrodL ε 2 1 = -1 / ε := by
  simp [harrodL]

/-- The multiplier `l₃₂` is unbounded as `ε → 0`: `|l₃₂| → ∞` as `ε → 0⁺`. -/
theorem harrod_multiplier_unbounded : Tendsto (fun ε => |harrodL ε 2 1|) (𝓝[>] 0) atTop := by
  refine tendsto_inv_nhdsGT_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [harrodL_two_one, abs_div, abs_neg, abs_one, abs_of_pos hε, one_div]

/-! ### `|L||U| = |A|` and the hypotheses of Theorems 3.1 and 3.2 -/

/-- `|L||U| = |A|` holds exactly for `0 < ε ≤ 2`. (For `ε = 0`, `harrodL 0` is not an LU factor
of `A`, see `harrod_isLU_iff`; the equation fails there as well.) -/
theorem harrod_abs_LU_iff (ε : ℝ) :
    (harrodL ε).map abs * (harrodU ε).map abs = (harrodA ε).map abs ↔ 0 < ε ∧ ε ≤ 2 := by
  constructor
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    have h21 := congrFun (congrFun h 2) 1
    simp [harrodA, harrodL, harrodU, mul_apply, Fin.sum_univ_three] at h11 h21
    -- `h11 : |ε - 2| + |ε| = 2` forces `0 ≤ ε ≤ 2`; `h21 : |-1/ε| |ε| = 1` forces `ε ≠ 0`
    rw [abs_div, abs_two, div_mul_cancel₀ _ two_ne_zero] at h11
    have hε : ε ≠ 0 := by
      rintro rfl
      simp at h21
    have a1 := le_abs_self (ε - 2)
    have a2 := neg_le_abs (ε - 2)
    have a3 := le_abs_self ε
    have a4 := neg_le_abs ε
    exact ⟨lt_of_le_of_ne (by linarith) (Ne.symm hε), by linarith⟩
  · rintro ⟨h0, h2⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [harrodA, harrodL, harrodU, mul_apply, Fin.sum_univ_three]
    · rw [abs_div, abs_two, div_mul_cancel₀ _ two_ne_zero]
    · rw [abs_div, abs_two, div_mul_cancel₀ _ two_ne_zero, abs_of_nonpos (by linarith),
        abs_of_pos h0]
      ring
    · rw [← abs_mul, div_mul_cancel₀ _ h0.ne', abs_neg, abs_one]

/-- For `0 < ε ≤ 2`, `|L||U| = |A|`: although `l₃₂` is unbounded, `|L||U|` stays bounded. -/
theorem harrod_abs_LU {ε : ℝ} (h0 : 0 < ε) (h2 : ε ≤ 2) :
    (harrodL ε).map abs * (harrodU ε).map abs = (harrodA ε).map abs :=
  (harrod_abs_LU_iff ε).mpr ⟨h0, h2⟩

/-- For nonsingular `A` (`ε ≠ 0`), `A` is of one of the types (a)–(d) of Theorem 3.1 (the
hypothesis of Theorems 3.1 and 3.2) iff `0 < ε ≤ 2`. -/
theorem harrodA_type_iff {ε : ℝ} (hε : ε ≠ 0) :
    ((harrodA ε).PosDef ∨ IsTotallyNonneg (harrodA ε) ∨ IsMMatrix (harrodA ε) ∨
      ∃ D₁ D₂ B : Matrix (Fin 3) (Fin 3) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧
        harrodA ε = D₁ * B * D₂ ∧ (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) ↔
      0 < ε ∧ ε ≤ 2 := by
  constructor
  · intro h
    have habs := (theorem_3_1' _ ((harrodA_isUnit_det_iff ε).mpr hε) (harrodA_isTridiagonal ε)
      h).2 _ _ (harrod_isLU hε)
    rw [← (harrod_isLU hε).eq] at habs
    exact (harrod_abs_LU_iff ε).mp habs
  · rintro ⟨h0, h2⟩
    exact Or.inr (Or.inr (Or.inl (harrodA_isMMatrix h0 h2)))

/-! ### Gaussian elimination performs very stably (Theorem 3.2) -/

/-- **"Gaussian elimination performs very stably, as Theorem 3.2 shows."** For every
`0 < ε ≤ 2`, if the unit roundoff `u` is sufficiently small then Gaussian elimination for
`Ax = b` succeeds and the computed solution satisfies `(A + F) x̂ = b` with
`|F| ≤ h(u)|A|`, `h(u) = (4u + 3u² + u³)/(1 - u)`; the factor `h(u)` does not depend on `ε`,
i.e. not on the size of the multiplier `l₃₂ = -1/ε`. (Instance of `theorem_3_2`, case (c).) -/
theorem harrod_stable {ε : ℝ} (h0 : 0 < ε) (h2 : ε ≤ 2) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ (u : ℝ) (fp : FPModel u), u < u₀ → ∀ b : Fin 3 → ℝ,
      fp.Succeeds (harrodA ε) ∧
      ∃ F : Matrix (Fin 3) (Fin 3) ℝ, (harrodA ε + F) *ᵥ fp.solve (harrodA ε) b = b ∧
        ∀ i j, |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) * |harrodA ε i j| :=
  theorem_3_2 (harrodA ε) ((harrodA_isUnit_det_iff ε).mpr h0.ne') (harrodA_isTridiagonal ε)
    (Or.inr (Or.inr (Or.inl (harrodA_isMMatrix h0 h2))))

/-! ### Summary -/

/-- **Harrod's example** (§3, p. 525). For `0 < ε ≤ 2` the matrix `A = [2 -2 0; ε-2 2 0; 0 -1 3]`
is tridiagonal, nonsingular and an M-matrix, and `A = LU` with `L = [1 0 0; (ε-2)/2 1 0; 0 -1/ε 1]`
and `U = [2 -2 0; 0 ε 0; 0 0 3]` is its (unique) LU factorization. The multiplier `l₃₂ = -1/ε`
is unbounded as `ε → 0⁺`; nevertheless `|L||U| = |A|`, and Gaussian elimination performs very
stably: the conclusion of Theorem 3.2 holds for `A`. -/
theorem harrod_example :
    (∀ ε : ℝ, 0 < ε → ε ≤ 2 →
      IsTridiagonal (harrodA ε) ∧ IsUnit (harrodA ε).det ∧ IsMMatrix (harrodA ε) ∧
      IsLU (harrodA ε) (harrodL ε) (harrodU ε) ∧
      (∀ L U, IsLU (harrodA ε) L U → L = harrodL ε ∧ U = harrodU ε) ∧
      harrodL ε 2 1 = -1 / ε ∧
      (harrodL ε).map abs * (harrodU ε).map abs = (harrodA ε).map abs ∧
      ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ (u : ℝ) (fp : FPModel u), u < u₀ → ∀ b : Fin 3 → ℝ,
        fp.Succeeds (harrodA ε) ∧
        ∃ F : Matrix (Fin 3) (Fin 3) ℝ, (harrodA ε + F) *ᵥ fp.solve (harrodA ε) b = b ∧
          ∀ i j, |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) * |harrodA ε i j|) ∧
    Tendsto (fun ε => |harrodL ε 2 1|) (𝓝[>] 0) atTop :=
  ⟨fun _ h0 h2 => ⟨harrodA_isTridiagonal _, (harrodA_isUnit_det_iff _).mpr h0.ne',
    harrodA_isMMatrix h0 h2, harrod_isLU h0.ne', fun _ _ h => harrod_LU_unique h0.ne' h,
    harrodL_two_one _, harrod_abs_LU h0 h2, harrod_stable h0 h2⟩,
    harrod_multiplier_unbounded⟩

/-! ### Remark (not in the paper): the threshold on `u` must depend on `ε` -/

/-- An arithmetic satisfying the model (2.4) with unit roundoff `u ≥ ε` (where `0 < ε ≤ 1`):
exact, except that it rounds the product `((ε-2)/2) · (-2) = 2 - ε` to `2`
(relative errors `ε/(2-ε) ≤ u` in (2.4a) and `ε/2 ≤ u` in (2.4b)). -/
def harrodBadFP {ε u : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (hu : ε ≤ u) : FPModel u where
  add := (· + ·)
  sub := (· - ·)
  mul x y := if x = (ε - 2) / 2 ∧ y = -2 then 2 else x * y
  div := (· / ·)
  add_a _ _ := ⟨0, by simp; linarith, by simp⟩
  add_b _ _ := ⟨0, by simp; linarith, by simp⟩
  sub_a _ _ := ⟨0, by simp; linarith, by simp⟩
  sub_b _ _ := ⟨0, by simp; linarith, by simp⟩
  mul_a x y := by
    by_cases h : x = (ε - 2) / 2 ∧ y = -2
    · obtain ⟨rfl, rfl⟩ := h
      have hne : (2 : ℝ) - ε ≠ 0 := by linarith
      refine ⟨ε / (2 - ε), ?_, ?_⟩
      · rw [abs_of_nonneg (div_nonneg h0.le (by linarith)), div_le_iff₀ (by linarith)]
        nlinarith
      · simp only [and_self, ite_true]
        field_simp
        ring
    · exact ⟨0, by simp; linarith, by simp [h]⟩
  mul_b x y := by
    by_cases h : x = (ε - 2) / 2 ∧ y = -2
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨-ε / 2, ?_, ?_⟩
      · rw [abs_div, abs_neg, abs_of_pos h0, abs_two]; linarith
      · simp only [and_self, ite_true]
        have hne : (1 : ℝ) + -ε / 2 ≠ 0 := by linarith
        rw [eq_div_iff hne]
        ring
    · exact ⟨0, by simp; linarith, by simp [h]⟩
  div_a _ _ _ := ⟨0, by simp; linarith, by simp⟩
  div_b _ _ _ := ⟨0, by simp; linarith, by simp⟩

/-- In the arithmetic `harrodBadFP`, the computed pivot `û₂ = fl(2 - fl(l̂₂₁ a₁₂)) = fl(2 - 2)`
(paper's `1`-based numbering; `fp.piv (harrodA ε) 1` in Lean) is zero. -/
lemma harrodBadFP_piv_one {ε u : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (hu : ε ≤ u) :
    (harrodBadFP h0 h1 hu).piv (harrodA ε) 1 = 0 := by
  simp [FPModel.piv, harrodBadFP, harrodA, ent]

/-- For `0 < ε ≤ 1` and every unit roundoff `u ≥ ε` there is an arithmetic satisfying the model
(2.4) in which Gaussian elimination on Harrod's matrix breaks down. -/
theorem harrod_breakdown {ε u : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (hu : ε ≤ u) :
    ∃ fp : FPModel u, ¬ fp.Succeeds (harrodA ε) :=
  ⟨harrodBadFP h0 h1 hu, fun h => h 1 (by norm_num) (harrodBadFP_piv_one h0 h1 hu)⟩

/-- Any threshold `u₀` below which Gaussian elimination on Harrod's matrix succeeds in every
arithmetic satisfying (2.4) (as provided by Theorem 3.2, `harrod_stable`) satisfies `u₀ ≤ ε`
(for `0 < ε ≤ 1`). -/
theorem harrod_threshold_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {u₀ : ℝ}
    (h : ∀ (u : ℝ) (fp : FPModel u), u < u₀ → fp.Succeeds (harrodA ε)) : u₀ ≤ ε := by
  by_contra hlt
  obtain ⟨fp, hfp⟩ := harrod_breakdown h0 h1 le_rfl
  exact hfp (h ε fp (not_le.mp hlt))

/-- No single threshold `u₀ > 0` works for Harrod's matrix for all `ε ∈ (0, 2]`: the threshold
in `harrod_stable` necessarily depends on `ε`. -/
theorem harrod_no_uniform_threshold :
    ¬ ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∀ (u : ℝ) (fp : FPModel u), u < u₀ →
      fp.Succeeds (harrodA ε) := by
  rintro ⟨u₀, hu₀, h⟩
  have hε : 0 < min (u₀ / 2) 1 := lt_min (by linarith) one_pos
  have := harrod_threshold_le hε (min_le_right _ _)
    (h _ hε (by linarith [min_le_right (u₀ / 2) 1]))
  linarith [min_le_left (u₀ / 2) 1]

end Higham
