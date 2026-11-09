import HighamTridiagonal.OpCount38
import HighamTridiagonal.Remarks
import HighamTridiagonal.Example42

/-!
# Unnumbered remarks on the condition numbers `cond(A, x)`, `cond(A)` and `κ∞(A)`

This file formalizes three unnumbered remarks of

  N. J. Higham, *Bounding the error in Gaussian elimination for tridiagonal systems*,
  SIAM J. Matrix Anal. Appl. 11 (1990), 521–530.

As elsewhere in the project, `|M|` is `M.map abs`, `e = (1, …, 1)ᵀ` is `fun _ => 1`, the norm of
a vector `v : Fin n → ℝ` is Mathlib's sup norm `‖v‖ = ‖v‖_∞`, `cond(A, x)` is `condSkeel A x`,
`cond(A) = cond(A, e)` is `condSkeelA A`, and `κ∞(A) = ‖A‖_∞ ‖A⁻¹‖_∞` is `kappaInf A`, where for
matrices `‖·‖` is the `∞`-operator norm (maximal absolute row sum), available through
`open scoped Matrix.Norms.Operator`.

## 1. `‖A⁻¹‖∞` and `κ∞(A)` from (3.8) with `y = e` (§3, p. 526, and §6, p. 529)

*"Thus, if `|A⁻¹| = |U⁻¹||L⁻¹|` and `y ≥ 0` then `|A⁻¹| y = |U⁻¹||L⁻¹| y = M(U)⁻¹ M(L)⁻¹ y`.
By taking `y = |A||x|` it follows that `cond(A, x)` can be computed in `O(n)` operations:
form `y = |A||x|`, solve `M(L) v = y`, solve `M(U) w = v`, compute `‖w‖∞ / ‖x‖∞`.   (3.8)
For the special case `y = e` and `A` symmetric positive definite, (3.8) was used in [15, §6] to
compute `‖A⁻¹‖∞` in `O(n)` operations."* (§3)

*"Since `A` is an M-matrix, `cond(A, x)`, `cond(A)`, and `κ∞(A)` were computed in `O(n)` flops
according to (3.8) (using `y = e` to compute `κ∞(A)`)."* (§6, the test problem)

The fact behind "using `y = e`" is that the `∞`-operator norm is the maximal absolute row sum:
* `linfty_opNorm_eq_norm_abs_mulVec_one`: `‖M‖∞ = ‖ |M| e ‖∞` for every real matrix `M`.

Hence, with (3.8):
* `norm_inv_eq_comparison`, `kappaInf_eq_comparison`: if the nonsingular tridiagonal `A = LU`
  satisfies `|A⁻¹| = |U⁻¹||L⁻¹|` (the hypothesis of (3.8)), then
  `‖A⁻¹‖∞ = ‖M(U)⁻¹ M(L)⁻¹ e‖∞` and `κ∞(A) = ‖A‖∞ ‖M(U)⁻¹ M(L)⁻¹ e‖∞`;
* `eq_3_8_norm_inv`: the same in the form of (3.8): if `M(L) v = e` and `M(U) w = v` then
  `‖w‖∞ = ‖A⁻¹‖∞` and `‖A‖∞ ‖w‖∞ = κ∞(A)`;
* `norm_inv_eq_solveComp`: `‖A⁻¹‖∞` is the sup norm of the vector produced by the two `O(n)`
  bidiagonal recurrences `solveCompL`, `solveCompU` of `Algorithm38.lean` started from `y = e`;
* `norm_inv_eq_comparison_of_type`, `norm_inv_eq_comparison_of_posDef` (the symmetric positive
  definite case of [15, §6]) and `norm_inv_eq_comparison_of_mMatrix` (the case of §6): for the
  matrices of Theorem 3.1 the hypothesis `|A⁻¹| = |U⁻¹||L⁻¹|` holds automatically (Theorem 3.1
  and Theorem 3.3), for every LU factorization.

**Operation counts.** In the cost model of `OpCount38.lean` (each `+ - * / |·| max` costs `1`;
reading entries of `A` is free) we implement:
* `normInvCounted A`: the LU factorization (2.3), `M(L) v = e`, `M(U) w = v`, `‖w‖∞`; it returns
  `‖A⁻¹‖∞` under the hypothesis of (3.8) (`normInvCounted_val`) after exactly `13 n - 10`
  operations (`normInvCounted_ops`); `normInvCounted_of_posDef` is the claim about [15, §6].
* `kappaInfCounted A`: in addition `‖A‖∞ = ‖ |A| e ‖∞` from the three tridiagonal entries of each
  row (pass (b) of (3.8) with `x = e`) and one multiplication; it returns `κ∞(A)`
  (`kappaInfCounted_val`) after exactly `22 n - 16` operations for `n ≥ 1`
  (`kappaInfCounted_ops`).
* `section6_O_n_of_type`, `section6_O_n_of_mMatrix`: for the matrices of Theorem 3.1, in
  particular for tridiagonal M-matrices as in the test problem of §6, `cond(A, x)`, `cond(A)` and
  `κ∞(A)` are computed by (3.8) in at most `23 n + 1`, `23 n + 1` and `22 n + 1` operations.

## 2. `cond(A)/cond(A, x)` can be arbitrarily large (§6, p. 529)

*"Instead of computing `cond(A, x)` one could compute `cond(A) = cond(A, e) ≥ cond(A, x)`. The
same `cond(A)` value could be reused when solving systems with the same `A` but different
right-hand sides. However, this approach reduces the sharpness of the bounds, since
`cond(A)/cond(A, x)` can be arbitrarily large."*

(`cond(A, x) ≤ cond(A)` is `condSkeel_le_condSkeelA` in `Condition.lean`.)
* `exShear_condSkeel`, `exShear_condSkeelA`: for `A = [1 t; 0 1]` and `x = e₁ = (1, 0)ᵀ`,
  `|A⁻¹||A| = [1 2|t|; 0 1]`, `cond(A, x) = 1` and `cond(A) = 1 + 2|t|`;
* `condSkeelA_div_condSkeel_unbounded`: for every `M` there are a nonsingular tridiagonal
  `A ∈ ℝ^{2×2}` and `x ≠ 0` with `cond(A)/cond(A, x) > M`; `tendsto_exShear_ratio`: the ratio
  tends to `∞` along `A = [1 t; 0 1]`, `t → ∞`.
* `condSkeelA_div_condSkeel_unbounded_dim`: the same in every dimension `n ≥ 2`, with
  `A = I + t E₁₂` (`exShearN_condSkeel`, `exShearN_condSkeelA`: `cond(A, e₁) = 1`,
  `cond(A) = 1 + 2|t|`); `condSkeelA_div_condSkeel_dim_one`: for `n = 1` the ratio is always
  `1`, so `n ≥ 2` is needed.
* The ratio is unbounded even within each of the classes (a)–(c) of Theorem 3.1, for which
  (3.8) computes `cond(A, x)` exactly: `[1 t; 0 1]` is totally nonnegative for `t ≥ 0` and an
  M-matrix for `t ≤ 0` (`condSkeelA_div_condSkeel_unbounded_totallyNonneg`,
  `condSkeelA_div_condSkeel_unbounded_mMatrix`), and the symmetric positive definite matrix
  `[1 t; t t²+1]` has `cond(A, e₁) = 2t² + 1` and `cond(A) = 2t² + 1 + 2|t|(t² + 1)`
  (`condSkeelA_div_condSkeel_unbounded_posDef`).

## 3. `κ∞(A)` is not invariant under row scaling (§1, p. 522)

*"The key difference between (1.5) and (1.2) is in the condition number terms: `cond(A, x)` is
no larger than `κ∞(A)` and is often much smaller. In particular, `cond(A, x)` is invariant under
row scaling of `A`, whereas `κ∞(A)` is not."*

The invariance of `cond(A, x)` is `condSkeel_diagonal_mul` (`Remarks.lean`).
* `kappaInf_not_row_scaling_invariant`: there are a nonsingular `A ∈ ℝ^{2×2}` and a nonsingular
  diagonal `D = diag(d)` with `κ∞(DA) ≠ κ∞(A)` (`A = I`, `d = (1, 2)`: `κ∞(DA) = 2`,
  `κ∞(A) = 1`).
* `condSkeel_row_scaling_invariant_kappaInf_not`: both halves of the sentence together (with a
  tridiagonal witness); `kappaInf_row_scaling_unbounded`: `κ∞(DA)` can even be arbitrarily
  large, since `κ∞(diag(1, t)) = t` for `t ≥ 1`.

No extra hypotheses beyond those of the paper are used.
-/

open Matrix Finset Filter Topology

noncomputable section

namespace Higham

variable {n : ℕ}

/-! ### 1. `‖A⁻¹‖∞` and `κ∞(A)` from (3.8) with `y = e` -/

section NormFromRowSums

open scoped Matrix.Norms.Operator

/-- **The `∞`-operator norm is the maximal absolute row sum:** `‖M‖∞ = ‖ |M| e ‖∞` for every
real matrix `M` (in particular for every square matrix). This is why (3.8) with `y = e`
computes `‖A⁻¹‖∞ = ‖ |A⁻¹| e ‖∞`. -/
theorem linfty_opNorm_eq_norm_abs_mulVec_one {m p : Type*} [Fintype m] [Fintype p]
    (M : Matrix m p ℝ) : ‖M‖ = ‖M.map abs *ᵥ (fun _ => (1 : ℝ))‖ := by
  rw [linfty_opNorm_def, Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  ext
  simp only [coe_nnnorm, NNReal.coe_sum, mulVec, dotProduct, map_apply, mul_one,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)]

/-- **(3.8) with `y = e` computes `‖A⁻¹‖∞`.** If the nonsingular tridiagonal matrix `A = LU`
satisfies `|A⁻¹| = |U⁻¹||L⁻¹|` (the hypothesis of (3.8)), then
`‖A⁻¹‖∞ = ‖ |A⁻¹| e ‖∞ = ‖M(U)⁻¹ M(L)⁻¹ e‖∞`. -/
theorem norm_inv_eq_comparison (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) :
    ‖A⁻¹‖ = ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ := by
  rw [linfty_opNorm_eq_norm_abs_mulVec_one, abs_inv_mulVec_eq_comparison A L U hA hT hLU hinv]

/-- **`κ∞(A)` from (3.8) with `y = e`.** Under the hypotheses of `norm_inv_eq_comparison`,
`κ∞(A) = ‖A‖∞ ‖M(U)⁻¹ M(L)⁻¹ e‖∞`. -/
theorem kappaInf_eq_comparison (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) :
    kappaInf A = ‖A‖ * ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ := by
  rw [kappaInf, norm_inv_eq_comparison A L U hA hT hLU hinv]

/-- **(3.8) with `y = e`, in the form of (3.8).** If the nonsingular tridiagonal matrix `A = LU`
satisfies `|A⁻¹| = |U⁻¹||L⁻¹|`, then for the solutions of `M(L) v = e` and `M(U) w = v` we have
`‖w‖∞ = ‖A⁻¹‖∞` and `‖A‖∞ ‖w‖∞ = κ∞(A)`. -/
theorem eq_3_8_norm_inv (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) (v w : Fin n → ℝ)
    (hv : comparison L *ᵥ v = fun _ => 1) (hw : comparison U *ᵥ w = v) :
    ‖w‖ = ‖A⁻¹‖ ∧ ‖A‖ * ‖w‖ = kappaInf A := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  have hdetL : IsUnit (comparison L).det := by
    rw [hL, comparison_lowerBidiag]; exact isUnit_det_lowerBidiag _
  have hdetU : IsUnit (comparison U).det := by
    rw [hU, comparison_upperBidiag]
    exact isUnit_det_upperBidiag _ fun i hi => abs_ne_zero.mpr (hp i hi)
  have hv' : v = (comparison L)⁻¹ *ᵥ (fun _ => 1) := by
    rw [← hv, mulVec_mulVec, nonsing_inv_mul _ hdetL, one_mulVec]
  have hw' : w = (comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => 1)) := by
    rw [← hv', ← hw, mulVec_mulVec, nonsing_inv_mul _ hdetU, one_mulVec]
  have h1 : ‖w‖ = ‖A⁻¹‖ := by rw [hw', norm_inv_eq_comparison A L U hA hT hLU hinv]
  exact ⟨h1, by rw [h1, kappaInf]⟩

/-- **(3.8) with `y = e`, algorithmic form.** Under the hypothesis of (3.8), `‖A⁻¹‖∞` is the sup
norm of the vector obtained from `y = e` by the two `O(n)` bidiagonal recurrences of
`Algorithm38.lean` (forward substitution for `M(L) v = e`, back substitution for `M(U) w = v`,
with the multipliers and pivots of the recurrence (2.3)). -/
theorem norm_inv_eq_solveComp (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) :
    ‖A⁻¹‖ = ‖fun i : Fin n => solveCompU (n := n) (piv A) (supd A)
      (solveCompL (mult A) (fun _ : Fin n => (1 : ℝ))) i‖ := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  refine ((eq_3_8_norm_inv A L U hA hT hLU hinv
    (fun i => solveCompL (mult A) (fun _ : Fin n => (1 : ℝ)) i) _ ?_ ?_).1).symm
  · rw [hL]; exact comparison_lowerBidiag_mulVec_solveCompL _ _
  · rw [hU]; exact comparison_upperBidiag_mulVec_solveCompU _ hp _

/-- For the matrices of Theorem 3.1 (types (a)–(d)) the hypothesis of (3.8) holds for every LU
factorization (Theorem 3.1 and Theorem 3.3), so `A` has an LU factorization and for every LU
factorization `‖A⁻¹‖∞ = ‖M(U)⁻¹ M(L)⁻¹ e‖∞` and `κ∞(A) = ‖A‖∞ ‖M(U)⁻¹ M(L)⁻¹ e‖∞`. -/
theorem norm_inv_eq_comparison_of_type (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    (∃ L U, IsLU A L U) ∧ ∀ L U, IsLU A L U →
      ‖A⁻¹‖ = ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ ∧
      kappaInf A = ‖A‖ * ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ := by
  obtain ⟨hex, habs⟩ := theorem_3_1' A hA hT h
  refine ⟨hex, fun L U hLU => ?_⟩
  have h1 := habs L U hLU
  rw [← hLU.eq] at h1
  have hinv := (theorem_3_3 A L U hA hT hLU h1).symm
  exact ⟨norm_inv_eq_comparison A L U hA hT hLU hinv,
    kappaInf_eq_comparison A L U hA hT hLU hinv⟩

/-- **§3, the special case of [15, §6]: `y = e` and `A` symmetric positive definite.** A
symmetric positive definite tridiagonal `A` has an LU factorization, and for every LU
factorization `A = LU`, `‖A⁻¹‖∞ = ‖M(U)⁻¹ M(L)⁻¹ e‖∞` and `κ∞(A) = ‖A‖∞ ‖M(U)⁻¹ M(L)⁻¹ e‖∞`.
(Mathlib's `PosDef` includes symmetry; nonsingularity follows from positive definiteness.) -/
theorem norm_inv_eq_comparison_of_posDef (A : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsTridiagonal A) (hP : A.PosDef) :
    (∃ L U, IsLU A L U) ∧ ∀ L U, IsLU A L U →
      ‖A⁻¹‖ = ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ ∧
      kappaInf A = ‖A‖ * ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ :=
  norm_inv_eq_comparison_of_type A (isUnit_iff_ne_zero.mpr hP.det_pos.ne') hT (Or.inl hP)

/-- **§6: the M-matrix case.** A tridiagonal M-matrix `A` (such as the test matrix of §6) has an
LU factorization, and for every LU factorization `A = LU`, `‖A⁻¹‖∞ = ‖M(U)⁻¹ M(L)⁻¹ e‖∞` and
`κ∞(A) = ‖A‖∞ ‖M(U)⁻¹ M(L)⁻¹ e‖∞`. -/
theorem norm_inv_eq_comparison_of_mMatrix (A : Matrix (Fin n) (Fin n) ℝ)
    (hT : IsTridiagonal A) (hM : IsMMatrix A) :
    (∃ L U, IsLU A L U) ∧ ∀ L U, IsLU A L U →
      ‖A⁻¹‖ = ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ ∧
      kappaInf A = ‖A‖ * ‖(comparison U)⁻¹ *ᵥ ((comparison L)⁻¹ *ᵥ (fun _ => (1 : ℝ)))‖ :=
  norm_inv_eq_comparison_of_type A hM.1 hT (Or.inr (Or.inr (Or.inl hM)))

end NormFromRowSums

/-! ### Operation counts for `‖A⁻¹‖∞` and `κ∞(A)` -/

namespace OpCount

open Counted

/-- `‖A⁻¹‖∞` by (3.8) with `y = e`, in the cost model of `OpCount38.lean`: (a) the LU
factorization (2.3), (c) the forward pass for `M(L) v = e`, (d) the backward pass for
`M(U) w = v`, (e) `‖w‖∞` as the running maximum of `|w_0|, …, |w_{n-1}|`. -/
def normInvM (A : Matrix (Fin n) (Fin n) ℝ) : Counted ℝ := do
  let lu ← luPass A                           -- (a) [l_1, …, l_{n-1}], [u_0, …, u_{n-1}]
  let vs ← fwdPass lu.1 (List.replicate n 1)  -- (c) M(L) v = e
  let ws ← bwdPass A 0 lu.2 vs                -- (d) M(U) w = v
  let aw ← absPass ws                         -- (e) [|w_0|, …, |w_{n-1}|]
  maxPass aw                                  -- (e) ‖w‖∞

/-- `κ∞(A) = ‖A‖∞ ‖A⁻¹‖∞` in the cost model: `‖A‖∞ = ‖ |A| e ‖∞` from the three tridiagonal
entries of each row (pass (b) of (3.8) with `x = e`) followed by a running maximum, then
`‖A⁻¹‖∞` by `normInvM`, and one multiplication. -/
def kappaInfM (A : Matrix (Fin n) (Fin n) ℝ) : Counted ℝ := do
  let ys ← rowPass A 0 none (List.replicate n 1)  -- (b) with x = e: |A| e
  let na ← maxPass ys                             -- ‖A‖∞
  let ni ← normInvM A                             -- ‖A⁻¹‖∞
  mulOp na ni

lemma replicate_eq_map_vext : List.replicate n (1 : ℝ) =
    (List.range' 0 n).map (vext (fun _ : Fin n => (1 : ℝ))) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < n := by simpa using h1
    simp [vext, hj]

lemma replicate_eq_map_abs_vext : List.replicate n (1 : ℝ) =
    (List.range' 0 n).map (fun j => |vext (fun _ : Fin n => (1 : ℝ)) j|) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < n := by simpa using h1
    simp [vext, hj]

/-- The value of `normInvM A`: the sup norm of the solution of `M(L) v = e`, `M(U) w = v`
computed by the recurrences `solveCompL`, `solveCompU` (for every `A`). -/
theorem normInvM_val (A : Matrix (Fin n) (Fin n) ℝ) :
    (normInvM A).val = ‖fun i : Fin n => solveCompU (n := n) (piv A) (supd A)
      (solveCompL (mult A) (fun _ : Fin n => (1 : ℝ))) i‖ := by
  have h1 := luPass_val A
  have h4 := fwdPass_val (mult A) (fun _ : Fin n => (1 : ℝ))
  have h5 := bwdPass_val A (solveCompL (mult A) (fun _ : Fin n => (1 : ℝ))) n 0 (by simp)
  simp only [normInvM, val_bind, h1, replicate_eq_map_vext, h4, h5, absPass_val, List.map_map]
  exact maxPass_abs_eq_norm _

/-- `normInvM A` performs `3(n-1) + 3(n-1) + (5n-3) + n + (n-1) = 13 n - 10` operations
(`0` if `n = 0`, in agreement with truncated subtraction). -/
theorem normInvM_ops (A : Matrix (Fin n) (Fin n) ℝ) : (normInvM A).ops = 13 * n - 10 := by
  simp only [normInvM, ops_bind, luPass_ops, fwdPass_ops, bwdPass_ops, absPass_ops,
    maxPass_ops, absPass_length, bwdPass_length, fwdPass_length, luPass_length_fst,
    luPass_length_snd, List.length_replicate]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rfl
  · have e : n - 1 + 1 = n := by omega
    simp only [e, min_self]
    omega

/-- The running maximum of the entries of a nonnegative vector is its sup norm. -/
lemma maxPass_map_vext_of_nonneg (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (maxPass ((List.range' 0 n).map (vext y))).val = ‖y‖ := by
  have : (List.range' 0 n).map (vext y) = (List.range' 0 n).map (fun j => |vext y j|) := by
    refine List.map_congr_left fun j _ => ?_
    unfold vext; split_ifs <;> simp [abs_of_nonneg (hy _)]
  rw [this, maxPass_abs_eq_norm]
  congr 1; funext i; simp [vext]

/-- The value of `kappaInfM A` for tridiagonal `A` (tridiagonality is needed since only the
three tridiagonal entries of each row are read). -/
theorem kappaInfM_val {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) :
    (kappaInfM A).val = ‖A.map abs *ᵥ (fun _ => (1 : ℝ))‖ *
      ‖fun i : Fin n => solveCompU (n := n) (piv A) (supd A)
        (solveCompL (mult A) (fun _ : Fin n => (1 : ℝ))) i‖ := by
  have h3 := rowPass_val hT (fun _ : Fin n => (1 : ℝ)) n 0 none (by simp) (by simp)
  simp only [abs_one] at h3
  have hy : ∀ i, 0 ≤ (A.map abs *ᵥ (fun _ => (1 : ℝ))) i :=
    mulVec_nonneg_of_nonneg (fun _ _ => abs_nonneg _) (fun _ => zero_le_one)
  simp only [kappaInfM, val_bind, replicate_eq_map_abs_vext, h3, maxPass_map_vext_of_nonneg _ hy,
    normInvM_val, mulOp_val]

/-- `kappaInfM A` performs `(8n-6) + (n-1) + (13n-10) + 1 = 22 n - 16` operations if `n ≥ 1`
(and `1`, the final multiplication, if `n = 0`). -/
theorem kappaInfM_ops (A : Matrix (Fin n) (Fin n) ℝ) :
    (kappaInfM A).ops = if n = 0 then 1 else 22 * n - 16 := by
  simp only [kappaInfM, ops_bind, rowPass_ops, maxPass_ops, normInvM_ops, mulOp_ops,
    rowPass_length, List.length_replicate, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rfl
  · simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
    omega

end OpCount

open OpCount

/-- **`‖A⁻¹‖∞` by (3.8) with `y = e`, with operation count:** the computed value and the number
of arithmetic operations performed (see `OpCount.normInvM` and the cost model of
`OpCount38.lean`). -/
def normInvCounted (A : Matrix (Fin n) (Fin n) ℝ) : ℝ × ℕ :=
  ((normInvM A).val, (normInvM A).ops)

/-- **`κ∞(A)` by (3.8) with `y = e`, with operation count** (see `OpCount.kappaInfM`). -/
def kappaInfCounted (A : Matrix (Fin n) (Fin n) ℝ) : ℝ × ℕ :=
  ((kappaInfM A).val, (kappaInfM A).ops)

section CountedNorms

open scoped Matrix.Norms.Operator

/-- Under the hypothesis `|A⁻¹| = |U⁻¹||L⁻¹|` of (3.8), `normInvCounted` computes `‖A⁻¹‖∞`. -/
theorem normInvCounted_val (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) : (normInvCounted A).1 = ‖A⁻¹‖ := by
  rw [normInvCounted, normInvM_val, norm_inv_eq_solveComp A L U hA hT hLU hinv]

/-- `normInvCounted A` performs exactly `13 n - 10` operations (for every `A`; `0` if `n = 0`). -/
theorem normInvCounted_ops (A : Matrix (Fin n) (Fin n) ℝ) : (normInvCounted A).2 = 13 * n - 10 :=
  normInvM_ops A

/-- Under the hypothesis `|A⁻¹| = |U⁻¹||L⁻¹|` of (3.8), `kappaInfCounted` computes `κ∞(A)`. -/
theorem kappaInfCounted_val (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U)
    (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) : (kappaInfCounted A).1 = kappaInf A := by
  rw [kappaInfCounted, kappaInfM_val hT, kappaInf, ← linfty_opNorm_eq_norm_abs_mulVec_one,
    norm_inv_eq_solveComp A L U hA hT hLU hinv]

/-- `kappaInfCounted A` performs exactly `22 n - 16` operations if `n ≥ 1` (and `1` if
`n = 0`), for every `A`. -/
theorem kappaInfCounted_ops (A : Matrix (Fin n) (Fin n) ℝ) :
    (kappaInfCounted A).2 = if n = 0 then 1 else 22 * n - 16 :=
  kappaInfM_ops A

/-- **`O(n)`**: `kappaInfCounted A` performs at most `22 n + 1` operations. -/
theorem kappaInfCounted_ops_le (A : Matrix (Fin n) (Fin n) ℝ) :
    (kappaInfCounted A).2 ≤ 22 * n + 1 := by
  rw [kappaInfCounted_ops]; split_ifs <;> omega

/-- **§3: "For the special case `y = e` and `A` symmetric positive definite, (3.8) was used in
[15, §6] to compute `‖A⁻¹‖∞` in `O(n)` operations."** For a symmetric positive definite
tridiagonal `A`, `normInvCounted A` returns `‖A⁻¹‖∞` after exactly `13 n - 10` operations, and
`kappaInfCounted A` returns `κ∞(A)` after at most `22 n + 1` operations. -/
theorem normInvCounted_of_posDef (A : Matrix (Fin n) (Fin n) ℝ) (hT : IsTridiagonal A)
    (hP : A.PosDef) :
    ((normInvCounted A).1 = ‖A⁻¹‖ ∧ (normInvCounted A).2 = 13 * n - 10) ∧
      ((kappaInfCounted A).1 = kappaInf A ∧ (kappaInfCounted A).2 ≤ 22 * n + 1) := by
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  obtain ⟨L, U, hLU, habs⟩ := theorem_3_1 A hA hT (Or.inl hP)
  rw [← hLU.eq] at habs
  have hinv := (theorem_3_3 A L U hA hT hLU habs).symm
  exact ⟨⟨normInvCounted_val A L U hA hT hLU hinv, normInvCounted_ops A⟩,
    ⟨kappaInfCounted_val A L U hA hT hLU hinv, kappaInfCounted_ops_le A⟩⟩

/-- **§6: "`cond(A, x)`, `cond(A)`, and `κ∞(A)` were computed in `O(n)` flops according to (3.8)
(using `y = e` to compute `κ∞(A)`)"**, for the matrices of Theorem 3.1 (types (a)–(d)): for
every `x`, `condAlgCounted A x` returns `cond(A, x)`, `condAlgCounted A e` returns `cond(A)`
(each after at most `23 n + 1` operations), and `kappaInfCounted A` returns `κ∞(A)` (after at
most `22 n + 1` operations). -/
theorem section6_O_n_of_type (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) (x : Fin n → ℝ) :
    ((condAlgCounted A x).1 = condSkeel A x ∧ (condAlgCounted A x).2 ≤ 23 * n + 1) ∧
      ((condAlgCounted A (fun _ => 1)).1 = condSkeelA A ∧
        (condAlgCounted A (fun _ => 1)).2 ≤ 23 * n + 1) ∧
      ((kappaInfCounted A).1 = kappaInf A ∧ (kappaInfCounted A).2 ≤ 22 * n + 1) := by
  obtain ⟨L, U, hLU, habs⟩ := theorem_3_1 A hA hT h
  rw [← hLU.eq] at habs
  have hinv := (theorem_3_3 A L U hA hT hLU habs).symm
  exact ⟨eq_3_8_counted A L U hA hT hLU hinv x, eq_3_8_counted A L U hA hT hLU hinv _,
    kappaInfCounted_val A L U hA hT hLU hinv, kappaInfCounted_ops_le A⟩

/-- **§6, the test problem:** *"Since `A` is an M-matrix, `cond(A, x)`, `cond(A)`, and `κ∞(A)`
were computed in `O(n)` flops according to (3.8) (using `y = e` to compute `κ∞(A)`)."* -/
theorem section6_O_n_of_mMatrix (A : Matrix (Fin n) (Fin n) ℝ) (hT : IsTridiagonal A)
    (hM : IsMMatrix A) (x : Fin n → ℝ) :
    ((condAlgCounted A x).1 = condSkeel A x ∧ (condAlgCounted A x).2 ≤ 23 * n + 1) ∧
      ((condAlgCounted A (fun _ => 1)).1 = condSkeelA A ∧
        (condAlgCounted A (fun _ => 1)).2 ≤ 23 * n + 1) ∧
      ((kappaInfCounted A).1 = kappaInf A ∧ (kappaInfCounted A).2 ≤ 22 * n + 1) :=
  section6_O_n_of_type A hM.1 hT (Or.inr (Or.inr (Or.inl hM))) x

end CountedNorms

/-! Sanity checks: the counters are evaluated by the kernel (`decide`), in agreement with
`13 n - 10` and `22 n - 16`. -/

example : (normInvCounted (1 : Matrix (Fin 3) (Fin 3) ℝ)).2 = 29 := by decide

example : (kappaInfCounted (1 : Matrix (Fin 3) (Fin 3) ℝ)).2 = 50 := by decide

/-! ### 2. `cond(A)/cond(A, x)` can be arbitrarily large -/

/-- The sup norm of a vector whose largest entry in absolute value is `v i₀`. -/
lemma norm_eq_of_forall_abs_le {k : ℕ} (v : Fin k → ℝ) (i₀ : Fin k) (h : ∀ i, |v i| ≤ v i₀) :
    ‖v‖ = v i₀ := by
  have h0 : 0 ≤ v i₀ := (abs_nonneg _).trans (h i₀)
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg h0).mpr fun i => by rw [Real.norm_eq_abs]; exact h i
  · have := norm_le_pi_norm v i₀
    rwa [Real.norm_eq_abs, abs_of_nonneg h0] at this

section CondRatio

/-- The matrix `[1 t; 0 1]`: totally nonnegative for `t ≥ 0`, an M-matrix for `t ≤ 0`. -/
def exShear (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; 0, 1]

lemma exShear_isTridiagonal (t : ℝ) : IsTridiagonal (exShear t) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h

lemma exShear_det (t : ℝ) : (exShear t).det = 1 := by
  simp [exShear, det_fin_two]

lemma exShear_isUnit_det (t : ℝ) : IsUnit (exShear t).det := by
  rw [exShear_det]; exact isUnit_one

/-- `[1 t; 0 1]⁻¹ = [1 -t; 0 1]`. -/
lemma exShear_inv (t : ℝ) : (exShear t)⁻¹ = !![1, -t; 0, 1] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exShear, mul_apply, Fin.sum_univ_two]

/-- `|A⁻¹||A| = [1 2|t|; 0 1]` for `A = [1 t; 0 1]`. -/
lemma exShear_absProd (t : ℝ) :
    (exShear t)⁻¹.map abs * (exShear t).map abs = !![1, 2 * |t|; 0, 1] := by
  rw [exShear_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exShear, mul_apply, Fin.sum_univ_two]
  ring

/-- `‖e₁‖∞ = 1` for `e₁ = (1, 0)ᵀ`. -/
lemma norm_vec_one_zero : ‖(![1, 0] : Fin 2 → ℝ)‖ = 1 := by
  rw [norm_fin_two_of_le] <;> simp

/-- `cond(A, e₁) = 1` for `A = [1 t; 0 1]`. -/
theorem exShear_condSkeel (t : ℝ) : condSkeel (exShear t) ![1, 0] = 1 := by
  rw [condSkeel, exShear_absProd, norm_vec_one_zero, div_one]
  rw [norm_fin_two_of_le] <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- `cond(A) = 1 + 2|t|` for `A = [1 t; 0 1]`. -/
theorem exShear_condSkeelA (t : ℝ) : condSkeelA (exShear t) = 1 + 2 * |t| := by
  rw [condSkeelA, condSkeel, exShear_absProd, norm_ones (by norm_num), div_one]
  rw [norm_fin_two_of_le] <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- `cond(A)/cond(A, e₁) = 1 + 2|t|` for `A = [1 t; 0 1]`. -/
theorem exShear_ratio (t : ℝ) :
    condSkeelA (exShear t) / condSkeel (exShear t) ![1, 0] = 1 + 2 * |t| := by
  rw [exShear_condSkeelA, exShear_condSkeel, div_one]

lemma vec_one_zero_ne_zero : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

/-- `[1 t; 0 1]` is totally nonnegative for `t ≥ 0` (Theorem 3.1 (b): its LU factors `I` and
`[1 t; 0 1]` are nonnegative). -/
lemma exShear_isTotallyNonneg {t : ℝ} (ht : 0 ≤ t) : IsTotallyNonneg (exShear t) := by
  rw [theorem_3_1_b_equiv _ (exShear_isUnit_det t) (exShear_isTridiagonal t)]
  refine ⟨1, exShear t, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j h; exact one_apply_ne (ne_of_lt h)
  · intro i; exact one_apply_eq i
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all [exShear]
  · rw [Matrix.one_mul]
  · intro i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_ne h]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [exShear, ht]

/-- `[1 t; 0 1]` is an M-matrix for `t ≤ 0`. -/
lemma exShear_isMMatrix {t : ℝ} (ht : t ≤ 0) : IsMMatrix (exShear t) := by
  refine ⟨exShear_isUnit_det t, ?_, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all [exShear]
  · intro i j; rw [exShear_inv]; fin_cases i <;> fin_cases j <;> simp [ht]

/-- **§6: "`cond(A)/cond(A, x)` can be arbitrarily large."** For every `M` there are a
nonsingular tridiagonal `A ∈ ℝ^{2×2}` and `x ≠ 0` with `cond(A)/cond(A, x) > M`
(`A = [1 |M|; 0 1]`, `x = e₁`, ratio `1 + 2|M|`). -/
theorem condSkeelA_div_condSkeel_unbounded (M : ℝ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ), IsUnit A.det ∧ IsTridiagonal A ∧ x ≠ 0 ∧
      M < condSkeelA A / condSkeel A x := by
  refine ⟨exShear |M|, ![1, 0], exShear_isUnit_det _, exShear_isTridiagonal _,
    vec_one_zero_ne_zero, ?_⟩
  rw [exShear_ratio, abs_abs]
  linarith [le_abs_self M, abs_nonneg M]

/-- The ratio `cond(A)/cond(A, e₁)` tends to `∞` along `A = [1 t; 0 1]`, `t → ∞`. -/
theorem tendsto_exShear_ratio :
    Tendsto (fun t : ℝ => condSkeelA (exShear t) / condSkeel (exShear t) ![1, 0]) atTop atTop := by
  refine tendsto_atTop_mono (fun t => ?_) tendsto_id
  rw [exShear_ratio, id]
  linarith [le_abs_self t, abs_nonneg t]

/-- The ratio is unbounded within the **totally nonnegative** tridiagonal matrices (class (b) of
Theorem 3.1, for which (3.8) computes `cond(A, x)` exactly). -/
theorem condSkeelA_div_condSkeel_unbounded_totallyNonneg (M : ℝ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ), IsUnit A.det ∧ IsTridiagonal A ∧
      IsTotallyNonneg A ∧ x ≠ 0 ∧ M < condSkeelA A / condSkeel A x := by
  refine ⟨exShear |M|, ![1, 0], exShear_isUnit_det _, exShear_isTridiagonal _,
    exShear_isTotallyNonneg (abs_nonneg M), vec_one_zero_ne_zero, ?_⟩
  rw [exShear_ratio, abs_abs]
  linarith [le_abs_self M, abs_nonneg M]

/-- The ratio is unbounded within the tridiagonal **M-matrices** (class (c) of Theorem 3.1). -/
theorem condSkeelA_div_condSkeel_unbounded_mMatrix (M : ℝ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ), IsMMatrix A ∧ IsTridiagonal A ∧ x ≠ 0 ∧
      M < condSkeelA A / condSkeel A x := by
  refine ⟨exShear (-|M|), ![1, 0], exShear_isMMatrix (neg_nonpos.mpr (abs_nonneg M)),
    exShear_isTridiagonal _, vec_one_zero_ne_zero, ?_⟩
  rw [exShear_ratio, abs_neg, abs_abs]
  linarith [le_abs_self M, abs_nonneg M]

/-- The symmetric positive definite matrix `[1 t; t t²+1] = [1 t; 0 1]ᵀ [1 t; 0 1]`. -/
def exShearPD (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; t, t ^ 2 + 1]

lemma exShearPD_isTridiagonal (t : ℝ) : IsTridiagonal (exShearPD t) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h

/-- `[1 t; t t²+1] = [1 t; 0 1]ᴴ I [1 t; 0 1]`. -/
lemma exShearPD_eq (t : ℝ) : exShearPD t = (exShear t)ᴴ * 1 * exShear t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exShearPD, exShear, mul_apply, Fin.sum_univ_two]
  ring

/-- `[1 t; t t²+1]` is (symmetric) positive definite, for every `t`. -/
lemma exShearPD_posDef (t : ℝ) : (exShearPD t).PosDef := by
  rw [exShearPD_eq]
  refine Matrix.PosDef.one.conjTranspose_mul_mul_same ?_
  rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]
  exact exShear_isUnit_det t

/-- `[1 t; t t²+1]⁻¹ = [t²+1 -t; -t 1]` (the determinant is `1`). -/
lemma exShearPD_inv (t : ℝ) : (exShearPD t)⁻¹ = !![t ^ 2 + 1, -t; -t, 1] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exShearPD, mul_apply, Fin.sum_univ_two] <;> ring

/-- `|A⁻¹||A| = [2t²+1  2|t|(t²+1); 2|t|  2t²+1]` for `A = [1 t; t t²+1]`. -/
lemma exShearPD_absProd (t : ℝ) : (exShearPD t)⁻¹.map abs * (exShearPD t).map abs =
    !![2 * t ^ 2 + 1, 2 * |t| * (t ^ 2 + 1); 2 * |t|, 2 * t ^ 2 + 1] := by
  rw [exShearPD_inv]
  have h1 : |t ^ 2 + 1| = t ^ 2 + 1 := abs_of_pos (by positivity)
  have h2 : |t| * |t| = t ^ 2 := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exShearPD, mul_apply, Fin.sum_univ_two, h1] <;>
    nlinarith [h2]

/-- `cond(A, e₁) = 2t² + 1` for `A = [1 t; t t²+1]`. -/
theorem exShearPD_condSkeel (t : ℝ) : condSkeel (exShearPD t) ![1, 0] = 2 * t ^ 2 + 1 := by
  have h2 : |t| * |t| = t ^ 2 := by rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
  rw [condSkeel, exShearPD_absProd, norm_vec_one_zero, div_one]
  rw [norm_fin_two_of_le] <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith [sq_nonneg (|t| - 1), abs_nonneg t]

/-- `cond(A) = 2t² + 1 + 2|t|(t² + 1)` for `A = [1 t; t t²+1]`. -/
theorem exShearPD_condSkeelA (t : ℝ) :
    condSkeelA (exShearPD t) = 2 * t ^ 2 + 1 + 2 * |t| * (t ^ 2 + 1) := by
  rw [condSkeelA, condSkeel, exShearPD_absProd, norm_ones (by norm_num), div_one]
  rw [norm_fin_two_of_le] <;> simp [mulVec, dotProduct, Fin.sum_univ_two]
  · positivity
  · nlinarith [abs_nonneg t, sq_nonneg t]

/-- `cond(A)/cond(A, e₁) ≥ 1 + |t|` for `A = [1 t; t t²+1]`. -/
theorem exShearPD_ratio_ge (t : ℝ) :
    1 + |t| ≤ condSkeelA (exShearPD t) / condSkeel (exShearPD t) ![1, 0] := by
  rw [exShearPD_condSkeelA, exShearPD_condSkeel, le_div_iff₀ (by positivity)]
  nlinarith [abs_nonneg t, sq_nonneg t]

/-- The ratio is unbounded within the **symmetric positive definite** tridiagonal matrices
(class (a) of Theorem 3.1). -/
theorem condSkeelA_div_condSkeel_unbounded_posDef (M : ℝ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ), A.PosDef ∧ IsTridiagonal A ∧ x ≠ 0 ∧
      M < condSkeelA A / condSkeel A x := by
  refine ⟨exShearPD |M|, ![1, 0], exShearPD_posDef _, exShearPD_isTridiagonal _,
    vec_one_zero_ne_zero, ?_⟩
  have := exShearPD_ratio_ge |M|
  rw [abs_abs] at this
  linarith [le_abs_self M]

end CondRatio

/-! #### Every dimension `n ≥ 2` -/

section CondRatioDim

variable {m : ℕ}

/-- `A = I + t E₁₂ ∈ ℝ^{(m+2)×(m+2)}`: the identity with `t` added in position `(1, 2)` (in the
paper's 1-based indexing; `single 0 1 t` in Lean's 0-based indexing). For `m = 0` this is
`[1 t; 0 1]`. -/
def exShearN (m : ℕ) (t : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := 1 + single 0 1 t

lemma fin_one_ne_zero_of_two (m : ℕ) : (1 : Fin (m + 2)) ≠ 0 := by simp

lemma single01_mul_single01 (a b : ℝ) :
    single (0 : Fin (m + 2)) (1 : Fin (m + 2)) a * single 0 1 b = 0 :=
  single_mul_single_of_ne (c := a) (0 : Fin (m + 2)) (1 : Fin (m + 2)) 0
    (fin_one_ne_zero_of_two m) b

/-- `(I - t E₁₂)(I + t E₁₂) = I`, since `E₁₂² = 0`. -/
lemma exShearN_left_inv (t : ℝ) : (1 - single 0 1 t) * exShearN m t = 1 := by
  rw [exShearN, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
    single01_mul_single01]
  abel

lemma exShearN_inv (t : ℝ) : (exShearN m t)⁻¹ = 1 - single 0 1 t :=
  Matrix.inv_eq_left_inv (exShearN_left_inv t)

lemma exShearN_isUnit_det (t : ℝ) : IsUnit (exShearN m t).det :=
  Matrix.isUnit_det_of_left_inverse (exShearN_left_inv t)

lemma exShearN_isTridiagonal (t : ℝ) : IsTridiagonal (exShearN m t) := by
  intro i j h
  simp only [exShearN, Matrix.add_apply, single_apply]
  have hij : i ≠ j := by rintro rfl; omega
  rw [one_apply_ne hij]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    simp at h
  · simp

/-- `|I + c E₁₂| = I + |c| E₁₂`. -/
lemma map_abs_one_add_single (c : ℝ) :
    ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) + single 0 1 c).map abs = 1 + single 0 1 |c| := by
  ext i j
  simp only [map_apply, Matrix.add_apply, single_apply]
  by_cases h : (0 : Fin (m + 2)) = i ∧ (1 : Fin (m + 2)) = j
  · obtain ⟨rfl, rfl⟩ := h
    simp [one_apply_ne (fin_one_ne_zero_of_two m).symm]
  · simp only [h, ite_false, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_ne hij]

/-- `(I + c E₁₂) v = v + c v₂ e₁`. -/
lemma one_add_single_mulVec (c : ℝ) (v : Fin (m + 2) → ℝ) :
    ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) + single 0 1 c) *ᵥ v =
      v + Pi.single 0 (c * v 1) := by
  rw [add_mulVec, one_mulVec, single_mulVec_eq]
  congr 1
  ext i
  simp [Pi.single_apply]

/-- `|A⁻¹||A| = (I + |t| E₁₂)²` for `A = I + t E₁₂`. -/
lemma exShearN_absProd (t : ℝ) :
    (exShearN m t)⁻¹.map abs * (exShearN m t).map abs =
      (1 + single 0 1 |t|) * (1 + single 0 1 |t|) := by
  rw [exShearN_inv, exShearN, map_abs_one_add_single, sub_eq_add_neg, single_neg,
    map_abs_one_add_single, abs_neg]

lemma norm_pi_single_one : ‖(Pi.single 0 1 : Fin (m + 2) → ℝ)‖ = 1 := by
  rw [norm_eq_of_forall_abs_le _ 0]
  · simp
  · intro i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]

/-- `cond(A, e₁) = 1` for `A = I + t E₁₂` (`e₁ = Pi.single 0 1`, the first unit vector). -/
theorem exShearN_condSkeel (t : ℝ) : condSkeel (exShearN m t) (Pi.single 0 1) = 1 := by
  have habs : (fun i => |(Pi.single 0 1 : Fin (m + 2) → ℝ) i|) = Pi.single 0 1 := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  have h1 : ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) + single 0 1 |t|) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
    rw [one_add_single_mulVec, Pi.single_eq_of_ne (fin_one_ne_zero_of_two m), mul_zero,
      Pi.single_zero, add_zero]
  rw [condSkeel, exShearN_absProd, habs, ← mulVec_mulVec, h1, h1, norm_pi_single_one, div_one]

/-- `cond(A) = 1 + 2|t|` for `A = I + t E₁₂`. -/
theorem exShearN_condSkeelA (t : ℝ) : condSkeelA (exShearN m t) = 1 + 2 * |t| := by
  have h2 : ((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) + single 0 1 |t|) *ᵥ
      (((1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) + single 0 1 |t|) *ᵥ fun _ => 1) =
      fun i => if i = 0 then 1 + 2 * |t| else 1 := by
    rw [one_add_single_mulVec, one_add_single_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [fin_one_ne_zero_of_two m]
      ring
    · simp [hi]
  rw [condSkeelA, condSkeel, exShearN_absProd, ← mulVec_mulVec]
  simp only [abs_one]
  rw [h2, norm_ones (by omega), div_one, norm_eq_of_forall_abs_le _ 0]
  · simp
  · intro i
    by_cases hi : i = 0
    · subst hi
      simp only [ite_true]
      rw [abs_of_nonneg (by positivity)]
    · simp only [hi, ite_false, abs_one, ite_true]
      linarith [abs_nonneg t]

end CondRatioDim

/-- **§6: "`cond(A)/cond(A, x)` can be arbitrarily large", in every dimension `n ≥ 2`.** For
every `n ≥ 2` and every `M` there are a nonsingular tridiagonal `A ∈ ℝ^{n×n}` and `x ≠ 0` with
`cond(A)/cond(A, x) > M` (`A = I + |M| E₁₂`, `x = e₁`, ratio `1 + 2|M|`). -/
theorem condSkeelA_div_condSkeel_unbounded_dim {n : ℕ} (hn : 2 ≤ n) (M : ℝ) :
    ∃ (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ), IsUnit A.det ∧ IsTridiagonal A ∧
      x ≠ 0 ∧ M < condSkeelA A / condSkeel A x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  refine ⟨exShearN m |M|, Pi.single 0 1, exShearN_isUnit_det _, exShearN_isTridiagonal _,
    ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · rw [exShearN_condSkeelA, exShearN_condSkeel, div_one, abs_abs]
    linarith [le_abs_self M, abs_nonneg M]

/-- The restriction `n ≥ 2` in `condSkeelA_div_condSkeel_unbounded_dim` is necessary: for
`n = 1` we have `|A⁻¹||A| = 1`, so `cond(A)/cond(A, x) = 1` for every nonsingular `A` and every
`x ≠ 0`. -/
theorem condSkeelA_div_condSkeel_dim_one (A : Matrix (Fin 1) (Fin 1) ℝ) (hA : IsUnit A.det)
    (x : Fin 1 → ℝ) (hx : x ≠ 0) : condSkeelA A / condSkeel A x = 1 := by
  have h1 : A⁻¹.map abs * A.map abs = 1 := by
    have h := congrFun (congrFun (nonsing_inv_mul A hA) 0) 0
    simp only [mul_apply, Fin.sum_univ_one, one_apply_eq] at h
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp only [mul_apply, Fin.sum_univ_one, map_apply, ← abs_mul, h, abs_one, one_apply_eq]
  have hc : ∀ y : Fin 1 → ℝ, y ≠ 0 → condSkeel A y = 1 := by
    intro y hy
    rw [condSkeel, h1, one_mulVec]
    have : ‖fun i => |y i|‖ = ‖y‖ := by
      simp only [Pi.norm_def]
      congr 2
      ext i
      simp
    rw [this, div_self (norm_ne_zero_iff.mpr hy)]
  rw [condSkeelA, hc x hx, hc _ (fun h => by simpa using congrFun h 0), div_one]

/-! ### 3. `κ∞(A)` is not invariant under row scaling -/

section RowScaling

open scoped Matrix.Norms.Operator

/-- `κ∞(I) = 1` (for `n ≥ 1`). -/
lemma kappaInf_one (hn : 0 < n) : kappaInf (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h : ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖ = 1 := by
    rw [linfty_opNorm_eq_norm_abs_mulVec_one]
    have : (1 : Matrix (Fin n) (Fin n) ℝ).map abs = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [one_apply_ne hij]
    rw [this, one_mulVec, norm_ones hn]
  rw [kappaInf, inv_one, h, mul_one]

/-- `diag(1, t)⁻¹ = diag(1, t⁻¹)`. -/
lemma inv_diagonal_pair {t : ℝ} (ht : t ≠ 0) :
    (diagonal ![1, t])⁻¹ = diagonal ![1, t⁻¹] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ht]

/-- `κ∞(diag(1, t)) = t` for `t ≥ 1`. -/
theorem kappaInf_diagonal_pair {t : ℝ} (ht : 1 ≤ t) : kappaInf (diagonal ![1, t]) = t := by
  have ht0 : t ≠ 0 := by positivity
  have htpos : 0 < t := by linarith
  have h1 : ‖(diagonal ![1, t] : Matrix (Fin 2) (Fin 2) ℝ)‖ = t := by
    rw [linfty_opNorm_eq_norm_abs_mulVec_one, norm_eq_of_forall_abs_le _ 1]
    · simp [mulVec, dotProduct, Fin.sum_univ_two, abs_of_pos htpos]
    · intro i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, abs_of_pos htpos, ht]
  have h2 : ‖(diagonal ![1, t⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
    rw [linfty_opNorm_eq_norm_abs_mulVec_one, norm_fin_two_of_le]
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      rw [abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ ht
  rw [kappaInf, inv_diagonal_pair ht0, h1, h2, mul_one]

end RowScaling

/-- **§1: "`κ∞(A)` is not [invariant under row scaling]."** There are a nonsingular
`A ∈ ℝ^{2×2}` and a vector `d` with nonzero entries such that `κ∞(diag(d) A) ≠ κ∞(A)`
(`A = I`, `d = (1, 2)`: `κ∞(diag(d) A) = 2`, `κ∞(A) = 1`). -/
theorem kappaInf_not_row_scaling_invariant :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ), (∀ i, d i ≠ 0) ∧ IsUnit A.det ∧
      kappaInf (diagonal d * A) ≠ kappaInf A := by
  refine ⟨1, ![1, 2], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · simp
  · rw [Matrix.mul_one, kappaInf_diagonal_pair (by norm_num), kappaInf_one (by norm_num)]
    norm_num

/-- **§1: "`cond(A, x)` is invariant under row scaling of `A`, whereas `κ∞(A)` is not."** Both
halves together: for every `A` and every nonsingular diagonal `D = diag(d)`,
`cond(DA, x) = cond(A, x)` for all `x` (`condSkeel_diagonal_mul`), while there is a nonsingular
tridiagonal `A ∈ ℝ^{2×2}` and such a `D` with `κ∞(DA) ≠ κ∞(A)`. -/
theorem condSkeel_row_scaling_invariant_kappaInf_not :
    (∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ), (∀ i, d i ≠ 0) →
        ∀ x, condSkeel (diagonal d * A) x = condSkeel A x) ∧
      ∃ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ), (∀ i, d i ≠ 0) ∧ IsUnit A.det ∧
        IsTridiagonal A ∧ (∀ x, condSkeel (diagonal d * A) x = condSkeel A x) ∧
        kappaInf (diagonal d * A) ≠ kappaInf A := by
  refine ⟨fun m A d hd x => condSkeel_diagonal_mul A d hd x, 1, ![1, 2], ?_, by simp, ?_,
    fun x => condSkeel_diagonal_mul 1 _ ?_ x, ?_⟩
  · intro i; fin_cases i <;> simp
  · intro i j h
    have hij : i ≠ j := by
      rintro rfl; omega
    exact one_apply_ne hij
  · intro i; fin_cases i <;> simp
  · rw [Matrix.mul_one, kappaInf_diagonal_pair (by norm_num), kappaInf_one (by norm_num)]
    norm_num

/-- `κ∞` can even become arbitrarily large under row scaling (whereas `cond(A, x)` does not
change, `condSkeel_diagonal_mul`): `κ∞(diag(1, t) I) = t` for `t ≥ 1`, while `κ∞(I) = 1`. -/
theorem kappaInf_row_scaling_unbounded (M : ℝ) :
    ∃ d : Fin 2 → ℝ, (∀ i, d i ≠ 0) ∧ M < kappaInf (diagonal d * 1) ∧
      kappaInf (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  refine ⟨![1, max M 0 + 1], ?_, ?_, kappaInf_one (by norm_num)⟩
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have := le_max_right M 0
      positivity
  · rw [Matrix.mul_one, kappaInf_diagonal_pair (by linarith [le_max_right M 0])]
    linarith [le_max_left M 0]

end Higham
