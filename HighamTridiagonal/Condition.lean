import HighamTridiagonal.Basic

/-!
# Skeel's condition numbers and the forward error bound (1.5)

* `cond(A, x) = ‖ |A⁻¹| |A| |x| ‖_∞ / ‖x‖_∞`,
* `cond(A) = cond(A, e)`, `e = (1, …, 1)ᵀ`,
* (1.5): if `A x = b`, `(A + E) x̂ = b` and `|E| ≤ ε |A|` (in the paper `ε = c''_n u`) with
  `cond(A) ε < 1`, then `‖x - x̂‖_∞ / ‖x‖_∞ ≤ cond(A, x) ε / (1 - cond(A) ε)`.

The `∞`-norm of `v : Fin n → ℝ` is Mathlib's sup norm `‖v‖`.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- Skeel's condition number `cond(A, x) = ‖ |A⁻¹| |A| |x| ‖_∞ / ‖x‖_∞`. -/
def condSkeel (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ‖(A⁻¹.map abs * A.map abs) *ᵥ (fun i => |x i|)‖ / ‖x‖

/-- `cond(A) = cond(A, e)` with `e = (1, 1, …, 1)ᵀ`. -/
def condSkeelA (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := condSkeel A (fun _ => 1)

lemma norm_ones (hn : 0 < n) : ‖(fun _ : Fin n => (1 : ℝ))‖ = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [pi_norm_const]; simp

lemma nonneg_absProd (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    0 ≤ (A⁻¹.map abs * A.map abs) i j := by
  rw [mul_apply]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- `‖ |A⁻¹||A| |v| ‖_∞ ≤ cond(A) ‖v‖_∞`. -/
lemma norm_absProd_le (A : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) (v : Fin n → ℝ) :
    ‖(A⁻¹.map abs * A.map abs) *ᵥ (fun i => |v i|)‖ ≤ condSkeelA A * ‖v‖ := by
  set M := A⁻¹.map abs * A.map abs with hMdef
  have hM := nonneg_absProd A
  have hcond : condSkeelA A = ‖M *ᵥ (fun _ => (1 : ℝ))‖ := by
    rw [condSkeelA, condSkeel, norm_ones hn, div_one]; simp [hMdef]
  have hle : ∀ i, (M *ᵥ (fun i => |v i|)) i ≤ ‖v‖ * (M *ᵥ (fun _ => (1 : ℝ))) i := by
    intro i
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := norm_le_pi_norm v j
    rw [Real.norm_eq_abs] at this
    calc M i j * |v j| ≤ M i j * ‖v‖ := mul_le_mul_of_nonneg_left this (hM i j)
      _ = ‖v‖ * (M i j * 1) := by ring
  rw [hcond]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mulVec_nonneg_of_nonneg hM (fun _ => abs_nonneg _) i)]
  refine (hle i).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have := norm_le_pi_norm (M *ᵥ (fun _ => (1 : ℝ))) i
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- `cond(A, x) ≤ cond(A)` (Section 6). -/
theorem condSkeel_le_condSkeelA (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ≠ 0) :
    condSkeel A x ≤ condSkeelA A := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim x 0) hx
    · exact h
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [condSkeel, div_le_iff₀ hxpos]
  exact norm_absProd_le A hn x

/-- **(1.5)** Forward error bound from a componentwise backward error: if `A x = b`,
`(A + E) x̂ = b`, `|E| ≤ ε |A|` and `cond(A) ε < 1`, then
`‖x - x̂‖_∞ / ‖x‖_∞ ≤ cond(A, x) ε / (1 - cond(A) ε)`. -/
theorem eq_1_5 (A E : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (x xhat b : Fin n → ℝ)
    (hx : A *ᵥ x = b) (hx0 : x ≠ 0) (hxhat : (A + E) *ᵥ xhat = b) {ε : ℝ} (hε : 0 ≤ ε)
    (hE : ∀ i j, |E i j| ≤ ε * |A i j|) (hc : condSkeelA A * ε < 1) :
    ‖x - xhat‖ / ‖x‖ ≤ condSkeel A x * ε / (1 - condSkeelA A * ε) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim x 0) hx0
    · exact h
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set M := A⁻¹.map abs * A.map abs with hMdef
  have hM : ∀ i j, 0 ≤ M i j := nonneg_absProd A
  set d := x - xhat with hd
  -- `x - x̂ = A⁻¹ E x̂`
  have hdeq : d = A⁻¹ *ᵥ (E *ᵥ xhat) := by
    have h1 : A *ᵥ d = E *ᵥ xhat := by
      rw [hd, mulVec_sub, hx, ← hxhat, add_mulVec]; abel
    rw [← h1, mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
  -- `|x - x̂| ≤ ε |A⁻¹||A| (|x| + |x - x̂|)`
  have hcomp : ∀ i, |d i| ≤ ε * (M *ᵥ (fun j => |x j|)) i + ε * (M *ᵥ (fun j => |d j|)) i := by
    intro i
    have step1 : |d i| ≤ (A⁻¹.map abs *ᵥ fun j => |(E *ᵥ xhat) j|) i := by
      rw [hdeq]; exact abs_mulVec_le _ _ i
    have step2 : ∀ j, |(E *ᵥ xhat) j| ≤ ε * (A.map abs *ᵥ fun k => |xhat k|) j := by
      intro j
      refine (abs_mulVec_le E xhat j).trans ?_
      simp only [mulVec, dotProduct, map_apply, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hE j k) (abs_nonneg _)
    have step3 : ∀ k, |xhat k| ≤ |x k| + |d k| := by
      intro k
      have : xhat k = x k - d k := by simp [hd]
      rw [this]; exact abs_sub _ _
    calc |d i| ≤ (A⁻¹.map abs *ᵥ fun j => |(E *ᵥ xhat) j|) i := step1
      _ ≤ (A⁻¹.map abs *ᵥ fun j => ε * (A.map abs *ᵥ fun k => |xhat k|) j) i :=
          mulVec_mono_of_nonneg (fun _ _ => abs_nonneg _) step2 i
      _ = ε * (M *ᵥ fun k => |xhat k|) i := by
          rw [hMdef, ← mulVec_mulVec]
          simp only [mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ ε * (M *ᵥ fun k => |x k| + |d k|) i :=
          mul_le_mul_of_nonneg_left (mulVec_mono_of_nonneg hM step3 i) hε
      _ = ε * (M *ᵥ (fun j => |x j|)) i + ε * (M *ᵥ (fun j => |d j|)) i := by
          rw [← mul_add]
          congr 1
          simp only [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  -- take norms
  have hnorm : ‖d‖ ≤ ε * (condSkeel A x * ‖x‖) + ε * (condSkeelA A * ‖d‖) := by
    have h1 : ‖M *ᵥ (fun j => |x j|)‖ = condSkeel A x * ‖x‖ := by
      rw [condSkeel, div_mul_cancel₀ _ hxpos.ne']
    have h2 : ‖M *ᵥ (fun j => |d j|)‖ ≤ condSkeelA A * ‖d‖ := norm_absProd_le A hn d
    refine (pi_norm_le_iff_of_nonneg (by
      have := condSkeel_le_condSkeelA A x hx0
      have hc0 : 0 ≤ condSkeel A x := div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hcA : 0 ≤ condSkeelA A := le_trans hc0 this
      positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine (hcomp i).trans ?_
    have hx' : (M *ᵥ (fun j => |x j|)) i ≤ ‖M *ᵥ (fun j => |x j|)‖ := by
      have := norm_le_pi_norm (M *ᵥ (fun j => |x j|)) i
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have hd' : (M *ᵥ (fun j => |d j|)) i ≤ ‖M *ᵥ (fun j => |d j|)‖ := by
      have := norm_le_pi_norm (M *ᵥ (fun j => |d j|)) i
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    rw [← h1]
    gcongr
    exact hd'.trans h2
  have hpos : 0 < 1 - condSkeelA A * ε := by linarith
  rw [div_le_div_iff₀ hxpos hpos]
  nlinarith [norm_nonneg d]

end Higham
