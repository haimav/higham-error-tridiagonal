import HighamTridiagonal.FloatingPoint
import HighamTridiagonal.Theorem31

/-!
# Theorem 3.2

*If the tridiagonal matrix `A` is of type (a)–(d) in Theorem 3.1, and if the unit roundoff `u`
is sufficiently small, then Gaussian elimination for solving `Ax = b` succeeds and the computed
solution `x̂` satisfies*
`(A + F) x̂ = b`, `|F| ≤ h(u) |A|`, `h(u) = (4u + 3u² + u³) / (1 - u)`.

"`u` sufficiently small" is formalized as: there is `u₀ > 0` (depending only on `A`) such that
the conclusion holds for every floating point arithmetic `fp : FPModel u` satisfying the model
(2.4) with unit roundoff `u < u₀`, and every right-hand side `b`.

The proof follows the paper: for small `u` the computed pivots `û_i` are close to the exact
pivots `u_i`, so they are nonzero and `|L̂||Û| = |L̂ Û|` still holds; then (2.7) and (3.3) give the
result.  The continuity argument is phrased with the filter `roundoffToZero` on the type of all
arithmetics `Σ u, FPModel u`, which expresses convergence as `u → 0` *uniformly* over all
arithmetics with unit roundoff `u`.
-/

open Matrix Finset Filter Topology

noncomputable section

namespace Higham

variable {n : ℕ}

/-- A floating point arithmetic together with its unit roundoff. -/
abbrev FPArith := Σ u : ℝ, FPModel u

/-- The filter "unit roundoff `u → 0`" on the type of all floating point arithmetics. -/
def roundoffToZero : Filter FPArith := Filter.comap (fun p : FPArith => p.1) (𝓝 0)

lemma tendsto_unitRoundoff : Tendsto (fun p : FPArith => p.1) roundoffToZero (𝓝 0) :=
  tendsto_comap

/-- If `Z → z` and `W` is a relative perturbation of `Z` of size at most `u`, then `W → z`. -/
lemma tendsto_of_relErr {W Z : FPArith → ℝ} {z : ℝ} (hZ : Tendsto Z roundoffToZero (𝓝 z))
    (hWZ : ∀ p : FPArith, |W p - Z p| ≤ p.1 * |Z p|) : Tendsto W roundoffToZero (𝓝 z) := by
  have h1 : Tendsto (fun p : FPArith => p.1 * |Z p|) roundoffToZero (𝓝 0) := by
    simpa using tendsto_unitRoundoff.mul hZ.abs
  have h2 : Tendsto (fun p => W p - Z p) roundoffToZero (𝓝 0) :=
    squeeze_zero_norm' (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hWZ p) h1
  simpa using h2.add hZ

lemma relErr_of_model {u a b δ : ℝ} (hδ : |δ| ≤ u) (h : a = b * (1 + δ)) : |a - b| ≤ u * |b| := by
  rw [h, show b * (1 + δ) - b = δ * b by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

variable {X Y : FPArith → ℝ} {x y : ℝ}

lemma tendsto_fsub (hX : Tendsto X roundoffToZero (𝓝 x)) (hY : Tendsto Y roundoffToZero (𝓝 y)) :
    Tendsto (fun p : FPArith => p.2.sub (X p) (Y p)) roundoffToZero (𝓝 (x - y)) := by
  refine tendsto_of_relErr (hX.sub hY) fun p => ?_
  obtain ⟨δ, hδ, h⟩ := p.2.sub_a (X p) (Y p)
  exact relErr_of_model hδ h

lemma tendsto_fmul (hX : Tendsto X roundoffToZero (𝓝 x)) (hY : Tendsto Y roundoffToZero (𝓝 y)) :
    Tendsto (fun p : FPArith => p.2.mul (X p) (Y p)) roundoffToZero (𝓝 (x * y)) := by
  refine tendsto_of_relErr (hX.mul hY) fun p => ?_
  obtain ⟨δ, hδ, h⟩ := p.2.mul_a (X p) (Y p)
  exact relErr_of_model hδ h

lemma tendsto_fdiv (hX : Tendsto X roundoffToZero (𝓝 x)) (hY : Tendsto Y roundoffToZero (𝓝 y))
    (hy : y ≠ 0) :
    Tendsto (fun p : FPArith => p.2.div (X p) (Y p)) roundoffToZero (𝓝 (x / y)) := by
  have hXY : Tendsto (fun p => X p / Y p) roundoffToZero (𝓝 (x / y)) := hX.div hY hy
  have h1 : Tendsto (fun p : FPArith => p.1 * |X p / Y p|) roundoffToZero (𝓝 0) := by
    simpa using tendsto_unitRoundoff.mul hXY.abs
  have h2 : Tendsto (fun p : FPArith => p.2.div (X p) (Y p) - X p / Y p) roundoffToZero (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [hY.eventually_ne hy] with p hp
    obtain ⟨δ, hδ, h⟩ := p.2.div_a (X p) (Y p) hp
    simpa [Real.norm_eq_abs] using relErr_of_model hδ h
  simpa using h2.add hXY

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- As `u → 0` the computed pivots converge to the exact pivots (uniformly over all arithmetics),
provided the exact pivots `u_0, …, u_{n-1}` are nonzero. -/
theorem tendsto_fpPiv (hp : ∀ k, k < n → piv A k ≠ 0) :
    ∀ k, k < n → Tendsto (fun p : FPArith => p.2.piv A k) roundoffToZero (𝓝 (piv A k)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact tendsto_const_nhds
  | succ k ih =>
    intro hk
    have h := tendsto_fsub (tendsto_const_nhds (x := ent A (k + 1) (k + 1)))
      (tendsto_fmul (tendsto_fdiv (tendsto_const_nhds (x := ent A (k + 1) k)) (ih (by omega))
        (hp k (by omega))) (tendsto_const_nhds (x := ent A k (k + 1))))
    exact h

theorem tendsto_fpMult (hp : ∀ k, k < n → piv A k ≠ 0) {k : ℕ} (hk : k + 1 < n) :
    Tendsto (fun p : FPArith => p.2.mult A (k + 1)) roundoffToZero (𝓝 (mult A (k + 1))) :=
  tendsto_fdiv tendsto_const_nhds (tendsto_fpPiv A hp k (by omega)) (hp k (by omega))

/-- For `u` small enough (uniformly over all arithmetics), Gaussian elimination succeeds and the
computed factors satisfy the sign condition, hence `|L̂||Û| = |L̂ Û|`, provided the exact factors
do. -/
theorem eventually_succeeds_and_sign (hp : ∀ k, k < n → piv A k ≠ 0)
    (hs : ∀ k, k + 1 < n → 0 ≤ mult A (k + 1) * supd A k * piv A (k + 1)) :
    ∀ᶠ p in roundoffToZero, p.2.Succeeds A ∧
      ∀ k, k + 1 < n → 0 ≤ p.2.mult A (k + 1) * supd A k * p.2.piv A (k + 1) := by
  have hpiv : ∀ᶠ p in roundoffToZero, ∀ k : Fin n, p.2.piv A k ≠ 0 :=
    eventually_all.mpr fun k => (tendsto_fpPiv A hp k k.2).eventually_ne (hp k k.2)
  have hsign : ∀ᶠ p in roundoffToZero, ∀ k : Fin n, (k : ℕ) + 1 < n →
      0 ≤ p.2.mult A (k + 1) * supd A k * p.2.piv A (k + 1) := by
    refine eventually_all.mpr fun k => ?_
    by_cases hk : (k : ℕ) + 1 < n
    · by_cases h0 : mult A (k + 1) * supd A k = 0
      · rcases mul_eq_zero.mp h0 with hm | he
        · -- `c_{k+1} = 0`, hence `l̂_{k+1} = fl(0 / û_k) = 0`
          have hc : ent A (k + 1) k = 0 := by
            rw [mult_succ, div_eq_zero_iff] at hm
            exact hm.resolve_right (hp k k.2)
          filter_upwards [hpiv] with p hp'
          intro _
          have : p.2.mult A (k + 1) = 0 := by
            show p.2.div (ent A (k + 1) k) (p.2.piv A k) = 0
            rw [hc]; exact p.2.div_zero_left (hp' k)
          rw [this]; simp
        · filter_upwards with p
          intro _
          rw [he]; simp
      · have hpos : 0 < mult A (k + 1) * supd A k * piv A (k + 1) :=
          lt_of_le_of_ne (hs k hk) (mul_ne_zero h0 (hp (k + 1) hk)).symm
        have hlim : Tendsto (fun p : FPArith => p.2.mult A (k + 1) * supd A k * p.2.piv A (k + 1))
            roundoffToZero (𝓝 (mult A (k + 1) * supd A k * piv A (k + 1))) :=
          ((tendsto_fpMult A hp hk).mul tendsto_const_nhds).mul (tendsto_fpPiv A hp (k + 1) hk)
        filter_upwards [hlim.eventually_const_lt hpos] with p hp'
        intro _
        exact hp'.le
    · exact Eventually.of_forall fun _ h => absurd h hk
  filter_upwards [hpiv, hsign] with p h1 h2
  exact ⟨fun k hk => h1 ⟨k, hk⟩, fun k hk => h2 ⟨k, by omega⟩ hk⟩

/-- **Theorem 3.2.** If the (nonsingular) tridiagonal matrix `A` is of type (a)–(d) in
Theorem 3.1, and if the unit roundoff `u` is sufficiently small, then Gaussian elimination for
solving `Ax = b` succeeds and the computed solution `x̂` satisfies
`(A + F) x̂ = b`, `|F| ≤ h(u) |A|`, with `h(u) = (4u + 3u² + u³) / (1 - u)`. -/
theorem theorem_3_2 (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (h : A.PosDef ∨ IsTotallyNonneg A ∨ IsMMatrix A ∨
      ∃ D₁ D₂ B : Matrix (Fin n) (Fin n) ℝ, D₁.map abs = 1 ∧ D₂.map abs = 1 ∧ A = D₁ * B * D₂ ∧
        (B.PosDef ∨ IsTotallyNonneg B ∨ IsMMatrix B)) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ (u : ℝ) (fp : FPModel u), u < u₀ → ∀ b : Fin n → ℝ,
      fp.Succeeds A ∧
      ∃ F : Matrix (Fin n) (Fin n) ℝ, (A + F) *ᵥ fp.solve A b = b ∧
        ∀ i j, |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) * |A i j| := by
  -- the exact factors satisfy `|L||U| = |LU|` (Theorem 3.1)
  obtain ⟨L, U, hLU, habs⟩ := theorem_3_1 A hA hT h
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  have hs : ∀ k, k + 1 < n → 0 ≤ mult A (k + 1) * supd A k * piv A (k + 1) := by
    rw [← abs_mul_abs_eq_abs_mul_iff, ← hL, ← hU]; exact habs
  -- for `u` small enough the computed factors behave in the same way
  have hev := eventually_succeeds_and_sign A hp hs
  rw [roundoffToZero, eventually_comap, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hgood⟩ := hev
  refine ⟨min ε 1, lt_min hε one_pos, fun u fp hu b => ?_⟩
  have hu0 : 0 ≤ u := fp.u_nonneg
  have hu1 : u < 1 := lt_of_lt_of_le hu (min_le_right _ _)
  have huε : dist u 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hu0]
    exact lt_of_lt_of_le hu (min_le_left _ _)
  obtain ⟨hsucc, hsign⟩ := hgood huε ⟨u, fp⟩ rfl
  refine ⟨hsucc, ?_⟩
  -- `|L̂||Û| = |L̂ Û|`, and then (2.7) and (3.3)
  have habs' : (fp.Lhat A).map abs * (fp.Uhat A).map abs = (fp.Lhat A * fp.Uhat A).map abs :=
    (abs_mul_abs_eq_abs_mul_iff _ _ _).mpr hsign
  exact fp.eq_3_1_of_eq_3_2 A hu1 hT hsucc habs' b

end Higham
