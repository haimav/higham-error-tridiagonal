import HighamTridiagonal.Basic

/-!
# Floating point model and backward error analysis (Section 2)

We model a floating point arithmetic with unit roundoff `u` by four operations
`fl(x + y)`, `fl(x - y)`, `fl(x * y)`, `fl(x / y)` satisfying the model (2.4) of the paper:

* (2.4a) `fl(x op y) = (x op y)(1 + δ)`, `|δ| ≤ u`,
* (2.4b) `fl(x op y) = (x op y)/(1 + ε)`, `|ε| ≤ u`,

(for division, whenever the divisor is nonzero).  Gaussian elimination (2.3) followed by forward
and back substitution is then run in this arithmetic, and we prove the backward error results
(2.5), (2.6), (2.7) and the bound (3.3).
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- A floating point arithmetic with unit roundoff `u`, i.e. operations satisfying the model
(2.4a)–(2.4b). -/
structure FPModel (u : ℝ) where
  /-- `fl(x + y)` -/
  add : ℝ → ℝ → ℝ
  /-- `fl(x - y)` -/
  sub : ℝ → ℝ → ℝ
  /-- `fl(x * y)` -/
  mul : ℝ → ℝ → ℝ
  /-- `fl(x / y)` -/
  div : ℝ → ℝ → ℝ
  add_a : ∀ x y, ∃ δ, |δ| ≤ u ∧ add x y = (x + y) * (1 + δ)
  add_b : ∀ x y, ∃ ε, |ε| ≤ u ∧ add x y = (x + y) / (1 + ε)
  sub_a : ∀ x y, ∃ δ, |δ| ≤ u ∧ sub x y = (x - y) * (1 + δ)
  sub_b : ∀ x y, ∃ ε, |ε| ≤ u ∧ sub x y = (x - y) / (1 + ε)
  mul_a : ∀ x y, ∃ δ, |δ| ≤ u ∧ mul x y = (x * y) * (1 + δ)
  mul_b : ∀ x y, ∃ ε, |ε| ≤ u ∧ mul x y = (x * y) / (1 + ε)
  div_a : ∀ x y, y ≠ 0 → ∃ δ, |δ| ≤ u ∧ div x y = (x / y) * (1 + δ)
  div_b : ∀ x y, y ≠ 0 → ∃ ε, |ε| ≤ u ∧ div x y = (x / y) / (1 + ε)

namespace FPModel

/-- Exact arithmetic satisfies the model for every `u ≥ 0`; in particular the model is
consistent. -/
def exact {u : ℝ} (hu : 0 ≤ u) : FPModel u where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  add_a _ _ := ⟨0, by simpa using hu, by simp⟩
  add_b _ _ := ⟨0, by simpa using hu, by simp⟩
  sub_a _ _ := ⟨0, by simpa using hu, by simp⟩
  sub_b _ _ := ⟨0, by simpa using hu, by simp⟩
  mul_a _ _ := ⟨0, by simpa using hu, by simp⟩
  mul_b _ _ := ⟨0, by simpa using hu, by simp⟩
  div_a _ _ _ := ⟨0, by simpa using hu, by simp⟩
  div_b _ _ _ := ⟨0, by simpa using hu, by simp⟩

variable {u : ℝ} (fp : FPModel u)

lemma u_nonneg (fp : FPModel u) : 0 ≤ u := by
  obtain ⟨δ, hδ, -⟩ := fp.add_a 0 0
  exact (abs_nonneg δ).trans hδ

lemma one_add_ne_zero {ε : ℝ} (hu : u < 1) (hε : |ε| ≤ u) : 1 + ε ≠ 0 := by
  have := neg_abs_le ε
  intro h; linarith

/-- (2.4b) for subtraction, in multiplied-out form. -/
lemma sub_b' (hu : u < 1) (x y : ℝ) : ∃ ε, |ε| ≤ u ∧ fp.sub x y * (1 + ε) = x - y := by
  obtain ⟨ε, hε, h⟩ := fp.sub_b x y
  exact ⟨ε, hε, by rw [h, div_mul_cancel₀ _ (one_add_ne_zero hu hε)]⟩

/-- (2.4b) for division, in multiplied-out form. -/
lemma div_b' (hu : u < 1) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∃ ε, |ε| ≤ u ∧ fp.div x y * (1 + ε) * y = x := by
  obtain ⟨ε, hε, h⟩ := fp.div_b x y hy
  exact ⟨ε, hε, by rw [h, div_mul_cancel₀ _ (one_add_ne_zero hu hε), div_mul_cancel₀ _ hy]⟩

lemma div_zero_left {y : ℝ} (hy : y ≠ 0) : fp.div 0 y = 0 := by
  obtain ⟨δ, -, h⟩ := fp.div_a 0 y hy
  rw [h]; simp

/-! ### Gaussian elimination and the substitutions in floating point arithmetic -/

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- The computed pivots `û_i`: `û_0 = d_0`, `û_{i+1} = fl(d_{i+1} - fl(l̂_{i+1} e_i))` with
`l̂_{i+1} = fl(c_{i+1} / û_i)`. -/
def piv : ℕ → ℝ
  | 0 => ent A 0 0
  | i + 1 => fp.sub (ent A (i + 1) (i + 1)) (fp.mul (fp.div (ent A (i + 1) i) (piv i))
      (ent A i (i + 1)))

/-- The computed multipliers `l̂_{i+1} = fl(c_{i+1} / û_i)` (`l̂_0 = 0` is a dummy value). -/
def mult : ℕ → ℝ
  | 0 => 0
  | i + 1 => fp.div (ent A (i + 1) i) (fp.piv A i)

lemma piv_succ (i : ℕ) :
    fp.piv A (i + 1) = fp.sub (ent A (i + 1) (i + 1)) (fp.mul (fp.mult A (i + 1)) (ent A i (i + 1))) :=
  rfl

/-- Gaussian elimination succeeds: all the computed pivots `û_0, …, û_{n-1}` are nonzero (so no
division by zero occurs, neither in the factorization nor in the back substitution). -/
def Succeeds : Prop := ∀ i, i < n → fp.piv A i ≠ 0

/-- The computed factor `L̂` (unit lower bidiagonal). -/
def Lhat : Matrix (Fin n) (Fin n) ℝ := lowerBidiag (fp.mult A)

/-- The computed factor `Û` (upper bidiagonal; its superdiagonal is that of `A`). -/
def Uhat : Matrix (Fin n) (Fin n) ℝ := upperBidiag (fp.piv A) (supd A)

/-- Forward substitution `L̂ y = b`: `ŷ_0 = b_0`, `ŷ_{i+1} = fl(b_{i+1} - fl(l̂_{i+1} ŷ_i))`. -/
def fwd (b : Fin n → ℝ) : ℕ → ℝ
  | 0 => vext b 0
  | i + 1 => fp.sub (vext b (i + 1)) (fp.mul (fp.mult A (i + 1)) (fwd b i))

/-- Back substitution `Û x = y`: `x̂_{n-1} = fl(y_{n-1} / û_{n-1})`,
`x̂_i = fl(fl(y_i - fl(e_i x̂_{i+1})) / û_i)`. -/
def back (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  if h : i + 1 < n then
    fp.div (fp.sub (y i) (fp.mul (ent A i (i + 1)) (back y (i + 1)))) (fp.piv A i)
  else fp.div (y i) (fp.piv A i)
termination_by n - i

/-- The computed solution `x̂` of `A x = b` (Gaussian elimination without pivoting followed by
forward and back substitution, all in floating point arithmetic). -/
def solve (b : Fin n → ℝ) : Fin n → ℝ := fun i => fp.back A (fp.fwd A b) i

lemma back_of_lt (y : ℕ → ℝ) {i : ℕ} (h : i + 1 < n) :
    fp.back A y i = fp.div (fp.sub (y i) (fp.mul (ent A i (i + 1)) (fp.back A y (i + 1))))
      (fp.piv A i) := by
  rw [back, dite_eq_left h]

lemma back_of_not_lt (y : ℕ → ℝ) {i : ℕ} (h : ¬ i + 1 < n) :
    fp.back A y i = fp.div (y i) (fp.piv A i) := by
  rw [back, dite_eq_right h]

lemma vext_solve (b : Fin n → ℝ) (i : ℕ) :
    vext (fp.solve A b) i = if i < n then fp.back A (fp.fwd A b) i else 0 := by
  unfold vext solve
  split_ifs <;> rfl

end FPModel

open FPModel

/-! ### General bidiagonal matrices -/

/-- Lower bidiagonal matrix with diagonal `D` and subdiagonal `l`. -/
def lowerBidiagG (D l : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then D i else if (i : ℕ) = j + 1 then l i else 0

lemma lowerBidiagG_isTridiagonal (D l : ℕ → ℝ) : IsTridiagonal (lowerBidiagG (n := n) D l) := by
  intro i j h
  simp only [lowerBidiagG, of_apply]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

lemma ent_lowerBidiagG (D l : ℕ → ℝ) (i j : ℕ) (hi : i < n) (hj : j < n) :
    ent (lowerBidiagG (n := n) D l) i j = if i = j then D i else if i = j + 1 then l i else 0 := by
  simp [ent, hi, hj, lowerBidiagG]

lemma lowerBidiag_add_lowerBidiagG (l D m : ℕ → ℝ) :
    lowerBidiag (n := n) l + lowerBidiagG D m =
      lowerBidiagG (fun i => 1 + D i) (fun i => l i + m i) := by
  ext i j
  simp only [lowerBidiag, lowerBidiagG, Matrix.add_apply, of_apply]
  split_ifs <;> ring

lemma upperBidiag_add_upperBidiag (p e p' e' : ℕ → ℝ) :
    upperBidiag (n := n) p e + upperBidiag p' e' =
      upperBidiag (fun i => p i + p' i) (fun i => e i + e' i) := by
  ext i j
  simp only [upperBidiag, Matrix.add_apply, of_apply]
  split_ifs <;> ring

lemma ent_sup_mul_vext (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (E : ℕ → ℝ) (k : ℕ)
    (hM : k + 1 < n → ent M k (k + 1) = E k) : ent M k (k + 1) * vext v (k + 1) =
      E k * vext v (k + 1) := by
  by_cases h : k + 1 < n
  · rw [hM h]
  · simp [vext, h]

lemma mulVec_upperBidiag (P E : ℕ → ℝ) (v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    (upperBidiag P E *ᵥ v) ⟨k, hk⟩ = P k * vext v k + E k * vext v (k + 1) := by
  have hsup : ∀ k, k + 1 < n → ent (upperBidiag (n := n) P E) k (k + 1) = E k := fun k hk => by
    rw [ent_upperBidiag _ _ _ _ (by omega) hk]; simp
  cases k with
  | zero =>
    rw [mulVec_tridiag_zero (upperBidiag_isTridiagonal P E) v hk,
      ent_sup_mul_vext _ v E 0 (hsup 0), ent_upperBidiag _ _ _ _ hk hk]
    simp
  | succ k =>
    rw [mulVec_tridiag_succ (upperBidiag_isTridiagonal P E) v hk,
      ent_sup_mul_vext _ v E (k + 1) (hsup (k + 1)), ent_upperBidiag _ _ _ _ hk (by omega),
      ent_upperBidiag _ _ _ _ hk hk]
    simp [show k ≠ k + 1 + 1 by omega]

lemma mulVec_lowerBidiagG_zero (D l : ℕ → ℝ) (v : Fin n → ℝ) (hn : 0 < n) :
    (lowerBidiagG D l *ᵥ v) ⟨0, hn⟩ = D 0 * vext v 0 := by
  rw [mulVec_tridiag_zero (lowerBidiagG_isTridiagonal D l) v hn, ent_lowerBidiagG _ _ _ _ hn hn]
  by_cases h1 : 1 < n
  · rw [ent_lowerBidiagG _ _ _ _ hn h1]; simp
  · simp [vext, h1]

lemma mulVec_lowerBidiagG_succ (D l : ℕ → ℝ) (v : Fin n → ℝ) {k : ℕ} (hk : k + 1 < n) :
    (lowerBidiagG D l *ᵥ v) ⟨k + 1, hk⟩ = l (k + 1) * vext v k + D (k + 1) * vext v (k + 1) := by
  rw [mulVec_tridiag_succ (lowerBidiagG_isTridiagonal D l) v hk,
    ent_lowerBidiagG _ _ _ _ hk (by omega), ent_lowerBidiagG _ _ _ _ hk hk]
  by_cases h2 : k + 2 < n
  · rw [ent_lowerBidiagG _ _ _ _ hk h2]; simp
  · simp [vext, h2]

/-- If `|X| ≤ α|P|` and `|Y| ≤ β|Q|` entrywise then `|XY| ≤ αβ|P||Q|`. -/
lemma abs_mul_le_of_abs_le {X Y P Q : Matrix (Fin n) (Fin n) ℝ} {α β : ℝ}
    (hX : ∀ i j, |X i j| ≤ α * |P i j|) (hY : ∀ i j, |Y i j| ≤ β * |Q i j|) (i j : Fin n) :
    |(X * Y) i j| ≤ α * β * (P.map abs * Q.map abs) i j := by
  refine (abs_mul_le_abs_mul_abs X Y i j).trans ?_
  simp only [mul_apply, map_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  calc |X i k| * |Y k j| ≤ (α * |P i k|) * (β * |Q k j|) :=
        mul_le_mul (hX i k) (hY k j) (abs_nonneg _) ((abs_nonneg _).trans (hX i k))
    _ = α * β * (|P i k| * |Q k j|) := by ring

namespace FPModel

variable {u : ℝ} (fp : FPModel u) (A : Matrix (Fin n) (Fin n) ℝ)

/-! ### Equation (2.5) -/

/-- **(2.5)** `A = L̂ Û + E` with `|E| ≤ u |L̂||Û|`. -/
theorem eq_2_5 (hu : u < 1) (hT : IsTridiagonal A) (hs : fp.Succeeds A) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, A = fp.Lhat A * fp.Uhat A + E ∧
      ∀ i j, |E i j| ≤ u * ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j := by
  refine ⟨A - fp.Lhat A * fp.Uhat A, by abel, fun i j => ?_⟩
  have hu0 := fp.u_nonneg
  suffices h : |ent A i j - ent (fp.Lhat A * fp.Uhat A) i j| ≤
      u * ent ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j by
    simpa [ent_sub] using h
  rw [Lhat, Uhat, lowerBidiag_map_abs, upperBidiag_map_abs]
  have hi := i.2
  have hj := j.2
  rcases lt_trichotomy ((i : ℕ) + 1) j with h | h | h
  · rw [hT.ent_eq_zero (Or.inl h), (isTridiagonal_LU _ _ _).ent_eq_zero (Or.inl h),
      (isTridiagonal_LU _ _ _).ent_eq_zero (Or.inl h)]
    simp
  · rw [← h, ent_LU_sup _ _ _ (by omega), ent_LU_sup _ _ _ (by omega)]
    simp only [supd, sub_self, abs_zero]
    exact mul_nonneg hu0 (abs_nonneg _)
  rcases lt_trichotomy ((j : ℕ) + 1) i with h' | h' | h'
  · rw [hT.ent_eq_zero (Or.inr h'), (isTridiagonal_LU _ _ _).ent_eq_zero (Or.inr h'),
      (isTridiagonal_LU _ _ _).ent_eq_zero (Or.inr h')]
    simp
  · -- subdiagonal: `c_i - l̂_i û_{i-1} = ε l̂_i û_{i-1}`
    rw [← h', ent_LU_sub _ _ _ (by omega), ent_LU_sub _ _ _ (by omega)]
    obtain ⟨ε, hε, heq⟩ := fp.div_b' hu (ent A (j + 1) j) (hs j hj)
    have : ent A (j + 1) j - fp.mult A (j + 1) * fp.piv A j =
        ε * (fp.mult A (j + 1) * fp.piv A j) := by
      rw [← heq]; simp only [mult]; ring
    rw [this, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right hε (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hij : (i : ℕ) = j := by omega
    rw [← hij]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, ent_LU_zero_zero _ _ _ (by omega), ent_LU_zero_zero _ _ _ (by omega)]
      simp only [piv, sub_self, abs_zero]
      exact mul_nonneg hu0 (abs_nonneg _)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h0
      simp only [zero_add] at hk
      rw [hk, ent_LU_diag_succ _ _ _ (by omega), ent_LU_diag_succ _ _ _ (by omega)]
      -- diagonal: `d_i - l̂_i e_{i-1} - û_i = θ û_i + δ l̂_i e_{i-1}`
      obtain ⟨θ, hθ, hsub⟩ := fp.sub_b' hu (ent A (k + 1) (k + 1))
        (fp.mul (fp.mult A (k + 1)) (ent A k (k + 1)))
      obtain ⟨δ, hδ, hmul⟩ := fp.mul_a (fp.mult A (k + 1)) (ent A k (k + 1))
      have hpiv : fp.piv A (k + 1) = fp.sub (ent A (k + 1) (k + 1))
          (fp.mul (fp.mult A (k + 1)) (ent A k (k + 1))) := fp.piv_succ A k
      have : ent A (k + 1) (k + 1) - (fp.mult A (k + 1) * supd A k + fp.piv A (k + 1)) =
          θ * fp.piv A (k + 1) + δ * (fp.mult A (k + 1) * supd A k) := by
        simp only [supd]
        rw [hpiv]
        have h1 := hsub
        rw [hmul] at h1
        linarith
      rw [this]
      calc |θ * fp.piv A (k + 1) + δ * (fp.mult A (k + 1) * supd A k)|
          ≤ |θ| * |fp.piv A (k + 1)| + |δ| * (|fp.mult A (k + 1)| * |supd A k|) := by
            rw [← abs_mul, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ u * |fp.piv A (k + 1)| + u * (|fp.mult A (k + 1)| * |supd A k|) := by
            gcongr
        _ = u * (|fp.mult A (k + 1)| * |supd A k| + |fp.piv A (k + 1)|) := by ring

/-! ### Equation (2.6) -/

/-- **(2.6)** The computed solution satisfies `(L̂ + ΔL)(Û + ΔU) x̂ = b` with `|ΔL| ≤ u |L̂|` and
`|ΔU| ≤ (2u + u²) |Û|`. -/
theorem eq_2_6 (hu : u < 1) (hs : fp.Succeeds A) (b : Fin n → ℝ) :
    ∃ ΔL ΔU : Matrix (Fin n) (Fin n) ℝ,
      ((fp.Lhat A + ΔL) * (fp.Uhat A + ΔU)) *ᵥ fp.solve A b = b ∧
      (∀ i j, |ΔL i j| ≤ u * |fp.Lhat A i j|) ∧
      (∀ i j, |ΔU i j| ≤ (2 * u + u ^ 2) * |fp.Uhat A i j|) := by
  have hu0 := fp.u_nonneg
  set y := fp.fwd A b with hy
  set x := fp.solve A b with hx
  -- rounding errors of the forward substitution
  have hF : ∀ k : ℕ, ∃ δ ε : ℝ, |δ| ≤ u ∧ |ε| ≤ u ∧
      y (k + 1) * (1 + ε) + fp.mult A (k + 1) * (1 + δ) * y k = vext b (k + 1) := by
    intro k
    obtain ⟨δ, hδ, hmul⟩ := fp.mul_a (fp.mult A (k + 1)) (y k)
    obtain ⟨ε, hε, hsub⟩ := fp.sub_b' hu (vext b (k + 1)) (fp.mul (fp.mult A (k + 1)) (y k))
    refine ⟨δ, ε, hδ, hε, ?_⟩
    have : y (k + 1) = fp.sub (vext b (k + 1)) (fp.mul (fp.mult A (k + 1)) (y k)) := rfl
    rw [this, hsub, hmul]; ring
  choose δF εF hδF hεF hFeq using hF
  -- rounding errors of the back substitution
  have hB : ∀ k : ℕ, ∃ η δ : ℝ, |η| ≤ 2 * u + u ^ 2 ∧ |δ| ≤ u ∧ (k < n →
      y k = fp.piv A k * (1 + η) * vext x k + supd A k * (1 + δ) * vext x (k + 1)) := by
    intro k
    by_cases hk : k < n
    · have hpk := hs k hk
      by_cases hk1 : k + 1 < n
      · obtain ⟨δ, hδ, hmul⟩ := fp.mul_a (ent A k (k + 1)) (fp.back A y (k + 1))
        obtain ⟨ε₁, hε₁, hsub⟩ := fp.sub_b' hu (y k) (fp.mul (ent A k (k + 1)) (fp.back A y (k + 1)))
        obtain ⟨ε₂, hε₂, hdiv⟩ := fp.div_b' hu
          (fp.sub (y k) (fp.mul (ent A k (k + 1)) (fp.back A y (k + 1)))) hpk
        refine ⟨ε₁ + ε₂ + ε₁ * ε₂, δ, ?_, hδ, fun _ => ?_⟩
        · calc |ε₁ + ε₂ + ε₁ * ε₂| ≤ |ε₁| + |ε₂| + |ε₁| * |ε₂| := by
                rw [← abs_mul]; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
            _ ≤ u + u + u * u := by gcongr
            _ = 2 * u + u ^ 2 := by ring
        · rw [vext_solve, vext_solve, ite_eq_left hk, ite_eq_left hk1, fp.back_of_lt A y hk1]
          simp only [supd]
          set t := fp.mul (ent A k (k + 1)) (fp.back A y (k + 1)) with ht
          set q := fp.div (fp.sub (y k) t) (fp.piv A k) with hq
          linear_combination (-1 : ℝ) * hsub - (1 + ε₁) * hdiv + hmul
      · obtain ⟨ε₂, hε₂, hdiv⟩ := fp.div_b' hu (y k) hpk
        refine ⟨ε₂, 0, ?_, by simpa using hu0, fun _ => ?_⟩
        · nlinarith [abs_nonneg ε₂]
        · rw [vext_solve, vext_solve, ite_eq_left hk, ite_eq_right hk1,
            fp.back_of_not_lt A y hk1]
          linear_combination (-1 : ℝ) * hdiv
    · exact ⟨0, 0, by simp; positivity, by simpa using hu0, fun h => absurd h hk⟩
  choose ηB δB hηB hδB hBeq using hB
  -- the perturbation matrices
  set ΔL : Matrix (Fin n) (Fin n) ℝ :=
    lowerBidiagG (fun i => if i = 0 then 0 else εF (i - 1))
      (fun i => fp.mult A i * δF (i - 1)) with hΔL
  set ΔU : Matrix (Fin n) (Fin n) ℝ :=
    upperBidiag (fun i => fp.piv A i * ηB i) (fun i => supd A i * δB i) with hΔU
  refine ⟨ΔL, ΔU, ?_, ?_, ?_⟩
  · have hUx : (fp.Uhat A + ΔU) *ᵥ x = fun i : Fin n => y i := by
      funext i
      rw [Uhat, hΔU, upperBidiag_add_upperBidiag, mulVec_upperBidiag _ _ _ i.2,
        hBeq i i.2]
      ring
    have hLy : (fp.Lhat A + ΔL) *ᵥ (fun i : Fin n => y i) = b := by
      funext ⟨i, hi⟩
      rw [Lhat, hΔL, lowerBidiag_add_lowerBidiagG]
      cases i with
      | zero =>
        rw [mulVec_lowerBidiagG_zero _ _ _ hi]
        simp [vext, hy, fwd, hi]
      | succ k =>
        rw [mulVec_lowerBidiagG_succ _ _ _ hi]
        have hyk : vext (fun i : Fin n => y i) k = y k := by simp [vext, show k < n by omega]
        have hyk1 : vext (fun i : Fin n => y i) (k + 1) = y (k + 1) := by simp [vext, hi]
        rw [hyk, hyk1, ite_eq_right (by omega), show k + 1 - 1 = k by omega]
        have := hFeq k
        have hb : vext b (k + 1) = b ⟨k + 1, hi⟩ := by simp [vext, hi]
        rw [hb] at this
        linear_combination this
    rw [← mulVec_mulVec, hUx, hLy]
  · intro i j
    simp only [hΔL, Lhat, lowerBidiagG, lowerBidiag, of_apply]
    split_ifs with h1 h2 h3
    · simp [hu0]
    · simpa using hεF _
    · rw [abs_mul, mul_comm u]
      exact mul_le_mul_of_nonneg_left (hδF _) (abs_nonneg _)
    · simp
  · intro i j
    simp only [hΔU, Uhat, upperBidiag, of_apply]
    split_ifs with h1 h2
    · rw [abs_mul, mul_comm (2 * u + u ^ 2)]
      exact mul_le_mul_of_nonneg_left (hηB _) (abs_nonneg _)
    · rw [abs_mul, mul_comm (2 * u + u ^ 2)]
      refine mul_le_mul_of_nonneg_left ((hδB _).trans ?_) (abs_nonneg _)
      nlinarith
    · simp

/-! ### Equation (2.7) -/

/-- **(2.7)** `(A + F) x̂ = b` with `|F| ≤ f(u) |L̂||Û|`, `f(u) = 4u + 3u² + u³`. -/
theorem eq_2_7 (hu : u < 1) (hT : IsTridiagonal A) (hs : fp.Succeeds A) (b : Fin n → ℝ) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (A + F) *ᵥ fp.solve A b = b ∧
      ∀ i j, |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) *
        ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j := by
  have hu0 := fp.u_nonneg
  obtain ⟨E, hAE, hE⟩ := fp.eq_2_5 A hu hT hs
  obtain ⟨ΔL, ΔU, hsol, hΔL, hΔU⟩ := fp.eq_2_6 A hu hs b
  refine ⟨(fp.Lhat A + ΔL) * (fp.Uhat A + ΔU) - A, by rw [add_sub_cancel]; exact hsol, ?_⟩
  intro i j
  set P := (fp.Lhat A).map abs * (fp.Uhat A).map abs with hP
  have hF : (fp.Lhat A + ΔL) * (fp.Uhat A + ΔU) - A =
      -E + ΔL * fp.Uhat A + fp.Lhat A * ΔU + ΔL * ΔU := by
    have h : (fp.Lhat A + ΔL) * (fp.Uhat A + ΔU) - (fp.Lhat A * fp.Uhat A + E) =
        -E + ΔL * fp.Uhat A + fp.Lhat A * ΔU + ΔL * ΔU := by
      simp only [Matrix.add_mul, Matrix.mul_add]; abel
    rw [← h, ← hAE]
  rw [hF]
  have h1 : |(-E) i j| ≤ u * P i j := by rw [Matrix.neg_apply, abs_neg]; exact hE i j
  have h2 : |(ΔL * fp.Uhat A) i j| ≤ u * 1 * P i j :=
    abs_mul_le_of_abs_le hΔL (fun _ _ => by rw [one_mul]) i j
  have h3 : |(fp.Lhat A * ΔU) i j| ≤ 1 * (2 * u + u ^ 2) * P i j :=
    abs_mul_le_of_abs_le (fun _ _ => by rw [one_mul]) hΔU i j
  have h4 : |(ΔL * ΔU) i j| ≤ u * (2 * u + u ^ 2) * P i j :=
    abs_mul_le_of_abs_le hΔL hΔU i j
  simp only [Matrix.add_apply]
  calc |(-E) i j + (ΔL * fp.Uhat A) i j + (fp.Lhat A * ΔU) i j + (ΔL * ΔU) i j|
      ≤ |(-E) i j| + |(ΔL * fp.Uhat A) i j| + |(fp.Lhat A * ΔU) i j| + |(ΔL * ΔU) i j| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ u * P i j + u * 1 * P i j + 1 * (2 * u + u ^ 2) * P i j + u * (2 * u + u ^ 2) * P i j := by
        gcongr
    _ = (4 * u + 3 * u ^ 2 + u ^ 3) * P i j := by ring

/-! ### Equation (3.3) -/

/-- **(3.3)** If `|L̂||Û| = |L̂ Û|` then `|L̂||Û| ≤ |A| / (1 - u)`. -/
theorem eq_3_3 (hu : u < 1) (hT : IsTridiagonal A) (hs : fp.Succeeds A)
    (habs : (fp.Lhat A).map abs * (fp.Uhat A).map abs = (fp.Lhat A * fp.Uhat A).map abs) :
    ∀ i j, ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j ≤ 1 / (1 - u) * |A i j| := by
  obtain ⟨E, hAE, hE⟩ := fp.eq_2_5 A hu hT hs
  intro i j
  have hpos : 0 < 1 - u := by linarith
  have hP : ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j = |A i j - E i j| := by
    rw [habs, map_apply]
    congr 1
    have := congrFun (congrFun hAE i) j
    rw [Matrix.add_apply] at this
    linarith
  have key : ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j ≤
      |A i j| + u * ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j := by
    have h1 := hE i j
    calc _ = |A i j - E i j| := hP
      _ ≤ |A i j| + |E i j| := abs_sub _ _
      _ ≤ _ := by linarith
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hpos]
  linarith

/-! ### (3.2) implies (3.1) -/

/-- **(3.2) ⟹ (3.1)** (Section 3): if the computed factors satisfy `|L̂||Û| = |L̂ Û|`, then the
computed solution satisfies `(A + F) x̂ = b` with the "ideal" bound `|F| ≤ g(u) |A|`, where
`g(u) = (4u + 3u² + u³) / (1 - u)`. -/
theorem eq_3_1_of_eq_3_2 (hu : u < 1) (hT : IsTridiagonal A) (hs : fp.Succeeds A)
    (habs : (fp.Lhat A).map abs * (fp.Uhat A).map abs = (fp.Lhat A * fp.Uhat A).map abs)
    (b : Fin n → ℝ) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ, (A + F) *ᵥ fp.solve A b = b ∧
      ∀ i j, |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) * |A i j| := by
  have hu0 := fp.u_nonneg
  obtain ⟨F, hF, hFb⟩ := fp.eq_2_7 A hu hT hs b
  have h33 := fp.eq_3_3 A hu hT hs habs
  refine ⟨F, hF, fun i j => ?_⟩
  have hf : 0 ≤ 4 * u + 3 * u ^ 2 + u ^ 3 := by positivity
  calc |F i j| ≤ (4 * u + 3 * u ^ 2 + u ^ 3) *
        ((fp.Lhat A).map abs * (fp.Uhat A).map abs) i j := hFb i j
    _ ≤ (4 * u + 3 * u ^ 2 + u ^ 3) * (1 / (1 - u) * |A i j|) :=
        mul_le_mul_of_nonneg_left (h33 i j) hf
    _ = (4 * u + 3 * u ^ 2 + u ^ 3) / (1 - u) * |A i j| := by ring

end FPModel

end Higham
