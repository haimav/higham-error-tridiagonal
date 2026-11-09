import HighamTridiagonal.Inverse
import HighamTridiagonal.Determinant

/-!
# Totally nonnegative matrices

A matrix is *totally nonnegative* if all its minors of any order are nonnegative.  A minor is
the determinant of a square submatrix `A[I, J]` with strictly increasing row indices `I` and
column indices `J`; we encode `I, J` as order embeddings `Fin k ↪o Fin n`.

We show that total nonnegativity is preserved by transposition, by left multiplication by a
nonnegative diagonal matrix and by left multiplication by a nonnegative unit lower bidiagonal
matrix; consequently `A = L U` with nonnegative bidiagonal factors (and positive pivots) is
totally nonnegative.  This gives one direction of the equivalence in Theorem 3.1 (b).
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-- `A` is totally nonnegative: all its minors, of any order `k`, are nonnegative. -/
def IsTotallyNonneg (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (k : ℕ) (I J : Fin k ↪o Fin n), 0 ≤ (A.submatrix I J).det

/-- The order embedding of `Fin 1` picking out the index `i`. -/
def pick (i : Fin n) : Fin 1 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun _ => i) (Subsingleton.strictMono _)

namespace IsTotallyNonneg

variable {A M : Matrix (Fin n) (Fin n) ℝ}

/-- The entries (`1 × 1` minors) of a totally nonnegative matrix are nonnegative. -/
lemma entry_nonneg (h : IsTotallyNonneg A) (i j : Fin n) : 0 ≤ A i j := by
  have := h 1 (pick i) (pick j)
  simpa [det_fin_one, pick] using this

lemma ent_nonneg (h : IsTotallyNonneg A) (i j : ℕ) : 0 ≤ ent A i j := by
  by_cases hij : i < n ∧ j < n
  · rw [ent_of_lt A hij.1 hij.2]; exact h.entry_nonneg _ _
  · simp [ent, hij]

lemma transpose (h : IsTotallyNonneg A) : IsTotallyNonneg Aᵀ := by
  intro k I J
  rw [← transpose_submatrix, det_transpose]
  exact h k J I

lemma diagonal_mul (h : IsTotallyNonneg M) {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    IsTotallyNonneg (diagonal d * M) := by
  intro k I J
  have : (diagonal d * M).submatrix I J = of fun a b => (d ∘ I) a * M.submatrix I J a b := by
    ext a b; simp
  rw [this, det_mul_column]
  exact mul_nonneg (Finset.prod_nonneg fun a _ => hd _) (h k I J)

end IsTotallyNonneg

/-- The identity matrix is totally nonnegative. -/
lemma isTotallyNonneg_one : IsTotallyNonneg (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro k I J
  by_cases hrange : ∀ a, ∃ b, I a = J b
  · -- then `I = J`
    have hsub : Finset.univ.image I ⊆ Finset.univ.image J := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb⟩ := hrange a
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩
    have hcard : (Finset.univ.image J).card ≤ (Finset.univ.image I).card := by
      rw [Finset.card_image_of_injective _ I.injective,
        Finset.card_image_of_injective _ J.injective]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hIJ : (I : Fin k → Fin n) = J := by
      rw [← StrictMono.range_inj_of_wellFoundedLT I.strictMono J.strictMono]
      ext x
      have := congrArg (fun s : Finset (Fin n) => x ∈ s) heq
      simpa using this
    have : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix I J = 1 := by
      rw [show (J : Fin k → Fin n) = I from hIJ.symm]
      exact submatrix_one _ I.injective
    rw [this, det_one]; exact zero_le_one
  · simp only [not_forall, not_exists] at hrange
    obtain ⟨a, ha⟩ := hrange
    rw [det_eq_zero_of_row_eq_zero a fun b => by simp [one_apply, ha b]]

/-- The elementary unit lower bidiagonal matrix adding `t` times row `r` to row `r + 1`. -/
def elemLower (r : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lowerBidiag (fun i => if i = r + 1 then t else 0)

lemma elemLower_mul_apply (r : ℕ) (t : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (hr : r + 1 < n)
    (i j : Fin n) :
    (elemLower (n := n) r t * M) i j = M i j + if (i : ℕ) = r + 1 then t * M ⟨r, by omega⟩ j else 0 := by
  rw [show (elemLower (n := n) r t * M) i j = ent (elemLower (n := n) r t * M) i j from
    (ent_coe _ _ _).symm]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
  · rw [elemLower, h0, ent_lowerBidiag_mul_zero, ← h0, ent_coe, ite_eq_right (by omega), add_zero]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h0
    simp only [zero_add] at hk
    rw [elemLower, hk, ent_lowerBidiag_mul_succ _ _ (by omega) j.2, ← hk, ent_coe]
    split_ifs with h1
    · have : k = r := by omega
      subst this
      rw [ent_of_lt M (by omega) j.2]; ring
    · ring

/-- Adding a nonnegative multiple of row `r` to row `r + 1` preserves total nonnegativity. -/
theorem IsTotallyNonneg.elemLower_mul {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsTotallyNonneg M)
    {r : ℕ} (hr : r + 1 < n) {t : ℝ} (ht : 0 ≤ t) : IsTotallyNonneg (elemLower r t * M) := by
  intro k I J
  set R : Fin n := ⟨r, by omega⟩ with hR
  set S : Fin n := ⟨r + 1, hr⟩ with hS
  by_cases hI : ∃ a, I a = S
  · obtain ⟨a, ha⟩ := hI
    have hrow : (elemLower r t * M).submatrix I J =
        (M.submatrix I J).updateRow a (M.submatrix I J a + t • fun b => M R (J b)) := by
      ext b c
      rw [submatrix_apply, elemLower_mul_apply r t M hr]
      by_cases hb : b = a
      · subst hb
        rw [updateRow_self]
        simp [hS, hR, ha]
      · rw [updateRow_ne hb]
        have : (I b : ℕ) ≠ r + 1 := by
          intro h'
          exact hb (I.injective (Fin.ext (by rw [h', ha])))
        simp [this]
    rw [hrow, det_updateRow_add, updateRow_eq_self, det_updateRow_smul]
    apply add_nonneg (hM k I J) (mul_nonneg ht _)
    by_cases hR' : ∃ a', I a' = R
    · obtain ⟨a', ha'⟩ := hR'
      have hne : a' ≠ a := by
        intro h'; subst h'; rw [ha] at ha'; simp [hS, hR] at ha'
      rw [det_zero_of_row_eq hne]
      ext c
      rw [updateRow_ne hne, updateRow_self, submatrix_apply, ha']
    · simp only [not_exists] at hR'
      -- replace row index `r + 1` by `r`
      have hmono : StrictMono (Function.update (I : Fin k → Fin n) a R) := by
        intro b c hbc
        have hIbc := I.strictMono hbc
        by_cases hb : b = a
        · subst hb
          have hc : c ≠ b := ne_of_gt hbc
          rw [Function.update_self, Function.update_of_ne hc]
          rw [ha] at hIbc
          exact lt_trans (show R < S from Fin.mk_lt_mk.mpr (by omega)) hIbc
        · by_cases hc : c = a
          · subst hc
            rw [Function.update_self, Function.update_of_ne hb]
            rw [ha] at hIbc
            have h1 : (I b : ℕ) < r + 1 := hIbc
            have h2 : (I b : ℕ) ≠ r := fun h' => hR' b (Fin.ext h')
            exact Fin.lt_def.mpr (show (I b : ℕ) < r by omega)
          · rw [Function.update_of_ne hb, Function.update_of_ne hc]
            exact hIbc
      set I' : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono _ hmono with hI'
      have : (M.submatrix I J).updateRow a (fun b => M R (J b)) = M.submatrix I' J := by
        ext b c
        by_cases hb : b = a
        · subst hb; simp [hI']
        · rw [updateRow_ne hb]; simp [hI', Function.update_of_ne hb]
      rw [this]
      exact hM k I' J
  · simp only [not_exists] at hI
    have : (elemLower r t * M).submatrix I J = M.submatrix I J := by
      ext b c
      rw [submatrix_apply, elemLower_mul_apply r t M hr]
      have : (I b : ℕ) ≠ r + 1 := fun h' => hI b (Fin.ext h')
      simp [this]
    rw [this]; exact hM k I J

/-- Truncation of the subdiagonal sequence `l` to the indices `≤ m`. -/
def truncSeq (l : ℕ → ℝ) (m : ℕ) : ℕ → ℝ := fun i => if i ≤ m then l i else 0

lemma lowerBidiag_truncSeq_succ (l : ℕ → ℝ) (m : ℕ) (hm : m + 1 < n) :
    lowerBidiag (n := n) (truncSeq l (m + 1)) =
      lowerBidiag (truncSeq l m) * elemLower m (l (m + 1)) := by
  apply ext_ent
  intro i j hi hj
  rw [ent_lowerBidiag _ _ _ hi hj]
  unfold elemLower
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [ent_lowerBidiag_mul_zero, ent_lowerBidiag _ _ _ hi hj]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h0
    simp only [zero_add] at hi ⊢
    rw [ent_lowerBidiag_mul_succ _ _ hi hj, ent_lowerBidiag _ _ _ (by omega) hj,
      ent_lowerBidiag _ _ _ hi hj]
    simp only [truncSeq]
    rcases (show j = k ∨ j = k + 1 ∨ k = j + 1 ∨ (j + 1 < k ∨ k + 1 < j) by omega)
      with h | h | h | h
    · subst h
      simp only [show j + 1 ≠ j by omega, ite_true, ite_false, mul_one]
      split_ifs <;> first | ring1 | (exfalso; omega) |
        (obtain rfl : j = m := by omega
         ring1)
    · subst h
      simp only [show k ≠ k + 1 by omega, show k ≠ k + 1 + 1 by omega, ite_true, ite_false,
        mul_zero, zero_add]
    · subst h
      simp only [show j + 1 + 1 ≠ j by omega, show j + 1 + 1 ≠ j + 1 by omega,
        show j + 1 ≠ j by omega, ite_true, ite_false, add_zero]
      split_ifs <;> first | ring1 | (exfalso; omega)
    · simp only [show k + 1 ≠ j by omega, show k + 1 ≠ j + 1 by omega, show k ≠ j by omega,
        show k ≠ j + 1 by omega, ite_false, mul_zero, add_zero]

/-- Left multiplication by a unit lower bidiagonal matrix with nonnegative subdiagonal preserves
total nonnegativity. -/
theorem IsTotallyNonneg.lowerBidiag_mul {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsTotallyNonneg M)
    {l : ℕ → ℝ} (hl : ∀ i, 0 < i → i < n → 0 ≤ l i) : IsTotallyNonneg (lowerBidiag l * M) := by
  have key : ∀ m, ∀ M : Matrix (Fin n) (Fin n) ℝ, IsTotallyNonneg M →
      IsTotallyNonneg (lowerBidiag (truncSeq l m) * M) := by
    intro m
    induction m with
    | zero =>
      intro M hM
      have : lowerBidiag (n := n) (truncSeq l 0) = 1 := by
        ext i j
        simp only [lowerBidiag, of_apply, truncSeq, one_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [this, Matrix.one_mul]; exact hM
    | succ m ih =>
      intro M hM
      by_cases hm : m + 1 < n
      · rw [lowerBidiag_truncSeq_succ l m hm, Matrix.mul_assoc]
        exact ih _ (hM.elemLower_mul hm (hl (m + 1) (by omega) hm))
      · have : lowerBidiag (n := n) (truncSeq l (m + 1)) = lowerBidiag (truncSeq l m) :=
          lowerBidiag_congr fun i _ hi => by
            simp only [truncSeq]
            split_ifs <;> first | rfl | (exfalso; omega)
        rw [this]; exact ih M hM
  have : lowerBidiag (n := n) l = lowerBidiag (truncSeq l n) :=
    lowerBidiag_congr fun i _ hi => by simp [truncSeq, hi.le]
  rw [this]; exact key n M hM

/-- A product `L U` of a nonnegative unit lower bidiagonal matrix and a nonnegative upper
bidiagonal matrix with positive diagonal is totally nonnegative. -/
theorem isTotallyNonneg_lowerBidiag_mul_upperBidiag {l p e : ℕ → ℝ}
    (hl : ∀ i, 0 < i → i < n → 0 ≤ l i) (hp : ∀ i, i < n → 0 < p i)
    (he : ∀ i, i + 1 < n → 0 ≤ e i) :
    IsTotallyNonneg (lowerBidiag (n := n) l * upperBidiag p e) := by
  set v : ℕ → ℝ := fun i => e (i - 1) / p (i - 1) with hv
  have hU : upperBidiag (n := n) p e = diagonal (fun i : Fin n => p i) * (lowerBidiag v)ᵀ := by
    ext i j
    simp only [upperBidiag, of_apply, diagonal_mul, transpose_apply, lowerBidiag, hv]
    split_ifs with h1 h2 h3 h4 h5 <;> try first | ring1 | (exfalso; omega)
    · have : (j : ℕ) - 1 = i := by omega
      rw [this]
      field_simp [(hp i i.2).ne']
  have hvnn : ∀ i, 0 < i → i < n → 0 ≤ v i := fun i hi0 hi =>
    div_nonneg (he _ (by omega)) (hp _ (by omega)).le
  have hW : IsTotallyNonneg (lowerBidiag (n := n) v) := by
    have := isTotallyNonneg_one.lowerBidiag_mul hvnn
    rwa [Matrix.mul_one] at this
  rw [hU]
  exact (hW.transpose.diagonal_mul fun i => (hp i i.2).le).lowerBidiag_mul hl

/-- For a nonsingular tridiagonal totally nonnegative matrix all leading principal minors are
positive. -/
theorem IsTotallyNonneg.leadMinor_pos {A : Matrix (Fin n) (Fin n) ℝ} (hTN : IsTotallyNonneg A)
    (hA : IsUnit A.det) (hT : IsTridiagonal A) : ∀ m, m ≤ n → 0 < leadMinor A m := by
  have hnn : ∀ m, m ≤ n → 0 ≤ leadMinor A m := by
    intro m hm
    rw [leadMinor_eq_det_submatrix A hm]
    exact hTN m (Fin.castLEOrderEmb hm) (Fin.castLEOrderEmb hm)
  have hne : ∀ m, m ≤ n → leadMinor A m ≠ 0 := by
    intro m hm h0
    -- two consecutive vanishing minors propagate to `D_n = det A`
    have hm0 : m ≠ 0 := by rintro rfl; rw [leadMinor_zero] at h0; exact one_ne_zero h0
    have hmn : m ≠ n := by rintro rfl; rw [leadMinor_self] at h0; exact hA.ne_zero h0
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_lt (Nat.pos_of_ne_zero hm0)
    simp only [zero_add] at *
    have h1 : leadMinor A (m' + 2) = 0 := by
      have hrec := leadMinor_succ_succ hT m'
      rw [h0, mul_zero, zero_sub] at hrec
      have hc := hTN.ent_nonneg (m' + 1) m'
      have he := hTN.ent_nonneg m' (m' + 1)
      have hD := hnn m' (by omega)
      have hD2 := hnn (m' + 2) (by omega)
      have : 0 ≤ ent A (m' + 1) m' * ent A m' (m' + 1) * leadMinor A m' :=
        mul_nonneg (mul_nonneg hc he) hD
      linarith
    have hprop : ∀ d, leadMinor A (m' + 1 + d) = 0 ∧ leadMinor A (m' + 1 + d + 1) = 0 := by
      intro d
      induction d with
      | zero => exact ⟨h0, h1⟩
      | succ d ih =>
        refine ⟨ih.2, ?_⟩
        have hrec := leadMinor_succ_succ hT (m' + 1 + d)
        rw [show m' + 1 + (d + 1) + 1 = m' + 1 + d + 2 by ring, hrec, ih.1, ih.2]
        ring
    have := (hprop (n - (m' + 1))).1
    rw [show m' + 1 + (n - (m' + 1)) = n by omega, leadMinor_self] at this
    exact hA.ne_zero this
  exact fun m hm => lt_of_le_of_ne (hnn m hm) (hne m hm).symm

end Higham
