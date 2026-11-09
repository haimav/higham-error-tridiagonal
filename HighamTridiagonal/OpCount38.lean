import HighamTridiagonal.Algorithm38

/-!
# The algorithm (3.8) for `cond(A, x)`: correctness under the paper's hypothesis and an exact
operation count

Section 3 of the paper (p. 526) says: *if `|A⁻¹| = |U⁻¹||L⁻¹|` and `y ≥ 0` then
`|A⁻¹| y = |U⁻¹||L⁻¹| y = M(U)⁻¹ M(L)⁻¹ y`.  By taking `y = |A||x|` it follows that `cond(A, x)`
can be computed in `O(n)` operations:*

    form y = |A||x|,  solve M(L) v = y,  solve M(U) w = v,  compute ‖w‖∞ / ‖x‖∞.      (3.8)

`Algorithm38.lean` proves this (`eq_3_8`, `condAlg_eq_condSkeel`) under the stronger hypothesis
`|L||U| = |A|` of Theorem 3.3, and it does not count operations.  This file adds:

* `eq_3_8'`, `condAlg_eq_condSkeel'`: (3.8) under exactly the paper's hypothesis
  `|A⁻¹| = |U⁻¹||L⁻¹|`.
* `condAlgCounted A x : ℝ × ℕ`: an implementation of the whole computation, starting from `A`
  and `x`, that returns the computed value together with the number of arithmetic operations it
  performed.
* `condAlgCounted_val`: if `|A⁻¹| = |U⁻¹||L⁻¹|`, the value is `cond(A, x)`, for every `x`
  (for `x = 0` both sides are `0`, because division by zero is zero in Lean);
  `condAlgCounted_val_of_abs`: the same under `|L||U| = |A|` (via Theorem 3.3).
* `condAlgCounted_ops`: for every `A` and `x` the computation performs exactly `23 n - 16`
  operations if `n ≥ 1` (and `1`, the final division, if `n = 0`); `condAlgCounted_ops_le`:
  at most `23 n + 1`.  `eq_3_8_counted` combines value and count.

## The cost model

A computation is a value of `OpCount.Counted α`: a result of type `α` together with a natural
number, the number of arithmetic operations performed to obtain it.  `Counted` is a writer
monad: `pure a` costs nothing, and `m >>= f` costs the cost of `m` plus the cost of `f` applied
to the value of `m`.  The only computations with a nonzero cost are the six primitives

    addOp a b = a + b,  subOp a b = a - b,  mulOp a b = a * b,  divOp a b = a / b,
    absOp a = |a|,      maxOp a b = max a b,

each of cost `1`, each applied to values that are already available.  Everything else is free:
reading an entry of `A` or `x` (`ent A i j`, `List.ofFn x`), building and taking apart lists,
and control flow (testing whether a list is empty or whether `n = 0`).  The algorithm is written
in `do` notation in this monad, so the count is produced by the same recursion that produces the
values: the counter is incremented exactly where an arithmetic operation is performed.

## The algorithm

Each pass is a single pass: a structural recursion on a list (or on the number of steps left)
that carries the previously computed value (the backward pass instead returns the computed
suffix and reads off its head).  With `c_i = a_{i,i-1}`, `d_i = a_{ii}`, `e_i = a_{i,i+1}`
(0-based indices):

* (a) `luPass`: the recurrence (2.3): `u_0 = d_0`, `l_i = c_i / u_{i-1}`,
  `u_i = d_i - l_i e_{i-1}` for `i = 1, …, n-1`: `3 (n - 1)` operations.  The computed pivots
  and multipliers are `piv A i` and `mult A i` (`luPass_val`, `luPass_piv`, `luPass_mult`).
* (b) `absPass`: `|x_0|, …, |x_{n-1}|` (`n` operations).  `rowPass`: row by row,
  `y_i = |d_i||x_i| + |c_i||x_{i-1}| + |e_i||x_{i+1}|`, using only the three tridiagonal entries
  of row `i`; the terms with `x_{-1}` and `x_n` are absent.  This costs `2` operations plus `3`
  for each neighbour: `8 n - 6` operations for `n ≥ 1`.
* (c) `fwdPass`: `v_0 = y_0`, `v_i = y_i + |l_i| v_{i-1}` (solves `M(L) v = y`):
  `3 (n - 1)` operations.
* (d) `bwdPass`: `w_{n-1} = v_{n-1} / |u_{n-1}|`, `w_i = (v_i + |e_i| w_{i+1}) / |u_i|`
  (solves `M(U) w = v`): `5 n - 3` operations for `n ≥ 1`.
* (e) `absPass` and `maxPass`: `‖w‖∞` as the running maximum of `|w_0|, …, |w_{n-1}|`
  (`2 n - 1` operations), `‖x‖∞` as the running maximum of the `|x_i|` computed in (b)
  (`n - 1` operations), and the final division (`1` operation).

Total for `n ≥ 1`:
`3(n-1) + n + (8n-6) + 3(n-1) + (5n-3) + (2n-1) + (n-1) + 1 = 23 n - 16`.

The intermediate results are related to the existing (non-counted) recurrences `solveCompL` and
`solveCompU` of `Algorithm38.lean`, and `condAlgCounted_fst_eq_condAlg` shows that the value of
`condAlgCounted A x` is `condAlg A x` for every tridiagonal `A`.  The helper definitions and
lemmas live in the namespace `Higham.OpCount`.
-/

open Matrix Finset

noncomputable section

namespace Higham

variable {n : ℕ}

/-! ### (3.8) under the paper's hypothesis `|A⁻¹| = |U⁻¹||L⁻¹|` -/

/-- **(3.8)** under exactly the paper's hypothesis: if the nonsingular tridiagonal matrix
`A = LU` satisfies `|A⁻¹| = |U⁻¹||L⁻¹|`, then for any solutions `v`, `w` of `M(L) v = |A||x|` and
`M(U) w = v` we have `cond(A, x) = ‖w‖_∞ / ‖x‖_∞`. -/
theorem eq_3_8' (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (hT : IsTridiagonal A)
    (hLU : IsLU A L U) (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs) (x v w : Fin n → ℝ)
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
  have : w = (A⁻¹.map abs * A.map abs) *ᵥ fun i => |x i| := by
    rw [hw', hv', ← abs_inv_mulVec_eq_comparison A L U hA hT hLU hinv, mulVec_mulVec]
  rw [this, condSkeel]

/-- **(3.8), algorithmic form**, under exactly the paper's hypothesis `|A⁻¹| = |U⁻¹||L⁻¹|`: the
`O(n)` recurrences `condAlg` compute `cond(A, x)`. -/
theorem condAlg_eq_condSkeel' (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs)
    (x : Fin n → ℝ) : condAlg A x = condSkeel A x := by
  obtain ⟨hp, hL, hU⟩ := hLU.eq_recurrence hA hT
  apply eq_3_8' A L U hA hT hLU hinv x
    (fun i => solveCompL (mult A) (A.map abs *ᵥ fun j => |x j|) i)
  · rw [hL]; exact comparison_lowerBidiag_mulVec_solveCompL _ _
  · rw [hU]; exact comparison_upperBidiag_mulVec_solveCompU _ hp _

namespace OpCount

/-! ### The cost model -/

/-- A computation returning a value of type `α` together with the number of arithmetic
operations it performed. -/
structure Counted (α : Type) where
  /-- The computed value. -/
  val : α
  /-- The number of arithmetic operations performed. -/
  ops : ℕ

namespace Counted

/-- `Counted` is a writer monad for `(ℕ, +)`: `pure` costs nothing and the cost of `m >>= f` is
the cost of `m` plus the cost of `f` at the value of `m`. -/
instance : Monad Counted where
  pure a := ⟨a, 0⟩
  bind m f := ⟨(f m.val).val, m.ops + (f m.val).ops⟩

variable {α β : Type}

@[simp] lemma val_pure (a : α) : (pure a : Counted α).val = a := rfl
@[simp] lemma ops_pure (a : α) : (pure a : Counted α).ops = 0 := rfl
@[simp] lemma val_bind (m : Counted α) (f : α → Counted β) : (m >>= f).val = (f m.val).val :=
  rfl
@[simp] lemma ops_bind (m : Counted α) (f : α → Counted β) :
    (m >>= f).ops = m.ops + (f m.val).ops := rfl

end Counted

open Counted

/-- One addition `a + b` (cost `1`). -/
def addOp (a b : ℝ) : Counted ℝ := ⟨a + b, 1⟩
/-- One subtraction `a - b` (cost `1`). -/
def subOp (a b : ℝ) : Counted ℝ := ⟨a - b, 1⟩
/-- One multiplication `a * b` (cost `1`). -/
def mulOp (a b : ℝ) : Counted ℝ := ⟨a * b, 1⟩
/-- One division `a / b` (cost `1`). -/
def divOp (a b : ℝ) : Counted ℝ := ⟨a / b, 1⟩
/-- One absolute value `|a|` (cost `1`). -/
def absOp (a : ℝ) : Counted ℝ := ⟨|a|, 1⟩
/-- One maximum `max a b` (cost `1`). -/
def maxOp (a b : ℝ) : Counted ℝ := ⟨max a b, 1⟩

@[simp] lemma addOp_val (a b : ℝ) : (addOp a b).val = a + b := rfl
@[simp] lemma addOp_ops (a b : ℝ) : (addOp a b).ops = 1 := rfl
@[simp] lemma subOp_val (a b : ℝ) : (subOp a b).val = a - b := rfl
@[simp] lemma subOp_ops (a b : ℝ) : (subOp a b).ops = 1 := rfl
@[simp] lemma mulOp_val (a b : ℝ) : (mulOp a b).val = a * b := rfl
@[simp] lemma mulOp_ops (a b : ℝ) : (mulOp a b).ops = 1 := rfl
@[simp] lemma divOp_val (a b : ℝ) : (divOp a b).val = a / b := rfl
@[simp] lemma divOp_ops (a b : ℝ) : (divOp a b).ops = 1 := rfl
@[simp] lemma absOp_val (a : ℝ) : (absOp a).val = |a| := rfl
@[simp] lemma absOp_ops (a : ℝ) : (absOp a).ops = 1 := rfl
@[simp] lemma maxOp_val (a b : ℝ) : (maxOp a b).val = max a b := rfl
@[simp] lemma maxOp_ops (a b : ℝ) : (maxOp a b).ops = 1 := rfl

/-! ### The passes of the algorithm -/

/-- Steps `i + 1, …, i + m` of the recurrence (2.3), carrying the previous pivot `u = u_i`:
`l_{i+1} = c_{i+1} / u_i`, `u_{i+1} = d_{i+1} - l_{i+1} e_i` (three operations per step).
Returns `([l_{i+1}, …, l_{i+m}], [u_{i+1}, …, u_{i+m}])`. -/
def luFrom (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → ℝ → ℕ → Counted (List ℝ × List ℝ)
  | _, _, 0 => pure ([], [])
  | i, u, m + 1 => do
      let l ← divOp (ent A (i + 1) i) u              -- l_{i+1} = c_{i+1} / u_i
      let t ← mulOp l (ent A i (i + 1))              -- l_{i+1} e_i
      let u' ← subOp (ent A (i + 1) (i + 1)) t       -- u_{i+1} = d_{i+1} - l_{i+1} e_i
      let r ← luFrom A (i + 1) u' m
      pure (l :: r.1, u' :: r.2)

/-- **Pass (a).** The LU factorization of the tridiagonal matrix `A` by the recurrence (2.3):
returns the multipliers `[l_1, …, l_{n-1}]` and the pivots `[u_0, …, u_{n-1}]`, where
`u_0 = d_0` costs nothing. -/
def luPass (A : Matrix (Fin n) (Fin n) ℝ) : Counted (List ℝ × List ℝ) :=
  if n = 0 then pure ([], []) else do
    let r ← luFrom A 0 (ent A 0 0) (n - 1)
    pure (r.1, ent A 0 0 :: r.2)

/-- The entrywise absolute values of a list (one operation per entry). -/
def absPass : List ℝ → Counted (List ℝ)
  | [] => pure []
  | a :: as => do
      let b ← absOp a
      let bs ← absPass as
      pure (b :: bs)

/-- `addTermOp s m o` adds the term `|m| a` to `s` if the neighbour `o = some a` exists (three
operations), and returns `s` unchanged (no operation) if `o = none`. -/
def addTermOp (s m : ℝ) : Option ℝ → Counted ℝ
  | none => pure s
  | some a => do
      let am ← absOp m
      let t ← mulOp am a
      addOp s t

/-- **Pass (b).** The rows `i, i+1, …, n-1` of `y = |A||x|`, computed from the three tridiagonal
entries of each row: `rowPass A i p as`, where `as = [|x_i|, …, |x_{n-1}|]` and `p` is
`|x_{i-1}|` (`none` for the first row), returns `[y_i, …, y_{n-1}]` with
`y_i = |d_i||x_i| + |c_i||x_{i-1}| + |e_i||x_{i+1}|`.  The term with `x_{i-1}` is absent for the
first row (`p = none`; the value `ent A 0 (0 - 1)` passed in that case is not used) and the term
with `x_{i+1}` is absent for the last row (the list of remaining `|x_j|` is empty). -/
def rowPass (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Option ℝ → List ℝ → Counted (List ℝ)
  | _, _, [] => pure []
  | i, p, a :: as => do
      let ad ← absOp (ent A i i)
      let s ← mulOp ad a                                -- |d_i| |x_i|
      let s ← addTermOp s (ent A i (i - 1)) p           -- + |c_i| |x_{i-1}|   (if i > 0)
      let s ← addTermOp s (ent A i (i + 1)) as.head?    -- + |e_i| |x_{i+1}|   (if i < n - 1)
      let ys ← rowPass A (i + 1) (some a) as
      pure (s :: ys)

/-- Rows `i, i+1, …` of the forward substitution for `M(L) v = y`, carrying `v = v_{i-1}`: from
the lists `[l_i, …]` and `[y_i, …]` it computes `v_i = y_i + |l_i| v_{i-1}`, … (three
operations per row). -/
def fwdFrom : List ℝ → List ℝ → ℝ → Counted (List ℝ)
  | l :: ls, y :: ys, v => do
      let al ← absOp l
      let t ← mulOp al v
      let v' ← addOp y t                                -- v_i = y_i + |l_i| v_{i-1}
      let vs ← fwdFrom ls ys v'
      pure (v' :: vs)
  | _, _, _ => pure []

/-- **Pass (c).** Forward substitution for `M(L) v = y`, from the multipliers
`[l_1, …, l_{n-1}]` and `[y_0, …, y_{n-1}]`: `v_0 = y_0`, `v_i = y_i + |l_i| v_{i-1}`. -/
def fwdPass (ls ys : List ℝ) : Counted (List ℝ) :=
  match ys with
  | [] => pure []
  | y :: ys => do
      let vs ← fwdFrom ls ys y
      pure (y :: vs)

/-- **Pass (d).** Back substitution for `M(U) w = v` on the rows `i, …, n-1`, from the pivots
`[u_i, …, u_{n-1}]` and `[v_i, …, v_{n-1}]` (the superdiagonal `e_i = a_{i,i+1}` is read from
`A`).  The recursion returns the computed suffix `[w_i, …, w_{n-1}]`, whose head is used in the
next step: `w_{n-1} = v_{n-1} / |u_{n-1}|` (two operations) and
`w_i = (v_i + |e_i| w_{i+1}) / |u_i|` (five operations). -/
def bwdPass (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → List ℝ → List ℝ → Counted (List ℝ)
  | i, u :: us, v :: vs => do
      let ws ← bwdPass A (i + 1) us vs
      match ws with
      | [] => do                                        -- last row
          let au ← absOp u
          let w ← divOp v au                            -- w_{n-1} = v_{n-1} / |u_{n-1}|
          pure [w]
      | w' :: _ => do                                   -- w' = w_{i+1}
          let ae ← absOp (ent A i (i + 1))
          let t ← mulOp ae w'
          let s ← addOp v t
          let au ← absOp u
          let w ← divOp s au                            -- w_i = (v_i + |e_i| w_{i+1}) / |u_i|
          pure (w :: ws)
  | _, _, _ => pure []

/-- Running maximum of a list, carrying the current maximum `m` (one operation per entry). -/
def maxFrom : List ℝ → ℝ → Counted ℝ
  | [], m => pure m
  | a :: as, m => do
      let m' ← maxOp m a
      maxFrom as m'

/-- The maximum of a list (`0` for the empty list), as a running maximum started at the first
entry: `length - 1` operations.  Used in **pass (e)** for `‖w‖_∞` and `‖x‖_∞`. -/
def maxPass : List ℝ → Counted ℝ
  | [] => pure 0
  | a :: as => maxFrom as a

/-- The whole algorithm (3.8) in the cost model: (a) the LU factorization (2.3), (b) `|x|` and
`y = |A||x|`, (c) `M(L) v = y`, (d) `M(U) w = v`, (e) `‖w‖_∞ / ‖x‖_∞`. -/
def condAlgM (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Counted ℝ := do
  let lu ← luPass A                 -- (a) lu.1 = [l_1, …, l_{n-1}], lu.2 = [u_0, …, u_{n-1}]
  let ax ← absPass (List.ofFn x)    -- (b) [|x_0|, …, |x_{n-1}|]
  let ys ← rowPass A 0 none ax      -- (b) y = |A||x|
  let vs ← fwdPass lu.1 ys          -- (c) M(L) v = y
  let ws ← bwdPass A 0 lu.2 vs      -- (d) M(U) w = v
  let aw ← absPass ws               -- (e) [|w_0|, …, |w_{n-1}|]
  let nw ← maxPass aw               -- (e) ‖w‖_∞
  let nx ← maxPass ax               -- (e) ‖x‖_∞
  divOp nw nx                       -- (e) ‖w‖_∞ / ‖x‖_∞

/-! ### Values and operation counts of the passes -/

lemma luFrom_val (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ∀ (i : ℕ) (u : ℝ), u = piv A i →
    (luFrom A i u m).val =
      ((List.range' (i + 1) m).map (mult A), (List.range' (i + 1) m).map (piv A)) := by
  induction m with
  | zero => intro i u _; rfl
  | succ m ih =>
    intro i u hu
    subst hu
    have h := ih (i + 1) _ (piv_succ A i).symm
    simp only [luFrom, val_bind, val_pure, divOp_val, mulOp_val, subOp_val, ← mult_succ] at h ⊢
    rw [h]
    simp [List.range'_succ, piv_succ]

lemma luFrom_ops (A : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ∀ (i : ℕ) (u : ℝ),
    (luFrom A i u m).ops = 3 * m := by
  induction m with
  | zero => intro i u; rfl
  | succ m ih =>
    intro i u
    simp only [luFrom, ops_bind, ops_pure, divOp_ops, mulOp_ops, subOp_ops, ih]
    ring

/-- Pass (a) computes the multipliers `l_i = mult A i` (`1 ≤ i ≤ n - 1`) and the pivots
`u_i = piv A i` (`0 ≤ i ≤ n - 1`) of the recurrence (2.3). -/
theorem luPass_val (A : Matrix (Fin n) (Fin n) ℝ) :
    (luPass A).val = ((List.range' 1 (n - 1)).map (mult A), (List.range' 0 n).map (piv A)) := by
  unfold luPass
  split_ifs with hn
  · subst hn; rfl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    simp only [val_bind, val_pure, Nat.add_sub_cancel, luFrom_val A k 0 (ent A 0 0) rfl]
    simp [List.range'_succ]

lemma luPass_length_fst (A : Matrix (Fin n) (Fin n) ℝ) : (luPass A).val.1.length = n - 1 := by
  rw [luPass_val]; simp

lemma luPass_length_snd (A : Matrix (Fin n) (Fin n) ℝ) : (luPass A).val.2.length = n := by
  rw [luPass_val]; simp

/-- The `i`-th pivot computed by pass (a) is `u_i = piv A i`. -/
theorem luPass_piv (A : Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : i < n) :
    (luPass A).val.2[i]'(by rw [luPass_length_snd]; exact hi) = piv A i := by
  simp [luPass_val]

/-- The `i`-th multiplier computed by pass (a) is `l_{i+1} = mult A (i + 1)`. -/
theorem luPass_mult (A : Matrix (Fin n) (Fin n) ℝ) {i : ℕ} (hi : i + 1 < n) :
    (luPass A).val.1[i]'(by rw [luPass_length_fst]; omega) = mult A (i + 1) := by
  simp [luPass_val, add_comm]

/-- Pass (a) costs `3 (n - 1)` operations. -/
theorem luPass_ops (A : Matrix (Fin n) (Fin n) ℝ) : (luPass A).ops = 3 * (n - 1) := by
  unfold luPass
  split_ifs with hn
  · subst hn; rfl
  · simp [luFrom_ops]

lemma absPass_val (as : List ℝ) : (absPass as).val = as.map (fun a => |a|) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [absPass, ih]

lemma absPass_length (as : List ℝ) : (absPass as).val.length = as.length := by
  simp [absPass_val]

lemma absPass_ops (as : List ℝ) : (absPass as).ops = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [absPass, ih]; ring

@[simp] lemma addTermOp_val (s m : ℝ) (o : Option ℝ) :
    (addTermOp s m o).val = s + |m| * o.getD 0 := by
  cases o <;> simp [addTermOp]

@[simp] lemma addTermOp_none_ops (s m : ℝ) : (addTermOp s m none).ops = 0 := rfl

@[simp] lemma addTermOp_some_ops (s m a : ℝ) : (addTermOp s m (some a)).ops = 3 := rfl

lemma vext_abs (x : Fin n → ℝ) (k : ℕ) : vext (fun j => |x j|) k = |vext x k| := by
  unfold vext; split_ifs <;> simp

lemma isTridiagonal_map_abs {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) :
    IsTridiagonal (A.map abs) := by
  intro i j h; simp [hT i j h]

/-- Row `i` of `|A||x|` for tridiagonal `A`, written with the three tridiagonal entries. -/
lemma vext_absMulVec {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) (x : Fin n → ℝ)
    {i : ℕ} (hi : i < n) :
    vext (A.map abs *ᵥ fun k => |x k|) i =
      |ent A i i| * |vext x i| + |ent A i (i - 1)| * (if i = 0 then 0 else |vext x (i - 1)|) +
        |ent A i (i + 1)| * |vext x (i + 1)| := by
  have hT' := isTridiagonal_map_abs hT
  rw [show vext (A.map abs *ᵥ fun k => |x k|) i = (A.map abs *ᵥ fun k => |x k|) ⟨i, hi⟩ by
    simp [vext, hi]]
  cases i with
  | zero =>
    rw [mulVec_tridiag_zero hT' _ hi]
    simp only [ent_abs, vext_abs]
    simp
  | succ k =>
    rw [mulVec_tridiag_succ hT' _ hi]
    simp only [ent_abs, vext_abs, Nat.add_sub_cancel]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    ring

lemma head?_map_range'_getD (f : ℕ → ℝ) (i m : ℕ) :
    (((List.range' (i + 1) m).map f).head?).getD 0 = if m = 0 then 0 else f (i + 1) := by
  cases m <;> simp [List.range'_succ]

/-- Pass (b) computes `y = |A||x|` for tridiagonal `A` (tridiagonality is needed, since only
the three tridiagonal entries of each row are used). -/
theorem rowPass_val {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A) (x : Fin n → ℝ)
    (m : ℕ) : ∀ (i : ℕ) (p : Option ℝ), i + m = n →
    p.getD 0 = (if i = 0 then 0 else |vext x (i - 1)|) →
    (rowPass A i p ((List.range' i m).map (fun j => |vext x j|))).val =
      (List.range' i m).map (vext (A.map abs *ᵥ fun k => |x k|)) := by
  induction m with
  | zero => intro i p _ _; rfl
  | succ m ih =>
    intro i p him hp
    have h := ih (i + 1) (some |vext x i|) (by omega) (by simp)
    rw [List.range'_succ, List.map_cons, List.map_cons, rowPass.eq_2]
    simp only [val_bind, val_pure, absOp_val, mulOp_val, addTermOp_val, h, hp,
      head?_map_range'_getD]
    congr 1
    rw [vext_absMulVec hT x (by omega)]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : vext x (i + 1) = 0 := by simp [vext, show ¬ (i + 1 < n) by omega]
      simp [this]
    · simp [show m ≠ 0 by omega]

lemma rowPass_length (A : Matrix (Fin n) (Fin n) ℝ) (as : List ℝ) : ∀ (i : ℕ) (p : Option ℝ),
    (rowPass A i p as).val.length = as.length := by
  induction as with
  | nil => intro i p; rfl
  | cons a as ih => intro i p; simp [rowPass, ih]

/-- Pass (b) costs `2` operations per row plus `3` per existing neighbour.  On a list of `m ≥ 1`
entries this is `8 m - 6` operations if the first processed row has no left neighbour
(`p = none`, as for row `0`) and `8 m - 3` operations if it has one (`p = some _`); the last
processed row has no right neighbour. -/
theorem rowPass_ops (A : Matrix (Fin n) (Fin n) ℝ) (as : List ℝ) : ∀ (i : ℕ) (p : Option ℝ),
    (rowPass A i p as).ops = 8 * as.length - (if p.isSome then 3 else 6) := by
  induction as with
  | nil => intro i p; simp [rowPass]
  | cons a as ih =>
    intro i p
    have h := ih (i + 1) (some a)
    simp only [Option.isSome_some, ite_true] at h
    rw [rowPass.eq_2]
    cases as with
    | nil => cases p <;> simp [h]
    | cons b bs =>
      cases p <;> simp only [ops_bind, ops_pure, absOp_ops, mulOp_ops, addTermOp_none_ops,
        addTermOp_some_ops, List.head?_cons, h, List.length_cons, Option.isSome_none,
        Option.isSome_some] <;> simp <;> omega

lemma fwdFrom_val (l : ℕ → ℝ) (y : Fin n → ℝ) (m : ℕ) : ∀ i : ℕ,
    (fwdFrom ((List.range' (i + 1) m).map l) ((List.range' (i + 1) m).map (vext y))
      (solveCompL l y i)).val = (List.range' (i + 1) m).map (solveCompL l y) := by
  induction m with
  | zero => intro i; simp [fwdFrom]
  | succ m ih =>
    intro i
    have h := ih (i + 1)
    simp only [List.range'_succ, List.map_cons, fwdFrom, val_bind, val_pure, absOp_val, mulOp_val,
      addOp_val] at h ⊢
    have hs : vext y (i + 1) + |l (i + 1)| * solveCompL l y i = solveCompL l y (i + 1) := rfl
    rw [hs, h]

/-- Pass (c) computes the solution `v = solveCompL l y` of `M(L) v = y`. -/
theorem fwdPass_val (l : ℕ → ℝ) (y : Fin n → ℝ) :
    (fwdPass ((List.range' 1 (n - 1)).map l) ((List.range' 0 n).map (vext y))).val =
      (List.range' 0 n).map (solveCompL l y) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rfl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
    have h := fwdFrom_val l y k 0
    simp only [zero_add, Nat.add_sub_cancel] at h ⊢
    simp only [List.range'_succ, List.map_cons, fwdPass, val_bind, val_pure]
    simp only [zero_add] at *
    rw [show vext y 0 = solveCompL l y 0 from rfl, h]

lemma fwdFrom_ops (ls : List ℝ) : ∀ (ys : List ℝ) (v : ℝ),
    (fwdFrom ls ys v).ops = 3 * min ls.length ys.length := by
  induction ls with
  | nil => intro ys v; simp [fwdFrom]
  | cons l ls ih =>
    intro ys v
    cases ys with
    | nil => simp [fwdFrom]
    | cons y ys => simp [fwdFrom, ih]; omega

lemma fwdFrom_length (ls : List ℝ) : ∀ (ys : List ℝ) (v : ℝ),
    (fwdFrom ls ys v).val.length = min ls.length ys.length := by
  induction ls with
  | nil => intro ys v; simp [fwdFrom]
  | cons l ls ih =>
    intro ys v
    cases ys with
    | nil => simp [fwdFrom]
    | cons y ys => simp [fwdFrom, ih]

/-- Pass (c) costs `3` operations per row after the first: `3 (n - 1)` for lists of lengths
`n - 1` and `n`. -/
theorem fwdPass_ops (ls ys : List ℝ) :
    (fwdPass ls ys).ops = 3 * min ls.length (ys.length - 1) := by
  cases ys with
  | nil => simp [fwdPass]
  | cons y ys => simp [fwdPass, fwdFrom_ops]

lemma fwdPass_length (ls ys : List ℝ) :
    (fwdPass ls ys).val.length = min (ls.length + 1) ys.length := by
  cases ys with
  | nil => simp [fwdPass]
  | cons y ys => simp [fwdPass, fwdFrom_length]

/-- Pass (d) computes the solution `w = solveCompU (piv A) (supd A) v` of `M(U) w = v`. -/
theorem bwdPass_val (A : Matrix (Fin n) (Fin n) ℝ) (v : ℕ → ℝ) (m : ℕ) : ∀ i : ℕ, i + m = n →
    (bwdPass A i ((List.range' i m).map (piv A)) ((List.range' i m).map v)).val =
      (List.range' i m).map (solveCompU (n := n) (piv A) (supd A) v) := by
  induction m with
  | zero => intro i _; simp [bwdPass]
  | succ m ih =>
    intro i him
    have h := ih (i + 1) (by omega)
    rw [List.range'_succ, List.map_cons, List.map_cons, List.map_cons, bwdPass.eq_1]
    simp only [val_bind]
    rw [h]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [List.range'_zero, List.map_nil, val_bind, val_pure, absOp_val, divOp_val]
      rw [solveCompU.eq_1 (n := n) _ _ _ i, dite_eq_right (show ¬ (i + 1 < n) by omega)]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
      simp only [List.range'_succ, List.map_cons, val_bind, val_pure, absOp_val, mulOp_val,
        addOp_val, divOp_val]
      rw [solveCompU.eq_1 (n := n) _ _ _ i, dite_eq_left (show i + 1 < n by omega)]
      rfl

lemma bwdPass_length (A : Matrix (Fin n) (Fin n) ℝ) (us : List ℝ) : ∀ (vs : List ℝ) (i : ℕ),
    (bwdPass A i us vs).val.length = min us.length vs.length := by
  induction us with
  | nil => intro vs i; simp [bwdPass]
  | cons u us ih =>
    intro vs i
    cases vs with
    | nil => simp [bwdPass]
    | cons v vs =>
      have h := ih vs (i + 1)
      rw [bwdPass.eq_1]
      simp only [val_bind]
      rcases hw : (bwdPass A (i + 1) us vs).val with _ | ⟨w', ws'⟩
      · rw [hw] at h
        simp only [val_bind, val_pure, List.length_cons, List.length_nil] at h ⊢
        omega
      · rw [hw] at h
        simp only [val_bind, val_pure, List.length_cons] at h ⊢
        omega

/-- Pass (d) costs `2` operations for the last row and `5` for each other row: `5 n - 3`
operations for `n ≥ 1` rows. -/
theorem bwdPass_ops (A : Matrix (Fin n) (Fin n) ℝ) (us : List ℝ) : ∀ (vs : List ℝ) (i : ℕ),
    (bwdPass A i us vs).ops = 5 * min us.length vs.length - 3 := by
  induction us with
  | nil => intro vs i; simp [bwdPass]
  | cons u us ih =>
    intro vs i
    cases vs with
    | nil => simp [bwdPass]
    | cons v vs =>
      have h := ih vs (i + 1)
      have hl := bwdPass_length A us vs (i + 1)
      rw [bwdPass.eq_1]
      simp only [ops_bind]
      rcases hw : (bwdPass A (i + 1) us vs).val with _ | ⟨w', ws'⟩
      · rw [hw] at hl
        simp only [ops_bind, ops_pure, absOp_ops, divOp_ops, List.length_cons, List.length_nil,
          h] at hl ⊢
        omega
      · rw [hw] at hl
        simp only [ops_bind, ops_pure, absOp_ops, mulOp_ops, addOp_ops, divOp_ops,
          List.length_cons, h] at hl ⊢
        omega

lemma maxFrom_val (as : List ℝ) : ∀ m : ℝ, (maxFrom as m).val = as.foldl max m := by
  induction as with
  | nil => intro m; rfl
  | cons a as ih => intro m; simp [maxFrom, ih]

lemma maxFrom_ops (as : List ℝ) : ∀ m : ℝ, (maxFrom as m).ops = as.length := by
  induction as with
  | nil => intro m; rfl
  | cons a as ih => intro m; simp [maxFrom, ih]; ring

/-- The maximum of a list of length `m` costs `m - 1` operations. -/
theorem maxPass_ops (as : List ℝ) : (maxPass as).ops = as.length - 1 := by
  cases as with
  | nil => rfl
  | cons a as => simp [maxPass, maxFrom_ops]

lemma foldl_max_le_iff (as : List ℝ) : ∀ m c : ℝ,
    as.foldl max m ≤ c ↔ m ≤ c ∧ ∀ a ∈ as, a ≤ c := by
  induction as with
  | nil => intro m c; simp
  | cons a as ih => intro m c; simp [ih, and_assoc]

lemma maxPass_val_of_nonneg (as : List ℝ) (h : ∀ a ∈ as, 0 ≤ a) :
    (maxPass as).val = as.foldl max 0 := by
  cases as with
  | nil => rfl
  | cons a as => simp [maxPass, maxFrom_val, max_eq_right (h a (by simp))]

/-- Pass (e): the running maximum of `|g 0|, …, |g (n-1)|` is the sup norm of the vector
`(g 0, …, g (n-1))`. -/
theorem maxPass_abs_eq_norm (g : ℕ → ℝ) :
    (maxPass ((List.range' 0 n).map (fun j => |g j|))).val = ‖fun i : Fin n => g i‖ := by
  rw [maxPass_val_of_nonneg _ (by simp)]
  set L := (List.range' 0 n).map (fun j => |g j|)
  have hmem : ∀ i : Fin n, |g i| ∈ L := fun i =>
    List.mem_map.mpr ⟨i, List.mem_range'_1.mpr ⟨by omega, by simp⟩, rfl⟩
  have h0 : 0 ≤ L.foldl max 0 := ((foldl_max_le_iff L 0 _).mp le_rfl).1
  apply le_antisymm
  · refine (foldl_max_le_iff L 0 _).mpr ⟨norm_nonneg _, fun a ha => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hjn : j < n := by have := List.mem_range'_1.mp hj; omega
    have := norm_le_pi_norm (fun i : Fin n => g i) ⟨j, hjn⟩
    rwa [Real.norm_eq_abs] at this
  · refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact ((foldl_max_le_iff L 0 _).mp le_rfl).2 _ (hmem i)

lemma ofFn_eq_map_vext (x : Fin n → ℝ) : List.ofFn x = (List.range' 0 n).map (vext x) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < n := by simpa using h1
    simp [vext, hj]

end OpCount

open OpCount OpCount.Counted

/-! ### The counted algorithm: value and exact operation count -/

/-- **The algorithm (3.8) with operation count.**  `condAlgCounted A x` runs the whole
computation, starting from the matrix `A` and the vector `x`: (a) the LU factorization by the
recurrence (2.3), (b) `y = |A||x|` from the three tridiagonal entries of each row, (c) the forward
pass for `M(L) v = y`, (d) the backward pass for `M(U) w = v`, (e) `‖w‖_∞ / ‖x‖_∞`.  It returns
the computed value and the number of arithmetic operations (`+`, `-`, `*`, `/`, `|·|`, `max`,
each of cost `1`) that were performed; see the module docstring for the cost model. -/
def condAlgCounted (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ × ℕ :=
  ((condAlgM A x).val, (condAlgM A x).ops)

/-- For tridiagonal `A`, the value computed by `condAlgCounted` is that of the recurrences
`condAlg` of `Algorithm38.lean`.  (Tridiagonality is needed because `y = |A||x|` is formed from
the three tridiagonal entries of each row only; no other hypothesis is needed.) -/
theorem condAlgCounted_fst_eq_condAlg {A : Matrix (Fin n) (Fin n) ℝ} (hT : IsTridiagonal A)
    (x : Fin n → ℝ) : (condAlgCounted A x).1 = condAlg A x := by
  have h1 := luPass_val A
  have h2 : (absPass (List.ofFn x)).val = (List.range' 0 n).map (fun j => |vext x j|) := by
    rw [absPass_val, ofFn_eq_map_vext, List.map_map]; rfl
  have h3 : (rowPass A 0 none ((List.range' 0 n).map (fun j => |vext x j|))).val =
      (List.range' 0 n).map (vext (A.map abs *ᵥ fun k => |x k|)) :=
    rowPass_val hT x n 0 none (by simp) (by simp)
  have h4 := fwdPass_val (mult A) (A.map abs *ᵥ fun k => |x k|)
  have h5 := bwdPass_val A (solveCompL (mult A) (A.map abs *ᵥ fun k => |x k|)) n 0 (by simp)
  have h6 : (absPass ((List.range' 0 n).map (solveCompU (n := n) (piv A) (supd A)
      (solveCompL (mult A) (A.map abs *ᵥ fun k => |x k|))))).val =
      (List.range' 0 n).map (fun j => |solveCompU (n := n) (piv A) (supd A)
        (solveCompL (mult A) (A.map abs *ᵥ fun k => |x k|)) j|) := by
    rw [absPass_val, List.map_map]; rfl
  have h7 : (maxPass ((List.range' 0 n).map (fun j => |solveCompU (n := n) (piv A) (supd A)
      (solveCompL (mult A) (A.map abs *ᵥ fun k => |x k|)) j|))).val =
      ‖fun i : Fin n => solveCompU (n := n) (piv A) (supd A)
        (solveCompL (mult A) (A.map abs *ᵥ fun k => |x k|)) i‖ := maxPass_abs_eq_norm _
  have h8 : (maxPass ((List.range' 0 n).map (fun j => |vext x j|))).val = ‖x‖ := by
    rw [maxPass_abs_eq_norm]; congr 1; funext i; simp [vext]
  simp only [condAlgCounted, condAlgM, val_bind, h1, h2, h3, h4, h5, h6, h7, h8, divOp_val]
  rfl

/-- **(3.8): the counted algorithm computes `cond(A, x)`**, under exactly the paper's hypothesis
`|A⁻¹| = |U⁻¹||L⁻¹|`, for every `x` (for `x = 0` both sides are `0`). -/
theorem condAlgCounted_val (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs)
    (x : Fin n → ℝ) : (condAlgCounted A x).1 = condSkeel A x := by
  rw [condAlgCounted_fst_eq_condAlg hT, condAlg_eq_condSkeel' A L U hA hT hLU hinv]

/-- The counted algorithm computes `cond(A, x)` under the hypothesis `|L||U| = |A|` of
Theorem 3.3. -/
theorem condAlgCounted_val_of_abs (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (habs : L.map abs * U.map abs = A.map abs)
    (x : Fin n → ℝ) : (condAlgCounted A x).1 = condSkeel A x :=
  condAlgCounted_val A L U hA hT hLU (theorem_3_3 A L U hA hT hLU habs).symm x

/-- **The exact operation count of (3.8).**  For every `A` and `x`, `condAlgCounted A x`
performs exactly `23 n - 16` arithmetic operations if `n ≥ 1` (and `1`, the final division, if
`n = 0`):
`3(n-1)` for (a), `n + (8n-6)` for (b), `3(n-1)` for (c), `5n-3` for (d) and
`(2n-1) + (n-1) + 1` for (e). -/
theorem condAlgCounted_ops (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (condAlgCounted A x).2 = if n = 0 then 1 else 23 * n - 16 := by
  simp only [condAlgCounted, condAlgM, ops_bind, val_bind, luPass_ops, absPass_ops, rowPass_ops,
    fwdPass_ops, bwdPass_ops, maxPass_ops, divOp_ops, absPass_length, rowPass_length,
    fwdPass_length, bwdPass_length, luPass_length_fst, luPass_length_snd, List.length_ofFn,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rfl
  · have e : n - 1 + 1 = n := by omega
    simp only [e, min_self, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
    omega

theorem condAlgCounted_ops_of_pos (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (hn : 0 < n) :
    (condAlgCounted A x).2 = 23 * n - 16 := by
  rw [condAlgCounted_ops, ite_eq_right (Nat.pos_iff_ne_zero.mp hn)]

/-- **`O(n)` operations**: `condAlgCounted A x` performs at most `23 n + 1` operations. -/
theorem condAlgCounted_ops_le (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (condAlgCounted A x).2 ≤ 23 * n + 1 := by
  rw [condAlgCounted_ops]; split_ifs <;> omega

/-- `O(n)` with the quantifiers spelled out: one constant `C` bounds the operation count by
`C (n + 1)` for all dimensions `n` and all inputs `A`, `x`. -/
theorem condAlgCounted_ops_linear : ∃ C : ℕ, ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ), (condAlgCounted A x).2 ≤ C * (m + 1) :=
  ⟨23, fun _ A x => (condAlgCounted_ops_le A x).trans (by omega)⟩

/-- **(3.8): "`cond(A, x)` can be computed in `O(n)` operations."**  If the nonsingular
tridiagonal matrix `A = LU` satisfies `|A⁻¹| = |U⁻¹||L⁻¹|`, then `condAlgCounted` returns
`cond(A, x)` after at most `23 n + 1` arithmetic operations (exactly `23 n - 16` for `n ≥ 1`). -/
theorem eq_3_8_counted (A L U : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hT : IsTridiagonal A) (hLU : IsLU A L U) (hinv : A⁻¹.map abs = U⁻¹.map abs * L⁻¹.map abs)
    (x : Fin n → ℝ) :
    (condAlgCounted A x).1 = condSkeel A x ∧ (condAlgCounted A x).2 ≤ 23 * n + 1 :=
  ⟨condAlgCounted_val A L U hA hT hLU hinv x, condAlgCounted_ops_le A x⟩

/-! ### Sanity checks

The counter is obtained by running the recursion: the kernel evaluates it on concrete inputs
(by `decide`, i.e. by kernel reduction), in agreement with `23 n - 16`. -/

example : (condAlgCounted (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1)).2 = 7 := by decide

example : (condAlgCounted (1 : Matrix (Fin 3) (Fin 3) ℝ) (fun _ => 1)).2 = 53 := by decide

end Higham
