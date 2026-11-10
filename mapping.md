# Mapping: paper results → Lean theorems

Paper: N. J. Higham, *Bounding the error in Gaussian elimination for tridiagonal systems*,
SIAM J. Matrix Anal. Appl. 11(4) (1990), 521–530.

Lean 4 (`v4.35.0`) + Mathlib (`v4.35.0`). Build with `lake exe cache get && lake build`.
Every declaration listed here is proved: there is no `sorry` and no `axiom` anywhere in the
project. `#print axioms` shows only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) for every theorem below.

All links are relative to the repository root, of the form `file#Lline`. They are clickable on
GitHub and in most Markdown viewers.

## 1. Numbered results (theorems)

| Paper | Statement (paraphrase) | Lean declaration(s) | Human Verified? |
|---|---|---|---|
| **Theorem 3.1** | `A` nonsingular, tridiagonal; if (a) SPD, (b) totally nonnegative, (c) M-matrix, or (d) `A = D₁BD₂` with `\|D₁\| = \|D₂\| = I` and `B` of type (a)–(c), then `A` has an LU factorization and `\|L\|\|U\| = \|LU\|`. | `theorem_3_1` — [HighamTridiagonal/Theorem31.lean:402](HighamTridiagonal/Theorem31.lean#L402) <br>"every LU factorization" form: `theorem_3_1'` — [HighamTridiagonal/Theorem31.lean:426](HighamTridiagonal/Theorem31.lean#L426)<br>individual cases: `theorem_3_1_a` — [HighamTridiagonal/Theorem31.lean:66](HighamTridiagonal/Theorem31.lean#L66)<br>`theorem_3_1_b` — [HighamTridiagonal/Theorem31.lean:82](HighamTridiagonal/Theorem31.lean#L82)<br>`theorem_3_1_c` — [HighamTridiagonal/Theorem31.lean:223](HighamTridiagonal/Theorem31.lean#L223)<br>`theorem_3_1_d` — [HighamTridiagonal/Theorem31.lean:323](HighamTridiagonal/Theorem31.lean#L323) | YES |
| **Theorem 3.1 (b)**, "or equivalently" | For nonsingular tridiagonal `A`: `A` totally nonnegative ⇔ `L ≥ 0` and `U ≥ 0`. | `theorem_3_1_b_equiv` — [HighamTridiagonal/Theorem31.lean:93](HighamTridiagonal/Theorem31.lean#L93)<br>"the LU factors" form: `theorem_3_1_b_equiv'` — [HighamTridiagonal/Theorem31.lean:438](HighamTridiagonal/Theorem31.lean#L438) | YES |
| **Theorem 3.1 (c)**, "or equivalently" | For nonsingular tridiagonal `A`: `A` is an M-matrix ⇔ `L`, `U` have positive diagonal and nonpositive off-diagonal elements. | `theorem_3_1_c_equiv` — [HighamTridiagonal/Theorem31.lean:237](HighamTridiagonal/Theorem31.lean#L237)<br>"the LU factors" form: `theorem_3_1_c_equiv'` — [HighamTridiagonal/Theorem31.lean:451](HighamTridiagonal/Theorem31.lean#L451) | YES |
| **Theorem 3.2** | If `A` is of type (a)–(d) and `u` is sufficiently small, GE for `Ax = b` succeeds and the computed `x̂` satisfies `(A+F)x̂ = b`, `\|F\| ≤ h(u)\|A\|`, `h(u) = (4u+3u²+u³)/(1−u)`, i.e. (3.4). | `theorem_3_2` — [HighamTridiagonal/Theorem32.lean:146](HighamTridiagonal/Theorem32.lean#L146) | YES |
| **Theorem 3.3** | `A` nonsingular tridiagonal, `A = LU`, `\|L\|\|U\| = \|A\|` ⇒ `\|U⁻¹\|\|L⁻¹\| = \|A⁻¹\|`. | `theorem_3_3` — [HighamTridiagonal/Theorem33.lean:99](HighamTridiagonal/Theorem33.lean#L99) | YES |
| **Theorem 4.1** | `A` nonsingular, tridiagonal, diagonally dominant by rows or columns, `A = LU` ⇒ `\|L\|\|U\| ≤ 3\|A\|`. | `theorem_4_1` — [HighamTridiagonal/DiagDominant.lean:242](HighamTridiagonal/DiagDominant.lean#L242) | YES |
| **Theorem 4.2** | `A` nonsingular, row diagonally dominant, tridiagonal, `A = LU`, `y ≥ 0` ⇒ `‖\|U⁻¹\|\|L⁻¹\|y‖∞ ≤ (2n−1)‖\|A⁻¹\|y‖∞`. | `theorem_4_2` — [HighamTridiagonal/DiagDominant.lean:347](HighamTridiagonal/DiagDominant.lean#L347) | YES |

## 2. Numbered displayed equations

| Paper | Content | Lean declaration(s) | Human Verified? |
|---|---|---|---|
| (1.1) | Wilkinson's normwise backward error bound for GEPP on a **general dense** matrix (quoted from [22]). | Not formalized: quoted background result, not proved or used in the paper. Its tridiagonal analogue (2.7) is formalized. See §5. | YES |
| (1.2) | Normwise forward error bound from (1.1) via "standard perturbation theory": `‖x−x̂‖∞/‖x‖∞ ≤ κ∞(A)ε/(1−κ∞(A)ε)`. | `eq_1_2` — [HighamTridiagonal/Remarks.lean:43](HighamTridiagonal/Remarks.lean#L43)<br>`kappaInf` — [HighamTridiagonal/Remarks.lean:34](HighamTridiagonal/Remarks.lean#L34) | YES |
| (1.3) | de Boor–Pinkus componentwise backward error `\|E\| ≤ c_n u\|L̂\|\|Û\|` for GE on a **general dense** matrix (quoted from [5]). | Not formalized: quoted background result (constant `c_n = 2n + O(u)` from [5]). The tridiagonal version is (2.7), formalized. See §5. | YES|
| (1.4) | If `\|L̂\|\|Û\| ≤ c'_n\|A\|` then (1.3) gives `\|E\| ≤ c''_n u\|A\|`. | `eq_1_4` — [HighamTridiagonal/Remarks.lean:111](HighamTridiagonal/Remarks.lean#L111) | YES |
| (1.5) | Componentwise forward error bound: `‖x−x̂‖∞/‖x‖∞ ≤ cond(A,x)ε/(1−cond(A)ε)` when `\|E\| ≤ ε\|A\|`, `cond(A)ε < 1`; definitions of `cond(A,x)`, `cond(A)`. | `eq_1_5` — [HighamTridiagonal/Condition.lean:77](HighamTridiagonal/Condition.lean#L77)<br>`condSkeel` — [HighamTridiagonal/Condition.lean:23](HighamTridiagonal/Condition.lean#L23)<br>`condSkeelA` — [HighamTridiagonal/Condition.lean:27](HighamTridiagonal/Condition.lean#L27) | YES |
| (2.1) | Tridiagonal matrix `A` (subdiagonal `c`, diagonal `d`, superdiagonal `e`). | Definitions `IsTridiagonal` — [HighamTridiagonal/Basic.lean:36](HighamTridiagonal/Basic.lean#L36)<br>`ent` — [HighamTridiagonal/Basic.lean:50](HighamTridiagonal/Basic.lean#L50)<br>`supd` — [HighamTridiagonal/Basic.lean:150](HighamTridiagonal/Basic.lean#L150) | YES |
| (2.2) | `A = LU` with bidiagonal `L`, `U`, and `U`'s superdiagonal equal to `e`. | Definitions `IsLU` — [HighamTridiagonal/Basic.lean:41](HighamTridiagonal/Basic.lean#L41)<br>`lowerBidiag` — [HighamTridiagonal/Basic.lean:164](HighamTridiagonal/Basic.lean#L164)<br>`upperBidiag` — [HighamTridiagonal/Basic.lean:169](HighamTridiagonal/Basic.lean#L169)<br>Every LU factorization of a nonsingular tridiagonal matrix has the form (2.2): `IsLU.eq_recurrence` — [HighamTridiagonal/Basic.lean:429](HighamTridiagonal/Basic.lean#L429) | YES |
| (2.3) | The recurrence `u₁ = d₁`, `lᵢ = cᵢ/uᵢ₋₁`, `uᵢ = dᵢ − lᵢeᵢ₋₁`. | Definitions `piv` — [HighamTridiagonal/Basic.lean:139](HighamTridiagonal/Basic.lean#L139)<br>`mult` — [HighamTridiagonal/Basic.lean:145](HighamTridiagonal/Basic.lean#L145)<br>It produces an LU factorization: `eq_lowerBidiag_mul_upperBidiag` — [HighamTridiagonal/Basic.lean:315](HighamTridiagonal/Basic.lean#L315)<br>`isLU_recurrence` — [HighamTridiagonal/Basic.lean:328](HighamTridiagonal/Basic.lean#L328) | YES |
| (2.4) | Floating point model `fl(x op y) = (x op y)(1+δ) = (x op y)/(1+ε)`, `\|δ\|,\|ε\| ≤ u`. | Definition `FPModel` — [HighamTridiagonal/FloatingPoint.lean:27](HighamTridiagonal/FloatingPoint.lean#L27)<br>It is consistent (exact arithmetic is an instance): `FPModel.exact` — [HighamTridiagonal/FloatingPoint.lean:49](HighamTridiagonal/FloatingPoint.lean#L49)<br>The algorithm in this arithmetic: `FPModel.piv` — [HighamTridiagonal/FloatingPoint.lean:94](HighamTridiagonal/FloatingPoint.lean#L94)<br>`FPModel.mult` — [HighamTridiagonal/FloatingPoint.lean:100](HighamTridiagonal/FloatingPoint.lean#L100)<br>`FPModel.fwd` — [HighamTridiagonal/FloatingPoint.lean:126](HighamTridiagonal/FloatingPoint.lean#L126)<br>`FPModel.back` — [HighamTridiagonal/FloatingPoint.lean:132](HighamTridiagonal/FloatingPoint.lean#L132)<br>`FPModel.solve` — [HighamTridiagonal/FloatingPoint.lean:140](HighamTridiagonal/FloatingPoint.lean#L140)<br>`FPModel.Succeeds` — [HighamTridiagonal/FloatingPoint.lean:110](HighamTridiagonal/FloatingPoint.lean#L110)<br>`FPModel.Lhat` — [HighamTridiagonal/FloatingPoint.lean:120](HighamTridiagonal/FloatingPoint.lean#L120)<br>`FPModel.Uhat` — [HighamTridiagonal/FloatingPoint.lean:123](HighamTridiagonal/FloatingPoint.lean#L123) | YES |
| (2.5) | `A = L̂Û + E`, `\|E\| ≤ u\|L̂\|\|Û\|`. | `FPModel.eq_2_5` — [HighamTridiagonal/FloatingPoint.lean:245](HighamTridiagonal/FloatingPoint.lean#L245)<br>(hypothesis: the computed factorization exists, i.e. `û₀,…,û_{n−2} ≠ 0`: `FPModel.FactorSucceeds` — [HighamTridiagonal/FloatingPoint.lean:114](HighamTridiagonal/FloatingPoint.lean#L114)) | YES |
| (2.6) | `(L̂+ΔL)(Û+ΔU)x̂ = b`, `\|ΔL\| ≤ u\|L̂\|`, `\|ΔU\| ≤ (2u+u²)\|Û\|`. | `FPModel.eq_2_6` — [HighamTridiagonal/FloatingPoint.lean:309](HighamTridiagonal/FloatingPoint.lean#L309) | YES |
| (2.7) | `(A+F)x̂ = b`, `\|F\| ≤ f(u)\|L̂\|\|Û\|`, `f(u) = 4u+3u²+u³`. | `FPModel.eq_2_7` — [HighamTridiagonal/FloatingPoint.lean:406](HighamTridiagonal/FloatingPoint.lean#L406) | YES |
| (3.1), (3.2) | The "ideal bound" (3.1) `\|F\| ≤ g(u)\|A\|` holds if (3.2) `\|L̂\|\|Û\| = \|L̂Û\|`. | `FPModel.eq_3_1_of_eq_3_2` — [HighamTridiagonal/FloatingPoint.lean:471](HighamTridiagonal/FloatingPoint.lean#L471) | YES |
| (3.3) | If (3.2) holds, `\|L̂\|\|Û\| ≤ \|A\|/(1−u)`. | `FPModel.eq_3_3` — [HighamTridiagonal/FloatingPoint.lean:445](HighamTridiagonal/FloatingPoint.lean#L445) | YES|
| (3.4) | The bound of Theorem 3.2. | `theorem_3_2` — [HighamTridiagonal/Theorem32.lean:146](HighamTridiagonal/Theorem32.lean#L146) | YES |
| (3.5) | `\|L\|\|U\| = \|LU\|` ⇔ `\|lᵢeᵢ₋₁+uᵢ\| = \|lᵢ\|\|eᵢ₋₁\|+\|uᵢ\|` ∀i ⇔ "sign(lᵢeᵢ₋₁/uᵢ) = 1". | Exact form (the condition is `lᵢeᵢ₋₁/uᵢ ≥ 0`): `eq_3_5` — [HighamTridiagonal/Algorithm38.lean:196](HighamTridiagonal/Algorithm38.lean#L196)<br>`abs_mul_abs_eq_abs_mul_iff` — [HighamTridiagonal/Basic.lean:495](HighamTridiagonal/Basic.lean#L495)<br>Literal form "sign = 1" is sufficient: `eq_3_5_sign_sufficient` — [HighamTridiagonal/Algorithm38.lean:230](HighamTridiagonal/Algorithm38.lean#L230)<br>but not necessary: `eq_3_5_sign_not_necessary` — [HighamTridiagonal/Algorithm38.lean:238](HighamTridiagonal/Algorithm38.lean#L238) (see note 8) | N/A |
| (3.6) | `(U⁻¹)ᵢⱼ = (1/uⱼ) ∏_{p=i}^{j−1}(−e_p/u_p)`, `j ≥ i`. | `ent_inv_upperBidiag_eq_prod` — [HighamTridiagonal/Inverse.lean:105](HighamTridiagonal/Inverse.lean#L105) | N/A |
| (3.7) | `(L⁻¹)ᵢⱼ = ∏_{p=j}^{i−1}(−l_{p+1})`, `i ≥ j`. | `ent_inv_lowerBidiag_eq_prod` — [HighamTridiagonal/Inverse.lean:160](HighamTridiagonal/Inverse.lean#L160) | |
| (3.8) | If `\|A⁻¹\| = \|U⁻¹\|\|L⁻¹\|`, `cond(A,x)` "can be computed in `O(n)` operations": `y = \|A\|\|x\|`, solve `M(L)v = y`, `M(U)w = v`, return `‖w‖∞/‖x‖∞`. | Correctness under exactly the paper's hypothesis `\|A⁻¹\| = \|U⁻¹\|\|L⁻¹\|`: `eq_3_8'` — [HighamTridiagonal/OpCount38.lean:88](HighamTridiagonal/OpCount38.lean#L88)<br>`condAlg_eq_condSkeel'` — [HighamTridiagonal/OpCount38.lean:108](HighamTridiagonal/OpCount38.lean#L108)<br>Under Theorem 3.3's hypothesis `\|L\|\|U\| = \|A\|`: `eq_3_8` — [HighamTridiagonal/Algorithm38.lean:162](HighamTridiagonal/Algorithm38.lean#L162)<br>`condAlg_eq_condSkeel` — [HighamTridiagonal/Algorithm38.lean:183](HighamTridiagonal/Algorithm38.lean#L183)<br>The bidiagonal solves as recurrences: `solveCompL` — [HighamTridiagonal/Algorithm38.lean:101](HighamTridiagonal/Algorithm38.lean#L101)<br>`solveCompU` — [HighamTridiagonal/Algorithm38.lean:107](HighamTridiagonal/Algorithm38.lean#L107)<br>`comparison_lowerBidiag_mulVec_solveCompL` — [HighamTridiagonal/Algorithm38.lean:114](HighamTridiagonal/Algorithm38.lean#L114)<br>`comparison_upperBidiag_mulVec_solveCompU` — [HighamTridiagonal/Algorithm38.lean:129](HighamTridiagonal/Algorithm38.lean#L129)<br>`condAlg` — [HighamTridiagonal/Algorithm38.lean:155](HighamTridiagonal/Algorithm38.lean#L155)<br>**`O(n)` operation count** (cost model: each `+ − × ÷ \|·\| max` costs 1; the whole computation from `A`, `x`, including the LU factorization, takes exactly `23n − 16` operations): `condAlgCounted` — [HighamTridiagonal/OpCount38.lean:652](HighamTridiagonal/OpCount38.lean#L652)<br>`condAlgCounted_fst_eq_condAlg` — [HighamTridiagonal/OpCount38.lean:658](HighamTridiagonal/OpCount38.lean#L658)<br>`condAlgCounted_val` — [HighamTridiagonal/OpCount38.lean:684](HighamTridiagonal/OpCount38.lean#L684)<br>`condAlgCounted_val_of_abs` — [HighamTridiagonal/OpCount38.lean:691](HighamTridiagonal/OpCount38.lean#L691)<br>`condAlgCounted_ops` — [HighamTridiagonal/OpCount38.lean:701](HighamTridiagonal/OpCount38.lean#L701)<br>`condAlgCounted_ops_le` — [HighamTridiagonal/OpCount38.lean:718](HighamTridiagonal/OpCount38.lean#L718)<br>`condAlgCounted_ops_linear` — [HighamTridiagonal/OpCount38.lean:724](HighamTridiagonal/OpCount38.lean#L724)<br>`eq_3_8_counted` — [HighamTridiagonal/OpCount38.lean:731](HighamTridiagonal/OpCount38.lean#L731) | |
| (6.1) | For the test problem, (1.5) with (3.4) reads `‖x−x̂‖∞/‖x‖∞ ≤ 10.9 cond(A,x)u`. | General form (Theorem 3.2 + (1.5)): `forward_error_bound` — [HighamTridiagonal/Remarks.lean:126](HighamTridiagonal/Remarks.lean#L126)<br>Value of the constant: `constant_6_1` — [HighamTridiagonal/Remarks.lean:147](HighamTridiagonal/Remarks.lean#L147) (see note 9) | YES |

## 3. Unnumbered claims that are also formalized

| Paper (location) | Claim | Lean declaration(s) | Human Verified? |
|---|---|---|---|
| §3, p. 525 | Harrod's M-matrix `A = [2 −2 0; ε−2 2 0; 0 −1 3] = LU`: the multiplier `l₃₂ = −1/ε` is unbounded as `ε → 0`, yet GE "performs very stably, as Theorem 3.2 shows" | `harrod_example` — [HighamTridiagonal/Harrod.lean:292](HighamTridiagonal/Harrod.lean#L292)<br>`harrodA` — [HighamTridiagonal/Harrod.lean:79](HighamTridiagonal/Harrod.lean#L79)<br>`harrodL` — [HighamTridiagonal/Harrod.lean:83](HighamTridiagonal/Harrod.lean#L83)<br>`harrodU` — [HighamTridiagonal/Harrod.lean:86](HighamTridiagonal/Harrod.lean#L86)<br>`harrod_multiplier_unbounded` — [HighamTridiagonal/Harrod.lean:214](HighamTridiagonal/Harrod.lean#L214)<br>`harrod_stable` — [HighamTridiagonal/Harrod.lean:277](HighamTridiagonal/Harrod.lean#L277)<br>`harrodA_isMMatrix_iff` — [HighamTridiagonal/Harrod.lean:172](HighamTridiagonal/Harrod.lean#L172)<br>`harrod_LU_unique` — [HighamTridiagonal/Harrod.lean:151](HighamTridiagonal/Harrod.lean#L151)<br>`harrod_abs_LU` — [HighamTridiagonal/Harrod.lean:250](HighamTridiagonal/Harrod.lean#L250)<br>`harrodA_type_iff` — [HighamTridiagonal/Harrod.lean:256](HighamTridiagonal/Harrod.lean#L256)<br>Extra remark (not in the paper): the threshold `u₀` of Thm 3.2 cannot be uniform in `ε`: `harrod_no_uniform_threshold` — [HighamTridiagonal/Harrod.lean:370](HighamTridiagonal/Harrod.lean#L370) | |
| §3, after Thm 3.3 | `\|U⁻¹\| = M(U)⁻¹`, `\|L⁻¹\| = M(L)⁻¹` (comparison matrices) | `comparison` — [HighamTridiagonal/Algorithm38.lean:28](HighamTridiagonal/Algorithm38.lean#L28)<br>`abs_inv_factors_eq_inv_comparison` — [HighamTridiagonal/Algorithm38.lean:82](HighamTridiagonal/Algorithm38.lean#L82)<br>`abs_inv_upperBidiag` — [HighamTridiagonal/Algorithm38.lean:52](HighamTridiagonal/Algorithm38.lean#L52)<br>`abs_inv_lowerBidiag` — [HighamTridiagonal/Algorithm38.lean:68](HighamTridiagonal/Algorithm38.lean#L68) | |
| §3, before (3.8) | If `\|A⁻¹\| = \|U⁻¹\|\|L⁻¹\|` then `\|A⁻¹\|y = M(U)⁻¹M(L)⁻¹y` | `abs_inv_mulVec_eq_comparison` — [HighamTridiagonal/Algorithm38.lean:90](HighamTridiagonal/Algorithm38.lean#L90) | |
| §3 after (3.8); §6 | (3.8) with `y = e` computes `‖A⁻¹‖∞` (hence `κ∞(A)`) in `O(n)` operations, e.g. for SPD `A` | `‖M‖∞ = ‖\|M\|e‖∞`: `linfty_opNorm_eq_norm_abs_mulVec_one` — [HighamTridiagonal/CondRemarks.lean:117](HighamTridiagonal/CondRemarks.lean#L117)<br>`norm_inv_eq_comparison` — [HighamTridiagonal/CondRemarks.lean:130](HighamTridiagonal/CondRemarks.lean#L130)<br>`kappaInf_eq_comparison` — [HighamTridiagonal/CondRemarks.lean:138](HighamTridiagonal/CondRemarks.lean#L138)<br>`eq_3_8_norm_inv` — [HighamTridiagonal/CondRemarks.lean:147](HighamTridiagonal/CondRemarks.lean#L147)<br>`norm_inv_eq_solveComp` — [HighamTridiagonal/CondRemarks.lean:169](HighamTridiagonal/CondRemarks.lean#L169)<br>`norm_inv_eq_comparison_of_posDef` — [HighamTridiagonal/CondRemarks.lean:203](HighamTridiagonal/CondRemarks.lean#L203)<br>Operation counts (`13n − 10` for `‖A⁻¹‖∞`, `22n − 16` for `κ∞`): `normInvCounted` — [HighamTridiagonal/CondRemarks.lean:326](HighamTridiagonal/CondRemarks.lean#L326)<br>`normInvCounted_val` — [HighamTridiagonal/CondRemarks.lean:338](HighamTridiagonal/CondRemarks.lean#L338)<br>`normInvCounted_ops` — [HighamTridiagonal/CondRemarks.lean:344](HighamTridiagonal/CondRemarks.lean#L344)<br>`kappaInfCounted` — [HighamTridiagonal/CondRemarks.lean:330](HighamTridiagonal/CondRemarks.lean#L330)<br>`kappaInfCounted_val` — [HighamTridiagonal/CondRemarks.lean:348](HighamTridiagonal/CondRemarks.lean#L348)<br>`kappaInfCounted_ops` — [HighamTridiagonal/CondRemarks.lean:356](HighamTridiagonal/CondRemarks.lean#L356)<br>`section6_O_n_of_type` — [HighamTridiagonal/CondRemarks.lean:385](HighamTridiagonal/CondRemarks.lean#L385)<br>`section6_O_n_of_mMatrix` — [HighamTridiagonal/CondRemarks.lean:402](HighamTridiagonal/CondRemarks.lean#L402) | |
| §4, p. 526 | Nonsingular tridiagonal matrices diagonally dominant by rows or columns "have an LU factorization" (all pivots nonzero); nonsingularity cannot be dropped | `exists_LU_of_diagDominant` — [HighamTridiagonal/DDRemarks.lean:231](HighamTridiagonal/DDRemarks.lean#L231)<br>`piv_ne_zero_of_diagDominant` — [HighamTridiagonal/DDRemarks.lean:214](HighamTridiagonal/DDRemarks.lean#L214)<br>`rowDD_singular_no_LU_example` — [HighamTridiagonal/DDRemarks.lean:286](HighamTridiagonal/DDRemarks.lean#L286) | |
| §4, after Thm 4.2 | Column-dominant analogue: `‖\|U⁻¹\|\|L⁻¹\|y‖∞ ≤ (2n−1)θ‖\|A⁻¹\|y‖∞`, `θ = maxᵢ\|yᵢ\|/minᵢ\|yᵢ\|`, `y > 0` | `colDD_analogue` — [HighamTridiagonal/DiagDominant.lean:465](HighamTridiagonal/DiagDominant.lean#L465) | |
| §4, after Thm 4.2 | For `n = 2` the bound of Thm 4.2 is attained as `α → ∞` for `A = [1 1; −α α+1]`, `y = e` | `theorem_4_2_sharp_n2` — [HighamTridiagonal/Example42.lean:118](HighamTridiagonal/Example42.lean#L118)<br>`exA` — [HighamTridiagonal/Example42.lean:21](HighamTridiagonal/Example42.lean#L21)<br>`exL` — [HighamTridiagonal/Example42.lean:24](HighamTridiagonal/Example42.lean#L24)<br>`exU` — [HighamTridiagonal/Example42.lean:27](HighamTridiagonal/Example42.lean#L27) | |
| §4, after Thm 4.2 | "The bound is exact if the row diagonally dominant `A` happens to be symmetric (so that it is positive definite), nonnegative (… which implies it is totally nonnegative), or an M-matrix" | Exactness in the three cases: `rowDD_bound_exact` — [HighamTridiagonal/DDRemarks.lean:666](HighamTridiagonal/DDRemarks.lean#L666)<br>`rowDD_symm_bound_exact` — [HighamTridiagonal/DDRemarks.lean:601](HighamTridiagonal/DDRemarks.lean#L601)<br>`rowDD_nonneg_bound_exact` — [HighamTridiagonal/DDRemarks.lean:639](HighamTridiagonal/DDRemarks.lean#L639)<br>`mMatrix_bound_exact` — [HighamTridiagonal/DDRemarks.lean:650](HighamTridiagonal/DDRemarks.lean#L650)<br>"nonnegative ⇒ totally nonnegative": `rowDD_nonneg_isTotallyNonneg` — [HighamTridiagonal/DDRemarks.lean:372](HighamTridiagonal/DDRemarks.lean#L372)<br>`isTotallyNonneg_of_rowDD_nonneg` — [HighamTridiagonal/DDRemarks.lean:388](HighamTridiagonal/DDRemarks.lean#L388)<br>"symmetric ⇒ positive definite" (needs a positive diagonal, see note 10): `rowDD_symm_posDef` — [HighamTridiagonal/DDRemarks.lean:472](HighamTridiagonal/DDRemarks.lean#L472)<br>`rowDD_symm_not_posDef_example` — [HighamTridiagonal/DDRemarks.lean:546](HighamTridiagonal/DDRemarks.lean#L546)<br>`rowDD_symm_neg_bound_exact` — [HighamTridiagonal/DDRemarks.lean:612](HighamTridiagonal/DDRemarks.lean#L612)<br>General form for all types (a)–(d) of Thm 3.1: `bound_exact_of_type` — [HighamTridiagonal/Remarks.lean:157](HighamTridiagonal/Remarks.lean#L157) | |
| §4, proof of Thm 4.1 | `\|eᵢ\| ≤ \|uᵢ\|` (rows); `\|cᵢ₊₁\| ≤ \|uᵢ\|` (columns); `\|lᵢeᵢ₋₁\|+\|uᵢ\| ≤ 3\|dᵢ\|` | `rowDD_abs_supd_le_abs_piv` — [HighamTridiagonal/DiagDominant.lean:143](HighamTridiagonal/DiagDominant.lean#L143)<br>`colDD_abs_sub_le_abs_piv` — [HighamTridiagonal/DiagDominant.lean:172](HighamTridiagonal/DiagDominant.lean#L172)<br>`diag_bound` — [HighamTridiagonal/DiagDominant.lean:204](HighamTridiagonal/DiagDominant.lean#L204) | |
| §4 | Paper's definition of row diagonal dominance for tridiagonal `A` (`\|dᵢ\| ≥ \|cᵢ\|+\|eᵢ\|`) is equivalent to the general one used here | `isRowDiagDominant_iff_of_isTridiagonal` — [HighamTridiagonal/DiagDominant.lean:60](HighamTridiagonal/DiagDominant.lean#L60) | |
| §1 | `cond(A,x) ≤ κ∞(A)`; `cond(A,x)` is invariant under row scaling, "whereas `κ∞(A)` is not" | `condSkeel_le_kappa` — [HighamTridiagonal/Remarks.lean:70](HighamTridiagonal/Remarks.lean#L70)<br>`condSkeel_diagonal_mul` — [HighamTridiagonal/Remarks.lean:90](HighamTridiagonal/Remarks.lean#L90)<br>`kappaInf_not_row_scaling_invariant` — [HighamTridiagonal/CondRemarks.lean:813](HighamTridiagonal/CondRemarks.lean#L813)<br>`condSkeel_row_scaling_invariant_kappaInf_not` — [HighamTridiagonal/CondRemarks.lean:826](HighamTridiagonal/CondRemarks.lean#L826) | |
| §6 | `cond(A) = cond(A,e) ≥ cond(A,x)`, and "`cond(A)/cond(A,x)` can be arbitrarily large" | `condSkeel_le_condSkeelA` — [HighamTridiagonal/Condition.lean:64](HighamTridiagonal/Condition.lean#L64)<br>`condSkeelA_div_condSkeel_unbounded` — [HighamTridiagonal/CondRemarks.lean:507](HighamTridiagonal/CondRemarks.lean#L507)<br>also within the classes of Thm 3.1 and in every dimension `n ≥ 2`: `condSkeelA_div_condSkeel_unbounded_posDef` — [HighamTridiagonal/CondRemarks.lean:600](HighamTridiagonal/CondRemarks.lean#L600)<br>`condSkeelA_div_condSkeel_unbounded_totallyNonneg` — [HighamTridiagonal/CondRemarks.lean:524](HighamTridiagonal/CondRemarks.lean#L524)<br>`condSkeelA_div_condSkeel_unbounded_mMatrix` — [HighamTridiagonal/CondRemarks.lean:533](HighamTridiagonal/CondRemarks.lean#L533)<br>`condSkeelA_div_condSkeel_unbounded_dim` — [HighamTridiagonal/CondRemarks.lean:730](HighamTridiagonal/CondRemarks.lean#L730) | |
| §6 | `\|A\| ≤ \|L\|\|U\|` for any LU factorization (so `\|A\| ≤ \|L\|\|U\| ≤ 3\|A\|` under Thm 4.1) | `abs_le_abs_mul_abs_of_isLU` — [HighamTridiagonal/Remarks.lean:173](HighamTridiagonal/Remarks.lean#L173) | |
| §2 (implicit) | The LU factorization of a nonsingular tridiagonal matrix is unique | `IsLU.unique` — [HighamTridiagonal/Theorem31.lean:418](HighamTridiagonal/Theorem31.lean#L418) | |

## 4. Definitions used in the statements

| Concept | Lean definition |
|---|---|
| tridiagonal | `IsTridiagonal` — [HighamTridiagonal/Basic.lean:36](HighamTridiagonal/Basic.lean#L36) |
| LU factorization (`L` unit lower triangular, `U` upper triangular, `A = LU`) | `IsLU` — [HighamTridiagonal/Basic.lean:41](HighamTridiagonal/Basic.lean#L41) |
| entrywise absolute value `\|M\|` | `M.map abs` (Mathlib) |
| entrywise inequality `M ≤ N` | written out as `∀ i j, M i j ≤ N i j` |
| symmetric positive definite | `Matrix.PosDef` (Mathlib; for real matrices it includes symmetry `Aᵀ = A`) |
| totally nonnegative (all minors of all orders `≥ 0`) | `IsTotallyNonneg` — [HighamTridiagonal/TotallyNonneg.lean:26](HighamTridiagonal/TotallyNonneg.lean#L26) |
| M-matrix (nonsingular, `aᵢⱼ ≤ 0` for `i ≠ j`, `A⁻¹ ≥ 0`) | `IsMMatrix` — [HighamTridiagonal/Theorem31.lean:28](HighamTridiagonal/Theorem31.lean#L28) |
| diagonally dominant by rows / by columns | `IsRowDiagDominant` — [HighamTridiagonal/DiagDominant.lean:26](HighamTridiagonal/DiagDominant.lean#L26)<br>`IsColDiagDominant` — [HighamTridiagonal/DiagDominant.lean:30](HighamTridiagonal/DiagDominant.lean#L30) |
| floating point arithmetic with unit roundoff `u` | `FPModel` — [HighamTridiagonal/FloatingPoint.lean:27](HighamTridiagonal/FloatingPoint.lean#L27) |
| computed solution of `Ax = b` by GE + substitutions | `FPModel.solve` — [HighamTridiagonal/FloatingPoint.lean:140](HighamTridiagonal/FloatingPoint.lean#L140) |
| `cond(A,x)`, `cond(A)`, `κ∞(A)` | `condSkeel` — [HighamTridiagonal/Condition.lean:23](HighamTridiagonal/Condition.lean#L23)<br>`condSkeelA` — [HighamTridiagonal/Condition.lean:27](HighamTridiagonal/Condition.lean#L27)<br>`kappaInf` — [HighamTridiagonal/Remarks.lean:34](HighamTridiagonal/Remarks.lean#L34) |
| comparison matrix `M(B)` | `comparison` — [HighamTridiagonal/Algorithm38.lean:28](HighamTridiagonal/Algorithm38.lean#L28) |
| computed LU factorization exists (`û₀,…,û_{n−2} ≠ 0`) / GE succeeds (all `ûᵢ ≠ 0`) | `FPModel.FactorSucceeds` — [HighamTridiagonal/FloatingPoint.lean:114](HighamTridiagonal/FloatingPoint.lean#L114)<br>`FPModel.Succeeds` — [HighamTridiagonal/FloatingPoint.lean:110](HighamTridiagonal/FloatingPoint.lean#L110) |
| operation-counted computation (cost model for "`O(n)` operations") | `OpCount.Counted` — [HighamTridiagonal/OpCount38.lean:123](HighamTridiagonal/OpCount38.lean#L123)<br>`condAlgCounted` — [HighamTridiagonal/OpCount38.lean:652](HighamTridiagonal/OpCount38.lean#L652) |
| `‖v‖∞` | Mathlib's sup norm `‖v‖` on `Fin n → ℝ` (= `maxᵢ \|vᵢ\|`) |

## 5. Not formalized

* **(1.1) and (1.3).** These are known results about Gaussian elimination on general dense
  matrices: Wilkinson's GEPP bound with growth factor `ρₙ` and cubic `p(n)`, and the de
  Boor–Pinkus bound with `c_n = 2n + O(u)`. The paper quotes them as motivation. It neither
  proves nor uses them. What the paper does prove is their tridiagonal versions, (2.7) and
  Theorem 3.2 / (3.4), and those are formalized. The consequences the paper draws from (1.1)
  and (1.3), namely (1.2), (1.4) and (1.5), are formalized as stand-alone implications.
* **Other results quoted from the literature** (stated without proof in the paper, about general
  dense matrices or other algorithms): (1.4) holding for triangular and for totally nonnegative
  `A` [17], [5]; GEPP followed by one step of iterative refinement [1], [20]; the growth factor
  `ρₙ ≤ 1` for symmetric positive definite matrices [21]; the `O(n)` `κ∞` algorithms of [15] and
  the SONEST estimator [16] (§5).
* **Table 6.1 and the experiment of §6** (the Dorr matrix, measured errors). This is numerical
  data, not a mathematical claim. Only the constant in (6.1) is checked: `constant_6_1` — [HighamTridiagonal/Remarks.lean:147](HighamTridiagonal/Remarks.lean#L147).
* **Practical remarks:** Neumaier's experiments, the remarks on LAPACK, SONEST, LDLᵀ/BABE
  factorizations, the specific flop counts of §6 (e.g. "computing cond(A, x) requires 6n flops"
  for an LDLᵀ variant, which depend on the flop convention of [12]; the `O(n)` claim of §3 itself
  *is* formalized with an explicit cost model, `condAlgCounted_ops`), and the informal sentence
  in §4 that combining Theorem 4.1 with (2.7) gives a small componentwise backward error.

## 6. Notes on conventions and faithfulness

1. **Indices** are 0-based. With `ent A i j` the paper's entries (renumbered from 0) are
   `cᵢ₊₁ = ent A (i+1) i`, `dᵢ = ent A i i` and `eᵢ = ent A i (i+1)`. The pivots `uᵢ` are
   `piv A i`, the multipliers `lᵢ₊₁` are `mult A (i+1)`, and `eᵢ` is also written `supd A i`.
2. **LU factorization** means the general notion: `L` unit lower triangular, `U` upper
   triangular, `A = LU`. The bidiagonal shape (2.2) is not assumed. It is proved
   (`IsLU.eq_recurrence`), so the theorems apply to any LU factorization.
3. **Nonsingularity.** Theorems 3.1, 3.3, 4.1 and 4.2 assume `A` nonsingular
   (`IsUnit A.det`), exactly as in the paper. Theorem 3.2 refers to "type (a)–(d) in Theorem
   3.1", which is stated for nonsingular `A`, so `IsUnit A.det` is also a hypothesis there. It
   is genuinely needed: a singular totally nonnegative matrix such as `0` breaks Gaussian
   elimination.
4. **"`u` sufficiently small"** in Theorem 3.2 means: there is `u₀ > 0`, depending only on `A`,
   such that the conclusion holds for **every** arithmetic `fp : FPModel u` with `u < u₀`
   satisfying (2.4), and for **every** right-hand side `b`. "GE succeeds" (`FPModel.Succeeds`)
   means that all computed pivots `ûᵢ` are nonzero, so no division by zero occurs.
5. **Floating point model.** `FPModel u` packages arbitrary operations
   `fl(x+y), fl(x−y), fl(x*y), fl(x/y)` satisfying both (2.4a) and (2.4b). For division the
   axioms are required only for nonzero divisors. Any real arithmetic obeying the standard model
   (e.g. round-to-nearest without underflow or overflow) is an instance. The algorithm
   (`FPModel.piv/mult/fwd/back`) performs exactly the operations of (2.3) and of forward/back
   substitution: `l̂ᵢ = fl(cᵢ/ûᵢ₋₁)`, `ûᵢ = fl(dᵢ − fl(l̂ᵢeᵢ₋₁))`,
   `ŷᵢ = fl(bᵢ − fl(l̂ᵢŷᵢ₋₁))`, `x̂ᵢ = fl(fl(ŷᵢ − fl(eᵢx̂ᵢ₊₁))/ûᵢ)`.
6. **Diagonal dominance** uses the standard definition `∑_{j≠i}|aᵢⱼ| ≤ |aᵢᵢ|`; by columns
   means `Aᵀ` is dominant by rows, as in the paper. For tridiagonal matrices this is the
   paper's `|dᵢ| ≥ |cᵢ| + |eᵢ|` (`isRowDiagDominant_iff_of_isTridiagonal`).
7. **Norms.** `‖·‖∞` on vectors is the sup norm. For (1.2) and `κ∞` the matrix norm is the
   induced `∞`-norm (maximum row sum, Mathlib's `Matrix.Norms.Operator`).
8. **(3.5).** The paper writes the condition as `sign(lᵢeᵢ₋₁/uᵢ) = 1`. With the usual convention
   `sign(0) = 0` (Mathlib's `Real.sign`), that form is sufficient but **not necessary**: for a
   diagonal (or reducible) `A` we have `lᵢeᵢ₋₁ = 0`, so the sign is `0`, yet `|L||U| = |LU|`.
   The exact condition is `lᵢeᵢ₋₁/uᵢ ≥ 0` (equivalently `lᵢeᵢ₋₁uᵢ ≥ 0`); this is what `eq_3_5`
   proves and what the proof of Theorem 3.3 uses, and both facts about the literal form are
   proved. (Under a convention with `sign(0) = 1` the paper's wording would be exact.)
   Theorem 3.3 itself is unaffected.
9. **(6.1).** With `u = 2⁻²³` and `cond(A) = 1.33·10⁶` the exact constant
   `h(u)/(1 − cond(A)h(u))` lies in `[10.93u, 10.94u]` (`constant_6_1`), i.e. `10.9u` to three
   significant figures. Since the paper's `cond(A) = 1.33E6` is itself rounded, this is
   consistent with the paper's `10.9`; (6.1) is therefore formalized in its exact general form
   (`forward_error_bound`), with the numerical constant checked separately.
10. **"symmetric (so that it is positive definite)"** (§4). A symmetric, row diagonally dominant,
   nonsingular tridiagonal matrix is positive definite **if its diagonal is positive**
   (`rowDD_symm_posDef`); without that it can be indefinite and the bound of Theorem 4.2 can fail
   to be exact (`rowDD_symm_not_posDef_example`, the matrix `[2 1; 1 −2]`). With a negative
   diagonal the bound is again exact (`rowDD_symm_neg_bound_exact`).
11. **Unit roundoff.** The floating point lemmas (2.5)–(2.7), (3.1)–(3.3) assume `u < 1` (the
   paper leaves this implicit; it is needed to multiply (2.4b) out, since `1 + ε` must be
   nonzero). Theorem 3.2 has no such hypothesis: its `u₀` is chosen `≤ 1`.
