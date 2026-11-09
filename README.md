# higham-error-tridiagonal

A Lean 4 / Mathlib formalization of

> N. J. Higham, *Bounding the error in Gaussian elimination for tridiagonal systems*,
> SIAM J. Matrix Anal. Appl. 11(4) (1990), 521–530.

All numbered theorems of the paper (Theorems 3.1, 3.2, 3.3, 4.1, 4.2) are formalized and
proved. The same holds for the numbered equations that state mathematical claims, among them
the floating point backward error analysis (2.5)–(2.7) and the `O(n)` condition number
algorithm (3.8). There are no `sorry`s and no added axioms.

**See [`mapping.md`](mapping.md)** for the correspondence between the results of the paper and
the Lean declarations, with clickable `file:line` links and notes on conventions.

## Building

```bash
# install elan (Lean toolchain manager) if needed, then:
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check that only Lean's standard axioms are used:

```bash
lake env lean scripts/check_axioms.lean
```

## Layout

| File | Contents |
|---|---|
| `HighamTridiagonal/Basic.lean` | tridiagonal matrices, LU factorization, the recurrence (2.3), bidiagonal factors (2.2), uniqueness of the LU factorization, the sign condition for `\|L\|\|U\| = \|LU\|` |
| `HighamTridiagonal/Inverse.lean` | inverses of bidiagonal matrices, (3.6), (3.7) |
| `HighamTridiagonal/Determinant.lean` | leading principal minors of tridiagonal matrices and the pivots |
| `HighamTridiagonal/TotallyNonneg.lean` | totally nonnegative matrices |
| `HighamTridiagonal/Theorem31.lean` | Theorem 3.1 (including the equivalences in (b) and (c)) |
| `HighamTridiagonal/FloatingPoint.lean` | floating point model (2.4), the algorithm, (2.5)–(2.7), (3.1)–(3.3) |
| `HighamTridiagonal/Theorem32.lean` | Theorem 3.2 |
| `HighamTridiagonal/Theorem33.lean` | Theorem 3.3 |
| `HighamTridiagonal/DiagDominant.lean` | Theorems 4.1, 4.2 and the column-dominant analogue |
| `HighamTridiagonal/Condition.lean` | Skeel's condition numbers, (1.5) |
| `HighamTridiagonal/Algorithm38.lean` | comparison matrices, (3.5), (3.8) |
| `HighamTridiagonal/Remarks.lean` | (1.2), (1.4), (6.1) and other remarks |
