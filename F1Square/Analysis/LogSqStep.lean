/-
F1 square — **the `∫ log/x` layer, part 1: the `log²` step bracket** (`LogSqStep.lean`).
The `t4` slot's `poleB` component is `∫ f(x)/x dx = 4(log 2)²`, whose antiderivative is
`log²x/2` — the mirror of `Gn(n) = n·log n − n` for the `∫log` layer. This file opens
the campaign with the antiderivative object and its unit-step bracket:

    `Hn(n) := (log n)²`,
    `(log i + log(i+1))/(i+1)  ≤  Hn(i+1) − Hn(i)  ≤  (log i + log(i+1))/i`

— pure algebra over the certified per-step log bracket (`ExpBounds`): the difference of
squares collapses (`Hn(i+1) − Hn(i) = (log(i+1) − log i)·(log(i+1) + log i)`,
`Rmul_sub_add_self`), the first factor is bracketed by `[1/(i+1), 1/i]`
(`logN_step_lower/upper`), and the second factor is nonneg (`Rnonneg_logN`). General in
`i` — the telescope over `i = c·2^m + j` (unbounded) consumes exactly this shape.

HONEST SCOPE. An antiderivative object and a step inequality; no integral is evaluated
and no positivity is claimed. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.LogStep
import F1Square.Analysis.HarmonicLog32

namespace UOR.Bridge.F1Square.Analysis

/-- **The `∫ log/x` antiderivative at integer arguments**: `Hn(n) = (log n)²`
    (the exact value of `2·∫₁ⁿ log x/x dx`). -/
def Hn (n : Nat) (hn : 1 ≤ n) : Real := Rmul (logN n hn) (logN n hn)

/-- `Hn(1) ≈ 0` (`log 1 = 0`). -/
theorem Hn_one : Req (Hn 1 (by omega)) zero :=
  Req_trans (Rmul_congr logN_one (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))

/-- The difference of squares collapse:
    `Hn(i+1) − Hn(i) ≈ (log(i+1) − log i)·(log(i+1) + log i)`. -/
private theorem Hn_diff (i : Nat) (hi : 1 ≤ i) :
    Req (Rsub (Hn (i + 1) (by omega)) (Hn i hi))
      (Rmul (Rsub (logN (i + 1) (by omega)) (logN i hi))
        (Radd (logN (i + 1) (by omega)) (logN i hi))) :=
  Req_symm (Rmul_sub_add_self (logN (i + 1) (by omega)) (logN i hi))

/-- The step difference is bracketed below: `1/(i+1) ≤ log(i+1) − log i`. -/
private theorem logStep_diff_lower (i : Nat) (hi : 1 ≤ i) :
    Rle (ofQ (⟨1, i + 1⟩ : Q) (Nat.succ_pos i))
      (Rsub (logN (i + 1) (by omega)) (logN i hi)) :=
  Rle_Rsub_of_Radd_le (logN_step_lower i hi)

/-- The step difference is bracketed above: `log(i+1) − log i ≤ 1/i`. -/
private theorem logStep_diff_upper (i : Nat) (hi : 1 ≤ i) :
    Rle (Rsub (logN (i + 1) (by omega)) (logN i hi)) (ofQ (⟨1, i⟩ : Q) hi) :=
  Rsub_le_of_le_Radd
    (Rle_trans (logN_step_upper i hi) (Rle_of_Req (Radd_comm _ _)))

/-- The log sum factor is nonneg. -/
private theorem logsum_nonneg (i : Nat) (hi : 1 ≤ i) :
    Rnonneg (Radd (logN (i + 1) (by omega)) (logN i hi)) :=
  Rnonneg_Radd (Rnonneg_logN (i + 1) (by omega)) (Rnonneg_logN i hi)

/-- **The step bracket, lower side**:
    `(1/(i+1))·(log(i+1) + log i) ≤ Hn(i+1) − Hn(i)` — general in `i`. -/
theorem Hn_step_lower (i : Nat) (hi : 1 ≤ i) :
    Rle (Rmul (ofQ (⟨1, i + 1⟩ : Q) (Nat.succ_pos i))
        (Radd (logN (i + 1) (by omega)) (logN i hi)))
      (Rsub (Hn (i + 1) (by omega)) (Hn i hi)) :=
  Rle_trans (Rmul_le_Rmul_right (logsum_nonneg i hi) (logStep_diff_lower i hi))
    (Rle_of_Req (Req_symm (Hn_diff i hi)))

/-- **The step bracket, upper side**:
    `Hn(i+1) − Hn(i) ≤ (1/i)·(log(i+1) + log i)` — general in `i`. -/
theorem Hn_step_upper (i : Nat) (hi : 1 ≤ i) :
    Rle (Rsub (Hn (i + 1) (by omega)) (Hn i hi))
      (Rmul (ofQ (⟨1, i⟩ : Q) hi)
        (Radd (logN (i + 1) (by omega)) (logN i hi))) :=
  Rle_trans (Rle_of_Req (Hn_diff i hi))
    (Rmul_le_Rmul_right (logsum_nonneg i hi) (logStep_diff_upper i hi))

end UOR.Bridge.F1Square.Analysis
