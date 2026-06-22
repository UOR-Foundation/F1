/-
F1 square — v0.22.0 crux frontier: **the LOOSE UPPER bracket on the second Stieltjes constant `γ₂`**
(`γ₂ ≤ 1/20`), the last constant input to `Pos Rlambda4` (the n=4 prime–archimedean coupling).

`λ₄`'s arithmetic side carries `−2γγ₂` through `η₃`; with `γ > 0` a LOOSE UPPER bound `γ₂ ≤ ε`
(`ε` modest, here `1/20`) suffices to control it (the `Pos λ₄` margin is `≈ +0.054` once `γ₁ ≤ −0.0677`
and `γ₃ ≤ 1/8` are in place). This file builds that upper bracket by the SAME DISCRETE Euler–Maclaurin
acceleration as `GammaTwoBracket` (the `γ₂` LOWER bound) — but in the UPPER direction, mirroring the
`γ₃`/`γ₁` upper pipelines.

The per-step trapezoidal residual `sStep ≈ decompForm = b²·C2 + b·R1 + R0` (`b = ln p`, `δ = a−b`,
`u0 = 1/p`, `u1 = 1/(p+1)`):
  b²·C2 ≤ 1/(p(p+1))   (C2 = ½(u0+u1)−δ ≤ 1/(2p(p+1)(2p+1)) (`C2_le`), b² ≤ 4p (`logSq_le_self4`))
  b·R1  ≤ 0            (R1 = δ(u1−δ),  u1 ≤ δ)
  R0    ≤ 1/(p(p+1))   (R0 = ½δ²u1 − ⅓δ³ ≤ ½δ²u1, δ² ≤ 1/p²)
so `sStep ≤ 2/(p(p+1))`, telescoping to `γ₂ ≤ hSeq(N) + 2/(N+1) + corr + 1/(j+1)`.

The only new ingredient is `(ln p)² ≤ 4p` (`logSq_le_self4`): with `M = L/2`, `exp(M) ≥ 1+M ≥ M`, so
`exp(L) = exp(M)² ≥ M²`, i.e. `4·exp(L) ≥ L²`; `exp(ln p) = p`.  No `RrpowPos`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaThreeBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- `logN` opaque downstream: prevents exponential `whnf`/`isDefEq` blowup on the nested `δ = ln(p+1)−ln p`.
attribute [local irreducible] logN

-- ===========================================================================
-- (S1) The square-root cap `(ln p)² ≤ 4p`.
-- ===========================================================================

/-- **Square monotonicity** `0 ≤ A ≤ B ⟹ A² ≤ B²`. -/
theorem sq_le_sq {A B : Real} (hA : Rnonneg A) (hB : Rnonneg B) (hAB : Rle A B) :
    Rle (Rmul A A) (Rmul B B) :=
  Rle_trans (Rmul_le_Rmul_right hA hAB) (Rmul_le_Rmul_left hB hAB)

/-- **`L² ≤ 4·exp(L)`** for `L ≥ 0`.  With `M = L/2`: `exp(M) ≥ 1+M ≥ M ≥ 0`, so
    `exp(L) = exp(M+M) = exp(M)² ≥ M²`, and `4·M² = L²`. -/
theorem sq_le_4_exp (L : Real) (hL : Rnonneg L) :
    Rle (Rmul L L) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (RexpReal L)) := by
  have hMnn : Rnonneg (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) :=
    Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) hL
  have hEnn : Rnonneg (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) := RexpReal_nonneg _
  have hMleE : Rle (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)
      (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) :=
    Rle_trans (Rle_self_Radd_left Rnonneg_one) (RexpReal_ge_one_add_nonneg hMnn)
  have hsq := sq_le_sq hMnn hEnn hMleE
  -- M+M ≈ L
  have hcoef : Req (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) L := by
    refine Req_trans (Req_symm (Rmul_distrib_right _ _ L)) ?_
    refine Req_trans (Rmul_congr ?_ (Req_refl L)) (Rone_mul L)
    exact Req_trans (Radd_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  -- E² ≈ exp(L)
  have hE2 : Req (Rmul (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))
        (RexpReal (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))) (RexpReal L) :=
    Req_trans (Req_symm (RexpReal_add _ _)) (RexpReal_congr hcoef)
  -- L² ≈ 4·M²
  have hconst : Req (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide)))) one := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ (by decide) (by decide))) ?_
    exact Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  have hL2 : Req (Rmul L L)
      (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide))
        (Rmul (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) L))) := by
    refine Req_symm ?_
    refine Req_trans (Rmul_congr (Req_refl _) (prod_sq_reassoc (ofQ (⟨1, 2⟩ : Q) (by decide)) L)) ?_
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨4, 1⟩ : Q) (by decide))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨1, 2⟩ : Q) (by decide))) (Rmul L L))) ?_
    exact Req_trans (Rmul_congr hconst (Req_refl _)) (Rone_mul _)
  refine Rle_trans (Rle_of_Req hL2) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) hsq) ?_
  exact Rle_of_Req (Rmul_congr (Req_refl _) hE2)

/-- **`(ln p)² ≤ 4·p`** — the square-root cap. -/
theorem logSq_le_self4 (p : Nat) (hp : 1 ≤ p) :
    Rle (Rmul (logN p hp) (logN p hp)) (ofQ (⟨4 * (p : Int), 1⟩ : Q) Nat.one_pos) := by
  refine Rle_trans (sq_le_4_exp (logN p hp) (Rnonneg_logN p hp)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rexp_logN p hp))) ?_
  exact Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr (Qmul_den_pos (by decide) Nat.one_pos) Nat.one_pos
      (by show Qeq (mul (⟨4, 1⟩ : Q) (⟨(p : Int), 1⟩ : Q)) (⟨4 * (p : Int), 1⟩ : Q)
          simp only [Qeq, mul])))

-- ===========================================================================
-- (S2) The per-step UPPER bound `sStep p ≤ 2/(p(p+1))` on the squared-log trapezoidal residual.
-- ===========================================================================

/-- **`b²·C2 ≤ 1/(p(p+1))`** — `b² = (ln p)² ≤ 4p` (`logSq_le_self4`), `C2 ≤ 1/(2p(p+1)(2p+1))`
    (`C2_le`), so `b²·C2 ≤ 4p/(2p(p+1)(2p+1)) ≤ 1/(p(p+1))`. -/
theorem b2C2_le (p : Nat) (hp : 1 ≤ p) :
    Rle (Rmul (Rmul (logN p hp) (logN p hp))
          (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
              (Radd (ofQ (⟨1, p⟩ : Q) hp) (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))))
            (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))))
        (ofQ (⟨1, p * (p + 1)⟩ : Q) (Nat.mul_pos hp (Nat.succ_pos p))) := by
  have h4nn : Rnonneg (ofQ (⟨4 * (p : Int), 1⟩ : Q) Nat.one_pos) :=
    Rnonneg_ofQ Nat.one_pos (by show (0 : Int) ≤ 4 * (p : Int); omega)
  refine Rle_trans (Rmul_le_Rmul_right (C2_nonneg p hp) (logSq_le_self4 p hp)) ?_
  refine Rle_trans (Rmul_le_Rmul_left h4nn (C2_le p hp)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ (a := (⟨4 * (p : Int), 1⟩ : Q))
    (b := (⟨1, 2 * p * (p + 1) * (2 * p + 1)⟩ : Q)) Nat.one_pos
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hp) (Nat.succ_pos p)) (by omega)))) ?_
  refine Rle_ofQ_ofQ _ (Nat.mul_pos hp (Nat.succ_pos p)) ?_
  show Qle (mul (⟨4 * (p : Int), 1⟩ : Q) (⟨1, 2 * p * (p + 1) * (2 * p + 1)⟩ : Q))
    (⟨1, p * (p + 1)⟩ : Q)
  simp only [Qle, mul, Int.one_mul, Int.mul_one, Nat.one_mul, Nat.mul_one]
  have key : 4 * p * (p * (p + 1)) ≤ 2 * p * (p + 1) * (2 * p + 1) := by
    have e1 : ((2 * p * (p + 1) * (2 * p + 1) : Nat) : Int)
        = ((4 * p * (p * (p + 1)) + 2 * p * (p + 1) : Nat) : Int) := by push_cast; ring_uor
    have n1 : 2 * p * (p + 1) * (2 * p + 1) = 4 * p * (p * (p + 1)) + 2 * p * (p + 1) := by
      exact_mod_cast e1
    omega
  exact_mod_cast key

/-- **`b·R1 = b·δ(u1−δ) ≤ 0`** (`u1 ≤ δ`, so `δ(u1−δ) ≤ 0`). -/
theorem bR1_le_sq (p : Nat) (hp : 1 ≤ p) :
    Rle (Rmul (logN p hp)
          (Rsub (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
              (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
            (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
              (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))))
        zero := by
  have hδnn : Rnonneg (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)) :=
    Rnonneg_Rsub_of_Rle (logN_mono hp (Nat.le_succ p))
  -- δ·u1 ≤ δ·δ  (u1 ≤ δ)
  have hδu1 : Rle (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
        (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)))
      (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
        (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))) :=
    Rmul_le_Rmul_left hδnn (deltaLog_lower p hp)
  exact Rmul_nonpos_left (Rnonneg_logN p hp) (Rle_sub_zero hδu1)

/-- **`R0 = ½δ²u1 − ⅓δ³ ≤ 1/(p(p+1))`** (drop `−⅓δ³ ≤ 0`, `δ² ≤ 1/p²`, `u1 = 1/(p+1)`,
    `p(p+1) ≤ 2p²(p+1)`). -/
theorem R0_le_sq (p : Nat) (hp : 1 ≤ p) :
    Rle (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
            (Rmul (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
              (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p))))
          (Rmul (ofQ (⟨1, 3⟩ : Q) (by decide))
            (Rmul (Rmul (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp))
                (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))
              (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)))))
        (ofQ (⟨1, p * (p + 1)⟩ : Q) (Nat.mul_pos hp (Nat.succ_pos p))) := by
  have hδnn : Rnonneg (Rsub (logN (p + 1) (Nat.succ_pos p)) (logN p hp)) :=
    Rnonneg_Rsub_of_Rle (logN_mono hp (Nat.le_succ p))
  have hu1nn : Rnonneg (ofQ (⟨1, p + 1⟩ : Q) (Nat.succ_pos p)) :=
    Rnonneg_ofQ (Nat.succ_pos p) (by show (0 : Int) ≤ 1; decide)
  -- drop −⅓δ³: R0 ≤ ½δ²u1
  refine Rle_trans (Rsub_le_self _ (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide))
    (Rnonneg_Rmul (Rnonneg_Rmul_self _) hδnn))) ?_
  -- ½δ²u1 ≤ ½·(1/p²)·(1/(p+1))
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide))
    (Rmul_le_Rmul_right hu1nn (dsq_self_le p hp))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _)
    (Rmul_ofQ_ofQ (a := mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) (b := (⟨1, p + 1⟩ : Q))
      (Qmul_den_pos hp hp) (Nat.succ_pos p)))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ (a := (⟨1, 2⟩ : Q))
    (b := mul (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) (⟨1, p + 1⟩ : Q)) (by decide)
    (Qmul_den_pos (Qmul_den_pos hp hp) (Nat.succ_pos p)))) ?_
  refine Rle_ofQ_ofQ _ (Nat.mul_pos hp (Nat.succ_pos p)) ?_
  show Qle (mul (⟨1, 2⟩ : Q) (mul (mul (⟨1, p⟩ : Q) (⟨1, p⟩ : Q)) (⟨1, p + 1⟩ : Q)))
    (⟨1, p * (p + 1)⟩ : Q)
  simp only [Qle, mul, Int.one_mul, Int.mul_one, Nat.one_mul, Nat.mul_one]
  have key : p * (p + 1) ≤ 2 * (p * p * (p + 1)) := by
    have h2 : p * (p + 1) ≤ (p * p) * (p + 1) :=
      Nat.mul_le_mul_right (p + 1) (Nat.le_mul_of_pos_left p hp)
    omega
  exact_mod_cast key

/-- **The per-step UPPER bound** `sStep p ≤ 2/(p(p+1))` (`sStep_decomp`, `1 + 0 + 1`). -/
theorem sStep_le (p : Nat) (hp : 1 ≤ p) :
    Rle (sStep p hp) (ofQ (⟨2, p * (p + 1)⟩ : Q) (Nat.mul_pos hp (Nat.succ_pos p))) := by
  have hD : 0 < p * (p + 1) := Nat.mul_pos hp (Nat.succ_pos p)
  refine Rle_trans (Rle_of_Req (sStep_decomp p hp)) ?_
  refine Rle_trans (Radd_le_add (Radd_le_add (b2C2_le p hp) (bR1_le_sq p hp)) (R0_le_sq p hp)) ?_
  refine Rle_of_Req ?_
  refine Req_trans (Radd_congr (Radd_zero _) (Req_refl _)) ?_
  exact Radd_ofQ_same 1 1 (p * (p + 1)) hD

end UOR.Bridge.F1Square.Analysis
