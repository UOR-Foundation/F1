/-
F1 square — v0.22.0 crux frontier: **the certified UPPER bracket on the third Stieltjes constant `γ₃`**
via DISCRETE Euler–Maclaurin (NO constructive integration), the `λ₄` (n=4 coupling) input.

`γ₄`'s closed form (`LambdaFour.lean`) carries `γ₃` ONLY through `η₃` with coefficient `+2/3`, so
`λ₄^{arith}` carries `−(2/3)γ₃ ≈ −0.00137`. Hence `Pos λ₄` needs only a LOOSE UPPER bound on `γ₃`
(the side controlling that negative term) — this file builds it.

`γ₃ = g₃(N) + tail` (`g₃(N) = Σ_{k≤N}(ln k)³/k − ¼(ln N)⁴`, `GammaThree.lean`). The trapezoidal anchor
`½f(N)` (`f(x) = (ln x)³/x`) captures the leading tail `½(ln N)³/N`, leaving the summable residual
`s_p = O((ln p)³/p³)`. So `γ₃ ≤ g₃(N) − ½(ln N)³/N + ε = hSeq3(N) + ε`, certifiable at modest `N` with
the rational cubed/quartic-log evaluators.

THIS FILE — part (A): the cubed-log UPPER-sum evaluator `lnCubeSumUp` (a rational upper bound for
`Σ_{k=1}^N (ln k)³/k`, the `GammaTwoBracket.lnSqSumLo` analogue, upper side, via `logBound` cubed and
round-up) and the quartic- and cubed-log LOWER bounds (`logQuartic`/`lnCubeOver` via `logLowBound`), the
pieces of the upper bound on `hSeq3 N`. The accelerated sequence, residual, telescoping and final
assembly follow.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.GammaThree
import F1Square.Analysis.GammaTwoBracket

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- ===========================================================================
-- (A) `lnCubeSumUp` — a rational UPPER bound for `lnCubeSum N = Σ_{k=1}^N (ln k)³/k`.
-- ===========================================================================

/-- The accumulated rational upper bound for `Σ_{k=1}^N (ln k)³/k`, at fixed denominator `D`: each new
    term `(log(n+1))³/(n+1) ≤ (logBound n)³·(1/(n+1))`, then round UP. -/
def lnCubeSumUp (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (n + 1) =>
      qRoundUp (add (lnCubeSumUp T D n)
        (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩)) D

theorem lnCubeSumUp_den_pos (T D : Nat) (hD : 0 < D) : ∀ N, 0 < (lnCubeSumUp T D N).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`lnCubeSum N ≤ ofQ(lnCubeSumUp T D N)`** — the partial sum `Σ (log k)³/k` bounded ABOVE
    term-by-term via `logCube_le` (depth-`T` `logBound` cubed), accumulated at denominator `D`
    (round up). -/
theorem lnCubeSum_le (T D : Nat) (hD : 0 < D) :
    ∀ N, Rle (lnCubeSum N) (ofQ (lnCubeSumUp T D N) (lnCubeSumUp_den_pos T D hD N)) := by
  intro N
  induction N with
  | zero =>
    have h0 : Req (ofQ (lnCubeSumUp T D 0) (lnCubeSumUp_den_pos T D hD 0)) zero :=
      Req_of_seq_Qeq (fun n => by show Qeq (⟨0, D⟩ : Q) ⟨0, 1⟩; simp only [Qeq]; push_cast; ring_uor)
    exact Rle_of_Req (Req_symm h0)
  | succ n ih =>
    have Ld := logBound_den_pos T D hD n
    have hcubed : 0 < (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)).den :=
      Qmul_den_pos (Qmul_den_pos Ld Ld) Ld
    have hmuld : 0 < (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n))
        (⟨1, n + 1⟩ : Q)).den := Qmul_den_pos hcubed (Nat.succ_pos n)
    -- per-term upper bound `(ln(n+1))³·(1/(n+1)) ≤ ofQ((logBound n)³·(1/(n+1)))`
    have hterm : Rle (lnCubeOver (n + 1) (by omega))
        (ofQ (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩) hmuld) := by
      refine Rle_trans (Rmul_le_Rmul_right
        (Rnonneg_ofQ (Nat.succ_pos n) (by show (0 : Int) ≤ 1; decide)) (logCube_le T D n hD)) ?_
      exact Rle_of_Req (Rmul_ofQ_ofQ hcubed (Nat.succ_pos n))
    have hadd := add_den_pos (lnCubeSumUp_den_pos T D hD n) hmuld
    -- accumulate: lnCubeSum n + lnCubeOver(n+1) ≤ ofQ(prev + term) ≤ ofQ(round-up)
    refine Rle_trans (Radd_le_add ih hterm) ?_
    refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ (lnCubeSumUp_den_pos T D hD n) hmuld)) ?_
    exact Rle_ofQ_ofQ hadd (lnCubeSumUp_den_pos T D hD (n + 1))
      (qRoundUp_ge (add (lnCubeSumUp T D n)
        (mul (mul (mul (logBound T D n) (logBound T D n)) (logBound T D n)) ⟨1, n + 1⟩)) hadd D)

-- ===========================================================================
-- (B) Quartic-/cubed-log LOWER bounds (`logLowBound`) — for the subtracted terms of `hSeq3`.
-- ===========================================================================

/-- `ofQ(logLowBound T D M) ≥ 0`. -/
theorem logLowBound_ofQ_nonneg (T D M : Nat) (hD : 0 < D) :
    Rnonneg (ofQ (logLowBound T D M) (logLowBound_den_pos T D hD M)) :=
  Rnonneg_ofQ (logLowBound_den_pos T D hD M) (logLowBound_num_nonneg T D M)

/-- **Cubed-log lower bound** `(logLowBound M)³ ≤ (ln(M+1))³` (`logCube`), depth `T ≤ 21`. -/
theorem logCube_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
          (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M) (logLowBound_den_pos T D hD M))
            (logLowBound_den_pos T D hD M)))
        (logCube (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  refine Rle_trans (Rle_of_Req ?_) (cube_mono (logLowBound_ofQ_nonneg T D M hD)
    (Rnonneg_logN (M + 1) (Nat.succ_pos M)) (logN_ge_logLowBound T D hD hT M))
  exact Req_symm (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LLd LLd) (Req_refl _))
    (Rmul_ofQ_ofQ (Qmul_den_pos LLd LLd) LLd))

/-- **Quartic-log lower bound** `(logLowBound M)⁴ ≤ (ln(M+1))⁴` (`logQuartic = logCube·logN`). -/
theorem logQuartic_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
            (logLowBound T D M))
          (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M)
            (logLowBound_den_pos T D hD M)) (logLowBound_den_pos T D hD M))
            (logLowBound_den_pos T D hD M)))
        (logQuartic (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  have hcubed : 0 < (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M)).den :=
    Qmul_den_pos (Qmul_den_pos LLd LLd) LLd
  have hcubenn : Rnonneg (ofQ (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
      hcubed) :=
    Rnonneg_congr (Req_trans (Rmul_congr (Rmul_ofQ_ofQ LLd LLd) (Req_refl _))
        (Rmul_ofQ_ofQ (Qmul_den_pos LLd LLd) LLd))
      (Rnonneg_Rmul (Rnonneg_Rmul (logLowBound_ofQ_nonneg T D M hD) (logLowBound_ofQ_nonneg T D M hD))
        (logLowBound_ofQ_nonneg T D M hD))
  -- (LL)⁴ = (LL)³·LL ≤ (ln)³·LL ≤ (ln)³·(ln) = logQuartic
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hcubed LLd)) ?_
  refine Rle_trans (Rmul_le_Rmul_right (logLowBound_ofQ_nonneg T D M hD) (logCube_ge T D M hD hT)) ?_
  exact Rmul_le_Rmul_left (logCube_nonneg (M + 1) (Nat.succ_pos M)) (logN_ge_logLowBound T D hD hT M)

/-- **Cubed-log-over-`N` lower bound** `(logLowBound M)³·(1/(M+1)) ≤ (ln(M+1))³/(M+1)` (`lnCubeOver`)
    — the trapezoidal anchor `f(M+1)`, bounded below. -/
theorem lnCubeOver_ge (T D M : Nat) (hD : 0 < D) (hT : T ≤ 21) :
    Rle (ofQ (mul (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M))
            (⟨1, M + 1⟩ : Q))
          (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos (logLowBound_den_pos T D hD M)
            (logLowBound_den_pos T D hD M)) (logLowBound_den_pos T D hD M)) (Nat.succ_pos M)))
        (lnCubeOver (M + 1) (Nat.succ_pos M)) := by
  have LLd := logLowBound_den_pos T D hD M
  have hcubed : 0 < (mul (mul (logLowBound T D M) (logLowBound T D M)) (logLowBound T D M)).den :=
    Qmul_den_pos (Qmul_den_pos LLd LLd) LLd
  have hovnn : Rnonneg (ofQ (⟨1, M + 1⟩ : Q) (Nat.succ_pos M)) :=
    Rnonneg_ofQ (Nat.succ_pos M) (by show (0 : Int) ≤ 1; decide)
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hcubed (Nat.succ_pos M))) ?_
  exact Rmul_le_Rmul_right hovnn (logCube_ge T D M hD hT)

-- ===========================================================================
-- (C1) The accelerated sequence `hSeq3 j = g₃(j) − ½·(ln(j+1))³/(j+1)` (`→ γ₃`), whose per-step
-- increment is the trapezoidal residual `sStep3` (`f(x) = (ln x)³/x`, ∫ = ¼(ln x)⁴).
-- ===========================================================================

/-- The Euler–Maclaurin **accelerated sequence** `hSeq3 j = g₃(j) − ½·(ln(j+1))³/(j+1)` — same limit
    `γ₃` as `g₃`, but its increment is the summable trapezoidal residual. -/
def hSeq3 (j : Nat) : Real :=
  Rsub (g3Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))

/-- The **per-step trapezoidal residual** `s_p = ½[(ln(p+1))³/(p+1) + (ln p)³/p] − ¼[(ln(p+1))⁴ −
    (ln p)⁴]` (`p ≥ 1`) — `O((ln p)³/p³)`, the increment of `hSeq3`. -/
def sStep3 (p : Nat) (hp : 1 ≤ p) : Real :=
  Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (p + 1) (Nat.succ_pos p)))
             (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver p hp)))
       (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
         (Rsub (logQuartic (p + 1) (Nat.succ_pos p)) (logQuartic p hp)))

/-- **`hSeq3(j+1) − hSeq3 j ≈ s_{j+1}`** — the increment of the accelerated sequence is the trapezoidal
    residual (`g3Seq_step_eq` gives `e_{j+1}`; `half_add_self`/`resid_regroup` move the correction). -/
theorem hSeq3_step_eq (j : Nat) :
    Req (Rsub (hSeq3 (j + 1)) (hSeq3 j)) (sStep3 (j + 1) (Nat.succ_pos j)) := by
  unfold hSeq3 sStep3
  refine Req_trans (Rsub_sub_sub (g3Seq (j + 1))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
    (g3Seq j) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))) ?_
  refine Req_trans (Rsub_congr (g3Seq_step_eq j) (Req_refl _)) ?_
  -- e_{j+1} = (ln(j+2))³/(j+2) − ¼Δ; rewrite the leading `(ln(j+2))³/(j+2)` as ½·+½·
  show Req
    (Rsub (Rsub (lnCubeOver (j + 2) (Nat.succ_pos (j + 1)))
        (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
          (Rsub (logQuartic (j + 2) (Nat.succ_pos (j + 1))) (logQuartic (j + 1) (Nat.succ_pos j)))))
      (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j))))) _
  refine Req_trans (Rsub_congr
    (Rsub_congr (half_add_self (lnCubeOver (j + 2) (Nat.succ_pos (j + 1)))) (Req_refl _))
    (Req_refl _)) ?_
  exact resid_regroup (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 2) (Nat.succ_pos (j + 1))))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (lnCubeOver (j + 1) (Nat.succ_pos j)))
    (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
      (Rsub (logQuartic (j + 2) (Nat.succ_pos (j + 1))) (logQuartic (j + 1) (Nat.succ_pos j))))

-- ===========================================================================
-- (C2a) Coefficient-consolidation helpers (the rational `RMulNF` collapses for the quartic residual)
-- and the cube-binomial / W-expansion (the `a = b + δ` substitution algebra).
-- ===========================================================================

/-- **`½·(3·x) ≈ (3/2)·x`** — the coefficient collapse `½·3 = 3/2` (via `Rmul_ofQ_ofQ` then `ofQ_congr`). -/
theorem half_three (x : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x))
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) x) := by
  have hc : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨3, 1⟩ : Q) (by decide)))
      (ofQ (⟨3, 2⟩ : Q) (by decide)) :=
    Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  exact Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 2⟩ : Q) (by decide)) (ofQ (⟨3, 1⟩ : Q) (by decide)) x))
    (Rmul_congr hc (Req_refl x))

/-- **`¼·(6·x) ≈ (3/2)·x`** — the coefficient collapse `¼·6 = 3/2`. -/
theorem quarter_six (x : Real) :
    Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) x))
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) x) := by
  have hc : Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨6, 1⟩ : Q) (by decide)))
      (ofQ (⟨3, 2⟩ : Q) (by decide)) :=
    Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  exact Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨6, 1⟩ : Q) (by decide)) x))
    (Rmul_congr hc (Req_refl x))

/-- **`¼·(4·x) ≈ x`** — the coefficient collapse `¼·4 = 1`. -/
theorem quarter_four (x : Real) :
    Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) x)) x := by
  have hc : Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨4, 1⟩ : Q) (by decide))) one :=
    Req_trans (Rmul_ofQ_ofQ (by decide) (by decide)) (ofQ_congr (by decide) (by decide) (by decide))
  exact Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, 4⟩ : Q) (by decide)) (ofQ (⟨4, 1⟩ : Q) (by decide)) x))
    (Req_trans (Rmul_congr hc (Req_refl x)) (Rone_mul x))

/-- `x + x + x ≈ 3·x` (the additive-to-scalar `3` merge, `ofQ⟨3,1⟩`). -/
theorem three_merge (x : Real) :
    Req (Radd (Radd x x) x) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x) := by
  have h3 : Req (Radd (Radd one one) one) (ofQ (⟨3, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  refine Req_trans (Radd_congr (Radd_congr hx1 hx1) hx1) ?_
  refine Req_trans (Radd_congr (Req_symm (Rmul_distrib_right one one x)) (Req_refl _)) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right (Radd one one) one x)) (Rmul_congr h3 (Req_refl x))

/-- `x + x + x + x ≈ 4·x` (the additive-to-scalar `4` merge, `ofQ⟨4,1⟩`). -/
theorem four_merge (x : Real) :
    Req (Radd (Radd (Radd x x) x) x) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) x) := by
  have h4 : Req (Radd (Radd (Radd one one) one) one) (ofQ (⟨4, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr hx1 hx1) hx1) hx1) ?_
  refine Req_trans (Radd_congr (Radd_congr
    (Req_symm (Rmul_distrib_right one one x)) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Req_symm (Rmul_distrib_right (Radd one one) one x)) (Req_refl _)) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right (Radd (Radd one one) one) one x))
    (Rmul_congr h4 (Req_refl x))

/-- `2·x + x + x + x + x + x ≈ 6·x` — used to merge the six `b²d²` copies of `W`'s cross expansion into
    `6·(b²d²)` (the `¼·6 = 3/2` consolidation feeds on this). Built as `(2x+x)+x+x+x = ...`. -/
theorem six_merge (x : Real) :
    Req (Radd (Radd (Radd (Radd (Radd x x) x) x) x) x) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) x) := by
  have h6 : Req (Radd (Radd (Radd (Radd (Radd one one) one) one) one) one)
      (ofQ (⟨6, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Radd_congr (Radd_congr hx1 hx1) hx1) hx1)
    hx1) hx1) ?_
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Radd_congr
    (Req_symm (Rmul_distrib_right one one x)) (Req_refl _)) (Req_refl _)) (Req_refl _))
    (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr
    (Req_symm (Rmul_distrib_right (Radd one one) one x)) (Req_refl _)) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr
    (Req_symm (Rmul_distrib_right (Radd (Radd one one) one) one x)) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr
    (Req_symm (Rmul_distrib_right (Radd (Radd (Radd one one) one) one) one x)) (Req_refl _)) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right (Radd (Radd (Radd (Radd one one) one) one) one) one x))
    (Rmul_congr h6 (Req_refl x))

/-- `x + 3·x ≈ 4·x` (coefficient merge `1 + 3 = 4`). -/
theorem one_plus_three (x : Real) :
    Req (Radd x (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x)) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) x) := by
  have h4 : Req (Radd one (ofQ (⟨3, 1⟩ : Q) (by decide))) (ofQ (⟨4, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  refine Req_trans (Radd_congr hx1 (Req_refl _)) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right one (ofQ (⟨3, 1⟩ : Q) (by decide)) x))
    (Rmul_congr h4 (Req_refl x))

/-- `3·x + x ≈ 4·x` (coefficient merge `3 + 1 = 4`). -/
theorem three_plus_one (x : Real) :
    Req (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x) x) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) x) := by
  have h4 : Req (Radd (ofQ (⟨3, 1⟩ : Q) (by decide)) one) (ofQ (⟨4, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, one, ofQ, add, Qeq]; push_cast
  have hx1 : Req x (Rmul one x) := Req_symm (Req_trans (Rmul_comm one x) (Rmul_one x))
  refine Req_trans (Radd_congr (Req_refl _) hx1) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right (ofQ (⟨3, 1⟩ : Q) (by decide)) one x))
    (Rmul_congr h4 (Req_refl x))

/-- `3·x + 3·x ≈ 6·x` (coefficient merge `3 + 3 = 6`). -/
theorem three_plus_three (x : Real) :
    Req (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) x))
        (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) x) := by
  have h6 : Req (Radd (ofQ (⟨3, 1⟩ : Q) (by decide)) (ofQ (⟨3, 1⟩ : Q) (by decide)))
      (ofQ (⟨6, 1⟩ : Q) (by decide)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, ofQ, add, Qeq]; push_cast
  exact Req_trans (Req_symm (Rmul_distrib_right (ofQ (⟨3, 1⟩ : Q) (by decide))
    (ofQ (⟨3, 1⟩ : Q) (by decide)) x)) (Rmul_congr h6 (Req_refl x))

/-- Left-nested degree-4 flattening: `((x·y)·z)·w ≈ RprodL [x,y,z,w]`. -/
theorem Rmul_eq_RprodL4L (x y z w : Real) :
    Req (Rmul (Rmul (Rmul x y) z) w) (RprodL [x, y, z, w]) :=
  Req_trans (Rmul_congr (Rmul_eq_RprodL3 x y z) (Req_refl w))
    (Req_trans (Rmul_congr (Req_refl (RprodL [x, y, z])) (Req_symm (Rmul_one w)))
      (Req_symm (RprodL_append [x, y, z] [w])))

/-- Left-nested degree-5 flattening: `(((x·y)·z)·w)·v ≈ RprodL [x,y,z,w,v]`. -/
theorem Rmul_eq_RprodL5L (x y z w v : Real) :
    Req (Rmul (Rmul (Rmul (Rmul x y) z) w) v) (RprodL [x, y, z, w, v]) :=
  Req_trans (Rmul_congr (Rmul_eq_RprodL4L x y z w) (Req_refl v))
    (Req_trans (Rmul_congr (Req_refl (RprodL [x, y, z, w])) (Req_symm (Rmul_one v)))
      (Req_symm (RprodL_append [x, y, z, w] [v])))

/-- **Monomial normalizer `X·(c·u) → RprodL`** where `X = (x₁·x₂)·x₃` is a left-nested cube: reassociate
    `X·(c·u) ≈ ((X·c)·u)` then flatten to `RprodL [x₁,x₂,x₃,c,u]`. -/
theorem cube_times_pair (x₁ x₂ x₃ c u : Real) :
    Req (Rmul (Rmul (Rmul x₁ x₂) x₃) (Rmul c u))
        (RprodL [x₁, x₂, x₃, c, u]) :=
  Req_trans (Req_symm (Rmul_assoc (Rmul (Rmul x₁ x₂) x₃) c u))
    (Rmul_eq_RprodL5L x₁ x₂ x₃ c u)

/-- **Monomial normalizer `(x·y)·(c·(z·w)) → RprodL [x,y,c,z,w]`** (reassociate to left-nested 5). -/
theorem pair_times_triple (x y c z w : Real) :
    Req (Rmul (Rmul x y) (Rmul c (Rmul z w))) (RprodL [x, y, c, z, w]) :=
  Req_trans (Req_symm (Rmul_assoc (Rmul x y) c (Rmul z w)))
    (Req_trans (Req_symm (Rmul_assoc (Rmul (Rmul x y) c) z w))
      (Rmul_eq_RprodL5L x y c z w))

/-- **Monomial normalizer `x·((z₁·z₂)·(c·w)) → RprodL [x,z₁,z₂,c,w]`** (reassociate to left-nested 5). -/
theorem single_times_sqpair (x z₁ z₂ c w : Real) :
    Req (Rmul x (Rmul (Rmul z₁ z₂) (Rmul c w))) (RprodL [x, z₁, z₂, c, w]) :=
  Req_trans (Req_symm (Rmul_assoc x (Rmul z₁ z₂) (Rmul c w)))
    (Req_trans (Rmul_congr (Req_symm (Rmul_assoc x z₁ z₂)) (Req_refl _))
      (Req_trans (Req_symm (Rmul_assoc (Rmul (Rmul x z₁) z₂) c w))
        (Rmul_eq_RprodL5L x z₁ z₂ c w)))

set_option maxHeartbeats 8000000 in
/-- **The cube binomial** `(b+d)³ ≈ b³ + 3·(b²d) + 3·(bd²) + d³` (`b³ = (b·b)·b`, etc.; the `3`s as
    `ofQ⟨3,1⟩` factors), for the `a = b+δ` substitution in `partA`/`partC`.  Expand `(b+d)²` via
    `sq_binom2`, distribute the trailing `(b+d)`, normalize each monomial, and merge `2X + X = 3X`
    (`two_plus_one`). -/
theorem cube_binom (b d : Real) :
    Req (Rmul (Rmul (Radd b d) (Radd b d)) (Radd b d))
        (Radd (Radd (Radd (Rmul (Rmul b b) b)
                  (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
              (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
          (Rmul (Rmul d d) d)) := by
  -- (b+d)² = b² + 2(bd) + d²
  refine Req_trans (Rmul_congr (sq_binom2 b d) (Req_refl (Radd b d))) ?_
  -- distribute the trailing (b+d): X·(b+d) = X·b + X·d
  refine Req_trans (Rmul_distrib
    (Radd (Radd (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d))) (Rmul d d)) b d) ?_
  -- expand X·b and X·d into their three monomials each
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_distrib_right (Radd (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)))
        (Rmul d d) b)
      (Radd_congr (Rmul_distrib_right (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)) b)
        (Req_refl _)))
    (Req_trans (Rmul_distrib_right (Radd (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)))
        (Rmul d d) d)
      (Radd_congr (Rmul_distrib_right (Rmul b b) (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)) d)
        (Req_refl _)))) ?_
  -- now: ((b³ + (2bd)·b) + d²·b) + ((b²d + (2bd)·d) + d³)
  -- normalize the six monomials to canonical and regroup
  -- m_bbb = b³, m1 = (2bd)·b ≈ 2·(b²d), m_ddb = d²·b ≈ bd², m_bbd = b²d, m2 = (2bd)·d ≈ 2·(bd²), m_ddd = d³
  have e1 : Req (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)) b)
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) :=
    Req_trans (Rmul_assoc (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d) b)
      (Rmul_congr (Req_refl _)
        (Req_trans (Rmul_assoc b d b)
          (Req_trans (Rmul_congr (Req_refl b) (Rmul_comm d b))
            (Req_symm (Rmul_assoc b b d)))))
  have e2 : Req (Rmul (Rmul d d) b) (Rmul (Rmul b d) d) :=
    Req_trans (Rmul_comm (Rmul d d) b) (Req_symm (Rmul_assoc b d d))
  have e3 : Req (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d)) d)
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) :=
    Rmul_assoc (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul b d) d
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Req_refl _) e1) e2)
    (Radd_congr (Radd_congr (Req_refl _) e3) (Req_refl _))) ?_
  -- ((b³ + 2·b²d) + bd²) + ((b²d + 2·bd²) + d³); flatten, permute pairs adjacent, regroup, merge
  refine Req_trans (Radd_congr
    (Radd_eq_RsumL3 (Rmul (Rmul b b) b)
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)) (Rmul (Rmul b d) d))
    (Radd_eq_RsumL3 (Rmul (Rmul b b) d)
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) (Rmul (Rmul d d) d))) ?_
  refine Req_trans (Req_symm (RsumL_append
    [Rmul (Rmul b b) b, Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d), Rmul (Rmul b d) d]
    [Rmul (Rmul b b) d, Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d), Rmul (Rmul d d) d])) ?_
  refine Req_trans (RsumL_perm (List.Perm.cons (Rmul (Rmul b b) b)
    (List.Perm.cons (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      ((List.Perm.swap (Rmul (Rmul b b) d) (Rmul (Rmul b d) d)
          [Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d), Rmul (Rmul d d) d]).trans
        (List.Perm.cons (Rmul (Rmul b b) d)
          (List.Perm.swap (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
            (Rmul (Rmul b d) d) [Rmul (Rmul d d) d])))))) ?_
  -- RsumL[b³, 2b²d, b²d, 2bd², bd², d³] = Radd b³ (Radd 2b²d (Radd b²d REST))
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Rmul (Rmul b b) d)
      (Radd (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
        (Radd (Rmul (Rmul b d) d) (Radd (Rmul (Rmul d d) d) zero)))))) ?_
  refine Req_trans (Radd_congr (Req_refl _)
    (Radd_congr (two_plus_one (Rmul (Rmul b b) d)) (Req_refl _))) ?_
  -- Radd b³ (Radd 3b²d REST), REST = Radd 2bd² (Radd bd² (Radd d³ zero))
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      (Rmul (Rmul b d) d) (Radd (Rmul (Rmul d d) d) zero))))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (two_plus_one (Rmul (Rmul b d) d)) (Req_refl _)))) ?_
  -- Radd b³ (Radd 3b²d (Radd 3bd² (Radd d³ zero)))
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (Req_refl _) (Radd_zero (Rmul (Rmul d d) d))))) ?_
  -- Radd b³ (Radd 3b²d (Radd 3bd² d³)) → reassociate to ((b³ + 3b²d) + 3bd²) + d³
  refine Req_trans (Req_symm (Radd_assoc (Rmul (Rmul b b) b)
    (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) (Rmul (Rmul d d) d)))) ?_
  exact Req_symm (Radd_assoc
    (Radd (Rmul (Rmul b b) b) (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
    (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)) (Rmul (Rmul d d) d))

set_option maxHeartbeats 8000000 in
/-- **PART A** of `lhsForm3`: `½·a³·u1 → ½b³u1 + (3/2)b²δu1 + (3/2)bδ²u1 + ½δ³u1` (`a = b+δ`,
    `cube_binom`, distribute, `½·3 = 3/2` via `half_three`), as the 4 canonical monomials
    `n2, n4, n6, n8` (`δ = a − b`). -/
theorem partA3_eq (a b u1 : Real) :
    Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (Rmul (Rmul a a) a) u1))
      (Radd (Radd (Radd
          (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1])
          (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1]))
          (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1]))
          (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1])) := by
  have ha := sub_add_cancel_real a b
  -- a³ ≈ b³ + 3b²δ + 3bδ² + δ³
  have ha3 : Req (Rmul (Rmul a a) a)
      (Radd (Radd (Radd (Rmul (Rmul b b) b)
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
            (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
          (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b))) :=
    Req_trans (Rmul_congr (Rmul_congr ha ha) ha) (cube_binom b (Rsub a b))
  -- ½·(a³·u1): rewrite a³, distribute u1 then ½
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr ha3 (Req_refl u1))) ?_
  refine Req_trans (Rmul_congr (Req_refl _)
    (Req_trans (Rmul_distrib_right (Radd (Radd (Rmul (Rmul b b) b)
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
      (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) u1)
      (Radd_congr (Req_trans (Rmul_distrib_right (Radd (Rmul (Rmul b b) b)
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))) u1)
        (Radd_congr (Rmul_distrib_right (Rmul (Rmul b b) b)
          (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))) u1) (Req_refl _)))
        (Req_refl _)))) ?_
  refine Req_trans (Rmul_distrib (ofQ (⟨1, 2⟩ : Q) (by decide))
    (Radd (Radd (Rmul (Rmul (Rmul b b) b) u1)
        (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))) u1))
      (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))) u1))
    (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) u1)) ?_
  refine Req_trans (Radd_congr (Rmul_distrib (ofQ (⟨1, 2⟩ : Q) (by decide))
    (Radd (Rmul (Rmul (Rmul b b) b) u1)
      (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))) u1))
    (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))) u1))
    (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Rmul_distrib (ofQ (⟨1, 2⟩ : Q) (by decide))
    (Rmul (Rmul (Rmul b b) b) u1)
    (Rmul (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))) u1))
    (Req_refl _)) (Req_refl _)) ?_
  -- now normalize the four monomials
  refine Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_
  · exact Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L b b b u1)
  · exact Req_trans (Rmul_congr (Req_refl _)
      (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b)) u1))
      (Req_trans (half_three (Rmul (Rmul (Rmul b b) (Rsub a b)) u1))
        (Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L b b (Rsub a b) u1)))
  · exact Req_trans (Rmul_congr (Req_refl _)
      (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b)) u1))
      (Req_trans (half_three (Rmul (Rmul (Rmul b (Rsub a b)) (Rsub a b)) u1))
        (Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L b (Rsub a b) (Rsub a b) u1)))
  · exact Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L (Rsub a b) (Rsub a b) (Rsub a b) u1)

set_option maxHeartbeats 40000000 in
/-- The collect step of `W_expand` (abstract `d`): `(b³+3b²d+3bd²+d³) + (3b³+3b²d+bd²) ≈
    4b³+6b²d+4bd²+d³`.  Kept abstract in `d` so the heavy flatten/perm/merge elaborates cheaply
    (instantiated at `d = a−b` in `W_expand`). -/
theorem W_collect (b d : Real) :
    Req (Radd (Radd (Radd (Radd (Rmul (Rmul b b) b)
                  (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
              (Rmul (Rmul d d) d))
          (Radd (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
                  (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
                (Rmul (Rmul b d) d)))
        (Radd (Radd (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
                  (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
              (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
          (Rmul (Rmul d d) d)) := by
  refine Req_trans (Radd_congr
    (Req_trans (Radd_congr (Radd_eq_RsumL3 (Rmul (Rmul b b) b)
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)))
      (RsumL_singleton (Rmul (Rmul d d) d)))
      (Req_symm (RsumL_append [Rmul (Rmul b b) b,
        Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
        Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d)]
        [Rmul (Rmul d d) d])))
    (Radd_eq_RsumL3 (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Rmul (Rmul b d) d))) ?_
  refine Req_trans (Req_symm (RsumL_append
    [Rmul (Rmul b b) b, Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d),
     Rmul (Rmul d d) d]
    [Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b),
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
     Rmul (Rmul b d) d])) ?_
  -- perm to group like terms, then regroup + merge
  have s1 := List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      (List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
        (Rmul (Rmul d d) d)
        [Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
         Rmul (Rmul b d) d]))
  have s2 := List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      [Rmul (Rmul d d) d,
       Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
       Rmul (Rmul b d) d])
  have s3 := List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
    (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    [Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d),
     Rmul (Rmul d d) d,
     Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d),
     Rmul (Rmul b d) d]
  have t1 := List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
    (List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Rmul (Rmul d d) d)
      [Rmul (Rmul b d) d])
  have t2 := List.Perm.swap (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
    [Rmul (Rmul d d) d, Rmul (Rmul b d) d]
  have t3 := List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      (List.Perm.swap (Rmul (Rmul b d) d)
        (Rmul (Rmul d d) d) []))
  refine Req_trans (RsumL_perm (List.Perm.cons (Rmul (Rmul b b) b)
    ((s1.trans (s2.trans s3)).trans
      (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
        (List.Perm.cons (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
          (t1.trans (t2.trans t3))))))) ?_
  -- RsumL[b³, 3b³, 3b²δ, 3b²δ, 3bδ², bδ², δ³] → regroup + merge
  -- merge b³+3b³ = 4b³ (outermost two terms; NOT wrapped in Radd_congr)
  refine Req_trans (Req_symm (Radd_assoc (Rmul (Rmul b b) b)
    (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
    (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
        (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
          (Radd (Rmul (Rmul b d) d)
            (Radd (Rmul (Rmul d d) d) zero))))))) ?_
  refine Req_trans (Radd_congr (one_plus_three (Rmul (Rmul b b) b)) (Req_refl _)) ?_
  -- group + merge 3b²δ+3b²δ = 6b²δ
  refine Req_trans (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
      (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
        (Radd (Rmul (Rmul b d) d)
          (Radd (Rmul (Rmul d d) d) zero)))))) ?_
  refine Req_trans (Radd_congr (Req_refl _)
    (Radd_congr (three_plus_three (Rmul (Rmul b b) d)) (Req_refl _))) ?_
  -- group + merge 3bδ²+bδ² = 4bδ²
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Req_symm (Radd_assoc (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      (Rmul (Rmul b d) d)
      (Radd (Rmul (Rmul d d) d) zero))))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (three_plus_one (Rmul (Rmul b d) d)) (Req_refl _)))) ?_
  -- drop the trailing zero and reassociate to the target shape
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _)
    (Radd_congr (Req_refl _) (Radd_zero (Rmul (Rmul d d) d))))) ?_
  refine Req_trans (Req_symm (Radd_assoc (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
    (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d))
    (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
      (Rmul (Rmul d d) d)))) ?_
  exact Req_symm (Radd_assoc
    (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
      (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) d)))
    (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b d) d))
    (Rmul (Rmul d d) d))

set_option maxHeartbeats 8000000 in
/-- **W-expansion** `W = a³ + a²b + ab² + b³ ≈ 4b³ + 6b²δ + 4bδ² + δ³` (`δ = a − b`), for `partC`.
    Factored route: regroup `W = a³ + ((a²b+ab²)+b³)`; the last three terms all end in `·b` so
    `Rmul_distrib_right` (backward) factors them as `((a·a+a·b)+b·b)·b`; that inner sum is
    `inner_merge`'s `3b²+3bδ+δ²` (after `a = b+δ`); distribute `·b` → `3b³+3b²δ+bδ²`; add `cube_binom`'s
    `a³ = b³+3b²δ+3bδ²+δ³` and collect (`1+3=4`, `3+3=6`, `3+1=4`). -/
theorem W_expand (a b : Real) :
    Req (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
          (Rmul (Rmul b b) b))
        (Radd (Radd (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
                  (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
              (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
          (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b))) := by
  have ha := sub_add_cancel_real a b
  -- a³ ≈ b³ + 3b²δ + 3bδ² + δ³
  have ha3 : Req (Rmul (Rmul a a) a)
      (Radd (Radd (Radd (Rmul (Rmul b b) b)
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
            (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
          (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b))) :=
    Req_trans (Rmul_congr (Rmul_congr ha ha) ha) (cube_binom b (Rsub a b))
  -- ((a²b+ab²)+b³) ≈ ((a·a+a·b)+b·b)·b  (factor `·b` out of the three terms)
  have hfac : Req (Radd (Radd (Rmul (Rmul a a) b) (Rmul (Rmul a b) b)) (Rmul (Rmul b b) b))
      (Rmul (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b)) b) :=
    Req_trans (Radd_congr (Req_symm (Rmul_distrib_right (Rmul a a) (Rmul a b) b)) (Req_refl _))
      (Req_symm (Rmul_distrib_right (Radd (Rmul a a) (Rmul a b)) (Rmul b b) b))
  -- inner sum ≈ 3b² + 3bδ + δ²
  have hinner : Req (Radd (Radd (Rmul a a) (Rmul a b)) (Rmul b b))
      (Radd (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b (Rsub a b))))
            (Rmul (Rsub a b) (Rsub a b))) :=
    Req_trans (Radd_congr (Radd_congr (Rmul_congr ha ha) (Rmul_congr ha (Req_refl b))) (Req_refl _))
      (inner_merge b (Rsub a b))
  -- (3b²+3bδ+δ²)·b ≈ 3b³ + 3b²δ + bδ²
  have hbdb : Req (Rmul (Rmul b (Rsub a b)) b) (Rmul (Rmul b b) (Rsub a b)) :=
    Req_trans (Rmul_assoc b (Rsub a b) b)
      (Req_trans (Rmul_congr (Req_refl b) (Rmul_comm (Rsub a b) b))
        (Req_symm (Rmul_assoc b b (Rsub a b))))
  have hddb : Req (Rmul (Rmul (Rsub a b) (Rsub a b)) b) (Rmul (Rmul b (Rsub a b)) (Rsub a b)) :=
    Req_trans (Rmul_comm (Rmul (Rsub a b) (Rsub a b)) b)
      (Req_symm (Rmul_assoc b (Rsub a b) (Rsub a b)))
  have hdist : Req
      (Rmul (Radd (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))
                  (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b (Rsub a b))))
                (Rmul (Rsub a b) (Rsub a b))) b)
      (Radd (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
            (Rmul (Rmul b (Rsub a b)) (Rsub a b))) := by
    refine Req_trans (Rmul_distrib_right (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b (Rsub a b)))) (Rmul (Rsub a b) (Rsub a b)) b) ?_
    refine Radd_congr (Req_trans (Rmul_distrib_right (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b))
        (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b (Rsub a b))) b) ?_) hddb
    refine Radd_congr ?_ ?_
    · exact Req_trans (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b b) b) (Req_refl _)
    · exact Req_trans (Rmul_assoc (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul b (Rsub a b)) b)
        (Rmul_congr (Req_refl _) hbdb)
  -- assemble S2 = ((a²b+ab²)+b³) ≈ 3b³ + 3b²δ + bδ²
  have hS2 : Req (Radd (Radd (Rmul (Rmul a a) b) (Rmul (Rmul a b) b)) (Rmul (Rmul b b) b))
      (Radd (Radd (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
                (Rmul (ofQ (⟨3, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
            (Rmul (Rmul b (Rsub a b)) (Rsub a b))) :=
    Req_trans hfac (Req_trans (Rmul_congr hinner (Req_refl b)) hdist)
  -- regroup W = a³ + ((a²b+ab²)+b³)
  refine Req_trans (Req_trans (Radd_congr (Radd_assoc (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)
      (Rmul (Rmul a b) b)) (Req_refl _))
    (Radd_assoc (Rmul (Rmul a a) a) (Radd (Rmul (Rmul a a) b) (Rmul (Rmul a b) b))
      (Rmul (Rmul b b) b))) ?_
  exact Req_trans (Radd_congr ha3 hS2) (W_collect b (Rsub a b))

set_option maxHeartbeats 8000000 in
/-- **PART C** of `lhsForm3`: `¼·δ·W → b³δ + (3/2)b²δ² + bδ³ + ¼δ⁴` (`δ = a−b`, `W = a³+a²b+ab²+b³`),
    the POSITIVE monomials `n3,n5,n7,n9` (which `lhsForm3` then subtracts).  `W_expand`, distribute `δ`
    and `¼`, collapse `¼·4 = 1` (`quarter_four`) / `¼·6 = 3/2` (`quarter_six`), normalize. -/
theorem partC3_eq (a b : Real) :
    Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
          (Rmul (Rsub a b)
            (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
              (Rmul (Rmul b b) b))))
      (Radd (Radd (Radd (RprodL [b, b, b, Rsub a b])
            (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]))
          (RprodL [b, Rsub a b, Rsub a b, Rsub a b]))
        (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])) := by
  -- W ≈ 4b³+6b²δ+4bδ²+δ³
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl (Rsub a b)) (W_expand a b))) ?_
  -- distribute δ over the 4-term sum
  refine Req_trans (Rmul_congr (Req_refl _)
    (Req_trans (Rmul_distrib (Rsub a b)
        (Radd (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
            (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
          (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
        (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)))
      (Radd_congr (Req_trans (Rmul_distrib (Rsub a b)
          (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
            (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
          (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
        (Radd_congr (Rmul_distrib (Rsub a b)
          (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b))
          (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b)))) (Req_refl _)))
        (Req_refl _)))) ?_
  -- distribute ¼ over the 4-term sum
  refine Req_trans (Rmul_distrib (ofQ (⟨1, 4⟩ : Q) (by decide))
    (Radd (Radd (Rmul (Rsub a b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b)))
        (Rmul (Rsub a b) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b)))))
      (Rmul (Rsub a b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b)))))
    (Rmul (Rsub a b) (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)))) ?_
  refine Req_trans (Radd_congr (Rmul_distrib (ofQ (⟨1, 4⟩ : Q) (by decide))
    (Radd (Rmul (Rsub a b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b)))
        (Rmul (Rsub a b) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b)))))
      (Rmul (Rsub a b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b)))))
    (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Rmul_distrib (ofQ (⟨1, 4⟩ : Q) (by decide))
    (Rmul (Rsub a b) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b)))
    (Rmul (Rsub a b) (Rmul (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b)))))
    (Req_refl _)) (Req_refl _)) ?_
  -- normalize the four monomials
  refine Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_
  · exact Req_trans (Rmul_congr (Req_refl _)
      (Rmul_left_comm3 (Rsub a b) (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) b)))
      (Req_trans (quarter_four (Rmul (Rsub a b) (Rmul (Rmul b b) b)))
        (Req_trans (Rmul_comm (Rsub a b) (Rmul (Rmul b b) b))
          (Rmul_eq_RprodL4L b b b (Rsub a b))))
  · exact Req_trans (Rmul_congr (Req_refl _)
      (Rmul_left_comm3 (Rsub a b) (ofQ (⟨6, 1⟩ : Q) (by decide)) (Rmul (Rmul b b) (Rsub a b))))
      (Req_trans (quarter_six (Rmul (Rsub a b) (Rmul (Rmul b b) (Rsub a b))))
        (Rmul_congr (Req_refl _)
          (Req_trans (Rmul_comm (Rsub a b) (Rmul (Rmul b b) (Rsub a b)))
            (Rmul_eq_RprodL4L b b (Rsub a b) (Rsub a b)))))
  · exact Req_trans (Rmul_congr (Req_refl _)
      (Rmul_left_comm3 (Rsub a b) (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
      (Req_trans (quarter_four (Rmul (Rsub a b) (Rmul (Rmul b (Rsub a b)) (Rsub a b))))
        (Req_trans (Rmul_comm (Rsub a b) (Rmul (Rmul b (Rsub a b)) (Rsub a b)))
          (Rmul_eq_RprodL4L b (Rsub a b) (Rsub a b) (Rsub a b))))
  · exact Rmul_congr (Req_refl _)
      (Req_trans (Rmul_comm (Rsub a b) (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)))
        (Rmul_eq_RprodL4L (Rsub a b) (Rsub a b) (Rsub a b) (Rsub a b)))

-- ===========================================================================
-- (C2b) The quartic residual decomposition `sStep3 ≈ decompForm3 = b³·C2 + b²·R2 + b·R1 + R0`
-- (`d = a − b`, `C2 = ½(u0+u1) − d`, `R2 = (3/2)·d·(u1−d)`, `R1 = d²·((3/2)u1 − d)`,
-- `R0 = ½d³u1 − ¼d⁴`).  The keystone: `b²·R2 ≤ 0` (drops), leaving only the clean-telescoping terms.
-- ===========================================================================

/-- The **stage-1 residual form** (`sStep3` after `quartic_diff_identity`), parameterized:
    `½a³u1 + ½b³u0 − ¼·(a−b)·(a³+a²b+ab²+b³)`. -/
def lhsForm3 (a b u0 u1 : Real) : Real :=
  Rsub (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (Rmul (Rmul a a) a) u1))
             (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) u0)))
       (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
         (Rmul (Rsub a b)
           (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
             (Rmul (Rmul b b) b))))

/-- The **bound-ready decomposition** `b³·C2 + b²·R2 + b·R1 + R0` of the trapezoidal residual
    (`d = a − b`, `C2 = ½(u0+u1) − d`, `R2 = (3/2)·d·(u1−d)`, `R1 = d²·((3/2)u1 − d)`,
    `R0 = ½d³u1 − ¼d⁴`). -/
def decompForm3 (a b u0 u1 : Real) : Real :=
  Radd (Radd (Radd
      (Rmul (Rmul (Rmul b b) b)
        (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Radd u0 u1)) (Rsub a b)))
      (Rmul (Rmul b b)
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) (Rsub u1 (Rsub a b))))))
      (Rmul b
        (Rmul (Rmul (Rsub a b) (Rsub a b))
          (Rsub (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) u1) (Rsub a b)))))
    (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) u1))
          (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
            (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) (Rsub a b))))

/-- **`decompForm3` expands to its 9 canonical monomials** (coefficient-first `RprodL`, `d = a − b` an
    atom): distribute each of the four grouped terms and normalize. -/
theorem decompForm3_eq_RsumL (a b u0 u1 : Real) :
    Req (decompForm3 a b u0 u1)
      (RsumL [ RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
               RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
               Rneg (RprodL [b, b, b, Rsub a b]),
               RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
               Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
               RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
               Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b]),
               RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1],
               Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b]) ]) := by
  -- the 9 canonical monomials
  -- hP : P ≈ RsumL [n1, n2, n3]
  have hn1 : Req (Rmul (Rmul (Rmul b b) b) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) u0))
      (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0]) :=
    Req_trans (cube_times_pair b b b (ofQ (⟨1, 2⟩ : Q) (by decide)) u0)
      (RprodL_perm
        (((List.Perm.cons b (List.Perm.cons b (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [u0]))).trans
          (List.Perm.cons b (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [b, u0]))).trans
          (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [b, b, u0])))
  have hn2 : Req (Rmul (Rmul (Rmul b b) b) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) u1))
      (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1]) :=
    Req_trans (cube_times_pair b b b (ofQ (⟨1, 2⟩ : Q) (by decide)) u1)
      (RprodL_perm
        (((List.Perm.cons b (List.Perm.cons b (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [u1]))).trans
          (List.Perm.cons b (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [b, u1]))).trans
          (List.Perm.swap (ofQ (⟨1, 2⟩ : Q) (by decide)) b [b, b, u1])))
  have hPb : Req (Rmul (Rmul (Rmul b b) b) (Rsub a b)) (RprodL [b, b, b, Rsub a b]) :=
    Rmul_eq_RprodL4L b b b (Rsub a b)
  have hP : Req (Rmul (Rmul (Rmul b b) b)
        (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Radd u0 u1)) (Rsub a b)))
      (RsumL [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
              RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
              Rneg (RprodL [b, b, b, Rsub a b])]) := by
    refine Req_trans (Rmul_sub_distrib (Rmul (Rmul b b) b)
      (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Radd u0 u1)) (Rsub a b)) ?_
    refine Req_trans (Radd_congr ?_ (Rneg_congr hPb)) (Radd_eq_RsumL3 _ _ _)
    refine Req_trans (Rmul_congr (Req_refl _)
      (Rmul_distrib (ofQ (⟨1, 2⟩ : Q) (by decide)) u0 u1)) ?_
    refine Req_trans (Rmul_distrib (Rmul (Rmul b b) b)
      (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) u0) (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) u1)) ?_
    exact Radd_congr hn1 hn2
  -- hQ2 : Q2 ≈ RsumL [n4, n5]
  have hQ2a : Req (Rmul (Rmul b b)
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) u1)))
      (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1]) :=
    Req_trans (pair_times_triple b b (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rsub a b) u1)
      (RprodL_perm
        ((List.Perm.cons b (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) b [Rsub a b, u1])).trans
          (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) b [b, Rsub a b, u1])))
  have hQ2b : Req (Rmul (Rmul b b)
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) (Rsub a b))))
      (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]) :=
    Req_trans (pair_times_triple b b (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rsub a b) (Rsub a b))
      (RprodL_perm
        ((List.Perm.cons b (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) b [Rsub a b, Rsub a b])).trans
          (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) b [b, Rsub a b, Rsub a b])))
  have hQ2 : Req (Rmul (Rmul b b)
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) (Rsub u1 (Rsub a b)))))
      (RsumL [RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
              Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])]) := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _)
      (Rmul_sub_distrib (Rsub a b) u1 (Rsub a b)))) ?_
    refine Req_trans (Rmul_congr (Req_refl _)
      (Rmul_sub_distrib (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) u1)
        (Rmul (Rsub a b) (Rsub a b)))) ?_
    refine Req_trans (Rmul_sub_distrib (Rmul b b)
      (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) u1))
      (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rmul (Rsub a b) (Rsub a b)))) ?_
    exact Req_trans (Radd_congr hQ2a (Rneg_congr hQ2b)) (Radd_eq_RsumL _ _)
  -- hQ1 : Q1 ≈ RsumL [n6, n7]
  have hQ1a : Req (Rmul b (Rmul (Rmul (Rsub a b) (Rsub a b))
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) u1)))
      (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1]) :=
    Req_trans (single_times_sqpair b (Rsub a b) (Rsub a b) (ofQ (⟨3, 2⟩ : Q) (by decide)) u1)
      (RprodL_perm
        (((List.Perm.cons b (List.Perm.cons (Rsub a b)
            (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rsub a b) [u1]))).trans
          (List.Perm.cons b (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) (Rsub a b) [Rsub a b, u1]))).trans
          (List.Perm.swap (ofQ (⟨3, 2⟩ : Q) (by decide)) b [Rsub a b, Rsub a b, u1])))
  have hQ1b : Req (Rmul b (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)))
      (RprodL [b, Rsub a b, Rsub a b, Rsub a b]) :=
    Req_trans (Req_symm (Rmul_assoc b (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)))
      (Req_trans (Rmul_congr (Req_symm (Rmul_assoc b (Rsub a b) (Rsub a b))) (Req_refl _))
        (Rmul_eq_RprodL4L b (Rsub a b) (Rsub a b) (Rsub a b)))
  have hQ1 : Req (Rmul b (Rmul (Rmul (Rsub a b) (Rsub a b))
        (Rsub (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) u1) (Rsub a b))))
      (RsumL [RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
              Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])]) := by
    refine Req_trans (Rmul_congr (Req_refl _)
      (Rmul_sub_distrib (Rmul (Rsub a b) (Rsub a b))
        (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) u1) (Rsub a b))) ?_
    refine Req_trans (Rmul_sub_distrib b
      (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rmul (ofQ (⟨3, 2⟩ : Q) (by decide)) u1))
      (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b))) ?_
    exact Req_trans (Radd_congr hQ1a (Rneg_congr hQ1b)) (Radd_eq_RsumL _ _)
  -- hQ0 : Q0 ≈ RsumL [n8, n9]
  have hQ0a : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
        (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) u1))
      (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1]) :=
    Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L (Rsub a b) (Rsub a b) (Rsub a b) u1)
  have hQ0b : Req (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
        (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) (Rsub a b)))
      (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b]) :=
    Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L (Rsub a b) (Rsub a b) (Rsub a b) (Rsub a b))
  have hQ0 : Req
      (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide))
              (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) u1))
            (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
              (Rmul (Rmul (Rmul (Rsub a b) (Rsub a b)) (Rsub a b)) (Rsub a b))))
      (RsumL [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1],
              Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])]) :=
    Req_trans (Radd_congr hQ0a (Rneg_congr hQ0b)) (Radd_eq_RsumL _ _)
  -- assemble: decompForm3 = Radd(Radd(Radd P Q2)Q1)Q0
  unfold decompForm3
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr hP hQ2) hQ1) hQ0) ?_
  refine Req_trans (Radd_congr (Radd_congr (Req_symm (RsumL_append
      [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
       RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1], Rneg (RprodL [b, b, b, Rsub a b])]
      [RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
       Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])]))
      (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Req_symm (RsumL_append
      [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
       RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1], Rneg (RprodL [b, b, b, Rsub a b]),
       RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
       Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])]
      [RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
       Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])])) (Req_refl _)) ?_
  exact Req_symm (RsumL_append
    [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
     RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1], Rneg (RprodL [b, b, b, Rsub a b]),
     RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
     Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
     RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
     Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])]
    [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1],
     Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])])

set_option maxHeartbeats 8000000 in
/-- **`lhsForm3` expands to its 9 canonical monomials** in the order `[n2,n4,n6,n8,n1,n3,n5,n7,n9]`
    (partA gives `n2,n4,n6,n8`; `½b³u0 = n1`; `−partC` gives `n3,n5,n7,n9`). -/
theorem lhsForm3_eq_RsumL (a b u0 u1 : Real) :
    Req (lhsForm3 a b u0 u1)
      (RsumL [ RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
               RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
               RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
               RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1],
               RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0],
               Rneg (RprodL [b, b, b, Rsub a b]),
               Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
               Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b]),
               Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b]) ]) := by
  -- ½b³u0 ≈ n1
  have hb3u0 : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (by decide)) (Rmul (Rmul (Rmul b b) b) u0))
      (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0]) :=
    Rmul_congr (Req_refl _) (Rmul_eq_RprodL4L b b b u0)
  -- −partC ≈ [n3,n5,n7,n9]
  have hnegC : Req
      (Rneg (Rmul (ofQ (⟨1, 4⟩ : Q) (by decide))
        (Rmul (Rsub a b)
          (Radd (Radd (Radd (Rmul (Rmul a a) a) (Rmul (Rmul a a) b)) (Rmul (Rmul a b) b))
            (Rmul (Rmul b b) b)))))
      (Radd (Radd (Radd (Rneg (RprodL [b, b, b, Rsub a b]))
            (Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])))
          (Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])))
        (Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b]))) := by
    refine Req_trans (Rneg_congr (partC3_eq a b)) ?_
    refine Req_trans (Rneg_Radd (Radd (Radd (RprodL [b, b, b, Rsub a b])
        (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]))
        (RprodL [b, Rsub a b, Rsub a b, Rsub a b]))
      (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])) ?_
    refine Radd_congr ?_ (Req_refl _)
    refine Req_trans (Rneg_Radd (Radd (RprodL [b, b, b, Rsub a b])
        (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]))
      (RprodL [b, Rsub a b, Rsub a b, Rsub a b])) ?_
    exact Radd_congr (Rneg_Radd (RprodL [b, b, b, Rsub a b])
      (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])) (Req_refl _)
  -- assemble: lhsForm3 = Radd (Radd (½a³u1) (½b³u0)) (Rneg partC)
  unfold lhsForm3
  refine Req_trans (Radd_congr (Radd_congr (partA3_eq a b u1) hb3u0) hnegC) ?_
  -- flatten Radd (Radd PA n1) NC to RsumL[n2,n4,n6,n8,n1,n3,n5,n7,n9]
  -- PA = Radd(Radd(Radd n2 n4) n6) n8 → RsumL[n2,n4,n6,n8]
  have hPA : Req (Radd (Radd (Radd (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1])
        (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1]))
      (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1]))
      (RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1]))
      (RsumL [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
              RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
              RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
              RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1]]) :=
    Req_trans (Radd_congr (Radd_eq_RsumL3 _ _ _) (RsumL_singleton _))
      (Req_symm (RsumL_append
        [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
         RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
         RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1]]
        [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1]]))
  have hNC : Req (Radd (Radd (Radd (Rneg (RprodL [b, b, b, Rsub a b]))
          (Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b])))
        (Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])))
      (Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])))
      (RsumL [Rneg (RprodL [b, b, b, Rsub a b]),
              Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
              Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b]),
              Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])]) :=
    Req_trans (Radd_congr (Radd_eq_RsumL3 _ _ _) (RsumL_singleton _))
      (Req_symm (RsumL_append
        [Rneg (RprodL [b, b, b, Rsub a b]),
         Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
         Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b])]
        [Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])]))
  -- Radd (Radd PA n1) NC → Radd (RsumL[n2,n4,n6,n8,n1]) (RsumL[n3,n5,n7,n9]) → RsumL all 9
  refine Req_trans (Radd_congr (Req_trans (Radd_congr hPA (RsumL_singleton _))
    (Req_symm (RsumL_append
      [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
       RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
       RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
       RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1]]
      [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0]]))) hNC) ?_
  exact Req_symm (RsumL_append
    [RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u1],
     RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, u1],
     RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, Rsub a b, Rsub a b, u1],
     RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, u1],
     RprodL [ofQ (⟨1, 2⟩ : Q) (by decide), b, b, b, u0]]
    [Rneg (RprodL [b, b, b, Rsub a b]),
     Rneg (RprodL [ofQ (⟨3, 2⟩ : Q) (by decide), b, b, Rsub a b, Rsub a b]),
     Rneg (RprodL [b, Rsub a b, Rsub a b, Rsub a b]),
     Rneg (RprodL [ofQ (⟨1, 4⟩ : Q) (by decide), Rsub a b, Rsub a b, Rsub a b, Rsub a b])])

set_option maxHeartbeats 8000000 in
/-- **The keystone identity** `lhsForm3 ≈ decompForm3` — both expand to the same 9 canonical monomials
    (`lhsForm3_eq_RsumL` / `decompForm3_eq_RsumL`), matched by a 9-element permutation
    `[n2,n4,n6,n8,n1,n3,n5,n7,n9] ~ [n1,…,n9]` (explicit `List.Perm`, swap elements inferred). -/
theorem decomp_generic3 (a b u0 u1 : Real) :
    Req (lhsForm3 a b u0 u1) (decompForm3 a b u0 u1) := by
  refine Req_trans (lhsForm3_eq_RsumL a b u0 u1)
    (Req_trans (RsumL_perm ?_) (Req_symm (decompForm3_eq_RsumL a b u0 u1)))
  exact (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans ((List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))))).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))))).trans ((List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _))))).trans (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ _)))))))))))))))

set_option maxHeartbeats 8000000 in
/-- **`sStep3 p ≈ decompForm3`** at the log/reciprocal atoms (`a = ln(p+1)`, `b = ln p`, `u0 = 1/p`,
    `u1 = 1/(p+1)`): `sStep3` matches `lhsForm3` on the nose except the quartic difference
    `(ln(p+1))⁴ − (ln p)⁴`, which `quartic_diff_identity` rewrites to `(a−b)(a³+a²b+ab²+b³)`; then
    `decomp_generic3`. -/
theorem sStep3_decomp (p : Nat) (hp : 1 ≤ p) :
    Req (sStep3 p hp)
      (decompForm3 (logN (p + 1) (Nat.succ_pos p)) (logN p hp)
        (ofQ (⟨1, p⟩ : Q) (by show 0 < p; omega)) (ofQ (⟨1, p + 1⟩ : Q) (by show 0 < p + 1; omega))) := by
  refine Req_trans ?_ (decomp_generic3 (logN (p + 1) (Nat.succ_pos p)) (logN p hp)
    (ofQ (⟨1, p⟩ : Q) (by show 0 < p; omega)) (ofQ (⟨1, p + 1⟩ : Q) (by show 0 < p + 1; omega)))
  unfold sStep3 lhsForm3 lnCubeOver logCube logQuartic
  exact Rsub_congr (Req_refl _)
    (Rmul_congr (Req_refl _)
      (Req_symm (quartic_diff_identity (logN (p + 1) (Nat.succ_pos p)) (logN p hp))))

end UOR.Bridge.F1Square.Analysis
