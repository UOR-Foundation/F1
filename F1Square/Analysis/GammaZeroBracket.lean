/-
F1 square — v0.22.0 crux frontier: **tightening the Euler–Mascheroni constant `γ`** toward the
`[0.577, 0.578]` bracket the `Pos Rlambda3` (`λ₃`) certificate needs (the dominant constant blocker —
the loose `γ ∈ [0.54, 0.66]` alone keeps `λ₃`'s certified lower bound negative via `−3γ²`).

`γ = Σ_{n≥0} cApprox n ∞`, `cApprox n ∞ = 1/(n+1) − 2·artanh(1/(2n+3))` (the accelerated γ-series term,
`GammaAccel.lean`). The per-term tight rational bracket reuses `GammaOne`'s artanh tail machinery at
`p = n+1` (the term's artanh argument `1/(2n+3) = 1/(2(n+1)+1)`):

  • **lower** `cApprox n T' ≥ cLowQ T n := 1/(n+1) − dPlusQ T (n+1)`  (`dPlusQ` over-estimates `2·artanh`,
    so this under-estimates the term — uniformly in the evaluation depth `T'`, since `artSum` at any
    depth is `≤ artanh ≤ dPlusQ`).

THIS FILE — part (A): the per-term lower bound `cApprox_ge_cLowQ`. The rounded accumulator over `K`
terms, the uniform tail correction `Σ_{n≥K} cApprox n ∞ ≥ 1/(2(K+1))`, and the `Rgamma_h` assembly
follow (mirroring the `GammaOneBracket`/`lnSumLo` pattern).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaAccel
import F1Square.Analysis.GammaOne

namespace UOR.Bridge.F1Square.Analysis

/-- The **per-term rational lower bound** for the accelerated γ-series term: `1/(n+1) − dPlusQ T (n+1)`
    (`dPlusQ T (n+1)` over-estimates `2·artanh(1/(2n+3))`). -/
def cLowQ (T n : Nat) : Q := Qsub (⟨1, n + 1⟩ : Q) (dPlusQ T (n + 1))

theorem cLowQ_den_pos (T n : Nat) : 0 < (cLowQ T n).den :=
  Qsub_den_pos (Nat.succ_pos n) (dPlusQ_den_pos T (n + 1) (Nat.succ_pos n))

/-- **`cLowQ T n ≤ cApprox n T'`** for every evaluation depth `T'` — the term `cApprox n T'`
    (`= 1/(n+1) − 2·artSum(1/(2n+3), T')`) under-estimated by `cLowQ`, since
    `2·artSum(…, T') ≤ 2·artSum(…, T) + 2·tail = dPlusQ T (n+1)` (`artSum_le_value` + `deltaTail_eq`). -/
theorem cApprox_ge_cLowQ (T n T' : Nat) : Qle (cLowQ T n) (cApprox n T') := by
  -- `2n+3 = 2(n+1)+1` (so `cApprox`'s artanh argument matches `dPlusQ (n+1)`'s)
  have harg : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
  unfold cLowQ cApprox dPlusQ
  rw [harg]
  refine Qadd_le_add (Qle_refl _) (Qneg_le_neg (Qmul_le_mul_left (by decide) ?_))
  -- artSum(1/(2(n+1)+1), T') ≤ artSum(1/(2(n+1)+1), T) + tail
  have htaild : 0 < (⟨1, npow (2 * (n + 1) + 1) (2 * T + 1) * (4 * (n + 1) * ((n + 1) + 1))⟩ : Q).den :=
    Nat.mul_pos (npow_pos (Nat.succ_pos _) _)
      (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos n)) (Nat.succ_pos (n + 1)))
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul (⟨1, 2 * (n + 1) + 1⟩ : Q) ⟨1, 2 * (n + 1) + 1⟩)).num := by
    show 0 < (add (⟨1, 1⟩ : Q) (neg (mul ⟨1, 2 * (n + 1) + 1⟩ ⟨1, 2 * (n + 1) + 1⟩))).num
    simp only [add, neg, mul]
    have h9 : ((9 : Nat) : Int)
        ≤ (((2 * (n + 1) + 1) * (2 * (n + 1) + 1) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul (show 3 ≤ 2 * (n + 1) + 1 by omega) (show 3 ≤ 2 * (n + 1) + 1 by omega)
    push_cast at h9 ⊢; omega
  exact artSum_le_value (by show (0 : Int) ≤ 1; decide) (Nat.succ_pos _) htaild hWn T
    (deltaTail_eq (n + 1) T) T'

-- ===========================================================================
-- (B) The rounded accumulator and the partial-sum lower bound `gammaLoBound ≤ Ssum cLowQ ≤ gammaHseq`.
-- ===========================================================================

/-- The **rounded lower-bound accumulator** for `Σ_{n<K} cLowQ T n`, at fixed denominator `D`
    (round down each step, keeping the denominator bounded for a feasible final `decide`). -/
def gammaLoBound (T D : Nat) : Nat → Q
  | 0 => ⟨0, D⟩
  | (K + 1) => qRoundDown (add (gammaLoBound T D K) (cLowQ T K)) D

theorem gammaLoBound_den_pos (T D : Nat) (hD : 0 < D) : ∀ K, 0 < (gammaLoBound T D K).den
  | 0 => hD
  | (_ + 1) => hD

/-- **`gammaLoBound T D K ≤ Σ_{n<K} cLowQ T n`** — the round-down accumulator stays below the exact
    partial sum (`qRoundDown_le` at each step). -/
theorem gammaLoBound_le_Ssum (T D : Nat) (hD : 0 < D) :
    ∀ K, Qle (gammaLoBound T D K) (Ssum (cLowQ T) K)
  | 0 => by
      show Qle (⟨0, D⟩ : Q) (⟨0, 1⟩ : Q); simp only [Qle]; omega
  | (K + 1) => by
      have hadd : 0 < (add (gammaLoBound T D K) (cLowQ T K)).den :=
        add_den_pos (gammaLoBound_den_pos T D hD K) (cLowQ_den_pos T K)
      refine Qle_trans hadd
        (qRoundDown_le (add (gammaLoBound T D K) (cLowQ T K)) hadd D) ?_
      show Qle (add (gammaLoBound T D K) (cLowQ T K)) (add (Ssum (cLowQ T) K) (cLowQ T K))
      exact Qadd_le_add (gammaLoBound_le_Ssum T D hD K) (Qle_refl _)

/-- **`Σ_{n<K} cLowQ T n ≤ gammaHseq j`** for `K ≤ 2(j+1)` — the partial sum of per-term lower bounds
    is dominated by the (longer, deeper) accelerated approximant `gammaHseq j` (`Ssum_le_of_le` with
    `cApprox_ge_cLowQ`, then `Ssum_le` to extend the upper limit; `cApprox` terms are `≥ 0`). -/
theorem Ssum_cLowQ_le_gammaHseq (T j K : Nat) (hK : K ≤ 2 * (j + 1)) :
    Qle (Ssum (cLowQ T) K) (gammaHseq j) := by
  refine Qle_trans (Ssum_den_pos (fun i => cApprox_den_pos i (j + 1)) K)
    (Ssum_le_of_le (fun i => cApprox_ge_cLowQ T i (j + 1)) K) ?_
  show Qle (Ssum (fun i => cApprox i (j + 1)) K) (Ssum (fun i => cApprox i (j + 1)) (gammaHN j))
  exact Ssum_le (fun i => cApprox_num_nonneg i (j + 1)) (fun i => cApprox_den_pos i (j + 1))
    (by unfold gammaHN; omega)

end UOR.Bridge.F1Square.Analysis
