/-
F1 square — v0.22.0 crux frontier: **`Pos Rlambda4`** (the `n = 4` prime–archimedean coupling
coefficient), the next rung beyond `Pos Rlambda3`.

Assembled from the three tightened constant brackets — `γ₁ ≤ −0.0677` (`Rgamma1_le_neg0677`),
`γ₂ ≤ 1/40` (`Rgamma2_le`), `γ₃ ≤ 1/8` (`Rgamma3_le`) — together with `γ ∈ [0.577,0.578]`,
`γ₂ ≥ −0.02`, `ζ(2) ≥ 1.644`, `ζ(3) ≤ 1.217`, `ζ(4) ≥ 1.082`, `log 4π ≤ 2.5316`.

`λ₄ = λ₄^{arith} + λ₄^{∞}`, `λ₄^{arith} = −(4η₀ + 6η₁ + 4η₂ + η₃)`,
`η₃ = γ⁴ + 4γ²γ₁ + 2γ₁² + 2γγ₂ + (2/3)γ₃`. The η-anchor uppers give `λ₄^{arith} ≥ ≈ +1.0897` and the
archimedean lower (`arch(4) = 1 − 2(γ+log4π) + (9/2)ζ(2) − (7/2)ζ(3) + (15/16)ζ(4)`) gives
`λ₄^{∞} ≥ ≈ −1.0663`, so `λ₄ ≥ ≈ +0.023` (true `λ₄ ≈ 0.370`).  This is `n = 4` ONLY — NOT the crux
(the uniform `∀ n` = RH); `liPositivityHolds` stays `none`, RH open.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.GammaTwoUpper
import F1Square.Analysis.LambdaThreePos
import F1Square.Analysis.LambdaFour

namespace UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

-- ===========================================================================
-- (P) The `η₃` product UPPER bounds.
-- ===========================================================================

/-- `ofQ q ≤ 0` when `q.num ≤ 0`. -/
theorem ofQ_nonpos {q : Q} (hd : 0 < q.den) (hn : q.num ≤ 0) : Rle (ofQ q hd) zero := by
  refine Rle_of_Rnonneg_Rsub (Rnonneg_congr ?_
    (Rnonneg_ofQ (c := neg q) hd (by show (0 : Int) ≤ -q.num; omega)))
  exact Req_symm (Req_trans (Req_trans (Radd_comm zero (Rneg (ofQ q hd))) (Radd_zero _))
    (Rneg_ofQ q hd))

/-- `b·c ≤ a·c` when `a ≤ b` and `c ≤ 0` (antitone in mult by a nonpositive factor). -/
theorem Rmul_le_Rmul_right_nonpos {a b c : Real} (hab : Rle a b) (hc : Rle c zero) :
    Rle (Rmul b c) (Rmul a c) := by
  have hcn : Rnonneg (Rneg c) :=
    Rnonneg_congr (Req_trans (Radd_comm zero (Rneg c)) (Radd_zero (Rneg c)))
      (Rnonneg_Rsub_of_Rle hc)
  have h := Rmul_le_Rmul_right hcn hab
  have h' : Rle (Rneg (Rmul a c)) (Rneg (Rmul b c)) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_right a c)))
      (Rle_trans h (Rle_of_Req (Rmul_neg_right b c)))
  exact Rle_trans (Rle_of_Req (Req_symm (Rneg_neg (Rmul b c))))
    (Rle_trans (Rle_Rneg h') (Rle_of_Req (Rneg_neg (Rmul a c))))

/-- **`γ⁴ ≤ (578/1000)⁴`** — `γ⁴ = ((γ·γ)·γ)·γ`, four `≤ γ_hi` steps. -/
theorem Rgamma_pow4_le :
    Rle (Rmul (Rmul (Rmul Rgamma_h Rgamma_h) Rgamma_h) Rgamma_h)
      (ofQ (mul (mul (mul (⟨578, 1000⟩ : Q) (⟨578, 1000⟩ : Q)) (⟨578, 1000⟩ : Q)) (⟨578, 1000⟩ : Q))
        (by decide)) := by
  have hcube : Rle (Rmul (Rmul Rgamma_h Rgamma_h) Rgamma_h)
      (ofQ (mul (mul (⟨578, 1000⟩ : Q) (⟨578, 1000⟩ : Q)) (⟨578, 1000⟩ : Q)) (by decide)) := by
    refine Rle_trans (Rmul_le_Rmul_right Rgamma_h_nonneg Rgamma_sq_le) ?_
    refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) Rgamma_h_le_578) ?_
    exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (by decide))
  refine Rle_trans (Rmul_le_Rmul_right Rgamma_h_nonneg hcube) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) Rgamma_h_le_578) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (by decide))

/-- **`γ²·γ₁ ≤ (577/1000)²·(−677/10000)`** — sharp upper (`γ² ≥ γ_lo²`, `γ₁ ≤ 0`, `γ₁ ≤ γ₁_hi`). -/
theorem Rgamma_sq_gamma1_le :
    Rle (Rmul (Rmul Rgamma_h Rgamma_h) Rgamma1)
      (ofQ (mul (mul (⟨577, 1000⟩ : Q) (⟨577, 1000⟩ : Q)) (⟨-677, 10000⟩ : Q)) (by decide)) := by
  have hg1nonpos : Rle Rgamma1 zero :=
    Rle_trans Rgamma1_le_neg0677 (ofQ_nonpos (by decide) (by decide))
  -- γ²·γ₁ ≤ γ_lo²·γ₁
  refine Rle_trans (Rmul_le_Rmul_right_nonpos Rgamma_sq_ge hg1nonpos) ?_
  -- γ_lo²·γ₁ ≤ γ_lo²·γ₁_hi
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) Rgamma1_le_neg0677) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (by decide))

/-- **`γ₁² ≤ (762/10000)²`** — `|γ₁| ≤ 762/10000` (`Rmul_le_mul_of_abs`). -/
theorem Rgamma1_sq_le :
    Rle (Rmul Rgamma1 Rgamma1) (ofQ (mul (⟨762, 10000⟩ : Q) (⟨762, 10000⟩ : Q)) (by decide)) := by
  have hlo : Rle (Rneg (ofQ (⟨762, 10000⟩ : Q) (by decide))) Rgamma1 :=
    Rle_trans (Rle_of_Req (Rneg_ofQ (⟨762, 10000⟩ : Q) (by decide))) Rgamma1_ge_neg0762
  have hhi : Rle Rgamma1 (ofQ (⟨762, 10000⟩ : Q) (by decide)) :=
    Rle_trans Rgamma1_le_neg0677 (Rle_ofQ_ofQ (by decide) (by decide) (by decide))
  exact Rle_trans (Rmul_le_mul_of_abs hlo hhi hlo hhi)
    (Rle_of_Req (Rmul_ofQ_ofQ (by decide) (by decide)))

/-- **`γ·γ₂ ≤ (578/1000)·(1/40)`** — `γ₂ ≤ 1/40`, `γ ≤ γ_hi`, both `≥ 0`. -/
theorem Rgamma_gamma2_le :
    Rle (Rmul Rgamma_h Rgamma2) (ofQ (mul (⟨578, 1000⟩ : Q) (⟨1, 40⟩ : Q)) (by decide)) := by
  refine Rle_trans (Rmul_le_Rmul_left Rgamma_h_nonneg Rgamma2_le) ?_
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ (by decide) (by decide)) Rgamma_h_le_578) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (by decide))

end UOR.Bridge.F1Square.Analysis
