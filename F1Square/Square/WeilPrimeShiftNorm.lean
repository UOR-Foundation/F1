/-
F1 square — **the q^{-1/2} normalization bridge** (`WeilPrimeShiftNorm.lean`) for the CC (finite-place) Weil weight.

n^{-1/2} is built as √(1/n) via `RsqrtRealPos` (the below-1 square root), which lands the squaring
identity directly on `1/n = Rinv (ofQ ⟨n,1⟩)`.  We then prove the two maintainer-named identities
for the reflection-symmetric point test `h` (`h(n) = h(1/n)`):
  • reflection:      F(1/n) = n · F(n)          (weight at 1/n is √n)
  • normalization:   F(n) + n⁻¹·F(1/n) = 2·n^{-1/2}·h(n)
where F(q) = q^{-1/2}·h(q).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.SqrtRealOf
import F1Square.Analysis.RealDiv
import F1Square.Analysis.ClampedInv
import F1Square.Analysis.RlogMulPos
import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Positivity witness for the rational constant `ofQ ⟨n,1⟩` (needed by `Rinv`).
-- ===========================================================================

/-- `ofQ ⟨n,1⟩` (for `n ≥ 1`) is positive at index `1`: `Qbound 1 = 1/2 < n`. -/
theorem ofQn_wit (n : Nat) (hn : 1 ≤ n) :
    Qlt (Qbound 1) ((ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos).seq 1) := by
  apply ge1_pos_witness
  show Qle (⟨1, 1⟩ : Q) (⟨(n : Int), 1⟩ : Q)
  show (1 : Int) * ((1 : Nat) : Int) ≤ (n : Int) * ((1 : Nat) : Int)
  have hn' : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
  omega

-- ===========================================================================
-- (1)  qInvSqrt = n^{-1/2} = √(1/n), with (n^{-1/2})² = 1/n.
-- ===========================================================================

/-- The scale hypothesis `1 ≤ n²·(1/n)` needed to root `1/n` below `1`.  `n²·(1/n) = n ≥ 1`. -/
theorem qInvSqrt_scale (n : Nat) (hn : 1 ≤ n) :
    Rle one (Rmul (ofQ (⟨(n : Int) * (n : Int), 1⟩ : Q) Nat.one_pos)
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))) := by
  -- n²·(1/n) ≈ n
  have hPmul : Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
      (ofQ (⟨(n : Int) * (n : Int), 1⟩ : Q) Nat.one_pos) :=
    Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos
  have hEq : Req (Rmul (ofQ (⟨(n : Int) * (n : Int), 1⟩ : Q) Nat.one_pos)
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn)))
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) := by
    refine Req_trans (Rmul_congr (Req_symm hPmul)
      (Req_refl (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn)))) ?_
    refine Req_trans (Rmul_assoc (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_Rinv_self (ofQn_wit n hn))) ?_
    exact Rmul_one _
  have hone : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) := by
    have hle : Qle (⟨1, 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) := by
      show (1 : Int) * ((1 : Nat) : Int) ≤ (n : Int) * ((1 : Nat) : Int)
      have hn' : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
      omega
    exact Rle_ofQ_ofQ (by decide) Nat.one_pos hle
  exact Rle_trans hone (Rle_of_Req (Req_symm hEq))

/-- **`n^{-1/2}`** as the constructive real `√(1/n)` (`RsqrtRealPos` of `1/n = Rinv (ofQ ⟨n,1⟩)`). -/
def qInvSqrt (n : Nat) (hn : 1 ≤ n) : Real :=
  RsqrtRealPos (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
    n (by omega) (qInvSqrt_scale n hn)

/-- **`(n^{-1/2})² = 1/n`** — the squaring identity lands exactly on `Rinv (ofQ ⟨n,1⟩)`. -/
theorem qInvSqrt_sq (n : Nat) (hn : 1 ≤ n) :
    Req (Rmul (qInvSqrt n hn) (qInvSqrt n hn))
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn)) :=
  RsqrtRealPos_sq (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
    n (by omega) (qInvSqrt_scale n hn)

/-- `n^{-1/2} ≥ 0`. -/
theorem qInvSqrt_nonneg (n : Nat) (hn : 1 ≤ n) : Rnonneg (qInvSqrt n hn) :=
  RsqrtRealPos_nonneg (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
    n (by omega) (qInvSqrt_scale n hn)

-- ===========================================================================
-- The bridge lemma  n · n^{-1/2} = √n.
-- ===========================================================================

/-- **`n · n^{-1/2} = √n`** — the weight at `1/n` (namely `(1/n)^{-1/2} = √n`) equals `n · n^{-1/2}`.
    Proved by uniqueness of the non-negative square root: `y = n·n^{-1/2}` has `y² = n²·(1/n) = n`. -/
theorem n_mul_qInvSqrt (n : Nat) (hn : 1 ≤ n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) :
    Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn))
      (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1) := by
  have hy : Rnonneg (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn)) :=
    Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (show (0 : Int) ≤ (n : Int) by exact_mod_cast Nat.zero_le n))
      (qInvSqrt_nonneg n hn)
  have hsq : Req (Rmul (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn))
      (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn)))
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) := by
    refine Req_trans (Rmul_mul_mul_comm (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn)
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) (qInvSqrt n hn)) ?_
    refine Req_trans (Rmul_congr (Req_refl (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))) (qInvSqrt_sq n hn)) ?_
    refine Req_trans (Rmul_assoc (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))) ?_
    refine Req_trans (Rmul_congr (Req_refl (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
      (Rmul_Rinv_self (ofQn_wit n hn))) ?_
    exact Rmul_one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
  exact RsqrtReal_unique (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1 hy hsq

-- ===========================================================================
-- (2)  The two normalization identities for a reflection-symmetric point test.
--       F(q) := q^{-1/2}·h(q);  weight at 1/n is √n = (1/n)^{-1/2}.
-- ===========================================================================

/-- **Reflection identity**: `F(1/n) = n · F(n)` for `h(n) = h(1/n)`.
    `Finv := √n·h(1/n)` and `Fn := n^{-1/2}·h(n)`. -/
theorem F_reflect (n : Nat) (hn : 1 ≤ n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
    (h : Q → Real) (hsym : Req (h (⟨(n : Int), 1⟩ : Q)) (h (⟨1, n⟩ : Q))) :
    Req (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1) (h (⟨1, n⟩ : Q)))
      (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
        (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))) := by
  -- n·Fn ≈ (n·n^{-1/2})·h(n) ≈ √n·h(n) ≈ √n·h(1/n) = Finv
  have hchain : Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q))))
      (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1) (h (⟨1, n⟩ : Q))) := by
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))) ?_
    refine Req_trans (Rmul_congr (n_mul_qInvSqrt n hn han1) (Req_refl (h (⟨(n : Int), 1⟩ : Q)))) ?_
    exact Rmul_congr (Req_refl (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1)) hsym
  exact Req_symm hchain

/-- **Normalization identity**: `F(n) + n⁻¹·F(1/n) = 2·n^{-1/2}·h(n)` for `h(n) = h(1/n)`.
    The correctly-normalized symmetric weight: the unsymmetrized CC term `Fn` plus its `n⁻¹`-scaled
    reflection collapses to twice the point value against the genuine `n^{-1/2}` weight. -/
theorem F_normalization (n : Nat) (hn : 1 ≤ n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
    (h : Q → Real) (hsym : Req (h (⟨(n : Int), 1⟩ : Q)) (h (⟨1, n⟩ : Q))) :
    Req
      (Radd (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))
        (Rmul (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
          (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1) (h (⟨1, n⟩ : Q)))))
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))) := by
  -- n⁻¹·Finv ≈ n⁻¹·(n·Fn) ≈ (n⁻¹·n)·Fn ≈ 1·Fn ≈ Fn
  have hstep : Req (Rmul (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
      (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1) (h (⟨1, n⟩ : Q))))
      (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q))) := by
    refine Req_trans (Rmul_congr (Req_refl (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1
      (ofQn_wit n hn))) (F_reflect n hn han1 h hsym)) ?_
    refine Req_trans (Req_symm (Rmul_assoc
      (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
      (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
      (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q))))) ?_
    have hRN : Req (Rmul (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
        (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) one :=
      Req_trans (Rmul_comm (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn))
        (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) (Rmul_Rinv_self (ofQn_wit n hn))
    refine Req_trans (Rmul_congr hRN (Req_refl (Rmul (qInvSqrt n hn)
      (h (⟨(n : Int), 1⟩ : Q))))) ?_
    exact Rone_mul (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))
  refine Req_trans (Radd_congr (Req_refl (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q)))) hstep) ?_
  exact Req_symm (Rmul_two_eq_add (Rmul (qInvSqrt n hn) (h (⟨(n : Int), 1⟩ : Q))))

end UOR.Bridge.F1Square.Square
