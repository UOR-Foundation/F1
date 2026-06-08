/-
F1 square — **v0.15.1: toward `exp∘log = id`** (the ζ-convergence gate).

`exp(log n) = n` is the bound that makes `Σ n^{-s}` converge for `Re s > 1`. Because `log` is built
independently (`log x = 2·artanh((x−1)/(x+1))`, `Log.lean`), this is a genuine power-series composition,
not a definitional identity. This file assembles the pieces toward it. First brick: the **congruence**
`exp` respects `≈` (`RexpReal_congr`) — needed to substitute log-equalities under `exp` — and the
**reciprocal law** `exp(−y)·exp(y) ≈ 1` (`RexpReal_mul_neg`, from the keystone `RexpReal_add`).

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.ExpRealAdd
import F1Square.Analysis.ComplexExp

namespace UOR.Bridge.F1Square.Analysis

/-- **`exp` respects Bishop equality**: `x ≈ y ⇒ exp x ≈ exp y`. The two exp diagonals are reconciled
    through a common deep depth `D = Rₓ + R_y`: depth tails on each side (`expSum_trunc_bound`,
    `RexpReal_trunc_le`) and the Lipschitz middle (`expSum_Lip_le`, `LipS ≤ U`) with the argument gap
    `|xₐ − yᵦ| ≤ 4/(n+1)` (regularity `xreg_n_le` + the hypothesis `h`). -/
theorem RexpReal_congr {x y : Real} (h : Req x y) : Req (RexpReal x) (RexpReal y) := by
  refine Req_of_lin_bound
    (C := 1 + 4 * (expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat) ?_
  intro n
  show Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n)))) _
  have hRxn : n ≤ RexpReal_R x n := n_le_RexpReal_R x n
  have hRyn : n ≤ RexpReal_R y n := n_le_RexpReal_R y n
  have hxLe : Qle (Qabs (x.seq (RexpReal_R x n))) ⟨((xBound x + xBound y : Nat) : Int), 1⟩ :=
    canon_bound_le (Nat.le_add_right _ _) _
  have hyLe : Qle (Qabs (y.seq (RexpReal_R y n))) ⟨((xBound x + xBound y : Nat) : Int), 1⟩ :=
    canon_bound_le (Nat.le_add_left _ _) _
  -- piece 1: |exp(xₐ, Rₓ) − exp(xₐ, D)| ≤ 1/(2(n+1))
  have hP1 : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n)))) ⟨1, 2 * (n + 1)⟩ := by
    rw [Qabs_Qsub_comm]
    exact Qle_trans (fct_pos _)
      (expSum_trunc_bound (M := xBound x) (x.den_pos _) (canon_bound x _)
        (a := RexpReal_R x n) (b := RexpReal_R x n + RexpReal_R y n) (by unfold RexpReal_R; omega) (by omega))
      (RexpReal_trunc_le x n)
  -- piece 3: |exp(yᵦ, D) − exp(yᵦ, R_y)| ≤ 1/(2(n+1))
  have hP3 : Qle (Qabs (Qsub (expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n)))) ⟨1, 2 * (n + 1)⟩ :=
    Qle_trans (fct_pos _)
      (expSum_trunc_bound (M := xBound y) (y.den_pos _) (canon_bound y _)
        (a := RexpReal_R y n) (b := RexpReal_R x n + RexpReal_R y n) (by unfold RexpReal_R; omega) (by omega))
      (RexpReal_trunc_le y n)
  -- argument gap: |xₐ − yᵦ| ≤ 4/(n+1)
  have hh : Qle (Qabs (Qsub (x.seq (RexpReal_R y n)) (y.seq (RexpReal_R y n)))) ⟨2, n + 1⟩ :=
    Qle_trans (b := (⟨2, RexpReal_R y n + 1⟩ : Q)) (by omega : (0:Nat) < RexpReal_R y n + 1)
      (h (RexpReal_R y n)) (by simp only [Qle]; push_cast; omega)
  have hargs : Qle (Qabs (Qsub (x.seq (RexpReal_R x n)) (y.seq (RexpReal_R y n)))) ⟨4, n + 1⟩ := by
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (x.den_pos _)))
        (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (Qabs_sub_triangle (a := x.seq (RexpReal_R x n)) (b := x.seq (RexpReal_R y n))
        (c := y.seq (RexpReal_R y n)) (x.den_pos _) (x.den_pos _) (y.den_pos _)) ?_
    refine Qle_trans (add_den_pos (Nat.succ_pos n) (Nat.succ_pos n))
      (Qadd_le_add (xreg_n_le x hRxn hRyn) hh) (Qeq_le ?_)
    simp only [Qeq, add]; push_cast; ring_uor
  -- piece 2: Lipschitz middle ≤ U·4/(n+1)
  have hLip : Qle (LipS (xBound x + xBound y) (RexpReal_R x n + RexpReal_R y n))
      ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ :=
    Qle_trans (expM_U_den_pos _ _) (LipS_le_U _ _) (Qle_toNat (expM_U_num_nonneg _ _) (expM_U_den_pos _ _))
  have hP2 : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))))
      (mul ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ ⟨4, n + 1⟩) := by
    refine Qle_trans (Qmul_den_pos (LipS_den_pos _ _) (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (expSum_Lip_le (x.den_pos _) (y.den_pos _) hxLe hyLe _) ?_
    exact Qle_trans (Qmul_den_pos Nat.one_pos (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (y.den_pos _))))
      (Qmul_le_mul_right (Qabs_num_nonneg _) hLip) (Qmul_le_mul_left (Int.ofNat_nonneg _) hargs)
  -- assemble: piece1 + (piece2 + piece3)
  have h2 : 0 < 2 * (n + 1) := by omega
  have hRest : Qle (Qabs (Qsub (expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))))
      (add (mul ⟨((expM_U (xBound x + xBound y) (2 * (xBound x + xBound y))).num.toNat : Int), 1⟩ ⟨4, n + 1⟩)
        ⟨1, 2 * (n + 1)⟩) :=
    Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _))) (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (y.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _))))
      (Qabs_sub_triangle
        (a := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
        (b := expSum (y.seq (RexpReal_R y n)) (RexpReal_R x n + RexpReal_R y n))
        (c := expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))
        (expSum_den_pos (x.den_pos _) _) (expSum_den_pos (y.den_pos _) _)
        (expSum_den_pos (y.den_pos _) _)) (Qadd_le_add hP2 hP3)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (x.den_pos _) _))) (Qabs_den_pos (Qsub_den_pos (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (y.den_pos _) _))))
    (Qabs_sub_triangle
      (a := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n))
      (b := expSum (x.seq (RexpReal_R x n)) (RexpReal_R x n + RexpReal_R y n))
      (c := expSum (y.seq (RexpReal_R y n)) (RexpReal_R y n))
      (expSum_den_pos (x.den_pos _) _) (expSum_den_pos (x.den_pos _) _)
      (expSum_den_pos (y.den_pos _) _)) ?_
  refine Qle_trans (add_den_pos h2 (add_den_pos (Qmul_den_pos Nat.one_pos (Nat.succ_pos n)) h2))
    (Qadd_le_add hP1 hRest) (Qeq_le ?_)
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **The reciprocal law** `exp(−y)·exp(y) ≈ 1`: from the homomorphism keystone `RexpReal_add` at
    `(−y, y)` and `exp 0 ≈ 1`. Hence `exp(−y)` is the multiplicative inverse of `exp y`. -/
theorem RexpReal_mul_neg (y : Real) : Req (Rmul (RexpReal (Rneg y)) (RexpReal y)) one :=
  Req_trans (Req_symm (RexpReal_add (Rneg y) y))
    (Req_trans (RexpReal_congr (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y))) RexpReal_zero)

/-- The finite geometric sum `Σ_{k=0}^N wᵏ`. -/
def gPow (w : Q) : Nat → Q
  | 0 => ⟨1, 1⟩
  | (n + 1) => add (gPow w n) (qpow w (n + 1))

theorem gPow_den_pos {w : Q} (hwd : 0 < w.den) : ∀ N, 0 < (gPow w N).den
  | 0 => Nat.one_pos
  | (n + 1) => add_den_pos (gPow_den_pos hwd n) (qpow_den_pos hwd (n + 1))

theorem gPow_num_nonneg {w : Q} (hw0 : 0 ≤ w.num) : ∀ N, 0 ≤ (gPow w N).num
  | 0 => by show (0 : Int) ≤ 1; decide
  | (n + 1) => by
      show 0 ≤ (gPow w n).num * ((qpow w (n + 1)).den : Int)
          + (qpow w (n + 1)).num * ((gPow w n).den : Int)
      exact Int.add_nonneg
        (Int.mul_nonneg (gPow_num_nonneg hw0 n) (Int.ofNat_nonneg _))
        (Int.mul_nonneg (qpow_nonneg hw0 (n + 1)) (Int.ofNat_nonneg _))

/-- **The geometric telescoping closed form**: `(Σ_{k=0}^N wᵏ)·(1 − w) = 1 − w^{N+1}`. -/
theorem gPow_telescope {w : Q} (hwd : 0 < w.den) :
    ∀ N, Qeq (mul (gPow w N) (Qsub ⟨1, 1⟩ w)) (Qsub ⟨1, 1⟩ (qpow w (N + 1)))
  | 0 => by
      show Qeq (mul (⟨1, 1⟩ : Q) (Qsub ⟨1, 1⟩ w)) (Qsub ⟨1, 1⟩ (mul w ⟨1, 1⟩))
      simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  | (N + 1) => by
      show Qeq (mul (add (gPow w N) (qpow w (N + 1))) (Qsub ⟨1, 1⟩ w))
        (Qsub ⟨1, 1⟩ (mul w (qpow w (N + 1))))
      have hd1w : 0 < (Qsub (⟨1, 1⟩ : Q) w).den := Qsub_den_pos Nat.one_pos hwd
      have hqp : 0 < (qpow w (N + 1)).den := qpow_den_pos hwd (N + 1)
      have hgp : 0 < (gPow w N).den := gPow_den_pos hwd N
      have hdistrib : Qeq (mul (add (gPow w N) (qpow w (N + 1))) (Qsub ⟨1, 1⟩ w))
          (add (mul (gPow w N) (Qsub ⟨1, 1⟩ w)) (mul (qpow w (N + 1)) (Qsub ⟨1, 1⟩ w))) := by
        simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
      have hfin : Qeq (add (Qsub ⟨1, 1⟩ (qpow w (N + 1))) (mul (qpow w (N + 1)) (Qsub ⟨1, 1⟩ w)))
          (Qsub ⟨1, 1⟩ (mul w (qpow w (N + 1)))) := by
        simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
      exact Qeq_trans (add_den_pos (Qmul_den_pos hgp hd1w) (Qmul_den_pos hqp hd1w)) hdistrib
        (Qeq_trans (add_den_pos (Qsub_den_pos Nat.one_pos hqp) (Qmul_den_pos hqp hd1w))
          (Qadd_congr (gPow_telescope hwd N) (Qeq_refl _)) hfin)

end UOR.Bridge.F1Square.Analysis
