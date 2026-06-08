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

/-- `0 + a ≈ a`. -/
theorem Qzero_add (a : Q) : Qeq (add ⟨0, 1⟩ a) a := by simp only [Qeq, add]; push_cast; ring_uor

/-- Commutativity of `ℚ` addition (up to `≈`). -/
theorem Qadd_comm (a b : Q) : Qeq (add a b) (add b a) := by simp only [Qeq, add]; push_cast; ring_uor

/-- Commutativity of `ℚ` multiplication (up to `≈`). -/
theorem Qmul_comm (a b : Q) : Qeq (mul a b) (mul b a) := by simp only [Qeq, mul]; push_cast; ring_uor

/-- Associativity of `ℚ` multiplication (up to `≈`). -/
theorem Qmul_assoc (a b c : Q) : Qeq (mul (mul a b) c) (mul a (mul b c)) := by
  simp only [Qeq, mul]; push_cast; ring_uor

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

-- ===========================================================================
-- Formal power series calculus (coefficient sequences `Nat → Q`), toward the
-- chain rule `(exp∘a)' = a'·(exp∘a)` that pins exp(2·artanh w) = (1+w)/(1−w).
-- ===========================================================================

/-- The **formal derivative** of a power series: `(c')ₖ = (k+1)·c_{k+1}`. -/
def fderiv (c : Nat → Q) (k : Nat) : Q := mul ⟨(k + 1 : Int), 1⟩ (c (k + 1))

/-- The **formal (Cauchy) product** of two power series: `(a·b)ₖ = Σ_{i≤k} aᵢ·b_{k−i}`. -/
def fmul (a b : Nat → Q) (k : Nat) : Q := Fsum (fun i => mul (a i) (b (k - i))) k

theorem fderiv_den_pos {c : Nat → Q} (hc : ∀ i, 0 < (c i).den) (k : Nat) : 0 < (fderiv c k).den :=
  Qmul_den_pos Nat.one_pos (hc (k + 1))

theorem fmul_den_pos {a b : Nat → Q} (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    0 < (fmul a b k).den := Fsum_den_pos (fun i => Qmul_den_pos (ha i) (hb (k - i))) k

/-- **The Leibniz product rule for formal power series**: `(a·b)' = a'·b + a·b'`. -/
theorem fderiv_fmul (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fderiv (fmul a b) k) (add (fmul (fderiv a) b k) (fmul a (fderiv b) k)) := by
  have hT : ∀ i, 0 < (mul (a i) (b (k + 1 - i))).den := fun i => Qmul_den_pos (ha i) (hb _)
  have hTL : ∀ i, 0 < (mul (⟨((i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  have hTR : ∀ i, 0 < (mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  have hTk1 : ∀ i, 0 < (mul (⟨(k + 1 : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))).den :=
    fun i => Qmul_den_pos Nat.one_pos (hT i)
  -- left factor sum  Σ_{i≤k+1} i·(aᵢ b_{k+1−i})  =  a'·b at k
  have hLeft : Qeq (Fsum (fun i => mul (⟨((i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) (k + 1))
      (fmul (fderiv a) b k) := by
    refine Qeq_trans (add_den_pos (hTL 0) (Fsum_den_pos (fun i => hTL (i + 1)) k)) (Fsum_front hTL k) ?_
    refine Qeq_trans (add_den_pos Nat.one_pos (fmul_den_pos (fun i => fderiv_den_pos ha i) hb k)) (Qadd_congr
        (show Qeq (mul (⟨((0 : Nat) : Int), 1⟩ : Q) (mul (a 0) (b (k + 1 - 0)))) (⟨0, 1⟩ : Q) by
          simp only [Qeq, mul]; push_cast; ring_uor)
        (Fsum_congr_le (fun i _ =>
          show Qeq (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (mul (a (i + 1)) (b (k + 1 - (i + 1)))))
              (mul (fderiv a i) (b (k - i))) by
            show Qeq (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (mul (a (i + 1)) (b (k + 1 - (i + 1)))))
              (mul (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) (a (i + 1))) (b (k - i)))
            rw [Nat.succ_sub_succ]; simp only [Qeq, mul]; push_cast; ring_uor))) ?_
    exact Qzero_add (fmul (fderiv a) b k)
  -- right factor sum  Σ_{i≤k+1} (k+1−i)·(aᵢ b_{k+1−i})  =  a·b' at k
  have hRight : Qeq (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) (k + 1))
      (fmul a (fderiv b) k) := by
    show Qeq (add (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) k)
        (mul (⟨((k + 1 - (k + 1) : Nat) : Int), 1⟩ : Q) (mul (a (k + 1)) (b (k + 1 - (k + 1))))))
      (fmul a (fderiv b) k)
    refine Qeq_trans (add_den_pos (Fsum_den_pos hTR k) Nat.one_pos) (Qadd_congr (Qeq_refl _)
        (show Qeq (mul (⟨((k + 1 - (k + 1) : Nat) : Int), 1⟩ : Q) (mul (a (k + 1)) (b (k + 1 - (k + 1))))) (⟨0, 1⟩ : Q) by
          rw [Nat.sub_self]; simp only [Qeq, mul]; push_cast; ring_uor)) ?_
    refine Qeq_trans (Fsum_den_pos hTR k) (Qadd_zero_right
        (Fsum (fun i => mul (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q) (mul (a i) (b (k + 1 - i)))) k)) ?_
    refine Fsum_congr_le (fun i hi => ?_)
    have hidx : k + 1 - i = (k - i) + 1 := by omega
    rw [hidx]
    show Qeq (mul (⟨(((k - i) + 1 : Nat) : Int), 1⟩ : Q) (mul (a i) (b ((k - i) + 1))))
      (mul (a i) (mul (⟨((k - i : Nat) : Int) + 1, 1⟩ : Q) (b ((k - i) + 1))))
    simp only [Qeq, mul]; push_cast; ring_uor
  -- assemble: (k+1)·Σ T = Σ (i + (k+1−i))·T = hLeft + hRight
  show Qeq (mul (⟨(k + 1 : Int), 1⟩ : Q) (Fsum (fun i => mul (a i) (b (k + 1 - i))) (k + 1)))
    (add (fmul (fderiv a) b k) (fmul a (fderiv b) k))
  refine Qeq_trans (Fsum_den_pos hTk1 (k + 1))
    (Qeq_symm (Fsum_mul_left (c := (⟨(k + 1 : Int), 1⟩ : Q)) Nat.one_pos hT (k + 1))) ?_
  refine Qeq_trans (Fsum_den_pos (fun i => add_den_pos (hTL i) (hTR i)) (k + 1))
    (Fsum_congr_le (k := k + 1) (fun i hi => by
      have hcoef : Qeq (add (⟨((i : Nat) : Int), 1⟩ : Q) (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q))
          (⟨(k + 1 : Int), 1⟩ : Q) := by simp only [Qeq, add]; push_cast; omega
      exact Qeq_trans (Qmul_den_pos (add_den_pos Nat.one_pos Nat.one_pos) (hT i))
        (Qmul_congr (Qeq_symm hcoef) (Qeq_refl (mul (a i) (b (k + 1 - i)))))
        (Qmul_add_right (⟨((i : Nat) : Int), 1⟩ : Q) (⟨((k + 1 - i : Nat) : Int), 1⟩ : Q)
          (mul (a i) (b (k + 1 - i)))))) ?_
  refine Qeq_trans (add_den_pos (Fsum_den_pos hTL (k + 1)) (Fsum_den_pos hTR (k + 1)))
    (Fsum_add hTL hTR (k + 1)) ?_
  exact Qadd_congr hLeft hRight

/-- **Sum reversal**: `Σ_{i=0}^{k} fᵢ ≈ Σ_{i=0}^{k} f_{k−i}`. -/
theorem Fsum_reverse {f : Nat → Q} (hf : ∀ i, 0 < (f i).den) :
    ∀ k, Qeq (Fsum f k) (Fsum (fun i => f (k - i)) k)
  | 0 => Qeq_refl _
  | (k + 1) => by
      have hrev := Fsum_reverse hf k
      have hRHS : Qeq (Fsum (fun i => f (k + 1 - i)) (k + 1))
          (add (f (k + 1)) (Fsum (fun i => f (k - i)) k)) := by
        refine Qeq_trans (add_den_pos (hf (k + 1 - 0)) (Fsum_den_pos (fun i => hf (k + 1 - (i + 1))) k))
          (Fsum_front (fun i => hf (k + 1 - i)) k) (Qadd_congr (Qeq_refl _)
          (Fsum_congr_le (fun i hi => ?_)))
        have hidx : k + 1 - (i + 1) = k - i := by omega
        rw [hidx]; exact Qeq_refl _
      exact Qeq_trans (add_den_pos (hf (k + 1)) (Fsum_den_pos (fun i => hf (k - i)) k))
        (Qeq_trans (add_den_pos (hf (k + 1)) (Fsum_den_pos hf k))
          (Qadd_comm (Fsum f k) (f (k + 1))) (Qadd_congr (Qeq_refl _) hrev))
        (Qeq_symm hRHS)

/-- **Commutativity of the formal Cauchy product**: `a·b ≈ b·a`. -/
theorem fmul_comm (a b : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den) (k : Nat) :
    Qeq (fmul a b k) (fmul b a k) := by
  show Qeq (Fsum (fun i => mul (a i) (b (k - i))) k) (Fsum (fun i => mul (b i) (a (k - i))) k)
  refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (ha (k - i)) (hb (k - (k - i)))) k)
    (Fsum_reverse (fun i => Qmul_den_pos (ha i) (hb (k - i))) k)
    (Fsum_congr_le (fun i hi => ?_))
  have hidx : k - (k - i) = i := by omega
  show Qeq (mul (a (k - i)) (b (k - (k - i)))) (mul (b i) (a (k - i)))
  rw [hidx]
  exact Qmul_comm (a (k - i)) (b i)

/-- **Associativity of the formal Cauchy product**: `(a·b)·c ≈ a·(b·c)` — both are `Σ_{i+j+l=k} aᵢbⱼc_l`,
    connected by the triangle/antidiagonal reindex. -/
theorem fmul_assoc (a b c : Nat → Q) (ha : ∀ i, 0 < (a i).den) (hb : ∀ i, 0 < (b i).den)
    (hc : ∀ i, 0 < (c i).den) (k : Nat) :
    Qeq (fmul (fmul a b) c k) (fmul a (fmul b c) k) := by
  have hg : ∀ i j, 0 < (mul (mul (a i) (b j)) (c (k - (i + j)))).den :=
    fun i j => Qmul_den_pos (Qmul_den_pos (ha i) (hb j)) (hc _)
  have hLHS : Qeq (fmul (fmul a b) c k)
      (Fsum (fun m => Fsum (fun i => mul (mul (a i) (b (m - i))) (c (k - (i + (m - i))))) m) k) := by
    show Qeq (Fsum (fun m => mul (Fsum (fun i => mul (a i) (b (m - i))) m) (c (k - m))) k) _
    refine Fsum_congr_le (fun m hm => ?_)
    refine Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos (Qmul_den_pos (ha i) (hb (m - i))) (hc (k - m))) m)
      (Fsum_mul_const_right (hc (k - m)) (fun i => Qmul_den_pos (ha i) (hb (m - i))) m)
      (Fsum_congr_le (fun i hi => ?_))
    have hidx : k - (i + (m - i)) = k - m := by omega
    rw [hidx]; exact Qeq_refl _
  have hRHS : Qeq (fmul a (fmul b c) k)
      (Fsum (fun i => Fsum (fun j => mul (mul (a i) (b j)) (c (k - (i + j)))) (k - i)) k) := by
    show Qeq (Fsum (fun i => mul (a i) (Fsum (fun j => mul (b j) (c (k - i - j))) (k - i))) k) _
    refine Fsum_congr_le (fun i hi => ?_)
    refine Qeq_trans (Fsum_den_pos (fun j => Qmul_den_pos (ha i) (Qmul_den_pos (hb j) (hc (k - i - j)))) (k - i))
      (Qeq_symm (Fsum_mul_left (ha i) (fun j => Qmul_den_pos (hb j) (hc (k - i - j))) (k - i)))
      (Fsum_congr_le (fun j hj => ?_))
    have hidx : k - i - j = k - (i + j) := by omega
    rw [hidx]; exact Qeq_symm (Qmul_assoc (a i) (b j) (c (k - (i + j))))
  exact Qeq_trans (Fsum_den_pos (fun m => Fsum_den_pos (fun i => hg i (m - i)) m) k) hLHS
    (Qeq_trans (Fsum_den_pos (fun i => Fsum_den_pos (fun j => hg i j) (k - i)) k)
      (Qeq_symm (Fsum_triangle_reindex hg k)) (Qeq_symm hRHS))

end UOR.Bridge.F1Square.Analysis
