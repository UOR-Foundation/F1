/-
F1 square — the **`n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ = n⁻ˢ · e^{−s·δ_n}` (`δ_n = log(n+1) − log n`),
the engine of the η-series **variation bound** `Σ |n⁻ˢ − (n+1)⁻ˢ| < ∞` (`Re s > 0`) — the integration-free
route to `ζ` on the critical strip. The recurrence is the direct consequence of the complex exponential
law `Cexp_add`: `n⁻ˢ = e^{−s·log n}` (`cpowNeg`), and `log(n+1) = log n + δ_n`, so
`e^{−s·log(n+1)} = e^{−s·log n}·e^{−s·δ_n}`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.EulerMaclaurin
import F1Square.Analysis.ComplexExpAdd
import F1Square.Analysis.ComplexZeta

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Complex-algebra helpers (componentwise `Ceq = ⟨Req, Req⟩` lifts of the real laws).
-- ===========================================================================

/-- `Rsub (Rneg x) (Rneg y) ≈ Rneg (Rsub x y)` (both `≈ y − x`). -/
theorem Rsub_RnegRneg (x y : Real) : Req (Rsub (Rneg x) (Rneg y)) (Rneg (Rsub x y)) :=
  Req_symm (Rneg_Radd x (Rneg y))

/-- ℂ addition respects `≈`. -/
theorem Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') := ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- ℂ negation respects `≈`. -/
theorem Cneg_congr {z z' : Complex} (h : Ceq z z') : Ceq (Cneg z) (Cneg z') :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- ℂ multiplication respects `≈`. -/
theorem Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

/-- ℂ subtraction respects `≈`. -/
theorem Csub_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Csub z w) (Csub z' w') := Cadd_congr hz (Cneg_congr hw)

/-- `z·(−w) ≈ −(z·w)` on ℂ. -/
theorem Cmul_neg_right (z w : Complex) : Ceq (Cmul z (Cneg w)) (Cneg (Cmul z w)) :=
  ⟨Req_trans (Rsub_congr (Rmul_neg_right z.re w.re) (Rmul_neg_right z.im w.im))
      (Rsub_RnegRneg (Rmul z.re w.re) (Rmul z.im w.im)),
   Req_trans (Radd_congr (Rmul_neg_right z.re w.im) (Rmul_neg_right z.im w.re))
      (Req_symm (Rneg_Radd (Rmul z.re w.im) (Rmul z.im w.re)))⟩

/-- **The consecutive-log gap** `δ_n = log(n+1) − log n` (for `n ≥ 2`), as a constructive real. -/
def deltaLogNat (n : Nat) (hn : 2 ≤ n) : Real :=
  Rsub (RlogNat (n + 1) (by omega)) (RlogNat n hn)

/-- **The `n⁻ˢ` multiplicative recurrence** `(n+1)⁻ˢ ≈ n⁻ˢ · e^{−s·δ_n}` (for `n ≥ 2`). Both sides are
    `Cexp` of an argument; `log(n+1) = log n + δ_n` (`Radd_Rsub_self`) lifts through `Rmul_distrib` to the
    complex argument additivity, and `Cexp_add`/`Cexp_congr` close it. -/
theorem cpowNeg_succ (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (cpowNeg s (n + 1))
      (Cmul (cpowNeg s n)
        (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)) := by
  have h1 : 2 ≤ n + 1 := by omega
  unfold cpowNeg
  rw [dif_pos h1, dif_pos hn]
  -- both `ncpow` are `Cexp` of the argument `−s·log`; reduce to `Cexp_add` via argument additivity
  refine Ceq_trans (Cexp_congr (z := ⟨Rmul (Rneg s.re) (RlogNat (n + 1) h1), Rmul (Rneg s.im) (RlogNat (n + 1) h1)⟩)
      (w := Cadd ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
        ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩) ?_)
    (Cexp_add ⟨Rmul (Rneg s.re) (RlogNat n hn), Rmul (Rneg s.im) (RlogNat n hn)⟩
      ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)
  -- argument additivity: `−s·log(n+1) ≈ −s·log n + (−s)·δ_n`, componentwise
  have hlog : Req (RlogNat (n + 1) h1) (Radd (RlogNat n hn) (deltaLogNat n hn)) :=
    Req_symm (Radd_Rsub_self (RlogNat n hn) (RlogNat (n + 1) h1))
  exact ⟨Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.re) (RlogNat n hn) (deltaLogNat n hn)),
    Req_trans (Rmul_congr (Req_refl _) hlog)
      (Rmul_distrib (Rneg s.im) (RlogNat n hn) (deltaLogNat n hn))⟩

/-- **The `n⁻ˢ` consecutive difference** `n⁻ˢ − (n+1)⁻ˢ ≈ n⁻ˢ·(1 − e^{−s·δ_n})` (for `n ≥ 2`) — the form
    on which the variation modulus `|n⁻ˢ − (n+1)⁻ˢ| ≤ |n⁻ˢ|·|1 − e^{−s·δ_n}|` is read off. Factor `n⁻ˢ`
    out of `n⁻ˢ − n⁻ˢ·e^{−s·δ_n}` (`cpowNeg_succ`) via `Cmul_distrib`/`Cmul_one`/`Cmul_neg_right`. -/
theorem cpowNeg_diff (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Ceq (Csub (cpowNeg s n) (cpowNeg s (n + 1)))
      (Cmul (cpowNeg s n)
        (Csub Cone (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))) :=
  Ceq_trans (Cadd_congr (Ceq_refl _) (Cneg_congr (cpowNeg_succ s n hn)))
    (Ceq_trans (Cadd_congr (Ceq_symm (Cmul_one (cpowNeg s n)))
        (Ceq_symm (Cmul_neg_right (cpowNeg s n)
          (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩))))
      (Ceq_symm (Cmul_distrib (cpowNeg s n) Cone
        (Cneg (Cexp ⟨Rmul (Rneg s.re) (deltaLogNat n hn), Rmul (Rneg s.im) (deltaLogNat n hn)⟩)))))

/-- **`e^{−d} ≤ 1` for `d ≥ 0`** (the exponential of a non-positive argument is at most `1`). From
    `e^{−d}·e^d = 1` and `e^d ≥ 1`: `e^{−d} = e^{−d}·1 ≤ e^{−d}·e^d = 1`. -/
theorem RexpReal_neg_le_one (d : Real) (hd : Rnonneg d) : Rle (RexpReal (Rneg d)) one := by
  have hprod : Req (Rmul (RexpReal (Rneg d)) (RexpReal d)) one :=
    Req_trans (Req_symm (RexpReal_add (Rneg d) d))
      (Req_trans (RexpReal_congr (Req_trans (Radd_comm (Rneg d) d) (Radd_neg d))) RexpReal_zero)
  exact Rle_trans (Rle_of_Req (Req_symm (Rmul_one (RexpReal (Rneg d)))))
    (Rle_trans (Rmul_le_Rmul_left (RexpReal_nonneg (Rneg d)) (RexpReal_ge_one hd))
      (Rle_of_Req hprod))

-- ===========================================================================
-- The `n⁻ˢ` per-term component bounds `−n⁻ᴿᵉˢ ≤ Re/Im(n⁻ˢ) ≤ n⁻ᴿᵉˢ` (no real-abs; two-sided `Rle`,
-- mirroring `ComplexZeta`'s `czetaTerm_re_le`/`ge`). `cpowNeg s n = e^{−s·log n}` for `n ≥ 2`. -/
-- ===========================================================================

/-- `Re(n⁻ˢ) ≤ e^{−Re s·log n}` (`= n⁻ᴿᵉˢ`). -/
theorem cpowNeg_re_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).re) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_le _

/-- `−e^{−Re s·log n} ≤ Re(n⁻ˢ)`. -/
theorem cpowNeg_re_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).re) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_re_ge _

/-- `Im(n⁻ˢ) ≤ e^{−Re s·log n}`. -/
theorem cpowNeg_im_le (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle ((cpowNeg s n).im) (RexpReal (Rmul (Rneg s.re) (RlogNat n hn))) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_le _

/-- `−e^{−Re s·log n} ≤ Im(n⁻ˢ)`. -/
theorem cpowNeg_im_ge (s : Complex) (n : Nat) (hn : 2 ≤ n) :
    Rle (Rneg (RexpReal (Rmul (Rneg s.re) (RlogNat n hn)))) ((cpowNeg s n).im) := by
  unfold cpowNeg; rw [dif_pos hn]; exact Cexp_im_ge _


-- ===========================================================================
-- The tight exponential lower bound  1 + 4t ≤ e^t  (t ∈ [−1/2,0]), i.e. 1 − e^{−d} ≤ 4d.
-- The analytic crux of the η variation bound: lifts the Q-level quadratic remainder
-- `expSum_quad` (|expSum q N − (1+q)| ≤ |q|²·expSumM ≤ 3q²) through the diagonal, using the
-- algebra (1+q)−3q² ≥ 1+4q (q∈[−1,0]) to get a LINEAR bound (no real-side product to reconcile).
-- ===========================================================================

-- GOAL 1 (Q-level): for |q| ≤ 1 and q ≤ 1/(N+1) (the wiggle/upper bound) and N ≥ 1,
--   1 + 4q ≤ expSum q N + 3/(N+1).
-- Proof idea (by_cases on sign of q):
--   q ≥ 0:  expSum q N ≥ 1+q (expSum_ge_one_add, index N-1+1=N); 1+4q = (1+q)+3q ≤ expSum+3q ≤ expSum+3/(N+1)
--           since 3q ≤ 3/(N+1) (q ≤ 1/(N+1)).
--   q < 0:  expSum_quad gives |expSum q N − (1+q)| ≤ |q|²·expSumM 1 N ≤ 3q² (expSumM 1 N ≤ 3).
--           So expSum q N ≥ (1+q) − 3q². For q ∈ [−1,0): (1+q)−3q² ≥ 1+4q  (⟺ q(q+1) ≤ 0). Hence
--           1+4q ≤ expSum q N ≤ expSum q N + 3/(N+1).
-- expSumM 1 N ≤ ⟨3,1⟩ :  Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
theorem expSum_ge_one_add_four {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨1, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨3, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 3/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    -- 3q ≤ 3/(N+1)
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨3, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    -- assemble
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨3, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  1+4q ≤ (1+q) - 3q² ≤ expSum  ≤ expSum + 3/(N+1)
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q) := hq1
    -- quadratic remainder:  expSum q N ≥ (1+q) - |q|²·expSumM 1 N
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    -- |q|² ≤ |q|·1 = |q| = -q  (since q<0);  expSumM ≤ 3
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    -- expSum q N ≥ (1+q) − R   where R = |q|²·expSumM
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      -- (1+q) ≤ expSum + R
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      -- commute to  (1+q) ≤ R + expSum
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    -- 1+4q ≤ (1+q) − 3q²    (⟺ q(q+1) ≤ 0, here via |q|²≤|q|=−q)
    -- step: |q|·|q| ≤ |q|·1
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    -- now 1+4q ≤ (1+q) − |q|²·expSumM
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      -- R := |q|²·expSumM ;  show R ≤ (-q)·3 = -3q.
      -- step a:  R ≤ |q|²·3
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      -- step b:  |q|²·3 ≤ |q|·3
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      -- |q|·3 = (-q)·3   (|q| = -q since q<0)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      -- subtraction antitone:  (1+q) − (-3q) ≤ (1+q) − R ,  and (1+q) − (-3q) = 1+4q.
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · -- 1+4q = (1+q) − (-q)·3
        exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · -- (1+q) − (-q)·3 ≤ (1+q) − R  via R ≤ (-q)·3
        simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    -- chain: 1+4q ≤ (1+q)−R ≤ expSum ≤ expSum + 3/(N+1)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd)
      (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)))
      hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 3; decide))

-- Helper: the loose form of GOAL 1 with the Bishop upper bound `q ≤ 2/(N+1)` (slack `6/(N+1)`).
-- This is the form actually available at the diagonal (the real `t ≤ 0` only gives `2/(N+1)`).
private theorem expSum_ge_four_loose {q : Q} (hqd : 0 < q.den) (N : Nat) (hN1 : 1 ≤ N)
    (hq1 : Qle (Qabs q) (⟨1, 1⟩ : Q)) (hqhi : Qle q (⟨2, N + 1⟩ : Q)) :
    Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q)) (add (expSum q N) (⟨6, N + 1⟩ : Q)) := by
  by_cases hq0 : 0 ≤ q.num
  · -- q ≥ 0 :  1+4q = (1+q) + 3q ≤ expSum + 6/(N+1)
    have hge : Qle (add (⟨1, 1⟩ : Q) q) (expSum q N) := by
      have h := expSum_ge_one_add hq0 hqd (N - 1)
      rwa [(by omega : N - 1 + 1 = N)] at h
    have h3q : Qle (mul (⟨3, 1⟩ : Q) q) (⟨6, N + 1⟩ : Q) := by
      have h := Qmul_le_mul_left (c := (⟨3, 1⟩ : Q)) (by decide) hqhi
      refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos N)) h (Qeq_le ?_)
      simp only [Qeq, mul]; push_cast; ring_uor
    have hsum : Qle (add (add (⟨1, 1⟩ : Q) q) (mul (⟨3, 1⟩ : Q) q))
        (add (expSum q N) (⟨6, N + 1⟩ : Q)) := Qadd_le_add hge h3q
    refine Qle_trans (add_den_pos (add_den_pos (by decide) hqd) (Qmul_den_pos (by decide) hqd))
      (Qeq_le ?_) hsum
    simp only [Qeq, add, mul]; push_cast; ring_uor
  · -- q < 0 :  identical to GOAL 1, slack 3 ≤ 6
    have hq0 : q.num < 0 := Int.not_le.mp hq0
    have hNsucc : N - 1 + 1 = N := by omega
    have hquad := expSum_quad hqd hq1 (N - 1)
    rw [hNsucc] at hquad
    have hnn_q : 0 ≤ (Qabs q).num := Qabs_num_nonneg q
    have hEbound : Qle (expSumM 1 N) (⟨3, 1⟩ : Q) :=
      Qle_trans (expM_U_den_pos 1 2) (expSumM_le_U 1 N) (by decide)
    have hRden : 0 < (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)).den :=
      Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (expSumM_den_pos 1 N)
    have hlow : Qle (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)))
        (expSum q N) := by
      have hle1 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (expSum q N) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) :=
        Qle_add_of_Qabs_sub (add_den_pos (by decide) hqd) (expSum_den_pos hqd N) hRden
          (by rw [Qabs_Qsub_comm]; exact hquad)
      have hle2 : Qle (add (⟨1, 1⟩ : Q) q)
          (add (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (expSum q N)) :=
        Qle_trans (add_den_pos (expSum_den_pos hqd N) hRden) hle1
          (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
      exact Qsub_le_of_le_add hRden (expSum_den_pos hqd N) hle2
    have hsq : Qle (mul (Qabs q) (Qabs q)) (Qabs q) := by
      have h := Qmul_le_mul_left (c := Qabs q) hnn_q hq1
      refine Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) h (Qeq_le ?_)
      simp only [Qeq, mul, Qabs]; push_cast; ring_uor
    have hfinal : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) q))
        (Qsub (add (⟨1, 1⟩ : Q) q) (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))) := by
      have hRle : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N))
          (mul (mul (Qabs q) (Qabs q)) (⟨3, 1⟩ : Q)) :=
        Qmul_le_mul_left (Int.mul_nonneg hnn_q hnn_q) hEbound
      have hR3 : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (Qabs q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qmul_den_pos (Qabs_den_pos hqd) (Qabs_den_pos hqd)) (by decide))
          hRle (Qmul_le_mul_right (by decide) hsq)
      have habsneg : Qeq (mul (Qabs q) (⟨3, 1⟩ : Q)) (mul (neg q) (⟨3, 1⟩ : Q)) := by
        have hna : (q.num.natAbs : Int) = -q.num := by omega
        simp only [Qeq, mul, Qabs, neg]; push_cast; rw [hna]
      have hkey : Qle (mul (mul (Qabs q) (Qabs q)) (expSumM 1 N)) (mul (neg q) (⟨3, 1⟩ : Q)) :=
        Qle_trans (Qmul_den_pos (Qabs_den_pos hqd) (by decide)) hR3 (Qeq_le habsneg)
      refine Qle_trans (b := Qsub (add (⟨1, 1⟩ : Q) q) (mul (neg q) (⟨3, 1⟩ : Q)))
        (Qsub_den_pos (add_den_pos (by decide) hqd)
        (Qmul_den_pos (neg_den_pos hqd) (by decide))) ?_ ?_
      · exact Qeq_le (by simp only [Qeq, Qsub, add, neg, mul, Qabs]; push_cast; ring_uor)
      · simp only [Qsub]
        exact Qadd_le_add (Qle_refl _) (Qneg_le_neg hkey)
    refine Qle_trans (Qsub_den_pos (add_den_pos (by decide) hqd) hRden) hfinal ?_
    exact Qle_trans (expSum_den_pos hqd N) hlow
      (Qle_self_add (by show (0 : Int) ≤ 6; decide))

-- GOAL 2 (real lift): for t ≤ 0 and t ≥ −1/2,  1 + 4t ≤ e^t.
-- Mirror RexpReal_ge_one_add_nonneg (RealPow:899-942). Diagonal j, R := RexpReal_R t j (≥ 4(j+1)).
-- LHS.seq(2j+1) = add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq A)) with A = Ridx (ofQ⟨4,1⟩) t (2*(2j+1)+1) (deep, ≥ R-scale).
-- Sample q := t.seq R.  From ht0 (t≤0): q ≤ 1/(R+1).  From htlo (t≥−1/2): q ≥ −1 (R large).  ⟹ |q|≤1.
-- Use expSum_ge_one_add_four at q,R; reconcile t.seq A ↔ t.seq R (and t.seq(2j+1)) by xreg_n_le × 4.
theorem RexpReal_ge_one_add_four {t : Real} (ht0 : Rle t zero)
    (htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) t) :
    Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) t)) (RexpReal t) := by
  intro j
  show Qle (add (⟨1, 1⟩ : Q)
      (mul (⟨4, 1⟩ : Q) (t.seq (Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)))))
    (add (expSum (t.seq (RexpReal_R t j)) (RexpReal_R t j)) ⟨2, j + 1⟩)
  -- xBound t ≥ 2 (since (t.seq 0).den ≥ 1)
  have hxB : 2 ≤ xBound t := by unfold xBound; have := t.den_pos 0; omega
  -- RexpReal_K t ≥ 2
  have hK2 : 2 ≤ RexpReal_K t := by
    unfold RexpReal_K
    have hp : 0 < npow (xBound t) (2 * xBound t + 1) := npow_pos (by omega) _
    omega
  -- R ≥ 8*(j+1) + 4
  have hRlb : 8 * (j + 1) + 4 ≤ RexpReal_R t j := by
    unfold RexpReal_R
    have hmul : 4 * (j + 1) * 2 ≤ 4 * (j + 1) * RexpReal_K t := Nat.mul_le_mul_left _ hK2
    omega
  -- RmulK ≥ 2  (xBound t ≥ 2)
  have hKmul : 2 ≤ RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t := by unfold RmulK; omega
  -- A ≥ 8*(j+1) - 1
  have hAlb : 8 * (j + 1) ≤ Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) + 1 := by
    rw [Ridx_succ (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1)]
    have hmul : 2 * 2 * (2 * j + 1 + 1)
        ≤ 2 * RmulK (ofQ (⟨4, 1⟩ : Q) (by decide)) t * (2 * j + 1 + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKmul)
    omega
  -- abstract the two heavy indices
  generalize hRdef : RexpReal_R t j = R at hRlb ⊢
  generalize hAdef : Ridx (ofQ (⟨4, 1⟩ : Q) (by decide)) t (2 * j + 1) = A at hAlb ⊢
  have hqd : 0 < (t.seq R).den := t.den_pos _
  -- the floor n₀ = 8(j+1) - 1, so n₀ + 1 = 8(j+1)
  have hn0A : 8 * (j + 1) - 1 ≤ A := by omega
  have hn0R : 8 * (j + 1) - 1 ≤ R := by omega
  have hn0succ : (8 * (j + 1) - 1) + 1 = 8 * (j + 1) := by omega
  -- q-bounds:  upper  q ≤ 2/(R+1)
  have hqhi : Qle (t.seq R) (⟨2, R + 1⟩ : Q) := by
    have h := ht0 R
    -- zero.seq R = ⟨0,1⟩ ;  add ⟨0,1⟩ ⟨2,R+1⟩ ≈ ⟨2,R+1⟩
    refine Qle_trans (add_den_pos (zero.den_pos R) (Nat.succ_pos R)) h (Qeq_le ?_)
    simp only [zero, ofQ, Qeq, add]; push_cast; ring_uor
  -- q-bounds: lower  -1/2 - 2/(R+1) ≤ q  ⟹  |q| ≤ 1
  have hq1 : Qle (Qabs (t.seq R)) (⟨1, 1⟩ : Q) := by
    have hlo := htlo R
    -- (Rneg (ofQ ⟨1,2⟩)).seq R = ⟨-1,2⟩
    have hlo' : Qle (⟨-1, 2⟩ : Q) (add (t.seq R) (⟨2, R + 1⟩ : Q)) := by
      refine Qle_trans (b := (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))).seq R)
        (Real.den_pos _ R) (Qeq_le ?_) hlo
      simp only [Rneg, ofQ, neg, Qeq]
    -- so q.num ≥ -(q.den)  (i.e. q ≥ -1) using R ≥ 3
    by_cases hsgn : 0 ≤ (t.seq R).num
    · -- q ≥ 0:  |q| = q ≤ 2/(R+1) ≤ 1
      have habsq : Qeq (Qabs (t.seq R)) (t.seq R) := by
        have hna : ((t.seq R).num.natAbs : Int) = (t.seq R).num := by omega
        simp only [Qeq, Qabs]; push_cast; rw [hna]
      have hle2 : Qle (Qabs (t.seq R)) (⟨2, R + 1⟩ : Q) :=
        Qle_trans hqd (Qeq_le habsq) hqhi
      exact Qle_trans (Nat.succ_pos R) hle2 (by simp only [Qle]; push_cast; omega)
    · -- q < 0:  |q| = -q ≤ 1/2 + 2/(R+1) ≤ 1  (R ≥ 3)
      have hneg : (t.seq R).num < 0 := Int.not_le.mp hsgn
      have hRbig : (3 : Int) ≤ ((R : Nat) : Int) := by
        have : 3 ≤ R := by omega
        exact_mod_cast this
      have hdpos : (1 : Int) ≤ ((t.seq R).den : Int) := by have := hqd; omega
      have hP : (0 : Int) < ((R : Nat) : Int) + 1 := by omega
      -- unfold hlo':  -(d·(R+1)) ≤ (n·(R+1) + 2·d)·2
      simp only [Qle, add] at hlo'
      push_cast at hlo'
      -- abbreviate the two products
      have hkey : -(t.seq R).num ≤ ((t.seq R).den : Int) := by
        -- write d, n, P
        -- hstar :  -(d*P) ≤ 2*n*P + 4*d
        have hstar : -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
            ≤ 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by
          have h := hlo'
          have e : (-1 : Int) * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1))
              = -(((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          have e2 : ((t.seq R).num * (((R : Nat) : Int) + 1) + 2 * ((t.seq R).den : Int)) * 2
              = 2 * ((t.seq R).num * (((R : Nat) : Int) + 1)) + 4 * ((t.seq R).den : Int) := by ring_uor
          rw [e, e2] at h; exact h
        -- h4d :  4*d ≤ d*P   (since P ≥ 4)
        have h4d : 4 * ((t.seq R).den : Int) ≤ ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := by
          have := Int.mul_le_mul_of_nonneg_left (a := (4 : Int)) (b := ((R : Nat) : Int) + 1)
            (c := ((t.seq R).den : Int)) (by omega) (by omega)
          have e : ((t.seq R).den : Int) * 4 = 4 * ((t.seq R).den : Int) := by ring_uor
          have e2 : ((t.seq R).den : Int) * (((R : Nat) : Int) + 1)
              = ((t.seq R).den : Int) * (((R : Nat) : Int) + 1) := rfl
          omega
        -- combine:  -(2n)*P ≤ (2d)*P
        have hcomb : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
            ≤ (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1) := by
          have e1 : (-(2 * (t.seq R).num)) * (((R : Nat) : Int) + 1)
              = -(2 * ((t.seq R).num * (((R : Nat) : Int) + 1))) := by ring_uor
          have e2 : (2 * ((t.seq R).den : Int)) * (((R : Nat) : Int) + 1)
              = 2 * (((t.seq R).den : Int) * (((R : Nat) : Int) + 1)) := by ring_uor
          rw [e1, e2]; omega
        have hcanc : -(2 * (t.seq R).num) ≤ 2 * ((t.seq R).den : Int) :=
          Int.le_of_mul_le_mul_right hcomb hP
        omega
      simp only [Qle, Qabs]
      push_cast
      have hna : ((t.seq R).num.natAbs : Int) = -(t.seq R).num := by omega
      rw [hna]; omega
  -- the loose lower bound at q = t.seq R, N = R
  have hlb : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R)))
      (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) :=
    expSum_ge_four_loose hqd R (by omega) hq1 hqhi
  -- reconcile t.seq A with t.seq R at floor n0 (×4)
  have hAR : Qle (Qabs (Qsub (t.seq A) (t.seq R))) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q) :=
    xreg_n_le t hn0A hn0R
  -- 4·|t.seq A − t.seq R| ≤ 8/(n0+1) = 1/(j+1)
  have hrec : Qle (mul (⟨4, 1⟩ : Q) (t.seq A))
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)) := by
    -- |4·(A) − 4·(R)| = 4·|A−R| ≤ 8/(n0+1)
    have hmuldiff : Qle (Qabs (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R))))
        (⟨1, j + 1⟩ : Q) := by
      have he : Qeq (Qsub (mul (⟨4, 1⟩ : Q) (t.seq A)) (mul (⟨4, 1⟩ : Q) (t.seq R)))
          (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))) := by
        simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
      have h2 : Qle (Qabs (mul (⟨4, 1⟩ : Q) (Qsub (t.seq A) (t.seq R))))
          (⟨1, j + 1⟩ : Q) := by
        rw [Qabs_mul]
        -- |4|·|A−R| ≤ ⟨4,1⟩·⟨2,n0+1⟩ = ⟨8,n0+1⟩ ≤ ⟨1,j+1⟩
        have h4 : Qeq (Qabs (⟨4, 1⟩ : Q)) (⟨4, 1⟩ : Q) := by simp only [Qeq, Qabs]; push_cast
        have hstep : Qle (mul (Qabs (⟨4, 1⟩ : Q)) (Qabs (Qsub (t.seq A) (t.seq R))))
            (mul (⟨4, 1⟩ : Q) (⟨2, (8 * (j + 1) - 1) + 1⟩ : Q)) :=
          Qmul_le_mul (Qabs_den_pos (by decide)) (by decide)
            (Qabs_den_pos (Qsub_den_pos (t.den_pos _) (t.den_pos _)))
            (by decide) (Qabs_num_nonneg _) (Qeq_le h4) hAR
        refine Qle_trans (Qmul_den_pos (by decide) (Nat.succ_pos _)) hstep ?_
        exact Qeq_le (by rw [hn0succ]; simp only [Qeq, mul]; push_cast; ring_uor)
      exact Qle_trans (Qabs_den_pos (Qmul_den_pos (by decide)
        (Qsub_den_pos (t.den_pos _) (t.den_pos _)))) (Qeq_le (Qabs_Qeq he)) h2
    exact Qle_add_of_Qabs_sub (Qmul_den_pos (by decide) (t.den_pos _))
      (Qmul_den_pos (by decide) (t.den_pos _)) (Nat.succ_pos _) hmuldiff
  -- assemble:  LHS ≤ add ⟨1,1⟩ (mul ⟨4,1⟩ (t.seq R)) + 1/(j+1)
  --               ≤ expSum + 6/(R+1) + 1/(j+1)  ≤ expSum + 2/(j+1)
  have hLHS : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq R))) (⟨1, j + 1⟩ : Q)) := by
    refine Qle_trans (b := add (⟨1, 1⟩ : Q)
      (add (mul (⟨4, 1⟩ : Q) (t.seq R)) (⟨1, j + 1⟩ : Q)))
      (add_den_pos (by decide) (add_den_pos (Qmul_den_pos (by decide) (t.den_pos _))
        (Nat.succ_pos _))) (Qadd_le_add (Qle_refl _) hrec) ?_
    exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)
  -- chain hLHS with hlb (add 1/(j+1) on both)
  have hchain : Qle (add (⟨1, 1⟩ : Q) (mul (⟨4, 1⟩ : Q) (t.seq A)))
      (add (add (expSum (t.seq R) R) (⟨6, R + 1⟩ : Q)) (⟨1, j + 1⟩ : Q)) :=
    Qle_trans (add_den_pos (add_den_pos (by decide) (Qmul_den_pos (by decide) (t.den_pos _)))
      (Nat.succ_pos _)) hLHS (Qadd_le_add hlb (Qle_refl _))
  -- final slack:  6/(R+1) + 1/(j+1) ≤ 2/(j+1)
  refine Qle_trans (add_den_pos (add_den_pos (expSum_den_pos hqd R) (Nat.succ_pos _))
    (Nat.succ_pos _)) hchain ?_
  -- (expSum + 6/(R+1)) + 1/(j+1) = expSum + (6/(R+1) + 1/(j+1)) ≤ expSum + 2/(j+1)
  refine Qle_trans (b := add (expSum (t.seq R) R)
    (add (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q)))
    (add_den_pos (expSum_den_pos hqd R) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
    (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)) ?_
  refine Qadd_le_add (Qle_refl _) ?_
  -- 6/(R+1) + 1/(j+1) ≤ 2/(j+1)   (R ≥ 8(j+1)+4 ⟹ 6/(R+1) ≤ 1/(j+1))
  have h6 : Qle (⟨6, R + 1⟩ : Q) (⟨1, j + 1⟩ : Q) := by
    have hRi : (8 : Int) * ((j : Int) + 1) + 4 ≤ (R : Int) := by exact_mod_cast hRlb
    simp only [Qle]; push_cast; omega
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Qadd_le_add h6 (Qle_refl _)) ?_
  exact Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor)

-- real-algebra rearrangements (copied from GammaOne, which is not in this import chain)
private theorem Rsub_le_of_le_add' {x y z : Real} (h : Rle x (Radd z y)) : Rle (Rsub x y) z :=
  Rle_trans (Rsub_le_sub h (Rle_refl y))
    (Rle_of_Req (Req_trans (Radd_assoc z y (Rneg y))
      (Req_trans (Radd_congr (Req_refl z) (Radd_neg y)) (Radd_zero z))))

private theorem Rle_add_of_Rsub_le' {x y z : Real} (h : Rle (Rsub x y) z) : Rle x (Radd y z) := by
  have heq : Req (Radd (Rsub x y) y) x :=
    Req_trans (Radd_assoc x (Rneg y) y)
      (Req_trans (Radd_congr (Req_refl x) (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y)))
        (Radd_zero x))
  exact Rle_trans (Rle_of_Req (Req_symm heq))
    (Rle_trans (Radd_le_add h (Rle_refl y)) (Rle_of_Req (Radd_comm z y)))

-- GOAL 3 (corollary, the applied form): 1 − e^{−d} ≤ 4d  for 0 ≤ d ≤ 1/2.
theorem RexpReal_one_sub_neg_le {d : Real} (hd0 : Rnonneg d)
    (hd1 : Rle d (ofQ (⟨1, 2⟩ : Q) (by decide))) :
    Rle (Rsub one (RexpReal (Rneg d))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) := by
  -- apply GOAL 2 at t := Rneg d
  have ht0 : Rle (Rneg d) zero :=
    Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hd0)) (Rle_of_Req Rneg_zero)
  have htlo : Rle (Rneg (ofQ (⟨1, 2⟩ : Q) (by decide))) (Rneg d) := Rle_Rneg hd1
  have hG2 : Rle (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (RexpReal (Rneg d)) := RexpReal_ge_one_add_four ht0 htlo
  -- rewrite LHS:  1 + 4·(−d) ≈ 1 − 4·d
  have hEq : Req (Radd one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (Rneg d)))
      (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) :=
    Radd_congr (Req_refl _) (Rmul_neg_right (ofQ (⟨4, 1⟩ : Q) (by decide)) d)
  have hG2' : Rle (Rsub one (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d)) (RexpReal (Rneg d)) :=
    Rle_trans (Rle_of_Req (Req_symm hEq)) hG2
  -- rearrange:  1 − 4d ≤ e^{−d}  ⟹  1 ≤ 4d + e^{−d}  ⟹  1 − e^{−d} ≤ 4d
  have h1 : Rle one (Radd (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) d) (RexpReal (Rneg d))) :=
    Rle_add_of_Rsub_le' hG2'
  exact Rsub_le_of_le_add' h1

end UOR.Bridge.F1Square.Analysis
