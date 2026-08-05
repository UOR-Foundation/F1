/-
F1 square — **the dilated-tail integrand is bounded UNIFORMLY in `t`** (`DilTailUniformBound.lean`):
for a `t`-window `⊆ (0,1]` and `f` with clean order-`(n+2)` half-line decay, the `m`-th dilated-tail
integrand

    `dilTailIntegrand f g n m a t = g(t)·(1/max(t,a))·twTerm (dilateTestR (1/max(t,a)) f) n m`

obeys the `genSum`-ready two-sided bound `(g.M·(1/a)·Cf·2ⁿ)/((m+1)m)` at EVERY window point `t`, with a
constant that does NOT depend on `t`. This is the pointwise-in-`t` companion of `convTwTerm_bound` (which
bounds the *integrated* value `∫_t (…)`), and it is the estimate the `∫_t` reconstruction of
`M[f⋆g]=M[f]·M[g]` consumes to commute the tail sum `Σ_m` with the outer integral `∫_t`.

The uniformity is exactly what the decay bricks secured: on the window `t ≤ 1` (and `a ≤ 1`) the inner
dilation scale `clampedInv(a,t) = 1/max(t,a) ≥ 1` (`ofQ_inv_le_clampedInv`), so `dilateTestR_window_hdec`
gives `dilateTestR (1/max(t,a)) f` the SAME order-`(n+2)` window decay with the SAME constant `Cf`, and
`twTerm_bound` turns that into the `(Cf·2ⁿ)/((m+1)m)` term bound — with no `t`-dependence in the constant.
The `g`-weight `|g(t)|·|1/max(t,a)| ≤ g.M·(1/a)` is likewise `t`-uniform.

HONEST SCOPE. The uniform-in-`t` magnitude bound only (`m ≥ 1`, mirroring `convTwTerm_bound`). It builds
NO tail assembly, NO limit-inside-the-integral, NO covariance application, NO factorization
`M[f⋆g]=M[f]·M[g]`, NO positivity, NO crux. Step 4 (band-coupling positivity) is RH; the crux fields stay
`none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.TwTermMulConvDilated
import F1Square.Square.DilateTestRDecay
import F1Square.Analysis.ClampedInvLower

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 4000000

/-- **The dilated-tail integrand is bounded uniformly in the window variable `t`.** For a `t`-window
    `[lo, lo+w] ⊆ (0,1]` (`lo+w ≤ 1`, `a ≤ 1`) and `f` with clean order-`(n+2)` half-line decay
    (constant `Cf`), the `m`-th dilated-tail integrand at any window point `t = lo + w·s` (`s ∈ [0,1]`)
    obeys `|dilTailIntegrand f g n m a t| ≤ (g.M·(1/a)·Cf·2ⁿ)/((m+1)m)`, a bound with NO `t`-dependence.
    The pointwise-in-`t` companion of `convTwTerm_bound`. -/
theorem dilTailIntegrand_window_bound (f g : L2Test) (n : Nat) {Cf : Q}
    (hCfd : 0 < Cf.den) (hCfn : 0 ≤ Cf.num)
    (hfdec : ∀ (k : Nat), ∀ y, Rle (ofQ (⟨(k : Int) + 1, 1⟩ : Q) Nat.one_pos) (Rabs y) →
      Rle (Rabs (f.f y)) (ofQ (mul Cf (⟨1, (k + 1) ^ (n + 2)⟩ : Q))
        (Qmul_den_pos hCfd (Nat.pos_pow_of_pos _ (Nat.succ_pos k)))))
    (a : Q) (han : 0 < a.num) (had : 0 < a.den) (ha1 : Qle a (⟨1, 1⟩ : Q))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hw1 : Qle (add lo w) (⟨1, 1⟩ : Q)) (m : Nat) (hm : 1 ≤ m) :
    ∀ s, Rle zero s → Rle s one →
      Rle (Rabs (dilTailIntegrand f g n m a han had (affineMap lo w hlo hw s)))
        (ofQ (mul (mul g.M (Qinv a))
              (mul (mul Cf (⟨((2 ^ n : Nat) : Int), 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q)))
          (Qmul_den_pos (Qmul_den_pos g.hMd (Qinv_den_pos han))
            (Qmul_den_pos (Qmul_den_pos hCfd Nat.one_pos) (digamma_succ_mul_pos hm)))) := by
  intro s h0 h1
  -- the window point t' = lo + w·s ∈ [lo, lo+w] ⊆ (0,1]
  have ht'1 : Rle (affineMap lo w hlo hw s) (ofQ (⟨1, 1⟩ : Q) (by decide)) := by
    have hws : Rle (Rmul (ofQ w hw) s) (ofQ w hw) :=
      Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hw hwn) h1)
        (Rle_of_Req (Rmul_one (ofQ w hw)))
    refine Rle_trans (Radd_le_add (Rle_of_Req (Req_refl _)) hws)
      (Rle_trans (Rle_of_Req (Radd_ofQ_ofQ hlo hw))
        (Rle_ofQ_ofQ (add_den_pos hlo hw) (by decide) hw1))
  -- (1) clampedInv a t' ≥ 1 (t' ≤ 1, a ≤ 1)
  have hc1 : Rle one (clampedInv a han had (affineMap lo w hlo hw s)) :=
    Rle_trans (Rle_of_Req (ofQ_congr (by decide) (Qinv_den_pos (by decide)) (by decide)))
      (ofQ_inv_le_clampedInv han had (B := (⟨1, 1⟩ : Q)) (by decide) (by decide) ht'1 ha1)
  -- (2) the g-weight bound: |g(t')·clampedInv(a,t')| ≤ g.M·(1/a)
  have hgc : Rle (Rabs (Rmul (g.f (affineMap lo w hlo hw s))
        (clampedInv a han had (affineMap lo w hlo hw s))))
      (ofQ (mul g.M (Qinv a)) (Qmul_den_pos g.hMd (Qinv_den_pos han))) := by
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
      (Rnonneg_ofQ (Qinv_den_pos han) (Int.le_of_lt (Qinv_num_pos had)))
      (g.hbd _) ((recipTest a han had).hbd _)) ?_
    exact Rle_of_Req (Rmul_ofQ_ofQ _ _)
  -- (3) the dilated twisted tail term bound: |twTerm (dilate c_t' f) n m| ≤ (Cf·2ⁿ)/((m+1)m)
  have htw := twTerm_bound
    (dilateTestR (clampedInv a han had (affineMap lo w hlo hw s)) (Qinv a) (Qinv_den_pos han)
      (Int.le_of_lt (Qinv_num_pos had)) ((recipTest a han had).hbd (affineMap lo w hlo hw s)) f)
    n hCfd hCfn
    (dilateTestR_window_hdec f n hCfd hCfn hfdec
      (clampedInv a han had (affineMap lo w hlo hw s)) (Qinv a) (Qinv_den_pos han)
      (Int.le_of_lt (Qinv_num_pos had)) ((recipTest a han had).hbd (affineMap lo w hlo hw s)) hc1)
    m hm
  have htwabs : Rle (Rabs (twTerm
        (dilateTestR (clampedInv a han had (affineMap lo w hlo hw s)) (Qinv a) (Qinv_den_pos han)
          (Int.le_of_lt (Qinv_num_pos had)) ((recipTest a han had).hbd (affineMap lo w hlo hw s)) f)
        n m))
      (ofQ (mul (mul Cf (⟨((2 ^ n : Nat) : Int), 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (Qmul_den_pos hCfd Nat.one_pos) (digamma_succ_mul_pos hm))) :=
    Rabs_le_of_both htw.2 (Rle_trans (Rle_Rneg htw.1) (Rle_of_Req (Rneg_neg _)))
  have hdnn : Rnonneg (ofQ (mul (mul Cf (⟨((2 ^ n : Nat) : Int), 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q))
      (Qmul_den_pos (Qmul_den_pos hCfd Nat.one_pos) (digamma_succ_mul_pos hm))) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_Rabs _)) htwabs)
  -- (4) assemble: |dilTailIntegrand| = |g·clampedInv|·|twTerm| ≤ (g.M·1/a)·((Cf·2ⁿ)/((m+1)m))
  unfold dilTailIntegrand
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) hdnn hgc htwabs) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ _ _)

end UOR.Bridge.F1Square.Square
