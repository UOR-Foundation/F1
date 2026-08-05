/-
F1 square — **scale-uniform tail-decay preservation under real dilation** (`DilateTestRDecay.lean`):
dilation by a real scale `c ≥ 1` only enlarges the argument (`|c·y| = |c|·|y| ≥ |y|`), so the clean
k-indexed half-line decay of `f` transfers to `dilateTestR c f` with the SAME constant `Cf` — uniformly
in `c` (for every `c ≥ 1`). This is the analytic heart of the uniform-in-`t` decay the `∫_t`
reconstruction of `M[f⋆g]=M[f]·M[g]` needs: on the `t`-window `⊆ (0,1]` the convolution's inner
dilation scale is `clampedInv(a,t) = 1/max(t,a) ≥ 1` (since `t ≤ 1` and `a ≤ 1`), so every dilated tail
`twTail (dilateTestR (clampedInv a t) f) n` exists with a `t`-independent decay constant.

The point is the *uniformity*: `twTerm_bound`/`twTail`/`convMellinHat` all consume a decay hypothesis in
the clean k-indexed shape `∀ k, ∀ y, |y| ≥ k+1 → |f(y)| ≤ Cf/(k+1)^{n+2}`; here that shape is shown to
be preserved by `dilateTestR c` for *any* `c ≥ 1` with the *same* `Cf`, so the eventual limit-inside-the-
integral step has a bound independent of the integration variable `t`.

HONEST SCOPE. The decay-hypothesis transport only (clean k-indexed `hfdec` ↦ same shape for the `c ≥ 1`
dilate). It builds NO tail assembly, NO covariance application, NO `∫_t` reconstruction, NO factorization
`M[f⋆g]=M[f]·M[g]`, NO positivity, NO crux. Step 4 (band-coupling positivity) is RH; the crux fields stay
`none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.DilateTestR
import F1Square.Square.MellinHat

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **A real scale `c ≥ 1` enlarges every argument**: `|y| ≤ |c·y|`. The chain-rule fact behind
    scale-uniform decay preservation (`|c·y| = |c|·|y| ≥ 1·|y| = |y|`, since `|c| = c ≥ 1`). -/
theorem Rabs_le_Rabs_Rmul_of_one_le {c : Real} (hc1 : Rle one c) (y : Real) :
    Rle (Rabs y) (Rabs (Rmul c y)) := by
  have hcnn : Rnonneg c :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) hc1)
  have h1c : Rle one (Rabs c) :=
    Rle_trans hc1 (Rle_of_Req (Req_symm (Rabs_of_nonneg hcnn)))
  refine Rle_trans (Rle_of_Req (Req_symm (Rone_mul (Rabs y)))) ?_
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs y) h1c) ?_
  exact Rle_of_Req (Req_symm (Rabs_Rmul c y))

/-- **Scale-uniform tail-decay preservation**: if `f` has clean order-`(n+2)` half-line decay with
    constant `Cf`, then for ANY real scale `c ≥ 1` (bounded by `S`), the real dilation
    `dilateTestR c f` has the SAME decay with the SAME constant `Cf` — the bound is uniform in `c`. The
    proof: `(dilateTestR c f).f y = f.f (c·y)` and `|c·y| ≥ |y| ≥ k+1`, so `f`'s own decay at index `k`
    applies at the enlarged point `c·y`. -/
theorem dilateTestR_hfdec (f : L2Test) (n : Nat) {Cf : Q} (hCfd : 0 < Cf.den) (hCfn : 0 ≤ Cf.num)
    (hfdec : ∀ (k : Nat), ∀ y, Rle (ofQ (⟨(k : Int) + 1, 1⟩ : Q) Nat.one_pos) (Rabs y) →
      Rle (Rabs (f.f y)) (ofQ (mul Cf (⟨1, (k + 1) ^ (n + 2)⟩ : Q))
        (Qmul_den_pos hCfd (Nat.pos_pow_of_pos _ (Nat.succ_pos k)))))
    (c : Real) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num) (hcS : Rle (Rabs c) (ofQ S hSd))
    (hc1 : Rle one c) :
    ∀ (k : Nat), ∀ y, Rle (ofQ (⟨(k : Int) + 1, 1⟩ : Q) Nat.one_pos) (Rabs y) →
      Rle (Rabs ((dilateTestR c S hSd hSn hcS f).f y)) (ofQ (mul Cf (⟨1, (k + 1) ^ (n + 2)⟩ : Q))
        (Qmul_den_pos hCfd (Nat.pos_pow_of_pos _ (Nat.succ_pos k)))) := by
  intro k y hy
  show Rle (Rabs (f.f (Rmul c y)))
    (ofQ (mul Cf (⟨1, (k + 1) ^ (n + 2)⟩ : Q))
      (Qmul_den_pos hCfd (Nat.pos_pow_of_pos _ (Nat.succ_pos k))))
  exact hfdec k (Rmul c y) (Rle_trans hy (Rabs_le_Rabs_Rmul_of_one_le hc1 y))

end UOR.Bridge.F1Square.Square
