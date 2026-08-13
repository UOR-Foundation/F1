/-
F1 square — **the canonical-autocorr bridge** (`WeilPrimeShiftBridge.lean`): the canonical autocorrelation `autocorr` (built on the
rational-scale `mulConv`) equals the landed point-test `autocorrL2` (built on the real-scale
`mulConvRTest`) at every in-band rational scale `q ∈ [0, S]`.

Both objects are, after unfolding, the SAME Haar integral of the SAME product integrand
`(reflectTest a (dilate·q g)) · (reflectTest a g) · (1/max(·,a))` over the window `[lo, lo+w]`; they
differ ONLY in how the inner dilation-by-`q` is realized:

  • `autocorr`   uses the rational-scale `dilateTest q g   .f z = g(q·z)`   (modulus `g.L·q`);
  • `autocorrL2` uses the real-scale   `dilateTestR (clamp q) g .f z = g((clamp q)·z)` (modulus `g.L·S`).

In-band (`0 ≤ q ≤ S`) the `[0,S]`-clamp is inert (`qBandQ_eq_of_band`: `clamp q ≈ q`), so the two
dilation scales agree at EVERY point, hence the two integrands agree pointwise. The two Lipschitz
moduli differ (`g.L·q` vs `g.L·S`), so the bridge is closed by the different-modulus window
congruence `riemannIntegralI_congr_unit_mod` (both `haarIntegral`s are, definitionally,
`riemannIntegralI` of the product certificate against the `recipTest` density).

HONEST SCOPE. This is a pointwise-VALUE identity between two constructed integrals — no positivity,
no Mellin/convolution theorem, no crux claim. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftAutocorr
import F1Square.Square.TwTermPowBand

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **Canonical `autocorr` = in-band `autocorrL2`.** For an in-band rational scale
    `q ∈ [0, S]` (`hq0 : 0 ≤ q`, `hqS : q ≤ S`), the canonical autocorrelation
    `autocorr g q … = (g ⋆ g^τ)(q)` (rational-scale `mulConv`) equals the point value of the landed
    autocorr point-test `(autocorrL2 g S …).f (ofQ q)` (real-scale `mulConvRTest`) at `q`.

    Both unfold to `haarIntegral` of the product integrand
    `(reflectTest a (dilate·q g)) · (reflectTest a g)`; the only difference is the rational-scale
    `dilateTest q g` (`autocorr`) vs the real-scale `dilateTestR (clamp q) g` (`autocorrL2`). In band
    the `[0,S]`-clamp is inert (`qBandQ_eq_of_band`), so the scales — hence the whole integrands —
    agree pointwise (`g.hfc` through `Rmul_congr`); the two Lipschitz moduli differ, so the equality
    of the integrals is the different-modulus window congruence `riemannIntegralI_congr_unit_mod`. -/
theorem autocorr_eq_autocorrL2 (g : L2Test) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (hq0 : Qle (⟨0, 1⟩ : Q) q) (hqS : Qle q S) :
    Req (autocorr g q hqn hqd a han had lo w hlo hw hwn)
        ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q hqd)) := by
  -- The clamp is inert in band: `q ≈ clamp q`.
  have hax : Rle (ofQ (⟨0, 1⟩ : Q) (by decide)) (ofQ q hqd) := Rle_ofQ_ofQ (by decide) hqd hq0
  have hxb : Rle (ofQ q hqd) (ofQ S hSd) := Rle_ofQ_ofQ hqd hSd hqS
  have hqs : Req (ofQ q hqd)
      (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) :=
    Req_symm (qBandQ_eq_of_band hax hxb)
  -- Rewrite the RHS point value as the explicit Haar integral of the real-scale product integrand.
  rw [autocorrL2_f_haar]
  -- Both sides are `riemannIntegralI` of the product certificate against the `recipTest` density;
  -- the two integrands agree pointwise, the moduli differ → different-modulus window congruence.
  refine riemannIntegralI_congr_unit_mod
    (l2L_den (productTest (reflectTest a han had (dilateTest q hqn hqd g))
        (reflectTest a han had g)) (recipTest a han had))
    (l2L_num (productTest (reflectTest a han had (dilateTest q hqn hqd g))
        (reflectTest a han had g)) (recipTest a han had))
    (l2lip (productTest (reflectTest a han had (dilateTest q hqn hqd g))
        (reflectTest a han had g)) (recipTest a han had))
    (l2fc (productTest (reflectTest a han had (dilateTest q hqn hqd g))
        (reflectTest a han had g)) (recipTest a han had))
    (l2L_den (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) g)) (reflectTest a han had g)) (recipTest a han had))
    (l2L_num (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) g)) (reflectTest a han had g)) (recipTest a han had))
    (l2lip (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) g)) (reflectTest a han had g)) (recipTest a han had))
    (l2fc (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) g)) (reflectTest a han had g)) (recipTest a han had))
    lo w hlo hw hwn ?_
  -- Pointwise integrand agreement (independent of the window point): the `recipTest` density and the
  -- outer `reflectTest a g` factors coincide; the inner `reflectTest a (dilate·q g)` factors agree
  -- because `q ≈ clamp q`, so `g(q·(1/max(·,a))) ≈ g((clamp q)·(1/max(·,a)))` by `g.hfc`.
  intro x _ _
  exact Rmul_congr
    (Rmul_congr (g.hfc _ _ (Rmul_congr hqs (Req_refl _))) (Req_refl _)) (Req_refl _)

end UOR.Bridge.F1Square.Square
