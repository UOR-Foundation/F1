/-
F1 square — **the continuous real-scale normalized cross-correlation** `F_{f,g}(x) = x^{-1/2}·H_{f,g}(x)`
(`WeilCrossF.lean`), the two-input integrand of the closed Weil form's non-prime complement.

WHAT IS BUILT:
  • `HcrossTest f g` — the real-scale cross-correlation `H_{f,g}(x) = ∫ f(x/t)·g(1/t) d^×t` as a genuine
    `L2Test` in `x` (`mulConvRTest f (reflectTest g)`, the two-test generalization of `autocorrL2`).
  • `HForm_eq_HcrossTest` — the BRIDGE: at an in-band rational scale `q ∈ [0,S]` the continuous test's
    value IS the finite-prime Haar form `H_q(f,g) = HForm f g q` (port of `autocorr_eq_autocorrL2` to
    two independent tests: in band the `[0,S]`-clamp is inert, the two dilation realizations agree
    pointwise, `riemannIntegralI_congr_unit_mod` closes the different moduli).
  • `FTest f g = invSqrtTest · HcrossTest f g` — the normalized cross-correlation as an `L2Test`
    (`productTest` with the certified `x^{-1/2}` weight of `WeilInvSqrt`).
  • `FTest_ofQ` — RATIONAL IN-BAND READBACK: `F_{f,g}(q) ≈ BForm f g q` (`1 ≤ q ≤ B`, `q ≤ S`).
  • `FTest_one_symm` — the value at `1` is symmetric, `F_{f,g}(1) ≈ F_{g,f}(1)` (via the readback at
    `q = 1` and the proven `HForm_recip_one`) — the vanishing of the arch-tail numerator at the
    endpoint, the datum the `x = 1` improper limit consumes.
  • `qBandQ_ge_real` + `HcrossTest_high_vanish` — COMPACT SUPPORT: for every REAL `x ≥ Bd` (with
    `a+w ≤ Bd·a`, `Bd ≤ S`) the cross-correlation vanishes, `H_{f,g}(x) ≈ 0`, hence `F_{f,g}(x) ≈ 0`
    (`FTest_high_vanish`) — the decay the improper integrals consume.
  • `FTest_add_left/right` — BIADDITIVITY of the values in each test argument.

NO `primeGram`/`vFrom`/`vHat`, NO PSD, NO RH input.  Pure Lean 4 core, no Mathlib, choice-free.
-/

import F1Square.Square.WeilInvSqrt
import F1Square.Square.WeilPrimeShiftHaarForm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The real-scale cross-correlation test `H_{f,g}` and the rational bridge.
-- ===========================================================================

/-- **The real-scale cross-correlation** `H_{f,g}(x) = ∫ f(x/t)·g(1/t) d^×t` as an `L2Test` in `x`
    (window `lo = a`, scale band `[0, S]`) — `mulConvRTest f (reflectTest g)`, the two-test
    generalization of `autocorrL2`. -/
def HcrossTest (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : L2Test :=
  mulConvRTest f (reflectTest a han had g) S hSd hSn a han had a w had hw hwn

/-- The diagonal is the landed autocorrelation test: `HcrossTest g g = autocorrL2 g` (definitional). -/
theorem HcrossTest_diag (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    HcrossTest g g S hSd hSn a han had w hw hwn
      = autocorrL2 g S hSd hSn a han had a w had hw hwn := rfl

/-- **THE RATIONAL BRIDGE**: at an in-band rational scale `q ∈ [0, S]`, the continuous test's value is
    the finite-prime Haar form — `HForm f g q ≈ (HcrossTest f g).f (ofQ q)`.  Port of
    `autocorr_eq_autocorrL2` to two independent tests: in band the `[0,S]`-clamp is inert
    (`qBandQ_eq_of_band`), so the rational-scale `dilateTest q f` and the real-scale
    `dilateTestR (clamp q) f` agree pointwise (`f.hfc`), and the different Lipschitz moduli are
    reconciled by `riemannIntegralI_congr_unit_mod`. -/
theorem HForm_eq_HcrossTest (f g : L2Test) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hq0 : Qle (⟨0, 1⟩ : Q) q) (hqS : Qle q S) :
    Req (HForm f g q hqn hqd a han had w hw hwn)
        ((HcrossTest f g S hSd hSn a han had w hw hwn).f (ofQ q hqd)) := by
  have hax : Rle (ofQ (⟨0, 1⟩ : Q) (by decide)) (ofQ q hqd) := Rle_ofQ_ofQ (by decide) hqd hq0
  have hxb : Rle (ofQ q hqd) (ofQ S hSd) := Rle_ofQ_ofQ hqd hSd hqS
  have hqs : Req (ofQ q hqd)
      (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) :=
    Req_symm (qBandQ_eq_of_band hax hxb)
  show Req (haarIntegral (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)) a han had a w had hw hwn)
      (haarIntegral (productTest (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
          (clampS_absle S hSd hSn (ofQ q hqd)) f))
        (reflectTest a han had g)) a han had a w had hw hwn)
  refine riemannIntegralI_congr_unit_mod
    (l2L_den (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)) (recipTest a han had))
    (l2L_num (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)) (recipTest a han had))
    (l2lip (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)) (recipTest a han had))
    (l2fc (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)) (recipTest a han had))
    (l2L_den (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) f)) (reflectTest a han had g)) (recipTest a han had))
    (l2L_num (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) f)) (reflectTest a han had g)) (recipTest a han had))
    (l2lip (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) f)) (reflectTest a han had g)) (recipTest a han had))
    (l2fc (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q hqd)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ q hqd)) f)) (reflectTest a han had g)) (recipTest a han had))
    a w had hw hwn ?_
  intro x _ _
  exact Rmul_congr
    (Rmul_congr (f.hfc _ _ (Rmul_congr hqs (Req_refl _))) (Req_refl _)) (Req_refl _)

-- ===========================================================================
-- (2) The normalized cross-correlation `F_{f,g} = x^{-1/2}·H_{f,g}` and its readbacks.
-- ===========================================================================

/-- **THE CONTINUOUS NORMALIZED CROSS-CORRELATION** `F_{f,g}(x) = x^{-1/2}·H_{f,g}(x)` as an `L2Test`
    (the certified `x^{-1/2}` weight times the cross-correlation test). -/
def FTest (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : L2Test :=
  productTest (invSqrtTest B hBd hB1 N hN hBN)
    (HcrossTest f g S hSd hSn a han had w hw hwn)

/-- **★ RATIONAL IN-BAND READBACK TO `BForm`**: at a rational `1 ≤ q ≤ B` (with `q ≤ S`), the
    continuous normalized cross-correlation IS the finite-prime normalized form —
    `F_{f,g}(q) ≈ B_q(f,g) = q^{-1/2}·H_q(f,g)`. -/
theorem FTest_ofQ (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (q : Q) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) (hqB : Qle q B) (hqS : Qle q S) :
    Req ((FTest B hBd hB1 N hN hBN f g S hSd hSn a han had w hw hwn).f (ofQ q hqd))
        (BForm f g q (qnum_pos_of_one_le hqd hq1) hqd a han had w hw hwn) := by
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  have hq0 : Qle (⟨0, 1⟩ : Q) q := by
    simp only [Qle]; push_cast; omega
  show Req (Rmul (invSqrtF B hBd hB1 N hN hBN (ofQ q hqd))
        ((HcrossTest f g S hSd hSn a han had w hw hwn).f (ofQ q hqd)))
      (Rmul (normWeight q) (HForm f g q hqn hqd a han had w hw hwn))
  exact Rmul_congr (invSqrtF_ofQ B hBd hB1 N hN hBN q hqd hq1 hqB)
    (Req_symm (HForm_eq_HcrossTest f g q hqn hqd S hSd hSn a han had w hw hwn hq0 hqS))

/-- **THE VALUE AT `1` IS SYMMETRIC**: `F_{f,g}(1) ≈ F_{g,f}(1)` — the readback at `q = 1` plus the
    proven `n = 1` reciprocity `HForm_recip_one`.  This is exactly the vanishing of the arch-tail
    numerator `F_{f,g} + F_{g,f} − 2F_{f,g}(1)/x` at the endpoint `x = 1`, the datum the improper
    `x = 1` limit consumes. -/
theorem FTest_one_symm (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hS1 : Qle (⟨1, 1⟩ : Q) S) :
    Req ((FTest B hBd hB1 N hN hBN f g S hSd hSn a han had w hw hwn).f one)
        ((FTest B hBd hB1 N hN hBN g f S hSd hSn a han had w hw hwn).f one) := by
  have h1 := FTest_ofQ B hBd hB1 N hN hBN f g S hSd hSn a han had w hw hwn
    (⟨1, 1⟩ : Q) (by decide) (Qle_refl _) hB1 hS1
  have h2 := FTest_ofQ B hBd hB1 N hN hBN g f S hSd hSn a han had w hw hwn
    (⟨1, 1⟩ : Q) (by decide) (Qle_refl _) hB1 hS1
  refine Req_trans h1 (Req_trans ?_ (Req_symm h2))
  -- BForm f g 1 ≈ BForm g f 1 : the weight is shared; H_1(f,g) ≈ H_1(g,f) is HForm_recip_one.
  exact Rmul_congr (Req_refl _) (HForm_recip_one f g a han had w hw hwn)

-- ===========================================================================
-- (3) Compact support: the cross-correlation vanishes at every real `x ≥ Bd`.
-- ===========================================================================

/-- **The band clamp preserves real lower bounds**: `x ≥ Bd` (with `0 ≤ Bd ≤ S`) gives
    `qBandQ 0 S x ≥ Bd` — per index, `min(max(xₙ,0),S)` stays above `Bd` up to the `Rle` slack. -/
theorem qBandQ_ge_real (S : Q) (hSd : 0 < S.den) (Bd : Q) (hBdd : 0 < Bd.den)
    (hBd0 : Qle (⟨0, 1⟩ : Q) Bd) (hBdS : Qle Bd S) (x : Real)
    (hx : Rle (ofQ Bd hBdd) x) :
    Rle (ofQ Bd hBdd) (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) := by
  intro n
  have hxn := hx n
  show Qle Bd (add (Qmin (Qmax (x.seq n) (⟨0, 1⟩ : Q)) S) (⟨2, n + 1⟩ : Q))
  unfold Qmin
  split
  · -- band value = max(xₙ, 0) ≥ xₙ, and Bd ≤ xₙ + slack
    refine Qle_trans (add_den_pos (x.den_pos n) (Nat.succ_pos n)) hxn
      (Qadd_le_add ?_ (Qle_refl _))
    unfold Qmax
    split
    · assumption
    · exact Qle_refl _
  · -- band value = S ≥ Bd
    exact Qle_trans hSd hBdS (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Pointwise vanishing of the cross integrand at a window sample** for a clamped scale `≥ Bd`
    (`a+w ≤ Bd·a`): at `qp ∈ [a, a+w]` the first factor is `f(X·(1/qp))` with
    `X·(1/qp) ≥ Bd·(1/qp) ≥ 1/a`, so `hgh_f` kills it. -/
theorem crossIntegrand_pt_zero (f g : L2Test)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (Bd : Q) (hBdd : 0 < Bd.den) (hBdn : 0 ≤ Bd.num)
    (hband : Qle (add a w) (mul Bd a))
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (X : Real) (hX : Rle (ofQ Bd hBdd) X)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num)
    (haqp : Qle a qp) (hqpaw : Qle qp (add a w)) :
    Req (Rmul (f.f (Rmul X (clampedInv a han had (ofQ qp hqpd))))
          ((reflectTest a han had g).f (ofQ qp hqpd))) zero := by
  -- the rational threshold: 1/a ≤ Bd·(1/qp)
  have hrat : Qle (Qinv a) (mul Bd (Qinv qp)) := by
    have hqpBda : Qle qp (mul Bd a) := Qle_trans (add_den_pos had hw) hqpaw hband
    show ((Qinv a).num) * ((mul Bd (Qinv qp)).den : Int)
        ≤ ((mul Bd (Qinv qp)).num) * ((Qinv a).den : Int)
    show ((a.den : Int)) * ((Bd.den * qp.num.toNat : Nat) : Int)
        ≤ (Bd.num * (qp.den : Int)) * ((a.num.toNat : Nat) : Int)
    have h := hqpBda
    simp only [Qle, mul] at h
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqpn),
      Int.toNat_of_nonneg (Int.le_of_lt han)] at *
    -- h : qp.num * (Bd.den * a.den) ≤ Bd.num * a.num * qp.den
    -- goal : a.den * (Bd.den * qp.num) ≤ Bd.num * qp.den * a.num
    have e1 : (a.den : Int) * ((Bd.den : Int) * qp.num)
        = qp.num * ((Bd.den : Int) * (a.den : Int)) := by ring_uor
    have e2 : Bd.num * (qp.den : Int) * a.num = Bd.num * a.num * (qp.den : Int) := by ring_uor
    omega
  -- lift to the real product: 1/a ≤ Bd·(1/qp) ≤ X·(1/qp) = X·clampedInv a qp
  have hclamp : Req (clampedInv a han had (ofQ qp hqpd)) (ofQ (Qinv qp) (Qinv_den_pos hqpn)) :=
    clampedInv_ofQ han had hqpd hqpn haqp
  have hnninv : Rnonneg (ofQ (Qinv qp) (Qinv_den_pos hqpn)) :=
    Rnonneg_ofQ (Qinv_den_pos hqpn) (Int.le_of_lt (Qinv_num_pos hqpd))
  have hstep : Rle (ofQ (mul Bd (Qinv qp)) (Qmul_den_pos hBdd (Qinv_den_pos hqpn)))
      (Rmul X (clampedInv a han had (ofQ qp hqpd))) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ hBdd (Qinv_den_pos hqpn)))) ?_
    refine Rle_trans (Rmul_le_Rmul_right hnninv hX) ?_
    exact Rle_of_Req (Rmul_congr (Req_refl X) (Req_symm hclamp))
  have harg : Rle (ofQ (Qinv a) (Qinv_den_pos han))
      (Rmul X (clampedInv a han had (ofQ qp hqpd))) :=
    Rle_trans (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos hBdd (Qinv_den_pos hqpn)) hrat) hstep
  exact Req_trans (Rmul_congr (hgh_f _ harg) (Req_refl _))
    (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- **★ COMPACT SUPPORT (high side)**: for every REAL `x ≥ Bd` (with `a+w ≤ Bd·a`, `0 ≤ Bd ≤ S`),
    the cross-correlation vanishes — `H_{f,g}(x) ≈ 0`.  The window samples are rational points
    `qp ∈ [a, a+w]`, where `crossIntegrand_pt_zero` fires with the clamped scale `≥ Bd`
    (`qBandQ_ge_ofQ`). -/
theorem HcrossTest_high_vanish (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (Bd : Q) (hBdd : 0 < Bd.den) (hBd0 : Qle (⟨0, 1⟩ : Q) Bd) (hBdS : Qle Bd S)
    (hband : Qle (add a w) (mul Bd a))
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (x : Real) (hx : Rle (ofQ Bd hBdd) x) :
    Req ((HcrossTest f g S hSd hSn a han had w hw hwn).f x) zero := by
  have hBdn : 0 ≤ Bd.num := by
    have h := hBd0
    simp only [Qle] at h
    push_cast at h
    omega
  have hXge : Rle (ofQ Bd hBdd) (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) :=
    qBandQ_ge_real S hSd Bd hBdd hBd0 hBdS x hx
  show Req (haarIntegral (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
        (clampS_absle S hSd hSn x) f)) (reflectTest a han had g))
      a han had a w had hw hwn) zero
  refine haarIntegral_window_vanish _ a han had a w had hw hwn ?_
  intro M i hi
  have hqid : (0 : Nat) < M + 1 := Nat.succ_pos M
  have hmul_nn : (0 : Int) ≤ (mul w (⟨(i : Int), M + 1⟩ : Q)).num := by
    show (0 : Int) ≤ w.num * (i : Int); exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hqpd : 0 < (add a (mul w (⟨(i : Int), M + 1⟩ : Q))).den :=
    add_den_pos had (Qmul_den_pos hw hqid)
  have hlo_qp : Qle a (add a (mul w (⟨(i : Int), M + 1⟩ : Q))) := Qle_self_add hmul_nn
  have hqpn : 0 < (add a (mul w (⟨(i : Int), M + 1⟩ : Q))).num := qnum_pos_of_le han hqpd hlo_qp
  have step1 : Req (affineMap a w had hw (ofQ (⟨(i : Int), M + 1⟩ : Q) hqid))
      (ofQ (add a (mul w (⟨(i : Int), M + 1⟩ : Q))) hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ a had)) (Rmul_ofQ_ofQ hw hqid))
      (Radd_ofQ_ofQ had (Qmul_den_pos hw hqid))
  have hqi_le1 : Qle (⟨(i : Int), M + 1⟩ : Q) (⟨1, 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hmul_le : Qle (mul w (⟨(i : Int), M + 1⟩ : Q)) w :=
    Qle_trans (Qmul_den_pos hw (by decide)) (Qmul_le_mul_left hwn hqi_le1)
      (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
  have hqpaw : Qle (add a (mul w (⟨(i : Int), M + 1⟩ : Q))) (add a w) :=
    Qle_trans (add_den_pos had hw) (Qadd_le_add (Qle_refl a) hmul_le) (Qle_refl _)
  refine Req_trans ((productTest (reflectTest a han had (dilateTestR
      (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
      (clampS_absle S hSd hSn x) f)) (reflectTest a han had g)).hfc _ _ step1) ?_
  exact crossIntegrand_pt_zero f g a han had w hw hwn Bd hBdd hBdn hband hgh_f
    (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) hXge
    (add a (mul w (⟨(i : Int), M + 1⟩ : Q))) hqpd hqpn hlo_qp hqpaw

/-- **`F_{f,g}` inherits the compact support**: `F_{f,g}(x) = weight·H_{f,g}(x) ≈ weight·0 ≈ 0` for
    real `x ≥ Bd`. -/
theorem FTest_high_vanish (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (Bd : Q) (hBdd : 0 < Bd.den) (hBd0 : Qle (⟨0, 1⟩ : Q) Bd) (hBdS : Qle Bd S)
    (hband : Qle (add a w) (mul Bd a))
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (x : Real) (hx : Rle (ofQ Bd hBdd) x) :
    Req ((FTest B hBd hB1 N hN hBN f g S hSd hSn a han had w hw hwn).f x) zero := by
  show Req (Rmul (invSqrtF B hBd hB1 N hN hBN x)
      ((HcrossTest f g S hSd hSn a han had w hw hwn).f x)) zero
  exact Req_trans (Rmul_congr (Req_refl _)
      (HcrossTest_high_vanish f g S hSd hSn a han had w hw hwn Bd hBdd hBd0 hBdS hband hgh_f x hx))
    (Rmul_zero _)

-- ===========================================================================
-- (4) Biadditivity of the values.
-- ===========================================================================

/-- **`H_{f,g}` is additive in the FIRST argument at every real point**: the dilated slot of
    `L2Test.add` splits pointwise, then `haarIntegral_L2add`. -/
theorem HcrossTest_add_left (f₁ f₂ g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x : Real) :
    Req ((HcrossTest (L2Test.add f₁ f₂) g S hSd hSn a han had w hw hwn).f x)
        (Radd ((HcrossTest f₁ g S hSd hSn a han had w hw hwn).f x)
              ((HcrossTest f₂ g S hSd hSn a han had w hw hwn).f x)) := by
  show Req (haarIntegral (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
        (clampS_absle S hSd hSn x) (L2Test.add f₁ f₂))) (reflectTest a han had g))
      a han had a w had hw hwn) _
  refine Req_trans
    (haarIntegral_congr_window
      (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
        (clampS_absle S hSd hSn x) (L2Test.add f₁ f₂))) (reflectTest a han had g))
      (L2Test.add
        (productTest (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
          (clampS_absle S hSd hSn x) f₁)) (reflectTest a han had g))
        (productTest (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
          (clampS_absle S hSd hSn x) f₂)) (reflectTest a han had g)))
      a a han had han had a w had hw hwn
      (fun t _ _ => Rmul_congr (Rmul_distrib_right _ _ _) (Req_refl _)))
    (haarIntegral_L2add _ _ a han had a w had hw hwn)

/-- **`H_{f,g}` is additive in the SECOND argument at every real point** (the reflected outer slot
    splits, `Rmul_distrib`). -/
theorem HcrossTest_add_right (f g₁ g₂ : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x : Real) :
    Req ((HcrossTest f (L2Test.add g₁ g₂) S hSd hSn a han had w hw hwn).f x)
        (Radd ((HcrossTest f g₁ S hSd hSn a han had w hw hwn).f x)
              ((HcrossTest f g₂ S hSd hSn a han had w hw hwn).f x)) := by
  show Req (haarIntegral (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
        (clampS_absle S hSd hSn x) f)) (reflectTest a han had (L2Test.add g₁ g₂)))
      a han had a w had hw hwn) _
  refine Req_trans
    (haarIntegral_congr_window
      (productTest (reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
        (clampS_absle S hSd hSn x) f)) (reflectTest a han had (L2Test.add g₁ g₂)))
      (L2Test.add
        (productTest (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
          (clampS_absle S hSd hSn x) f)) (reflectTest a han had g₁))
        (productTest (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) S hSd hSn
          (clampS_absle S hSd hSn x) f)) (reflectTest a han had g₂)))
      a a han had han had a w had hw hwn
      (fun t _ _ => Rmul_congr (Rmul_distrib _ _ _) (Req_refl _)))
    (haarIntegral_L2add _ _ a han had a w had hw hwn)

/-- **`F_{f,g}` is additive in the FIRST argument at every real point** (weight distributes). -/
theorem FTest_add_left (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f₁ f₂ g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x : Real) :
    Req ((FTest B hBd hB1 N hN hBN (L2Test.add f₁ f₂) g S hSd hSn a han had w hw hwn).f x)
        (Radd ((FTest B hBd hB1 N hN hBN f₁ g S hSd hSn a han had w hw hwn).f x)
              ((FTest B hBd hB1 N hN hBN f₂ g S hSd hSn a han had w hw hwn).f x)) := by
  show Req (Rmul (invSqrtF B hBd hB1 N hN hBN x)
      ((HcrossTest (L2Test.add f₁ f₂) g S hSd hSn a han had w hw hwn).f x)) _
  refine Req_trans (Rmul_congr (Req_refl _)
    (HcrossTest_add_left f₁ f₂ g S hSd hSn a han had w hw hwn x)) ?_
  exact Rmul_distrib _ _ _

theorem FTest_add_right (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g₁ g₂ : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x : Real) :
    Req ((FTest B hBd hB1 N hN hBN f (L2Test.add g₁ g₂) S hSd hSn a han had w hw hwn).f x)
        (Radd ((FTest B hBd hB1 N hN hBN f g₁ S hSd hSn a han had w hw hwn).f x)
              ((FTest B hBd hB1 N hN hBN f g₂ S hSd hSn a han had w hw hwn).f x)) := by
  show Req (Rmul (invSqrtF B hBd hB1 N hN hBN x)
      ((HcrossTest f (L2Test.add g₁ g₂) S hSd hSn a han had w hw hwn).f x)) _
  refine Req_trans (Rmul_congr (Req_refl _)
    (HcrossTest_add_right f g₁ g₂ S hSd hSn a han had w hw hwn x)) ?_
  exact Rmul_distrib _ _ _

end UOR.Bridge.F1Square.Square
