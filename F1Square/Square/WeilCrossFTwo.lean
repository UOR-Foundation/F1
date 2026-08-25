/-
F1 square — **the two-sided normalized cross-correlation** `F⁺_{f,g}(x) = x^{-1/2}·H_{f,g}(x)` on the
positive band `[c, B]` (`WeilCrossFTwo.lean`) — the object the semantic Weil bridge needs BELOW `1`,
where the high-side `FTest` (weight clamped to `1`) is not `x^{-1/2}·H`.

WHAT IS BUILT (all over the two-sided weight `invSqrtTwoTest` of `WeilInvSqrtTwo`):
  • `FTwo f g = invSqrtTwoTest · HcrossTest f g` — an `L2Test`, genuinely `x^{-1/2}·H_{f,g}(x)` on `[c,B]`.
  • `FTwo_ofQ` — TWO-SIDED RATIONAL READBACK: `F⁺_{f,g}(q) ≈ BForm f g q` for every rational
    `c ≤ q ≤ B` (`q ≤ S`) — integer scales `n` AND reciprocal scales `1/n`.
  • `FTwo_eq_FTest_high` — AGREEMENT WITH THE HIGH-SIDE OBJECT: on `1 ≤ x ≤ B` (real), the two
    weights are the unique non-negative root of the same inert-clamp radicand, so
    `F⁺_{f,g}(x) ≈ F_{f,g}(x)`.
  • `FTwo_low_vanish` — LOW-SIDE COMPACT SUPPORT: `F⁺_{f,g}(x) ≈ 0` for real `0 ≤ x ≤ b·a` (the
    dilated factor `f(x/t)` has argument `≤ x/a ≤ b`, killed by `f`'s low support).
  • `FTwo_recip_int` — INTEGER-SCALE RECIPROCAL TRANSPOSE: `(1/n)·F⁺_{f,g}(1/n) ≈ F⁺_{g,f}(n)` for
    `1 ≤ n ≤ B` (`n ≤ S`) — from the readbacks and the PROVEN all-scale adjoint law
    `BForm_adjoint_swap_all`.  The real-scale law `x⁻¹F⁺_{f,g}(1/x) = F⁺_{g,f}(x)` needs the
    general-rational reciprocity + density extension — NOT built here.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilInvSqrtTwo
import F1Square.Square.WeilCrossF

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The two-sided normalized cross-correlation.
-- ===========================================================================

/-- **THE TWO-SIDED NORMALIZED CROSS-CORRELATION** `F⁺_{f,g} = x^{-1/2}·H_{f,g}` on `[c, B]`. -/
def FTwo (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : L2Test :=
  productTest (invSqrtTwoTest c B hcn hcd hBd hB1 hcB hc1 N hN hBN)
    (HcrossTest f g S hSd hSn a han had w hw hwn)

/-- **TWO-SIDED RATIONAL READBACK**: `F⁺_{f,g}(q) ≈ B_q(f,g)` for every rational `c ≤ q ≤ B`, `q ≤ S`. -/
theorem FTwo_ofQ (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (q : Q) (hqd : 0 < q.den) (hcq : Qle c q) (hqB : Qle q B) (hqS : Qle q S) :
    Req ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f (ofQ q hqd))
        (BForm f g q (qnum_pos_of_le hcn hqd hcq) hqd a han had w hw hwn) := by
  have hqn : 0 < q.num := qnum_pos_of_le hcn hqd hcq
  have hq0 : Qle (⟨0, 1⟩ : Q) q := by
    simp only [Qle]; push_cast; omega
  show Req (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN (ofQ q hqd))
        ((HcrossTest f g S hSd hSn a han had w hw hwn).f (ofQ q hqd)))
      (Rmul (normWeight q) (HForm f g q hqn hqd a han had w hw hwn))
  exact Rmul_congr (invSqrtTwoF_ofQ c B hcn hcd hBd hB1 hcB N hN hBN q hqd hcq hqB)
    (Req_symm (HForm_eq_HcrossTest f g q hqn hqd S hSd hSn a han had w hw hwn hq0 hqS))

-- ===========================================================================
-- (2) Agreement with the high-side object on `[1, B]`.
-- ===========================================================================

/-- On `1 ≤ x ≤ B` the two radicands agree (both clamps inert on the same band value). -/
theorem twoRad_eq_isqRad_high (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hc1 : Qle c (⟨1, 1⟩ : Q)) (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ B hBd)) :
    Req (twoRad c B hcn hcd hBd x) (isqRad B hBd x) := by
  have hcx : Rle (ofQ c hcd) x := Rle_trans (Rle_ofQ_ofQ hcd (by decide) hc1) hx1
  have hb2 : Req (twoBand c B hcd hBd x) x := qBandQ_eq_of_band hcx hxB
  have hb1 : Req (isqBand B hBd x) x := qBandQ_eq_of_band hx1 hxB
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ hcn hcd hcx
  refine Req_trans (clampedInv_congr c hcn hcd hb2) ?_
  refine Req_trans (clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hkx hcx) ?_
  refine Req_trans (Req_symm (clampedInv_eq_of_ge (a := (⟨1, 1⟩ : Q)) (han := by decide)
    (had := by decide) hkx hx1)) ?_
  exact Req_symm (clampedInv_congr (⟨1, 1⟩ : Q) (by decide) (by decide) hb1)

/-- On `1 ≤ x ≤ B` the two weights agree: `invSqrtTwoF x ≈ invSqrtF x` (unique root of the same
    radicand). -/
theorem invSqrtTwoF_eq_high (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ B hBd)) :
    Req (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) (invSqrtF B hBd hB1 N hN hBN x) :=
  RsqrtRealPos_unique (isqRad B hBd x) N hN (isqRad_scale B hBd hB1 N hN hBN x)
    (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x)
    (Req_trans (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x)
      (twoRad_eq_isqRad_high c B hcn hcd hBd hc1 x hx1 hxB))

/-- **AGREEMENT WITH THE HIGH-SIDE OBJECT**: on real `1 ≤ x ≤ B`, `F⁺_{f,g}(x) ≈ F_{f,g}(x)`. -/
theorem FTwo_eq_FTest_high (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ B hBd)) :
    Req ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f x)
        ((FTest B hBd hB1 N hN hBN f g S hSd hSn a han had w hw hwn).f x) := by
  rw [FTest_f]
  show Req (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
        ((HcrossTest f g S hSd hSn a han had w hw hwn).f x)) _
  exact Rmul_congr (invSqrtTwoF_eq_high c B hcn hcd hBd hB1 hcB hc1 N hN hBN x hx1 hxB) (Req_refl _)

-- ===========================================================================
-- (3) Low-side compact support: `H_{f,g}(x) ≈ 0` for real `0 ≤ x ≤ b·a` (inert clamp route).
-- ===========================================================================

/-- **Pointwise low-side vanishing at a window sample** `qp ≥ a`: the dilated factor `f(x·(1/qp))` has
    argument `≤ x/a ≤ b` for `0 ≤ x ≤ b·a`, killed by `f`'s low support. -/
theorem crossIntegrand_low_pt_zero (f g : L2Test)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (x : Real) (hx0 : Rle zero x)
    (hxba : Rle x (ofQ (mul b a) (Qmul_den_pos hbd had)))
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp) :
    Req (Rmul (f.f (Rmul x (clampedInv a han had (ofQ qp hqpd))))
          ((reflectTest a han had g).f (ofQ qp hqpd))) zero := by
  have hclamp : Req (clampedInv a han had (ofQ qp hqpd)) (ofQ (Qinv qp) (Qinv_den_pos hqpn)) :=
    clampedInv_ofQ han had hqpd hqpn haqp
  have hinv_le : Qle (Qinv qp) (Qinv a) := Qinv_antitone hqpn han haqp
  have hnn1a : Rnonneg (ofQ (Qinv a) (Qinv_den_pos han)) :=
    Rnonneg_ofQ (Qinv_den_pos han) (Int.le_of_lt (Qinv_num_pos had))
  have hxnn : Rnonneg x := Rnonneg_of_Rle_zero hx0
  -- x·(1/qp) ≤ x·(1/a) ≤ (b·a)·(1/a) ≈ b
  have hQ : Qeq (mul (mul b a) (Qinv a)) b := by
    have ht : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg (Int.le_of_lt han)
    show (b.num * a.num * (a.den : Int)) * (b.den : Int)
      = b.num * ((b.den * a.den * a.num.toNat : Nat) : Int)
    push_cast [ht]
    ring_uor
  have harg : Rle (Rmul x (clampedInv a han had (ofQ qp hqpd))) (ofQ b hbd) := by
    refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl x) hclamp)) ?_
    refine Rle_trans (Rmul_le_Rmul_left hxnn
      (Rle_ofQ_ofQ (Qinv_den_pos hqpn) (Qinv_den_pos han) hinv_le)) ?_
    refine Rle_trans (Rmul_le_Rmul_right hnn1a hxba) ?_
    refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos hbd had) (Qinv_den_pos han)) ?_)
    exact ofQ_congr (Qmul_den_pos (Qmul_den_pos hbd had) (Qinv_den_pos han)) hbd hQ
  exact Req_trans (Rmul_congr (hgl_f _ harg) (Req_refl _))
    (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- **LOW-SIDE COMPACT SUPPORT**: for real `0 ≤ x ≤ b·a` (with `x ≤ S`), `H_{f,g}(x) ≈ 0`.  The scale
    clamp is inert (`qBandQ_eq_of_band`), so the value is the genuine convolution at `x`
    (`mulConvR_congr`), whose window samples vanish by `crossIntegrand_low_pt_zero`. -/
theorem HcrossTest_low_vanish (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (x : Real) (hx0 : Rle zero x) (hxS : Rle x (ofQ S hSd))
    (hxba : Rle x (ofQ (mul b a) (Qmul_den_pos hbd had))) :
    Req ((HcrossTest f g S hSd hSn a han had w hw hwn).f x) zero := by
  rw [HcrossTest_f]
  have hxabs : Rle (Rabs x) (ofQ S hSd) :=
    Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_of_Rle_zero hx0))) hxS
  have hclamp : Req (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd x) x := qBandQ_eq_of_band hx0 hxS
  refine Req_trans (mulConvR_congr f (reflectTest a han had g) _ x S hSd hSn
    (clampS_absle S hSd hSn x) hxabs a han had a w had hw hwn hclamp) ?_
  show Req (haarIntegral (productTest (reflectTest a han had (dilateTestR x S hSd hSn hxabs f))
      (reflectTest a han had g)) a han had a w had hw hwn) zero
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
  refine Req_trans ((productTest (reflectTest a han had (dilateTestR x S hSd hSn hxabs f))
      (reflectTest a han had g)).hfc _ _ step1) ?_
  exact crossIntegrand_low_pt_zero f g a han had b hbd hbn hgl_f x hx0 hxba
    (add a (mul w (⟨(i : Int), M + 1⟩ : Q))) hqpd hqpn hlo_qp

/-- `F⁺_{f,g}` inherits the low-side compact support. -/
theorem FTwo_low_vanish (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (x : Real) (hx0 : Rle zero x) (hxS : Rle x (ofQ S hSd))
    (hxba : Rle x (ofQ (mul b a) (Qmul_den_pos hbd had))) :
    Req ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f x) zero := by
  show Req (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
      ((HcrossTest f g S hSd hSn a han had w hw hwn).f x)) zero
  exact Req_trans (Rmul_congr (Req_refl _)
    (HcrossTest_low_vanish f g S hSd hSn a han had w hw hwn b hbd hbn hgl_f x hx0 hxS hxba))
    (Rmul_zero _)

-- ===========================================================================
-- (4) Integer-scale reciprocal transpose of the two-sided object.
-- ===========================================================================

/-- **INTEGER-SCALE RECIPROCAL TRANSPOSE**: `(1/(m+1))·F⁺_{f,g}(1/(m+1)) ≈ F⁺_{g,f}(m+1)` for
    `1 ≤ m`, `m+1 ≤ B`, `m+1 ≤ S` — the two-sided readbacks at `1/(m+1)` and `m+1` joined by the
    PROVEN all-scale adjoint law `BForm_adjoint_swap_all` (`B_{1/n}(f,g) = n·B_n(g,f)`). -/
theorem FTwo_recip_int (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (m : Nat) (hm : 1 ≤ m)
    (hcm : Qle c (⟨1, m + 1⟩ : Q)) (hmB : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) B)
    (hmS : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) S) :
    Req (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
          ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f
            (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))))
        ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN g f S hSd hSn a han had w hw hwn).f
          (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)) := by
  have hrecB : Qle (⟨1, m + 1⟩ : Q) B := by
    have h1 : Qle (⟨1, m + 1⟩ : Q) (⟨1, 1⟩ : Q) := by simp only [Qle]; push_cast; omega
    exact Qle_trans (by decide) h1 hB1
  have hrecS : Qle (⟨1, m + 1⟩ : Q) S := by
    have h1 : Qle (⟨1, m + 1⟩ : Q) (⟨1, 1⟩ : Q) := by simp only [Qle]; push_cast; omega
    have hS1 : Qle (⟨1, 1⟩ : Q) S :=
      Qle_trans Nat.one_pos (by simp only [Qle]; push_cast; omega) hmS
    exact Qle_trans (by decide) h1 hS1
  have hcint : Qle c (⟨((m + 1 : Nat) : Int), 1⟩ : Q) :=
    Qle_trans (by decide) hc1 (by simp only [Qle]; push_cast; omega)
  have hlo := FTwo_ofQ c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn
    (⟨1, m + 1⟩ : Q) (Nat.succ_pos m) hcm hrecB hrecS
  have hhi := FTwo_ofQ c B hcn hcd hBd hB1 hcB hc1 N hN hBN g f S hSd hSn a han had w hw hwn
    (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos hcint hmB hmS
  -- (1/n)·B_{1/n}(f,g) ≈ (1/n)·(n·B_n(g,f)) ≈ B_n(g,f)
  refine Req_trans (Rmul_congr (Req_refl _) hlo) ?_
  refine Req_trans (Rmul_congr (Req_refl _)
    (BForm_adjoint_swap_all f g a han had w hw hwn b hbd hbn m hm hgh_g hgl_f hfit)) ?_
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
    (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) _)) ?_
  refine Req_trans (Rmul_congr (ofQ_recip_one m) (Req_refl _)) ?_
  exact Req_trans (Rone_mul _) (Req_symm hhi)

end UOR.Bridge.F1Square.Square
