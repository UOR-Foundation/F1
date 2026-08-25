/-
F1 square — **the REAL-scale reciprocal transpose of the two-sided normalized correlation**
(`WeilRecipReal.lean`):

    `x⁻¹·F⁺_{f,g}(1/x) = F⁺_{g,f}(x)`   for every REAL `1 ≤ x ≤ hi`  (`hi ≤ B`, `hi ≤ S`)

— bridge item 2.  Route: the cross-correlation law `H_{f,g}(x) ≈ H_{g,f}(1/x)` holds at every
RATIONAL scale `q ≥ 1` (`HForm_recip_all_Q`, no overlap hypothesis) and both sides are rational-
Lipschitz in `x` (the `L2Test` certificate of `HcrossTest`, composed with the `1`-Lipschitz reciprocal
`1/x = clampedInv 1 x`), so the DENSITY PRINCIPLE (`Req_of_lipschitz_dense`) lifts it to every real
`x` of the band.  The weight identity `x⁻¹·w(1/x) = w(x)` (`w = invSqrtTwoF`, the two-sided `x^{-1/2}`)
is the unique-root argument `(x⁻¹·w(1/x))² = x⁻²·x = 1/x = w(x)²`.  The reciprocal `x⁻¹` is realized as
`clampedInv 1 x` (inert on `x ≥ 1`), so no positivity witness is threaded.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilDensity
import F1Square.Square.WeilRecipQ

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) `H_{f,g}(x) ≈ H_{g,f}(1/x)` at every real `1 ≤ x ≤ hi`, by density.
-- ===========================================================================

/-- The reciprocal composite `x ↦ H(1/max(x,1))` is rational-Lipschitz with `H`'s own modulus. -/
theorem Hcross_recip_lip (Hs : L2Test) (x y : Real) :
    Rle (Rabs (Rsub (Hs.f (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
                    (Hs.f (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) y))))
        (Rmul (ofQ Hs.L Hs.hLd) (Rabs (Rsub x y))) := by
  refine Rle_trans (Hs.hlip _ _) ?_
  refine Rmul_le_Rmul_left (Rnonneg_ofQ Hs.hLd Hs.hLn) ?_
  refine Rle_trans (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide) x y) ?_
  have hone : Req (ofQ (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q)))
        (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide)))) one :=
    Req_of_seq_Qeq (fun _ => by
      show Qeq (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (⟨1, 1⟩ : Q); decide)
  exact Rle_of_Req (Req_trans (Rmul_congr hone (Req_refl _)) (Rone_mul _))

/-- **THE REAL-SCALE CROSS-CORRELATION LAW**: `H_{f,g}(x) ≈ H_{g,f}(1/x)` for every real `1 ≤ x ≤ hi`
    (`hi ≤ S`), by rational density from `HForm_recip_all_Q`. -/
theorem Hcross_recip_real (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hi : Q) (hhid : 0 < hi.den) (hhi1 : Qle (⟨1, 1⟩ : Q) hi) (hhiS : Qle hi S)
    (x : Real) (hx1 : Rle one x) (hxhi : Rle x (ofQ hi hhid)) :
    Req ((HcrossTest f g S hSd hSn a han had w hw hwn).f x)
        ((HcrossTest g f S hSd hSn a han had w hw hwn).f
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)) := by
  refine Req_of_lipschitz_dense
    (fun t => (HcrossTest f g S hSd hSn a han had w hw hwn).f t)
    (fun t => (HcrossTest g f S hSd hSn a han had w hw hwn).f
      (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) t))
    (HcrossTest f g S hSd hSn a han had w hw hwn).L
    (HcrossTest g f S hSd hSn a han had w hw hwn).L
    (HcrossTest f g S hSd hSn a han had w hw hwn).hLd
    (HcrossTest f g S hSd hSn a han had w hw hwn).hLn
    (HcrossTest g f S hSd hSn a han had w hw hwn).hLd
    (HcrossTest g f S hSd hSn a han had w hw hwn).hLn
    (HcrossTest f g S hSd hSn a han had w hw hwn).hlip
    (Hcross_recip_lip (HcrossTest g f S hSd hSn a han had w hw hwn))
    (⟨1, 1⟩ : Q) hi (by decide) hhid hhi1 ?_ x hx1 hxhi
  -- rational agreement on [1, hi]
  intro q hqd hq1 hqhi
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  have hq0 : Qle (⟨0, 1⟩ : Q) q := by simp only [Qle]; push_cast; omega
  have hqS : Qle q S := Qle_trans hhid hqhi hhiS
  have hqi0 : Qle (⟨0, 1⟩ : Q) (Qinv q) := qinv_num_nonneg q
  have hqiS : Qle (Qinv q) S := by
    -- 1/q ≤ 1 ≤ S
    have h1 : Qle (Qinv q) (⟨1, 1⟩ : Q) := by
      have hqq := hq1
      simp only [Qle] at hqq
      show (q.den : Int) * ((1 : Nat) : Int) ≤ 1 * ((q.num.toNat : Nat) : Int)
      push_cast [Int.toNat_of_nonneg (Int.le_of_lt hqn)] at hqq ⊢
      omega
    exact Qle_trans (by decide) h1 (Qle_trans hhid hhi1 hhiS)
  -- H_{f,g}(q) ≈ H_q ≈ H_{1/q}(g,f) ≈ H_{g,f}(ofQ (1/q)) ≈ H_{g,f}(clampedInv 1 (ofQ q))
  refine Req_trans (Req_symm (HForm_eq_HcrossTest f g q hqn hqd S hSd hSn a han had w hw hwn hq0 hqS)) ?_
  refine Req_trans (HForm_recip_all_Q f g a han had w hw hwn b hbd hbn q hqn hqd hq1 hgh_f hgl_g hfit) ?_
  refine Req_trans (HForm_eq_HcrossTest g f (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn)
    S hSd hSn a han had w hw hwn hqi0 hqiS) ?_
  exact (HcrossTest g f S hSd hSn a han had w hw hwn).hfc _ _
    (Req_symm (clampedInv_ofQ (by decide) (by decide) hqd hqn hq1))

-- ===========================================================================
-- (2) The real weight identity `x⁻¹·w(1/x) = w(x)` and the reciprocal-transpose law.
-- ===========================================================================

/-- The two-sided radicand at `1/x` is `x` itself for real `1 ≤ x ≤ B` (`1/x ∈ [1/B, 1] ⊆ [c, B]`,
    both clamps inert). -/
theorem twoRad_recip (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hcB1 : Qle (mul c B) (⟨1, 1⟩ : Q)) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ B hBd)) :
    Req (twoRad c B hcn hcd hBd (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)) x := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx1
  -- 1/x = Rinv x
  have hinv : Req (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) (Rinv x kx hkx) :=
    clampedInv_eq_of_ge hkx hx1
  -- bounds: 1/B ≤ 1/x ≤ 1, hence c ≤ 1/x ≤ B
  have hinv_le1 : Rle (Rinv x kx hkx) one :=
    Rle_trans (Rinv_le_ofQ_inv (a := (⟨1, 1⟩ : Q)) (by decide) (by decide) hkx hx1)
      (Rle_of_Req (Req_of_seq_Qeq (fun _ => by
        show Qeq (Qinv (⟨1, 1⟩ : Q)) (⟨1, 1⟩ : Q); decide)))
  have hinv_ge : Rle (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rinv x kx hkx) := by
    -- (1/B)·x ≤ (1/B)·B = 1 = (1/x)·x … multiply through: (1/B) ≤ (1/x) since x ≤ B
    have hxr : Req (Rmul x (Rinv x kx hkx)) one := Rmul_Rinv_self hkx
    have hnnx : Rnonneg (Rinv x kx hkx) := Rnonneg_Rinv x kx hkx
    have hnnQ : Rnonneg (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
      Rnonneg_ofQ (Qinv_den_pos hBn) (Int.le_of_lt (Qinv_num_pos hBd))
    have hQ : Qeq (mul (Qinv B) B) (⟨1, 1⟩ : Q) :=
      Qeq_trans (Qmul_den_pos hBd (Qinv_den_pos hBn)) (Qmul_comm (Qinv B) B) (Qmul_Qinv hBn)
    have hL : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul x (Rinv x kx hkx)))
        (ofQ (Qinv B) (Qinv_den_pos hBn)) := Req_trans (Rmul_congr (Req_refl _) hxr) (Rmul_one _)
    have hstep : Rle (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul x (Rinv x kx hkx)))
        (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (Rinv x kx hkx))) :=
      Rmul_le_Rmul_left hnnQ (Rmul_le_Rmul_right hnnx hxB)
    have hR : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (Rinv x kx hkx)))
        (Rinv x kx hkx) := by
      refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
      refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hBn) hBd)
        (ofQ_congr (Qmul_den_pos (Qinv_den_pos hBn) hBd) (by decide) hQ)) (Req_refl _)) ?_
      exact Rone_mul _
    exact Rle_trans (Rle_of_Req (Req_symm hL)) (Rle_trans hstep (Rle_of_Req hR))
  have hc_le_invB : Qle c (Qinv B) := by
    have h := hcB1
    show c.num * ((B.num.toNat : Nat) : Int) ≤ (B.den : Int) * (c.den : Int)
    simp only [Qle, mul] at h
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hBn)] at h ⊢
    have hcomm : (B.den : Int) * (c.den : Int) = (c.den : Int) * (B.den : Int) := Int.mul_comm _ _
    omega
  have hc_inv : Rle (ofQ c hcd) (Rinv x kx hkx) :=
    Rle_trans (Rle_ofQ_ofQ hcd (Qinv_den_pos hBn) hc_le_invB) hinv_ge
  have hinv_B : Rle (Rinv x kx hkx) (ofQ B hBd) :=
    Rle_trans hinv_le1 (Rle_ofQ_ofQ (by decide) hBd hB1)
  -- radicand at 1/x: band inert, clamp inert, so it is 1/(1/x) = x
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ hcn hcd hc_inv
  have hband : Req (twoBand c B hcd hBd (Rinv x kx hkx)) (Rinv x kx hkx) :=
    qBandQ_eq_of_band hc_inv hinv_B
  refine Req_trans (twoRad_congr c B hcn hcd hBd hinv) ?_
  show Req (clampedInv c hcn hcd (twoBand c B hcd hBd (Rinv x kx hkx))) x
  refine Req_trans (clampedInv_congr c hcn hcd hband) ?_
  refine Req_trans (clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hki hc_inv) ?_
  -- Rinv (Rinv x) ≈ x  (both are the multiplicative inverse of Rinv x)
  have h1 : Req (Rmul (Rinv x kx hkx) (Rinv (Rinv x kx hkx) ki hki)) one := Rmul_Rinv_self hki
  have h2 : Req (Rmul (Rinv x kx hkx) x) one :=
    Req_trans (Rmul_comm _ _) (Rmul_Rinv_self hkx)
  -- cancel the common nonzero factor Rinv x: u·y = 1 = u·x with u·x' … use x = x·(u·y) = (x·u)·y = y
  refine Req_symm ?_
  refine Req_trans (Req_symm (Rmul_one x)) ?_
  refine Req_trans (Rmul_congr (Req_refl x) (Req_symm h1)) ?_
  refine Req_trans (Req_symm (Rmul_assoc x (Rinv x kx hkx) (Rinv (Rinv x kx hkx) ki hki))) ?_
  refine Req_trans (Rmul_congr (Rmul_Rinv_self hkx) (Req_refl _)) ?_
  exact Rone_mul _

/-- **THE REAL WEIGHT IDENTITY** `x⁻¹·w(1/x) ≈ w(x)` for real `1 ≤ x ≤ B` (`w` the two-sided
    `x^{-1/2}`): both sides are non-negative with square `1/x` (`(x⁻¹·w(1/x))² = x⁻²·x`). -/
theorem invSqrtTwoF_recip (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hcB1 : Qle (mul c B) (⟨1, 1⟩ : Q))
    (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ B hBd)) :
    Req (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
          (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN
            (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)))
        (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) := by
  have hrad := twoRad_recip c B hcn hcd hBd hcB1 hB1 x hx1 hxB
  -- the radicand at x is 1/x (band and clamp inert on [1,B] ∋ x)
  have hcx : Rle (ofQ c hcd) x := Rle_trans (Rle_ofQ_ofQ hcd (by decide) hc1) hx1
  have hbandx : Req (twoBand c B hcd hBd x) x := qBandQ_eq_of_band hcx hxB
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ hcn hcd hcx
  have hradx : Req (twoRad c B hcn hcd hBd x) (Rinv x kx hkx) :=
    Req_trans (clampedInv_congr c hcn hcd hbandx)
      (clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hkx hcx)
  have hinvx : Req (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) (Rinv x kx hkx) :=
    clampedInv_eq_of_ge hkx hx1
  -- y := x⁻¹·w(1/x) is nonneg with y² = x⁻²·(w(1/x))² = x⁻²·x = x⁻¹ = rad(x)
  have hnn : Rnonneg (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
      (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) :=
    Rnonneg_Rmul (Rnonneg_clampedInv _ _ _ _) (invSqrtTwoF_nonneg _ _ _ _ _ _ _ _ _ _ _)
  have hsq : Req (Rmul
        (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
          (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)))
        (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
          (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))))
      (twoRad c B hcn hcd hBd x) := by
    refine Req_trans (Rmul_mul_mul_comm _ _ _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (invSqrtTwoF_sq _ _ _ _ _ _ _ _ _ _ _)) ?_
    refine Req_trans (Rmul_congr (Rmul_congr hinvx hinvx) hrad) ?_
    -- (1/x)·(1/x)·x = 1/x ≈ rad x
    refine Req_trans (Rmul_assoc _ _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) (Rmul_Rinv_self hkx))) ?_
    exact Req_trans (Rmul_one _) (Req_symm hradx)
  exact RsqrtRealPos_unique (twoRad c B hcn hcd hBd x) N hN
    (twoRad_scale c B hcn hcd hBd hB1 hcB N hN hBN x) hnn hsq

/-- **★★ THE REAL-SCALE RECIPROCAL TRANSPOSE** `x⁻¹·F⁺_{f,g}(1/x) ≈ F⁺_{g,f}(x)` for every real
    `1 ≤ x ≤ hi` (`hi ≤ B`, `hi ≤ S`, `c·B ≤ 1`) — bridge item 2.  The reciprocal `x⁻¹` and the
    argument `1/x` are both `clampedInv 1 x` (inert on `x ≥ 1`). -/
theorem FTwo_recip_real (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (hcB1 : Qle (mul c B) (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (f g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hi : Q) (hhid : 0 < hi.den) (hhi1 : Qle (⟨1, 1⟩ : Q) hi) (hhiS : Qle hi S) (hhiB : Qle hi B)
    (x : Real) (hx1 : Rle one x) (hxhi : Rle x (ofQ hi hhid)) :
    Req (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
          ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN f g S hSd hSn a han had w hw hwn).f
            (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)))
        ((FTwo c B hcn hcd hBd hB1 hcB hc1 N hN hBN g f S hSd hSn a han had w hw hwn).f x) := by
  have hxB : Rle x (ofQ B hBd) := Rle_trans hxhi (Rle_ofQ_ofQ hhid hBd hhiB)
  -- H_{g,f}(x) ≈ H_{f,g}(1/x)   (the law with f,g swapped)
  have hH : Req ((HcrossTest g f S hSd hSn a han had w hw hwn).f x)
      ((HcrossTest f g S hSd hSn a han had w hw hwn).f
        (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)) :=
    Hcross_recip_real g f S hSd hSn a han had w hw hwn b hbd hbn hgh_g hgl_f hfit
      hi hhid hhi1 hhiS x hx1 hxhi
  have hW := invSqrtTwoF_recip c B hcn hcd hBd hB1 hcB hcB1 hc1 N hN hBN x hx1 hxB
  show Req (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
      (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN
              (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
            ((HcrossTest f g S hSd hSn a han had w hw hwn).f
              (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))))
    (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
          ((HcrossTest g f S hSd hSn a han had w hw hwn).f x))
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  exact Rmul_congr hW (Req_symm hH)

end UOR.Bridge.F1Square.Square
