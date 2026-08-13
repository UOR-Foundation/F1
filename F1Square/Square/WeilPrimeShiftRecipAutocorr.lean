/-
F1 square — **the autocorrelation reciprocal self-duality** (`WeilPrimeShiftRecipAutocorr.lean`):
the pivotal Haar change-of-variables `autocorr g n ≈ autocorr g (1/n)`.

Target: autocorr g ⟨n,1⟩ ≈ autocorr g ⟨1,n⟩  (the autocorrelation point value is reciprocal
symmetric: h(n) ≈ h(1/n)), on a window bounded away from 0 with g of compact support in the band.

Route D (dilation + support-window reconciliation), using only the LINEAR (already-built) Haar
change of variables `haarIntegral_dilate`, the general split-at-a-node additivity
`riemannIntegralI_split_at`, the window congruences, and g's compact support.
-/
import F1Square.Square.Autocorr
import F1Square.Square.HaarInvariant
import F1Square.Square.IntervalSplitAtCap
import F1Square.Square.WeilPrimeShiftAutocorr
import F1Square.Square.MellinLinear
import F1Square.Analysis.IntervalCert

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Reusable wrappers on `haarIntegral` (= riemannIntegralI of the product certificate
-- of the test with `recipTest`).
-- ===========================================================================

/-- **Window-`Qeq` congruence of the Haar integral** — the endpoints are seen only through `Qeq`. -/
theorem haarIntegral_congr_Q (φ : L2Test) (af : Q) (hn : 0 < af.num) (hd : 0 < af.den)
    (lo w lo' w' : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hlo' : 0 < lo'.den) (hw' : 0 < w'.den) (hwn' : 0 ≤ w'.num)
    (hqa : Qeq lo lo') (hqw : Qeq w w') :
    Req (haarIntegral φ af hn hd lo w hlo hw hwn)
        (haarIntegral φ af hn hd lo' w' hlo' hw' hwn') :=
  riemannIntegralI_congr_Q (l2L_den φ (recipTest af hn hd)) (l2L_num φ (recipTest af hn hd))
    (l2lip φ (recipTest af hn hd)) (l2fc φ (recipTest af hn hd)) lo w lo' w'
    hlo hw hwn hlo' hw' hwn' hqa hqw

/-- **The Haar integral splits at an arbitrary rational node** `0 < w1 ≤ w`. -/
theorem haarIntegral_split_at (φ : L2Test) (af : Q) (hn : 0 < af.num) (hd : 0 < af.den)
    (lo w w1 : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hw1 : 0 < w1.den) (hw1n : 0 < w1.num) (hle : Qle w1 w) (hw2n : 0 ≤ (Qsub w w1).num) :
    Req (haarIntegral φ af hn hd lo w hlo hw hwn)
        (Radd (haarIntegral φ af hn hd lo w1 hlo hw1 (Int.le_of_lt hw1n))
              (haarIntegral φ af hn hd (add lo w1) (Qsub w w1)
                (add_den_pos hlo hw1) (Qsub_den_pos hw hw1) hw2n)) :=
  riemannIntegralI_split_at (l2L_den φ (recipTest af hn hd)) (l2L_num φ (recipTest af hn hd))
    (l2lip φ (recipTest af hn hd)) (l2fc φ (recipTest af hn hd)) lo w w1
    hlo hw hwn hw1 hw1n hle hw2n

/-- **Windowed congruence of the Haar integral across possibly different floors**: if the two product
    integrands (test·density) agree on the window `[lo, lo+w]`, the two Haar integrals agree. The two
    Lipschitz moduli are reconciled at their common weakening `Lc = l2L φ ρ + l2L ψ ρ'`. -/
theorem haarIntegral_congr_window (φ ψ : L2Test) (af af' : Q)
    (hn : 0 < af.num) (hd : 0 < af.den) (hn' : 0 < af'.num) (hd' : 0 < af'.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hagree : ∀ x, Rle zero x → Rle x one →
      Req (Rmul (φ.f (affineMap lo w hlo hw x)) (clampedInv af hn hd (affineMap lo w hlo hw x)))
          (Rmul (ψ.f (affineMap lo w hlo hw x)) (clampedInv af' hn' hd' (affineMap lo w hlo hw x)))) :
    Req (haarIntegral φ af hn hd lo w hlo hw hwn)
        (haarIntegral ψ af' hn' hd' lo w hlo hw hwn) := by
  have Lcd : 0 < (add (l2L φ (recipTest af hn hd)) (l2L ψ (recipTest af' hn' hd'))).den :=
    add_den_pos (l2L_den φ (recipTest af hn hd)) (l2L_den ψ (recipTest af' hn' hd'))
  have Lcn : 0 ≤ (add (l2L φ (recipTest af hn hd)) (l2L ψ (recipTest af' hn' hd'))).num :=
    Qadd_num_nonneg_loc (l2L_num φ (recipTest af hn hd)) (l2L_num ψ (recipTest af' hn' hd'))
  -- weaken both product certificates to the common modulus `Lc = l2L φ ρ + l2L ψ ρ'`
  have hφw : ∀ x y, Rle (Rabs (Rsub (Rmul (φ.f x) ((recipTest af hn hd).f x))
        (Rmul (φ.f y) ((recipTest af hn hd).f y))))
      (Rmul (ofQ (add (l2L φ (recipTest af hn hd)) (l2L ψ (recipTest af' hn' hd'))) Lcd)
        (Rabs (Rsub x y))) := fun x y =>
    lip_mono (l2L_den φ (recipTest af hn hd)) Lcd (Qle_self_add (l2L_num ψ (recipTest af' hn' hd')))
      (Rnonneg_Rabs (Rsub x y)) (l2lip φ (recipTest af hn hd) x y)
  have hψw : ∀ x y, Rle (Rabs (Rsub (Rmul (ψ.f x) ((recipTest af' hn' hd').f x))
        (Rmul (ψ.f y) ((recipTest af' hn' hd').f y))))
      (Rmul (ofQ (add (l2L φ (recipTest af hn hd)) (l2L ψ (recipTest af' hn' hd'))) Lcd)
        (Rabs (Rsub x y))) := fun x y =>
    lip_mono (l2L_den ψ (recipTest af' hn' hd')) Lcd
      (Qle_self_add_l (l2L_num φ (recipTest af hn hd)))
      (Rnonneg_Rabs (Rsub x y)) (l2lip ψ (recipTest af' hn' hd') x y)
  -- haarIntegral φ = RI(φρ, l2L φρ) ≈ RI(φρ, Lc) ≈ RI(ψρ', Lc) ≈ RI(ψρ', l2L ψρ') = haarIntegral ψ
  refine Req_trans
    (riemannIntegralI_certif_irrel (l2L_den φ (recipTest af hn hd)) (l2L_num φ (recipTest af hn hd))
      (l2lip φ (recipTest af hn hd)) (l2fc φ (recipTest af hn hd))
      Lcd Lcn hφw (l2fc φ (recipTest af hn hd)) lo w hlo hw hwn) ?_
  refine Req_trans
    (riemannIntegralI_congr_unit Lcd Lcn hφw (l2fc φ (recipTest af hn hd)) hψw
      (l2fc ψ (recipTest af' hn' hd')) lo w hlo hw hwn hagree) ?_
  exact riemannIntegralI_certif_irrel Lcd Lcn hψw (l2fc ψ (recipTest af' hn' hd'))
    (l2L_den ψ (recipTest af' hn' hd')) (l2L_num ψ (recipTest af' hn' hd'))
    (l2lip ψ (recipTest af' hn' hd')) (l2fc ψ (recipTest af' hn' hd')) lo w hlo hw hwn

-- ===========================================================================
-- Rational-point value of the convolution integrand `Ps = (dilate s g)^τ · g^τ`.
-- ===========================================================================

/-- **The convolution integrand at a rational point `Qv ≥ a`**: with `Ps` the product of the reflected
    `s`-dilation of `g` and the reflected `g`, `Ps(Qv) ≈ g(s/Qv)·g(1/Qv)`. Both factors are read by
    `reflectTest_ofQ`; the first `dilateTest`-factor's argument is `s·(1/Qv)`. -/
theorem Ps_ofQ (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (s : Q) (hsn : 0 < s.num) (hsd : 0 < s.den) (Qv : Q) (hQd : 0 < Qv.den) (hQn : 0 < Qv.num)
    (haQ : Qle a Qv) :
    Req ((productTest (reflectTest a han had (dilateTest s hsn hsd g)) (reflectTest a han had g)).f
          (ofQ Qv hQd))
        (Rmul (g.f (ofQ (mul s (Qinv Qv)) (Qmul_den_pos hsd (Qinv_den_pos hQn))))
              (g.f (ofQ (Qinv Qv) (Qinv_den_pos hQn)))) :=
  Rmul_congr
    (Req_trans (reflectTest_ofQ a Qv han had hQd hQn haQ (dilateTest s hsn hsd g))
      (g.hfc _ _ (Rmul_ofQ_ofQ hsd (Qinv_den_pos hQn))))
    (reflectTest_ofQ a Qv han had hQd hQn haQ g)

-- ===========================================================================
-- Pointwise support vanishing of the two convolution integrands.
-- ===========================================================================

/-- **The reciprocal-scale collapse** `n·(1/(n·qp)) = 1/qp` (as `Qeq`). -/
theorem mul_n_Qinv_mul_n (n : Nat) (qp : Q) (hqpn : 0 < qp.num) :
    Qeq (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) qp))) (Qinv qp) := by
  have hq : (0 : Int) ≤ qp.num := Int.le_of_lt hqpn
  have hnq : (0 : Int) ≤ (n : Int) * qp.num := Int.mul_nonneg (Int.ofNat_nonneg n) hq
  simp only [Qeq, mul, Qinv]
  push_cast [Int.toNat_of_nonneg hq, Int.toNat_of_nonneg hnq]
  simp only [Int.one_mul, Int.mul_assoc]
  exact Int.mul_left_comm _ _ _

/-- **High-side vanishing at a sample point** `qp ≤ a`: the dilated autocorr integrand
    `dilateTest n Pn` vanishes at `ofQ qp` — its first factor is `g(1/qp)` and `1/qp ≥ 1/a`. -/
theorem dilDN_pt_zero (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num)
    (hqp_le_a : Qle qp a) (hnqp_ge_a : Qle a (mul (⟨(n : Int), 1⟩ : Q) qp)) :
    Req ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
           (productTest (reflectTest a han had
                (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos g))
              (reflectTest a han had g))).f (ofQ qp hqpd)) zero := by
  have hmn : 0 < (mul (⟨(n : Int), 1⟩ : Q) qp).num :=
    Int.mul_pos (by show (0 : Int) < (n : Int); exact_mod_cast hn0) hqpn
  have hmd : 0 < (mul (⟨(n : Int), 1⟩ : Q) qp).den := Qmul_den_pos Nat.one_pos hqpd
  -- (dilateTest n Pn)(ofQ qp) ≈ Pn(ofQ (n·qp))
  have e1 : Req ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
        (productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos g))
          (reflectTest a han had g))).f (ofQ qp hqpd))
      ((productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos g))
          (reflectTest a han had g)).f (ofQ (mul (⟨(n : Int), 1⟩ : Q) qp) hmd)) :=
    (productTest (reflectTest a han had
        (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos g))
      (reflectTest a han had g)).hfc _ _ (Rmul_ofQ_ofQ Nat.one_pos hqpd)
  -- Pn(ofQ (n·qp)) ≈ g(n·(1/(n·qp)))·g(1/(n·qp))
  have e2 := Ps_ofQ g a han had (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
    (mul (⟨(n : Int), 1⟩ : Q) qp) hmd hmn hnqp_ge_a
  -- first factor arg 1/qp ≥ 1/a, so g = 0
  have hfle : Qle (Qinv a)
      (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) qp))) :=
    Qle_trans (Qinv_den_pos hqpn) (Qinv_antitone han hqpn hqp_le_a)
      (Qeq_le (Qeq_symm (mul_n_Qinv_mul_n n qp hqpn)))
  have hfz : Req (g.f (ofQ (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) qp)))
        (Qmul_den_pos Nat.one_pos (Qinv_den_pos hmn)))) zero :=
    hgh _ (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hmn)) hfle)
  refine Req_trans e1 (Req_trans e2 ?_)
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- **Low-side vanishing at a sample point** `1 ≤ n·b·qp`: the autocorr integrand `P1n` at reciprocal
    scale `1/n` vanishes at `ofQ qp` — its first factor is `g(1/(n·qp))` and `1/(n·qp) ≤ b`. -/
theorem P1n_pt_zero (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (b : Q) (hbd : 0 < b.den) (_hbn : 0 < b.num)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp)
    (hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) qp)) :
    Req ((productTest (reflectTest a han had
           (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g)) (reflectTest a han had g)).f
          (ofQ qp hqpd)) zero := by
  have e2 := Ps_ofQ g a han had (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 qp hqpd hqpn haqp
  have hlow : Qle (mul (⟨1, n⟩ : Q) (Qinv qp)) b := qlow_engine b n hqpn hbig
  have hfz : Req (g.f (ofQ (mul (⟨1, n⟩ : Q) (Qinv qp))
        (Qmul_den_pos hn0 (Qinv_den_pos hqpn)))) zero :=
    hgl _ (Rle_ofQ_ofQ (Qmul_den_pos hn0 (Qinv_den_pos hqpn)) hbd hlow)
  refine Req_trans e2 ?_
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

-- ===========================================================================
-- Window vanishing of the two integrands, via `haarIntegral_window_vanish`.
-- ===========================================================================

/-- **The dilated high-side integrand vanishes over a window sitting at/below `a`** (with `a ≤ n·lo`):
    every sample `qp ≤ lo+w ≤ a`, and `n·qp ≥ n·lo ≥ a`, so `dilDN_pt_zero` fires. -/
theorem left_DN_window_vanish (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (af : Q) (hafn : 0 < af.num) (hafd : 0 < af.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (H1 : Qle (add lo w) a) (H2 : Qle a (mul (⟨(n : Int), 1⟩ : Q) lo)) :
    Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
             Nat.one_pos
             (productTest (reflectTest a han had
                  (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                    Nat.one_pos g)) (reflectTest a han had g)))
          af hafn hafd lo w hlo hw hwn) zero := by
  refine haarIntegral_window_vanish _ af hafn hafd lo w hlo hw hwn ?_
  intro N i hi
  have hqid : (0 : Nat) < N + 1 := Nat.succ_pos N
  have hmul_nn : (0 : Int) ≤ (mul w (⟨(i : Int), N + 1⟩ : Q)).num := by
    show (0 : Int) ≤ w.num * (i : Int); exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hqpd : 0 < (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))).den :=
    add_den_pos hlo (Qmul_den_pos hw hqid)
  have hlo_qp : Qle lo (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) := Qle_self_add hmul_nn
  have hqpn : 0 < (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))).num := qnum_pos_of_le hlon hqpd hlo_qp
  have step1 : Req (affineMap lo w hlo hw (ofQ (⟨(i : Int), N + 1⟩ : Q) hqid))
      (ofQ (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ lo hlo)) (Rmul_ofQ_ofQ hw hqid))
      (Radd_ofQ_ofQ hlo (Qmul_den_pos hw hqid))
  -- qp ≤ a
  have hqi_le1 : Qle (⟨(i : Int), N + 1⟩ : Q) (⟨1, 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hmul_le : Qle (mul w (⟨(i : Int), N + 1⟩ : Q)) w :=
    Qle_trans (Qmul_den_pos hw (by decide)) (Qmul_le_mul_left hwn hqi_le1)
      (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
  have hqp_le_a : Qle (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) a :=
    Qle_trans (add_den_pos hlo hw) (Qadd_le_add (Qle_refl lo) hmul_le) H1
  -- n·qp ≥ a
  have hnqp_ge_a : Qle a (mul (⟨(n : Int), 1⟩ : Q) (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))) :=
    Qle_trans (Qmul_den_pos Nat.one_pos hlo) H2
      (Qmul_le_mul_left (Int.ofNat_nonneg n) hlo_qp)
  exact Req_trans
    ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
        (productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
              Nat.one_pos g)) (reflectTest a han had g))).hfc _ _ step1)
    (dilDN_pt_zero g a han had n hn0 hgh (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) hqpd hqpn
      hqp_le_a hnqp_ge_a)

/-- **The low-side integrand vanishes over a window sitting at/above `(a+w)/n`** (with `a ≤ lo` and
    `1 ≤ n·b·lo`): every sample `qp ≥ lo ≥ a`, and `n·b·qp ≥ n·b·lo ≥ 1`, so `P1n_pt_zero` fires. -/
theorem right_I1n_window_vanish (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (Ha : Qle a lo) (Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) lo)) :
    Req (haarIntegral (productTest (reflectTest a han had
             (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g)) (reflectTest a han had g))
          a han had lo w hlo hw hwn) zero := by
  refine haarIntegral_window_vanish _ a han had lo w hlo hw hwn ?_
  intro N i hi
  have hqid : (0 : Nat) < N + 1 := Nat.succ_pos N
  have hmul_nn : (0 : Int) ≤ (mul w (⟨(i : Int), N + 1⟩ : Q)).num := by
    show (0 : Int) ≤ w.num * (i : Int); exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hqpd : 0 < (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))).den :=
    add_den_pos hlo (Qmul_den_pos hw hqid)
  have hlo_qp : Qle lo (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) := Qle_self_add hmul_nn
  have hqpn : 0 < (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))).num := qnum_pos_of_le hlon hqpd hlo_qp
  have step1 : Req (affineMap lo w hlo hw (ofQ (⟨(i : Int), N + 1⟩ : Q) hqid))
      (ofQ (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ lo hlo)) (Rmul_ofQ_ofQ hw hqid))
      (Radd_ofQ_ofQ hlo (Qmul_den_pos hw hqid))
  have haqp : Qle a (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) := Qle_trans hlo Ha hlo_qp
  have hnb_nn : (0 : Int) ≤ (mul (⟨(n : Int), 1⟩ : Q) b).num := by
    show (0 : Int) ≤ (n : Int) * b.num
    exact Int.mul_nonneg (Int.ofNat_nonneg n) (Int.le_of_lt hbn)
  have hbig : Qle (⟨1, 1⟩ : Q)
      (mul (mul (⟨(n : Int), 1⟩ : Q) b) (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))) :=
    Qle_trans (Qmul_den_pos (Qmul_den_pos Nat.one_pos hbd) hlo) Hbig
      (Qmul_le_mul_left hnb_nn hlo_qp)
  exact Req_trans
    ((productTest (reflectTest a han had
        (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g))
      (reflectTest a han had g)).hfc _ _ step1)
    (P1n_pt_zero g a han had n hn0 b hbd hbn hgl (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn haqp hbig)

-- ===========================================================================
-- Rational arithmetic used to reconcile the two shifted windows.
-- ===========================================================================

/-- `a < Y ⟹ 0 < (Y − a).num`. -/
theorem Qsub_num_pos_of_lt {a Y : Q} (h : Qlt a Y) : 0 < (Qsub Y a).num := by
  simp only [Qsub, add, neg, Int.neg_mul]
  have h' : a.num * (Y.den : Int) < Y.num * (a.den : Int) := h
  omega

/-- `a ≤ Y ⟹ 0 ≤ (Y − a).num`. -/
theorem Qsub_num_nonneg_of_le {a Y : Q} (h : Qle a Y) : 0 ≤ (Qsub Y a).num := by
  simp only [Qsub, add, neg, Int.neg_mul]
  have h' : a.num * (Y.den : Int) ≤ Y.num * (a.den : Int) := h
  omega

/-- `n·((1/n)·x) = x` (as `Qeq`). -/
theorem n_mul_inv_n (n : Nat) (x : Q) :
    Qeq (mul (⟨(n : Int), 1⟩ : Q) (mul (⟨1, n⟩ : Q) x)) x := by
  simp only [Qeq, mul]; push_cast
  simp only [Int.one_mul, Int.mul_assoc]; exact Int.mul_left_comm _ _ _

/-- `(1/n)·X ≤ X` for `X ≥ 0`, `n ≥ 1`. -/
theorem inv_n_mul_le (X : Q) (hXn : 0 ≤ X.num) (n : Nat) (hn0 : 0 < n) :
    Qle (mul (⟨1, n⟩ : Q) X) X := by
  simp only [Qle, mul]; push_cast
  have hd : (0 : Int) ≤ X.num * (X.den : Int) := Int.mul_nonneg hXn (Int.ofNat_nonneg X.den)
  have h1n : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn0
  calc 1 * X.num * (X.den : Int) = X.num * (X.den : Int) * 1 := by rw [Int.one_mul, Int.mul_one]
    _ ≤ X.num * (X.den : Int) * (n : Int) := Int.mul_le_mul_of_nonneg_left h1n hd
    _ = X.num * ((n : Int) * (X.den : Int)) := by
          rw [Int.mul_assoc, Int.mul_comm (X.den : Int) (n : Int)]

/-- The DN split node `a − (a/n)` has positive numerator when `n ≥ 2`. -/
theorem w1_num_pos (a : Q) (han : 0 < a.num) (had : 0 < a.den) (n : Nat) (hn2 : 2 ≤ n) :
    0 < (Qsub a (mul (⟨1, n⟩ : Q) a)).num := by
  have e : (Qsub a (mul (⟨1, n⟩ : Q) a)).num = a.num * (a.den : Int) * ((n : Int) - 1) := by
    simp only [Qsub, add, neg, mul]; push_cast; ring_uor
  rw [e]
  have h2 : (0 : Int) < (n : Int) - 1 := by
    have h2n : (2 : Int) ≤ (n : Int) := by exact_mod_cast hn2
    omega
  exact Int.mul_pos (Int.mul_pos han (by exact_mod_cast had)) h2

/-- `n·a < a+w ⟹ a < (a+w)/n`. -/
theorem CoreStrict (a w : Q) (n : Nat)
    (hcore : Qlt (mul (⟨(n : Int), 1⟩ : Q) a) (add a w)) :
    Qlt a (mul (⟨1, n⟩ : Q) (add a w)) := by
  have hc := hcore
  simp only [Qlt, mul, add, neg] at hc
  push_cast at hc
  show a.num * ((mul (⟨1, n⟩ : Q) (add a w)).den : Int)
      < (mul (⟨1, n⟩ : Q) (add a w)).num * (a.den : Int)
  simp only [mul, add]; push_cast
  have eL : a.num * ((n : Int) * ((a.den : Int) * (w.den : Int)))
          = (n : Int) * a.num * ((a.den : Int) * (w.den : Int)) := by ring_uor
  have eR : 1 * (a.num * (w.den : Int) + w.num * (a.den : Int)) * (a.den : Int)
          = (a.num * (w.den : Int) + w.num * (a.den : Int)) * (1 * (a.den : Int)) := by ring_uor
  rw [eL, eR]; exact hc

-- ===========================================================================
-- The crux pointwise identity on the core window: dilate-n of the n-integrand,
-- weighted by 1/max(t,a/n), equals the 1/n-integrand weighted by 1/max(t,a).
-- ===========================================================================

/-- **The reciprocal change-of-variables integrand identity** on the band `t ≥ a`:
    `(dilateTest n Pn)(t)·(1/max(t,a/n))  ≈  P1n(t)·(1/max(t,a))`. Both densities are `1/t`;
    `clampedInv_dilate_on` turns `n·(1/max(nt,a)) = 1/max(t,a)`, so the two convolution integrands
    coincide up to `Rmul_comm` of their `g`-factors. This is the heart of the reciprocal duality. -/
theorem core_integrand_agree (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (t : Real) (ht : Rle (ofQ a had) t) :
    Req (Rmul ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                 Nat.one_pos
                 (productTest (reflectTest a han had
                      (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                        Nat.one_pos g)) (reflectTest a han had g))).f t)
              (clampedInv (mul (⟨1, n⟩ : Q) a)
                (by show (0 : Int) < 1 * a.num; rw [Int.one_mul]; exact han)
                (Qmul_den_pos hn0 had) t))
        (Rmul ((productTest (reflectTest a han had
                    (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g))
                  (reflectTest a han had g)).f t)
              (clampedInv a han had t)) := by
  -- abbreviating positivity proofs
  have hnn_num : (0 : Int) < (n : Int) := by exact_mod_cast hn0
  -- t ≥ 0
  have h0t : Rnonneg t := Rnonneg_of_Rle_zero
    (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ had (Int.le_of_lt han))) ht)
  -- t ≤ n·t, hence a ≤ n·t
  have hone11 : Req (ofQ (⟨1, 1⟩ : Q) (by decide)) one := Req_of_seq_Qeq (fun _ => Qeq_refl _)
  have h1n : Qle (⟨1, 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) := by simp only [Qle]; push_cast; omega
  have ht_le_nt : Rle t (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t) :=
    Rle_trans
      (Rle_of_Req (Req_trans (Req_symm (Rone_mul t))
        (Rmul_congr (Req_symm hone11) (Req_refl t))))
      (Rmul_le_Rmul_right h0t (Rle_ofQ_ofQ (by decide) Nat.one_pos h1n))
  have hant : Rle (ofQ a had) (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t) :=
    Rle_trans ht ht_le_nt
  -- the density cancellation n·(1/max(nt,a)) = 1/max(t,a)
  have DIL : Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
        (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t)))
      (clampedInv a han had t) :=
    clampedInv_dilate_on (⟨(n : Int), 1⟩ : Q) a a Nat.one_pos han had han had ht hant
  -- the first-factor collapses:  1/n · (1/max(t,a)) = 1/max(nt,a)
  have hprod_one : Req (Rmul (ofQ (⟨1, n⟩ : Q) hn0) (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) one :=
    Req_trans (Rmul_ofQ_ofQ hn0 Nat.one_pos)
      (Req_trans (ofQ_congr (Qmul_den_pos hn0 Nat.one_pos) (by decide)
          (by simp only [Qeq, mul]; push_cast; omega)) hone11)
  have Econgr : Req (Rmul (ofQ (⟨1, n⟩ : Q) hn0) (clampedInv a han had t))
      (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t)) :=
    Req_trans (Rmul_congr (Req_refl (ofQ (⟨1, n⟩ : Q) hn0)) (Req_symm DIL))
      (Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, n⟩ : Q) hn0)
          (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
          (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
        (Req_trans (Rmul_congr hprod_one (Req_refl _)) (Rone_mul _)))
  -- the g-factor congruences
  have hfirstL := g.hfc _ _ DIL
  have hfirstR := g.hfc _ _ Econgr
  -- inner product identity (Rmul_comm of the two g-values)
  have hinner : Req
      (Rmul (g.f (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
              (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
            (g.f (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
      (Rmul (g.f (Rmul (ofQ (⟨1, n⟩ : Q) hn0) (clampedInv a han had t)))
            (g.f (clampedInv a han had t))) :=
    Req_trans (Rmul_congr hfirstL (Req_refl _))
      (Req_trans (Rmul_comm (g.f (clampedInv a han had t))
          (g.f (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
        (Req_symm (Rmul_congr hfirstR (Req_refl _))))
  -- density congruence: both clamps are 1/t on t ≥ a ≥ a/n
  obtain ⟨kt, hkt⟩ := Pos_of_Rle_ofQ han had ht
  have haN_le_a : Qle (mul (⟨1, n⟩ : Q) a) a := by
    simp only [Qle, mul]
    push_cast
    have hd : (0 : Int) ≤ a.num * (a.den : Int) :=
      Int.mul_nonneg (Int.le_of_lt han) (Int.ofNat_nonneg a.den)
    have h1n : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn0
    calc 1 * a.num * (a.den : Int) = a.num * (a.den : Int) * 1 := by rw [Int.one_mul, Int.mul_one]
      _ ≤ a.num * (a.den : Int) * (n : Int) := Int.mul_le_mul_of_nonneg_left h1n hd
      _ = a.num * ((n : Int) * (a.den : Int)) := by
            rw [Int.mul_assoc, Int.mul_comm (a.den : Int) (n : Int)]
  have htN : Rle (ofQ (mul (⟨1, n⟩ : Q) a) (Qmul_den_pos hn0 had)) t :=
    Rle_trans (Rle_ofQ_ofQ (Qmul_den_pos hn0 had) had haN_le_a) ht
  have hdens : Req (clampedInv (mul (⟨1, n⟩ : Q) a)
        (by show (0 : Int) < 1 * a.num; rw [Int.one_mul]; exact han) (Qmul_den_pos hn0 had) t)
      (clampedInv a han had t) :=
    Req_trans (clampedInv_eq_of_ge hkt htN) (Req_symm (clampedInv_eq_of_ge hkt ht))
  exact Rmul_congr hinner hdens

-- ===========================================================================
-- THE AUTOCORRELATION RECIPROCAL SELF-DUALITY (the pivotal change of variables).
-- ===========================================================================

set_option maxHeartbeats 2000000 in
/-- **Autocorrelation reciprocal self-duality** (`2 ≤ n`): for a self-supported test `g`
    (vanishing above `1/a` and below `b`, support fitting the window `1/b ≤ a+w`, and the window
    wide enough for the `n`-core, `n·a < a+w`), the autocorrelation point value is reciprocal
    symmetric: `autocorr g n ≈ autocorr g (1/n)`. The proof is Route D — dilate `autocorr g n` by
    `1/n` onto the shifted window `[a/n, (a+w)/n]` (`haarIntegral_dilate`), restrict both sides to the
    common core `[a, (a+w)/n]` by dropping support-free pieces (`riemannIntegralI_split_at` +
    `haarIntegral_window_vanish`), and match the two integrands on the core (`core_integrand_agree`,
    the reciprocal change of variables `n·(1/max(nt,a)) = 1/max(t,a)`). -/
theorem autocorr_recip_core (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hcore : Qlt (mul (⟨(n : Int), 1⟩ : Q) a) (add a w)) :
    Req (autocorr g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had a w had hw hwn)
        (autocorr g (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had a w had hw hwn) := by
  have hsn : (0 : Int) < (n : Int) := Int.ofNat_pos.mpr hn0
  -- data abbreviations
  let Pn : L2Test := productTest (reflectTest a han had
      (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos g)) (reflectTest a han had g)
  let P1n : L2Test := productTest (reflectTest a han had
      (dilateTest (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 g)) (reflectTest a han had g)
  -- positivity of the scaled quantities
  have haN_num : 0 < (mul (⟨1, n⟩ : Q) a).num := by
    show (0 : Int) < 1 * a.num; rw [Int.one_mul]; exact han
  have haN_den : 0 < (mul (⟨1, n⟩ : Q) a).den := Qmul_den_pos hn0 had
  have hwN_den : 0 < (mul (⟨1, n⟩ : Q) w).den := Qmul_den_pos hn0 hw
  have hwN_num : 0 ≤ (mul (⟨1, n⟩ : Q) w).num := by
    show (0 : Int) ≤ 1 * w.num; rw [Int.one_mul]; exact hwn
  -- split-node facts (DN window [a/n, (a+w)/n], node w1 = a − a/n)
  have hw1_den : 0 < (Qsub a (mul (⟨1, n⟩ : Q) a)).den := Qsub_den_pos had haN_den
  have hw1_num : 0 < (Qsub a (mul (⟨1, n⟩ : Q) a)).num := w1_num_pos a han had n hn2
  have CoreLB : Qle a (mul (⟨1, n⟩ : Q) (add a w)) := Int.le_of_lt (CoreStrict a w n hcore)
  have hdistrib : Qeq (add (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)) (mul (⟨1, n⟩ : Q) (add a w)) := by
    simp only [Qeq, add, mul]; push_cast; ring_uor
  have h_a_le_aNwN : Qle a (add (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)) :=
    Qle_trans (Qmul_den_pos hn0 (add_den_pos had hw)) CoreLB (Qeq_le (Qeq_symm hdistrib))
  have hle : Qle (Qsub a (mul (⟨1, n⟩ : Q) a)) (mul (⟨1, n⟩ : Q) w) :=
    Qsub_le_of_le_add haN_den hwN_den h_a_le_aNwN
  have hw2n : 0 ≤ (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a))).num :=
    Qsub_num_nonneg_of_le hle
  -- I_1n split node w1' = (a+w)/n − a
  have hawn : 0 ≤ (add a w).num := by
    show (0 : Int) ≤ a.num * (w.den : Int) + w.num * (a.den : Int)
    exact Int.add_nonneg (Int.mul_nonneg (Int.le_of_lt han) (Int.ofNat_nonneg w.den))
      (Int.mul_nonneg hwn (Int.ofNat_nonneg a.den))
  have hw1'_den : 0 < (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a).den :=
    Qsub_den_pos (Qmul_den_pos hn0 (add_den_pos had hw)) had
  have hw1'_num : 0 < (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a).num :=
    Qsub_num_pos_of_lt (CoreStrict a w n hcore)
  have hle' : Qle (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) w :=
    Qsub_le_of_le_add had hw (inv_n_mul_le (add a w) hawn n hn0)
  have hw2n' : 0 ≤ (Qsub w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)).num :=
    Qsub_num_nonneg_of_le hle'
  -- window reconciliation Qeqs
  have QB1 : Qeq (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a))) a := by
    simp only [Qeq, add, neg, mul, Qsub]; push_cast; ring_uor
  have QB2 : Qeq (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
      (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) := by
    simp only [Qeq, add, neg, mul, Qsub]; push_cast; ring_uor
  have QC1 : Qeq (mul (mul (⟨(n : Int), 1⟩ : Q) b)
      (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))) (mul b (add a w)) := by
    simp only [Qeq, add, neg, mul, Qsub]; push_cast; ring_uor
  have QC2 : Qle (⟨1, 1⟩ : Q) (mul b (add a w)) :=
    Qle_trans (Qmul_den_pos hbd (Qinv_den_pos hbn)) (Qeq_le (Qeq_symm (Qmul_Qinv hbn)))
      (Qmul_le_mul_left (Int.le_of_lt hbn) hfit)
  have Hbig : Qle (⟨1, 1⟩ : Q)
      (mul (mul (⟨(n : Int), 1⟩ : Q) b) (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))) :=
    Qle_trans (Qmul_den_pos hbd (add_den_pos had hw)) QC2 (Qeq_le (Qeq_symm QC1))
  have Ha : Qle a (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)) :=
    Qle_add_right_nonneg (Int.le_of_lt hw1'_num)
  have hlon' : 0 < (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)).num :=
    qnum_pos_of_le han (add_den_pos had hw1'_den) Ha
  -- STEP A: I_n ≈ DN (dilate by 1/n onto [a/n, (a+w)/n])
  have stepA : Req (haarIntegral Pn a han had a w had hw hwn)
      (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        haN_den hwN_den hwN_num) :=
    Req_trans
      (haarIntegral_congr_Q Pn a han had a w
        (mul (⟨(n : Int), 1⟩ : Q) (mul (⟨1, n⟩ : Q) a)) (mul (⟨(n : Int), 1⟩ : Q) (mul (⟨1, n⟩ : Q) w))
        had hw hwn (Qmul_den_pos Nat.one_pos haN_den) (Qmul_den_pos Nat.one_pos hwN_den)
        (Int.mul_nonneg (Int.le_of_lt hsn) hwN_num)
        (Qeq_symm (n_mul_inv_n n a)) (Qeq_symm (n_mul_inv_n n w)))
      (haarIntegral_dilate Pn (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos (mul (⟨1, n⟩ : Q) a) a
        haN_num haN_den han had (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w) haN_den hwN_den hwN_num
        (Rle_of_Req (Req_refl _))
        (Rle_ofQ_ofQ had (Qmul_den_pos Nat.one_pos haN_den)
          (Qeq_le (Qeq_symm (n_mul_inv_n n a)))))
  -- STEP B: DN ≈ right_DN (split, drop the support-free left piece [a/n, a])
  have hleftDN : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a))
        haN_den hw1_den (Int.le_of_lt hw1_num)) zero :=
    left_DN_window_vanish g a han had n hn0 hgh (mul (⟨1, n⟩ : Q) a) haN_num haN_den
      (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)) haN_den hw1_den (Int.le_of_lt hw1_num)
      haN_num (Qeq_le QB1) (Qeq_le (Qeq_symm (n_mul_inv_n n a)))
  have stepB : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        haN_den hwN_den hwN_num)
      (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n) :=
    Req_trans
      (haarIntegral_split_at (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        (Qsub a (mul (⟨1, n⟩ : Q) a)) haN_den hwN_den hwN_num hw1_den hw1_num hle hw2n)
      (Req_trans (Radd_congr hleftDN (Req_refl _))
        (Req_trans (Radd_comm zero _) (Radd_zero _)))
  -- STEP C: right_DN ≈ left_I1n (align window to core, swap floor + integrand)
  have stepC : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n)
      (haarIntegral P1n a han had a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_congr_Q (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n
        had hw1'_den (Int.le_of_lt hw1'_num) QB1 QB2)
      (haarIntegral_congr_window (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos Pn) P1n
        (mul (⟨1, n⟩ : Q) a) a haN_num haN_den han had
        a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) had hw1'_den (Int.le_of_lt hw1'_num)
        (fun x h0 _h1 => core_integrand_agree g a han had n hn0
          (affineMap a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) had hw1'_den x)
          (Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw1'_den (Int.le_of_lt hw1'_num))
            (Rnonneg_of_Rle_zero h0)))))
  -- STEP D: I_1n ≈ left_I1n (split, drop the support-free right piece [(a+w)/n, a+w])
  have hrightI1n : Req (haarIntegral P1n a han had
        (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)) (Qsub w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))
        (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n') zero :=
    right_I1n_window_vanish g a han had n hn0 b hbd hbn hgl
      (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)) (Qsub w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))
      (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n' hlon' Ha Hbig
  have stepD : Req (haarIntegral P1n a han had a w had hw hwn)
      (haarIntegral P1n a han had a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_split_at P1n a han had a w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw hwn hw1'_den hw1'_num hle' hw2n')
      (Req_trans (Radd_congr (Req_refl _) hrightI1n) (Radd_zero _))
  -- assemble
  show Req (haarIntegral Pn a han had a w had hw hwn) (haarIntegral P1n a han had a w had hw hwn)
  exact Req_trans stepA (Req_trans stepB (Req_trans stepC (Req_symm stepD)))

/-- **Autocorrelation reciprocal self-duality** (all `n ≥ 1`): `autocorr g n ≈ autocorr g (1/n)` —
    the reciprocal-symmetric point value `h(n) ≈ h(1/n)` of the Haar-self-dual autocorrelation cone
    `g ⋆ g^τ`, on the window `[a, a+w]` with `g` compactly supported inside the band `[b, 1/a]`
    (`1/b ≤ a+w`, `n·a < a+w`). The substantive change of variables is `autocorr_recip_core`
    (`n ≥ 2`); `n = 1` is the reflexive identity `h(1) = h(1)`. -/
theorem autocorr_recip (g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hcore : Qlt (mul (⟨(n : Int), 1⟩ : Q) a) (add a w)) :
    Req (autocorr g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had a w had hw hwn)
        (autocorr g (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had a w had hw hwn) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- n = 1 : the two points coincide, reflexivity
    have hn1 : n = 1 := by omega
    subst hn1
    exact Req_refl _
  · exact autocorr_recip_core g a han had w hw hwn b hbd hbn n hn0 h2 hgh hgl hfit hcore

end UOR.Bridge.F1Square.Square
