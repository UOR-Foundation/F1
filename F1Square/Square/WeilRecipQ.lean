/-
F1 square — **two-test reciprocity at every RATIONAL scale** (`WeilRecipQ.lean`):

    `H_q(f,g) = H_{1/q}(g,f)`   for every rational `q > 1`

— the general-rational port of `HForm_recip_core` (which was stated at integer scales `n` and their
reciprocals `1/n` only).  Rational density is what lifts the finite-prime reciprocity to REAL scales
(`WeilDensity.Req_of_lipschitz_dense`), so the scale set must be dense: this file supplies it.

Same Route D as the integer case, with `⟨n,1⟩ ↦ q` and `⟨1,n⟩ ↦ Qinv q` throughout: dilate `H_q(f,g)`
by `1/q` onto `[a/q, (a+w)/q]` (`haarIntegral_dilate`, which already takes an arbitrary rational
dilation), drop the support-free pieces, and match the two integrands on the core
(`core_integrand_agree_Q`: `q·(1/max(q·t, a)) = 1/max(t, a)` by `clampedInv_dilate_on`).  The six
rational-arithmetic helpers (`Qmul_Qinv_mul_gen`, `q_mul_inv_q`, `inv_q_mul_le`, `w1_num_pos_gen`,
`CoreStrict_gen`, `qlow_engine_gen`) replace their `Nat` specializations.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftHaarForm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) Rational-scale arithmetic helpers (the `Nat` helpers generalized to `q : Q`).
-- ===========================================================================

/-- `q·(1/(q·qp)) ≈ 1/qp` for positive `q, qp`. -/
theorem Qmul_Qinv_mul_gen (q qp : Q) (hqn : 0 < q.num) (hqpn : 0 < qp.num) :
    Qeq (mul q (Qinv (mul q qp))) (Qinv qp) := by
  have hq := Int.toNat_of_nonneg (Int.le_of_lt hqpn)
  have hqq : ((q.num * qp.num).toNat : Int) = q.num * qp.num :=
    Int.toNat_of_nonneg (Int.mul_nonneg (Int.le_of_lt hqn) (Int.le_of_lt hqpn))
  show q.num * ((q.den * qp.den : Nat) : Int) * ((qp.num.toNat : Nat) : Int)
    = (qp.den : Int) * ((q.den * (q.num * qp.num).toNat : Nat) : Int)
  push_cast [hq, hqq]
  ring_uor

/-- `q·(q⁻¹·x) ≈ x` for positive `q`. -/
theorem q_mul_inv_q (q x : Q) (hqn : 0 < q.num) :
    Qeq (mul q (mul (Qinv q) x)) x := by
  have hq := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  show q.num * ((q.den : Int) * x.num) * (x.den : Int)
    = x.num * ((q.den * (q.num.toNat * x.den) : Nat) : Int)
  push_cast [hq]
  ring_uor

/-- `q⁻¹·X ≤ X` for `X ≥ 0` and `q ≥ 1`. -/
theorem inv_q_mul_le (X : Q) (hXn : 0 ≤ X.num) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hq1 : Qle (⟨1, 1⟩ : Q) q) :
    Qle (mul (Qinv q) X) X := by
  have hq := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  have h1 : (q.den : Int) ≤ q.num := by
    have h := hq1; simp only [Qle] at h; push_cast at h; omega
  show (mul (Qinv q) X).num * (X.den : Int) ≤ X.num * ((mul (Qinv q) X).den : Int)
  show ((q.den : Int) * X.num) * (X.den : Int) ≤ X.num * ((q.num.toNat * X.den : Nat) : Int)
  push_cast [hq]
  have hXd : (0 : Int) ≤ (X.den : Int) := Int.ofNat_nonneg _
  calc (q.den : Int) * X.num * (X.den : Int)
      = (X.num * (X.den : Int)) * (q.den : Int) := by ring_uor
    _ ≤ (X.num * (X.den : Int)) * q.num :=
        Int.mul_le_mul_of_nonneg_left h1 (Int.mul_nonneg hXn hXd)
    _ = X.num * (q.num * (X.den : Int)) := by ring_uor

/-- `1 < q ⟹ q.den < q.num`. -/
theorem qnum_gt_den_of_one_lt (q : Q) (hq1 : Qlt (⟨1, 1⟩ : Q) q) : (q.den : Int) < q.num := by
  have h := hq1; simp only [Qlt] at h; push_cast at h; omega

/-- The DN split node `a − a/q` has positive numerator when `q > 1`. -/
theorem w1_num_pos_gen (a : Q) (han : 0 < a.num) (had : 0 < a.den) (q : Q) (hqn : 0 < q.num)
    (hq1 : Qlt (⟨1, 1⟩ : Q) q) :
    0 < (Qsub a (mul (Qinv q) a)).num := by
  have hq := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  have hgt := qnum_gt_den_of_one_lt q hq1
  have e : (Qsub a (mul (Qinv q) a)).num = a.num * (a.den : Int) * (q.num - (q.den : Int)) := by
    simp only [Qsub, add, neg, mul, Qinv]; push_cast [hq]; ring_uor
  rw [e]
  exact Int.mul_pos (Int.mul_pos han (by exact_mod_cast had)) (by omega)

/-- `q·a < a+w ⟹ a < (a+w)/q`. -/
theorem CoreStrict_gen (a w : Q) (q : Q) (hqn : 0 < q.num)
    (hcore : Qlt (mul q a) (add a w)) :
    Qlt a (mul (Qinv q) (add a w)) := by
  have hq := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  have hc := hcore
  simp only [Qlt, mul, add] at hc
  push_cast at hc
  show a.num * ((mul (Qinv q) (add a w)).den : Int)
      < (mul (Qinv q) (add a w)).num * (a.den : Int)
  simp only [mul, add, Qinv]; push_cast [hq]
  have eL : a.num * (q.num * ((a.den : Int) * (w.den : Int)))
          = q.num * a.num * ((a.den : Int) * (w.den : Int)) := by ring_uor
  have eR : (q.den : Int) * (a.num * (w.den : Int) + w.num * (a.den : Int)) * (a.den : Int)
          = (a.num * (w.den : Int) + w.num * (a.den : Int)) * ((q.den : Int) * (a.den : Int)) := by
    ring_uor
  rw [eL, eR]; exact hc

/-- From `1 ≤ q·b·qp` get `(1/q)·(1/qp) ≤ b`. -/
theorem qlow_engine_gen (b : Q) (q : Q) (hqn : 0 < q.num) {qp : Q} (hqpn : 0 < qp.num)
    (h : Qle (⟨1, 1⟩ : Q) (mul (mul q b) qp)) :
    Qle (mul (Qinv q) (Qinv qp)) b := by
  have hpne := Int.toNat_of_nonneg (Int.le_of_lt hqpn)
  have hqne := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  simp only [Qle, Qinv, mul] at h ⊢
  push_cast [hpne, hqne] at h ⊢
  have eL : (q.den : Int) * (qp.den : Int) * (b.den : Int)
      = 1 * ((q.den : Int) * (b.den : Int) * (qp.den : Int)) := by ring_uor
  have eR : b.num * (q.num * qp.num) = q.num * b.num * qp.num * 1 := by ring_uor
  rw [eL, eR]
  exact h

/-- `1 ≤ q` (as `Qle`) from `1 < q`. -/
theorem Qle_of_one_lt (q : Q) (hq1 : Qlt (⟨1, 1⟩ : Q) q) : Qle (⟨1, 1⟩ : Q) q := by
  have h := hq1; simp only [Qlt] at h; simp only [Qle]; omega

-- ===========================================================================
-- (1) Pointwise support vanishing of the two convolution integrands at scale `q` / `1/q`.
-- ===========================================================================

/-- High-side vanishing at a sample `qp ≤ a`: the dilated integrand `dilateTest q P_q` vanishes at
    `ofQ qp` — its first factor is `f(1/qp)` with `1/qp ≥ 1/a`. -/
theorem dilDN_pt_zero_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num)
    (hqp_le_a : Qle qp a) (hqqp_ge_a : Qle a (mul q qp)) :
    Req ((dilateTest q hqn hqd
           (productTest (reflectTest a han had (dilateTest q hqn hqd f))
              (reflectTest a han had g))).f (ofQ qp hqpd)) zero := by
  have hmn : 0 < (mul q qp).num := Int.mul_pos hqn hqpn
  have hmd : 0 < (mul q qp).den := Qmul_den_pos hqd hqpd
  have e1 : Req ((dilateTest q hqn hqd
        (productTest (reflectTest a han had (dilateTest q hqn hqd f))
          (reflectTest a han had g))).f (ofQ qp hqpd))
      ((productTest (reflectTest a han had (dilateTest q hqn hqd f))
          (reflectTest a han had g)).f (ofQ (mul q qp) hmd)) :=
    (productTest (reflectTest a han had (dilateTest q hqn hqd f))
      (reflectTest a han had g)).hfc _ _ (Rmul_ofQ_ofQ hqd hqpd)
  have e2 := Ps_ofQ2 f g a han had q hqn hqd (mul q qp) hmd hmn hqqp_ge_a
  have hfle : Qle (Qinv a) (mul q (Qinv (mul q qp))) :=
    Qle_trans (Qinv_den_pos hqpn) (Qinv_antitone han hqpn hqp_le_a)
      (Qeq_le (Qeq_symm (Qmul_Qinv_mul_gen q qp hqn hqpn)))
  have hfz : Req (f.f (ofQ (mul q (Qinv (mul q qp)))
        (Qmul_den_pos hqd (Qinv_den_pos hmn)))) zero :=
    hgh_f _ (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos hqd (Qinv_den_pos hmn)) hfle)
  refine Req_trans e1 (Req_trans e2 ?_)
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- Low-side vanishing at a sample `1 ≤ q·b·qp`: the `H_{1/q}(g,f)` integrand vanishes at `ofQ qp`
    — its first factor is `g(1/(q·qp))` and `1/(q·qp) ≤ b`. -/
theorem P1n_pt_zero_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (b : Q) (hbd : 0 < b.den) (_hbn : 0 < b.num)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp)
    (hbig : Qle (⟨1, 1⟩ : Q) (mul (mul q b) qp)) :
    Req ((productTest (reflectTest a han had
           (dilateTest (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) g)) (reflectTest a han had f)).f
          (ofQ qp hqpd)) zero := by
  have e2 := Ps_ofQ2 g f a han had (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) qp hqpd hqpn haqp
  have hlow : Qle (mul (Qinv q) (Qinv qp)) b := qlow_engine_gen b q hqn hqpn hbig
  have hfz : Req (g.f (ofQ (mul (Qinv q) (Qinv qp))
        (Qmul_den_pos (Qinv_den_pos hqn) (Qinv_den_pos hqpn)))) zero :=
    hgl_g _ (Rle_ofQ_ofQ (Qmul_den_pos (Qinv_den_pos hqn) (Qinv_den_pos hqpn)) hbd hlow)
  refine Req_trans e2 ?_
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- Degenerate high-side pointwise vanishing (`qp ≤ q·a`): the `H_q(f,g)` integrand vanishes at
    `ofQ qp` — its first factor is `f(q/qp)` with `q/qp ≥ 1/a`. -/
theorem Pn_pt_zero_degen_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp)
    (hqp_le_qa : Qle qp (mul q a)) :
    Req ((productTest (reflectTest a han had (dilateTest q hqn hqd f))
           (reflectTest a han had g)).f (ofQ qp hqpd)) zero := by
  have hqa_num : 0 < (mul q a).num := Int.mul_pos hqn han
  have e2 := Ps_ofQ2 f g a han had q hqn hqd qp hqpd hqpn haqp
  have hfle : Qle (Qinv a) (mul q (Qinv qp)) := by
    have s1 : Qle (Qinv (mul q a)) (Qinv qp) := Qinv_antitone hqa_num hqpn hqp_le_qa
    have s2 : Qle (mul q (Qinv (mul q a))) (mul q (Qinv qp)) :=
      Qmul_le_mul_left (Int.le_of_lt hqn) s1
    exact Qle_trans (Qmul_den_pos hqd (Qinv_den_pos hqa_num))
      (Qeq_le (Qeq_symm (Qmul_Qinv_mul_gen q a hqn han))) s2
  have hfz : Req (f.f (ofQ (mul q (Qinv qp)) (Qmul_den_pos hqd (Qinv_den_pos hqpn)))) zero :=
    hgh_f _ (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos hqd (Qinv_den_pos hqpn)) hfle)
  refine Req_trans e2 ?_
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

-- ===========================================================================
-- (2) Window vanishing (rational scale).
-- ===========================================================================

/-- The dilated high-side integrand vanishes over a window at/below `a` (with `a ≤ q·lo`). -/
theorem left_DN_window_vanish_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (af : Q) (hafn : 0 < af.num) (hafd : 0 < af.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (H1 : Qle (add lo w) a) (H2 : Qle a (mul q lo)) :
    Req (haarIntegral (dilateTest q hqn hqd
             (productTest (reflectTest a han had (dilateTest q hqn hqd f)) (reflectTest a han had g)))
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
  have hqi_le1 : Qle (⟨(i : Int), N + 1⟩ : Q) (⟨1, 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hmul_le : Qle (mul w (⟨(i : Int), N + 1⟩ : Q)) w :=
    Qle_trans (Qmul_den_pos hw (by decide)) (Qmul_le_mul_left hwn hqi_le1)
      (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
  have hqp_le_a : Qle (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) a :=
    Qle_trans (add_den_pos hlo hw) (Qadd_le_add (Qle_refl lo) hmul_le) H1
  have hqqp_ge_a : Qle a (mul q (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))) :=
    Qle_trans (Qmul_den_pos hqd hlo) H2 (Qmul_le_mul_left (Int.le_of_lt hqn) hlo_qp)
  exact Req_trans
    ((dilateTest q hqn hqd (productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g))).hfc _ _ step1)
    (dilDN_pt_zero_Q f g a han had q hqn hqd hgh_f (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn hqp_le_a hqqp_ge_a)

/-- The low-side integrand vanishes over a window at/above `a` (with `1 ≤ q·b·lo`). -/
theorem right_I1n_window_vanish_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (Ha : Qle a lo) (Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul q b) lo)) :
    Req (haarIntegral (productTest (reflectTest a han had
             (dilateTest (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) g)) (reflectTest a han had f))
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
  have hqb_nn : (0 : Int) ≤ (mul q b).num := Int.mul_nonneg (Int.le_of_lt hqn) (Int.le_of_lt hbn)
  have hbig : Qle (⟨1, 1⟩ : Q) (mul (mul q b) (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))) :=
    Qle_trans (Qmul_den_pos (Qmul_den_pos hqd hbd) hlo) Hbig (Qmul_le_mul_left hqb_nn hlo_qp)
  exact Req_trans
    ((productTest (reflectTest a han had
        (dilateTest (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) g))
      (reflectTest a han had f)).hfc _ _ step1)
    (P1n_pt_zero_Q f g a han had q hqn hqd b hbd hbn hgl_g (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn haqp hbig)

/-- The `H_q(f,g)` form vanishes on the window when `a+w ≤ q·a`. -/
theorem Pn_window_vanish_degen_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (Hdeg : Qle (add a w) (mul q a)) :
    Req (haarIntegral (productTest (reflectTest a han had (dilateTest q hqn hqd f))
           (reflectTest a han had g)) a han had a w had hw hwn) zero := by
  refine haarIntegral_window_vanish _ a han had a w had hw hwn ?_
  intro N i hi
  have hqid : (0 : Nat) < N + 1 := Nat.succ_pos N
  have hmul_nn : (0 : Int) ≤ (mul w (⟨(i : Int), N + 1⟩ : Q)).num := by
    show (0 : Int) ≤ w.num * (i : Int); exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hqpd : 0 < (add a (mul w (⟨(i : Int), N + 1⟩ : Q))).den :=
    add_den_pos had (Qmul_den_pos hw hqid)
  have hlo_qp : Qle a (add a (mul w (⟨(i : Int), N + 1⟩ : Q))) := Qle_self_add hmul_nn
  have hqpn : 0 < (add a (mul w (⟨(i : Int), N + 1⟩ : Q))).num := qnum_pos_of_le han hqpd hlo_qp
  have step1 : Req (affineMap a w had hw (ofQ (⟨(i : Int), N + 1⟩ : Q) hqid))
      (ofQ (add a (mul w (⟨(i : Int), N + 1⟩ : Q))) hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ a had)) (Rmul_ofQ_ofQ hw hqid))
      (Radd_ofQ_ofQ had (Qmul_den_pos hw hqid))
  have hqi_le1 : Qle (⟨(i : Int), N + 1⟩ : Q) (⟨1, 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hmul_le : Qle (mul w (⟨(i : Int), N + 1⟩ : Q)) w :=
    Qle_trans (Qmul_den_pos hw (by decide)) (Qmul_le_mul_left hwn hqi_le1)
      (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
  have hqp_le_qa : Qle (add a (mul w (⟨(i : Int), N + 1⟩ : Q))) (mul q a) :=
    Qle_trans (add_den_pos had hw) (Qadd_le_add (Qle_refl a) hmul_le) Hdeg
  exact Req_trans
    ((productTest (reflectTest a han had (dilateTest q hqn hqd f))
        (reflectTest a han had g)).hfc _ _ step1)
    (Pn_pt_zero_degen_Q f g a han had q hqn hqd hgh_f (add a (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn hlo_qp hqp_le_qa)

-- ===========================================================================
-- (3) The core pointwise identity at rational scale.
-- ===========================================================================

/-- The reciprocal change-of-variables integrand identity on `t ≥ a`, scale `q ≥ 1`:
    `(dilateTest q P_{f,g})(t)·(1/max(t,a/q)) ≈ P_{g,f}(t)·(1/max(t,a))`. -/
theorem core_integrand_agree_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q)
    (t : Real) (ht : Rle (ofQ a had) t) :
    Req (Rmul ((dilateTest q hqn hqd
                 (productTest (reflectTest a han had (dilateTest q hqn hqd f))
                   (reflectTest a han had g))).f t)
              (clampedInv (mul (Qinv q) a) (Int.mul_pos (Qinv_num_pos hqd) han)
                (Qmul_den_pos (Qinv_den_pos hqn) had) t))
        (Rmul ((productTest (reflectTest a han had
                    (dilateTest (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) g))
                  (reflectTest a han had f)).f t)
              (clampedInv a han had t)) := by
  have h0t : Rnonneg t := Rnonneg_of_Rle_zero
    (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ had (Int.le_of_lt han))) ht)
  have hone11 : Req (ofQ (⟨1, 1⟩ : Q) (by decide)) one := Req_of_seq_Qeq (fun _ => Qeq_refl _)
  have ht_le_qt : Rle t (Rmul (ofQ q hqd) t) :=
    Rle_trans
      (Rle_of_Req (Req_trans (Req_symm (Rone_mul t))
        (Rmul_congr (Req_symm hone11) (Req_refl t))))
      (Rmul_le_Rmul_right h0t (Rle_ofQ_ofQ (by decide) hqd hq1))
  have haqt : Rle (ofQ a had) (Rmul (ofQ q hqd) t) := Rle_trans ht ht_le_qt
  have DIL : Req (Rmul (ofQ q hqd) (clampedInv a han had (Rmul (ofQ q hqd) t)))
      (clampedInv a han had t) :=
    clampedInv_dilate_on q a a hqd han had han had ht haqt
  have hprod_one : Req (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (ofQ q hqd)) one :=
    Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hqn) hqd)
      (Req_trans (ofQ_congr (Qmul_den_pos (Qinv_den_pos hqn) hqd) (by decide) (Qinv_mul hqd hqn))
        hone11)
  have Econgr : Req (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (clampedInv a han had t))
      (clampedInv a han had (Rmul (ofQ q hqd) t)) :=
    Req_trans (Rmul_congr (Req_refl _) (Req_symm DIL))
      (Req_trans (Req_symm (Rmul_assoc _ _ _))
        (Req_trans (Rmul_congr hprod_one (Req_refl _)) (Rone_mul _)))
  have hfirstL := f.hfc _ _ DIL
  have hfirstR := g.hfc _ _ Econgr
  have hinner : Req
      (Rmul (f.f (Rmul (ofQ q hqd) (clampedInv a han had (Rmul (ofQ q hqd) t))))
            (g.f (clampedInv a han had (Rmul (ofQ q hqd) t))))
      (Rmul (g.f (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (clampedInv a han had t)))
            (f.f (clampedInv a han had t))) :=
    Req_trans (Rmul_congr hfirstL (Req_refl _))
      (Req_trans (Rmul_comm (f.f (clampedInv a han had t))
          (g.f (clampedInv a han had (Rmul (ofQ q hqd) t))))
        (Req_symm (Rmul_congr hfirstR (Req_refl _))))
  obtain ⟨kt, hkt⟩ := Pos_of_Rle_ofQ han had ht
  have haN_le_a : Qle (mul (Qinv q) a) a := inv_q_mul_le a (Int.le_of_lt han) q hqn hqd hq1
  have htN : Rle (ofQ (mul (Qinv q) a) (Qmul_den_pos (Qinv_den_pos hqn) had)) t :=
    Rle_trans (Rle_ofQ_ofQ (Qmul_den_pos (Qinv_den_pos hqn) had) had haN_le_a) ht
  have hdens : Req (clampedInv (mul (Qinv q) a) (Int.mul_pos (Qinv_num_pos hqd) han)
        (Qmul_den_pos (Qinv_den_pos hqn) had) t)
      (clampedInv a han had t) :=
    Req_trans (clampedInv_eq_of_ge hkt htN) (Req_symm (clampedInv_eq_of_ge hkt ht))
  exact Rmul_congr hinner hdens

-- ===========================================================================
-- (4) The reciprocity at rational scale `q > 1` (Route D), the scale congruence, and all scales.
-- ===========================================================================

set_option maxHeartbeats 2000000 in
/-- **★ TWO-TEST RECIPROCITY AT RATIONAL SCALE** `H_q(f,g) = H_{1/q}(g,f)` for rational `q > 1` in
    the strict-core regime `q·a < a+w` — Route D with a rational dilation. -/
theorem HForm_recip_core_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (hq1 : Qlt (⟨1, 1⟩ : Q) q)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hcore : Qlt (mul q a) (add a w)) :
    Req (HForm f g q hqn hqd a han had w hw hwn)
        (HForm g f (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) a han had w hw hwn) := by
  have hq1le : Qle (⟨1, 1⟩ : Q) q := Qle_of_one_lt q hq1
  have hqi_n : 0 < (Qinv q).num := Qinv_num_pos hqd
  have hqi_d : 0 < (Qinv q).den := Qinv_den_pos hqn
  have hq_toNat := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  let PnF : L2Test := productTest (reflectTest a han had (dilateTest q hqn hqd f))
    (reflectTest a han had g)
  let P1nF : L2Test := productTest (reflectTest a han had
    (dilateTest (Qinv q) hqi_n hqi_d g)) (reflectTest a han had f)
  have haN_num : 0 < (mul (Qinv q) a).num := Int.mul_pos hqi_n han
  have haN_den : 0 < (mul (Qinv q) a).den := Qmul_den_pos hqi_d had
  have hwN_den : 0 < (mul (Qinv q) w).den := Qmul_den_pos hqi_d hw
  have hwN_num : 0 ≤ (mul (Qinv q) w).num := Int.mul_nonneg (Int.le_of_lt hqi_n) hwn
  have hw1_den : 0 < (Qsub a (mul (Qinv q) a)).den := Qsub_den_pos had haN_den
  have hw1_num : 0 < (Qsub a (mul (Qinv q) a)).num := w1_num_pos_gen a han had q hqn hq1
  have CoreLB : Qle a (mul (Qinv q) (add a w)) := Int.le_of_lt (CoreStrict_gen a w q hqn hcore)
  have hdistrib : Qeq (add (mul (Qinv q) a) (mul (Qinv q) w)) (mul (Qinv q) (add a w)) := by
    simp only [Qeq, add, mul, Qinv]; push_cast [hq_toNat]; ring_uor
  have h_a_le_aNwN : Qle a (add (mul (Qinv q) a) (mul (Qinv q) w)) :=
    Qle_trans (Qmul_den_pos hqi_d (add_den_pos had hw)) CoreLB (Qeq_le (Qeq_symm hdistrib))
  have hle : Qle (Qsub a (mul (Qinv q) a)) (mul (Qinv q) w) :=
    Qsub_le_of_le_add haN_den hwN_den h_a_le_aNwN
  have hw2n : 0 ≤ (Qsub (mul (Qinv q) w) (Qsub a (mul (Qinv q) a))).num :=
    Qsub_num_nonneg_of_le hle
  have hawn : 0 ≤ (add a w).num := by
    show (0 : Int) ≤ a.num * (w.den : Int) + w.num * (a.den : Int)
    exact Int.add_nonneg (Int.mul_nonneg (Int.le_of_lt han) (Int.ofNat_nonneg w.den))
      (Int.mul_nonneg hwn (Int.ofNat_nonneg a.den))
  have hw1'_den : 0 < (Qsub (mul (Qinv q) (add a w)) a).den :=
    Qsub_den_pos (Qmul_den_pos hqi_d (add_den_pos had hw)) had
  have hw1'_num : 0 < (Qsub (mul (Qinv q) (add a w)) a).num :=
    Qsub_num_pos_of_lt (CoreStrict_gen a w q hqn hcore)
  have hle' : Qle (Qsub (mul (Qinv q) (add a w)) a) w :=
    Qsub_le_of_le_add had hw (inv_q_mul_le (add a w) hawn q hqn hqd hq1le)
  have hw2n' : 0 ≤ (Qsub w (Qsub (mul (Qinv q) (add a w)) a)).num :=
    Qsub_num_nonneg_of_le hle'
  have QB1 : Qeq (add (mul (Qinv q) a) (Qsub a (mul (Qinv q) a))) a := by
    simp only [Qeq, add, neg, mul, Qsub, Qinv]; push_cast [hq_toNat]; ring_uor
  have QB2 : Qeq (Qsub (mul (Qinv q) w) (Qsub a (mul (Qinv q) a)))
      (Qsub (mul (Qinv q) (add a w)) a) := by
    simp only [Qeq, add, neg, mul, Qsub, Qinv]; push_cast [hq_toNat]; ring_uor
  have QC1 : Qeq (mul (mul q b) (add a (Qsub (mul (Qinv q) (add a w)) a))) (mul b (add a w)) := by
    simp only [Qeq, add, neg, mul, Qsub, Qinv]; push_cast [hq_toNat]; ring_uor
  have QC2 : Qle (⟨1, 1⟩ : Q) (mul b (add a w)) :=
    Qle_trans (Qmul_den_pos hbd (Qinv_den_pos hbn)) (Qeq_le (Qeq_symm (Qmul_Qinv hbn)))
      (Qmul_le_mul_left (Int.le_of_lt hbn) hfit)
  have Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul q b) (add a (Qsub (mul (Qinv q) (add a w)) a))) :=
    Qle_trans (Qmul_den_pos hbd (add_den_pos had hw)) QC2 (Qeq_le (Qeq_symm QC1))
  have Ha : Qle a (add a (Qsub (mul (Qinv q) (add a w)) a)) :=
    Qle_add_right_nonneg (Int.le_of_lt hw1'_num)
  have hlon' : 0 < (add a (Qsub (mul (Qinv q) (add a w)) a)).num :=
    qnum_pos_of_le han (add_den_pos had hw1'_den) Ha
  -- STEP A: dilate by 1/q onto [a/q, (a+w)/q]
  have stepA : Req (haarIntegral PnF a han had a w had hw hwn)
      (haarIntegral (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den (mul (Qinv q) a) (mul (Qinv q) w)
        haN_den hwN_den hwN_num) :=
    Req_trans
      (haarIntegral_congr_Q PnF a han had a w
        (mul q (mul (Qinv q) a)) (mul q (mul (Qinv q) w))
        had hw hwn (Qmul_den_pos hqd haN_den) (Qmul_den_pos hqd hwN_den)
        (Int.mul_nonneg (Int.le_of_lt hqn) hwN_num)
        (Qeq_symm (q_mul_inv_q q a hqn)) (Qeq_symm (q_mul_inv_q q w hqn)))
      (haarIntegral_dilate PnF q hqn hqd (mul (Qinv q) a) a
        haN_num haN_den han had (mul (Qinv q) a) (mul (Qinv q) w) haN_den hwN_den hwN_num
        (Rle_of_Req (Req_refl _))
        (Rle_ofQ_ofQ had (Qmul_den_pos hqd haN_den)
          (Qeq_le (Qeq_symm (q_mul_inv_q q a hqn)))))
  -- STEP B: drop the support-free left piece [a/q, a]
  have hleftDN : Req (haarIntegral (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den (mul (Qinv q) a) (Qsub a (mul (Qinv q) a))
        haN_den hw1_den (Int.le_of_lt hw1_num)) zero :=
    left_DN_window_vanish_Q f g a han had q hqn hqd hgh_f (mul (Qinv q) a) haN_num haN_den
      (mul (Qinv q) a) (Qsub a (mul (Qinv q) a)) haN_den hw1_den (Int.le_of_lt hw1_num)
      haN_num (Qeq_le QB1) (Qeq_le (Qeq_symm (q_mul_inv_q q a hqn)))
  have stepB : Req (haarIntegral (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den (mul (Qinv q) a) (mul (Qinv q) w)
        haN_den hwN_den hwN_num)
      (haarIntegral (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den
        (add (mul (Qinv q) a) (Qsub a (mul (Qinv q) a)))
        (Qsub (mul (Qinv q) w) (Qsub a (mul (Qinv q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n) :=
    Req_trans
      (haarIntegral_split_at (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den (mul (Qinv q) a) (mul (Qinv q) w)
        (Qsub a (mul (Qinv q) a)) haN_den hwN_den hwN_num hw1_den hw1_num hle hw2n)
      (Req_trans (Radd_congr hleftDN (Req_refl _))
        (Req_trans (Radd_comm zero _) (Radd_zero _)))
  -- STEP C: align window to core, swap floor + integrand
  have stepC : Req (haarIntegral (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den
        (add (mul (Qinv q) a) (Qsub a (mul (Qinv q) a)))
        (Qsub (mul (Qinv q) w) (Qsub a (mul (Qinv q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n)
      (haarIntegral P1nF a han had a (Qsub (mul (Qinv q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_congr_Q (dilateTest q hqn hqd PnF)
        (mul (Qinv q) a) haN_num haN_den
        (add (mul (Qinv q) a) (Qsub a (mul (Qinv q) a)))
        (Qsub (mul (Qinv q) w) (Qsub a (mul (Qinv q) a)))
        a (Qsub (mul (Qinv q) (add a w)) a)
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n
        had hw1'_den (Int.le_of_lt hw1'_num) QB1 QB2)
      (haarIntegral_congr_window (dilateTest q hqn hqd PnF) P1nF
        (mul (Qinv q) a) a haN_num haN_den han had
        a (Qsub (mul (Qinv q) (add a w)) a) had hw1'_den (Int.le_of_lt hw1'_num)
        (fun x h0 _h1 => core_integrand_agree_Q f g a han had q hqn hqd hq1le
          (affineMap a (Qsub (mul (Qinv q) (add a w)) a) had hw1'_den x)
          (Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw1'_den (Int.le_of_lt hw1'_num))
            (Rnonneg_of_Rle_zero h0)))))
  -- STEP D: drop the support-free right piece
  have hrightI1n : Req (haarIntegral P1nF a han had
        (add a (Qsub (mul (Qinv q) (add a w)) a)) (Qsub w (Qsub (mul (Qinv q) (add a w)) a))
        (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n') zero :=
    right_I1n_window_vanish_Q f g a han had q hqn hqd b hbd hbn hgl_g
      (add a (Qsub (mul (Qinv q) (add a w)) a)) (Qsub w (Qsub (mul (Qinv q) (add a w)) a))
      (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n' hlon' Ha Hbig
  have stepD : Req (haarIntegral P1nF a han had a w had hw hwn)
      (haarIntegral P1nF a han had a (Qsub (mul (Qinv q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_split_at P1nF a han had a w (Qsub (mul (Qinv q) (add a w)) a)
        had hw hwn hw1'_den hw1'_num hle' hw2n')
      (Req_trans (Radd_congr (Req_refl _) hrightI1n) (Radd_zero _))
  show Req (haarIntegral PnF a han had a w had hw hwn) (haarIntegral P1nF a han had a w had hw hwn)
  exact Req_trans stepA (Req_trans stepB (Req_trans stepC (Req_symm stepD)))

/-- The Haar form respects rational equality of the scale: `Qeq q q' ⟹ H_q(f,g) ≈ H_{q'}(f,g)`. -/
theorem HForm_congr_scale (f g : L2Test) (q q' : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hq'n : 0 < q'.num) (hq'd : 0 < q'.den) (h : Qeq q q')
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (HForm f g q hqn hqd a han had w hw hwn) (HForm f g q' hq'n hq'd a han had w hw hwn) :=
  haarIntegral_congr_window
    (productTest (reflectTest a han had (dilateTest q hqn hqd f)) (reflectTest a han had g))
    (productTest (reflectTest a han had (dilateTest q' hq'n hq'd f)) (reflectTest a han had g))
    a a han had han had a w had hw hwn
    (fun x _ _ => Rmul_congr (Rmul_congr
      (f.hfc _ _ (Rmul_congr (ofQ_congr hqd hq'd h) (Req_refl _))) (Req_refl _)) (Req_refl _))

/-- **★ TWO-TEST RECIPROCITY AT EVERY RATIONAL SCALE `q ≥ 1`** (no overlap hypothesis): strict core,
    degenerate `a+w ≤ q·a` (both sides `0`), and `q ≈ 1` (integrand commutation). -/
theorem HForm_recip_all_Q (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (HForm f g q hqn hqd a han had w hw hwn)
        (HForm g f (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) a han had w hw hwn) := by
  rcases Qle_or_Qlt q (⟨1, 1⟩ : Q) with hle | hlt
  · -- q ≈ 1
    have hq_eq : Qeq q (⟨1, 1⟩ : Q) := by
      have h1 := hle; have h2 := hq1
      simp only [Qle] at h1 h2; simp only [Qeq]; omega
    have hqi_eq : Qeq (Qinv q) (⟨1, 1⟩ : Q) := Qinv_congr hqn (by decide) hq_eq
    refine Req_trans (HForm_congr_scale f g q (⟨1, 1⟩ : Q) hqn hqd (by decide) (by decide) hq_eq
      a han had w hw hwn) ?_
    refine Req_trans (HForm_recip_one f g a han had w hw hwn) ?_
    exact HForm_congr_scale g f (⟨1, 1⟩ : Q) (Qinv q) (by decide) (by decide)
      (Qinv_num_pos hqd) (Qinv_den_pos hqn) (Qeq_symm hqi_eq) a han had w hw hwn
  · -- q > 1
    rcases Qle_or_Qlt (add a w) (mul q a) with hdeg | hcore
    · -- degenerate: both sides vanish
      have hL : Req (HForm f g q hqn hqd a han had w hw hwn) zero :=
        Pn_window_vanish_degen_Q f g a han had q hqn hqd hgh_f w hw hwn hdeg
      have QC2 : Qle (⟨1, 1⟩ : Q) (mul b (add a w)) :=
        Qle_trans (Qmul_den_pos hbd (Qinv_den_pos hbn)) (Qeq_le (Qeq_symm (Qmul_Qinv hbn)))
          (Qmul_le_mul_left (Int.le_of_lt hbn) hfit)
      have step : Qle (mul b (add a w)) (mul (mul q b) a) :=
        Qle_trans (Qmul_den_pos hbd (Qmul_den_pos hqd had))
          (Qmul_le_mul_left (Int.le_of_lt hbn) hdeg)
          (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
      have Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul q b) a) :=
        Qle_trans (Qmul_den_pos hbd (add_den_pos had hw)) QC2 step
      have hR : Req (HForm g f (Qinv q) (Qinv_num_pos hqd) (Qinv_den_pos hqn) a han had w hw hwn)
          zero :=
        right_I1n_window_vanish_Q f g a han had q hqn hqd b hbd hbn hgl_g a w had hw hwn han
          (Qle_refl a) Hbig
      exact Req_trans hL (Req_symm hR)
    · exact HForm_recip_core_Q f g a han had w hw hwn b hbd hbn q hqn hqd hlt hgh_f hgl_g hfit hcore

end UOR.Bridge.F1Square.Square
