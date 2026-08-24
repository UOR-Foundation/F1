/-
F1 square — **the genuine two-test finite-prime Haar bilinear form** (`WeilPrimeShiftHaarForm.lean`).

Replaces the scalar façade (`Nop`/`primePlaceOp` were weighted point evaluation) with a real
two-input Haar form on TWO independent compactly-supported tests `f, g`:

    H_q(f,g) = ∫ f(q/t)·g(1/t) d^×t = mulConv f (reflectTest a g) q      (Haar integral)
    B_q(f,g) = q^{-1/2}·H_q(f,g)                                          (the q^{-1/2} normalization)

with the DIAGONAL `H_q(g,g) = autocorr g q` HOLDING DEFINITIONALLY (autocorr = mulConv g (reflectTest g)).

The load-bearing new result is the genuine two-test reciprocal / adjoint change of variables, proved
WITHOUT assuming reciprocal symmetry — a direct generalization of `autocorr_recip_core` from `(g,g)`
to two independent tests threaded through the SAME Route-D scaffold (dilate → split → drop
support-free pieces → match on the core). The core integrand identity is
`(dilate_n H_{f,g})(t) = f(1/t)·g(1/(nt)) = g(1/(nt))·f(1/t) = H_{g,f}(t)` — `Rmul_comm` plus the same
density cancellation `n·(1/max(nt,a)) = 1/max(t,a)`:

    H_q(f,g) = H_{1/q}(g,f)          (`HForm_recip`)
    B_q(f,g) = q^{-1}·B_{1/q}(g,f)   (`BForm_adjoint`, the CORRECT operator law N_q* = q^{-1} N_{1/q})

Both are TWO-INPUT identities on independent vectors — NOT diagonal reciprocity of a single `h`.

Support/window hypotheses are threaded for BOTH tests (fixed bounded windows are not automatically
dilation-stable). Reuses the existing `haarIntegral_dilate`, `haarIntegral_split_at`,
`haarIntegral_congr_window`, `haarIntegral_window_vanish`, `core`-arithmetic, and `reflectTest_ofQ`
from `WeilPrimeShiftRecipAutocorr` — nothing rebuilt. No `primeGram`, no `vFrom`/`vHat`, no PSD, no
trace wrappers.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftOperator

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The two-test convolution integrand `(reflect(dilate_s f))·(reflect g)`, point value.
-- ===========================================================================

/-- **The two-test convolution integrand at a rational point `Qv ≥ a`**: with first factor the reflected
    `s`-dilation of `f` and second factor the reflected `g`, its value at `Qv` is `f(s/Qv)·g(1/Qv)`. -/
theorem Ps_ofQ2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (s : Q) (hsn : 0 < s.num) (hsd : 0 < s.den) (Qv : Q) (hQd : 0 < Qv.den) (hQn : 0 < Qv.num)
    (haQ : Qle a Qv) :
    Req ((productTest (reflectTest a han had (dilateTest s hsn hsd f)) (reflectTest a han had g)).f
          (ofQ Qv hQd))
        (Rmul (f.f (ofQ (mul s (Qinv Qv)) (Qmul_den_pos hsd (Qinv_den_pos hQn))))
              (g.f (ofQ (Qinv Qv) (Qinv_den_pos hQn)))) :=
  Rmul_congr
    (Req_trans (reflectTest_ofQ a Qv han had hQd hQn haQ (dilateTest s hsn hsd f))
      (f.hfc _ _ (Rmul_ofQ_ofQ hsd (Qinv_den_pos hQn))))
    (reflectTest_ofQ a Qv han had hQd hQn haQ g)

/-- **High-side vanishing at a sample point** `qp ≤ a`: the dilated two-test integrand
    `dilateTest n (Pn := (reflect(dilate_n f))·(reflect g))` vanishes at `ofQ qp` — its first factor is
    `f(1/qp)` and `1/qp ≥ 1/a`, so `hgh_f` fires. -/
theorem dilDN_pt_zero2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num)
    (hqp_le_a : Qle qp a) (hnqp_ge_a : Qle a (mul (⟨(n : Int), 1⟩ : Q) qp)) :
    Req ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
           (productTest (reflectTest a han had
                (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
              (reflectTest a han had g))).f (ofQ qp hqpd)) zero := by
  have hmn : 0 < (mul (⟨(n : Int), 1⟩ : Q) qp).num :=
    Int.mul_pos (by show (0 : Int) < (n : Int); exact_mod_cast hn0) hqpn
  have hmd : 0 < (mul (⟨(n : Int), 1⟩ : Q) qp).den := Qmul_den_pos Nat.one_pos hqpd
  have e1 : Req ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
        (productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
          (reflectTest a han had g))).f (ofQ qp hqpd))
      ((productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
          (reflectTest a han had g)).f (ofQ (mul (⟨(n : Int), 1⟩ : Q) qp) hmd)) :=
    (productTest (reflectTest a han had
        (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
      (reflectTest a han had g)).hfc _ _ (Rmul_ofQ_ofQ Nat.one_pos hqpd)
  have e2 := Ps_ofQ2 f g a han had (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
    (mul (⟨(n : Int), 1⟩ : Q) qp) hmd hmn hnqp_ge_a
  have hfle : Qle (Qinv a)
      (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) qp))) :=
    Qle_trans (Qinv_den_pos hqpn) (Qinv_antitone han hqpn hqp_le_a)
      (Qeq_le (Qeq_symm (mul_n_Qinv_mul_n n qp hqpn)))
  have hfz : Req (f.f (ofQ (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) qp)))
        (Qmul_den_pos Nat.one_pos (Qinv_den_pos hmn)))) zero :=
    hgh_f _ (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hmn)) hfle)
  refine Req_trans e1 (Req_trans e2 ?_)
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- **Low-side vanishing at a sample point** `1 ≤ n·b·qp`: the two-test integrand for `H_{1/n}(g,f)`,
    `(reflect(dilate_{1/n} g))·(reflect f)`, vanishes at `ofQ qp` — its first factor is `g(1/(n·qp))`
    and `1/(n·qp) ≤ b`, so `hgl_g` fires. -/
theorem P1n_pt_zero2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (b : Q) (hbd : 0 < b.den) (_hbn : 0 < b.num)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp)
    (hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) qp)) :
    Req ((productTest (reflectTest a han had
           (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g)) (reflectTest a han had f)).f
          (ofQ qp hqpd)) zero := by
  have e2 := Ps_ofQ2 g f a han had (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 qp hqpd hqpn haqp
  have hlow : Qle (mul (⟨1, n⟩ : Q) (Qinv qp)) b := qlow_engine b n hqpn hbig
  have hfz : Req (g.f (ofQ (mul (⟨1, n⟩ : Q) (Qinv qp))
        (Qmul_den_pos hn0 (Qinv_den_pos hqpn)))) zero :=
    hgl_g _ (Rle_ofQ_ofQ (Qmul_den_pos hn0 (Qinv_den_pos hqpn)) hbd hlow)
  refine Req_trans e2 ?_
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

-- ===========================================================================
-- Window vanishing of the two integrands, via `haarIntegral_window_vanish`.
-- ===========================================================================

/-- **The dilated high-side integrand vanishes over a window at/below `a`** (`a ≤ n·lo`): every sample
    `qp ≤ lo+w ≤ a`, and `n·qp ≥ a`, so `dilDN_pt_zero2` fires (dilated factor `f`). -/
theorem left_DN_window_vanish2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (af : Q) (hafn : 0 < af.num) (hafd : 0 < af.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (H1 : Qle (add lo w) a) (H2 : Qle a (mul (⟨(n : Int), 1⟩ : Q) lo)) :
    Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
             Nat.one_pos
             (productTest (reflectTest a han had
                  (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                    Nat.one_pos f)) (reflectTest a han had g)))
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
  have hnqp_ge_a : Qle a (mul (⟨(n : Int), 1⟩ : Q) (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))) :=
    Qle_trans (Qmul_den_pos Nat.one_pos hlo) H2
      (Qmul_le_mul_left (Int.ofNat_nonneg n) hlo_qp)
  exact Req_trans
    ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos
        (productTest (reflectTest a han had
            (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
              Nat.one_pos f)) (reflectTest a han had g))).hfc _ _ step1)
    (dilDN_pt_zero2 f g a han had n hn0 hgh_f (add lo (mul w (⟨(i : Int), N + 1⟩ : Q))) hqpd hqpn
      hqp_le_a hnqp_ge_a)

/-- **The low-side integrand vanishes over a window at/above `a`** (`a ≤ lo`, `1 ≤ n·b·lo`): every
    sample `qp ≥ lo ≥ a`, and `n·b·qp ≥ 1`, so `P1n_pt_zero2` fires (dilated factor `g`). -/
theorem right_I1n_window_vanish2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hlon : 0 < lo.num)
    (Ha : Qle a lo) (Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) lo)) :
    Req (haarIntegral (productTest (reflectTest a han had
             (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g)) (reflectTest a han had f))
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
      (reflectTest a han had f)).hfc _ _ step1)
    (P1n_pt_zero2 f g a han had n hn0 b hbd hbn hgl_g (add lo (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn haqp hbig)

-- ===========================================================================
-- The two-test crux pointwise identity on the core window.
-- ===========================================================================

/-- **The two-test reciprocal change-of-variables integrand identity** on the band `t ≥ a`:
    `(dilateTest n P_{f,g})(t)·(1/max(t,a/n)) ≈ P_{g,f}(t)·(1/max(t,a))`, where
    `P_{f,g} = (reflect(dilate_n f))·(reflect g)` and `P_{g,f} = (reflect(dilate_{1/n} g))·(reflect f)`.
    The density cancellation `n·(1/max(nt,a)) = 1/max(t,a)` is `clampedInv_dilate_on`; the two factors
    swap by `Rmul_comm` (`f`-factor and `g`-factor). Heart of the two-test reciprocal duality. -/
theorem core_integrand_agree2 (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n) (t : Real) (ht : Rle (ofQ a had) t) :
    Req (Rmul ((dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                 Nat.one_pos
                 (productTest (reflectTest a han had
                      (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0)
                        Nat.one_pos f)) (reflectTest a han had g))).f t)
              (clampedInv (mul (⟨1, n⟩ : Q) a)
                (by show (0 : Int) < 1 * a.num; rw [Int.one_mul]; exact han)
                (Qmul_den_pos hn0 had) t))
        (Rmul ((productTest (reflectTest a han had
                    (dilateTest (⟨1, n⟩ : Q) (by show (0 : Int) < 1; decide) hn0 g))
                  (reflectTest a han had f)).f t)
              (clampedInv a han had t)) := by
  have hnn_num : (0 : Int) < (n : Int) := by exact_mod_cast hn0
  have h0t : Rnonneg t := Rnonneg_of_Rle_zero
    (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ had (Int.le_of_lt han))) ht)
  have hone11 : Req (ofQ (⟨1, 1⟩ : Q) (by decide)) one := Req_of_seq_Qeq (fun _ => Qeq_refl _)
  have h1n : Qle (⟨1, 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) := by simp only [Qle]; push_cast; omega
  have ht_le_nt : Rle t (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t) :=
    Rle_trans
      (Rle_of_Req (Req_trans (Req_symm (Rone_mul t))
        (Rmul_congr (Req_symm hone11) (Req_refl t))))
      (Rmul_le_Rmul_right h0t (Rle_ofQ_ofQ (by decide) Nat.one_pos h1n))
  have hant : Rle (ofQ a had) (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t) :=
    Rle_trans ht ht_le_nt
  have DIL : Req (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
        (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t)))
      (clampedInv a han had t) :=
    clampedInv_dilate_on (⟨(n : Int), 1⟩ : Q) a a Nat.one_pos han had han had ht hant
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
  -- f in the dilated slot, g in the plain slot (of the LHS); swapped on the RHS
  have hfirstL := f.hfc _ _ DIL
  have hfirstR := g.hfc _ _ Econgr
  have hinner : Req
      (Rmul (f.f (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)
              (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
            (g.f (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
      (Rmul (g.f (Rmul (ofQ (⟨1, n⟩ : Q) hn0) (clampedInv a han had t)))
            (f.f (clampedInv a han had t))) :=
    Req_trans (Rmul_congr hfirstL (Req_refl _))
      (Req_trans (Rmul_comm (f.f (clampedInv a han had t))
          (g.f (clampedInv a han had (Rmul (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) t))))
        (Req_symm (Rmul_congr hfirstR (Req_refl _))))
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
-- The two-test Haar bilinear form and its reciprocal law.
-- ===========================================================================

/-- **The two-test finite-prime Haar form** `H_q(f,g) = ∫ f(q/t)·g(1/t) d^×t = mulConv f (reflect g) q`,
    on the window `[a, a+w]` (lo = a).  DIAGONAL: `H_q(g,g) = autocorr g q` DEFINITIONALLY. -/
def HForm (f g : L2Test) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  mulConv f (reflectTest a han had g) q hqn hqd a han had a w had hw hwn

/-- `H_q(g,g) = autocorr g q` — the diagonal of the two-test Haar form IS the autocorrelation. -/
theorem HForm_diag (g : L2Test) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    HForm g g q hqn hqd a han had w hw hwn
      = autocorr g q hqn hqd a han had a w had hw hwn := rfl

set_option maxHeartbeats 2000000 in
/-- **★ THE TWO-TEST RECIPROCAL / ADJOINT LAW** `H_q(f,g) = H_{1/q}(g,f)` (for `2 ≤ n`, `q = n`):
    the genuine two-input Haar change of variables on independent compactly-supported tests, proved
    WITHOUT assuming reciprocal symmetry.  Route D generalized to two tests: dilate `H_n(f,g)` by
    `1/n` onto `[a/n, (a+w)/n]` (`haarIntegral_dilate`), drop the support-free pieces
    (`left_DN_window_vanish2` uses `hgh_f`, `right_I1n_window_vanish2` uses `hgl_g`), and match on the
    core (`core_integrand_agree2`).  The diagonal `f = g` recovers `autocorr_recip_core`. -/
theorem HForm_recip_core (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hcore : Qlt (mul (⟨(n : Int), 1⟩ : Q) a) (add a w)) :
    Req (HForm f g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had w hw hwn)
        (HForm g f (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had w hw hwn) := by
  have hsn : (0 : Int) < (n : Int) := Int.ofNat_pos.mpr hn0
  let PnF : L2Test := productTest (reflectTest a han had
      (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos f)) (reflectTest a han had g)
  let P1nF : L2Test := productTest (reflectTest a han had
      (dilateTest (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 g)) (reflectTest a han had f)
  have haN_num : 0 < (mul (⟨1, n⟩ : Q) a).num := by
    show (0 : Int) < 1 * a.num; rw [Int.one_mul]; exact han
  have haN_den : 0 < (mul (⟨1, n⟩ : Q) a).den := Qmul_den_pos hn0 had
  have hwN_den : 0 < (mul (⟨1, n⟩ : Q) w).den := Qmul_den_pos hn0 hw
  have hwN_num : 0 ≤ (mul (⟨1, n⟩ : Q) w).num := by
    show (0 : Int) ≤ 1 * w.num; rw [Int.one_mul]; exact hwn
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
  -- STEP A: H_n(f,g) ≈ dilate-1/n onto [a/n, (a+w)/n]
  have stepA : Req (haarIntegral PnF a han had a w had hw hwn)
      (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        haN_den hwN_den hwN_num) :=
    Req_trans
      (haarIntegral_congr_Q PnF a han had a w
        (mul (⟨(n : Int), 1⟩ : Q) (mul (⟨1, n⟩ : Q) a)) (mul (⟨(n : Int), 1⟩ : Q) (mul (⟨1, n⟩ : Q) w))
        had hw hwn (Qmul_den_pos Nat.one_pos haN_den) (Qmul_den_pos Nat.one_pos hwN_den)
        (Int.mul_nonneg (Int.le_of_lt hsn) hwN_num)
        (Qeq_symm (n_mul_inv_n n a)) (Qeq_symm (n_mul_inv_n n w)))
      (haarIntegral_dilate PnF (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos (mul (⟨1, n⟩ : Q) a) a
        haN_num haN_den han had (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w) haN_den hwN_den hwN_num
        (Rle_of_Req (Req_refl _))
        (Rle_ofQ_ofQ had (Qmul_den_pos Nat.one_pos haN_den)
          (Qeq_le (Qeq_symm (n_mul_inv_n n a)))))
  -- STEP B: drop the support-free left piece [a/n, a]
  have hleftDN : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a))
        haN_den hw1_den (Int.le_of_lt hw1_num)) zero :=
    left_DN_window_vanish2 f g a han had n hn0 hgh_f (mul (⟨1, n⟩ : Q) a) haN_num haN_den
      (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)) haN_den hw1_den (Int.le_of_lt hw1_num)
      haN_num (Qeq_le QB1) (Qeq_le (Qeq_symm (n_mul_inv_n n a)))
  have stepB : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        haN_den hwN_den hwN_num)
      (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n) :=
    Req_trans
      (haarIntegral_split_at (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den (mul (⟨1, n⟩ : Q) a) (mul (⟨1, n⟩ : Q) w)
        (Qsub a (mul (⟨1, n⟩ : Q) a)) haN_den hwN_den hwN_num hw1_den hw1_num hle hw2n)
      (Req_trans (Radd_congr hleftDN (Req_refl _))
        (Req_trans (Radd_comm zero _) (Radd_zero _)))
  -- STEP C: align window to core, swap floor + integrand to P_{g,f}
  have stepC : Req (haarIntegral (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n)
      (haarIntegral P1nF a han had a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_congr_Q (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF)
        (mul (⟨1, n⟩ : Q) a) haN_num haN_den
        (add (mul (⟨1, n⟩ : Q) a) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        (Qsub (mul (⟨1, n⟩ : Q) w) (Qsub a (mul (⟨1, n⟩ : Q) a)))
        a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        (add_den_pos haN_den hw1_den) (Qsub_den_pos hwN_den hw1_den) hw2n
        had hw1'_den (Int.le_of_lt hw1'_num) QB1 QB2)
      (haarIntegral_congr_window (dilateTest (⟨(n : Int), 1⟩ : Q) hsn Nat.one_pos PnF) P1nF
        (mul (⟨1, n⟩ : Q) a) a haN_num haN_den han had
        a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) had hw1'_den (Int.le_of_lt hw1'_num)
        (fun x h0 _h1 => core_integrand_agree2 f g a han had n hn0
          (affineMap a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a) had hw1'_den x)
          (Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw1'_den (Int.le_of_lt hw1'_num))
            (Rnonneg_of_Rle_zero h0)))))
  -- STEP D: drop the support-free right piece [(a+w)/n, a+w] of H_{1/n}(g,f)
  have hrightI1n : Req (haarIntegral P1nF a han had
        (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)) (Qsub w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))
        (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n') zero :=
    right_I1n_window_vanish2 f g a han had n hn0 b hbd hbn hgl_g
      (add a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)) (Qsub w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a))
      (add_den_pos had hw1'_den) (Qsub_den_pos hw hw1'_den) hw2n' hlon' Ha Hbig
  have stepD : Req (haarIntegral P1nF a han had a w had hw hwn)
      (haarIntegral P1nF a han had a (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw1'_den (Int.le_of_lt hw1'_num)) :=
    Req_trans
      (haarIntegral_split_at P1nF a han had a w (Qsub (mul (⟨1, n⟩ : Q) (add a w)) a)
        had hw hwn hw1'_den hw1'_num hle' hw2n')
      (Req_trans (Radd_congr (Req_refl _) hrightI1n) (Radd_zero _))
  show Req (haarIntegral PnF a han had a w had hw hwn) (haarIntegral P1nF a han had a w had hw hwn)
  exact Req_trans stepA (Req_trans stepB (Req_trans stepC (Req_symm stepD)))

/-- **The two-test reciprocal / adjoint law (strict-core regime)** `H_n(f,g) = H_{1/n}(g,f)` on
    independent compactly-supported tests, for `n ≥ 2` in the overlapping-core regime `n·a < a+w`
    (`hcore`).  The all-scale version WITHOUT `hcore` is `HForm_recip_all`.  (In the fold only places with
    `Λ(n) ≠ 0` contribute, and `Λ(n) ≠ 0 ⟹ n ≥ 2`; `n = 1` is vacuous since `Λ(1) = 0`.)  Alias of
    `HForm_recip_core`. -/
theorem HForm_recip (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hcore : Qlt (mul (⟨(n : Int), 1⟩ : Q) a) (add a w)) :
    Req (HForm f g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had w hw hwn)
        (HForm g f (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had w hw hwn) :=
  HForm_recip_core f g a han had w hw hwn b hbd hbn n hn0 hn2 hgh_f hgl_g hfit hcore

-- ===========================================================================
-- The DEGENERATE regime (a+w ≤ n·a): both two-test forms vanish, giving all-scale reciprocity.
-- ===========================================================================

/-- **Degenerate high-side pointwise vanishing** (`qp ≤ n·a`): the `H_n(f,g)` integrand
    `(reflect(dilate_n f))·(reflect g)` vanishes at `ofQ qp` — its first factor is `f(n/qp)` with
    `n/qp ≥ 1/a`, so `hgh_f` fires. -/
theorem Pn_pt_zero_degen (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (qp : Q) (hqpd : 0 < qp.den) (hqpn : 0 < qp.num) (haqp : Qle a qp)
    (hqp_le_na : Qle qp (mul (⟨(n : Int), 1⟩ : Q) a)) :
    Req ((productTest (reflectTest a han had
           (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
           (reflectTest a han had g)).f (ofQ qp hqpd)) zero := by
  have hna_num : 0 < (mul (⟨(n : Int), 1⟩ : Q) a).num :=
    Int.mul_pos (by show (0 : Int) < (n : Int); exact_mod_cast hn0) han
  have e2 := Ps_ofQ2 f g a han had (⟨(n : Int), 1⟩ : Q)
    (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos qp hqpd hqpn haqp
  have hfle : Qle (Qinv a) (mul (⟨(n : Int), 1⟩ : Q) (Qinv qp)) := by
    have s1 : Qle (Qinv (mul (⟨(n : Int), 1⟩ : Q) a)) (Qinv qp) :=
      Qinv_antitone hna_num hqpn hqp_le_na
    have s2 : Qle (mul (⟨(n : Int), 1⟩ : Q) (Qinv (mul (⟨(n : Int), 1⟩ : Q) a)))
                  (mul (⟨(n : Int), 1⟩ : Q) (Qinv qp)) :=
      Qmul_le_mul_left (by show (0 : Int) ≤ (n : Int); exact Int.ofNat_nonneg n) s1
    exact Qle_trans (Qmul_den_pos Nat.one_pos (Qinv_den_pos hna_num))
      (Qeq_le (Qeq_symm (mul_n_Qinv_mul_n n a han))) s2
  have hfz : Req (f.f (ofQ (mul (⟨(n : Int), 1⟩ : Q) (Qinv qp))
        (Qmul_den_pos Nat.one_pos (Qinv_den_pos hqpn)))) zero :=
    hgh_f _ (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hqpn)) hfle)
  refine Req_trans e2 ?_
  exact Req_trans (Rmul_congr hfz (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))

/-- **The `H_n(f,g)` form vanishes on the window when `a+w ≤ n·a`** — every sample `qp ≤ a+w ≤ n·a`, so
    `Pn_pt_zero_degen` fires. -/
theorem Pn_window_vanish_degen (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (n : Nat) (hn0 : 0 < n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (Hdeg : Qle (add a w) (mul (⟨(n : Int), 1⟩ : Q) a)) :
    Req (haarIntegral (productTest (reflectTest a han had
           (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
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
  have hqp_le_na : Qle (add a (mul w (⟨(i : Int), N + 1⟩ : Q))) (mul (⟨(n : Int), 1⟩ : Q) a) :=
    Qle_trans (add_den_pos had hw) (Qadd_le_add (Qle_refl a) hmul_le) Hdeg
  exact Req_trans
    ((productTest (reflectTest a han had
        (dilateTest (⟨(n : Int), 1⟩ : Q) (by show (0 : Int) < (n : Int); exact_mod_cast hn0) Nat.one_pos f))
        (reflectTest a han had g)).hfc _ _ step1)
    (Pn_pt_zero_degen f g a han had n hn0 hgh_f (add a (mul w (⟨(i : Int), N + 1⟩ : Q)))
      hqpd hqpn hlo_qp hqp_le_na)

/-- **★ ALL-SCALE TWO-TEST RECIPROCITY** `H_n(f,g) = H_{1/n}(g,f)` for EVERY place `n ≥ 2` — NO overlap
    (`hcore`) hypothesis.  Splits on `Qle_or_Qlt (a+w) (n·a)`: the strict-core regime is
    `HForm_recip_core`; the degenerate regime `a+w ≤ n·a` makes BOTH sides `0` — `H_n(f,g)` by the
    high-support vanishing of `f` (`Pn_window_vanish_degen`), and `H_{1/n}(g,f)` by the low-support
    vanishing of `g` together with `hfit` (`right_I1n_window_vanish2`, floor `a`, `1 ≤ n·b·a`). -/
theorem HForm_recip_all (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n) (hn2 : 2 ≤ n)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (HForm f g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had w hw hwn)
        (HForm g f (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had w hw hwn) := by
  rcases Qle_or_Qlt (add a w) (mul (⟨(n : Int), 1⟩ : Q) a) with hdeg | hcore
  · -- degenerate: both sides are 0
    have hL : Req (HForm f g (⟨(n : Int), 1⟩ : Q) (Int.ofNat_pos.mpr hn0) Nat.one_pos a han had w hw hwn)
        zero := Pn_window_vanish_degen f g a han had n hn0 hgh_f w hw hwn hdeg
    have QC2 : Qle (⟨1, 1⟩ : Q) (mul b (add a w)) :=
      Qle_trans (Qmul_den_pos hbd (Qinv_den_pos hbn)) (Qeq_le (Qeq_symm (Qmul_Qinv hbn)))
        (Qmul_le_mul_left (Int.le_of_lt hbn) hfit)
    have step : Qle (mul b (add a w)) (mul (mul (⟨(n : Int), 1⟩ : Q) b) a) :=
      Qle_trans (Qmul_den_pos hbd (Qmul_den_pos Nat.one_pos had))
        (Qmul_le_mul_left (Int.le_of_lt hbn) hdeg)
        (Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor))
    have Hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) a) :=
      Qle_trans (Qmul_den_pos hbd (add_den_pos had hw)) QC2 step
    have hR : Req (HForm g f (⟨1, n⟩ : Q) (show (0 : Int) < 1 by decide) hn0 a han had w hw hwn)
        zero :=
      right_I1n_window_vanish2 f g a han had n hn0 b hbd hbn hgl_g a w had hw hwn han
        (Qle_refl a) Hbig
    exact Req_trans hL (Req_symm hR)
  · exact HForm_recip_core f g a han had w hw hwn b hbd hbn n hn0 hn2 hgh_f hgl_g hfit hcore

-- ===========================================================================
-- The q^{-1/2} normalization B_q(f,g) = q^{-1/2}·H_q(f,g) and its adjoint law.
-- ===========================================================================

/-- `(1/(m+1))·(m+1) = 1` as reals: `ofQ⟨1,m+1⟩·ofQ⟨m+1,1⟩ ≈ one`. -/
theorem ofQ_recip_one (m : Nat) :
    Req (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
              (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)) one :=
  Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos m) Nat.one_pos)
    (Req_trans (ofQ_congr (Qmul_den_pos (Nat.succ_pos m) Nat.one_pos) (by decide)
        (by simp only [Qeq, mul]; push_cast; omega)) (Req_of_seq_Qeq (fun _ => Qeq_refl _)))

/-- The weight identity `√(m+1) = (m+1)·(m+1)^{-1/2}` at the `normWeight` level:
    `normWeight⟨1,m+1⟩ ≈ (m+1)·normWeight⟨m+1,1⟩`. -/
theorem normWeight_recip_lo (m : Nat) (hm : 1 ≤ m) :
    Req (normWeight (⟨1, m + 1⟩ : Q))
        (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
              (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) :=
  Req_trans (normWeight_lo m hm)
    (Req_trans (Req_symm (n_mul_qInvSqrt (m + 1) (Nat.succ_pos m) (oneLeSucc m)))
      (Rmul_congr (Req_refl _) (Req_symm (normWeight_hi m))))

/-- The weight identity `(m+1)^{-1/2} = (m+1)^{-1}·√(m+1)` at the `normWeight` level:
    `normWeight⟨m+1,1⟩ ≈ (m+1)^{-1}·normWeight⟨1,m+1⟩`. -/
theorem normWeight_recip_hi (m : Nat) (hm : 1 ≤ m) :
    Req (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
        (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)) (normWeight (⟨1, m + 1⟩ : Q))) := by
  refine Req_symm ?_
  refine Req_trans (Rmul_congr (Req_refl (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))
      (normWeight_recip_lo m hm)) ?_
  refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
      (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
      (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)))) ?_
  exact Req_trans (Rmul_congr (ofQ_recip_one m) (Req_refl _)) (Rone_mul _)

/-- **The `q^{-1/2}`-normalized two-test Haar form** `B_q(f,g) = q^{-1/2}·H_q(f,g) = normWeight(q)·H_q(f,g)`. -/
def BForm (f g : L2Test) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  Rmul (normWeight q) (HForm f g q hqn hqd a han had w hw hwn)

/-- **★ THE CORRECT ADJOINT LAW (all-scale, no overlap hypothesis)** `B_{m+1}(f,g) = (m+1)^{-1}·B_{1/(m+1)}(g,f)`
    (i.e. `N_q* = q^{-1}N_{1/q}`).  From `HForm_recip_all` (`H_{m+1}(f,g) = H_{1/(m+1)}(g,f)`, EVERY place)
    and the weight identity `(m+1)^{-1/2} = (m+1)^{-1}·√(m+1)`.  No `hcore`; no PSD. -/
theorem BForm_adjoint_all (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (m : Nat) (hm : 1 ≤ m)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
          a han had w hw hwn)
        (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
          (BForm g f (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
            a han had w hw hwn)) := by
  show Req (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
              (HForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                a han had w hw hwn))
           (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
              (Rmul (normWeight (⟨1, m + 1⟩ : Q))
                (HForm g f (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
                  a han had w hw hwn)))
  refine Req_trans (Rmul_congr (Req_refl _)
      (HForm_recip_all f g a han had w hw hwn b hbd hbn (m + 1) (Nat.succ_pos m) (by omega)
        hgh_f hgl_g hfit)) ?_
  refine Req_trans (Rmul_congr (normWeight_recip_hi m hm) (Req_refl _)) ?_
  exact Rmul_assoc _ _ _

/-- **The swapped-scale adjoint law (all-scale)** `B_{1/(m+1)}(f,g) = (m+1)·B_{m+1}(g,f)`.  From
    `HForm_recip_all` in the other order (`H_{1/(m+1)}(f,g) = H_{m+1}(g,f)`) and `√(m+1) = (m+1)·(m+1)^{-1/2}`. -/
theorem BForm_adjoint_swap_all (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (m : Nat) (hm : 1 ≤ m)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (BForm f g (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
          a han had w hw hwn)
        (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
          (BForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
            a han had w hw hwn)) := by
  show Req (Rmul (normWeight (⟨1, m + 1⟩ : Q))
              (HForm f g (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
                a han had w hw hwn))
           (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
              (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
                (HForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                  a han had w hw hwn)))
  refine Req_trans (Rmul_congr (Req_refl _)
      (Req_symm (HForm_recip_all g f a han had w hw hwn b hbd hbn (m + 1) (Nat.succ_pos m) (by omega)
        hgh_g hgl_f hfit))) ?_
  refine Req_trans (Rmul_congr (normWeight_recip_lo m hm) (Req_refl _)) ?_
  exact Rmul_assoc _ _ _

-- ===========================================================================
-- The per-place two-test form P_n(f,g) and its two-input symmetry.
-- ===========================================================================

/-- **The per-place two-test form** `P_m(f,g) = Λ(m+1)·(B_{m+1}(f,g) + (m+1)^{-1}·B_{1/(m+1)}(f,g))`
    (indexed `0`-based, place `m+1`).  Genuine two-input form — `f, g` need not coincide. -/
def PForm (m : Nat) (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  Rmul (vonMangoldt (m + 1))
    (Radd (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
             a han had w hw hwn)
          (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
                (BForm f g (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
                  a han had w hw hwn)))

set_option maxHeartbeats 1000000 in
/-- **★ (Requirement 1) THE TWO-INPUT SYMMETRY (all-scale, no overlap hypothesis)** `P_m(f,g) = P_m(g,f)`
    on independent compactly-supported tests, from the all-scale adjoint law in both scale directions
    (`BForm_adjoint_all`, `BForm_adjoint_swap_all`) and `Radd_comm`.  `m = 0` (`Λ(1) = 0`) is vacuous.
    NO `hcore`; NOT derived from any diagonal assumption; NOT PSD. -/
theorem PForm_symm_all (m : Nat) (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (PForm m f g a han had w hw hwn) (PForm m g f a han had w hw hwn) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have L : Req (PForm 0 f g a han had w hw hwn) zero :=
      Req_trans (Rmul_congr vonMangoldt_one (Req_refl _))
        (Req_trans (Rmul_comm zero _) (Rmul_zero _))
    have R : Req (PForm 0 g f a han had w hw hwn) zero :=
      Req_trans (Rmul_congr vonMangoldt_one (Req_refl _))
        (Req_trans (Rmul_comm zero _) (Rmul_zero _))
    exact Req_trans L (Req_symm R)
  · have hm : 1 ≤ m := hpos
    refine Rmul_congr (Req_refl _) ?_
    have adj1 : Req (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m))
                      Nat.one_pos a han had w hw hwn)
                    (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
                      (BForm g f (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
                        a han had w hw hwn)) :=
      BForm_adjoint_all f g a han had w hw hwn b hbd hbn m hm hgh_f hgl_g hfit
    have adj2 : Req (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
                      (BForm f g (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
                        a han had w hw hwn))
                    (BForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m))
                      Nat.one_pos a han had w hw hwn) := by
      refine Req_trans (Rmul_congr (Req_refl _)
        (BForm_adjoint_swap_all f g a han had w hw hwn b hbd hbn m hm hgh_g hgl_f hfit)) ?_
      refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
          (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
          (BForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
            a han had w hw hwn))) ?_
      exact Req_trans (Rmul_congr (ofQ_recip_one m) (Req_refl _)) (Rone_mul _)
    exact Req_trans (Radd_congr adj1 adj2) (Radd_comm _ _)

-- ===========================================================================
-- The off-diagonal finite fold PrimeForm_X(f,g) = Σ_{m<X} P_m(f,g), symmetric over the FULL cutoff.
-- ===========================================================================

/-- **The off-diagonal finite prime fold** `PrimeForm_X(f,g) = Σ_{m<X} P_m(f,g)` over the complete
    cutoff `X` — a genuine two-input finite fold on independent tests. -/
def PrimeForm (X : Nat) (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  RsumN (fun m => PForm m f g a han had w hw hwn) X

/-- **★ (Requirement 3) SYMMETRY OF THE FULL OFF-DIAGONAL FOLD** `PrimeForm_X(f,g) = PrimeForm_X(g,f)`
    over the COMPLETE cutoff `X`, with NO overlap hypothesis — `RsumN_congr` over the all-scale
    per-place symmetry `PForm_symm_all` (each place, including `m = 0` via `Λ(1) = 0`). -/
theorem PrimeForm_symm (X : Nat) (f g : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (hgh_f : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (f.f y) zero)
    (hgl_f : ∀ y, Rle y (ofQ b hbd) → Req (f.f y) zero)
    (hgh_g : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl_g : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w)) :
    Req (PrimeForm X f g a han had w hw hwn) (PrimeForm X g f a han had w hw hwn) :=
  RsumN_congr X (fun m _ =>
    PForm_symm_all m f g a han had w hw hwn b hbd hbn hgh_f hgl_f hgh_g hgl_g hfit)

-- ===========================================================================
-- The diagonal readback: PrimeForm_X(g,g) IS both weilPrimePart(normAutocorrTest) and the
-- collapsed Burnol sum (the existing primePlaceOp readbacks).
-- ===========================================================================

/-- **The diagonal Haar form is the autocorrelation point value**: `H_q(C.g,C.g) = autocorr C.g q ≈ acPtC C q`
    (in band `0 ≤ q ≤ S`), via `autocorr_eq_autocorrL2` and the `acPt_pos` readback. -/
theorem HForm_diag_acPtC (C : NormCtx) (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den)
    (hq0 : Qle (⟨0, 1⟩ : Q) q) (hqS : Qle q C.S) :
    Req (HForm C.g C.g q hqn hqd C.a C.han C.had C.w C.hw C.hwn) (acPtC C q) :=
  Req_trans
    (autocorr_eq_autocorrL2 C.g q hqn hqd C.a C.han C.had C.a C.w C.had C.hw C.hwn
      C.S C.hSd C.hSn hq0 hqS)
    (Req_symm (acPt_pos C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn q hqd))

set_option maxHeartbeats 800000 in
/-- **★ (Requirement 2) THE DIAGONAL IS THE EXISTING `primePlaceOp`**: `P_m(C.g,C.g) = primePlaceOp (acPtC C) m`
    — the two-test per-place form on the diagonal is exactly the scalar per-place operator of the
    normalized autocorrelation.  `BForm C.g C.g q = normWeight(q)·autocorr C.g q ≈ normWeight(q)·acPtC q
    = Nop (acPtC C) q` via `HForm_diag_acPtC`. -/
theorem PForm_diag (C : NormCtx) (m : Nat) (hmS : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) C.S) :
    Req (PForm m C.g C.g C.a C.han C.had C.w C.hw C.hwn) (primePlaceOp (acPtC C) m) := by
  have hq0hi : Qle (⟨0, 1⟩ : Q) (⟨((m + 1 : Nat) : Int), 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hq0lo : Qle (⟨0, 1⟩ : Q) (⟨1, m + 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hqSlo : Qle (⟨1, m + 1⟩ : Q) C.S := by
    have r1 : Qle (⟨1, m + 1⟩ : Q) (⟨1, 1⟩ : Q) := by simp only [Qle]; push_cast; omega
    exact Qle_trans (by decide) r1 C.hS1
  refine Rmul_congr (Req_refl _)
    (Radd_congr
      (Rmul_congr (Req_refl _)
        (HForm_diag_acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m))
          Nat.one_pos hq0hi hmS))
      (Rmul_congr (Req_refl _)
        (Rmul_congr (Req_refl _)
          (HForm_diag_acPtC C (⟨1, m + 1⟩ : Q) (show (0 : Int) < 1 by decide) (Nat.succ_pos m)
            hq0lo hqSlo))))

/-- **★ (Requirement 6a) THE DIAGONAL FOLD IS `weilPrimePart (normAutocorrTest C)`**: `PrimeForm_X(C.g,C.g)`
    equals the finite-place Weil prime side of the normalized-autocorrelation test.  `RsumN_congr` over
    `PForm_diag` (band from `normCtx_hnS`) then `primePlaceOp_readback`. -/
theorem PrimeForm_diag_weilPrimePart (C : NormCtx) :
    Req (PrimeForm C.X C.g C.g C.a C.han C.had C.w C.hw C.hwn)
        (weilPrimePart (normAutocorrTest C)) :=
  Req_trans (RsumN_congr C.X (fun m hm => PForm_diag C m (normCtx_hnS C m hm)))
    (primePlaceOp_readback C)

/-- **★ (Requirement 6b) THE DIAGONAL FOLD IS THE COLLAPSED BURNOL SUM**: `PrimeForm_X(C.g,C.g)` equals
    `Σ_{m<X} 2·Λ(m+1)·(m+1)^{-1/2}·h(m+1)` (`primePlaceOp_readback_collapsed`). -/
theorem PrimeForm_diag_collapsed (C : NormCtx) :
    Req (PrimeForm C.X C.g C.g C.a C.han C.had C.w C.hw C.hwn)
        (RsumN (fun m => Rmul (vonMangoldt (m + 1))
          (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
            (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m))
              (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q))))) C.X) :=
  Req_trans (RsumN_congr C.X (fun m hm => PForm_diag C m (normCtx_hnS C m hm)))
    (primePlaceOp_readback_collapsed C)

end UOR.Bridge.F1Square.Square
