/-
F1 square — **the autocorrelation-consuming WeilPrimeShift layer** (`WeilPrimeShiftAutocorr.lean`):
`autocorrWeilTest` + `weilPrimeShiftFold_autocorr` — THE FIRST DOWNSTREAM CONSUMER of the committed
`weilPrimeShiftFold`, feeding it the constructed autocorrelation cone object.

The autocorrelation `g ⋆ g^τ`, packaged as a bounded-Lipschitz test in its point variable via
`mulConvRTest g (reflectTest a g) S` (call it `autocorrL2 g`), is bundled into a point-value
`WeilTest` with the support cutoff `X` DERIVED — not hypothesized — from two explicit
compact-support facts on `g`:
  * `hgh` : `g` vanishes at/above the ceiling `1/a`  (high side / integer scales `n`),
  * `hgl` : `g` vanishes at/below a floor `b`         (low side  / reciprocal scales `1/n`).
These give `supp_high` and `supp_low` of the `WeilTest` by the mulConvR-level vanishing lemmas
`autocorrL2_high_vanish` / `autocorrL2_low_vanish` (the mulConvR analogue of deliverable A's
`autocorr_vanish_high`, reproved directly on the real-scale convolution so no `mulConv ↔ mulConvR`
bridge is needed, and extended to the reciprocal side which deliverable A does not cover).

Then `weilPrimeShiftFold_autocorr` is a DIRECT instance of the committed `weilPrimeShiftFold` at
`φ = autocorrL2 g`, so the finite-place Weil shift-fold now has a genuine consumer built on the cone.

HONEST SCOPE. This is the point-value consumer only. It is NOT the positivity of the Weil
functional on the cone (step 4 = RH), NOT the Mellin convolution theorem. The crux fields stay `none`.

SUPPORT-STABILIZATION (subsumed here). The window-restricted integral-vanishing machinery
(`riemannIntegral_le_pts`, `riemannIntegral_pts_zero`, `riemannIntegralI_pts_zero`,
`haarIntegral_window_vanish`) and the band-ratio rational engine (`qnum_pos_of_le`, `qinv_scale_le`,
`qlow_engine`, `qBandQ_ge_ofQ`) are proved here directly on the real-scale convolution `mulConvR`, so
`autocorrL2_high_vanish`/`autocorrL2_low_vanish` derive the `WeilTest` support at both `n` and `1/n`
with no `mulConv ↔ mulConvR` bridge — the support-stabilization prerequisite lives in this module.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/
import F1Square.Square.WeilPrimeShift
import F1Square.Square.MulConvRTest
import F1Square.Square.Autocorr

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Deliverable A machinery (verbatim copies — dropped on integration).
-- ===========================================================================

/-- **Partition-point monotonicity of the certified integral** (deliverable A). -/
theorem riemannIntegral_le_pts {f g : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (hfg : ∀ (N i : Nat), i < N + 1 →
      Rle (f (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))
          (g (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))) :
    Rle (riemannIntegral hLd hLn hlipf hfcf) (riemannIntegral hLd hLn hlipg hfcg) := by
  have hZfReg : RReg (fun j => Radd (dyadicR f 0) (genSum (dyadicTerm f) (digammaMidx L j))) :=
    RReg_add_const (dyadicR f 0) _ (dyadicSum_RReg hLd hLn hlipf hfcf)
  have hZgReg : RReg (fun j => Radd (dyadicR g 0) (genSum (dyadicTerm g) (digammaMidx L j))) :=
    RReg_add_const (dyadicR g 0) _ (dyadicSum_RReg hLd hLn hlipg hfcg)
  have hZle : ∀ j, Rle (Radd (dyadicR f 0) (genSum (dyadicTerm f) (digammaMidx L j)))
      (Radd (dyadicR g 0) (genSum (dyadicTerm g) (digammaMidx L j))) := fun j =>
    Rle_trans (Rle_of_Req (Req_symm (dyadicR_eq f (digammaMidx L j))))
      (Rle_trans (riemannSum_le (2 ^ digammaMidx L j - 1)
          (fun i hi => hfg (2 ^ digammaMidx L j - 1) i hi))
        (Rle_of_Req (dyadicR_eq g (digammaMidx L j))))
  refine Rle_trans (Rle_of_Req (Req_symm
      (Rlim_add_const (dyadicR f 0) _ (dyadicSum_RReg hLd hLn hlipf hfcf) hZfReg))) ?_
  exact Rle_trans (Rlim_le_seq hZfReg hZgReg hZle)
    (Rle_of_Req (Rlim_add_const (dyadicR g 0) _ (dyadicSum_RReg hLd hLn hlipg hfcg) hZgReg))

/-- **Partition-point vanishing of the certified integral** (deliverable A). -/
theorem riemannIntegral_pts_zero {g : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (hz : ∀ (N i : Nat), i < N + 1 →
      Req (g (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N))) zero) :
    Req (riemannIntegral hLd hLn hlipg hfcg) zero := by
  have zlip : ∀ x y, Rle (Rabs (Rsub (zero) (zero))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) :=
    fun x y => Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Radd_neg zero)) Rabs_zero))
      (Rle_zero_of_Rnonneg (Rnonneg_Rmul (Rnonneg_ofQ hLd hLn) (Rnonneg_Rabs _)))
  have zfc : ∀ x y, Req x y → Req (zero) (zero) := fun _ _ _ => Req_refl zero
  have hZ : Req (riemannIntegral (f := fun _ => zero) hLd hLn zlip zfc) zero :=
    riemannIntegral_const_gen zero hLd hLn zlip zfc
  have hle : Rle (riemannIntegral hLd hLn hlipg hfcg)
      (riemannIntegral (f := fun _ => zero) hLd hLn zlip zfc) :=
    riemannIntegral_le_pts hLd hLn hlipg hfcg zlip zfc (fun N i hi => Rle_of_Req (hz N i hi))
  have hge : Rle (riemannIntegral (f := fun _ => zero) hLd hLn zlip zfc)
      (riemannIntegral hLd hLn hlipg hfcg) :=
    riemannIntegral_le_pts hLd hLn zlip zfc hlipg hfcg
      (fun N i hi => Rle_of_Req (Req_symm (hz N i hi)))
  exact Req_trans (Rle_antisymm hle hge) hZ

/-- **Window-restricted vanishing of the interval integral** (deliverable A). -/
theorem riemannIntegralI_pts_zero {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hz : ∀ (N i : Nat), i < N + 1 →
      Req (f (affineMap lo w hlo hw (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))) zero) :
    Req (riemannIntegralI hLd hLn hlip hfc lo w hlo hw hwn) zero := by
  have hinner : Req (riemannIntegral (f := fun x => f (affineMap lo w hlo hw x)) (L := mul L w)
        (Qmul_den_pos hLd hw) (Int.mul_nonneg hLn hwn)
        (affine_lip hLd hLn hlip lo w hlo hw hwn)
        (fun x y h => hfc _ _ (affineMap_congr lo w hlo hw h))) zero :=
    riemannIntegral_pts_zero (Qmul_den_pos hLd hw) (Int.mul_nonneg hLn hwn)
      (affine_lip hLd hLn hlip lo w hlo hw hwn)
      (fun x y h => hfc _ _ (affineMap_congr lo w hlo hw h))
      (fun N i hi => hz N i hi)
  show Req (Rmul (ofQ w hw) (riemannIntegral (f := fun x => f (affineMap lo w hlo hw x)) (L := mul L w)
        (Qmul_den_pos hLd hw) (Int.mul_nonneg hLn hwn)
        (affine_lip hLd hLn hlip lo w hlo hw hwn)
        (fun x y h => hfc _ _ (affineMap_congr lo w hlo hw h)))) zero
  exact Req_trans (Rmul_congr (Req_refl (ofQ w hw)) hinner) (Rmul_zero (ofQ w hw))

/-- `0·x ≈ 0` (deliverable A). -/
private theorem Rzero_mul_A (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

/-- **The Haar integral vanishes when the test vanishes on the window** (deliverable A). -/
theorem haarIntegral_window_vanish (φ : L2Test) (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hvan : ∀ (N i : Nat), i < N + 1 →
      Req (φ.f (affineMap lo w hlo hw (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))) zero) :
    Req (haarIntegral φ a han had lo w hlo hw hwn) zero := by
  refine riemannIntegralI_pts_zero (l2L_den φ (recipTest a han had))
    (l2L_num φ (recipTest a han had)) (l2lip φ (recipTest a han had))
    (l2fc φ (recipTest a han had)) lo w hlo hw hwn ?_
  intro N i hi
  exact Req_trans (Rmul_congr (hvan N i hi) (Req_refl _)) (Rzero_mul_A _)

/-- **Numerator positivity from an order bound** (deliverable A). -/
theorem qnum_pos_of_le {a b : Q} (han : 0 < a.num) (hbd : 0 < b.den)
    (h : Qle a b) : 0 < b.num := by
  simp only [Qle] at h
  have hbd' : (0 : Int) < (b.den : Int) := by exact_mod_cast hbd
  have h1 : (0 : Int) < a.num * (b.den : Int) := Int.mul_pos han hbd'
  have h2 : (0 : Int) < b.num * (a.den : Int) := by omega
  have h0 : 0 * (a.den : Int) < b.num * (a.den : Int) := by rw [Int.zero_mul]; exact h2
  exact Int.lt_of_mul_lt_mul_right h0 (Int.ofNat_nonneg _)

/-- **The reciprocal scaling bound** `qp ≤ n·a ⟹ 1/a ≤ n·(1/qp)` (deliverable A). -/
theorem qinv_scale_le {a qp : Q} (han : 0 < a.num) (hqn : 0 < qp.num) (n : Nat)
    (h : Qle qp (mul (⟨(n : Int), 1⟩ : Q) a)) :
    Qle (Qinv a) (mul (⟨(n : Int), 1⟩ : Q) (Qinv qp)) := by
  have hane : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg (Int.le_of_lt han)
  have hpne : (qp.num.toNat : Int) = qp.num := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  simp only [Qle, Qinv, mul] at h ⊢
  push_cast [hane, hpne] at h ⊢
  have e1 : ((a.den : Int)) * (1 * qp.num) = qp.num * (1 * (a.den : Int)) := by ring_uor
  have e2 : ((n : Int)) * (qp.den : Int) * a.num = (n : Int) * a.num * (qp.den : Int) := by ring_uor
  rw [e1, e2]
  exact h

-- ===========================================================================
-- New rational engines and the band lower bound.
-- ===========================================================================

/-- **The reciprocal cross-multiplication engine for the LOW side**: `1 ≤ n·b·qp ⟹ (1/n)·(1/qp) ≤ b`.
    The low-side mirror of `qinv_scale_le`: `g` vanishes BELOW the floor `b`, and on the window the
    reflected/dilated reciprocal-scale argument `1/(n·qp)` sits below `b`. -/
theorem qlow_engine (b : Q) (n : Nat) {qp : Q} (hqn : 0 < qp.num)
    (h : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) qp)) :
    Qle (mul (⟨1, n⟩ : Q) (Qinv qp)) b := by
  have hpne : (qp.num.toNat : Int) = qp.num := Int.toNat_of_nonneg (Int.le_of_lt hqn)
  simp only [Qle, Qinv, mul] at h ⊢
  push_cast [hpne] at h ⊢
  have eL : 1 * (qp.den : Int) * b.den = 1 * (1 * (b.den : Int) * qp.den) := by ring_uor
  have eR : b.num * ((n : Int) * qp.num) = (n : Int) * b.num * qp.num * 1 := by ring_uor
  rw [eL, eR]
  exact h

/-- **The band clamp preserves a rational lower bound at a rational point**: for `T ≤ q0` and
    `T ≤ S`, the `[0,S]`-band of `ofQ q0` stays `≥ ofQ T` (the clamp floor `0 ≤ T ≤ q0` never cuts,
    and the ceiling `S ≥ T` never cuts below `T`). This is what carries the high-side threshold
    through the totalizing clamp of `mulConvRTest` for scales `q0 = n` that may exceed `S`. -/
theorem qBandQ_ge_ofQ (T S q0 : Q) (hTd : 0 < T.den) (hSd : 0 < S.den) (hq0d : 0 < q0.den)
    (hTq0 : Qle T q0) (hTS : Qle T S) :
    Rle (ofQ T hTd) (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q0 hq0d)) := by
  intro m
  show Qle T (add (Qmin (Qmax q0 (⟨0, 1⟩ : Q)) S) (⟨2, m + 1⟩ : Q))
  have hqmax : Qle T (Qmax q0 (⟨0, 1⟩ : Q)) := Qle_trans hq0d hTq0 (Qmax_ge_left q0 (⟨0, 1⟩ : Q))
  have hmin : Qle T (Qmin (Qmax q0 (⟨0, 1⟩ : Q)) S) := Qle_Qmin hqmax hTS
  exact Qle_trans (Qmin_den_pos (Qmax_den_pos hq0d (by decide)) hSd) hmin
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

-- ===========================================================================
-- The autocorrelation packaged as a point test, and its rational-point value.
-- ===========================================================================

/-- **The autocorrelation `g ⋆ g^τ` as a bounded-Lipschitz test in its point variable** — the
    convolution `mulConvRTest g (reflectTest a g) S`, ready to be bundled into a `WeilTest`. -/
def autocorrL2 (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : L2Test :=
  mulConvRTest g (reflectTest a han had g) S hSd hSn a han had lo w hlo hw hwn

/-- The rational-point value of `autocorrL2` unfolds to the Haar integral of the productTest
    integrand `reflectTest a (dilateTestR (clamp q0) g) · reflectTest a g`. -/
theorem autocorrL2_f_haar (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (q0 : Q) (hq0d : 0 < q0.den) :
    (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q0 hq0d)
    = haarIntegral (productTest
        (reflectTest a han had (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q0 hq0d)) S hSd hSn
          (clampS_absle S hSd hSn (ofQ q0 hq0d)) g))
        (reflectTest a han had g)) a han had lo w hlo hw hwn := rfl

/-- **The autocorr point-test vanishes at a rational scale `q0` once its first factor vanishes at
    every window sample point** — the mulConvR window-vanishing hook. -/
theorem mulConvR_ofQ_vanish (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (q0 : Q) (hq0d : 0 < q0.den)
    (hfac : ∀ (N i : Nat), i < N + 1 →
      Req ((reflectTest a han had (dilateTestR
              (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ q0 hq0d)) S hSd hSn
              (clampS_absle S hSd hSn (ofQ q0 hq0d)) g)).f
            (affineMap lo w hlo hw (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))) zero) :
    Req ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q0 hq0d)) zero := by
  rw [autocorrL2_f_haar]
  refine haarIntegral_window_vanish _ a han had lo w hlo hw hwn ?_
  intro N i hi
  exact Req_trans (Rmul_congr (hfac N i hi) (Req_refl _)) (Rzero_mul_A _)

-- ===========================================================================
-- The two derived support-vanishing lemmas (high = integer scales, low = reciprocal scales).
-- ===========================================================================

/-- **High-side support vanishing**: the autocorr point-test vanishes at every integer scale `n > X`,
    DERIVED from `g` vanishing above the ceiling `1/a` (`hgh`), with the band-ratio cutoff
    `lo+w ≤ (X+1)·a` (`hband_hi`) and `X+1 ≤ S` (`hTS`). At each window sample `qp`, the first factor
    is `g(clamp(n)·(1/qp))`, and `clamp(n) ≥ X+1` (via `qBandQ_ge_ofQ`) gives `clamp(n)/qp ≥ 1/a`. -/
theorem autocorrL2_high_vanish (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (halo : Qle a lo)
    (hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S)
    (hband_hi : Qle (add lo w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (n : Nat) (hn : X < n) :
    Req ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f
          (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) zero := by
  refine mulConvR_ofQ_vanish g S hSd hSn a han had lo w hlo hw hwn
    (⟨(n : Int), 1⟩ : Q) Nat.one_pos ?_
  intro N i hi
  let qi : Q := (⟨(i : Int), N + 1⟩ : Q)
  let qp : Q := add lo (mul w qi)
  have hqpd : 0 < qp.den := add_den_pos hlo (Qmul_den_pos hw (Nat.succ_pos N))
  have hmulnn : (0 : Int) ≤ (mul w qi).num := by
    show (0 : Int) ≤ w.num * (i : Int)
    exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hlo_qp : Qle lo qp := Qle_self_add hmulnn
  have haqp : Qle a qp := Qle_trans hlo halo hlo_qp
  have hqpn : 0 < qp.num := qnum_pos_of_le han hqpd haqp
  have hqi_le : Qle qi (⟨1, 1⟩ : Q) := by
    show Qle (⟨(i : Int), N + 1⟩ : Q) (⟨1, 1⟩ : Q)
    simp only [Qle]; push_cast; omega
  have hmul_le : Qle (mul w qi) w := by
    have h1 : Qle (mul w qi) (mul w (⟨1, 1⟩ : Q)) := Qmul_le_mul_left hwn hqi_le
    have h2 : Qle (mul w (⟨1, 1⟩ : Q)) w :=
      Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor)
    exact Qle_trans (Qmul_den_pos hw (by decide)) h1 h2
  have hqp_lw : Qle qp (add lo w) := Qadd_le_add (Qle_refl lo) hmul_le
  have step1 : Req (affineMap lo w hlo hw (ofQ qi (Nat.succ_pos N))) (ofQ qp hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ lo hlo)) (Rmul_ofQ_ofQ hw (Nat.succ_pos N)))
      (Radd_ofQ_ofQ hlo (Qmul_den_pos hw (Nat.succ_pos N)))
  -- threshold: qp ≤ (X+1)·a, hence 1/a ≤ (X+1)·(1/qp)
  have hqp_na : Qle qp (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a) :=
    Qle_trans (add_den_pos hlo hw) hqp_lw hband_hi
  have hscale : Qle (Qinv a) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) (Qinv qp)) :=
    qinv_scale_le han hqpn (X + 1) hqp_na
  have hTn_le : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hlb : Rle (ofQ (⟨((X + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
                 (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) :=
    qBandQ_ge_ofQ (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S (⟨(n : Int), 1⟩ : Q)
      Nat.one_pos hSd Nat.one_pos hTn_le hTS
  have hval : Rle (ofQ (Qinv a) (Qinv_den_pos han))
      (Rmul (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
            (ofQ (Qinv qp) (Qinv_den_pos hqpn))) :=
    Rle_trans
      (Rle_ofQ_ofQ (Qinv_den_pos han) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hqpn)) hscale)
      (Rle_trans
        (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (Qinv_den_pos hqpn))))
        (Rmul_le_Rmul_right (Rnonneg_ofQ (Qinv_den_pos hqpn) (Int.le_of_lt (Qinv_num_pos hqpd))) hlb))
  exact Req_trans
    ((reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) g)).hfc _ _ step1)
    (Req_trans
      (reflectTest_ofQ a qp han had hqpd hqpn haqp
        (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) S hSd hSn
          (clampS_absle S hSd hSn (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) g))
      (hgh _ hval))

/-- **Low-side support vanishing**: the autocorr point-test vanishes at every reciprocal scale
    `1/n` for `n > X`, DERIVED from `g` vanishing below a floor `b` (`hgl`), with the reciprocal
    band-ratio `1 ≤ (X+1)·b·lo` (`hband_lo`) and `1 ≤ S` (`hS1`). At each window sample `qp`, the
    first factor is `g((1/n)·(1/qp)) = g(1/(n·qp))`, and `1/(n·qp) ≤ b` (via `qlow_engine`, using
    `qp ≥ lo` and `n ≥ X+1`). The clamp is inert here since `1/n ≤ 1 ≤ S`. -/
theorem autocorrL2_low_vanish (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (halo : Qle a lo)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 ≤ b.num)
    (hS1 : Qle (⟨1, 1⟩ : Q) S)
    (hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo))
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (n : Nat) (hn : X < n) (hnpos : 0 < n) :
    Req ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ (⟨1, n⟩ : Q) hnpos)) zero := by
  refine mulConvR_ofQ_vanish g S hSd hSn a han had lo w hlo hw hwn
    (⟨1, n⟩ : Q) hnpos ?_
  intro N i hi
  let qi : Q := (⟨(i : Int), N + 1⟩ : Q)
  let qp : Q := add lo (mul w qi)
  have hqpd : 0 < qp.den := add_den_pos hlo (Qmul_den_pos hw (Nat.succ_pos N))
  have hmulnn : (0 : Int) ≤ (mul w qi).num := by
    show (0 : Int) ≤ w.num * (i : Int)
    exact Int.mul_nonneg hwn (Int.ofNat_nonneg i)
  have hlo_qp : Qle lo qp := Qle_self_add hmulnn
  have haqp : Qle a qp := Qle_trans hlo halo hlo_qp
  have hqpn : 0 < qp.num := qnum_pos_of_le han hqpd haqp
  have step1 : Req (affineMap lo w hlo hw (ofQ qi (Nat.succ_pos N))) (ofQ qp hqpd) :=
    Req_trans (Radd_congr (Req_refl (ofQ lo hlo)) (Rmul_ofQ_ofQ hw (Nat.succ_pos N)))
      (Radd_ofQ_ofQ hlo (Qmul_den_pos hw (Nat.succ_pos N)))
  -- the clamp is inert: 0 ≤ 1/n ≤ 1 ≤ S
  have hn1 : Qle (⟨1, n⟩ : Q) (⟨1, 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have hax : Rle (ofQ (⟨0, 1⟩ : Q) (by decide)) (ofQ (⟨1, n⟩ : Q) hnpos) :=
    Rle_ofQ_ofQ (by decide) hnpos (by simp only [Qle]; push_cast; omega)
  have hxb : Rle (ofQ (⟨1, n⟩ : Q) hnpos) (ofQ S hSd) :=
    Rle_ofQ_ofQ hnpos hSd (Qle_trans (by decide) hn1 hS1)
  have hXeq : Req (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨1, n⟩ : Q) hnpos))
                  (ofQ (⟨1, n⟩ : Q) hnpos) := qBandQ_eq_of_band hax hxb
  -- the reciprocal-scale threshold: 1/(n·qp) ≤ b
  have hlonum : 0 < lo.num := qnum_pos_of_le han hlo halo
  have hTn_le : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) (⟨(n : Int), 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  have h1 : Qle (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo)
                (mul (mul (⟨(n : Int), 1⟩ : Q) b) lo) :=
    Qmul_le_mul_right (Int.le_of_lt hlonum) (Qmul_le_mul_right hbn hTn_le)
  have hmnb : (0 : Int) ≤ (n : Int) * b.num := Int.mul_nonneg (Int.ofNat_nonneg n) hbn
  have h2 : Qle (mul (mul (⟨(n : Int), 1⟩ : Q) b) lo)
                (mul (mul (⟨(n : Int), 1⟩ : Q) b) qp) :=
    Qmul_le_mul_left hmnb hlo_qp
  have hmid1 : 0 < (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo).den :=
    Qmul_den_pos (Qmul_den_pos Nat.one_pos hbd) hlo
  have hmid2 : 0 < (mul (mul (⟨(n : Int), 1⟩ : Q) b) lo).den :=
    Qmul_den_pos (Qmul_den_pos Nat.one_pos hbd) hlo
  have hbig : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨(n : Int), 1⟩ : Q) b) qp) :=
    Qle_trans hmid2 (Qle_trans hmid1 hband_lo h1) h2
  have hlow_q : Qle (mul (⟨1, n⟩ : Q) (Qinv qp)) b := qlow_engine b n hqpn hbig
  have hle : Rle (Rmul (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨1, n⟩ : Q) hnpos))
                       (ofQ (Qinv qp) (Qinv_den_pos hqpn)))
                 (ofQ b hbd) :=
    Rle_trans
      (Rle_of_Req (Req_trans
        (Rmul_congr hXeq (Req_refl (ofQ (Qinv qp) (Qinv_den_pos hqpn))))
        (Rmul_ofQ_ofQ hnpos (Qinv_den_pos hqpn))))
      (Rle_ofQ_ofQ (Qmul_den_pos hnpos (Qinv_den_pos hqpn)) hbd hlow_q)
  exact Req_trans
    ((reflectTest a han had (dilateTestR
        (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨1, n⟩ : Q) hnpos)) S hSd hSn
        (clampS_absle S hSd hSn (ofQ (⟨1, n⟩ : Q) hnpos)) g)).hfc _ _ step1)
    (Req_trans
      (reflectTest_ofQ a qp han had hqpd hqpn haqp
        (dilateTestR
          (qBandQ (⟨0, 1⟩ : Q) S (by decide) hSd (ofQ (⟨1, n⟩ : Q) hnpos)) S hSd hSn
          (clampS_absle S hSd hSn (ofQ (⟨1, n⟩ : Q) hnpos)) g))
      (hgl _ hle))

-- ===========================================================================
-- THE DELIVERABLE: the WeilTest bundle, its readback, and the fold consumer.
-- ===========================================================================

/-- **The autocorrelation cone as a point-value `WeilTest`** — `weilTestOfL2 (autocorrL2 g)` with the
    support cutoff `X` and the `supp_high`/`supp_low` proofs DERIVED from the two compact-support
    facts on `g` (`hgh`: vanishing above `1/a`, `hgl`: vanishing below `b`) via `autocorrL2_high_vanish`
    / `autocorrL2_low_vanish`. This is the genuine point-value test the finite-place Weil functional
    consumes, built on the constructed autocorrelation. -/
def autocorrWeilTest (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (hX : 1 ≤ X) (halo : Qle a lo)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 ≤ b.num)
    (hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S) (hS1 : Qle (⟨1, 1⟩ : Q) S)
    (hband_hi : Qle (add lo w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a))
    (hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero) : WeilTest :=
  weilTestOfL2 (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn) X hX
    (fun n hn => by
      show Req ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f
                  (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) zero
      exact autocorrL2_high_vanish g S hSd hSn a han had lo w hlo hw hwn X halo hTS hband_hi hgh n hn)
    (fun n hn => by
      have hnpos : 0 < n := by omega
      show Req (dite (0 < (⟨1, n⟩ : Q).den)
                 (fun h => (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ (⟨1, n⟩ : Q) h))
                 (fun _ => zero)) zero
      rw [dif_pos hnpos]
      exact autocorrL2_low_vanish g S hSd hSn a han had lo w hlo hw hwn X halo b hbd hbn hS1
        hband_lo hgl n hn hnpos)

/-- **Point-value readback** (no private `l2pt` exposed to consumers): the bundled test's rational
    evaluation is the autocorr point-test value at `ofQ q`. -/
theorem autocorrWeilTest_apply (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (hX : 1 ≤ X) (halo : Qle a lo)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 ≤ b.num)
    (hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S) (hS1 : Qle (⟨1, 1⟩ : Q) S)
    (hband_hi : Qle (add lo w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a))
    (hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (q : Q) (hq : 0 < q.den) :
    Req ((autocorrWeilTest g S hSd hSn a han had lo w hlo hw hwn X hX halo b hbd hbn
            hTS hS1 hband_hi hband_lo hgh hgl).f q)
        ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q hq)) := by
  show Req (dite (0 < q.den)
             (fun h => (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q h))
             (fun _ => zero))
           ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ q hq))
  rw [dif_pos hq]
  exact Req_refl _

/-- **THE FIRST CONSUMER OF `weilPrimeShiftFold`**: the finite fold of genuine multiplicative
    dilation/shift local terms of the autocorrelation point-test equals `weilPrimePart` of the bundled
    autocorrelation `WeilTest` — a direct instance of the committed `weilPrimeShiftFold` at
    `φ = autocorrL2 g`. The finite-place Weil shift-fold now runs on the constructed cone object. -/
theorem weilPrimeShiftFold_autocorr (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (hX : 1 ≤ X) (halo : Qle a lo)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 ≤ b.num)
    (hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S) (hS1 : Qle (⟨1, 1⟩ : Q) S)
    (hband_hi : Qle (add lo w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a))
    (hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) lo))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero) :
    Req (RsumN (weilPrimeShiftTerm (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn)) X)
        (weilPrimePart (autocorrWeilTest g S hSd hSn a han had lo w hlo hw hwn X hX halo b hbd hbn
            hTS hS1 hband_hi hband_lo hgh hgl)) :=
  weilPrimeShiftFold (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn) X hX
    (fun n hn => by
      show Req ((autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f
                  (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) zero
      exact autocorrL2_high_vanish g S hSd hSn a han had lo w hlo hw hwn X halo hTS hband_hi hgh n hn)
    (fun n hn => by
      have hnpos : 0 < n := by omega
      show Req (dite (0 < (⟨1, n⟩ : Q).den)
                 (fun h => (autocorrL2 g S hSd hSn a han had lo w hlo hw hwn).f (ofQ (⟨1, n⟩ : Q) h))
                 (fun _ => zero)) zero
      rw [dif_pos hnpos]
      exact autocorrL2_low_vanish g S hSd hSn a han had lo w hlo hw hwn X halo b hbd hbn hS1
        hband_lo hgl n hn hnpos)

end UOR.Bridge.F1Square.Square
