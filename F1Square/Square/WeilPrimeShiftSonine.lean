/-
F1 square — **the CC √-normalization on the real autocorrelation** (`WeilPrimeShiftSonine.lean`).

Analytic-normalization content (self-contained; imports no `CoupledWeil*`): the reciprocally-symmetric
autocorrelation point value `acPt`, its PROVEN reflection symmetry `autocorr_recip_all`
(`h(n) ≈ h(1/n)` for all `n`, by cases — the reciprocal CoV regime plus the support-vanishing regime,
no assumed symmetry), the CC symmetric normalization `ac_CC_normalization` (`F_normalization`
instantiated on the actual autocorrelation), the per-place symmetric value `acPlaceSym`
(`= F(n)+n⁻¹F(1/n)`, `F(q)=q^{-1/2}·acPt`) with its `acPlaceSym_collapse` (`= 2·n^{-1/2}·h(n)`), and the
Λ-weighted normalized fold `acNormFold` (`acNormFold_collapse`).

The genuine downstream CONSUMER of `acNormFold` — the normalized autocorrelation as a real `WeilTest`
whose `weilPrimePart` equals `acNormFold`, and the arch-MINUS-prime `weilValue` at that slot — lives in
`WeilPrimeShiftCrux.lean` (the point-value prime side, NOT the coupled-kernel prime-Gram, NOT `vFrom`).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftBridge
import F1Square.Square.WeilPrimeShiftRecipAutocorr
import F1Square.Square.WeilPrimeShiftNorm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The autocorrelation as a TOTAL rational point function `acPt` (window lo = a).   [LEG 3]
-- ===========================================================================

/-- **The autocorrelation point value** `h(q) = (autocorrL2 g S …).f (ofQ q)`, totalized with the
    junk value `0` at the impossible `q.den = 0`.  The window is `[a, a+w]` (lo = a). -/
def acPt (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (q : Q) : Real :=
  if hh : 0 < q.den then
    (autocorrL2 g S hSd hSn a han had a w had hw hwn).f (ofQ q hh)
  else zero

/-- Readback: at a positive-denominator rational, `acPt` is the landed point-test value. -/
theorem acPt_pos (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (q : Q) (hq : 0 < q.den) :
    Req (acPt g S hSd hSn a han had w hw hwn q)
        ((autocorrL2 g S hSd hSn a han had a w had hw hwn).f (ofQ q hq)) := by
  show Req (if hh : 0 < q.den then
      (autocorrL2 g S hSd hSn a han had a w had hw hwn).f (ofQ q hh) else zero)
      ((autocorrL2 g S hSd hSn a han had a w had hw hwn).f (ofQ q hq))
  rw [dif_pos hq]
  exact Req_refl _

-- ===========================================================================
-- (a)  The autocorrelation reciprocal self-duality for ALL n ≥ 1.   [LEG 3]
-- ===========================================================================

/-- **`h(n) ≈ h(1/n)` for ALL `n ≥ 1`** (the reflection symmetry `hsym` fed to `F_normalization`).
    `g` compactly supported inside `[b, 1/a]` (`hgh`: vanishing `≥ 1/a`; `hgl`: vanishing `≤ b`;
    `hfit`: `1/b ≤ a+w`); the scale sits in band (`hnS`: `n ≤ S`).  Case split on `n·a < a+w`:
    in regime `autocorr_recip` + `autocorr_eq_autocorrL2`; out of regime both point values vanish
    by `autocorrL2_high_vanish` / `autocorrL2_low_vanish` (the band cutoffs are derived from
    `a+w ≤ n·a` and `hfit`). -/
theorem autocorr_recip_all (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hnS : Qle (⟨(n : Int), 1⟩ : Q) S) :
    Req (acPt g S hSd hSn a han had w hw hwn (⟨(n : Int), 1⟩ : Q))
        (acPt g S hSd hSn a han had w hw hwn (⟨1, n⟩ : Q)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Readbacks of the two point values.
  have eN := acPt_pos g S hSd hSn a han had w hw hwn (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos
  have eR := acPt_pos g S hSd hSn a han had w hw hwn (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)
  -- Convenient positive-denominator/positive-numerator witnesses.
  have hqnN : (0 : Int) < (⟨((m + 1 : Nat) : Int), 1⟩ : Q).num := Int.ofNat_pos.mpr hn0
  have h1pos : (0 : Int) < (⟨1, m + 1⟩ : Q).num := by show (0 : Int) < 1; decide
  rcases Qle_or_Qlt (add a w) (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) a) with hdeg | hcore
  · -- Degenerate: both point values vanish.
    -- hstep : 1/b ≤ (m+1)·a
    have hstep : Qle (Qinv b) (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) a) :=
      Qle_trans (add_den_pos had hw) hfit hdeg
    -- hband_lo : 1 ≤ ((m+1)·b)·a
    have hb : (b.num.toNat : Int) = b.num := Int.toNat_of_nonneg (Int.le_of_lt hbn)
    have h1' : Qeq (⟨1, 1⟩ : Q) (mul (Qinv b) b) := by
      simp only [Qeq, Qinv, mul]; push_cast [hb]; ring_uor
    have h3 : Qeq (mul (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) a) b)
                  (mul (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) b) a) := by
      simp only [Qeq, mul]; push_cast; ring_uor
    have hInvbd : 0 < (Qinv b).den := Qinv_den_pos hbn
    have d1 : 0 < (mul (Qinv b) b).den := Qmul_den_pos hInvbd hbd
    have d2 : 0 < (mul (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) a) b).den :=
      Qmul_den_pos (Qmul_den_pos Nat.one_pos had) hbd
    have hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((m + 1 : Nat) : Int), 1⟩ : Q) b) a) :=
      Qle_trans d1 (Qeq_le h1')
        (Qle_trans d2 (Qmul_le_mul_right (Int.le_of_lt hbn) hstep) (Qeq_le h3))
    -- vanish at n and at 1/n
    have vanN : Req ((autocorrL2 g S hSd hSn a han had a w had hw hwn).f
          (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)) zero :=
      autocorrL2_high_vanish g S hSd hSn a han had a w had hw hwn m (Qle_refl a) hnS hdeg hgh
        (m + 1) (Nat.lt_succ_self m)
    have vanR : Req ((autocorrL2 g S hSd hSn a han had a w had hw hwn).f
          (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))) zero := by
      have hS1 : Qle (⟨1, 1⟩ : Q) S :=
        Qle_trans Nat.one_pos (by simp only [Qle]; push_cast; omega) hnS
      exact autocorrL2_low_vanish g S hSd hSn a han had a w had hw hwn m (Qle_refl a) b hbd
        (Int.le_of_lt hbn) hS1 hband_lo hgl (m + 1) (Nat.lt_succ_self m) (Nat.succ_pos m)
    exact Req_trans (Req_trans eN vanN) (Req_symm (Req_trans eR vanR))
  · -- Non-degenerate: `autocorr_recip`, bridged both sides.
    have recip :=
      autocorr_recip g a han had w hw hwn b hbd hbn (m + 1) hn0 hgh hgl hfit hcore
    have hq0N : Qle (⟨0, 1⟩ : Q) (⟨((m + 1 : Nat) : Int), 1⟩ : Q) := by
      simp only [Qle]; push_cast; omega
    have hq0R : Qle (⟨0, 1⟩ : Q) (⟨1, m + 1⟩ : Q) := by
      simp only [Qle]; push_cast; omega
    have hqSR : Qle (⟨1, m + 1⟩ : Q) S := by
      have hr1 : Qle (⟨1, m + 1⟩ : Q) (⟨1, 1⟩ : Q) := by simp only [Qle]; push_cast; omega
      have hS1 : Qle (⟨1, 1⟩ : Q) S :=
        Qle_trans Nat.one_pos (by simp only [Qle]; push_cast; omega) hnS
      exact Qle_trans (by decide) hr1 hS1
    have bridgeN :=
      autocorr_eq_autocorrL2 g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) hqnN Nat.one_pos
        a han had a w had hw hwn S hSd hSn hq0N hnS
    have bridgeR :=
      autocorr_eq_autocorrL2 g (⟨1, m + 1⟩ : Q) h1pos (Nat.succ_pos m)
        a han had a w had hw hwn S hSd hSn hq0R hqSR
    -- Chain: acPt(n) ≈ AC.f(n) ≈ autocorr(n) ≈ autocorr(1/n) ≈ AC.f(1/n) ≈ acPt(1/n)
    exact Req_trans eN
      (Req_trans (Req_symm bridgeN)
        (Req_trans recip (Req_trans bridgeR (Req_symm eR))))

-- ===========================================================================
-- (b)  F_normalization on the ACTUAL autocorrelation.   [LEG 3]
-- ===========================================================================

/-- **`F(n) + n⁻¹·F(1/n) = 2·n^{-1/2}·h(n)` for the ACTUAL autocorrelation** — `F_normalization`
    instantiated with `h = acPt` and `hsym = autocorr_recip_all` (PROVEN, not assumed). -/
theorem ac_CC_normalization (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hnS : Qle (⟨(n : Int), 1⟩ : Q) S) :
    Req
      (Radd (Rmul (qInvSqrt n hn0) (acPt g S hSd hSn a han had w hw hwn (⟨(n : Int), 1⟩ : Q)))
        (Rmul (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn0))
          (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1)
            (acPt g S hSd hSn a han had w hw hwn (⟨1, n⟩ : Q)))))
      (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
        (Rmul (qInvSqrt n hn0) (acPt g S hSd hSn a han had w hw hwn (⟨(n : Int), 1⟩ : Q)))) :=
  F_normalization n hn0 han1 (acPt g S hSd hSn a han had w hw hwn)
    (autocorr_recip_all g S hSd hSn a han had w hw hwn b hbd hbn n hn0 hgh hgl hfit hnS)

-- ===========================================================================
-- (c)  The normalized autocorr place value, its collapse, and the Λ-weighted fold.   [LEG 3]
-- ===========================================================================

/-- **The normalized (symmetric) autocorr place value** `F(n) + n⁻¹·F(1/n)`, where
    `F(q) = q^{-1/2}·h(q)` and the weight at `1/n` is `√n = (1/n)^{-1/2}`. -/
def acPlaceSym (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (n : Nat) (hn0 : 0 < n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) : Real :=
  Radd (Rmul (qInvSqrt n hn0) (acPt g S hSd hSn a han had w hw hwn (⟨(n : Int), 1⟩ : Q)))
    (Rmul (Rinv (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit n hn0))
      (Rmul (RsqrtReal (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos) han1)
        (acPt g S hSd hSn a han had w hw hwn (⟨1, n⟩ : Q))))

/-- **The normalized place value collapses to `2·n^{-1/2}·h(n)`** — `ac_CC_normalization`. -/
theorem acPlaceSym_collapse (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num)
    (n : Nat) (hn0 : 0 < n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hnS : Qle (⟨(n : Int), 1⟩ : Q) S) :
    Req (acPlaceSym g S hSd hSn a han had w hw hwn n hn0 han1)
        (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
          (Rmul (qInvSqrt n hn0) (acPt g S hSd hSn a han had w hw hwn (⟨(n : Int), 1⟩ : Q)))) :=
  ac_CC_normalization g S hSd hSn a han had w hw hwn b hbd hbn n hn0 han1 hgh hgl hfit hnS

/-- The successor scale `m+1 ≥ 1` dominates `1`, packaged for the fold's per-index `han1`. -/
theorem oneLeSucc (m : Nat) : Rle one (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) := by
  have hle : Qle (⟨1, 1⟩ : Q) (⟨((m + 1 : Nat) : Int), 1⟩ : Q) := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast; omega
  exact Rle_ofQ_ofQ (by decide) Nat.one_pos hle

/-- **The Λ-weighted normalized autocorr fold** — the finite-place symmetric-normalization fold over
    places `1..X` of `Λ(m+1)·(F(m+1) + (m+1)⁻¹·F(1/(m+1)))`. -/
def acNormFold (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (X : Nat) : Real :=
  RsumN (fun m => Rmul (vonMangoldt (m + 1))
    (acPlaceSym g S hSd hSn a han had w hw hwn (m + 1) (Nat.succ_pos m) (oneLeSucc m))) X

/-- **The normalized fold collapses termwise to `Σ Λ(m+1)·2·(m+1)^{-1/2}·h(m+1)`** — each place is
    the symmetric collapse (`acPlaceSym_collapse`) under the Λ weight; the reflection symmetry is the
    PROVEN `autocorr_recip_all`, never assumed. -/
theorem acNormFold_collapse (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 < b.num) (X : Nat)
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero)
    (hfit : Qle (Qinv b) (add a w))
    (hnS : ∀ m : Nat, m < X → Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) S) :
    Req (acNormFold g S hSd hSn a han had w hw hwn X)
        (RsumN (fun m => Rmul (vonMangoldt (m + 1))
          (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
            (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m))
              (acPt g S hSd hSn a han had w hw hwn (⟨((m + 1 : Nat) : Int), 1⟩ : Q))))) X) :=
  RsumN_congr X (fun m hm =>
    Rmul_congr (Req_refl _)
      (acPlaceSym_collapse g S hSd hSn a han had w hw hwn b hbd hbn (m + 1) (Nat.succ_pos m)
        (oneLeSucc m) hgh hgl hfit (hnS m hm)))

end UOR.Bridge.F1Square.Square
