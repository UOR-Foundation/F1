/-
F1 square — the Sonine local-defect telescope consuming the autocorrelation (`WeilPrimeShiftSonine.lean`).
Sonine / local-defect TELESCOPE.

LEG 3 (included verbatim below, unchanged) delivered the reciprocally-symmetric autocorrelation
point value `acPt`, its proven reflection symmetry `autocorr_recip_all`, the CC symmetric
normalization `ac_CC_normalization`, and the Λ-weighted normalized fold `acNormFold`.

LEG 4 consumes that autocorrelation place-value data IMMEDIATELY inside the coupled Weil kernel's
prime-Gram Sonine structure and proves the LOCAL-DEFECT TELESCOPE: extending the prime side by one
prime power `M → M+1` adds exactly one MANIFEST NONNEG SQUARE local defect
`|D_M|² = Λ(M+1)·(Σ_i c_i·placeVal(g_i, M))² ≥ 0`.

(4a) `localDefect` — the per-place defect `w(M)·(Σ_{i<N} c_i·v(M,i))²`.
(4b) `weilQuad_primeGram_telescope` — `weilQuad(primeGram w v (M+1)) c N =
       weilQuad(primeGram w v M) c N + localDefect w v c N M`  (via `weilQuad_primeGram_split`).
(4c) `localDefect_nonneg` — the increment is `Rnonneg` when `w(M) ≥ 0`
       (`Rnonneg_Rmul` × `Rnonneg_Rmul_self`).
(4d) `weilPrimeGram_telescope` / `weilPrimeGram_localDefect_nonneg` — on the GENUINE von Mangoldt
       weight the increment is UNCONDITIONALLY `Rnonneg` (`vonMangoldt_nonneg`); each prime power adds a
       genuine `≥0` square, no RH input.
(4e) `weilPrimeGram_vFrom_telescope` / `_nonneg` — the same on the coupled kernel's genuine
       place-value interface `v = vFrom g`, so the defect is built from REAL test place-values.
(4f) `placeVal_autocorrWeilTest_eq_acPt` — THE CONSUMPTION: the interface datum
       `placeVal (autocorrWeilTest g …) m` equals LEG 3's reciprocally-symmetric autocorrelation
       point values `acPt`, so the Sonine local defect at each place is assembled out of leg-3's
       normalized autocorrelation values.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftBridge
import F1Square.Square.WeilPrimeShiftRecipAutocorr
import F1Square.Square.WeilPrimeShiftNorm
import F1Square.Square.CoupledWeilKernel
import F1Square.Square.CoupledWeilPlaceValue

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

-- ===========================================================================
-- ===========================================================================
-- LEG 4 — the Sonine / local-defect telescope consuming the autocorrelation prime side.
-- ===========================================================================
-- ===========================================================================

-- ---------------------------------------------------------------------------
-- (4a) The per-place local defect square.
-- ---------------------------------------------------------------------------

/-- **The local per-place defect** `|D_M|² = w(M)·(Σ_{i<N} c_i·v(M,i))²` — the manifest weighted
    square contributed by the prime power at place `M`.  This is exactly the `M`-th summand of the
    prime-Gram square-split (`weilQuad_primeGram_split`). -/
def localDefect (w : Nat → Real) (v : Nat → Nat → Real) (c : Nat → Real) (N M : Nat) : Real :=
  Rmul (w M) (Rmul (RsumN (fun i => Rmul (c i) (v M i)) N)
                   (RsumN (fun i => Rmul (c i) (v M i)) N))

-- ---------------------------------------------------------------------------
-- (4b) The telescope: one extra prime power adds exactly one local defect.
-- ---------------------------------------------------------------------------

/-- **★ THE SONINE LOCAL-DEFECT TELESCOPE**: extending the prime side by one prime power adds exactly
    one square local defect —
        `weilQuad(primeGram w v (M+1)) c N = weilQuad(primeGram w v M) c N + localDefect w v c N M`.
    Proof: the prime-Gram quadratic form is a weighted sum of squares over prime powers
    (`weilQuad_primeGram_split`), and `Σ_{m<M+1} = Σ_{m<M} + [term at M]` by the fold's successor
    (definitional `RsumN`). -/
theorem weilQuad_primeGram_telescope (w : Nat → Real) (v : Nat → Nat → Real)
    (c : Nat → Real) (N M : Nat) :
    Req (weilQuad (primeGram w v (M + 1)) c N)
        (Radd (weilQuad (primeGram w v M) c N) (localDefect w v c N M)) :=
  Req_trans (weilQuad_primeGram_split w v c N (M + 1))
    (Radd_congr (Req_symm (weilQuad_primeGram_split w v c N M)) (Req_refl _))

-- ---------------------------------------------------------------------------
-- (4c) The increment is a manifest nonneg square (generic weight).
-- ---------------------------------------------------------------------------

/-- **The local defect is `Rnonneg` when the weight is `≥ 0`** — a nonnegative weight times a manifest
    square (`Rnonneg_Rmul` × `Rnonneg_Rmul_self`), NO sqrt. -/
theorem localDefect_nonneg (w : Nat → Real) (v : Nat → Nat → Real) (c : Nat → Real) (N M : Nat)
    (hw : Rnonneg (w M)) : Rnonneg (localDefect w v c N M) :=
  Rnonneg_Rmul hw (Rnonneg_Rmul_self (RsumN (fun i => Rmul (c i) (v M i)) N))

-- ---------------------------------------------------------------------------
-- (4d) The genuine von Mangoldt weight: the increment is UNCONDITIONALLY nonneg.
-- ---------------------------------------------------------------------------

/-- **The telescope on the genuine von Mangoldt prime Gram** — `weilPrimeGram v M =
    primeGram (Λ∘succ) v M` (definitional), so the same one-place-adds-one-square telescope holds. -/
theorem weilPrimeGram_telescope (v : Nat → Nat → Real) (c : Nat → Real) (N M : Nat) :
    Req (weilQuad (weilPrimeGram v (M + 1)) c N)
        (Radd (weilQuad (weilPrimeGram v M) c N)
              (localDefect (fun m => vonMangoldt (m + 1)) v c N M)) :=
  weilQuad_primeGram_telescope (fun m => vonMangoldt (m + 1)) v c N M

/-- **The genuine local defect is UNCONDITIONALLY `Rnonneg`** — the von Mangoldt weight is `≥ 0`
    (`vonMangoldt_nonneg`), so every prime power adds a genuine nonnegative square, NO RH input. -/
theorem weilPrimeGram_localDefect_nonneg (v : Nat → Nat → Real) (c : Nat → Real) (N M : Nat) :
    Rnonneg (localDefect (fun m => vonMangoldt (m + 1)) v c N M) :=
  localDefect_nonneg (fun m => vonMangoldt (m + 1)) v c N M (vonMangoldt_nonneg (M + 1))

-- ---------------------------------------------------------------------------
-- (4e) On the coupled kernel's genuine place-value interface `v = vFrom g`.
-- ---------------------------------------------------------------------------

/-- **The telescope on real test place-values** `v = vFrom g` (`vFrom g m i = placeVal (g i) m`):
    each prime power adds the genuine square `Λ(M+1)·(Σ_i c_i·placeVal(g_i, M))²`. -/
theorem weilPrimeGram_vFrom_telescope (g : Nat → WeilTest) (c : Nat → Real) (N M : Nat) :
    Req (weilQuad (weilPrimeGram (vFrom g) (M + 1)) c N)
        (Radd (weilQuad (weilPrimeGram (vFrom g) M) c N)
              (localDefect (fun m => vonMangoldt (m + 1)) (vFrom g) c N M)) :=
  weilPrimeGram_telescope (vFrom g) c N M

/-- **The genuine place-value local defect is UNCONDITIONALLY `Rnonneg`** — `Λ(M+1) ≥ 0` times the
    manifest square of the real place-value combination. -/
theorem weilPrimeGram_vFrom_localDefect_nonneg (g : Nat → WeilTest) (c : Nat → Real) (N M : Nat) :
    Rnonneg (localDefect (fun m => vonMangoldt (m + 1)) (vFrom g) c N M) :=
  weilPrimeGram_localDefect_nonneg (vFrom g) c N M

-- ---------------------------------------------------------------------------
-- (4f) THE CONSUMPTION: the interface datum is LEG 3's autocorrelation point values.
-- ---------------------------------------------------------------------------

/-- **★ THE CONSUMPTION OF LEG 3**: the coupled kernel's per-place interface datum
    `placeVal (autocorrWeilTest g …) m` — the `v` feeding the Sonine local defect at place `m` —
    is exactly LEG 3's reciprocally-symmetric autocorrelation point value
    `h(m+1) + (m+1)⁻¹·h(1/(m+1))` built from `acPt` (window `lo = a`).  So each Sonine local defect
    `localDefect (Λ∘succ) (vFrom (autocorr family)) c N M` is assembled out of leg-3's normalized
    autocorrelation values, whose reflection symmetry `autocorr_recip_all` is PROVEN, not assumed. -/
theorem placeVal_autocorrWeilTest_eq_acPt (g : L2Test) (S : Q) (hSd : 0 < S.den) (hSn : 0 ≤ S.num)
    (a : Q) (han : 0 < a.num) (had : 0 < a.den)
    (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (X : Nat) (hX : 1 ≤ X)
    (b : Q) (hbd : 0 < b.den) (hbn : 0 ≤ b.num)
    (hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S) (hS1 : Qle (⟨1, 1⟩ : Q) S)
    (hband_hi : Qle (add a w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a))
    (hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) a))
    (hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero)
    (hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero) (m : Nat) :
    Req (placeVal (autocorrWeilTest g S hSd hSn a han had a w had hw hwn X hX (Qle_refl a) b hbd hbn
            hTS hS1 hband_hi hband_lo hgh hgl) m)
        (Radd (acPt g S hSd hSn a han had w hw hwn (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
          (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
            (acPt g S hSd hSn a han had w hw hwn (⟨1, m + 1⟩ : Q)))) := by
  show Req (Radd ((autocorrWeilTest g S hSd hSn a han had a w had hw hwn X hX (Qle_refl a) b hbd hbn
            hTS hS1 hband_hi hband_lo hgh hgl).f (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
        (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
          ((autocorrWeilTest g S hSd hSn a han had a w had hw hwn X hX (Qle_refl a) b hbd hbn
            hTS hS1 hband_hi hband_lo hgh hgl).f (⟨1, m + 1⟩ : Q))))
      (Radd (acPt g S hSd hSn a han had w hw hwn (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
        (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
          (acPt g S hSd hSn a han had w hw hwn (⟨1, m + 1⟩ : Q))))
  refine Radd_congr ?_ (Rmul_congr (Req_refl _) ?_)
  · exact Req_trans
      (autocorrWeilTest_apply g S hSd hSn a han had a w had hw hwn X hX (Qle_refl a) b hbd hbn
        hTS hS1 hband_hi hband_lo hgh hgl (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
      (Req_symm (acPt_pos g S hSd hSn a han had w hw hwn (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos))
  · exact Req_trans
      (autocorrWeilTest_apply g S hSd hSn a han had a w had hw hwn X hX (Qle_refl a) b hbd hbn
        hTS hS1 hband_hi hband_lo hgh hgl (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
      (Req_symm (acPt_pos g S hSd hSn a han had w hw hwn (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))

end UOR.Bridge.F1Square.Square
