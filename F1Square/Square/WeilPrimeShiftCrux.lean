/-
F1 square — **the GENUINE connection: normalized autocorrelation ⟶ scalar coupled
arch-MINUS-prime Weil functional** (`WeilPrimeShiftCrux.lean`).

The prior work built `acNormFold` — the Λ-weighted, √-Burnol-normalized fold of the
autocorrelation place values — but it TERMINATED UNUSED: nothing consumed it into the
actual Weil pairing machinery.  This file closes that gap WITHOUT any of the rejected
shortcuts (no `vFrom`/`primeGram` Gram identification, no Mellin/transform factorization,
no re-assumed reciprocal symmetry — the reflection self-duality used is the PROVEN
`autocorr_recip_all`, threaded through `acPlaceSym`).

WHAT IS BUILT (point-value, non-Gram):
  1. `normAutocorrTest`  — a genuine `WeilTest` whose rational-point value is
     `q^{-1/2}·(autocorr point value acPt)`; the weight is `n^{-1/2}=qInvSqrt` at integer
     scales and `n^{1/2}=RsqrtReal` at reciprocal scales `1/n` (i.e. exactly `q^{-1/2}`),
     multiplying the bundled autocorrelation test `autocorrWeilTest`; support cutoff and
     vanishing INHERITED from that bundle.
  2. `weilPrimePart_normAutocorr` — THE RECOVERY: the finite-place Weil prime side of this
     test, `Σ_{m<X} Λ(m+1)·placeVal`, equals `acNormFold` — the normalized autocorrelation
     fold IS the genuine point-value Weil prime side.  Proved by identifying each
     `placeVal` with `acPlaceSym` (the un-collapsed `F(n)+n⁻¹F(1/n)` place value), the
     `n=1` term killed by `Λ(1)=0`.
  3. `normAutocorrSlot` / `weilValue_normAutocorr` — the assembled functional
     `W = poles − (acNormFold + weilArchConst + archTail)` with the correct MINUS sign
     (`poles`,`archTail` are honest interface Real inputs — the two integral components CC
     leaves unverified in print).
  4. `normAutocorr_nonzero` — under a nonzero-at-one-point hypothesis, the test is a proved
     nonzero supported test.
  5. `normAutocorr_weil_psd_iff_hodge` — the crux tie: PSD of the pairing family ⟺
     Hodge-index negativity (`weil_psd_iff_hodge`); `Rnonneg (weilValue …) = RH` is the
     open content, NEVER proved here.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/
import F1Square.Square.WeilPrimeShiftSonine
import F1Square.Square.Pairing

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The bundled context (packs the compactly-supported `g`, its window, the cutoff
-- `X`, the band data, and the two compact-support facts — so every downstream
-- object threads a single `C : NormCtx`).  The window low edge is `lo = a`.
-- ===========================================================================

/-- Everything the autocorrelation `WeilTest` construction needs, bundled. -/
structure NormCtx where
  g : L2Test
  S : Q
  hSd : 0 < S.den
  hSn : 0 ≤ S.num
  a : Q
  han : 0 < a.num
  had : 0 < a.den
  w : Q
  hw : 0 < w.den
  hwn : 0 ≤ w.num
  X : Nat
  hX : 1 ≤ X
  b : Q
  hbd : 0 < b.den
  hbn : 0 ≤ b.num
  hTS : Qle (⟨((X + 1 : Nat) : Int), 1⟩ : Q) S
  hS1 : Qle (⟨1, 1⟩ : Q) S
  hband_hi : Qle (add a w) (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) a)
  hband_lo : Qle (⟨1, 1⟩ : Q) (mul (mul (⟨((X + 1 : Nat) : Int), 1⟩ : Q) b) a)
  hgh : ∀ y, Rle (ofQ (Qinv a) (Qinv_den_pos han)) y → Req (g.f y) zero
  hgl : ∀ y, Rle y (ofQ b hbd) → Req (g.f y) zero

/-- The bundled autocorrelation `WeilTest` (`autocorrWeilTest` with window `lo = a`). -/
def acT (C : NormCtx) : WeilTest :=
  autocorrWeilTest C.g C.S C.hSd C.hSn C.a C.han C.had C.a C.w C.had C.hw C.hwn
    C.X C.hX (Qle_refl C.a) C.b C.hbd C.hbn C.hTS C.hS1 C.hband_hi C.hband_lo C.hgh C.hgl

/-- The autocorrelation point value `acPt`, threaded through `C` (window `lo = a`). -/
def acPtC (C : NormCtx) (q : Q) : Real :=
  acPt C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn q

/-- The Λ-weighted √-normalized autocorrelation fold, threaded through `C`. -/
def acNormFoldC (C : NormCtx) : Real :=
  acNormFold C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn C.X

/-- The un-collapsed symmetric place value `F(n)+n⁻¹F(1/n)`, threaded through `C`. -/
def acPlaceSymC (C : NormCtx) (n : Nat) (hn : 0 < n)
    (han1 : Rle one (ofQ (⟨(n : Int), 1⟩ : Q) Nat.one_pos)) : Real :=
  acPlaceSym C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn n hn han1

/-- The bundled test's rational point value is the autocorrelation point value `acPt`
    (window `lo = a`): readback of `autocorrWeilTest`, bridged to `acPt` by `acPt_pos`. -/
theorem acbase_eq_acPt (C : NormCtx) (q : Q) (hq : 0 < q.den) :
    Req ((acT C).f q) (acPtC C q) :=
  Req_trans
    (autocorrWeilTest_apply C.g C.S C.hSd C.hSn C.a C.han C.had C.a C.w C.had C.hw C.hwn
      C.X C.hX (Qle_refl C.a) C.b C.hbd C.hbn C.hTS C.hS1 C.hband_hi C.hband_lo C.hgh C.hgl q hq)
    (Req_symm (acPt_pos C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn q hq))

-- ===========================================================================
-- The `q^{-1/2}` weight, as a total function of the rational point.
--   integer scale  q = ⟨n,1⟩ :  n^{-1/2} = qInvSqrt n
--   recip scale    q = ⟨1,n⟩ :  n^{1/2}  = √n = RsqrtReal (ofQ ⟨n,1⟩)   (= (1/n)^{-1/2})
-- ===========================================================================

/-- `1 ≤ i` (Int) upgrades to `1 ≤ i.toNat`. -/
theorem toNat_ge_one {i : Int} (h : 1 ≤ i) : 1 ≤ i.toNat := by omega

/-- `1 ≤ d` gives `1 ≤ ofQ ⟨d,1⟩` (mirror of `oneLeSucc` for a general denominator). -/
theorem oneLe_ofQ_den (d : Nat) (hd : 1 ≤ d) :
    Rle one (ofQ (⟨(d : Int), 1⟩ : Q) Nat.one_pos) := by
  have hle : Qle (⟨1, 1⟩ : Q) (⟨(d : Int), 1⟩ : Q) := by
    simp only [Qle]; push_cast; omega
  exact Rle_ofQ_ofQ (by decide) Nat.one_pos hle

/-- The integer-scale weight `n^{-1/2}` (guarded; junk `0` off the integer scales). -/
def intWeight (i : Int) : Real :=
  if h : 1 ≤ i then qInvSqrt i.toNat (toNat_ge_one h) else zero

/-- The reciprocal-scale weight `√d = (1/d)^{-1/2}` (guarded; junk `0` when `d = 0`). -/
def recipWeight (d : Nat) : Real :=
  if h : 1 ≤ d then RsqrtReal (ofQ (⟨(d : Int), 1⟩ : Q) Nat.one_pos) (oneLe_ofQ_den d h) else zero

/-- **The `q^{-1/2}` weight**: `n^{-1/2}` at integer scales `⟨n,1⟩`, `√d` at reciprocal
    scales `⟨1,d⟩` (`den ≠ 1`), junk elsewhere (never read). -/
def normWeight (q : Q) : Real :=
  if q.den = 1 then intWeight q.num else recipWeight q.den

theorem intWeight_ofNat (n : Nat) (hn : 1 ≤ n) :
    Req (intWeight ((n : Int))) (qInvSqrt n hn) := by
  have hi : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
  show Req (if h : 1 ≤ ((n : Int)) then qInvSqrt ((n : Int)).toNat (toNat_ge_one h) else zero)
        (qInvSqrt n hn)
  rw [dif_pos hi]
  exact Req_refl _

theorem recipWeight_val (d : Nat) (hd : 1 ≤ d) :
    Req (recipWeight d) (RsqrtReal (ofQ (⟨(d : Int), 1⟩ : Q) Nat.one_pos) (oneLe_ofQ_den d hd)) := by
  show Req (if h : 1 ≤ d then RsqrtReal (ofQ (⟨(d : Int), 1⟩ : Q) Nat.one_pos) (oneLe_ofQ_den d h)
              else zero)
        (RsqrtReal (ofQ (⟨(d : Int), 1⟩ : Q) Nat.one_pos) (oneLe_ofQ_den d hd))
  rw [dif_pos hd]
  exact Req_refl _

/-- The weight at an integer scale `⟨m+1,1⟩` is `(m+1)^{-1/2} = qInvSqrt (m+1)`. -/
theorem normWeight_hi (m : Nat) :
    Req (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (qInvSqrt (m + 1) (Nat.succ_pos m)) := by
  show Req (if (⟨((m + 1 : Nat) : Int), 1⟩ : Q).den = 1
              then intWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q).num
              else recipWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q).den)
        (qInvSqrt (m + 1) (Nat.succ_pos m))
  rw [if_pos (rfl : (⟨((m + 1 : Nat) : Int), 1⟩ : Q).den = 1)]
  exact intWeight_ofNat (m + 1) (Nat.succ_pos m)

/-- The weight at a reciprocal scale `⟨1,m+1⟩` (`m ≥ 1`) is `(m+1)^{1/2} = √(m+1)`. -/
theorem normWeight_lo (m : Nat) (hm : 1 ≤ m) :
    Req (normWeight (⟨1, m + 1⟩ : Q))
        (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m)) := by
  have hne : ¬ ((⟨1, m + 1⟩ : Q).den = 1) := by
    have hd : (⟨1, m + 1⟩ : Q).den = m + 1 := rfl
    omega
  show Req (if (⟨1, m + 1⟩ : Q).den = 1
              then intWeight (⟨1, m + 1⟩ : Q).num
              else recipWeight (⟨1, m + 1⟩ : Q).den)
        (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m))
  rw [if_neg hne]
  refine Req_trans (recipWeight_val (m + 1) (Nat.succ_pos m)) ?_
  exact Req_refl _

-- ===========================================================================
-- (1)  `normAutocorrTest` — the genuine `q^{-1/2}·acPt` `WeilTest`.
-- ===========================================================================

/-- **THE NORMALIZED-AUTOCORRELATION WEIL TEST**: the point value `q^{-1/2}·acPt(q)`, built
    on the bundled autocorrelation test `acT`; support cutoff `X` and vanishing INHERITED
    from `acT` (the weight kills nothing: `weight·0 = 0`). -/
def normAutocorrTest (C : NormCtx) : WeilTest where
  f := fun q => Rmul (normWeight q) ((acT C).f q)
  X := C.X
  hX := C.hX
  supp_high := fun n hn =>
    Req_trans (Rmul_congr (Req_refl _) ((acT C).supp_high n hn)) (Rmul_zero _)
  supp_low := fun n hn =>
    Req_trans (Rmul_congr (Req_refl _) ((acT C).supp_low n hn)) (Rmul_zero _)

/-- Point-value readback at an integer scale: `f(m+1) ≈ (m+1)^{-1/2}·acPt(m+1)`. -/
theorem normAutocorr_f_hi (C : NormCtx) (m : Nat) :
    Req ((normAutocorrTest C).f (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
        (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m)) (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) := by
  show Req (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
              ((acT C).f (⟨((m + 1 : Nat) : Int), 1⟩ : Q)))
        (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m)) (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q)))
  exact Rmul_congr (normWeight_hi m) (acbase_eq_acPt C (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)

/-- Point-value readback at a reciprocal scale (`m ≥ 1`): `f(1/(m+1)) ≈ √(m+1)·acPt(1/(m+1))`. -/
theorem normAutocorr_f_lo (C : NormCtx) (m : Nat) (hm : 1 ≤ m) :
    Req ((normAutocorrTest C).f (⟨1, m + 1⟩ : Q))
        (Rmul (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m))
              (acPtC C (⟨1, m + 1⟩ : Q))) := by
  show Req (Rmul (normWeight (⟨1, m + 1⟩ : Q)) ((acT C).f (⟨1, m + 1⟩ : Q)))
        (Rmul (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m))
              (acPtC C (⟨1, m + 1⟩ : Q)))
  exact Rmul_congr (normWeight_lo m hm) (acbase_eq_acPt C (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))

-- ===========================================================================
-- (2)  The prime-side recovery: `weilPrimePart normAutocorrTest = acNormFold`.
-- ===========================================================================

/-- The reciprocal-weight bridge `(m+1)⁻¹ = ofQ ⟨1,m+1⟩ ≈ Rinv (ofQ ⟨m+1,1⟩)` — matches the
    unsymmetrized `n⁻¹` weight of `placeVal` to the `Rinv` weight of `acPlaceSym`. -/
theorem recip_bridge (m : Nat) :
    Req (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
        (Rinv (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) 1 (ofQn_wit (m + 1) (Nat.succ_pos m))) := by
  have hqn : (0 : Int) < (⟨((m + 1 : Nat) : Int), 1⟩ : Q).num := by
    show (0 : Int) < ((m + 1 : Nat) : Int); exact_mod_cast Nat.succ_pos m
  refine Req_symm (Req_trans (Rinv_ofQ Nat.one_pos hqn (ofQn_wit (m + 1) (Nat.succ_pos m))) ?_)
  apply Req_of_seq_Qeq
  intro _
  show Qeq (Qinv (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (⟨1, m + 1⟩ : Q)
  have ht : ((⟨((m + 1 : Nat) : Int), 1⟩ : Q).num).toNat = m + 1 := rfl
  simp only [Qeq, Qinv, ht]
  push_cast
  omega

/-- The finite-place value `f(n+1) + (n+1)⁻¹·f(1/(n+1))` — a LOCAL copy matching `weilPrimeTerm`'s
    inner expression in `Weil.lean` verbatim (so `weilPrimeTerm T n = Λ(n+1)·placeVal T n` by `rfl`),
    to avoid importing `CoupledWeilPlaceValue` (which drags `CoupledWeilKernel → ComplexZeta`). -/
private def placeVal (T : WeilTest) (n : Nat) : Real :=
  Radd (T.f (⟨((n + 1 : Nat) : Int), 1⟩ : Q))
    (Rmul (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) (T.f (⟨1, n + 1⟩ : Q)))

/-- **The place value of `normAutocorrTest` IS the symmetric autocorrelation place value**
    `acPlaceSym` (for `m ≥ 1`): `placeVal (n+1) = (n+1)^{-1/2}·acPt(n+1) + (n+1)⁻¹·√(n+1)·acPt(1/(n+1))`
    — the un-collapsed `F(n)+n⁻¹F(1/n)` with `F(q)=q^{-1/2}·acPt`. -/
theorem placeVal_eq_acPlaceSym (C : NormCtx) (m : Nat) (hm : 1 ≤ m) :
    Req (placeVal (normAutocorrTest C) m)
        (acPlaceSymC C (m + 1) (Nat.succ_pos m) (oneLeSucc m)) := by
  show Req
    (Radd ((normAutocorrTest C).f (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
          (Rmul (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)) ((normAutocorrTest C).f (⟨1, m + 1⟩ : Q))))
    (Radd (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m)) (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q)))
          (Rmul (Rinv (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) 1
                  (ofQn_wit (m + 1) (Nat.succ_pos m)))
                (Rmul (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m))
                      (acPtC C (⟨1, m + 1⟩ : Q)))))
  exact Radd_congr (normAutocorr_f_hi C m)
    (Rmul_congr (recip_bridge m) (normAutocorr_f_lo C m hm))

/-- **★ THE NON-GRAM PRIME-KERNEL RECOVERY**: the finite-place Weil prime side of the
    normalized-autocorrelation test equals the Λ-weighted √-normalized autocorrelation fold
    `acNormFold`.  Point-value identity (via `placeVal_eq_acPlaceSym` under `RsumN_congr`),
    the `n=1` term killed by `Λ(1)=0`.  NO `vFrom`, NO `primeGram`. -/
theorem weilPrimePart_normAutocorr (C : NormCtx) :
    Req (weilPrimePart (normAutocorrTest C)) (acNormFoldC C) := by
  show Req (RsumN (weilPrimeTerm (normAutocorrTest C)) C.X)
        (RsumN (fun m => Rmul (vonMangoldt (m + 1))
          (acPlaceSymC C (m + 1) (Nat.succ_pos m) (oneLeSucc m))) C.X)
  refine RsumN_congr C.X (fun m _ => ?_)
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hL : Req (weilPrimeTerm (normAutocorrTest C) 0) zero := by
      show Req (Rmul (vonMangoldt (0 + 1)) (placeVal (normAutocorrTest C) 0)) zero
      exact Req_trans (Rmul_congr vonMangoldt_one (Req_refl _))
        (Req_trans (Rmul_comm zero _) (Rmul_zero _))
    have hR : Req (Rmul (vonMangoldt (0 + 1))
        (acPlaceSymC C (0 + 1) (Nat.succ_pos 0) (oneLeSucc 0))) zero :=
      Req_trans (Rmul_congr vonMangoldt_one (Req_refl _))
        (Req_trans (Rmul_comm zero _) (Rmul_zero _))
    exact Req_trans hL (Req_symm hR)
  · show Req (Rmul (vonMangoldt (m + 1)) (placeVal (normAutocorrTest C) m))
        (Rmul (vonMangoldt (m + 1)) (acPlaceSymC C (m + 1) (Nat.succ_pos m) (oneLeSucc m)))
    exact Rmul_congr (Req_refl _) (placeVal_eq_acPlaceSym C m hpos)

-- ===========================================================================
-- (3)  The assembled arch-MINUS-prime functional at the normalized-autocorr slot.
-- ===========================================================================

/-- **The Weil pairing slot** on the normalized-autocorrelation test; `poles`/`archTail`
    are the honest interface Real inputs (the two integral components CC leaves unverified
    in print). -/
def normAutocorrSlot (C : NormCtx) (poles archTail : Real) : WeilSlot where
  test := normAutocorrTest C
  poles := poles
  archTail := archTail

/-- **THE ARCH-MINUS-PRIME WEIL FUNCTIONAL at the normalized-autocorr slot**:
    `W = poles − (acNormFold + weilArchConst + archTail)` — the assembled functional
    `weilValue` with the finite-place side rewritten to `acNormFold` (deliverable 2), the
    MINUS sign of `weilValue` intact.  `acNormFold` is now the ACTUAL point-value Weil prime
    side of the normalized autocorrelation. -/
theorem weilValue_normAutocorr (C : NormCtx) (poles archTail : Real) :
    Req (weilValue (normAutocorrSlot C poles archTail))
        (Rsub poles
          (Radd (acNormFoldC C)
                (Radd (weilArchConst (normAutocorrTest C)) archTail))) := by
  show Req
    (Rsub poles
      (Radd (weilPrimePart (normAutocorrTest C))
            (Radd (weilArchConst (normAutocorrTest C)) archTail)))
    (Rsub poles
      (Radd (acNormFoldC C)
            (Radd (weilArchConst (normAutocorrTest C)) archTail)))
  exact Rsub_congr (Req_refl poles)
    (Radd_congr (weilPrimePart_normAutocorr C) (Req_refl _))

-- ===========================================================================
-- (4)  A proved-nonzero supported normalized-autocorr test.
-- ===========================================================================

/-- **NONZERO INSTANTIATION**: if the autocorrelation `q^{-1/2}·acPt` value at the integer
    scale `m+1` is nonzero (the explicit in-band nonvanishing hypothesis), then
    `normAutocorrTest.f` is nonzero there — a proved-nonzero, compactly-supported point-value
    test.  (Stated with the nonzero hypothesis explicit: no literal `g` is fabricated.) -/
theorem normAutocorr_nonzero (C : NormCtx) (m : Nat)
    (hpos : ¬ Req (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m))
              (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) zero) :
    ¬ Req ((normAutocorrTest C).f (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) zero := by
  intro h
  exact hpos (Req_trans (Req_symm (normAutocorr_f_hi C m)) h)

-- ===========================================================================
-- (5)  Tie to the crux (positivity = RH — NOT proved).
-- ===========================================================================

/-- **TIE TO THE CRUX (positivity = RH, NEVER proved here).**  Feeding the family
    `W n = weilValue (normAutocorrSlot Cₙ poles archTail)` (the arch-MINUS-prime functional of
    the normalized autocorrelation, deliverable 3) into `weil_psd_iff_hodge` shows that PSD
    of the pairing family is EQUIVALENT to Hodge-index negativity of the induced spectral
    square (`weilSpectralSquare W`); through the standing chain (Hodge index ⟺ Li
    non-negativity ⟺ dominance, and `hodgeIndex_iff_RH`) the property `∀ n>0, Rnonneg (W n)`
    — Weil positivity of the genuine normalized-autocorrelation functional — is RH.  That
    positivity is the OPEN content and is asserted NOWHERE in this file; here we only expose
    the equivalence, which is elementary and two-sided. -/
theorem normAutocorr_weil_psd_iff_hodge (W : Nat → Real) :
    (∀ n : Nat, 0 < n → Rnonneg (W n)) ↔ SpectralHodgeNeg (weilSpectralSquare W) :=
  weil_psd_iff_hodge W

end UOR.Bridge.F1Square.Square
