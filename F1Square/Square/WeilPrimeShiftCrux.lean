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
  /-- strict lower support edge `b > 0` (needed by the CC √-normalization collapse) -/
  hbnpos : 0 < b.num
  /-- the compact-support fit `1/b ≤ a+w` (the window contains the reflected support) -/
  hfit : Qle (Qinv b) (add a w)
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
-- **The genuine total `q^{-1/2}` weight** `q ↦ √(1/q) = Rsqrt (Qinv q)` — an ACTUAL function of the
-- rational VALUE, representation-invariant on the positive cone `q.num > 0` (where `x^{-1/2}` is
-- defined and where the autocorrelation window lives).  Junk `0` off the positive cone (`x^{-1/2}`
-- has no value there, and the window is never read there).  This is the admissible replacement for
-- the previous selected-point weight (which gave `1/2` and `2/4` DIFFERENT weights).
--   integer scale  q = ⟨n,1⟩ :  Rsqrt (Qinv ⟨n,1⟩) = Rsqrt ⟨1,n⟩ = n^{-1/2}     = qInvSqrt n
--   recip scale    q = ⟨1,n⟩ :  Rsqrt (Qinv ⟨1,n⟩) = Rsqrt ⟨n,1⟩ = √n = (1/n)^{-1/2} = RsqrtReal(ofQ⟨n,1⟩)
-- ===========================================================================

/-- **`Rsqrt` is `Qeq`-congruent**: equal rational radicands have equal square roots (two-sided
    `Rsqrt_mono` + `Rle_antisymm`). -/
theorem Rsqrt_congr {q q' : Q} (hqd : 0 < q.den) (hq'd : 0 < q'.den)
    (hq : Qle (⟨0, 1⟩ : Q) q) (hq' : Qle (⟨0, 1⟩ : Q) q') (h : Qeq q q') :
    Req (Rsqrt q hqd hq) (Rsqrt q' hq'd hq') :=
  Rle_antisymm
    (Rsqrt_mono hqd hq'd hq hq' (Qeq_le h))
    (Rsqrt_mono hq'd hqd hq' hq (Qeq_le (Qeq_symm h)))

/-- **`Qinv` is `Qeq`-congruent** on the positive-numerator cone (`1/q` depends only on `q`'s value). -/
theorem Qinv_congr {q q' : Q} (hqn : 0 < q.num) (hq'n : 0 < q'.num) (h : Qeq q q') :
    Qeq (Qinv q) (Qinv q') := by
  show (q.den : Int) * ((q'.num.toNat : Nat) : Int) = (q'.den : Int) * ((q.num.toNat : Nat) : Int)
  rw [Int.toNat_of_nonneg (Int.le_of_lt hqn), Int.toNat_of_nonneg (Int.le_of_lt hq'n)]
  have h' : q.num * (q'.den : Int) = q'.num * (q.den : Int) := h
  calc (q.den : Int) * q'.num
      = q'.num * (q.den : Int) := Int.mul_comm _ _
    _ = q.num * (q'.den : Int) := h'.symm
    _ = (q'.den : Int) * q.num := Int.mul_comm _ _

/-- `0 ≤ Qinv q` (its numerator is `q.den ≥ 0`) — the nonneg radicand certificate. -/
theorem qinv_num_nonneg (q : Q) : Qle (⟨0, 1⟩ : Q) (Qinv q) := by
  show (0 : Int) * ((Qinv q).den : Int) ≤ (q.den : Int) * ((1 : Nat) : Int)
  have : (0 : Int) ≤ (q.den : Int) := Int.ofNat_nonneg _
  omega

/-- **THE `q^{-1/2}` WEIGHT**, a genuine total function of the rational point: `√(1/q) = Rsqrt (Qinv q)`
    on the positive cone `q.num > 0` (where `x^{-1/2}` is defined and where the autocorrelation lives),
    junk `0` off it.  Representation-invariant (`normWeight_congr`). -/
def normWeight (q : Q) : Real :=
  if h : 0 < q.num then Rsqrt (Qinv q) (Qinv_den_pos h) (qinv_num_nonneg q) else zero

/-- On the positive cone the weight is `Rsqrt (Qinv q)` (the guard fires). -/
theorem normWeight_pos_eq {q : Q} (hqn : 0 < q.num) :
    Req (normWeight q) (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)) := by
  show Req (if h : 0 < q.num then Rsqrt (Qinv q) (Qinv_den_pos h) (qinv_num_nonneg q) else zero)
        (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q))
  rw [dif_pos hqn]
  exact Req_refl _

/-- **THE ADMISSIBILITY / RATIONAL-CONGRUENCE OF THE WEIGHT**: on the positive cone the weight depends
    only on the rational's VALUE, not its representative — `1/2` and `2/4` both receive `√2`.  This is
    exactly the invariance whose ABSENCE made the previous `normWeight` selected-point data. -/
theorem normWeight_congr {q q' : Q} (hqn : 0 < q.num) (hq'n : 0 < q'.num) (h : Qeq q q') :
    Req (normWeight q) (normWeight q') :=
  Req_trans (normWeight_pos_eq hqn)
    (Req_trans
      (Rsqrt_congr (Qinv_den_pos hqn) (Qinv_den_pos hq'n) (qinv_num_nonneg q) (qinv_num_nonneg q')
        (Qinv_congr hqn hq'n h))
      (Req_symm (normWeight_pos_eq hq'n)))

/-- The weight at an integer scale `⟨m+1,1⟩` is `(m+1)^{-1/2} = qInvSqrt (m+1)`:
    `√(1/(m+1)) = Rsqrt ⟨1,m+1⟩`, matched to `qInvSqrt` by unique-nonneg-root (`Rsqrt_unique`). -/
theorem normWeight_hi (m : Nat) :
    Req (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (qInvSqrt (m + 1) (Nat.succ_pos m)) := by
  have hnum : 0 < (⟨((m + 1 : Nat) : Int), 1⟩ : Q).num := by
    show (0 : Int) < ((m + 1 : Nat) : Int); exact_mod_cast Nat.succ_pos m
  refine Req_trans (normWeight_pos_eq hnum) ?_
  refine Req_symm (Rsqrt_unique (Qinv_den_pos hnum) (qinv_num_nonneg _)
    (qInvSqrt_nonneg (m + 1) (Nat.succ_pos m)) ?_)
  exact Req_trans (qInvSqrt_sq (m + 1) (Nat.succ_pos m))
    (Rinv_ofQ Nat.one_pos hnum (ofQn_wit (m + 1) (Nat.succ_pos m)))

/-- The weight at a reciprocal scale `⟨1,m+1⟩` is `(m+1)^{1/2} = √(m+1) = RsqrtReal (ofQ ⟨m+1,1⟩)`:
    `√(m+1) = Rsqrt ⟨m+1,1⟩`, matched to `RsqrtReal` by unique-nonneg-root (`Rsqrt_unique`). -/
theorem normWeight_lo (m : Nat) (hm : 1 ≤ m) :
    Req (normWeight (⟨1, m + 1⟩ : Q))
        (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m)) := by
  have hnum : 0 < (⟨1, m + 1⟩ : Q).num := by show (0 : Int) < 1; decide
  refine Req_trans (normWeight_pos_eq hnum) ?_
  refine Req_symm (Rsqrt_unique (Qinv_den_pos hnum) (qinv_num_nonneg _)
    (RsqrtReal_nonneg _ (oneLeSucc m)) ?_)
  refine Req_trans (RsqrtReal_sq (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m)) ?_
  exact ofQ_congr Nat.one_pos (Qinv_den_pos hnum) (Qeq_refl _)

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

/-- The bundled autocorrelation value `(acT C).f` respects rational equality (`Qeq`-congruence):
    it is `acPt` under `acbase_eq_acPt`, and `acPt` is congruent (`acPt_congr`). -/
theorem acT_congr (C : NormCtx) {q q' : Q} (hqd : 0 < q.den) (hq'd : 0 < q'.den) (h : Qeq q q') :
    Req ((acT C).f q) ((acT C).f q') :=
  Req_trans (acbase_eq_acPt C q hqd)
    (Req_trans
      (acPt_congr C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn q q' hqd hq'd h)
      (Req_symm (acbase_eq_acPt C q' hq'd)))

/-- **THE NORMALIZED AUTOCORRELATION IS A GENUINE ADMISSIBLE FUNCTION**: its point value
    `q^{-1/2}·acPt(q)` depends only on the rational's VALUE on the positive cone, not its representative
    — `normWeight_congr` (weight) times `acT_congr` (autocorrelation).  So `normAutocorrTest` is a real
    function of the multiplicative point, NOT selected-point data: `1/2` and `2/4` map to the same value. -/
theorem normAutocorrTest_congr (C : NormCtx) {q q' : Q}
    (hqn : 0 < q.num) (hq'n : 0 < q'.num) (hqd : 0 < q.den) (hq'd : 0 < q'.den) (h : Qeq q q') :
    Req ((normAutocorrTest C).f q) ((normAutocorrTest C).f q') :=
  Rmul_congr (normWeight_congr hqn hq'n h) (acT_congr C hqd hq'd h)

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

/-- The per-place band hypothesis of `acNormFold_collapse`, derived from the cutoff `C.hTS`:
    for `m < X`, `⟨m+1,1⟩ ≤ ⟨X+1,1⟩ ≤ S`. -/
theorem normCtx_hnS (C : NormCtx) (m : Nat) (hm : m < C.X) :
    Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) C.S := by
  have hab : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (⟨((C.X + 1 : Nat) : Int), 1⟩ : Q) := by
    show ((m + 1 : Nat) : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast; omega
  exact Qle_trans Nat.one_pos hab C.hTS

/-- **★ THE COLLAPSED BURNOL-NORMALIZED PRIME SIDE**: the finite-place Weil prime side of the
    normalized-autocorrelation test collapses to the genuine `Σ_{m<X} 2·Λ(m+1)·(m+1)^{-1/2}·h(m+1)` —
    the Burnol √-normalized prime sum `Σ 2Λ(n) n^{-1/2} h(n)`.  Chains the prime-side recovery
    (`weilPrimePart_normAutocorr`) with the CC symmetric collapse (`acNormFold_collapse`, previously
    orphaned) using the STRENGTHENED `NormCtx` support data (`hbnpos`, `hfit`) and the derived per-place
    band (`normCtx_hnS`).  The reflection symmetry consumed is the PROVEN `autocorr_recip_all`. -/
theorem weilPrimePart_normAutocorr_collapsed (C : NormCtx) :
    Req (weilPrimePart (normAutocorrTest C))
        (RsumN (fun m => Rmul (vonMangoldt (m + 1))
          (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
            (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m))
              (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q))))) C.X) :=
  Req_trans (weilPrimePart_normAutocorr C)
    (acNormFold_collapse C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn
      C.b C.hbd C.hbnpos C.X C.hgh C.hgl C.hfit (fun m hm => normCtx_hnS C m hm))

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

/-- **THE DEFINITIONAL PSD ⟺ HODGE RESTATEMENT (content-free; NOT an RH tie).**  For an ARBITRARY
    family `W`, `weilSpectralSquare W` is BUILT from `W`, so `(∀ n>0, Rnonneg (W n)) ⟺ Hodge-index
    negativity of `weilSpectralSquare W`` is a purely definitional two-sided restatement (`weil_psd_iff_hodge`).

    IMPORTANT — this lemma establishes NOTHING about RH for the constructed normalized-autocorrelation
    functional.  It does not mention `NormCtx`, `weilValue`, or `genuineSpectralSquare`, and
    `weilSpectralSquare W` is NOT identified with the genuine spectral/Li square for the constructed
    `W`.  The genuine RH tie requires the classical explicit-formula identity `W n ≈ genuineLamSeq E.eta n`
    (constructed arch-MINUS-prime functional = the genuine Li coefficients), which is PROVED NOWHERE.
    The honest conditional form — assuming exactly that identity as an explicit hypothesis — is
    `WeilPrimeShiftRH.normAutocorr_positivity_iff_RH`.  Positivity itself (= RH) is asserted nowhere. -/
theorem normAutocorr_weil_psd_iff_hodge (W : Nat → Real) :
    (∀ n : Nat, 0 < n → Rnonneg (W n)) ↔ SpectralHodgeNeg (weilSpectralSquare W) :=
  weil_psd_iff_hodge W

end UOR.Bridge.F1Square.Square
