/-
F1 square — **the direct point-value operator route**: the Haar-core normalized dilation `N(q)`, its
correctly-weighted adjoint law `N(1/q) = q·N(q)`, and the per-place operator `primePlaceOp` whose
finite quadratic readback is EXACTLY `weilPrimePart_normAutocorr_collapsed` (`WeilPrimeShiftOperator.lean`).

This is the operator layer over the proved point-value facts, built WITHOUT the rejected shortcuts:
NO `primeGram`, NO `vFrom`, NO `vHat`, and NO PSD claim about the operator.

WHAT IS BUILT (point-value operator form — the Haar-integral readback of the dilation):
  1. `Nop h q = q^{-1/2}·h(q) = normWeight(q)·h(q)` — the **Haar-core normalized dilation** acting on the
     autocorrelation point-value data `h`.  `Nop_hi`/`Nop_lo` read it back at integer/reciprocal scales.
  2. `Nop_adjoint` — **the correctly-weighted adjoint law** `N(1/n) = n·N(n)` (`N(q)† = N(1/q)` in
     point-value form): the reciprocal dilation is the forward dilation scaled by `n`, whenever the data
     has reciprocal self-duality `h(n) ≈ h(1/n)`.  Proved from the reflection identity `F_reflect`.
  3. `Nop_adjoint_ac` — the adjoint law PROVED on the ACTUAL autocorrelation, feeding the reciprocal
     self-duality from the PROVEN `autocorr_recip_all` (not assumed).
  4. `primePlaceOp h n = Λ(n+1)·(N(n+1)h + (n+1)⁻¹·N(1/(n+1))h)` — the per-place operator.
  5. `primePlaceOp_readback` / `primePlaceOp_readback_collapsed` — **THE FINITE QUADRATIC READBACK**:
     the fold of `primePlaceOp` over the autocorrelation point value equals `weilPrimePart
     (normAutocorrTest)`, hence (through `weilPrimePart_normAutocorr_collapsed`) the collapsed
     Burnol-normalized prime sum `Σ 2·Λ(n)·n^{-1/2}·h(n)`.  No `primeGram`, no `vFrom`, no PSD.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftCrux

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1)  N(q): the Haar-core normalized dilation operator (point-value form).
-- ===========================================================================

/-- **N(q): the Haar-core normalized dilation operator, point-value form.**  Acting on autocorrelation
    point-value data `h`, `N(q)h = q^{-1/2}·h(q) = normWeight(q)·h(q)` — the `q^{-1/2}`-normalized
    dilation-by-`q` read at the base point (the Haar-integral readback of the dilation). -/
def Nop (h : Q → Real) (q : Q) : Real := Rmul (normWeight q) (h q)

/-- Integer-scale readback: `N(n+1)h = (n+1)^{-1/2}·h(n+1)`. -/
theorem Nop_hi (h : Q → Real) (m : Nat) :
    Req (Nop h (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
        (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m)) (h (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) :=
  Rmul_congr (normWeight_hi m) (Req_refl _)

/-- Reciprocal-scale readback (`m ≥ 1`): `N(1/(m+1))h = √(m+1)·h(1/(m+1))`. -/
theorem Nop_lo (h : Q → Real) (m : Nat) (hm : 1 ≤ m) :
    Req (Nop h (⟨1, m + 1⟩ : Q))
        (Rmul (RsqrtReal (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) (oneLeSucc m))
              (h (⟨1, m + 1⟩ : Q))) :=
  Rmul_congr (normWeight_lo m hm) (Req_refl _)

-- ===========================================================================
-- (2)  The correctly-weighted adjoint law  N(1/n) = n·N(n).
-- ===========================================================================

/-- **THE CORRECTLY-WEIGHTED ADJOINT LAW** `N(1/n) = n·N(n)` (the point-value form of `N(q)† = N(1/q)`):
    the reciprocal normalized dilation equals the forward normalized dilation scaled by `n`, for any
    data `h` with reciprocal self-duality `hsym : h(n) ≈ h(1/n)`.  Proved from the reflection identity
    `F_reflect` (`√n·h(1/n) = n·(n^{-1/2}·h(n))`), bridged by the `Nop` readbacks.  No PSD is claimed. -/
theorem Nop_adjoint (h : Q → Real) (m : Nat) (hm : 1 ≤ m)
    (hsym : Req (h (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (h (⟨1, m + 1⟩ : Q))) :
    Req (Nop h (⟨1, m + 1⟩ : Q))
        (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
              (Nop h (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) :=
  Req_trans (Nop_lo h m hm)
    (Req_trans (F_reflect (m + 1) (Nat.succ_pos m) (oneLeSucc m) h hsym)
      (Rmul_congr (Req_refl _) (Req_symm (Nop_hi h m))))

/-- **THE ADJOINT LAW ON THE ACTUAL AUTOCORRELATION** (reciprocal self-duality NOT assumed): feeding
    the PROVEN `autocorr_recip_all` as the `hsym` of `Nop_adjoint`, `N(1/(m+1)) = (m+1)·N(m+1)` holds on
    the genuine autocorrelation point value `acPtC C` (for `m ≥ 1`, place `m+1 ≤ S`). -/
theorem Nop_adjoint_ac (C : NormCtx) (m : Nat) (hm : 1 ≤ m)
    (hmS : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) C.S) :
    Req (Nop (acPtC C) (⟨1, m + 1⟩ : Q))
        (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
              (Nop (acPtC C) (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) :=
  Nop_adjoint (acPtC C) m hm
    (autocorr_recip_all C.g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos
      (m + 1) (Nat.succ_pos m) C.hgh C.hgl C.hfit hmS)

-- ===========================================================================
-- (3)  primePlaceOp and its finite quadratic readback.
-- ===========================================================================

/-- **The per-place operator** `primePlaceOp h n = Λ(n+1)·(N(n+1)h + (n+1)⁻¹·N(1/(n+1))h)` — the
    finite place `n+1` of the direct point-value operator route (indexed `0`-based to align with the
    `RsumN` fold).  The weight `(n+1)⁻¹ = ofQ ⟨1,n+1⟩` is the unsymmetrized CC weight, matching
    `weilPrimeTerm`. -/
def primePlaceOp (h : Q → Real) (n : Nat) : Real :=
  Rmul (vonMangoldt (n + 1))
    (Radd (Nop h (⟨((n + 1 : Nat) : Int), 1⟩ : Q))
      (Rmul (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) (Nop h (⟨1, n + 1⟩ : Q))))

/-- Per-place identity: `primePlaceOp (acPtC C) n = weilPrimeTerm (normAutocorrTest C) n` — the operator
    place value IS the finite-place Weil term of the normalized-autocorrelation test (each `Nop (acPtC C)`
    matched to `normAutocorrTest.f` by `acbase_eq_acPt`). -/
theorem primePlaceOp_eq_weilPrimeTerm (C : NormCtx) (n : Nat) :
    Req (primePlaceOp (acPtC C) n) (weilPrimeTerm (normAutocorrTest C) n) :=
  Rmul_congr (Req_refl _)
    (Radd_congr
      (Rmul_congr (Req_refl _)
        (Req_symm (acbase_eq_acPt C (⟨((n + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)))
      (Rmul_congr (Req_refl _)
        (Rmul_congr (Req_refl _)
          (Req_symm (acbase_eq_acPt C (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))))))

/-- **THE FINITE QUADRATIC READBACK**: the fold of the per-place operator over the autocorrelation point
    value equals the finite-place Weil prime side `weilPrimePart (normAutocorrTest C)` (`RsumN_congr` over
    the per-place identity; `weilPrimePart` is that sum by definition). -/
theorem primePlaceOp_readback (C : NormCtx) :
    Req (RsumN (primePlaceOp (acPtC C)) C.X) (weilPrimePart (normAutocorrTest C)) :=
  RsumN_congr C.X (fun n _ => primePlaceOp_eq_weilPrimeTerm C n)

/-- **★ primePlaceOp's finite quadratic readback IS `weilPrimePart_normAutocorr_collapsed`**: the fold of
    the per-place operator over the autocorrelation collapses to the genuine Burnol-normalized prime sum
    `Σ_{m<X} 2·Λ(m+1)·(m+1)^{-1/2}·h(m+1)`.  Chains `primePlaceOp_readback` with the collapsed identity.
    NO `primeGram`, NO `vFrom`, NO `vHat`; NO PSD claim. -/
theorem primePlaceOp_readback_collapsed (C : NormCtx) :
    Req (RsumN (primePlaceOp (acPtC C)) C.X)
        (RsumN (fun m => Rmul (vonMangoldt (m + 1))
          (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide))
            (Rmul (qInvSqrt (m + 1) (Nat.succ_pos m))
              (acPtC C (⟨((m + 1 : Nat) : Int), 1⟩ : Q))))) C.X) :=
  Req_trans (primePlaceOp_readback C) (weilPrimePart_normAutocorr_collapsed C)

end UOR.Bridge.F1Square.Square
