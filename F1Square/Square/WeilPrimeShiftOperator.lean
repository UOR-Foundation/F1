/-
F1 square — **the SCALAR point-value skeleton of the finite-prime side** (`WeilPrimeShiftOperator.lean`).

SCOPE / HONEST LABELLING.  `Nop` here is a SCALAR object — WEIGHTED POINT EVALUATION `q ↦ q^{-1/2}·h(q)`
of point-value data `h : Q → Real`, NOT an operator on `L2Test` and NOT a completion.  It is the
DIAGONAL shadow of the genuine two-test Haar bilinear form `HForm`/`BForm` (`WeilPrimeShiftHaarForm.lean`),
which is where the real operator content lives:
  • the genuine two-input reciprocal / adjoint law `H_q(f,g) = H_{1/q}(g,f)` (`HForm_recip`), and
  • the CORRECT adjoint law `B_q(f,g) = q^{-1}·B_{1/q}(g,f)`  (`BForm_adjoint`), i.e. `N_q* = q^{-1}·N_{1/q}`
    for `N_q = q^{-1/2}·U_q` — NOT `N_q* = N_{1/q}`.
This file only records the scalar diagonal skeleton and its readback to the collapsed prime sum.

WHAT IS BUILT (scalar, point-value):
  1. `Nop h q = q^{-1/2}·h(q) = normWeight(q)·h(q)` — weighted point evaluation.  `Nop_hi`/`Nop_lo`
     read it back at integer/reciprocal scales.
  2. `Nop_adjoint` / `Nop_adjoint_ac` — the DIAGONAL weight relation `(1/n)·N(1/n)h = N(n)h` on data with
     reciprocal self-duality `h(n) ≈ h(1/n)` (`autocorr_recip_all` on the actual autocorrelation).  This
     is a diagonal consequence of reciprocity, NOT the operator adjoint law (that is `BForm_adjoint`,
     `N_q* = q^{-1}·N_{1/q}`, on the genuine two-test form).
  3. `primePlaceOp h n = Λ(n+1)·(N(n+1)h + (n+1)⁻¹·N(1/(n+1))h)` — the per-place SCALAR.  Its diagonal
     value equals the diagonal of the genuine two-test `PForm` (`PForm_diag` in `WeilPrimeShiftHaarForm`).
  4. `primePlaceOp_readback` / `primePlaceOp_readback_collapsed` — the fold of `primePlaceOp` over the
     autocorrelation equals `weilPrimePart (normAutocorrTest)`, hence the collapsed Burnol-normalized
     prime sum `Σ 2·Λ(n)·n^{-1/2}·h(n)`.  No `primeGram`, no `vFrom`, no `vHat`, no PSD.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftCrux

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1)  N(q): the Haar-core normalized dilation operator (point-value form).
-- ===========================================================================

/-- **N(q): WEIGHTED POINT EVALUATION** (scalar, NOT an operator): on point-value data `h`,
    `N(q)h = q^{-1/2}·h(q) = normWeight(q)·h(q)`.  The genuine operator lives in the two-test Haar form
    `HForm`/`BForm` (`WeilPrimeShiftHaarForm.lean`); this is its diagonal shadow at the base point. -/
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

/-- **THE DIAGONAL WEIGHT RELATION** `N(1/n) = n·N(n)` on data `h` with reciprocal self-duality
    `hsym : h(n) ≈ h(1/n)`.  This is a DIAGONAL consequence of reciprocity, NOT the operator adjoint law
    (the correct adjoint is `N_q* = q^{-1}·N_{1/q}`, proved on the genuine two-test form as
    `WeilPrimeShiftHaarForm.BForm_adjoint`).  Proved from the reflection identity `F_reflect`
    (`√n·h(1/n) = n·(n^{-1/2}·h(n))`), bridged by the `Nop` readbacks.  No PSD is claimed. -/
theorem Nop_adjoint (h : Q → Real) (m : Nat) (hm : 1 ≤ m)
    (hsym : Req (h (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (h (⟨1, m + 1⟩ : Q))) :
    Req (Nop h (⟨1, m + 1⟩ : Q))
        (Rmul (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos)
              (Nop h (⟨((m + 1 : Nat) : Int), 1⟩ : Q))) :=
  Req_trans (Nop_lo h m hm)
    (Req_trans (F_reflect (m + 1) (Nat.succ_pos m) (oneLeSucc m) h hsym)
      (Rmul_congr (Req_refl _) (Req_symm (Nop_hi h m))))

/-- **THE DIAGONAL WEIGHT RELATION ON THE ACTUAL AUTOCORRELATION** (reciprocal self-duality NOT assumed):
    feeding the PROVEN `autocorr_recip_all` as the `hsym` of `Nop_adjoint`, `N(1/(m+1)) = (m+1)·N(m+1)`
    holds on the genuine autocorrelation point value `acPtC C` (for `m ≥ 1`, place `m+1 ≤ S`).  Diagonal
    relation, not the operator adjoint — see `WeilPrimeShiftHaarForm.BForm_adjoint`. -/
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
