/-
F1 square — **the HONEST RH reduction for the normalized-autocorrelation Weil functional**
(`WeilPrimeShiftRH.lean`).

The definitional restatement `normAutocorr_weil_psd_iff_hodge` (PSD ⟺ Hodge of `weilSpectralSquare W`)
is content-free: for an arbitrary `W` the square is BUILT from `W`, so it establishes nothing about RH
for the constructed functional.  The genuine tie to RH requires identifying the constructed
arch-MINUS-prime family with the genuine Li coefficients — the classical EXPLICIT FORMULA
`W n ≈ genuineLamSeq E.eta n` (constructed prime−archimedean pairing = `λₙ`).  That identity is NOT
proved anywhere in this repository.  (Update: the certified pole and archimedean integrals of the
normalized autocorrelation now EXIST and are identified semantically — `MellinPole`/`PoleForm_diag`,
`ArchIntegral`/`ArchTailForm_diag`, `CoupledForm_diag_semantic`; what remains unbuilt is the explicit
formula itself, i.e. the equality of that constructed functional with the zero side / `λₙ`.)

This module states the reduction HONESTLY, with that identity as an EXPLICIT, audit-visible hypothesis
`hid`.  `normAutocorr_positivity_iff_RH` shows: IF the constructed family equals the genuine Li
sequence, THEN its Weil positivity `∀ n>0, Rnonneg (W n)` is EQUIVALENT to RH (`AllZerosOnLine`), via
the standing chain `spectral_bridge_nonneg` (Hodge ⟺ Li) ∘ `hodgeIndex_iff_RH` (Li ⟺ zeros).  It does
NOT prove `hid` for the constructed poles/archTail, does NOT prove positivity, and does NOT claim RH.
It precisely LOCALIZES the remaining wall to the explicit-formula identity `hid` — the honest form of
"identify the pairing family with `genuineLamSeq` before invoking the RH equivalence".

This is the one module in the normalized-autocorrelation layer that genuinely references the RH
endpoint (`hodgeIndex_iff_RH`), so it — and only it — carries the analytic-stack import; the
infrastructure modules (`WeilPrimeShiftCrux`, `…Sonine`) stay off it.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftCrux
import F1Square.Square.AtlasAnalyticFace

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

/-- **THE HONEST RH REDUCTION (positivity itself = RH is NOT proved; `hid` is NOT proved).**
    Given the classical explicit-formula identity `hid : ∀ n>0, W n ≈ genuineLamSeq E.eta n` — the
    constructed arch-MINUS-prime normalized-autocorrelation functional equals the genuine Li
    coefficients — the Weil positivity of the family `W` is EQUIVALENT to RH (all zeros on the critical
    line).  Chain: `Rnonneg`-congruence along `hid` turns `∀ n>0, Rnonneg (W n)` into
    `LiNonneg (genuineLamSeq E.eta)`; `spectral_bridge_nonneg` turns that into the Hodge-index
    non-negativity of `genuineSpectralSquare E`; `hodgeIndex_iff_RH` turns that into `AllZerosOnLine`.

    `hid` is the CLASSICAL EXPLICIT FORMULA and is asserted NOWHERE (the certified pole/archimedean
    integrals now exist — `MellinPole`, `ArchIntegral` — but their equality with the zero side / `λₙ`
    is the unbuilt local–global seam).
    Positivity `∀ n>0, Rnonneg (W n)` is the OPEN content and is asserted NOWHERE.  This theorem only
    exposes the reduction, localizing the entire remaining gap to `hid`.  Crux fields stay `none`. -/
theorem normAutocorr_positivity_iff_RH
    (E : StieltjesEta) (L : LiBridge E) (W : Nat → Real)
    (hid : ∀ n : Nat, 0 < n → Req (W n) (genuineLamSeq E.eta n)) :
    (∀ n : Nat, 0 < n → Rnonneg (W n)) ↔ AllZerosOnLine L.isZero := by
  have hstep1 : (∀ n : Nat, 0 < n → Rnonneg (W n)) ↔ LiNonneg (genuineLamSeq E.eta) := by
    constructor
    · intro h n hn; exact Rnonneg_congr (hid n hn) (h n hn)
    · intro h n hn; exact Rnonneg_congr (Req_symm (hid n hn)) (h n hn)
  exact Iff.trans hstep1
    (Iff.trans (spectral_bridge_nonneg (genuineSpectralSquare E)).symm (hodgeIndex_iff_RH E L))

end UOR.Bridge.F1Square.Square
