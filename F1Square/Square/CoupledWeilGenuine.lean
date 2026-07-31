/-
F1 square — **the coupled kernel welded to the genuine crux** (`CoupledWeilGenuine.lean`): connecting
the off-diagonal coupled Weil kernel to the program's central localization `atlas_crux_localization`,
so its strict diagonal dominance is tied to the GENUINE prime–archimedean coupling positivity, not a
generic induced square.

The coupled kernel's diagonal is `coupledWeil arch w v M (n,n) = arch n − primeGram(n,n)` — the Weil
value at index `n`. The explicit-formula identity is that this Weil value equals `2λₙ = −⟨Cₙ,Cₙ⟩ =
Rneg (genuineSpectralSquare E).cSq n` (the pairing dictionary, `genuineSpectralSquare_dict`). Supplying
that identity as an EXPLICIT hypothesis `hmatch` (exactly the `realizesDiag_genuine_iff` discipline —
the diagonal match is the interface, never proven; proving it is the explicit formula), the coupled
kernel's strict diagonal dominance becomes the genuine crux:

  • `coupledWeil_diag_pos_iff_genuine_crux` — under `hmatch`, `(∀n>0, Pos (coupledWeil arch w v M n n))
    ⟺ SpectralCrux (genuineSpectralSquare E)` (a `Pos_congr` on the diagonal match; `SpectralCrux` is
    `Pos (−cSq)`).
  • `coupledWeil_diag_pos_iff_genuine_coupling` — chaining through `atlas_crux_localization`, under
    `hmatch` the strict diagonal dominance is EQUIVALENT to the genuine coupling positivity
    `∀n>0, Pos (genuineArithSeq E.eta n + genuineArchSeq n)` — THE crux.

HONEST SCOPE. `hmatch` (the coupled Weil diagonal equals `2λₙ`, the explicit-formula identity) is an
EXPLICIT hypothesis, never discharged — there is no instantiation of `arch, w, v` at the genuine `ζ`
data that proves it, and even with it the strict dominance is `SpectralCrux` = RH, never asserted. This
weld only routes the coupled kernel's face into the program's central crux equivalence; it discharges
nothing. Crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/
import F1Square.Square.CoupledWeilKernel
import F1Square.Square.AtlasCruxSynthesis

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

set_option maxHeartbeats 1000000 in
/-- **The coupled kernel's strict diagonal dominance ⟺ the genuine `SpectralCrux`**, under the
    explicit-formula diagonal match `hmatch : coupledWeil arch w v M (n,n) ≈ −⟨Cₙ,Cₙ⟩ = 2λₙ`. A
    `Pos_congr` on the match (`SpectralCrux` unfolds to `∀n>0, Pos (Rneg (·.cSq n))`). The match is
    never proven; it is the interface. -/
theorem coupledWeil_diag_pos_iff_genuine_crux (E : StieltjesEta)
    (arch w : Nat → Real) (v : Nat → Nat → Real) (M : Nat)
    (hmatch : ∀ n, 0 < n →
      Req (coupledWeil arch w v M n n) (Rneg ((genuineSpectralSquare E).cSq n))) :
    (∀ n, 0 < n → Pos (coupledWeil arch w v M n n)) ↔ SpectralCrux (genuineSpectralSquare E) := by
  constructor
  · intro h n hn; exact Pos_congr (hmatch n hn) (h n hn)
  · intro h n hn; exact Pos_congr (Req_symm (hmatch n hn)) (h n hn)

set_option maxHeartbeats 1000000 in
/-- **★ THE GENUINE WELD**: under the explicit-formula diagonal match, the coupled kernel's strict
    diagonal dominance is EQUIVALENT to the genuine prime–archimedean coupling positivity
    `∀n>0, Pos (genuineArithSeq E.eta n + genuineArchSeq n)` — THE crux (`atlas_crux_localization`).
    Nothing here asserts either side. -/
theorem coupledWeil_diag_pos_iff_genuine_coupling (E : StieltjesEta)
    (arch w : Nat → Real) (v : Nat → Nat → Real) (M : Nat)
    (hmatch : ∀ n, 0 < n →
      Req (coupledWeil arch w v M n n) (Rneg ((genuineSpectralSquare E).cSq n))) :
    (∀ n, 0 < n → Pos (coupledWeil arch w v M n n))
      ↔ (∀ n, 0 < n → Pos (Radd (genuineArithSeq E.eta n) (genuineArchSeq n))) :=
  Iff.trans (coupledWeil_diag_pos_iff_genuine_crux E arch w v M hmatch)
    (atlas_crux_localization E).2.1

end UOR.Bridge.F1Square.Square
