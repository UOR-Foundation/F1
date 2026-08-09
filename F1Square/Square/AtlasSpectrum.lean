/-
F1 square — v0.21.0 stage G, brick **G2b.1-sourced (the atlas spectral operator)**: the genuine
UOR-Atlas signature `Σ = {10, 2, 7, −1}`, now SOURCED and formalized, with its computed
spectrum/trace verified and its indefiniteness established.

The UOR Atlas (`uor-atlas.md`, §5/§6.6) defines the scale-invariant spectral operator
    `M = (O+2)·I − T·Π_T − O·Π_O`   on `V_T ⊗ V_O`,   `(T, O) = (3, 8)`,
with `Π_T, Π_O` the projections onto the nontrivial (imaginary) factors. Its spectrum is the block
eigenvalues `(O+2) − T·ε_T − O·ε_O` for `ε_T, ε_O ∈ {0,1}`:
    `{O+2, O−1, T−1, −1} = {10, 7, 2, −1}`   with multiplicities `{1, T−1, O−1, (T−1)(O−1)} = {1, 2, 7, 14}`.
The Atlas records this as a COMPUTED fact (not posited) and verifies `Σ mᵢ = 24 = T·O` (dimension)
and `Σ mᵢλᵢ = 24 = T·O` (trace). This brick reproduces both checks in F1, by `decide`.

WHY THIS MATTERS FOR THE CRUX. v0.21.0 §10 named `Σ = {10,2,7,−1}` the hypothesized atlas signature
that, IF it lands in the metric, makes Gate B's infinite limit indefinite — and flagged it "not yet
sourced from the atlas repo". It is now sourced: the Atlas's own §5 operator HAS the negative
eigenspace (`−1`, multiplicity 14, the largest). So `atlasM` is INDEFINITE (`atlasM_indefinite`,
via `not_WeilPSD_of_neg_diag`): the atlas spectral signature does NOT supply a positive-definite
metric for Gate B.

This is faithful to the Atlas, NOT a defect of it. The Atlas (§5) builds `M` as a BALANCED operator
whose negative space shapes the positivity invariant (`positive 38 − reflection 14 = T·O = 24`); its
genuinely DEFINITE object is the Hurwitz norm `|x|² = Σ xᵢ² > 0` (§9, a manifest sum of squares —
`WeilPSD_rankOne`), which the Atlas explicitly states is a DIFFERENT object from "the signed
quadratic form over the primes whose non-negativity is the Riemann Hypothesis" (§9: "the model does
not identify the two; on the evidence to date they are different"). The intersection-form / Hodge
positivity that the crux fields track is RH-equivalent and OPEN by the Atlas's own §11/§12/§15 —
exactly where this construction stands. So this brick CLOSES the atlas object's spectral facet and
leaves the crux fields `none`, mirroring the Atlas.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.GaugeTower
import F1Square.Square.AtlasSpectralCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

-- ===========================================================================
-- The integer spectral data (`atlasT`/`atlasO`/`blockEig`/`atlasEig`/`atlasTrace`), the computed
-- spectrum/trace/multiplicity/signature facts, and the diagonal metric `atlasM` now live in the
-- zeta/crux-free `AtlasSpectralCore` (imported above). This module adds ONLY the indefiniteness
-- results, which genuinely need the `WeilPSD` machinery from `GaugeTower`.
-- ===========================================================================

/-- The `−1` (reflection) eigenspace: `−⟨e₁₀, e₁₀⟩ = 1 > 0` — a strictly negative diagonal entry. -/
theorem atlasM_neg_entry : Pos (Rneg (atlasM 10 10)) := by
  have e : atlasM 10 10 = ofQ ⟨-1, 1⟩ Nat.one_pos := rfl
  rw [e]
  exact Pos_congr (Req_symm (Rneg_ofQ ⟨-1, 1⟩ Nat.one_pos)) Pos_one

/-- **THE SOURCED MAKE-OR-BREAK: the atlas spectral signature `Σ = {10,2,7,−1}` is INDEFINITE.**
    Its `−1` eigenspace (multiplicity 14) is a negative diagonal entry, so `atlasM` is not `WeilPSD`
    (`not_WeilPSD_of_neg_diag`). Per v0.21.0 §10, a negative signature entry in the metric makes
    Gate B's infinite limit indefinite — so the atlas spectral operator does NOT, by itself, supply
    the positive-definite limit Gate B needs. (Faithful to Atlas §5: `M` is balanced-with-negative-
    space by construction; the Atlas's definite object is the Hurwitz norm of §9, NOT identified
    with the RH form — so the crux stays `none`.) -/
theorem atlasM_indefinite : ¬ WeilPSD atlasM :=
  not_WeilPSD_of_neg_diag 10 atlasM_neg_entry

/-- **The atlas's DEFINITE object (Hurwitz norm, §9) is a sum of squares, hence `WeilPSD`** — a
    manifest, closed positivity, and a DIFFERENT object from the indefinite spectral form `atlasM`
    (Atlas §9: "the model does not identify the two; on the evidence to date they are different").
    The norm closes; the intersection-form/RH positivity (the crux) stays open. -/
theorem atlasNorm_psd (f : Nat → Real) : WeilPSD (fun i j => Rmul (f i) (f j)) :=
  WeilPSD_rankOne f

end UOR.Bridge.F1Square.Square
