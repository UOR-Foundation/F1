/-
F1 square — **the zeta/crux-free Atlas spectral core** (`AtlasSpectralCore.lean`). This is the
low-level substrate the Hilbert–Pólya operator is built on: the sourced integer spectral data of the
UOR-Atlas operator `M = (O+2)I − T·Π_T − O·Π_O` (Atlas §5/§6.6), with NO dependency on the crux-heavy
`WeilPSD`/`GaugeTower`/`E8Seed`/`Spectral` cone. It carries ONLY the block eigenvalue formula, the
computed spectrum/trace/multiplicity/signature facts (all by `decide`), and the diagonal metric
`atlasM` (which needs only the low-level real `ofQ`).

Extracted here so that the operator substrate `FinAtlasOperator` is DEMONSTRABLY zeta/crux-free again:
its cone is now `FinDirectLimit` (zeta-free metric) ⊕ this core (only `Analysis.Real`), with no path
to `ComplexZeta`, `GenuineLi`, `Spectral`, or `WeilPSD`. The `WeilPSD`-dependent indefiniteness
theorems (`atlasM_indefinite`, `atlasM_neg_entry`, `atlasNorm_psd`) stay in `AtlasSpectrum`, which now
imports this core.

The `−1` tail note: `atlasEig` is sourced only for the 24-dimensional carrier `i < T·O = 24`; its
value on `i ≥ 24` is a definitional artefact, NOT an unbounded Atlas spectrum (the operator layer
zeroes it — see `FinAtlasOperator.atlasObsEig`).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`. Crux fields `none`.
-/

import F1Square.Analysis.Real

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The atlas constants and the block eigenvalue formula M = (O+2)I − T·Π_T − O·Π_O.
-- ===========================================================================

/-- The minimal cyclic order `T = 3` (UOR Atlas §1). -/
def atlasT : Int := 3
/-- The maximal normed-division-algebra dimension `O = 8 = 2^T` (UOR Atlas §1). -/
def atlasO : Int := 8

/-- The block eigenvalue of `M = (O+2)I − T·Π_T − O·Π_O` on the `(ε_T, ε_O)` block
    (`ε = 0` trivial factor, `ε = 1` nontrivial/imaginary factor). -/
def blockEig (eT eO : Int) : Int := (atlasO + 2) - atlasT * eT - atlasO * eO

/-- The four block eigenvalues `{(0,0)↦10, (1,0)↦7, (0,1)↦2, (1,1)↦−1}` — the Atlas spectrum
    `{O+2, O−1, T−1, −1}`. Computed, not posited (Atlas §6.6). -/
theorem blockEig_spectrum :
    blockEig 0 0 = 10 ∧ blockEig 1 0 = 7 ∧ blockEig 0 1 = 2 ∧ blockEig 1 1 = -1 := by decide

/-- The eigenvalue at carrier index `i < T·O = 24`, laid out by block with the Atlas multiplicities:
    `i = 0` → `10` (mult 1); `i ∈ {1,2}` → `7` (mult `T−1 = 2`); `i ∈ {3..9}` → `2` (mult
    `O−1 = 7`); `i ∈ {10..23}` → `−1` (mult `(T−1)(O−1) = 14`). -/
def atlasEig : Nat → Int
  | 0 => blockEig 0 0
  | 1 => blockEig 1 0
  | 2 => blockEig 1 0
  | (n + 3) => if n < 7 then blockEig 0 1 else blockEig 1 1

-- ===========================================================================
-- The verified spectral facts (Atlas §6.6): dimension and trace both = T·O = 24.
-- ===========================================================================

/-- The trace `Σ_{i<24} λᵢ` of the atlas operator. -/
def atlasTrace : Int := ((List.range 24).map atlasEig).foldl (· + ·) 0

/-- **Trace = `T·O = 24`** (Atlas §6.6: `Σ mᵢλᵢ = 24`). Computed. -/
theorem atlasTrace_eq : atlasTrace = 24 := by decide

/-- **Multiplicities `{1, 2, 7, 14}`** over the 24-dimensional carrier (Atlas §5/§6.6), summing to
    `T·O = 24` (dimension). Computed. -/
theorem atlasMult :
    ((List.range 24).filter (fun i => atlasEig i == 10)).length = 1
    ∧ ((List.range 24).filter (fun i => atlasEig i == 7)).length = 2
    ∧ ((List.range 24).filter (fun i => atlasEig i == 2)).length = 7
    ∧ ((List.range 24).filter (fun i => atlasEig i == -1)).length = 14 := by decide

/-- The dimension of the carrier `V_T ⊗ V_O` is `T·O = 24`. -/
theorem atlasDim_eq : (List.range 24).length = 24 := by decide

/-- **THE ATLAS SPECTRAL SIGNATURE IS `(10, 14)`** — `10` positive eigendirections (`λ = 10, 7, 2`,
    multiplicities `1, 2, 7`) and `14` negative (`λ = −1`). Computed. This is a structural feature that
    distinguishes `atlasM` from the crux's intersection form: a Hodge-index / Lefschetz form has
    signature `(1, ρ−1)` — exactly ONE positive direction (`H² > 0`) and negative-definite on the
    primitive complement. `atlasM` has TEN positive directions, so it is a genuinely DIFFERENT
    indefinite object; the spectral operator alone cannot be the crux's intersection form (its definite
    companion is the Hurwitz norm §9, not the RH form). Crux fields stay `none`. -/
theorem atlasM_signature :
    ((List.range 24).filter (fun i => decide (0 < atlasEig i))).length = 10
    ∧ ((List.range 24).filter (fun i => decide (atlasEig i < 0))).length = 14 := by decide

/-- **`atlasM` is NOT of Hodge-index signature**: it has strictly more than one positive eigendirection
    (ten, `atlasM_signature`), whereas a Hodge-index form has exactly one. So the spectral operator is
    structurally distinct from the crux's intersection form — sharpening, as a theorem, why the
    spectral facet alone does not carry the crux. -/
theorem atlasM_not_hodge_signature :
    1 < ((List.range 24).filter (fun i => decide (0 < atlasEig i))).length := by
  rw [atlasM_signature.1]; decide

-- ===========================================================================
-- The operator as a diagonal metric over the carrier indices (low-level `ofQ` only).
-- ===========================================================================

/-- The atlas spectral operator as a diagonal metric over the carrier indices. Its indefiniteness
    (`atlasM_indefinite`, via the `−1` diagonal entry) is proved in `AtlasSpectrum`, which imports
    the `WeilPSD` machinery this core deliberately avoids. -/
def atlasM (i j : Nat) : Real := if i = j then ofQ ⟨atlasEig i, 1⟩ Nat.one_pos else zero

end UOR.Bridge.F1Square.Square
