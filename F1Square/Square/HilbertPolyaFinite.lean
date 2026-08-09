/-
F1 square — **Hilbert–Pólya contract: the FINITE APPROXIMANT / finite evidence** (task-7 finite
discharge). This module connects the abstract operator contract (`HilbertPolyaSpec`) to the
repository's *proved* finite self-adjoint machinery (`applyN`, `SymKernel`, `applyN_self_adjoint`,
`innerN`), and discharges **only** the finite symmetry rung of the operator ladder.

WHAT THIS IS — AND THE NAME'S OVERCLAIM. `finiteHP B N` is a `HilbertPolyaSpec` bundle whose carrier is
the FULL, INFINITE space `ℕ → ℝ` (NOT finite-dimensional — only the inner product `⟨·,·⟩_N` and the
operator `applyN B · N` are truncated at `N`), with `adj := op` STIPULATED (not derived). So the name
`finiteHP` overclaims twice: it is not finite (infinite carrier) and it is not a Hilbert–Pólya operator
(no self-adjointness is proved, `adj` is assumed). The ONE genuine fact is `finiteHP_symmetric`: a
prefix-kernel symmetry `⟨applyN B x, y⟩_N = ⟨x, applyN B y⟩_N` at truncation `N` (`applyN_self_adjoint`).
It is NOT derived from any Atlas structure — `B` is an arbitrary symmetric kernel supplied by the caller.

WHAT THIS IS NOT. A prefix-kernel symmetry at truncation `N` discharges **only** the finite symmetry
equation. It does NOT discharge: `NominalDense`, `NominalClosable`, `NominalClosed`,
`NominalAdjointDomainEq`, `NominalSelfAdjoint` (the `N → ∞` / adjoint-domain content — and recall
`NominalSelfAdjoint` is itself vacuous on this axiom-free bundle, `zeroBundle_NominalSelfAdjoint`),
`NominalHasSelfAdjointGenerator` (Stone), `NominalTraceFormula`, or any spectral/zero
obligation. Those rungs remain OPEN. A symmetric kernel truncated at `N`, on an infinite carrier with a
stipulated adjoint, is not a self-adjoint unbounded operator; finite-`N` symmetry is not essential
self-adjointness, and none of this is Atlas-derived.

NOTE ON THE FENCE. Unlike `HilbertPolyaSpec` (the ζ-free construction layer), this evidence module
imports the finite-symmetric machinery, which is file-level ζ-tainted (`SelfAdjoint → … → GenuineLi`).
That is why it is a SEPARATE, clearly-labelled finite-evidence module, not part of the ζ-free contract.

STATUS: finite symmetry — PROVED (finite); all infinite/spectral rungs — OPEN. Crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.HilbertPolyaSpec
import F1Square.Square.SelfAdjoint

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- A `HilbertPolyaSpec` bundle from a kernel `B` truncated at `N`: carrier the INFINITE `ℕ → ℝ`, inner
    product the finite `⟨x, y⟩_N = Σ_{i<N} xᵢ yᵢ`, operator the truncated action `applyN B · N`, and
    adjoint STIPULATED equal to it (`adj := op`). NAME CAVEAT: not finite (infinite carrier), not a
    Hilbert–Pólya operator (no self-adjointness proved). Its only genuine content is the prefix-kernel
    symmetry `finiteHP_symmetric`. -/
def finiteHP (B : Nat → Nat → Real) (N : Nat) : HilbertPolyaSpec where
  H := Nat → Real
  inner := fun x y => innerN x y N
  dom := fun _ => True
  op := fun c => applyN B c N
  adj := fun c => applyN B c N

/-- **PROVED (FINITE) — the finite approximant discharges the finite `Symmetric` obligation.** For a
    symmetric kernel `B` (`SymKernel B`), `NominalSymmetric (finiteHP B N)` holds at each truncation `N`:
    `⟨applyN B x, y⟩_N = ⟨x, applyN B y⟩_N` (`applyN_self_adjoint`). This is the single finite rung of
    the operator ladder that is dischargeable today; every infinite rung (density, closability,
    closedness, adjoint-domain equality, self-adjointness, Stone generator, trace, spectral inclusion,
    completeness) remains OPEN. A finite symmetry result, NOT self-adjointness. -/
theorem finiteHP_symmetric (B : Nat → Nat → Real) (hB : SymKernel B) (N : Nat) :
    NominalSymmetric (finiteHP B N) := by
  intro x y _ _
  show Req (innerN (applyN B x N) y N) (innerN x (applyN B y N) N)
  exact applyN_self_adjoint hB x y N

end UOR.Bridge.F1Square.Square
