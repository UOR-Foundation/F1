/-
F1 square — **Hilbert–Pólya contract: the FINITE APPROXIMANT / finite evidence** (task-7 finite
discharge). This module connects the abstract operator contract (`HilbertPolyaSpec`) to the
repository's *proved* finite self-adjoint machinery (`applyN`, `SymKernel`, `applyN_self_adjoint`,
`innerN`), and discharges **only** the finite symmetry rung of the operator ladder.

WHAT THIS IS. `finiteHP B N` is a concrete `HilbertPolyaSpec` bundle: carrier the coordinate vectors
`ℕ → ℝ`, inner product the finite `⟨·,·⟩_N`, operator the finite symmetric-matrix action
`applyN B · N`. For a symmetric kernel `B` it satisfies the contract's `Symmetric` obligation at each
truncation `N` — that is the theorem `finiteHP_symmetric`, a repackaging of `applyN_self_adjoint`.

WHAT THIS IS NOT. A FINITE symmetry/approximation result discharges **only** the finite obligation. It
does NOT discharge: `IsDense`, `Closable`, `Closed`, `AdjointDomainEq`, `SelfAdjoint` (the `N → ∞` /
adjoint-domain content), `HasSelfAdjointGenerator` (Stone), `TraceFormula`, or any spectral/zero
obligation. Those rungs of the ladder remain OPEN. A finite symmetric matrix is not a self-adjoint
unbounded operator; coordinatewise/finite-`N` symmetry is not essential self-adjointness.

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

/-- A concrete FINITE Hilbert–Pólya bundle from a kernel `B` truncated at `N`: carrier `ℕ → ℝ`, inner
    product the finite `⟨x, y⟩_N = Σ_{i<N} xᵢ yᵢ`, operator and formal adjoint the finite matrix
    action `applyN B · N`. This is the finite APPROXIMANT of a would-be Hilbert–Pólya operator; it
    realizes only the finite obligations. -/
def finiteHP (B : Nat → Nat → Real) (N : Nat) : HilbertPolyaSpec where
  H := Nat → Real
  inner := fun x y => innerN x y N
  dom := fun _ => True
  op := fun c => applyN B c N
  adj := fun c => applyN B c N

/-- **PROVED (FINITE) — the finite approximant discharges the finite `Symmetric` obligation.** For a
    symmetric kernel `B` (`SymKernel B`), `Symmetric (finiteHP B N)` holds at each truncation `N`:
    `⟨applyN B x, y⟩_N = ⟨x, applyN B y⟩_N` (`applyN_self_adjoint`). This is the single finite rung of
    the operator ladder that is dischargeable today; every infinite rung (density, closability,
    closedness, adjoint-domain equality, self-adjointness, Stone generator, trace, spectral inclusion,
    completeness) remains OPEN. A finite symmetry result, NOT self-adjointness. -/
theorem finiteHP_symmetric (B : Nat → Nat → Real) (hB : SymKernel B) (N : Nat) :
    Symmetric (finiteHP B N) := by
  intro x y _ _
  show Req (innerN (applyN B x N) y N) (innerN x (applyN B y N) N)
  exact applyN_self_adjoint hB x y N

end UOR.Bridge.F1Square.Square
