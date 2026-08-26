/-
F1 square — **THE SOURCE-DEFINED ATLAS DEFECT GRAM** (`AtlasDefectGram.lean`, AC-22 item 3, target-free).

    `atlasDefectGram_k(f,g) = poleGram(f,g) + primeFoldGram(f,g) + constGram(f,g) + tailGram_k(f,g)`

— the sum of the four channel integrals of the pointwise Atlas pairing `density·⟨Φ_f, MΦ_g⟩`, every
channel with an explicit NONNEGATIVE sourced density (`2(1+1/x)wr`, `2Λ(n)wr`, `(log 4π + γ)wr`, `2wr`),
test-INDEPENDENT indices (the scale `x ∈ [1,B]`, the place `m < X`, the window variable `t`, the fixed
`3 × 8` Atlas address), and single-test-LINEAR coordinates from the coherent scale field
(`U_x(f,t)`, `V(f,t)`, `D_x(f,t)`, `Z_x = xK_k(x)D_x`, `W_x = x^{-1}V`).  It is defined here from the source
field alone: this module's transitive cone contains neither `closedWeilBilin`, nor `CoupledForm`, nor the
dominance predicate (`WeilGeom` is the neutral base).  The identification with the compact coupled form,
`atlasCompactCoupled = atlasDefectGram` for all pairs of core tests, is `atlasDefect_readback`
(`AtlasDefectReadback.lean`).

HONEST SCOPE.  `⟨·, M·⟩` is the INDEFINITE Atlas pairing (`M = BᵀB − I`); each fiber pairing splits pointwise
as `4A_fA_g − 4B_fB_g` (`negFiber_split`), so `atlasDefectGram` is a difference of two positive Grams, not a
manifest sum of squares.  `atlasDefectGram_diag_nonneg` is NOT proved here and is NOT claimed anywhere:
by `atlasDefect_nonneg_imp_dominance` its universal diagonal nonnegativity implies
`CurrentArchDominatesPrime` (= positivity of the closed Weil form on the core), i.e. it IS the crux.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasArchGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **★ THE ATLAS DEFECT GRAM** at truncation `k ≥ 1`: pole + folded prime + constant + compact tail. -/
def atlasDefectGram (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : L2Test) : Real :=
  Radd (Radd (Radd (poleGram C f g) (primeFoldGram C f g)) (constGram C f g)) (tailGram C k hk f g)

end UOR.Bridge.F1Square.Square
