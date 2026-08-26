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


-- ===========================================================================
-- (1) The source identities a positive stage would have to consume (all pointwise, all proved).
-- ===========================================================================

/-- **Pole cut = prime cycle** at the same scale: `A(posFiber U V) = (U + V)/4 = B(negFiber U V)`. -/
theorem pole_cut_eq_prime_cycle (U V : Real) : Req (aCoefGa one U (Rneg V)) (bCoefGa one U V) := by
  unfold aCoefGa bCoefGa
  exact Rmul_congr (Req_refl _) (Radd_congr (Req_refl _) (Rneg_neg V))

/-- **Pole cycle = prime cut** at the same scale: `B(posFiber U V) = (U − V)/4 = A(negFiber U V)` (definitional). -/
theorem pole_cycle_eq_prime_cut (U V : Real) : bCoefGa one U (Rneg V) = aCoefGa one U V := rfl

/-- The swap at the upper scale `n = m+1`: the pole fiber's cut coordinate at `x = n` IS the folded prime
    fiber's cycle coordinate (same field `U_n`, same `V`). -/
theorem poleFiber_cut_at_upR (C : NormCtx) (m : Nat) (f : L2Test) (t : Real) :
    Req (aCoefGa one (Uc C (upR m) f t) (Rneg (Vc C f t))) (bCoefGa one (Uc C (upR m) f t) (Vc C f t)) :=
  pole_cut_eq_prime_cycle _ _

/-- **The constant channel is PURE CYCLE**: `negFiber V V` has cut coordinate `0` and cycle coordinate `V/2`. -/
theorem negFiber_VV_cut_zero (V : Real) : Req (aCoefGa one V V) zero := by
  unfold aCoefGa
  exact Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Rsub_congr (Rone_mul V) (Req_refl _)) (Radd_neg V))) (Rmul_zero cQ)
theorem negFiber_VV_cycle (V : Real) : Req (bCoefGa one V V) (Rmul cH V) := by
  unfold bCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Radd_congr (Rone_mul V) (Req_refl _)) (Req_symm (cTwo_mul V)))) ?_
  refine Req_trans (Req_symm (Rmul_assoc cQ cTwo V)) (Rmul_congr ?_ (Req_refl V))
  exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))

-- The far channel is PURE CUT (`posFiber_VV_cycle_zero`, `posFiber_VV_cut`, `tailFiber_high_pure_cut`) and the
-- `V/2` anchor is reconstructed from pole/tail cut coordinates (`anchor_from_pole_tail_ge_one`), both in
-- `AtlasFibers`.  What is NOT available here is a measure-respecting coupling of the atomic `Λ(n)` samples
-- (the prime channel, one scale per place) to the continuous pole/tail/far densities in `x`: equal
-- coordinate values at `x = n` identify fibers, not measures.

end UOR.Bridge.F1Square.Square
