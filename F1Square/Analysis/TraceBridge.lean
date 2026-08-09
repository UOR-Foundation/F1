/-
F1 square — Track 1, the **trace bridge**: the ARITH+ARCH-COMPLETE explicit-formula identity,
carried as a single labelled UNDISCHARGED seam, connecting the zero-moment side of `λₙ` to the FULL
constructed closed form `genuineLamSeq = genuineArithSeq + genuineArchSeq`. Nothing here is asserted
for the genuine zeros; the identity is a reduction around a hypothesis, not an established theorem.

WHAT THIS IS. The Bombieri–Lagarias zero-sum `witnessSum(zeroCayley) n = Σ_ρ (1 − Re((1−1/ρ)ⁿ))`
was already decomposed, by pure algebra, into per-order reciprocal moments
`= −Σ_{k=1}^{n} Re(M_k)`, `M_k = Σ_ρ C(n,k)(−1/ρ)ᵏ` (`witnessSum_moment_order`,
`ComplexBinomial.lean`). The classical **explicit formula** identifies that zero-moment sum with the
computable analytic data — and, crucially, that data has TWO places: the `−ζ′/ζ` Taylor coefficients
`ηⱼ` (the ARITHMETIC / prime side, `genuineArithSeq`) AND the Γ-factor / pole / trivial-zero
contribution (the ARCHIMEDEAN side, `genuineArchSeq`). Both closed forms are already built in this
substrate for every `n`. This module states the trace identity as a single labelled seam over BOTH
places and derives, constructively and only UNDER that seam, that the zero-sum equals the full `λₙ`.

WHY THIS SUPERSEDES `MomentEta.witnessSum_eq_genuineArith`. That earlier shape-match equated the
zero-moment sum with `genuineArithSeq` ALONE, under an arith-only per-order seam. Its own honesty
note records that this seam is *false* for the genuine zeros: `genuineArithSeq` is only a summand of
`λₙ` (e.g. `λ₁^{arith} = γ ≈ 0.577` vs the full `λ₁ ≈ 0.023`), while the zero-sum limit is the FULL
`λₙ`. The trace bridge here carries the archimedean place too, so its seam is the genuine (classical,
UNCONDITIONAL — the explicit formula holds regardless of RH) identity, not a stand-in that omits a
place. Positivity of the resulting `λₙ` is the RH content and is untouched here.

THE SEAM, EXACTLY. `traceSeam` asserts the real part of the total reciprocal-moment sum equals the
built closed-form combination `arithTail − genuineArchSeq` at level `n`:

    `Re(Σ_{k=1}^n M_k)  =  (Σ_{j=1}^n C(n,j) η_{j−1})  −  λₙ^{∞}`.

Rearranged, `−Re(Σ M_k) = −Σ C(n,j)η_{j−1} + λₙ^{∞} = genuineArithSeq + genuineArchSeq = genuineLamSeq`,
which is exactly the zero-sum by `witnessSum_moment_order`. So the seam is the per-level
explicit-formula identity for a given (finite) zero-enumeration — with the enumeration and its
symmetric convergence to ALL zeros carried by the companion `conv`/`factored`/`bl` seams, not here —
split across the two places; everything else in this module is `Radd`/`Rneg` bookkeeping, discharged
constructively.

THE `n = 1` ANCHOR — the classical secondary constant. At `n = 1` the seam reads (for the genuine
moments `u = 1/ρ`)

    `Σ_ρ Re(1/ρ)  =  1 + γ/2 − ½ log(4π)`,

the famous first Keiper–Li / Bombieri–Lagarias secondary constant `σ₁ = Σ_ρ 1/ρ`. `traceBridge_one`
shows the bridge at `n = 1` lands on the independently-certified `Rlambda1` (through `genuineLam_one`)
— a genuine reconciliation of the zero side with the built `λ₁`, not a restatement.

WHAT IS NOT DONE. The seam is the classical explicit formula and is NOT discharged (it needs the
Hadamard factorization / Riemann–von Mangoldt zero-counting for the LHS zero enumeration — the same
analytic input carried as the `conv`/`factored` seams of `HadamardXi` and the `bl` seam of
`BLZeroSum`). Discharging it would make the `bl` reduction genuine, but would still leave positivity
(= RH) open. The crux fields stay `none`; RH is open.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexBinomial
import F1Square.Analysis.GenuineLi

namespace UOR.Bridge.F1Square.Analysis

/-- **The trace-bridge identity (arith+arch-complete), given the explicit-formula seam.** For a list
    of reciprocal moments `us = {1/ρ}` and the level `n`, the Bombieri–Lagarias zero-sum over the
    Cayley factors `1 − u` equals the FULL constructed Li value `genuineLamSeq = genuineArithSeq +
    genuineArchSeq` — provided the single labelled seam `traceSeam` (the classical explicit formula,
    both places) holds:

      `Re(Σ_{k=1}^n M_k) = (Σ_{j=1}^n C(n,j) η_{j−1}) − λₙ^{∞}`.

    Proof: `witnessSum_moment_order` gives the zero-sum as `−Re(Σ M_k)`; rewrite by the seam and push
    the negation through `Radd`/`Rneg` (`Rneg_Radd`, `Rneg_neg`) to reach
    `Radd (Rneg (arithTail …)) (genuineArchSeq …) = genuineLamSeq` (definitionally). This is the honest
    arith+arch correction of `witnessSum_eq_genuineArith`: the seam here carries the archimedean place
    that the earlier arith-only seam omitted, so it is the genuine (unconditional) identity rather than
    a false stand-in. Positivity of the value is RH and is not addressed. -/
theorem witnessSum_eq_genuineLam (E : StieltjesEta) (us : List Complex) (n : Nat)
    (traceSeam : Req (CsumN (fun k => momentList us n k) n).re
                     (Radd (arithTail E.eta n n) (Rneg (genuineArchSeq n)))) :
    Req (witnessSum (us.map (fun u => Cadd Cone (Cneg u))) n) (genuineLamSeq E.eta n) := by
  refine Req_trans (witnessSum_moment_order n us) ?_
  show Req (Rneg (CsumN (fun k => momentList us n k) n).re) (genuineLamSeq E.eta n)
  refine Req_trans (Rneg_congr traceSeam) ?_
  refine Req_trans (Rneg_Radd (arithTail E.eta n n) (Rneg (genuineArchSeq n))) ?_
  exact Radd_congr (Req_refl _) (Rneg_neg (genuineArchSeq n))

/-- **The `n = 1` anchor — the trace bridge reproduces the certified `λ₁`, and its seam is the
    classical secondary constant `σ₁`.** Under the level-1 explicit-formula seam, the zero-sum at
    `n = 1` equals `Rlambda1` (via `witnessSum_eq_genuineLam` chained through `genuineLam_one`). At
    this level the seam unwinds, for the genuine moments `u = 1/ρ`, to
    `Σ_ρ Re(1/ρ) = 1 + γ/2 − ½ log(4π)` — the first Keiper–Li / Bombieri–Lagarias secondary constant
    `σ₁ = Σ_ρ 1/ρ`. So the bridge lands the zero side exactly on the independently-built `λ₁`, a real
    reconciliation of the two constructions. The seam itself (the σ₁ identity) is classical and not
    discharged; RH is untouched. -/
theorem traceBridge_one (E : StieltjesEta) (us : List Complex)
    (traceSeam : Req (CsumN (fun k => momentList us 1 k) 1).re
                     (Radd (arithTail E.eta 1 1) (Rneg (genuineArchSeq 1)))) :
    Req (witnessSum (us.map (fun u => Cadd Cone (Cneg u))) 1) Rlambda1 :=
  Req_trans (witnessSum_eq_genuineLam E us 1 traceSeam) (genuineLam_one E)

end UOR.Bridge.F1Square.Analysis
