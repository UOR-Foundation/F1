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

-- ===========================================================================
-- The Keiper–Li binomial-transform structure of the zero side: the level-`n`
-- moment factors as (binomial coefficient) × (n-independent secondary constant).
-- ===========================================================================

/-- Four-term interchange `(a + b) + (p + q) ≈ (a + p) + (b + q)`, from `Cadd` assoc/comm. -/
private theorem regroup4 (a b p q : Complex) :
    Ceq (Cadd (Cadd a b) (Cadd p q)) (Cadd (Cadd a p) (Cadd b q)) :=
  Ceq_trans (Cadd_assoc a b (Cadd p q))
    (Ceq_trans (Cadd_congr (Ceq_refl a)
        (Ceq_trans (Ceq_symm (Cadd_assoc b p q))
          (Cadd_congr (Cadd_comm b p) (Ceq_refl q))))
      (Ceq_trans (Cadd_congr (Ceq_refl a) (Cadd_assoc p b q))
        (Ceq_symm (Cadd_assoc a p (Cadd b q)))))

/-- A fixed scalar distributes over a complex sum: `c·(a + b) ≈ c·a + c·b` (the complex-argument
    additivity of `Cnsmul`, complementary to `Cnsmul_add`'s scalar additivity). -/
private theorem Cnsmul_Cadd (c : Nat) (a b : Complex) :
    Ceq (Cnsmul c (Cadd a b)) (Cadd (Cnsmul c a) (Cnsmul c b)) := by
  induction c with
  | zero => exact Ceq_symm (cadd_zero Czero)
  | succ c ih =>
      refine Ceq_trans (Cadd_congr (Ceq_refl (Cadd a b)) ih) ?_
      exact regroup4 a b (Cnsmul c a) (Cnsmul c b)

/-- `c · 0 ≈ 0`. -/
private theorem Cnsmul_czero : ∀ c, Ceq (Cnsmul c Czero) Czero
  | 0 => Ceq_refl Czero
  | (c + 1) => Ceq_trans (czero_cadd (Cnsmul c Czero)) (Cnsmul_czero c)

/-- The `n`-INDEPENDENT signed `k`-th reciprocal power sum `σ*_k = Σ_{u∈us} (−u)ᵏ`
    (`= Σ_ρ (−1/ρ)ᵏ` for the zero moments `u = 1/ρ`); it carries no `n`, and the level-`n` moments
    are its binomial multiples (`momentList_eq_binom_powerSum`). It is `(−1)ᵏ` times the classical
    Keiper–Li secondary constant `σ_k = Σ_ρ ρ^{−k}`, so — MIND THE SIGN — its real part at `k = 1`
    is `Re σ*₁ = −Σ_ρ Re(1/ρ) = −(1 + γ/2 − ½ log 4π) ≈ −0.0231`, the NEGATION of the classical
    `σ₁`; the outer `Rneg` in `witnessSum_eq_binom_powerSum` restores the positive `λ`. -/
def powerSumList : List Complex → Nat → Complex
  | [], _ => Czero
  | (u :: rest), k => Cadd (Cnpow (Cneg u) k) (powerSumList rest k)

/-- **THE KEIPER–LI BINOMIAL TRANSFORM** — the level-`n` reciprocal moment factors as the binomial
    coefficient times the `n`-independent secondary constant:

      `M_k = Σ_ρ C(n,k+1)(−1/ρ)^{k+1} = C(n,k+1) · σ*_{k+1}`,  `σ*_j = Σ_ρ (−1/ρ)ʲ` (`powerSumList`).

    So ALL the `n`-dependence of the zero side sits in the binomial coefficients `C(n,k+1)`, and the
    signed secondary constants `σ*_j = (−1)ʲ σ_j` are fixed — exactly the structure of the classical
    Li/Keiper explicit formula (each `λₙ` a binomial transform of the fixed `σ*_j`). This is what
    makes the trace-bridge seam an infinite family of `n`-uniform statements `Re σ*_j = (closed form)`
    rather than a separate fact per `n`. Pure algebra: `Cnsmul` linearity over the list sum. No seam,
    no RH. -/
theorem momentList_eq_binom_powerSum (n k : Nat) : ∀ us : List Complex,
    Ceq (momentList us n k) (Cnsmul (choose n (k + 1)) (powerSumList us (k + 1)))
  | [] => Ceq_symm (Cnsmul_czero (choose n (k + 1)))
  | (u :: rest) =>
      Ceq_trans
        (Cadd_congr (Ceq_refl (binTermC (Cneg u) n (k + 1)))
          (momentList_eq_binom_powerSum n k rest))
        (Ceq_symm (Cnsmul_Cadd (choose n (k + 1)) (Cnpow (Cneg u) (k + 1))
          (powerSumList rest (k + 1))))

/-- `nsmulR (c+1) x ≈ x + nsmulR c x` (the `1`-special-cased `nsmulR` recursion, put in add-front
    form; both cases close by `Radd_comm`/`Radd_zero`). -/
private theorem nsmulR_succ_comm :
    ∀ (c : Nat) (x : Real), Req (nsmulR (c + 1) x) (Radd x (nsmulR c x))
  | 0, x => Req_symm (Radd_zero x)
  | (c + 1), x => Radd_comm (nsmulR (c + 1) x) x

/-- The real part of an `n`-fold complex sum is the `n`-fold real sum of the real part:
    `Re (c · z) = c · Re z` (bridging `Cnsmul` to the arith side's `nsmulR`). -/
private theorem Cnsmul_re : ∀ (c : Nat) (z : Complex), Req (Cnsmul c z).re (nsmulR c z.re)
  | 0, _ => Req_refl zero
  | (c + 1), z =>
      Req_trans (Radd_congr (Req_refl z.re) (Cnsmul_re c z))
        (Req_symm (nsmulR_succ_comm c z.re))

/-- **THE ZERO-SUM AS A BINOMIAL TRANSFORM OF THE FIXED REAL SECONDARY CONSTANTS.** Combining
    `witnessSum_moment_order`, the Keiper–Li factoring `momentList_eq_binom_powerSum`, and the
    real-part bridges, the Bombieri–Lagarias zero-sum is *literally* the binomial transform of the
    `n`-independent fixed reals `Re σ*_j = Re (powerSumList us j)`:

      `witnessSum(zeroCayley) n = − Σ_{k=1}^{n} C(n,k) · Re σ*_k`.

    Every quantity on the right except the binomial coefficients is `n`-independent. So the ENTIRE
    trace bridge, at every `n` at once, rests on the fixed real numbers `Re σ*_j = (−1)ʲ Re σ_j`
    (`σ_j = Σ_ρ ρ^{−j}` the classical Keiper–Li secondary constants). MIND THE SIGN: at `j = 1`,
    `Re σ*₁ = −(1 + γ/2 − ½ log 4π) ≈ −0.0231`, and the outer `Rneg` makes `n = 1` land on `+λ₁`
    (the anchor). Evaluating those `Re σ*_j` against the built `η`/`ζ`/`γ`/`log 4π` closed forms is
    exactly the undischarged explicit-formula seam (it needs the symmetric zero enumeration); this
    theorem localizes the seam to that fixed sequence and is itself pure algebra — no seam, no RH. -/
theorem witnessSum_eq_binom_powerSum (us : List Complex) (n : Nat) :
    Req (witnessSum (us.map (fun u => Cadd Cone (Cneg u))) n)
        (Rneg (RsumN (fun k => nsmulR (choose n (k + 1)) (powerSumList us (k + 1)).re) n)) := by
  refine Req_trans (witnessSum_moment_order n us) ?_
  apply Rneg_congr
  refine Req_trans
    (CsumN_congr_le (fun k _ => momentList_eq_binom_powerSum n k us)).1 ?_
  rw [CsumN_re]
  exact RsumN_congr n (fun k _ => Cnsmul_re (choose n (k + 1)) (powerSumList us (k + 1)))

end UOR.Bridge.F1Square.Analysis
