/-
F1 square — Track 1: **conjugation algebra** — `Cconj` as a ring/limit homomorphism: congruence,
involution, distribution over `Cadd`/`Cneg`, fixing of reals, and commuting with the complex finite
sum `CsumN`.

These are the reusable componentwise/induction lemmas the *assembly* conjugations need — the
`CSpougeGammaW` Spouge bracket `c₀ + Σ cₖ/(s+k)` (a `CsumN`/`Cadd` of `Cinv` terms, toward the Γ-side
of `Cxi_conj`) and the `Ceta` block sums (the ζ-side). With `Cconj_Cmul` (`ComplexArgLower`),
`Cexp_conj`/`Cinv_conj` (`ComplexDigammaConj`), `Cpow_conj` (`ComplexLogConj`), and `Clim_Cconj`, this
completes the conjugation toolbox.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexSeries
import F1Square.Analysis.Reflection
import F1Square.Analysis.ComplexCore

namespace UOR.Bridge.F1Square.Analysis

-- `Cconj_congr`, `Cconj_Cconj`, `Cconj_Cadd`, `Cconj_Czero` now live in the zeta-free `ComplexCore`.

/-- **`Cconj` commutes with `Cneg`**: `conj(−z) = −conj z`. -/
theorem Cconj_Cneg (z : Complex) : Ceq (Cconj (Cneg z)) (Cneg (Cconj z)) :=
  ⟨Req_refl (Rneg z.re), Req_refl (Rneg (Rneg z.im))⟩

/-- **`Cconj` fixes the reals**: `conj(ofReal x) = ofReal x`. -/
theorem Cconj_ofReal (x : Real) : Ceq (Cconj (ofReal x)) (ofReal x) :=
  ⟨Req_refl x, Rneg_zero⟩

/-- **`Cconj` commutes with the complex finite sum**: `conj(Σ_{k<N} F k) = Σ_{k<N} conj(F k)`. The
    bridge for conjugating the Spouge bracket and the `Ceta` blocks. -/
theorem CsumN_Cconj (F : Nat → Complex) : ∀ N,
    Ceq (Cconj (CsumN F N)) (CsumN (fun n => Cconj (F n)) N)
  | 0 => Cconj_Czero
  | (n + 1) =>
      Ceq_trans (Cconj_Cadd (CsumN F n) (F n))
        (Cadd_congr (CsumN_Cconj F n) (Ceq_refl (Cconj (F n))))

end UOR.Bridge.F1Square.Analysis
