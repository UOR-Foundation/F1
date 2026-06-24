/-
F1 square — Track 1, item 3 substrate: the **Jacobi-theta Lipschitz bound** on `[1, ∞)`, the modulus
of continuity the Mellin integrand `t^{σ−1}·ψ(t)` needs to enter the certified-integration framework.

The per-term step `|e^{−aₘs} − e^{−aₘt}| ≤ rₘ·|s−t|` would normally need a case split on `s ≤ t` vs
`t ≤ s` (which constructively is undecidable). The **RmaxZero trick** removes it: the order-free bound

  `1 − e^{−z} ≤ 4·max(z, 0)`  for ALL real `z`

(here, via `1 − e^{−z} ≤ 1 − e^{−max(z,0)} ≤ 4·max(z,0)`, monotone in the exponent + the global
`RexpReal_one_sub_neg_le_global` on the nonneg argument `max(z,0)`) is symmetric enough that the signed
per-term difference factors through `max` with no dichotomy.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ThetaValueDecay
import F1Square.Analysis.ExpVarGlobal
import F1Square.Analysis.ClampOne

namespace UOR.Bridge.F1Square.Analysis

/-- `z ≤ max(z, 0)` (the tent dominates its argument). -/
theorem Rle_RmaxZero_self (z : Real) : Rle z (RmaxZero z) := by
  show Rle z (Rhalf (Radd z (Rabs z)))
  exact Rle_trans (Rle_of_Req (Req_symm (Rhalf_add_self z)))
    (Rhalf_le_Rhalf (Radd_le_add (Rle_refl z) (Rle_Rabs_self z)))

/-- `max(z, 0) ≤ |z|` (the tent is dominated by the absolute value). -/
theorem RmaxZero_le_Rabs (z : Real) : Rle (RmaxZero z) (Rabs z) := by
  show Rle (Rhalf (Radd z (Rabs z))) (Rabs z)
  exact Rle_trans (Rhalf_le_Rhalf (Radd_le_add (Rle_Rabs_self z) (Rle_refl (Rabs z))))
    (Rle_of_Req (Rhalf_add_self (Rabs z)))

/-- **Order-free global exp variation** `1 − e^{−z} ≤ 4·max(z, 0)` for EVERY real `z` (no `z ≥ 0`).
    `1 − e^{−z} ≤ 1 − e^{−max(z,0)}` (since `max(z,0) ≥ z` ⟹ `e^{−max(z,0)} ≤ e^{−z}`), and the latter
    is `≤ 4·max(z,0)` by the nonneg-argument bound. The `max` makes the signed per-term theta difference
    boundable without a real case split. -/
theorem RexpReal_one_sub_neg_le_maxZero (z : Real) :
    Rle (Rsub one (RexpReal (Rneg z))) (Rmul (ofQ (⟨4, 1⟩ : Q) (by decide)) (RmaxZero z)) := by
  have hexp : Rle (RexpReal (Rneg (RmaxZero z))) (RexpReal (Rneg z)) :=
    RexpReal_le_of_le (Rle_Rneg (Rle_RmaxZero_self z))
  have hsub : Rle (Rsub one (RexpReal (Rneg z))) (Rsub one (RexpReal (Rneg (RmaxZero z)))) :=
    Radd_le_add (Rle_refl one) (Rle_Rneg hexp)
  exact Rle_trans hsub (RexpReal_one_sub_neg_le_global (Rnonneg_RmaxZero z))

end UOR.Bridge.F1Square.Analysis
