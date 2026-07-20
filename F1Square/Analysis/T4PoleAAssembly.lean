/-
F1 square — **the `t4PoleA` assembly, part 1** (`T4PoleAAssembly.lean`). Toward
`t4PoleA ≈ 9/4`: the first exact piece value and the `Gn 3` telescope.

    `t4A12 ≈ 1`  —  `∫₁² (2log2 − log x) dx = 2log2 − (Gn 2 − Gn 1) = 2log2 − (2log2 − 1) = 1`,
    the logs cancelling *inside a single piece* (`Gn 2`'s log term IS the cone height `t4H`,
    definitionally);

    `t4A23 + t4A34 ≈ (t4H + t4H) − (Gn 4 − Gn 2)` — the middle pieces telescope, so
    `Gn 3` (the only `log 3` carrier) drops out of the assembly without ever being
    expanded.

What remains for `≈ 9/4`: expand `Gn 4 − Gn 2` through `logN 4 ≈ 2·logN 2`
(`logN_mul_gen`), fold in `t4Ah`/`t4Aq`, and cancel the `log 2` coefficient
(`6 − 8 + 3/2 + 1/2 = 0`).

HONEST SCOPE. Exact identities between constructed integrals and `Gn` data; no slot
field, no positivity. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.T4PoleAPieces

namespace UOR.Bridge.F1Square.Analysis

/-- `a − (a − b) ≈ b` (the double-subtraction collapse). -/
private theorem ta_sub_sub_self (a b : Real) : Req (Rsub a (Rsub a b)) b := by
  refine Req_trans (Radd_congr (Req_refl a) (Rneg_Radd a (Rneg b))) ?_
  refine Req_trans (Radd_congr (Req_refl a)
    (Radd_congr (Req_refl (Rneg a)) (Rneg_neg b))) ?_
  refine Req_trans (Req_symm (Radd_assoc a (Rneg a) b)) ?_
  refine Req_trans (Radd_congr (Radd_neg a) (Req_refl b)) ?_
  exact Req_trans (Radd_comm zero b) (Radd_zero b)

/-- **`t4A12 ≈ 1` — the first exact piece value**: `∫₁² (2log2 − log x) dx = 1`. The
    cone height is `Gn 2`'s own log term, so the logs cancel inside the piece. -/
theorem t4A12_val : Req t4A12 one := by
  refine Req_trans t4A12_eq ?_
  -- `Gn 1 ≈ −1`, and `−(−1) ≈ 1`
  refine Req_trans (Rsub_congr (Req_refl t4H)
    (Radd_congr (Req_refl (Gn 2 (by omega)))
      (Req_trans (Rneg_congr Gn_one) (Rneg_neg one)))) ?_
  -- `t4H − (Gn 2 + 1) ≈ (t4H − Gn 2) − 1`
  refine Req_trans (Rsub_Radd_eq t4H (Gn 2 (by omega)) one) ?_
  -- `t4H − Gn 2 = t4H − (t4H − 2) ≈ 2`
  refine Req_trans (Rsub_congr
    (ta_sub_sub_self t4H (ofQ (⟨((2 : Nat) : Int), 1⟩ : Q) Nat.one_pos))
    (Req_refl one)) ?_
  -- `2 − 1 ≈ 1`
  refine Req_trans (Rsub_ofQ_ofQ Nat.one_pos (by decide)) ?_
  exact ofQ_congr (Qsub_den_pos Nat.one_pos (by decide)) (by decide) (by decide)

/-- **The middle-piece telescope**: `t4A23 + t4A34 ≈ (t4H + t4H) − (Gn 4 − Gn 2)` —
    `Gn 3`, the only `log 3` carrier in the assembly, drops out here and is never
    expanded. -/
theorem t4A2334_val : Req (Radd t4A23 t4A34)
    (Rsub (Radd t4H t4H) (Rsub (Gn 4 (by omega)) (Gn 2 (by omega)))) := by
  refine Req_trans (Radd_congr t4A23_eq t4A34_eq) ?_
  refine Req_trans (Req_symm (Rsub_Radd_Radd t4H t4H
    (Rsub (Gn 3 (by omega)) (Gn 2 (by omega)))
    (Rsub (Gn 4 (by omega)) (Gn 3 (by omega))))) ?_
  refine Rsub_congr (Req_refl (Radd t4H t4H)) ?_
  refine Req_trans (Radd_comm (Rsub (Gn 3 (by omega)) (Gn 2 (by omega)))
    (Rsub (Gn 4 (by omega)) (Gn 3 (by omega)))) ?_
  exact Rsub_telescope (Gn 4 (by omega)) (Gn 3 (by omega)) (Gn 2 (by omega))

end UOR.Bridge.F1Square.Analysis
