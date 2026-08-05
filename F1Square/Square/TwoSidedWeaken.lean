/-
F1 square — **two small schedule-plumbing lemmas for the `∫_t` reconstruction's common evaluation
schedule** (`TwoSidedWeaken.lean`):

- `two_sided_weaken`: a two-sided bound `−B ≤ x ≤ B` weakens to any larger bound `−B' ≤ x ≤ B'`
  (`Qle B B'`) — the tool that lifts `convTwTerm_two_sided` (at the convolution constant `K_conv`) to
  the common constant `K⋆`, so `genSum_RReg` produces the regularity at `K⋆`'s schedule.
- `Qle_self_toNat_add`: a nonnegative rational is `≤` the integer `⟨K.num.toNat + c, 1⟩` (`c ≥ 0`) —
  the `Qle K_conv K⋆` step feeding the weakening (`K⋆ = ⟨K_conv.num.toNat + (Cf·2ⁿ).num.toNat, 1⟩`).

HONEST SCOPE. Two general order lemmas (a Real two-sided weakening and a `Q` bound). No convolution,
no tail assembly, no covariance, no factorization, no positivity, no crux. Step 4 (band-coupling
positivity) is RH; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RealPow
import F1Square.Analysis.Pi

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **A two-sided bound weakens to any larger bound.** `−B ≤ x ≤ B` and `B ≤ B'` give `−B' ≤ x ≤ B'`
    (`ofQ` monotone both above and, negated, below). -/
theorem two_sided_weaken {x : Real} {B B' : Q} (hBd : 0 < B.den) (hB'd : 0 < B'.den)
    (hBB' : Qle B B') (h : Rle (Rneg (ofQ B hBd)) x ∧ Rle x (ofQ B hBd)) :
    Rle (Rneg (ofQ B' hB'd)) x ∧ Rle x (ofQ B' hB'd) :=
  ⟨Rle_trans (Rle_Rneg (Rle_ofQ_ofQ hBd hB'd hBB')) h.1,
   Rle_trans h.2 (Rle_ofQ_ofQ hBd hB'd hBB')⟩

/-- **A nonnegative rational is `≤` the integer `⟨K.num.toNat + c, 1⟩`** (`c ≥ 0`). Since `K.num ≥ 0`,
    `K.num ≤ K.num.toNat ≤ (K.num.toNat + c)·K.den`, which is exactly `Qle K ⟨K.num.toNat + c, 1⟩`. -/
theorem Qle_self_toNat_add {K : Q} (hKd : 0 < K.den) (hK0 : 0 ≤ K.num) (c : Int) (hc : 0 ≤ c) :
    Qle K (⟨(K.num.toNat : Int) + c, 1⟩ : Q) := by
  show K.num * (1 : Int) ≤ ((K.num.toNat : Int) + c) * (K.den : Int)
  have hden : (1 : Int) ≤ (K.den : Int) := by have := hKd; omega
  have htn : K.num ≤ (K.num.toNat : Int) := by omega
  have h1 : (K.num.toNat : Int) * 1 ≤ (K.num.toNat : Int) * (K.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hden (Int.ofNat_nonneg _)
  have h2 : (K.num.toNat : Int) * (K.den : Int) ≤ ((K.num.toNat : Int) + c) * (K.den : Int) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  omega

end UOR.Bridge.F1Square.Square
