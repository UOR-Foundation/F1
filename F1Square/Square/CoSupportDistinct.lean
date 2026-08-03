/-
F1 square — **the pre-Hilbert layer, brick 84** (`CoSupportDistinct.lean`): **DISTINCT CO-SUPPORT
LEVELS ARE DISTINCT FUNCTIONS ON `[0,1]`** — the function-level upgrade of the moment-table
distinctness, again unlocked by the definiteness/metric iff (bricks 81–82).

The reusable bridge is: two tests whose *difference* carries a nonzero moment cannot agree
pointwise on `[0,1]`:

    `¬ Req (⟨φ−ψ, xⁿ⟩) 0`   ⟹   `¬ (∀ x ∈ [0,1], φ(x) ≈ ψ(x))`
      (`distinct_on_unit_of_moment_ne`).

The proof composes the metric iff (`dist2I_zero_iff_pointwise_eq`, brick 82) with the moment
bridge (`moments_zero_of_innerI_self_zero`, brick 63): if `φ` and `ψ` agreed on `[0,1]` then
`dist2I φ ψ = ⟨φ−ψ, φ−ψ⟩ ≈ 0`, which forces *every* moment of `φ−ψ` to vanish, contradicting the
one that does not.

Applied to the constructed filtration members: `deep3` (co-support level 3) and `deep4` (level 4)
differ already in their third moment — `⟨deep3, x³⟩ = −1/2520`, `⟨deep4, x³⟩ = 0`, so
`⟨deep3−deep4, x³⟩ = −1/2520 ≠ 0` — hence they are genuinely distinct **functions** on `[0,1]`
(`deep3_deep4_distinct_on_unit`). The same argument separates any two members whose moment tables
differ; the third-moment computation here is the template.

HONEST SCOPE. `¬ (∀ x ∈ [0,1], φ(x) ≈ ψ(x))` — "do not agree everywhere", the constructive negation
of pointwise agreement, NOT a constructed point of disagreement. This upgrades the moment-level
independence (`deep345_independent`) to a function-level distinctness statement, for the realized
members only. Nothing here touches the Weil form; the co-support skeleton's positivity is still
diagonal-multiplier level. Step 4 is RH. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.L2MetricIff
import F1Square.Square.CoSupportStrict
import F1Square.Square.DeepMemberFour

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **THE DISTINCTNESS BRIDGE**: two tests whose difference carries a nonzero moment do not agree
    pointwise on `[0,1]`. Metric iff (brick 82) + moment bridge (brick 63). -/
theorem distinct_on_unit_of_moment_ne (φ ψ : L2Test) (n : Nat)
    (hne : ¬ Req (mellinMoment (L2Test.sub φ ψ) n) zero) :
    ¬ (∀ x, Rle zero x → Rle x one → Req (φ.f x) (ψ.f x)) :=
  fun hall => hne (moments_zero_of_innerI_self_zero (L2Test.sub φ ψ)
    ((dist2I_zero_iff_pointwise_eq φ ψ).mpr hall) n)

/-- **`deep3` AND `deep4` ARE DISTINCT FUNCTIONS ON `[0,1]`** — they differ already in their third
    moment (`−1/2520` vs `0`), so the difference is a genuinely nonzero function there. -/
theorem deep3_deep4_distinct_on_unit :
    ¬ (∀ x, Rle zero x → Rle x one → Req (deep3.f x) (deep4.f x)) := by
  refine distinct_on_unit_of_moment_ne deep3 deep4 3 ?_
  intro hm
  have hval : Req (mellinMoment (L2Test.sub deep3 deep4) 3) (ofQ (⟨-1, 2520⟩ : Q) (by decide)) :=
    Req_trans (innerI_sub_left deep3 deep4 (powTest 3))
      (Req_trans (Rsub_congr deep3_moment_three deep4_moment_three) (Rsub_zero _))
  exact absurd ((Req_trans (Req_symm hval) hm) 5040) (by decide)

end UOR.Bridge.F1Square.Square
