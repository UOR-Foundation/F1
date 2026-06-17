/-
F1 square — **the Bombieri–Lagarias pipeline**: the constructive RH witness wired, end to end, to the
genuine Li sequence — the complete forward direction `RH ⟹ λₙ ≥ 0` as one kernel-checked artifact,
with the single classical input carried honestly as an explicit hypothesis (no axiom, no smuggling).

The witness (`RHWitness.lean`) proves the per-zero contribution `1 − Re((1−1/ρ)ⁿ)` is a manifest
non-negative when the zero's Cayley factor lies in the closed unit disk, and any finite sum of them is
`≥ 0` (`witnessSum_nonneg`). The reflection/symmetry bricks (`Reflection.lean`) pin "in the disk" to
"on the critical line". What was missing was the bridge to the ACTUAL coefficient `genuineLamSeq`: the
**Bombieri–Lagarias 1999 representation**, `λₙ = Σ_ρ (1 − Re((1−1/ρ)ⁿ))`, the limit of finite partial
witness sums over the nontrivial zeros.

THIS FILE supplies that bridge, honestly. `BLZeroSum` packages the two genuine classical facts as
hypotheses (a structure, NOT axioms):
- `onLine_unit` — under RH every enumerated zero's Cayley factor has unit modulus (`liRatio_on_line`
  transported through the Cayley map). A geometric fact about the zeros; it is NOT `λₙ ≥ 0`.
- `bl` — `[CLASSICAL, Bombieri–Lagarias 1999]` the genuine `λₙ` is the limit of the partial witness
  sums over the enumerated zeros. An EQUALITY (true regardless of RH); it does NOT assert any sign.

Neither field is the conclusion, so the pipeline is non-circular. The new CONSTRUCTIVE content is
`Rnonneg_Rlim` (non-negativity passes to a Bishop limit) plus the wiring: under RH every partial
witness sum is `≥ 0` (the witness), so their limit — `λₙ` — is `≥ 0`. The result
`bl_rh_implies_liNonneg : BLZeroSum E → AllZerosOnLine → LiNonneg (genuineLamSeq)` is axiom-clean
`{propext, Quot.sound}`: the classical content lives in the hypothesis `BLZeroSum`, visible to
`#print axioms`, and the RH content is the explicit `AllZerosOnLine`. Closing the crux would require
INHABITING `BLZeroSum` (classical, available) AND discharging `AllZerosOnLine` (RH, open) — so the
crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RHWitness
import F1Square.Analysis.Complete
import F1Square.Analysis.GenuineLi
import F1Square.Li

namespace UOR.Bridge.F1Square.Analysis

/-- **Non-negativity passes to a Bishop limit**: if every `X k ≥ 0` then `Rlim X h ≥ 0`. The limit's
    `n`-th approximant is `(X (4n+3)).seq (4n+3) ≥ −1/(4n+4) ≥ −1/(n+1)`, so the regularity floor is
    met at every index. The constructive core of the BL pipeline (a sum of non-negatives, taken to its
    convergent limit, stays non-negative). -/
theorem Rnonneg_Rlim {X : Nat → Real} (h : RReg X) (hX : ∀ k, Rnonneg (X k)) :
    Rnonneg (Rlim X h) := by
  intro n
  have hbc := hX (4 * n + 3) (4 * n + 3)
  have hbd : 0 < (neg (Qbound (4 * n + 3))).den := by show 0 < 4 * n + 3 + 1; omega
  have hab : Qle (neg (Qbound n)) (neg (Qbound (4 * n + 3))) := by
    simp only [Qle, neg, Qbound]; push_cast; omega
  rw [Rlim_seq]
  exact Qle_trans hbd hab hbc

end UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

/-- **The Bombieri–Lagarias zero-sum interface for the genuine Li sequence.** The two genuine
    classical facts, as explicit hypotheses (a structure, not axioms):

    * `zeroCayley k` — the Cayley factor `1 − 1/ρₖ` of the `k`-th enumerated nontrivial zero;
    * `onLine_unit` — under RH each has unit modulus (`liRatio_on_line` through the Cayley map);
    * `reg` / `bl` — `[CLASSICAL, Bombieri–Lagarias 1999]` `λₙ` is the (convergent) limit of the finite
      partial witness sums `Σ_{k<M} (1 − Re((zeroCayley k)ⁿ))` over the zeros.

    `bl` is an EQUALITY (no sign claim) and `onLine_unit` is a geometric fact — neither is `λₙ ≥ 0`,
    so deriving Li-nonnegativity from this interface is non-circular. -/
structure BLZeroSum (E : StieltjesEta) where
  /-- the nontrivial zero set (abstract; the genuine analytic object) -/
  isZero : Complex → Prop
  /-- the Cayley factor `1 − 1/ρₖ` of the `k`-th enumerated zero -/
  zeroCayley : Nat → Complex
  /-- under RH every enumerated Cayley factor has unit modulus (`liRatio_on_line`, transported) -/
  onLine_unit : AllZerosOnLine isZero → ∀ k, Req (cnormSq (zeroCayley k)) one
  /-- the partial witness sums converge (BL convergence) -/
  reg : ∀ n, RReg (fun M => witnessSum ((List.range M).map zeroCayley) n)
  /-- `[CLASSICAL, Bombieri–Lagarias 1999]`: `λₙ` is the limit of the partial zero witness sums -/
  bl : ∀ n, 0 < n →
    Req (genuineLamSeq E.eta n)
        (Rlim (fun M => witnessSum ((List.range M).map zeroCayley) n) (reg n))

/-- **THE FORWARD DIRECTION, CONSTRUCTIVELY, END TO END**: `RH ⟹ λₙ ≥ 0` for the genuine Li sequence.
    Under `AllZerosOnLine`, every enumerated Cayley factor has unit modulus (`onLine_unit`), so each is
    in the closed disk and every finite partial witness sum is `≥ 0` (`witnessSum_nonneg`); the limit
    is `≥ 0` (`Rnonneg_Rlim`); and `λₙ` IS that limit (`bl`). The classical Bombieri–Lagarias content
    is the hypothesis `BLZeroSum` (visible to `#print axioms`, not an axiom); the RH content is the
    explicit `AllZerosOnLine`. Axiom-clean; the crux fields stay `none` (inhabiting `BLZeroSum` is
    classical, discharging `AllZerosOnLine` is RH). -/
theorem bl_rh_implies_liNonneg (E : StieltjesEta) (B : BLZeroSum E)
    (hRH : AllZerosOnLine B.isZero) : LiNonneg (genuineLamSeq E.eta) := by
  intro n hn
  have hunit := B.onLine_unit hRH
  have hpart : ∀ M, Rnonneg (witnessSum ((List.range M).map B.zeroCayley) n) := by
    intro M
    refine witnessSum_nonneg _ n ?_
    intro w hw
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hw
    exact Rle_of_Req (hk ▸ hunit k)
  have hlim : Rnonneg
      (Rlim (fun M => witnessSum ((List.range M).map B.zeroCayley) n) (B.reg n)) :=
    Rnonneg_Rlim (B.reg n) hpart
  exact Rnonneg_congr (Req_symm (B.bl n hn)) hlim

end UOR.Bridge.F1Square.Square
