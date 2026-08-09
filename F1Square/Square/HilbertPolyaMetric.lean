/-
F1 square — task-4 substrate: the **positive-definite metric** `posForm` for the Hilbert–Pólya
contract, built zeta-free on `Analysis.RSum`.

`posForm c N = Σ_{i<N} c_i²` is the Euclidean / Hurwitz diagonal metric `‖c‖²_N`. Two properties are
*proven here from first principles* (not assumed):

  • `posForm_nonneg`  — it is positive-semidefinite (each square `c_i² ≥ 0`, `Rnonneg_RsumN`);
  • `posForm_definite` — it is genuinely **positive-definite**: `‖c‖²_N ≈ 0` forces every coordinate
    `c_i ≈ 0` (`i < N`). This rests on Bishop **square-definiteness** `x·x ≈ 0 ⟹ x ≈ 0`, which is the
    nontrivial content and is proven below at the ℚ level (a `√`-monotone squeeze against the
    convergent auxiliary index `n = (k+1)²`, killed by the generalized Archimedean lemma) — it is NOT
    an axiom or a `sorry`.

The archetype is the Hurwitz octonion norm `|x|² = Σ xᵢ²`, positive-definite by the composition-algebra
structure. This metric is deliberately kept **separate** from two nearby but different objects:

  (i)  the signed spectral observable `atlasM` (`Square.AtlasSpectrum`), which is *indefinite*
       (signature `(10,14)`, `atlasM_indefinite`) — a negative eigenvalue of that *operator* is not a
       self-adjointness failure of this metric, which stays positive-definite; and
  (ii) the rank-one Gram form `Rmul (f i) (f j)`, which is positive-*semi*definite but NOT
       positive-definite (it vanishes on a hyperplane), hence not a valid metric.

Two further items are named **obligations**, not built here: the octonion *composition* identity
`|xy| = |x||y|`, and the *completion* of this finite diagonal to an infinite-dimensional Hilbert
metric. Its crux fields are `none`.

**Import cone.** The transitive cone (`RSum`, `ROrder`, `Real` + their prerequisites) excludes every
RH-observable module — `GenuineLi`, `StieltjesEta`, `Rlambda`, `liRatio`, `CayleyMap`, `CzetaStrip`,
`RiemannZero`, `WeilLattice`, `Spectral`, `AtlasSpectrum`. It does transitively contain
`Analysis.Zeta` (via `RSum → Pi → … → ExpReal`), which is `ζ(s)` for integer `s ≥ 2` in the
convergent half-plane `Re(s) > 1` — an object that is explicitly *not* a route to RH (ζ has no zeros
there) and carries none of the critical-strip / λₙ machinery.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`/`axiom`, choice-free.
-/

import F1Square.Analysis.RSum
import F1Square.Analysis.ROrder
import F1Square.Analysis.Real
import F1Square.Analysis.RealSquareDefinite

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- A finite sum of non-negatives that equals `0` forces **every** summand to `0` (peeling the last
    term with `Radd_eq_zero_split`; induction on `N`). -/
private theorem RsumN_nonneg_eq_zero_imp (F : Nat → Real) (hnn : ∀ i, Rnonneg (F i)) :
    ∀ N, Req (RsumN F N) zero → ∀ i, i < N → Req (F i) zero := by
  intro N
  induction N with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro h i hi
    have hsplit := Radd_eq_zero_split (Rnonneg_RsumN n (fun j _ => hnn j)) (hnn n) h
    rcases Nat.lt_or_ge i n with hlt | hge
    · exact ih hsplit.1 i hlt
    · have hie : i = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hge
      rw [hie]; exact hsplit.2


-- ===========================================================================
-- The positive-definite metric.
-- ===========================================================================

/-- The Euclidean / Hurwitz diagonal metric `‖c‖²_N = Σ_{i<N} c_i²`, a genuine positive-definite
    inner-product norm (see `posForm_nonneg`, `posForm_definite`). The archetype is the Hurwitz
    octonion norm `|x|² = Σ xᵢ²`. -/
def posForm (c : Nat → Real) (N : Nat) : Real := RsumN (fun i => Rmul (c i) (c i)) N

/-- **Positive-semidefiniteness**: `‖c‖²_N ≥ 0` (each term `c_i² ≥ 0`). -/
theorem posForm_nonneg (c : Nat → Real) (N : Nat) : Rnonneg (posForm c N) :=
  Rnonneg_RsumN N (fun i _ => Rnonneg_Rmul_self_loc (c i))

/-- **Positive-definiteness** (this is a genuine metric): `‖c‖²_N ≈ 0` forces every coordinate
    `c_i ≈ 0` for `i < N`. A finite sum of non-negative squares vanishes only when each square — and
    hence each coordinate, by Bishop square-definiteness — vanishes. -/
theorem posForm_definite (c : Nat → Real) (N : Nat)
    (h : Req (posForm c N) zero) : ∀ i, i < N → Req (c i) zero := by
  intro i hi
  have hterm : Req (Rmul (c i) (c i)) zero :=
    RsumN_nonneg_eq_zero_imp (fun j => Rmul (c j) (c j)) (fun j => Rnonneg_Rmul_self_loc (c j)) N h i hi
  exact Rmul_self_eq_zero_imp hterm

end UOR.Bridge.F1Square.Square
