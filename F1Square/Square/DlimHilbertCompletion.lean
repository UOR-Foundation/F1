/-
F1 square — **the ℓ² completion of the finite-support direct limit: the analytic substrate**
(`DlimHilbertCompletion.lean`, phase 1). This is the CANDIDATE-INDEPENDENT genuine-completion layer the
operator contract demands: it consumes ONLY `FinDirectLimit` (the finite-support direct-limit pre-Hilbert
carrier `DLimRaw`/`dlimInner`) and builds the metric substrate on which the ℓ² completion, the maximal
weighted domain, and the self-adjoint diagonal operator will stand. It imports NO block-ladder, NO Atlas
candidate, NO nominal HP predicate, NO zeta/crux module.

WHAT IS BUILT HERE (the analytic substrate — genuine, representative-independent, sqrt-free):
- The SQUARED norm and distance `dlimNormSq a := ⟨a,a⟩.re`, `dlimDist2 a b := ‖a − b‖²`. Everything is
  kept SQUARED — no `Rsqrt`, hence no ζ/crux dependency; norm estimates will use squared quantities.
- Representative independence `dlimNormSq_wd`/`dlimSub_wd`/`dlimDist2_wd` (they descend to the colimit
  setoid `DLimEq`, via `dlimInner_wd`).
- NONNEGATIVITY (`dlimNormSq_nonneg`/`dlimDist2_nonneg`, from `dlimInner_self_nonneg`) and the
  SELF-DISTANCE `dlimDist2_self` (`‖a − a‖² ≈ 0`).
- The NORM-NULL EQUIVALENCE `dlimDist2_zero_iff` : `‖a − b‖² ≈ 0 ↔ a ≈ b` — the definiteness that makes
  the completion metric genuine (via `dlimInner_self_definite` and a colimit group-cancellation
  `dlimEq_of_sub_zero`).
- The (squared) CAUCHY relation `DLimCauchyU` : a sequence is Cauchy when `‖x_j − x_k‖²` is bounded by
  the squared canonical modulus `(1/(j+1) + 1/(k+1))²` — the ψ-free squared-Cauchy shape the completion
  members will carry.

STILL OPEN (next phases, flagged honestly): distance SYMMETRY `‖a−b‖²=‖b−a‖²`; the sqrt-free COMPLEX
Cauchy–Schwarz on `cInner` (`CnormSq⟨x,y⟩ ≤ 2⟨x,x⟩⟨y,y⟩`, the one genuinely-new brick); then the
completed inner product as a constructive limit (`Clim`), positive-definiteness/pre-Hilbert laws of the
completion, the explicit completeness proof, the isometric dense embedding of `DLimRaw` with an
approximation modulus, continuous coordinate reads against `dlimBasis`, and only then the maximal
weighted domain `D(M_w)` and its self-adjointness. This module is deliberately the substrate ONLY; it
does not name or assert a completed Hilbert space yet, and it does NOT extend any operator by continuity.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; the cone is `FinDirectLimit`'s
zeta/crux-free cone. Crux `none`.
-/

import F1Square.Square.FinDirectLimit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The squared norm and distance on the direct limit.
-- ===========================================================================

/-- Colimit subtraction `a − b := a + (−b)`. -/
def dlimSub (a b : DLimRaw) : DLimRaw := dlimAdd a (dlimNeg b)

/-- The SQUARED norm `‖a‖² := ⟨a, a⟩.re` (real by `dlimInner_self_im`, nonnegative by
    `dlimInner_self_nonneg`). Kept squared throughout — no `Rsqrt`. -/
def dlimNormSq (a : DLimRaw) : Real := (dlimInner a a).re

/-- The SQUARED distance `‖a − b‖²`. -/
def dlimDist2 (a b : DLimRaw) : Real := dlimNormSq (dlimSub a b)

/-- The squared norm respects the colimit setoid. -/
theorem dlimNormSq_wd {a a' : DLimRaw} (h : DLimEq a a') : Req (dlimNormSq a) (dlimNormSq a') :=
  (dlimInner_wd h h).1

/-- Subtraction respects the colimit setoid. -/
theorem dlimSub_wd {a a' b b' : DLimRaw} (ha : DLimEq a a') (hb : DLimEq b b') :
    DLimEq (dlimSub a b) (dlimSub a' b') :=
  dlimAdd_wd ha (dlimNeg_wd hb)

/-- The squared distance respects the colimit setoid. -/
theorem dlimDist2_wd {a a' b b' : DLimRaw} (ha : DLimEq a a') (hb : DLimEq b b') :
    Req (dlimDist2 a b) (dlimDist2 a' b') :=
  dlimNormSq_wd (dlimSub_wd ha hb)

-- ===========================================================================
-- Nonnegativity, self-distance, and the norm-null equivalence (definiteness).
-- ===========================================================================

/-- The squared norm is nonnegative. -/
theorem dlimNormSq_nonneg (a : DLimRaw) : Rnonneg (dlimNormSq a) := dlimInner_self_nonneg a

/-- The squared distance is nonnegative. -/
theorem dlimDist2_nonneg (a b : DLimRaw) : Rnonneg (dlimDist2 a b) := dlimInner_self_nonneg _

/-- `‖0‖² ≈ 0`. -/
theorem dlimNormSq_zero : Req (dlimNormSq dlimZero) zero :=
  (dlimInner_mk 0 (cvZero 0) (cvZero 0)).1

/-- **Self-distance vanishes**: `‖a − a‖² ≈ 0` (since `a − a ≈ 0`). -/
theorem dlimDist2_self (a : DLimRaw) : Req (dlimDist2 a a) zero :=
  Req_trans (dlimNormSq_wd (dlimAdd_neg a)) dlimNormSq_zero

/-- `(−b) + b ≈ 0`. -/
private theorem dlimNeg_add_self (b : DLimRaw) : DLimEq (dlimAdd (dlimNeg b) b) dlimZero :=
  DLimEq_trans (dlimAdd_comm (dlimNeg b) b) (dlimAdd_neg b)

/-- `0 + b ≈ b`. -/
private theorem dlimZero_add (b : DLimRaw) : DLimEq (dlimAdd dlimZero b) b :=
  DLimEq_trans (dlimAdd_comm dlimZero b) (dlimAdd_zero b)

/-- **Colimit group cancellation**: `a − b ≈ 0 ⟹ a ≈ b`. -/
theorem dlimEq_of_sub_zero {a b : DLimRaw} (h : DLimEq (dlimSub a b) dlimZero) : DLimEq a b :=
  DLimEq_trans (DLimEq_symm (dlimAdd_zero a))
    (DLimEq_trans (dlimAdd_wd (DLimEq_refl a) (DLimEq_symm (dlimNeg_add_self b)))
      (DLimEq_trans (DLimEq_symm (dlimAdd_assoc a (dlimNeg b) b))
        (DLimEq_trans (dlimAdd_wd h (DLimEq_refl b)) (dlimZero_add b))))

/-- **THE NORM-NULL EQUIVALENCE** — the definiteness of the completion metric: `‖a − b‖² ≈ 0 ↔ a ≈ b`.
    Forward: a vanishing squared norm gives `⟨a−b, a−b⟩ ≈ 0` (real part `0` + imaginary part `0`), then
    `dlimInner_self_definite` gives `a − b ≈ 0`, then group cancellation gives `a ≈ b`. Backward:
    `dlimDist2_wd` + `dlimDist2_self`. -/
theorem dlimDist2_zero_iff (a b : DLimRaw) : Req (dlimDist2 a b) zero ↔ DLimEq a b := by
  constructor
  · intro h
    have hcz : Ceq (dlimInner (dlimSub a b) (dlimSub a b)) Czero :=
      ⟨h, dlimInner_self_im (dlimSub a b)⟩
    exact dlimEq_of_sub_zero (dlimInner_self_definite (dlimSub a b) hcz)
  · intro h
    exact Req_trans (dlimDist2_wd (DLimEq_refl a) (DLimEq_symm h)) (dlimDist2_self a)

-- ===========================================================================
-- The squared Cauchy relation (the completion members' shape).
-- ===========================================================================

/-- The canonical squared Cauchy modulus `(1/(j+1) + 1/(k+1))²` as a real. -/
def dlimCauchyModR (j k : Nat) : Real :=
  ofQ (mul (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)))
    (Qmul_den_pos (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
                  (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k)))

/-- **The squared CAUCHY relation**: a sequence `x : ℕ → DLimRaw` is Cauchy when its pairwise squared
    distance is bounded by the squared canonical modulus. The ψ-free, `Rsqrt`-free shape a completed ℓ²
    member carries (mirroring the `L2CauchyU` template, complexified). -/
def DLimCauchyU (x : Nat → DLimRaw) : Prop :=
  ∀ j k : Nat, Rle (dlimDist2 (x j) (x k)) (dlimCauchyModR j k)

end UOR.Bridge.F1Square.Square
