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

- The NEGATION foundation and DISTANCE SYMMETRY `‖a−b‖² ≈ ‖b−a‖²`. The sesquilinear negation laws
  `dlimInner_neg_left`/`dlimInner_neg_right` (`⟨−a,b⟩ ≈ ⟨a,−b⟩ ≈ −⟨a,b⟩`) are derived from
  `dlimInner_smul_right` through `dlimNeg ≈ (−1)·` (a termwise `(−1)·z ≈ −z`), and `dlimNormSq_neg`
  (`‖−a‖² ≈ ‖a‖²`) collapses the two signs. Symmetry follows from `b − a ≈ −(a − b)`.

STILL OPEN (next phases, flagged honestly): the squared QUASI-TRIANGLE `d²(a,c) ≤ 2·d²(a,b)+2·d²(b,c)`
(the sqrt-free replacement for the ordinary triangle inequality, via the parallelogram expansion of
`‖u+v‖²`); the sqrt-free COMPLEX Cauchy–Schwarz on `cInner` (`CnormSq⟨x,y⟩ ≤ 2⟨x,x⟩⟨y,y⟩`); then the
completion members' regularity, the norm-null sequence equivalence and completion `Setoid`, the
constant-sequence embedding, the rescheduled operations, and only then the completed inner product as a
constructive limit (built from a clean `ComplexLimitCore`, NOT the `Analysis.ComplexLimit` that
transitively reaches `Analysis.Zeta`), positive-definiteness/pre-Hilbert laws, the explicit completeness
proof, the isometric dense embedding with approximation modulus, continuous coordinate reads, and finally
the maximal weighted domain `D(M_w)` and its self-adjointness. This module is deliberately the substrate
ONLY; it does not name or assert a completed Hilbert space yet, and it does NOT extend any operator by
continuity.

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
-- The negation foundation: `⟨−a, b⟩ ≈ ⟨a, −b⟩ ≈ −⟨a, b⟩` and `‖−a‖² ≈ ‖a‖²`.
-- ===========================================================================

/-- `Rneg` is an involution (component form), used to collapse a double complex negation. -/
private theorem Rneg_Rneg_loc (r : Real) : Req (Rneg (Rneg r)) r :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (r.seq n))) (r.seq n)
    simp only [Qeq, neg]; push_cast; ring_uor)

/-- Complex negation respects `Ceq`. -/
private theorem Cneg_congr_loc {z w : Complex} (h : Ceq z w) : Ceq (Cneg z) (Cneg w) :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- Complex negation is an involution. -/
private theorem Cneg_Cneg_loc (z : Complex) : Ceq (Cneg (Cneg z)) z :=
  ⟨Rneg_Rneg_loc z.re, Rneg_Rneg_loc z.im⟩

/-- `−0 ≈ 0`. -/
private theorem Rneg_zero_loc : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (zero.seq n)) (zero.seq n)
    simp only [zero_seq, Qeq, neg]; decide)

/-- `Cconj (−z) ≈ −(Cconj z)` — holds definitionally (both are `⟨−z.re, −(−z.im)⟩`). -/
private theorem Cconj_Cneg_loc (z : Complex) : Ceq (Cconj (Cneg z)) (Cneg (Cconj z)) :=
  ⟨Req_refl _, Req_refl _⟩

/-- `(−1)·z ≈ −z` (the bridge turning colimit negation into `(−1)·`), from the `ℝ` product laws:
    real part `(−1)·a − (−0)·b ≈ −a`, imaginary part `(−1)·b + (−0)·a ≈ −b`. -/
private theorem neg_one_Cmul_loc (z : Complex) : Ceq (Cmul (Cneg Cone) z) (Cneg z) :=
  have hone : ∀ w : Real, Req (Rmul (Rneg one) w) (Rneg w) := fun w =>
    Req_trans (Rmul_neg_left one w) (Rneg_congr (Req_trans (Rmul_comm one w) (Rmul_one w)))
  have hzero : ∀ w : Real, Req (Rmul (Rneg zero) w) zero := fun w =>
    Req_trans (Rmul_neg_left zero w)
      (Req_trans (Rneg_congr (Req_trans (Rmul_comm zero w) (Rmul_zero w))) Rneg_zero_loc)
  ⟨Req_trans (Rsub_congr (hone z.re) (hzero z.im)) (Rsub_zero (Rneg z.re)),
   Req_trans (Radd_congr (hone z.im) (hzero z.re)) (Radd_zero (Rneg z.im))⟩

/-- Colimit negation is `(−1)·` scaling (up to `DLimEq`). -/
private theorem dlimNeg_eq_smul (a : DLimRaw) :
    DLimEq (dlimNeg a) (dlimSmul (Cneg Cone) a) :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _)
      (CVecEq_trans (fun i => Ceq_symm (neg_one_Cmul_loc (a.vec i)))
        (CVecEq_symm (cvInc_id _)))⟩

/-- Colimit negation is an involution. -/
private theorem dlimNeg_dlimNeg (a : DLimRaw) : DLimEq (dlimNeg (dlimNeg a)) a :=
  ⟨a.stage, Nat.le_refl _, Nat.le_refl _,
    CVecEq_trans (cvInc_id _)
      (CVecEq_trans (fun i => Cneg_Cneg_loc (a.vec i)) (CVecEq_symm (cvInc_id _)))⟩

/-- Colimit negation distributes over addition: `−(a + b) ≈ (−a) + (−b)` — through `(−1)·` scaling. -/
private theorem dlimNeg_dlimAdd (a b : DLimRaw) :
    DLimEq (dlimNeg (dlimAdd a b)) (dlimAdd (dlimNeg a) (dlimNeg b)) :=
  DLimEq_trans (dlimNeg_eq_smul (dlimAdd a b))
    (DLimEq_trans (dlimSmul_dlimAdd (Cneg Cone) a b)
      (dlimAdd_wd (DLimEq_symm (dlimNeg_eq_smul a)) (DLimEq_symm (dlimNeg_eq_smul b))))

/-- **Right negation**: `⟨a, −b⟩ ≈ −⟨a, b⟩` (from `dlimInner_smul_right` at `(−1)`). -/
theorem dlimInner_neg_right (a b : DLimRaw) :
    Ceq (dlimInner a (dlimNeg b)) (Cneg (dlimInner a b)) :=
  Ceq_trans (dlimInner_wd (DLimEq_refl a) (dlimNeg_eq_smul b))
    (Ceq_trans (dlimInner_smul_right (Cneg Cone) a b)
      (neg_one_Cmul_loc (dlimInner a b)))

/-- **Left negation**: `⟨−a, b⟩ ≈ −⟨a, b⟩` (from right negation through Hermitian symmetry). -/
theorem dlimInner_neg_left (a b : DLimRaw) :
    Ceq (dlimInner (dlimNeg a) b) (Cneg (dlimInner a b)) :=
  Ceq_trans (dlimInner_conj (dlimNeg a) b)
    (Ceq_trans (Cconj_congr (dlimInner_neg_right b a))
      (Ceq_trans (Cconj_Cneg_loc (dlimInner b a))
        (Cneg_congr_loc (Ceq_symm (dlimInner_conj a b)))))

/-- **The squared norm is negation-invariant**: `‖−a‖² ≈ ‖a‖²` (the two signs cancel). -/
theorem dlimNormSq_neg (a : DLimRaw) : Req (dlimNormSq (dlimNeg a)) (dlimNormSq a) :=
  (Ceq_trans (dlimInner_neg_left a (dlimNeg a))
    (Ceq_trans (Cneg_congr_loc (dlimInner_neg_right a a))
      (Cneg_Cneg_loc (dlimInner a a)))).1

/-- `b − a ≈ −(a − b)` in the colimit group. -/
private theorem dlimSub_neg_comm (a b : DLimRaw) :
    DLimEq (dlimSub b a) (dlimNeg (dlimSub a b)) :=
  DLimEq_symm
    (DLimEq_trans (dlimNeg_dlimAdd a (dlimNeg b))
      (DLimEq_trans (dlimAdd_wd (DLimEq_refl (dlimNeg a)) (dlimNeg_dlimNeg b))
        (dlimAdd_comm (dlimNeg a) b)))

/-- **DISTANCE SYMMETRY** (gate item 1): `‖a − b‖² ≈ ‖b − a‖²`, via `b − a ≈ −(a − b)` and
    negation-invariance of the squared norm. The squared distance is a genuine symmetric gauge (though
    not itself an ordinary metric — the triangle law is replaced by the squared quasi-triangle). -/
theorem dlimDist2_symm (a b : DLimRaw) : Req (dlimDist2 a b) (dlimDist2 b a) :=
  Req_symm (Req_trans (dlimNormSq_wd (dlimSub_neg_comm a b)) (dlimNormSq_neg (dlimSub a b)))

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
