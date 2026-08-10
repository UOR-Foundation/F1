/-
F1 square — **the ℓ² completion of the finite-support direct limit: the analytic substrate**
(`DlimHilbertCompletion.lean`, phase 1). This is the CANDIDATE-INDEPENDENT genuine-completion layer the
operator contract demands: it consumes ONLY `FinDirectLimit` (the finite-support direct-limit pre-Hilbert
carrier `DLimRaw`/`dlimInner`) and builds the squared-distance substrate on which the ℓ² completion, the maximal
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
  the completion's squared-distance gauge definite (via `dlimInner_self_definite` and a colimit group-cancellation
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

/-- **THE NORM-NULL EQUIVALENCE** — the definiteness of the completion's squared-distance gauge (NOT a
    metric — `dlimDist2` is squared, only a quasi-triangle holds): `‖a − b‖² ≈ 0 ↔ a ≈ b`.
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
-- The parallelogram expansion and the squared QUASI-TRIANGLE.
-- ===========================================================================

/-- ℝ addition is monotone (ported verbatim from the clean `Pi.Radd_le_add`; kept local to preserve the
    import-only-`FinDirectLimit` fence). Both sides reindex to `2n+1`, so the sum bound lands pointwise. -/
private theorem Radd_le_add_loc {a a' b b' : Real} (ha : Rle a a') (hb : Rle b b') :
    Rle (Radd a b) (Radd a' b') := by
  intro n
  show Qle (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1)))
    (add (add (a'.seq (2 * n + 1)) (b'.seq (2 * n + 1))) ⟨2, n + 1⟩)
  have hsum := Qadd_le_add (ha (2 * n + 1)) (hb (2 * n + 1))
  refine Qle_congr_right ?_ ?_ hsum
  · exact add_den_pos (add_den_pos (a'.den_pos (2 * n + 1)) (Nat.succ_pos _))
      (add_den_pos (b'.den_pos (2 * n + 1)) (Nat.succ_pos _))
  · simp only [Qeq, add]; push_cast; ring_uor

/-- Adding a nonnegative real on the right can only increase: `x ≤ x + w` when `w ≥ 0`. -/
private theorem Rle_add_nonneg_right (x : Real) {w : Real} (hw : Rnonneg w) : Rle x (Radd x w) :=
  Rle_trans (Rle_of_Req (Req_symm (Radd_zero x)))
    (Radd_le_add_loc (Rle_refl x) (Rle_zero_of_Rnonneg hw))

/-- The 8-term cancellation `(P+s)+(r+Q)  ⊕  (P+(−s))+((−r)+Q)  ≈  (P+P)+(Q+Q)`. The cross terms
    `s, r` cancel against their negatives; proved by the shape-aware middle-four swap `Radd_swap`
    (which correctly tracks the Bishop reindexing across the balanced tree) plus `Radd_neg`/`Radd_zero`. -/
private theorem quasi_arith (P Q s r : Real) :
    Req (Radd (Radd (Radd P s) (Radd r Q)) (Radd (Radd P (Rneg s)) (Radd (Rneg r) Q)))
        (Radd (Radd P P) (Radd Q Q)) :=
  have hAC : Req (Radd (Radd P s) (Radd P (Rneg s))) (Radd P P) :=
    Req_trans (Radd_swap P s P (Rneg s))
      (Req_trans (Radd_congr (Req_refl (Radd P P)) (Radd_neg s)) (Radd_zero (Radd P P)))
  have hBD : Req (Radd (Radd r Q) (Radd (Rneg r) Q)) (Radd Q Q) :=
    Req_trans (Radd_swap r Q (Rneg r) Q)
      (Req_trans (Radd_congr (Radd_neg r) (Req_refl (Radd Q Q)))
        (Req_trans (Radd_comm zero (Radd Q Q)) (Radd_zero (Radd Q Q))))
  Req_trans (Radd_swap (Radd P s) (Radd r Q) (Radd P (Rneg s)) (Radd (Rneg r) Q))
    (Radd_congr hAC hBD)

/-- **Additivity in the LEFT slot**: `⟨a + b, c⟩ ≈ ⟨a, c⟩ + ⟨b, c⟩` (from right additivity through
    Hermitian symmetry `⟨·,·⟩ = conj⟨·,·⟩` and `Cconj_Cadd`). -/
theorem dlimInner_add_left (a b c : DLimRaw) :
    Ceq (dlimInner (dlimAdd a b) c) (Cadd (dlimInner a c) (dlimInner b c)) :=
  Ceq_trans (dlimInner_conj (dlimAdd a b) c)
    (Ceq_trans (Cconj_congr (dlimInner_add_right c a b))
      (Ceq_trans (Cconj_Cadd (dlimInner c a) (dlimInner c b))
        (Cadd_congr (Ceq_symm (dlimInner_conj a c)) (Ceq_symm (dlimInner_conj b c)))))

/-- **The parallelogram expansion**: `‖x + y‖² ≈ ‖x‖² + (⟨y,x⟩.re + ⟨x,y⟩.re) + ‖y‖²`. Purely the
    sesquilinear expansion of `⟨x+y, x+y⟩` (right- then left-additivity) read on the real part; the
    real part of a `Cadd` is the `Radd` of real parts definitionally. -/
theorem dlimNormSq_add (x y : DLimRaw) :
    Req (dlimNormSq (dlimAdd x y))
      (Radd (Radd (dlimNormSq x) (dlimInner y x).re)
            (Radd (dlimInner x y).re (dlimNormSq y))) :=
  (Ceq_trans (dlimInner_add_right (dlimAdd x y) x y)
    (Cadd_congr (dlimInner_add_left x y x) (dlimInner_add_left x y y))).1

/-- `(a − b) + (b − c) ≈ a − c` in the colimit group (`b` telescopes). -/
private theorem dlimAdd_sub_sub (a b c : DLimRaw) :
    DLimEq (dlimAdd (dlimSub a b) (dlimSub b c)) (dlimSub a c) :=
  DLimEq_trans (dlimAdd_assoc a (dlimNeg b) (dlimAdd b (dlimNeg c)))
    (DLimEq_trans (dlimAdd_wd (DLimEq_refl a)
        (DLimEq_symm (dlimAdd_assoc (dlimNeg b) b (dlimNeg c))))
      (DLimEq_trans (dlimAdd_wd (DLimEq_refl a)
          (dlimAdd_wd (dlimNeg_add_self b) (DLimEq_refl (dlimNeg c))))
        (dlimAdd_wd (DLimEq_refl a) (dlimZero_add (dlimNeg c)))))

/-- **THE SQUARED QUASI-TRIANGLE** (gate item 1): `d²(a,c) ≤ 2·d²(a,b) + 2·d²(b,c)`. This is the
    sqrt-free replacement for the ordinary triangle inequality — the squared distance is NOT a metric,
    but this quasi-triangle is exactly what the completion's Cauchy/limit arguments require. Proof:
    with `u := a−b`, `v := b−c`, `a−c ≈ u+v`, so `d²(a,c) ≈ ‖u+v‖²`; the parallelogram expansions of
    `‖u+v‖²` and `‖u−v‖²` share the cross term with opposite sign, and `‖u+v‖² + ‖u−v‖² ≈ 2‖u‖²+2‖v‖²`
    (`quasi_arith`), while `‖u−v‖² ≥ 0`, so `‖u+v‖² ≤ ‖u+v‖² + ‖u−v‖² ≈ 2‖u‖²+2‖v‖²`. -/
theorem dlimDist2_quasitriangle (a b c : DLimRaw) :
    Rle (dlimDist2 a c)
      (Radd (Radd (dlimDist2 a b) (dlimDist2 a b))
            (Radd (dlimDist2 b c) (dlimDist2 b c))) := by
  -- Abbreviations: u = a−b, v = b−c.
  have hEQplus : Req (dlimNormSq (dlimAdd (dlimSub a b) (dlimSub b c)))
      (Radd (Radd (dlimDist2 a b) (dlimInner (dlimSub b c) (dlimSub a b)).re)
            (Radd (dlimInner (dlimSub a b) (dlimSub b c)).re (dlimDist2 b c))) :=
    dlimNormSq_add (dlimSub a b) (dlimSub b c)
  have hEQminus : Req (dlimNormSq (dlimSub (dlimSub a b) (dlimSub b c)))
      (Radd (Radd (dlimDist2 a b) (Rneg (dlimInner (dlimSub b c) (dlimSub a b)).re))
            (Radd (Rneg (dlimInner (dlimSub a b) (dlimSub b c)).re) (dlimDist2 b c))) :=
    Req_trans (dlimNormSq_add (dlimSub a b) (dlimNeg (dlimSub b c)))
      (Radd_congr
        (Radd_congr (Req_refl (dlimDist2 a b)) (dlimInner_neg_left (dlimSub b c) (dlimSub a b)).1)
        (Radd_congr (dlimInner_neg_right (dlimSub a b) (dlimSub b c)).1
          (dlimNormSq_neg (dlimSub b c))))
  -- ‖u+v‖² ≤ ‖u+v‖² + ‖u−v‖² ≈ 2·d²(a,b) + 2·d²(b,c).
  have hstep : Rle (dlimNormSq (dlimAdd (dlimSub a b) (dlimSub b c)))
      (Radd (Radd (dlimDist2 a b) (dlimDist2 a b)) (Radd (dlimDist2 b c) (dlimDist2 b c))) :=
    Rle_trans
      (Rle_add_nonneg_right _ (dlimNormSq_nonneg (dlimSub (dlimSub a b) (dlimSub b c))))
      (Rle_of_Req (Req_trans (Radd_congr hEQplus hEQminus)
        (quasi_arith (dlimDist2 a b) (dlimDist2 b c)
          (dlimInner (dlimSub b c) (dlimSub a b)).re
          (dlimInner (dlimSub a b) (dlimSub b c)).re)))
  -- Transport d²(a,c) ≈ ‖u+v‖² along a−c ≈ u+v.
  exact Rle_trans
    (Rle_of_Req (dlimNormSq_wd (DLimEq_symm (dlimAdd_sub_sub a b c)))) hstep

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

-- ===========================================================================
-- Modulus properties (symmetry / nonnegativity / decay) and the Cauchy predicate's
-- constant witness and pointwise congruence (gate item 2).
-- ===========================================================================

/-- `ofQ` of a nonnegative rational is `Rnonneg`. -/
private theorem Rnonneg_ofQ_loc {q : Q} (hq : 0 < q.den) (hn : 0 ≤ q.num) : Rnonneg (ofQ q hq) := by
  intro n
  show (neg (Qbound n)).num * (q.den : Int) ≤ q.num * ((neg (Qbound n)).den : Int)
  have hd : (0 : Int) ≤ q.num * ((neg (Qbound n)).den : Int) :=
    Int.mul_nonneg hn (by show (0 : Int) ≤ ((neg (Qbound n)).den : Int); simp only [neg, Qbound]; omega)
  have hl : (neg (Qbound n)).num * (q.den : Int) ≤ 0 := by simp only [neg, Qbound]; push_cast; omega
  omega

/-- `ofQ` is monotone: `a ≤ b` (rationals) gives `ofQ a ≤ ofQ b`. -/
private theorem Rle_ofQ_of_Qle_loc {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (h : Qle a b) :
    Rle (ofQ a ha) (ofQ b hb) :=
  fun n => Qle_trans (b := b) hb h (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Modulus SYMMETRY**: `M(j,k) ≈ M(k,j)` — the canonical squared modulus is symmetric in `j, k`. -/
private theorem dlimCauchyMod_symm (j k : Nat) :
    Req (dlimCauchyModR j k) (dlimCauchyModR k j) := by
  unfold dlimCauchyModR
  exact ofQ_respects _ _ (by simp only [Qeq, mul, add]; push_cast; ring_uor)

/-- **Modulus NONNEGATIVITY**: `M(j,k) ≥ 0` (it is a square). -/
private theorem dlimCauchyMod_nonneg (j k : Nat) : Rnonneg (dlimCauchyModR j k) := by
  unfold dlimCauchyModR
  refine Rnonneg_ofQ_loc _ ?_
  have hX : (0 : Int) ≤ (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)).num := by
    simp only [add]; push_cast; omega
  exact Int.mul_nonneg hX hX

/-- **Modulus DECAY** (diagonal): `M(n,n) ≤ 4/(n+1)` — the diagonal modulus `(2/(n+1))²` is dominated
    by the canonical null real `ofQ ⟨4,n+1⟩`, so it vanishes with `n`. Proved by transporting
    `(2/(n+1))²` to `⟨4,(n+1)²⟩` and the degree-2 bound `4(n+1) ≤ 4(n+1)²`. -/
private theorem dlimCauchyMod_diag_decay (n : Nat) :
    Rle (dlimCauchyModR n n) (ofQ (⟨4, n + 1⟩ : Q) (Nat.succ_pos n)) := by
  unfold dlimCauchyModR
  apply Rle_ofQ_of_Qle_loc
  refine Qle_congr_left (a := (⟨4, (n + 1) * (n + 1)⟩ : Q)) ?_ ?_ ?_
  · exact Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
  · simp only [Qeq, mul, add]; push_cast; ring_uor
  · show (4 : Int) * ((n + 1 : Nat) : Int) ≤ (4 : Int) * (((n + 1) * (n + 1) : Nat) : Int)
    have hnn : (0 : Int) ≤ (n : Int) * ((n : Int) + 1) := Int.mul_nonneg (by omega) (by omega)
    have heq : ((n : Int) + 1) * ((n : Int) + 1) = ((n : Int) + 1) + (n : Int) * ((n : Int) + 1) := by
      ring_uor
    push_cast
    omega

/-- **The constant sequence is Cauchy** (gate item 2): `DLimCauchyU (fun _ => a)`, since
    `‖a − a‖² ≈ 0 ≤ M(j,k)`. -/
theorem DLimCauchyU_const (a : DLimRaw) : DLimCauchyU (fun _ => a) :=
  fun j k => Rle_trans (Rle_of_Req (dlimDist2_self a))
    (Rle_zero_of_Rnonneg (dlimCauchyMod_nonneg j k))

/-- **Pointwise `DLimEq` congruence of the Cauchy predicate** (gate item 2): if `x j ≈ y j` for every
    `j`, then `x` Cauchy ⟹ `y` Cauchy (the squared distances agree by `dlimDist2_wd`). -/
theorem DLimCauchyU_congr {x y : Nat → DLimRaw} (h : ∀ j, DLimEq (x j) (y j))
    (hx : DLimCauchyU x) : DLimCauchyU y :=
  fun j k => Rle_trans
    (Rle_of_Req (Req_symm (dlimDist2_wd (h j) (h k)))) (hx j k)

-- ===========================================================================
-- The completion raw carrier, its norm-null equivalence, the Setoid, and the
-- constant-sequence map + its injective reflection (gate items 4–7).
-- ===========================================================================

/-- **The completion raw carrier** (gate item 4): a Cauchy sequence of finite-support vectors together
    with its regularity proof (`DLimCauchyU`, the fixed canonical squared modulus). A completion member
    is such a sequence up to `DLimCompletionEq`. -/
structure DLimCompletionRaw where
  seq : Nat → DLimRaw
  reg : DLimCauchyU seq

/-- `⊕`-sum of two ℝ constants is the ℝ of their ℚ-sum. -/
private theorem Radd_ofQ_loc {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Radd (ofQ a ha) (ofQ b hb)) (ofQ (add a b) (add_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl (add a b))

/-- **The norm-null sequence equivalence** (gate item 5): `X ≈ Y` iff the squared distance
    `‖X n − Y n‖²` is eventually below every `1/(k+1)`. The `∀k` quantifier ABSORBS the factor-2 of the
    squared quasi-triangle (which the fixed-modulus relation could not), so this is a genuine transitive
    equivalence in the sqrt-free setting — the sound replacement for a metric-space equality. -/
def DLimCompletionEq (X Y : DLimCompletionRaw) : Prop :=
  ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    Rle (dlimDist2 (X.seq n) (Y.seq n)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))

/-- Reflexivity: `‖X n − X n‖² ≈ 0 ≤ 1/(k+1)`. -/
theorem DLimCompletionEq_refl (X : DLimCompletionRaw) : DLimCompletionEq X X :=
  fun k => ⟨0, fun n _ => Rle_trans (Rle_of_Req (dlimDist2_self (X.seq n)))
    (Rle_zero_of_Rnonneg (Rnonneg_ofQ_loc (Nat.succ_pos k) (by show (0 : Int) ≤ 1; decide)))⟩

/-- Symmetry: the squared distance is symmetric (`dlimDist2_symm`). -/
theorem DLimCompletionEq_symm {X Y : DLimCompletionRaw} (h : DLimCompletionEq X Y) :
    DLimCompletionEq Y X := by
  intro k
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => Rle_trans (Rle_of_Req (dlimDist2_symm (Y.seq n) (X.seq n))) (hN n hn)⟩

/-- Transitivity: the squared quasi-triangle `d²(Xn,Zn) ≤ 2·d²(Xn,Yn)+2·d²(Yn,Zn)`, with both middle
    distances driven below `1/(4(k+1))` (the auxiliary level `4k+3`), sums to `4/(4(k+1)) = 1/(k+1)`.
    The factor-4 is absorbed EXACTLY by refining the auxiliary index. -/
theorem DLimCompletionEq_trans {X Y Z : DLimCompletionRaw}
    (hXY : DLimCompletionEq X Y) (hYZ : DLimCompletionEq Y Z) : DLimCompletionEq X Z := by
  intro k
  obtain ⟨N1, hN1⟩ := hXY (4 * k + 3)
  obtain ⟨N2, hN2⟩ := hYZ (4 * k + 3)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  refine Rle_trans (dlimDist2_quasitriangle (X.seq n) (Y.seq n) (Z.seq n)) ?_
  refine Rle_trans
    (Radd_le_add_loc (Radd_le_add_loc (hN1 n hn1) (hN1 n hn1))
      (Radd_le_add_loc (hN2 n hn2) (hN2 n hn2))) ?_
  refine Rle_of_Req (Req_trans
    (Req_trans (Radd_congr (Radd_ofQ_loc _ _) (Radd_ofQ_loc _ _)) (Radd_ofQ_loc _ _))
    (ofQ_respects _ (Nat.succ_pos k) ?_))
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- The completion setoid (gate item 6). -/
instance dlimCompletionSetoid : Setoid DLimCompletionRaw where
  r := DLimCompletionEq
  iseqv := ⟨DLimCompletionEq_refl, fun h => DLimCompletionEq_symm h,
    fun h₁ h₂ => DLimCompletionEq_trans h₁ h₂⟩

/-- **The constant-sequence map** `DLimRaw → completion` (gate item 7): a finite-support vector as the
    constant Cauchy sequence. This is the underlying MAP only. Its INJECTIVITY (equality reflection) is
    `DLimCompletionEq_of_iff` below; the completed-distance ISOMETRY and DENSITY are separate theorems,
    still OPEN (they need the completed inner product). So this is **not yet** an isometric dense
    embedding — it is a well-defined, injective (mod the setoids) map into the completion carrier. -/
def DLimCompletionRaw.of (a : DLimRaw) : DLimCompletionRaw :=
  ⟨fun _ => a, DLimCauchyU_const a⟩

/-- The map respects the colimit setoid: `a ≈ b ⟹ of a ≈ of b` (the forward/`←` half of reflection). -/
theorem DLimCompletionEq_of {a b : DLimRaw} (h : DLimEq a b) :
    DLimCompletionEq (DLimCompletionRaw.of a) (DLimCompletionRaw.of b) :=
  fun k => ⟨0, fun n _ => Rle_trans
    (Rle_of_Req (Req_trans (dlimDist2_wd (DLimEq_refl a) (DLimEq_symm h)) (dlimDist2_self a)))
    (Rle_zero_of_Rnonneg (Rnonneg_ofQ_loc (Nat.succ_pos k) (by show (0 : Int) ≤ 1; decide)))⟩

/-- **Archimedean squeeze**: a nonnegative real that is `≤ 1/(k+1)` for every `k` is `≈ 0`. Proved by
    antisymmetry — `x ≥ 0` from nonnegativity, and `x ≤ 0` because `x ≤ 1/(k+1) + 2/(n+1)` for all `k` at
    each index `n`, and `Qarch_gen` kills the `1/(k+1)` tail. -/
private theorem Req_zero_of_nonneg_of_small {x : Real} (hnn : Rnonneg x)
    (hall : ∀ k : Nat, Rle x (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) : Req x zero := by
  refine Rle_antisymm ?_ (Rle_zero_of_Rnonneg hnn)
  intro n
  refine Qarch_gen (C := 1) (x.den_pos n) (add_den_pos (zero.den_pos n) (Nat.succ_pos n)) (fun k => ?_)
  have hb : Qle (x.seq n) (add (⟨1, k + 1⟩ : Q) (⟨2, n + 1⟩ : Q)) := hall k n
  refine Qle_congr_right (add_den_pos (Nat.succ_pos k) (Nat.succ_pos n)) ?_ hb
  simp only [Qeq, add, zero_seq]; push_cast; ring_uor

/-- **EMBEDDING REFLECTION / INJECTIVITY** (reviewer gate 1): `of a ≈ of b ↔ a ≈ b`. The map `of` is
    therefore injective modulo the two setoids. Forward: `of a ≈ of b` bounds the (constant) squared
    distance `‖a − b‖²` below every `1/(k+1)`, so it is `≈ 0` (the Archimedean squeeze), whence `a ≈ b`
    by the norm-null equivalence `dlimDist2_zero_iff`. Backward: `DLimCompletionEq_of`. -/
theorem DLimCompletionEq_of_iff (a b : DLimRaw) :
    DLimCompletionEq (DLimCompletionRaw.of a) (DLimCompletionRaw.of b) ↔ DLimEq a b := by
  refine ⟨fun h => ?_, DLimCompletionEq_of⟩
  have hall : ∀ k : Nat, Rle (dlimDist2 a b) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
    intro k
    obtain ⟨N, hN⟩ := h k
    exact hN N (Nat.le_refl N)
  exact (dlimDist2_zero_iff a b).mp (Req_zero_of_nonneg_of_small (dlimDist2_nonneg a b) hall)

-- ===========================================================================
-- Rescheduled operations on completion members (gate item 8): NEGATION and ADDITION.
-- Negation preserves the modulus outright; addition RESCHEDULES `n ↦ 2n+1` so the
-- factor-4 of the quasi-triangle is cancelled by `M(2j+1,2k+1) = ¼·M(j,k)`.
-- ===========================================================================

/-- Group cancellation `(a+c) − (b+c) ≈ a − b`. -/
private theorem dlimAdd_sub_cancel_right (a b c : DLimRaw) :
    DLimEq (dlimSub (dlimAdd a c) (dlimAdd b c)) (dlimSub a b) :=
  DLimEq_trans (dlimAdd_wd (DLimEq_refl (dlimAdd a c)) (dlimNeg_dlimAdd b c))
    (DLimEq_trans (dlimAdd_assoc a c (dlimAdd (dlimNeg b) (dlimNeg c)))
      (dlimAdd_wd (DLimEq_refl a)
        (DLimEq_trans (dlimAdd_wd (DLimEq_refl c) (dlimAdd_comm (dlimNeg b) (dlimNeg c)))
          (DLimEq_trans (DLimEq_symm (dlimAdd_assoc c (dlimNeg c) (dlimNeg b)))
            (DLimEq_trans (dlimAdd_wd (dlimAdd_neg c) (DLimEq_refl (dlimNeg b)))
              (dlimZero_add (dlimNeg b)))))))

/-- Group cancellation `(c+a) − (c+b) ≈ a − b`. -/
private theorem dlimAdd_sub_cancel_left (a b c : DLimRaw) :
    DLimEq (dlimSub (dlimAdd c a) (dlimAdd c b)) (dlimSub a b) :=
  DLimEq_trans (dlimSub_wd (dlimAdd_comm c a) (dlimAdd_comm c b)) (dlimAdd_sub_cancel_right a b c)

/-- `‖(−a) − (−b)‖² ≈ ‖a − b‖²`. -/
private theorem dlimDist2_neg_neg (a b : DLimRaw) :
    Req (dlimDist2 (dlimNeg a) (dlimNeg b)) (dlimDist2 a b) :=
  Req_trans (dlimNormSq_wd
      (DLimEq_trans (dlimAdd_wd (DLimEq_refl (dlimNeg a)) (dlimNeg_dlimNeg b))
        (dlimAdd_comm (dlimNeg a) b)))
    (dlimDist2_symm b a)

/-- `‖(a+c) − (b+c)‖² ≈ ‖a − b‖²` and `‖(c+a) − (c+b)‖² ≈ ‖a − b‖²`. -/
private theorem dlimDist2_add_right (a b c : DLimRaw) :
    Req (dlimDist2 (dlimAdd a c) (dlimAdd b c)) (dlimDist2 a b) :=
  dlimNormSq_wd (dlimAdd_sub_cancel_right a b c)

private theorem dlimDist2_add_left (a b c : DLimRaw) :
    Req (dlimDist2 (dlimAdd c a) (dlimAdd c b)) (dlimDist2 a b) :=
  dlimNormSq_wd (dlimAdd_sub_cancel_left a b c)

/-- **NEGATION** of a completion member (no rescheduling: negation preserves the squared modulus). -/
def dlimCompletionNeg (X : DLimCompletionRaw) : DLimCompletionRaw :=
  ⟨fun n => dlimNeg (X.seq n),
   fun j k => Rle_trans (Rle_of_Req (dlimDist2_neg_neg (X.seq j) (X.seq k))) (X.reg j k)⟩

/-- Negation preserves the completion equivalence. -/
theorem dlimCompletionNeg_congr {X Y : DLimCompletionRaw} (h : DLimCompletionEq X Y) :
    DLimCompletionEq (dlimCompletionNeg X) (dlimCompletionNeg Y) := by
  intro k
  obtain ⟨N, hN⟩ := h k
  exact ⟨N, fun n hn => Rle_trans (Rle_of_Req (dlimDist2_neg_neg (X.seq n) (Y.seq n))) (hN n hn)⟩

/-- **The modulus HALVES under doubling**: `4·M(2j+1,2k+1) ≈ M(j,k)` — the exact identity that makes the
    `n ↦ 2n+1` reschedule restore the canonical modulus after the quasi-triangle's factor-4. -/
private theorem dlimCauchyMod_halve (j k : Nat) :
    Req (Radd (Radd (dlimCauchyModR (2 * j + 1) (2 * k + 1)) (dlimCauchyModR (2 * j + 1) (2 * k + 1)))
             (Radd (dlimCauchyModR (2 * j + 1) (2 * k + 1)) (dlimCauchyModR (2 * j + 1) (2 * k + 1))))
        (dlimCauchyModR j k) := by
  unfold dlimCauchyModR
  refine Req_trans
    (Req_trans (Radd_congr (Radd_ofQ_loc _ _) (Radd_ofQ_loc _ _)) (Radd_ofQ_loc _ _))
    (ofQ_respects _ _ ?_)
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **ADDITION** of completion members, RESCHEDULED by `n ↦ 2n+1`: this restores the canonical squared
    modulus, since the quasi-triangle gives `4·M(2j+1,2k+1)` which equals `M(j,k)` (`dlimCauchyMod_halve`).
    The midpoint `X_{2k+1}+Y_{2j+1}` splits the coupled difference into a pure-`X` and a pure-`Y` part. -/
def dlimCompletionAdd (X Y : DLimCompletionRaw) : DLimCompletionRaw :=
  ⟨fun n => dlimAdd (X.seq (2 * n + 1)) (Y.seq (2 * n + 1)),
   fun j k => by
     refine Rle_trans (dlimDist2_quasitriangle
       (dlimAdd (X.seq (2 * j + 1)) (Y.seq (2 * j + 1)))
       (dlimAdd (X.seq (2 * k + 1)) (Y.seq (2 * j + 1)))
       (dlimAdd (X.seq (2 * k + 1)) (Y.seq (2 * k + 1)))) ?_
     refine Rle_trans (Radd_le_add_loc
       (Radd_le_add_loc
         (Rle_trans (Rle_of_Req (dlimDist2_add_right (X.seq (2 * j + 1)) (X.seq (2 * k + 1))
           (Y.seq (2 * j + 1)))) (X.reg (2 * j + 1) (2 * k + 1)))
         (Rle_trans (Rle_of_Req (dlimDist2_add_right (X.seq (2 * j + 1)) (X.seq (2 * k + 1))
           (Y.seq (2 * j + 1)))) (X.reg (2 * j + 1) (2 * k + 1))))
       (Radd_le_add_loc
         (Rle_trans (Rle_of_Req (dlimDist2_add_left (Y.seq (2 * j + 1)) (Y.seq (2 * k + 1))
           (X.seq (2 * k + 1)))) (Y.reg (2 * j + 1) (2 * k + 1)))
         (Rle_trans (Rle_of_Req (dlimDist2_add_left (Y.seq (2 * j + 1)) (Y.seq (2 * k + 1))
           (X.seq (2 * k + 1)))) (Y.reg (2 * j + 1) (2 * k + 1))))) ?_
     exact Rle_of_Req (dlimCauchyMod_halve j k)⟩

/-- Addition preserves the completion equivalence (the reschedule keeps `2n+1 ≥ N` once `n ≥ N`). -/
theorem dlimCompletionAdd_congr {X X' Y Y' : DLimCompletionRaw}
    (hX : DLimCompletionEq X X') (hY : DLimCompletionEq Y Y') :
    DLimCompletionEq (dlimCompletionAdd X Y) (dlimCompletionAdd X' Y') := by
  intro k
  obtain ⟨N1, hN1⟩ := hX (4 * k + 3)
  obtain ⟨N2, hN2⟩ := hY (4 * k + 3)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ 2 * n + 1 := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hn) (by omega)
  have hn2 : N2 ≤ 2 * n + 1 := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hn) (by omega)
  refine Rle_trans (dlimDist2_quasitriangle
    (dlimAdd (X.seq (2 * n + 1)) (Y.seq (2 * n + 1)))
    (dlimAdd (X'.seq (2 * n + 1)) (Y.seq (2 * n + 1)))
    (dlimAdd (X'.seq (2 * n + 1)) (Y'.seq (2 * n + 1)))) ?_
  refine Rle_trans (Radd_le_add_loc
    (Radd_le_add_loc
      (Rle_trans (Rle_of_Req (dlimDist2_add_right (X.seq (2 * n + 1)) (X'.seq (2 * n + 1))
        (Y.seq (2 * n + 1)))) (hN1 _ hn1))
      (Rle_trans (Rle_of_Req (dlimDist2_add_right (X.seq (2 * n + 1)) (X'.seq (2 * n + 1))
        (Y.seq (2 * n + 1)))) (hN1 _ hn1)))
    (Radd_le_add_loc
      (Rle_trans (Rle_of_Req (dlimDist2_add_left (Y.seq (2 * n + 1)) (Y'.seq (2 * n + 1))
        (X'.seq (2 * n + 1)))) (hN2 _ hn2))
      (Rle_trans (Rle_of_Req (dlimDist2_add_left (Y.seq (2 * n + 1)) (Y'.seq (2 * n + 1))
        (X'.seq (2 * n + 1)))) (hN2 _ hn2)))) ?_
  refine Rle_of_Req (Req_trans
    (Req_trans (Radd_congr (Radd_ofQ_loc _ _) (Radd_ofQ_loc _ _)) (Radd_ofQ_loc _ _))
    (ofQ_respects _ (Nat.succ_pos k) ?_))
  simp only [Qeq, add, mul]; push_cast; ring_uor

-- ===========================================================================
-- Cofinal-rescheduling invariance (reviewer gate 2): a member is completion-equivalent
-- to its odd subsequence `n ↦ X_{2n+1}`. Reusable through the modulus monotonicity.
-- ===========================================================================

/-- **Modulus MONOTONICITY**: larger indices give a smaller squared modulus, `M(p',q') ≤ M(p,q)` when
    `p ≤ p'` and `q ≤ q'`. Each `1/(·+1)` is antitone (linear at the ℚ level), the sum is monotone
    (`Qadd_le_add`), and squaring preserves the order among nonnegatives (`Qmul_le_mul`). -/
private theorem dlimCauchyMod_mono {p p' q q' : Nat} (hp : p ≤ p') (hq : q ≤ q') :
    Rle (dlimCauchyModR p' q') (dlimCauchyModR p q) := by
  unfold dlimCauchyModR
  refine Rle_ofQ_of_Qle_loc _ _ ?_
  have hSle : Qle (add (⟨1, p' + 1⟩ : Q) (⟨1, q' + 1⟩ : Q)) (add (⟨1, p + 1⟩ : Q) (⟨1, q + 1⟩ : Q)) :=
    Qadd_le_add
      (by show (1 : Int) * ((p + 1 : Nat) : Int) ≤ 1 * ((p' + 1 : Nat) : Int); push_cast; omega)
      (by show (1 : Int) * ((q + 1 : Nat) : Int) ≤ 1 * ((q' + 1 : Nat) : Int); push_cast; omega)
  have hden : 0 < (add (⟨1, p' + 1⟩ : Q) (⟨1, q' + 1⟩ : Q)).den :=
    add_den_pos (Nat.succ_pos p') (Nat.succ_pos q')
  have hnum : (0 : Int) ≤ (add (⟨1, p' + 1⟩ : Q) (⟨1, q' + 1⟩ : Q)).num := by
    simp only [add]; push_cast; omega
  exact Qmul_le_mul hden (add_den_pos (Nat.succ_pos p) (Nat.succ_pos q)) hden hnum hnum hSle hSle

/-- **The odd subsequence** `n ↦ X_{2n+1}` as a completion member: regular because `M(2j+1,2k+1) ≤
    M(j,k)` (`dlimCauchyMod_mono`). -/
def dlimReschedOdd (X : DLimCompletionRaw) : DLimCompletionRaw :=
  ⟨fun n => X.seq (2 * n + 1),
   fun j k => Rle_trans (X.reg (2 * j + 1) (2 * k + 1))
     (dlimCauchyMod_mono (by omega) (by omega))⟩

/-- **COFINAL-RESCHEDULING INVARIANCE** (reviewer gate 2): a completion member equals its odd
    subsequence in the completion, `X ≈ X_{2n+1}`. For `n ≥ 4k+3`, regularity bounds
    `‖X_n − X_{2n+1}‖² ≤ M(n,2n+1) ≤ M(n,n) ≤ 4/(n+1) ≤ 1/(k+1)` (monotonicity + the diagonal decay). -/
theorem dlimReschedOdd_eq (X : DLimCompletionRaw) : DLimCompletionEq X (dlimReschedOdd X) := by
  intro k
  refine ⟨4 * k + 3, fun n hn => ?_⟩
  refine Rle_trans (X.reg n (2 * n + 1)) ?_
  refine Rle_trans (dlimCauchyMod_mono (p := n) (p' := n) (q := n) (q' := 2 * n + 1)
    (Nat.le_refl n) (by omega)) ?_
  refine Rle_trans (dlimCauchyMod_diag_decay n) ?_
  refine Rle_ofQ_of_Qle_loc _ _ ?_
  show (4 : Int) * ((k + 1 : Nat) : Int) ≤ (1 : Int) * ((n + 1 : Nat) : Int)
  push_cast; omega

-- ===========================================================================
-- Additive structure on the completion (reviewer gate 3): zero, the group laws
-- modulo completion equivalence, and the `of`-homomorphism laws `of_add` / `of_neg`.
-- ===========================================================================

/-- **Pointwise-`DLimEq` sufficiency**: if `X n ≈ Y n` in the colimit for every `n`, then `X ≈ Y` in
    the completion (the squared distances are `≈ 0` at every index). The workhorse for the group laws
    whose two sides agree stagewise (possibly after a reschedule). -/
theorem DLimCompletionEq_of_pointwise {X Y : DLimCompletionRaw} (h : ∀ n, DLimEq (X.seq n) (Y.seq n)) :
    DLimCompletionEq X Y :=
  fun k => ⟨0, fun n _ => Rle_trans
    (Rle_of_Req (Req_trans (dlimDist2_wd (DLimEq_refl (X.seq n)) (DLimEq_symm (h n)))
      (dlimDist2_self (X.seq n))))
    (Rle_zero_of_Rnonneg (Rnonneg_ofQ_loc (Nat.succ_pos k) (by show (0 : Int) ≤ 1; decide)))⟩

/-- The completion zero (the constant `0` sequence). -/
def dlimCompletionZero : DLimCompletionRaw := DLimCompletionRaw.of dlimZero

/-- **Commutativity** of completion addition (stagewise `dlimAdd_comm` at the reschedule index). -/
theorem dlimCompletionAdd_comm (X Y : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd X Y) (dlimCompletionAdd Y X) :=
  DLimCompletionEq_of_pointwise (fun n => dlimAdd_comm (X.seq (2 * n + 1)) (Y.seq (2 * n + 1)))

/-- **Right unit**: `X + 0 ≈ X`. Stagewise `X_{2n+1} + 0 ≈ X_{2n+1}` gives `X + 0 ≈ X_{2n+1}`, then the
    cofinal invariance `dlimReschedOdd_eq` closes `X_{2n+1} ≈ X`. -/
theorem dlimCompletionAdd_zero (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd X dlimCompletionZero) X :=
  DLimCompletionEq_trans (Y := dlimReschedOdd X)
    (DLimCompletionEq_of_pointwise (fun n => dlimAdd_zero (X.seq (2 * n + 1))))
    (DLimCompletionEq_symm (dlimReschedOdd_eq X))

/-- **Additive inverse**: `X + (−X) ≈ 0` (stagewise `dlimAdd_neg` at the reschedule index; no realign
    needed since negation does not reschedule). -/
theorem dlimCompletionAdd_neg (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd X (dlimCompletionNeg X)) dlimCompletionZero :=
  DLimCompletionEq_of_pointwise (fun n => dlimAdd_neg (X.seq (2 * n + 1)))

/-- **`of` is additive** (`of_add`): `of (a + b) ≈ (of a) + (of b)`. Both sides are the constant
    sequence `a + b` (the reschedule of a constant sequence is itself), so this is stagewise reflexivity. -/
theorem DLimCompletionEq_of_add (a b : DLimRaw) :
    DLimCompletionEq (DLimCompletionRaw.of (dlimAdd a b))
      (dlimCompletionAdd (DLimCompletionRaw.of a) (DLimCompletionRaw.of b)) :=
  DLimCompletionEq_of_pointwise (fun _ => DLimEq_refl _)

/-- **`of` respects negation** (`of_neg`): `of (−a) ≈ −(of a)`, stagewise reflexivity. -/
theorem DLimCompletionEq_of_neg (a : DLimRaw) :
    DLimCompletionEq (DLimCompletionRaw.of (dlimNeg a))
      (dlimCompletionNeg (DLimCompletionRaw.of a)) :=
  DLimCompletionEq_of_pointwise (fun _ => DLimEq_refl _)

end UOR.Bridge.F1Square.Square
