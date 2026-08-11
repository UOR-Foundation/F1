/-
F1 square — **the ℓ² completion of the finite-support direct limit: the analytic substrate**
(`DlimHilbertCompletion.lean`, phase 1). This is the CANDIDATE-INDEPENDENT genuine-completion layer the
operator contract demands: it consumes `FinDirectLimit` (the finite-support direct-limit pre-Hilbert
carrier `DLimRaw`/`dlimInner`) together with the two ζ-free cores it splits off — `ComplexNormSqCore`
(the clean Complex squared modulus `cNormSq`) and `RealOrderCore` (the generic Bishop-real mul/order
lemmas) — and builds the squared-distance substrate on which the ℓ² completion, the maximal weighted
domain, and the self-adjoint diagonal operator will stand. Its whole import cone stays Zeta-free: NO
block-ladder, NO Atlas candidate, NO nominal HP predicate, NO zeta/crux module.

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

ALSO BUILT (the completion layer, on the substrate above): the squared QUASI-TRIANGLE
`d²(a,c) ≤ 2·d²(a,b)+2·d²(b,c)` (parallelogram expansion of `‖u+v‖²`); the Cauchy-modulus properties
(symmetry/nonnegativity/decay) and monotonicity; the completion carrier `DLimCompletionRaw`, its
NORM-NULL sequence equivalence (`∀k ∃N ∀n≥N ‖Xn−Yn‖²≤1/(k+1)`, the `∀k` absorbing the quasi-triangle
factor) with a genuine transitive `Setoid`; the constant-sequence MAP `of` with equality reflection
`of a ≈ of b ↔ a ≈ b` (INJECTIVE mod the setoids — NOT yet isometric or dense); the cofinal-rescheduling
invariance `X ≈ X_{2n+1}`; the rescheduled operations ADDITION (`n ↦ 2n+1`) and NEGATION with their
regularity and congruence; and the additive-group laws modulo completion equivalence — commutativity,
ASSOCIATIVITY, right unit, inverse, and the `of`-homomorphism laws `of_add`/`of_neg`.

ALSO BUILT (the scalar action, complete): SCALAR MULTIPLICATION `dlimCompletionSmul c X` via the
choice-free scalar-dependent affine reschedule `n ↦ scalarSchedule(c)·(n+1)−1` (`scalarSchedule c :=
xBound |c|²`), with regularity from the exact q⁻² modulus attenuation; its vector, scalar, and combined
congruences (so it is a well-defined action of the complex-scalar setoid); the SEVEN complex-module laws
modulo completion equivalence — `one_smul`, `zero_smul`, `smul_zero`, `smul_add`, `add_smul`,
`smul_assoc` — and the `of`-homomorphism law `of_smul`. The completion carrier is therefore a
complex-module modulo `DLimCompletionEq`.

STILL OPEN (next phases, flagged honestly): the completed INNER PRODUCT as a constructive limit
`⟨X,Y⟩ := ClimCore (n ↦ ⟨X_n,Y_n⟩)` (from the clean ζ-free `ComplexLimitCore`, NOT the
`Analysis.ComplexLimit`/`ComplexMod` that transitively reach `Analysis.Zeta`) — which first needs a
constructive complex Cauchy–Schwarz for `dlimInner` and uniform squared-norm bounds to prove the
inner-product sequence regular; the pre-Hilbert/positive-definiteness laws, the explicit completeness
proof, the ACTUAL isometry and density of `of`, continuous coordinate reads, and finally the maximal
weighted domain `D(M_w)` and its self-adjointness. This module is deliberately the completion layer ONLY;
it does NOT name or assert a completed Hilbert space, an operator, or self-adjointness, and it does NOT
extend any operator by continuity.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; the cone is `FinDirectLimit`'s
zeta/crux-free cone. Crux `none`.
-/

import F1Square.Square.FinDirectLimit
import F1Square.Analysis.ComplexNormSqCore
import F1Square.Analysis.RealOrderCore

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

/-- The affine schedule `σ_q(n) = q(n+1)−1` speeds up: `j ≤ σ_q(j)` for `q ≥ 1`. -/
private theorem sched_ge {q : Nat} (hq : 1 ≤ q) (j : Nat) : j ≤ q * (j + 1) - 1 := by
  have hm : j + 1 ≤ q * (j + 1) := Nat.le_mul_of_pos_left (j + 1) hq
  omega

/-- **The affine reschedule** `σ_q(n) = q(n+1)−1` (`q ≥ 1`) as a completion member — the generalization
    of the odd reschedule (`q = 2`) that scalar multiplication needs (with a scalar-DEPENDENT `q`).
    Regular because `M(σ_q j, σ_q k) ≤ M(j,k)` (monotonicity, since `σ_q j ≥ j`). -/
def dlimResched (q : Nat) (hq : 1 ≤ q) (X : DLimCompletionRaw) : DLimCompletionRaw :=
  ⟨fun n => X.seq (q * (n + 1) - 1),
   fun j k => Rle_trans (X.reg (q * (j + 1) - 1) (q * (k + 1) - 1))
     (dlimCauchyMod_mono (sched_ge hq j) (sched_ge hq k))⟩

/-- **AFFINE COFINAL INVARIANCE** (reviewer gate 2, generalized): `X ≈ X_{σ_q(n)}` for every `q ≥ 1`.
    For `n ≥ 4k+3`, `‖X_n − X_{σ_q n}‖² ≤ M(n,σ_q n) ≤ M(n,n) ≤ 4/(n+1) ≤ 1/(k+1)` — the threshold does
    not depend on `q`. -/
theorem dlimResched_eq (q : Nat) (hq : 1 ≤ q) (X : DLimCompletionRaw) :
    DLimCompletionEq X (dlimResched q hq X) := by
  intro k
  refine ⟨4 * k + 3, fun n hn => ?_⟩
  refine Rle_trans (X.reg n (q * (n + 1) - 1)) ?_
  refine Rle_trans (dlimCauchyMod_mono (p := n) (p' := n) (q := n) (q' := q * (n + 1) - 1)
    (Nat.le_refl n) (sched_ge hq n)) ?_
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

/-- **The associativity distance bound, over ABSTRACT points** (no completion nesting, so no whnf
    blow-up): `‖((a₄+y)+z₂) − (a₂+(y+z₄))‖² ≤ 2·‖a₄−a₂‖² + 2·‖z₂−z₄‖²`. With midpoint `(a₂+y)+z₂`, the
    point quasi-triangle plus the two `+`-cancellations (`dlimDist2_add_right`/`_add_left`) split the
    coupled difference into the pure-`a` and pure-`z` shifts; `y` cancels. -/
private theorem assoc_dist_bound (a4 a2 y z2 z4 : DLimRaw) :
    Rle (dlimDist2 (dlimAdd (dlimAdd a4 y) z2) (dlimAdd a2 (dlimAdd y z4)))
      (Radd (Radd (dlimDist2 a4 a2) (dlimDist2 a4 a2))
            (Radd (dlimDist2 z2 z4) (dlimDist2 z2 z4))) := by
  refine Rle_trans (Rle_of_Req (dlimDist2_wd (DLimEq_refl _)
    (DLimEq_symm (dlimAdd_assoc a2 y z4)))) ?_
  refine Rle_trans (dlimDist2_quasitriangle _ (dlimAdd (dlimAdd a2 y) z2) _) ?_
  exact Radd_le_add_loc
    (Radd_le_add_loc
      (Rle_of_Req (Req_trans (dlimDist2_add_right (dlimAdd a4 y) (dlimAdd a2 y) z2)
        (dlimDist2_add_right a4 a2 y)))
      (Rle_of_Req (Req_trans (dlimDist2_add_right (dlimAdd a4 y) (dlimAdd a2 y) z2)
        (dlimDist2_add_right a4 a2 y))))
    (Radd_le_add_loc
      (Rle_of_Req (dlimDist2_add_left z2 z4 (dlimAdd a2 y)))
      (Rle_of_Req (dlimDist2_add_left z2 z4 (dlimAdd a2 y))))

/-- **ASSOCIATIVITY** of completion addition (the last group law): `(X + Y) + Z ≈ X + (Y + Z)`. The two
    sides read `X` at `2(2n+1)+1` vs `2n+1` and `Z` at `2n+1` vs `2(2n+1)+1`; `assoc_dist_bound` reduces
    the distance to `2·d²(X₄,X₂) + 2·d²(Z₂,Z₄)`, each below `1/(4(k+1))` (regularity + monotonicity to the
    diagonal + decay, `n ≥ 8k+7`), collapsing to `1/(k+1)`. The completion nesting is touched only once
    (the boundary unification with `assoc_dist_bound`). -/
theorem dlimCompletionAdd_assoc (X Y Z : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd (dlimCompletionAdd X Y) Z)
      (dlimCompletionAdd X (dlimCompletionAdd Y Z)) := by
  intro k
  refine ⟨8 * k + 7, fun n hn => ?_⟩
  have hbnd : ∀ (W : DLimCompletionRaw) (p q : Nat), 2 * n + 1 ≤ p → 2 * n + 1 ≤ q →
      Rle (dlimDist2 (W.seq p) (W.seq q)) (ofQ (⟨1, (4 * k + 3) + 1⟩ : Q) (Nat.succ_pos _)) :=
    fun W p q hp hq => Rle_trans (W.reg p q)
      (Rle_trans (dlimCauchyMod_mono (p := 2 * n + 1) (p' := p) (q := 2 * n + 1) (q' := q) hp hq)
        (Rle_trans (dlimCauchyMod_diag_decay (2 * n + 1))
          (Rle_ofQ_of_Qle_loc _ _ (by
            show (4 : Int) * (((4 * k + 3) + 1 : Nat) : Int) ≤ (1 : Int) * (((2 * n + 1) + 1 : Nat) : Int)
            push_cast; omega))))
  refine Rle_trans (assoc_dist_bound (X.seq (2 * (2 * n + 1) + 1)) (X.seq (2 * n + 1))
    (Y.seq (2 * (2 * n + 1) + 1)) (Z.seq (2 * n + 1)) (Z.seq (2 * (2 * n + 1) + 1))) ?_
  refine Rle_trans (Radd_le_add_loc
    (Radd_le_add_loc (hbnd X (2 * (2 * n + 1) + 1) (2 * n + 1) (by omega) (by omega))
      (hbnd X (2 * (2 * n + 1) + 1) (2 * n + 1) (by omega) (by omega)))
    (Radd_le_add_loc (hbnd Z (2 * n + 1) (2 * (2 * n + 1) + 1) (by omega) (by omega))
      (hbnd Z (2 * n + 1) (2 * (2 * n + 1) + 1) (by omega) (by omega)))) ?_
  refine Rle_of_Req (Req_trans
    (Req_trans (Radd_congr (Radd_ofQ_loc _ _) (Radd_ofQ_loc _ _)) (Radd_ofQ_loc _ _))
    (ofQ_respects _ (Nat.succ_pos k) ?_))
  simp only [Qeq, add, mul]; push_cast; ring_uor

-- ===========================================================================
-- Raw squared-norm and squared-distance SCALING (reviewer gate 3): ‖c·v‖² ≈ |c|²·‖v‖²
-- and ‖c·a − c·b‖² ≈ |c|²·‖a − b‖². Both are EQUALITIES (no order/monotonicity needed).
-- Uses the clean modulus core `cNormSq`.
-- ===========================================================================

/-- `c · (−b) ≈ −(c · b)` (scalar multiplication commutes with negation). -/
private theorem smul_neg (c : Complex) (b : DLimRaw) :
    DLimEq (dlimSmul c (dlimNeg b)) (dlimNeg (dlimSmul c b)) :=
  DLimEq_trans (dlimSmul_wd (Ceq_refl c) (dlimNeg_eq_smul b))
    (DLimEq_trans (dlimSmul_assoc c (Cneg Cone) b)
      (DLimEq_trans (dlimSmul_wd (Cmul_comm c (Cneg Cone)) (DLimEq_refl b))
        (DLimEq_trans (DLimEq_symm (dlimSmul_assoc (Cneg Cone) c b))
          (DLimEq_symm (dlimNeg_eq_smul (dlimSmul c b))))))

/-- `c·a − c·b ≈ c·(a − b)` (scalar multiplication is additive on the colimit group). -/
private theorem dlimSmul_dlimSub (c : Complex) (a b : DLimRaw) :
    DLimEq (dlimSub (dlimSmul c a) (dlimSmul c b)) (dlimSmul c (dlimSub a b)) :=
  DLimEq_symm (DLimEq_trans (dlimSmul_dlimAdd c a (dlimNeg b))
    (dlimAdd_wd (DLimEq_refl (dlimSmul c a)) (smul_neg c b)))

/-- **Squared-norm scaling** (reviewer gate 3): `‖c · v‖² ≈ |c|² · ‖v‖²`. From
    `⟨c·v, c·v⟩ ≈ (c · conj c) · ⟨v, v⟩` (right-linearity twice + Hermitian symmetry + `Cconj_Cmul`, with
    `⟨v,v⟩` real so `conj⟨v,v⟩ ≈ ⟨v,v⟩`), whose real part is `|c|²·‖v‖²` (`Cmul_Cconj_re`/`Cmul_Cconj_im`
    + `dlimInner_self_im`). -/
theorem dlimNormSq_smul (c : Complex) (v : DLimRaw) :
    Req (dlimNormSq (dlimSmul c v)) (Rmul (cNormSq c) (dlimNormSq v)) := by
  have conj_self_v : Ceq (Cconj (dlimInner v v)) (dlimInner v v) :=
    ⟨Req_refl _, Req_trans (Rneg_congr (dlimInner_self_im v))
      (Req_trans Rneg_zero_loc (Req_symm (dlimInner_self_im v)))⟩
  have step2 : Ceq (dlimInner (dlimSmul c v) v) (Cmul (Cconj c) (dlimInner v v)) :=
    Ceq_trans (dlimInner_conj (dlimSmul c v) v)
      (Ceq_trans (Cconj_congr (dlimInner_smul_right c v v))
        (Ceq_trans (Cconj_Cmul c (dlimInner v v))
          (Cmul_congr (Ceq_refl _) conj_self_v)))
  have key : Ceq (dlimInner (dlimSmul c v) (dlimSmul c v))
      (Cmul (Cmul c (Cconj c)) (dlimInner v v)) :=
    Ceq_trans (dlimInner_smul_right c (dlimSmul c v) v)
      (Ceq_trans (Cmul_congr (Ceq_refl c) step2)
        (Ceq_symm (Cmul_assoc c (Cconj c) (dlimInner v v))))
  refine Req_trans key.1 ?_
  show Req (Rsub (Rmul (Cmul c (Cconj c)).re (dlimInner v v).re)
                 (Rmul (Cmul c (Cconj c)).im (dlimInner v v).im))
           (Rmul (cNormSq c) (dlimInner v v).re)
  refine Req_trans (Rsub_congr (Rmul_congr (Cmul_Cconj_re c) (Req_refl _))
    (Rmul_congr (Cmul_Cconj_im c) (dlimInner_self_im v))) ?_
  exact Req_trans (Rsub_congr (Req_refl _) (Rmul_zero zero))
    (Rsub_zero (Rmul (cNormSq c) (dlimInner v v).re))

/-- **Squared-distance scaling** (reviewer gate 3): `‖c·a − c·b‖² ≈ |c|² · ‖a − b‖²`, via
    `c·a − c·b ≈ c·(a − b)` and squared-norm scaling. -/
theorem dlimDist2_smul (c : Complex) (a b : DLimRaw) :
    Req (dlimDist2 (dlimSmul c a) (dlimSmul c b)) (Rmul (cNormSq c) (dlimDist2 a b)) :=
  Req_trans (dlimNormSq_wd (dlimSmul_dlimSub c a b)) (dlimNormSq_smul c (dlimSub a b))

-- ===========================================================================
-- Real-multiplication MONOTONICITY and the ℝ/ℚ order helpers used below are now imported
-- from the shared ζ-free `Analysis.RealOrderCore` (the extracted real-order core:
-- `Rnonneg_ofQ_loc`, `Rle_ofQ_of_Qle_loc`, `Radd_ofQ_loc`, `Radd_le_add_loc`, `Rmul_ofQ_ofQ_loc`,
-- `Qneg_le_neg_loc`, `mul_lo_core_loc`, `Rnonneg_Rmul_loc`, `Rnonneg_of_Rle_zero_loc`,
-- `Rnonneg_congr_loc`, `Rnonneg_Rsub_of_Rle_loc`, `Rle_of_Rnonneg_Rsub_loc`,
-- `Rmul_le_Rmul_left_loc` / `Rmul_le_Rmul_right_loc`) — no longer copied privately here.
-- ===========================================================================

-- ===========================================================================
-- The exact q⁻² affine-modulus ATTENUATION (reviewer gate 4): a scalar `x ≤ q` scales the
-- affine-rescheduled modulus back under the canonical one — `x · M(σ_q j, σ_q k) ≤ M(j,k)`.
-- ===========================================================================

/-- Abstract core of `M/q ≤ M` for nonnegative `N, D` and `q ≥ 1`: `(1·N)·D ≤ N·(q·D)`. -/
private theorem div_q_le (N D q : Int) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 1 ≤ q) :
    (1 * N) * D ≤ N * (q * D) := by
  have h0 : (0 : Int) ≤ N * D := Int.mul_nonneg hN hD
  have hk := Int.mul_le_mul_of_nonneg_left hq h0
  have e1 : (1 * N) * D = N * D * 1 := by ring_uor
  have e2 : N * (q * D) = N * D * q := by ring_uor
  rw [e1, e2]; exact hk

/-- **The q⁻² attenuation** (reviewer gate 4): for a real `x` with `x ≤ q` and `q ≥ 1`,
    `x · M(σ_q j, σ_q k) ≤ M(j, k)`  where `σ_q(n) = q(n+1)−1`. Since `M(σ_q j, σ_q k) = M(j,k)/q²`, the
    bound `x ≤ q` leaves `x·M(σ_q) ≤ q·(M/q²) = M/q ≤ M`. The `q³·X ≤ q⁴·X` core is exposed by the ℚ
    identity `q·M(σ_q j,σ_q k) ≈ M(j,k)/q` (`ring_uor` after the reschedule denominator `(q(j+1)−1)+1 =
    q(j+1)`), leaving `M/q ≤ M` (`div_q_le`). This is the scalar-multiplication regularity bridge. -/
theorem dlimCauchyMod_atten {x : Real} {q : Nat} (hq : 1 ≤ q)
    (hxq : Rle x (ofQ (⟨(q : Int), 1⟩ : Q) Nat.one_pos)) (j k : Nat) :
    Rle (Rmul x (dlimCauchyModR (q * (j + 1) - 1) (q * (k + 1) - 1))) (dlimCauchyModR j k) := by
  refine Rle_trans (Rmul_le_Rmul_right_loc (dlimCauchyMod_nonneg _ _) hxq) ?_
  unfold dlimCauchyModR
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ_loc _ _)) (Rle_ofQ_of_Qle_loc _ _ ?_)
  have hdj : (q * (j + 1) - 1) + 1 = q * (j + 1) := by
    have h : 0 < q * (j + 1) := Nat.mul_pos (by omega) (by omega); omega
  have hdk : (q * (k + 1) - 1) + 1 = q * (k + 1) := by
    have h : 0 < q * (k + 1) := Nat.mul_pos (by omega) (by omega); omega
  refine Qle_trans (b := mul (⟨1, q⟩ : Q)
      (mul (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))))
    ?hbden ?hqeq ?hle
  · exact Qmul_den_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
      (Qmul_den_pos (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
        (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k)))
  · exact Qeq_le (by simp only [Qeq, mul, add, hdj, hdk]; push_cast; ring_uor)
  · simp only [Qle, mul]; push_cast
    have hSn : (0 : Int) ≤ (1 : Int) * ((k + 1 : Nat) : Int) + 1 * ((j + 1 : Nat) : Int) := by omega
    have hNN : (0 : Int) ≤ ((1 : Int) * ((k + 1 : Nat) : Int) + 1 * ((j + 1 : Nat) : Int))
        * ((1 : Int) * ((k + 1 : Nat) : Int) + 1 * ((j + 1 : Nat) : Int)) := Int.mul_nonneg hSn hSn
    have hAB : (0 : Int) ≤ ((j + 1 : Nat) : Int) * ((k + 1 : Nat) : Int) :=
      Int.mul_nonneg (by omega) (by omega)
    have hDD : (0 : Int) ≤ (((j + 1 : Nat) : Int) * ((k + 1 : Nat) : Int))
        * (((j + 1 : Nat) : Int) * ((k + 1 : Nat) : Int)) := Int.mul_nonneg hAB hAB
    have hq' : (1 : Int) ≤ (q : Int) := by exact_mod_cast hq
    exact div_q_le _ _ _ hNN hDD hq'

-- ===========================================================================
-- SCALAR MULTIPLICATION on completion members (reviewer gate 5). The reschedule factor
-- is the choice-free `scalarSchedule c := xBound |c|²`; regularity chains distance-scaling,
-- `X.reg`, and the q⁻² attenuation.
-- ===========================================================================

/-- **The choice-free scalar reschedule factor** for `c`: `xBound |c|²` (always `≥ 1`). Being a concrete
    `Nat`-valued function of `c` (not an existential witness), it can index a completion sequence. -/
def scalarSchedule (c : Complex) : Nat := xBound (cNormSq c)

/-- `scalarSchedule c ≥ 1` (`xBound` is always positive). -/
theorem one_le_scalarSchedule (c : Complex) : 1 ≤ scalarSchedule c := xBound_pos (cNormSq c)

/-- `|c|² ≤ scalarSchedule c` — the choice-free scalar-magnitude bound (the `∃`-free companion of
    `cNormSq_nat_bound`, with the witness `xBound |c|²` exposed). -/
theorem cNormSq_le_scalarSchedule (c : Complex) :
    Rle (cNormSq c) (ofQ (⟨(scalarSchedule c : Int), 1⟩ : Q) Nat.one_pos) := by
  intro n
  show Qle ((cNormSq c).seq n) (add (⟨(scalarSchedule c : Int), 1⟩ : Q) ⟨2, n + 1⟩)
  have h1 : Qle ((cNormSq c).seq n) (Qabs ((cNormSq c).seq n)) := by
    show ((cNormSq c).seq n).num * ((Qabs ((cNormSq c).seq n)).den : Int)
      ≤ (Qabs ((cNormSq c).seq n)).num * (((cNormSq c).seq n).den : Int)
    simp only [Qabs]
    exact Int.mul_le_mul_of_nonneg_right Int.le_natAbs (by omega)
  have h2 : Qle (Qabs ((cNormSq c).seq n)) (⟨(scalarSchedule c : Int), 1⟩ : Q) :=
    canon_bound (cNormSq c) n
  have h3 : Qle (⟨(scalarSchedule c : Int), 1⟩ : Q)
      (add (⟨(scalarSchedule c : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_self_add (by show (0 : Int) ≤ 2; decide)
  have h23 := Qle_trans (b := (⟨(scalarSchedule c : Int), 1⟩ : Q))
    (by show (0 : Nat) < 1; decide) h2 h3
  exact Qle_trans (b := Qabs ((cNormSq c).seq n)) ((cNormSq c).den_pos n) h1 h23

/-- **SCALAR MULTIPLICATION** of a completion member (reviewer gate 5): `c · X`, rescheduled by
    `σ_{scalarSchedule c}` so the `|c|²`-inflation is attenuated back under the canonical modulus.
    Regular because `‖c·X_{σj} − c·X_{σk}‖² = |c|²·‖X_{σj} − X_{σk}‖² ≤ |c|²·M(σj,σk) ≤ M(j,k)`
    (distance scaling + `X.reg` + `dlimCauchyMod_atten`, with `|c|² ≤ scalarSchedule c`). -/
def dlimCompletionSmul (c : Complex) (X : DLimCompletionRaw) : DLimCompletionRaw :=
  ⟨fun n => dlimSmul c (X.seq (scalarSchedule c * (n + 1) - 1)),
   fun j k =>
     Rle_trans (Rle_of_Req (dlimDist2_smul c (X.seq (scalarSchedule c * (j + 1) - 1))
       (X.seq (scalarSchedule c * (k + 1) - 1))))
       (Rle_trans (Rmul_le_Rmul_left_loc (cNormSq_nonneg c)
         (X.reg (scalarSchedule c * (j + 1) - 1) (scalarSchedule c * (k + 1) - 1)))
         (dlimCauchyMod_atten (one_le_scalarSchedule c) (cNormSq_le_scalarSchedule c) j k))⟩

/-- **Schedule composition** (reviewer gate 5): `σ_r(σ_q(n)) = σ_{r·q}(n)` — composing affine reschedules
    multiplies their factors. The tool for the common-refinement congruence. -/
theorem sched_comp (q r n : Nat) (hq : 1 ≤ q) :
    r * ((q * (n + 1) - 1) + 1) - 1 = (r * q) * (n + 1) - 1 := by
  have h1 : (q * (n + 1) - 1) + 1 = q * (n + 1) := by
    have : 0 < q * (n + 1) := Nat.mul_pos (by omega) (by omega); omega
  rw [h1, Nat.mul_assoc]

/-- **Vector congruence** of scalar multiplication (reviewer gate 6): `X ≈ Y ⟹ c·X ≈ c·Y`. Same
    reschedule, so `‖c·X_σn − c·Y_σn‖² = |c|²·‖X_σn − Y_σn‖² ≤ (scalarSchedule c)·‖X_σn − Y_σn‖²`, and
    driving `‖X_σn − Y_σn‖² ≤ 1/(B(k+1))` (level `B(k+1)−1`, `B = scalarSchedule c`) collapses the `B`. -/
theorem dlimCompletionSmul_congr_vec {c : Complex} {X Y : DLimCompletionRaw}
    (h : DLimCompletionEq X Y) :
    DLimCompletionEq (dlimCompletionSmul c X) (dlimCompletionSmul c Y) := by
  intro k
  obtain ⟨N, hN⟩ := h (scalarSchedule c * (k + 1) - 1)
  refine ⟨N, fun n hn => ?_⟩
  have hσ : N ≤ scalarSchedule c * (n + 1) - 1 :=
    Nat.le_trans hn (sched_ge (one_le_scalarSchedule c) n)
  refine Rle_trans (Rle_of_Req (dlimDist2_smul c (X.seq (scalarSchedule c * (n + 1) - 1))
    (Y.seq (scalarSchedule c * (n + 1) - 1)))) ?_
  refine Rle_trans (Rmul_le_Rmul_right_loc (dlimDist2_nonneg _ _) (cNormSq_le_scalarSchedule c)) ?_
  refine Rle_trans (Rmul_le_Rmul_left_loc
    (Rnonneg_ofQ_loc Nat.one_pos (by show (0 : Int) ≤ (scalarSchedule c : Int); omega))
    (hN (scalarSchedule c * (n + 1) - 1) hσ)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ_loc _ _)) (Rle_ofQ_of_Qle_loc _ _ ?_)
  have h1 : (scalarSchedule c * (k + 1) - 1) + 1 = scalarSchedule c * (k + 1) := by
    have : 0 < scalarSchedule c * (k + 1) :=
      Nat.mul_pos (one_le_scalarSchedule c) (by omega); omega
  exact Qeq_le (by simp only [Qeq, mul, h1]; push_cast; ring_uor)

/-- **Scalar congruence** of scalar multiplication (reviewer gate 6): `Ceq c c' ⟹ c·X ≈ c'·X`.
    This is what makes `dlimCompletionSmul` a well-defined action of the complex-scalar setoid.
    Because `c` and `c'` carry DIFFERENT reschedule factors `q = scalarSchedule c`, `r = scalarSchedule c'`,
    the two sides are aligned by a COMMON REFINEMENT: reschedule `c·X` by `r` and `c'·X` by `q`, landing
    both at index `σ_{qr}(n)` (`sched_comp` collapses the composed affine schedules, `Nat.mul_comm` matches
    `qr = rq`). There the SAME colimit vector `X_{σ_{qr}(n)}` is scaled by `c` on one side and `c'` on the
    other, so raw `dlimSmul_wd hc` closes it stagewise; cofinal invariance (`dlimResched_eq`) bridges each
    side to its unrescheduled form. NO scalar-difference estimate or uniform-norm bound is needed. -/
theorem dlimCompletionSmul_congr_scalar {c c' : Complex} {X : DLimCompletionRaw} (hc : Ceq c c') :
    DLimCompletionEq (dlimCompletionSmul c X) (dlimCompletionSmul c' X) := by
  have hq : 1 ≤ scalarSchedule c := one_le_scalarSchedule c
  have hr : 1 ≤ scalarSchedule c' := one_le_scalarSchedule c'
  refine DLimCompletionEq_trans
    (dlimResched_eq (scalarSchedule c') hr (dlimCompletionSmul c X)) ?_
  refine DLimCompletionEq_trans ?_
    (DLimCompletionEq_symm (dlimResched_eq (scalarSchedule c) hq (dlimCompletionSmul c' X)))
  refine DLimCompletionEq_of_pointwise (fun n => ?_)
  show DLimEq (dlimSmul c (X.seq (scalarSchedule c * ((scalarSchedule c' * (n + 1) - 1) + 1) - 1)))
    (dlimSmul c' (X.seq (scalarSchedule c' * ((scalarSchedule c * (n + 1) - 1) + 1) - 1)))
  have hAB : scalarSchedule c * ((scalarSchedule c' * (n + 1) - 1) + 1) - 1
      = scalarSchedule c' * ((scalarSchedule c * (n + 1) - 1) + 1) - 1 := by
    rw [sched_comp (scalarSchedule c') (scalarSchedule c) n hr,
      sched_comp (scalarSchedule c) (scalarSchedule c') n hq,
      Nat.mul_comm (scalarSchedule c') (scalarSchedule c)]
  rw [hAB]
  exact dlimSmul_wd hc (DLimEq_refl _)

/-- **Combined (two-argument) congruence** of scalar multiplication: `c ≈ c'` and `X ≈ Y` together give
    `c·X ≈ c'·Y`. Compose the vector congruence (`c·X ≈ c·Y`) with the scalar congruence (`c·Y ≈ c'·Y`). -/
theorem dlimCompletionSmul_congr {c c' : Complex} {X Y : DLimCompletionRaw}
    (hc : Ceq c c') (hXY : DLimCompletionEq X Y) :
    DLimCompletionEq (dlimCompletionSmul c X) (dlimCompletionSmul c' Y) :=
  DLimCompletionEq_trans (dlimCompletionSmul_congr_vec hXY) (dlimCompletionSmul_congr_scalar hc)

-- ===========================================================================
-- COMPLEX-MODULE LAWS on the completion (reviewer gate 6). Each law bridges its two sides — which carry
-- DIFFERENT reschedule factors — by a common affine refinement, applying the raw colimit scalar law
-- (`dlimSmul_one` / `dlimZero_smul` / `dlimSmul_zero` / `dlimSmul_dlimAdd` / `dlimSmul_Cadd` /
-- `dlimSmul_assoc`) stagewise at the aligned index. No completed-inner-product estimates are used.
-- ===========================================================================

/-- **The reschedule-alignment combinator**: to prove `Z1 ≈ Z2` it suffices to give affine factors `α,β ≥ 1`
    and a stagewise `DLimEq` between `Z1` rescheduled by `α` and `Z2` rescheduled by `β` — cofinal
    invariance (`dlimResched_eq`) bridges each side to its reschedule. This is the workhorse for the module
    laws whose two sides only agree after a common refinement of their scalar schedules. -/
private theorem completion_eq_via_resched {Z1 Z2 : DLimCompletionRaw} {α β : Nat}
    (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (h : ∀ n, DLimEq (Z1.seq (α * (n + 1) - 1)) (Z2.seq (β * (n + 1) - 1))) :
    DLimCompletionEq Z1 Z2 :=
  DLimCompletionEq_trans (dlimResched_eq α hα Z1)
    (DLimCompletionEq_trans
      (DLimCompletionEq_of_pointwise (X := dlimResched α hα Z1) (Y := dlimResched β hβ Z2) h)
      (DLimCompletionEq_symm (dlimResched_eq β hβ Z2)))

/-- **`1·X ≈ X`** (`one_smul`). Stagewise `dlimSmul_one` gives `Cone·X ≈ X_{σ_B}`; cofinal invariance closes. -/
theorem dlimCompletionSmul_one (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSmul Cone X) X :=
  DLimCompletionEq_trans (Y := dlimResched (scalarSchedule Cone) (one_le_scalarSchedule Cone) X)
    (DLimCompletionEq_of_pointwise
      (fun n => dlimSmul_one (X.seq (scalarSchedule Cone * (n + 1) - 1))))
    (DLimCompletionEq_symm (dlimResched_eq (scalarSchedule Cone) (one_le_scalarSchedule Cone) X))

/-- **`0·X ≈ 0`** (`zero_smul`). Stagewise `dlimZero_smul`; the completion zero is the constant `0`. -/
theorem dlimCompletionZero_smul (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSmul Czero X) dlimCompletionZero :=
  DLimCompletionEq_of_pointwise
    (fun n => dlimZero_smul (X.seq (scalarSchedule Czero * (n + 1) - 1)))

/-- **`c·0 ≈ 0`** (`smul_zero`). Stagewise `dlimSmul_zero` (the reschedule of the constant `0` is `0`). -/
theorem dlimCompletionSmul_zero (c : Complex) :
    DLimCompletionEq (dlimCompletionSmul c dlimCompletionZero) dlimCompletionZero :=
  DLimCompletionEq_of_pointwise (fun _ => dlimSmul_zero c)

/-- **`of` commutes with scalar multiplication** (`of_smul`): `c · (of a) ≈ of (c·a)`. Both sides are the
    constant sequence `c·a` (a reschedule of a constant is itself), so this is stagewise reflexivity. -/
theorem DLimCompletionEq_of_smul (c : Complex) (a : DLimRaw) :
    DLimCompletionEq (dlimCompletionSmul c (DLimCompletionRaw.of a))
      (DLimCompletionRaw.of (dlimSmul c a)) :=
  DLimCompletionEq_of_pointwise (fun _ => DLimEq_refl (dlimSmul c a))

/-- **`c·(X + Y) ≈ c·X + c·Y`** (`smul_add`). Both sides are stagewise equal at index `n` after matching the
    two composed schedules `σ_2 ∘ σ_{B_c}` and `σ_{B_c} ∘ σ_2` (which share the factor `2·B_c`), then applying
    the raw distributivity `dlimSmul_dlimAdd`. -/
theorem dlimCompletionSmul_add (c : Complex) (X Y : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSmul c (dlimCompletionAdd X Y))
      (dlimCompletionAdd (dlimCompletionSmul c X) (dlimCompletionSmul c Y)) :=
  DLimCompletionEq_of_pointwise (fun n => by
    show DLimEq
      (dlimSmul c (dlimAdd (X.seq (2 * (scalarSchedule c * (n + 1) - 1) + 1))
        (Y.seq (2 * (scalarSchedule c * (n + 1) - 1) + 1))))
      (dlimAdd (dlimSmul c (X.seq (scalarSchedule c * ((2 * n + 1) + 1) - 1)))
        (dlimSmul c (Y.seq (scalarSchedule c * ((2 * n + 1) + 1) - 1))))
    have hpos : 0 < scalarSchedule c * (n + 1) :=
      Nat.mul_pos (one_le_scalarSchedule c) (Nat.succ_pos n)
    have e0 : (2 * n + 1) + 1 = 2 * (n + 1) := by omega
    have e1 : scalarSchedule c * ((2 * n + 1) + 1) = 2 * (scalarSchedule c * (n + 1)) := by
      rw [e0, Nat.mul_left_comm]
    have key : 2 * (scalarSchedule c * (n + 1) - 1) + 1 = scalarSchedule c * ((2 * n + 1) + 1) - 1 := by
      rw [e1]; omega
    rw [key]
    exact dlimSmul_dlimAdd c (X.seq (scalarSchedule c * ((2 * n + 1) + 1) - 1))
      (Y.seq (scalarSchedule c * ((2 * n + 1) + 1) - 1)))

/-- **`(c + d)·X ≈ c·X + d·X`** (`add_smul`). The two summands `c·X`, `d·X` carry different factors `B_c`,
    `B_d`; reschedule each so both use `B_c·B_d` (`dlimCompletionAdd_congr` + cofinal invariance), landing
    their colimit vectors at a COMMON index, where the raw `dlimSmul_Cadd` recombines `c·v + d·v` into
    `(c+d)·v`. A final common refinement (`completion_eq_via_resched`) matches that against `(c+d)·X`. -/
theorem dlimCompletionSmul_Cadd (c d : Complex) (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSmul (Cadd c d) X)
      (dlimCompletionAdd (dlimCompletionSmul c X) (dlimCompletionSmul d X)) := by
  have hq_c : 1 ≤ scalarSchedule c := one_le_scalarSchedule c
  have hq_d : 1 ≤ scalarSchedule d := one_le_scalarSchedule d
  have hq_s : 1 ≤ scalarSchedule (Cadd c d) := one_le_scalarSchedule (Cadd c d)
  refine DLimCompletionEq_trans ?_
    (DLimCompletionEq_symm (dlimCompletionAdd_congr
      (dlimResched_eq (scalarSchedule d) hq_d (dlimCompletionSmul c X))
      (dlimResched_eq (scalarSchedule c) hq_c (dlimCompletionSmul d X))))
  refine completion_eq_via_resched (α := 2 * (scalarSchedule c * scalarSchedule d))
    (β := scalarSchedule (Cadd c d))
    (Nat.mul_pos (by omega) (Nat.mul_pos hq_c hq_d)) hq_s (fun n => ?_)
  dsimp only [dlimCompletionSmul, dlimCompletionAdd, dlimResched, DLimCompletionRaw.seq]
  have hP : 0 < scalarSchedule (Cadd c d) * (n + 1) := Nat.mul_pos hq_s (Nat.succ_pos n)
  have e1 : 2 * (scalarSchedule (Cadd c d) * (n + 1) - 1) + 1 + 1
      = 2 * (scalarSchedule (Cadd c d) * (n + 1)) := by omega
  have e3 : 2 * (scalarSchedule c * scalarSchedule d) * (n + 1) - 1 + 1
      = 2 * (scalarSchedule c * scalarSchedule d) * (n + 1) := by
    have : 0 < 2 * (scalarSchedule c * scalarSchedule d) * (n + 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (Nat.mul_pos hq_c hq_d)) (Nat.succ_pos n)
    omega
  have hA : scalarSchedule c *
        (scalarSchedule d * (2 * (scalarSchedule (Cadd c d) * (n + 1) - 1) + 1 + 1) - 1 + 1) - 1
      = scalarSchedule (Cadd c d) *
        (2 * (scalarSchedule c * scalarSchedule d) * (n + 1) - 1 + 1) - 1 := by
    rw [e1]
    have e2 : scalarSchedule d * (2 * (scalarSchedule (Cadd c d) * (n + 1))) - 1 + 1
        = scalarSchedule d * (2 * (scalarSchedule (Cadd c d) * (n + 1))) := by
      have : 0 < scalarSchedule d * (2 * (scalarSchedule (Cadd c d) * (n + 1))) :=
        Nat.mul_pos hq_d (Nat.mul_pos (by omega) hP)
      omega
    rw [e2, e3,
      show scalarSchedule c * (scalarSchedule d * (2 * (scalarSchedule (Cadd c d) * (n + 1))))
         = scalarSchedule (Cadd c d) * (2 * (scalarSchedule c * scalarSchedule d) * (n + 1)) from by
        ac_rfl]
  have hB : scalarSchedule d *
        (scalarSchedule c * (2 * (scalarSchedule (Cadd c d) * (n + 1) - 1) + 1 + 1) - 1 + 1) - 1
      = scalarSchedule (Cadd c d) *
        (2 * (scalarSchedule c * scalarSchedule d) * (n + 1) - 1 + 1) - 1 := by
    rw [e1]
    have e2 : scalarSchedule c * (2 * (scalarSchedule (Cadd c d) * (n + 1))) - 1 + 1
        = scalarSchedule c * (2 * (scalarSchedule (Cadd c d) * (n + 1))) := by
      have : 0 < scalarSchedule c * (2 * (scalarSchedule (Cadd c d) * (n + 1))) :=
        Nat.mul_pos hq_c (Nat.mul_pos (by omega) hP)
      omega
    rw [e2, e3,
      show scalarSchedule d * (scalarSchedule c * (2 * (scalarSchedule (Cadd c d) * (n + 1))))
         = scalarSchedule (Cadd c d) * (2 * (scalarSchedule c * scalarSchedule d) * (n + 1)) from by
        ac_rfl]
  rw [hA, hB]
  exact dlimSmul_Cadd c d (X.seq (scalarSchedule (Cadd c d) *
    (2 * (scalarSchedule c * scalarSchedule d) * (n + 1) - 1 + 1) - 1))

/-- **`c·(d·X) ≈ (c·d)·X`** (`smul_assoc`). After a common refinement of the three factors `B_c`, `B_d`,
    `B_{cd}`, the raw `dlimSmul_assoc` collapses the nested scaling `c·(d·v)` to `(c·d)·v` at the aligned
    colimit vector; `sched_comp` + `ac_rfl` match the composed schedules. -/
theorem dlimCompletionSmul_assoc (c d : Complex) (X : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSmul c (dlimCompletionSmul d X))
      (dlimCompletionSmul (Cmul c d) X) := by
  have hq_c : 1 ≤ scalarSchedule c := one_le_scalarSchedule c
  have hq_e : 1 ≤ scalarSchedule (Cmul c d) := one_le_scalarSchedule (Cmul c d)
  have hβ : 1 ≤ scalarSchedule d * scalarSchedule c :=
    Nat.mul_pos (one_le_scalarSchedule d) hq_c
  refine completion_eq_via_resched (α := scalarSchedule (Cmul c d))
    (β := scalarSchedule d * scalarSchedule c) hq_e hβ (fun n => ?_)
  refine DLimEq_trans (dlimSmul_assoc c d
    (X.seq (scalarSchedule d * ((scalarSchedule c *
      ((scalarSchedule (Cmul c d) * (n + 1) - 1) + 1) - 1) + 1) - 1))) ?_
  have hidx : scalarSchedule d * ((scalarSchedule c *
        ((scalarSchedule (Cmul c d) * (n + 1) - 1) + 1) - 1) + 1) - 1
      = scalarSchedule (Cmul c d) *
        (((scalarSchedule d * scalarSchedule c) * (n + 1) - 1) + 1) - 1 := by
    rw [sched_comp (scalarSchedule (Cmul c d)) (scalarSchedule c) n hq_e,
        sched_comp (scalarSchedule c * scalarSchedule (Cmul c d)) (scalarSchedule d) n
          (Nat.mul_pos hq_c hq_e),
        sched_comp (scalarSchedule d * scalarSchedule c) (scalarSchedule (Cmul c d)) n hβ,
        show scalarSchedule d * (scalarSchedule c * scalarSchedule (Cmul c d))
           = scalarSchedule (Cmul c d) * (scalarSchedule d * scalarSchedule c) from by ac_rfl]
  rw [hidx]
  exact DLimEq_refl _

-- ===========================================================================
-- TOWARD THE COMPLETED INNER PRODUCT (reviewer gate: the completed inner product
-- `⟨X,Y⟩ := ClimCore (n ↦ ⟨Xₙ,Yₙ⟩)`). This section builds the four analytic foundations the
-- inner-product-sequence REGULARITY needs — all ζ-free, sqrt-free:
--   • subtraction bilinearity of `dlimInner` (for the difference split);
--   • the AM-GM/polarization core `2λ·Re⟨u,v⟩ ≤ ‖u‖² + λ²‖v‖²` (the constructive complex
--     Cauchy–Schwarz seed — NO sqrt, NO discriminant);
--   • the positive-rational left-cancellation for `Rle` (isolates the first-order term by dividing
--     through by `2λ`, done by multiplying by the rational inverse — NO `Pos`-chain, NO sqrt-monotone);
--   • the choice-free uniform squared-norm bound `‖Xₙ‖² ≤ normBound X` for a completion representative.
-- ===========================================================================

/-- **Subtraction bilinearity (left slot)**: `⟨a − b, c⟩ ≈ ⟨a,c⟩ − ⟨b,c⟩`. -/
theorem dlimInner_sub_left (a b c : DLimRaw) :
    Ceq (dlimInner (dlimSub a b) c) (Cadd (dlimInner a c) (Cneg (dlimInner b c))) :=
  Ceq_trans (dlimInner_add_left a (dlimNeg b) c)
    (Cadd_congr (Ceq_refl (dlimInner a c)) (dlimInner_neg_left b c))

/-- **Subtraction bilinearity (right slot)**: `⟨a, b − c⟩ ≈ ⟨a,b⟩ − ⟨a,c⟩`. -/
theorem dlimInner_sub_right (a b c : DLimRaw) :
    Ceq (dlimInner a (dlimSub b c)) (Cadd (dlimInner a b) (Cneg (dlimInner a c))) :=
  Ceq_trans (dlimInner_add_right a b (dlimNeg c))
    (Cadd_congr (Ceq_refl (dlimInner a b)) (dlimInner_neg_right a c))

/-- **The AM-GM / polarization core** — the constructive, sqrt-free complex Cauchy–Schwarz seed: for any
    rational scalar `lam`, `2·lam·Re⟨u,v⟩ ≤ ‖u‖² + lam²·‖v‖²`. Proof is `‖u − lam·v‖² ≥ 0`
    (`dlimNormSq_nonneg`) expanded by the sesquilinear/parallelogram laws (`dlimNormSq_add`,
    `dlimNormSq_smul`). Holds for EVERY `lam` (no sign hypothesis) — the polarization identity is unsigned. -/
theorem dlimInner_re_amgm {lam : Q} (hlam : 0 < lam.den) (u v : DLimRaw) :
    Rle (Rmul (Radd (ofQ lam hlam) (ofQ lam hlam)) (dlimInner u v).re)
        (Radd (dlimNormSq u) (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v))) := by
  have hz : Req (Rmul zero (dlimInner u v).im) zero :=
    Req_trans (Rmul_comm zero (dlimInner u v).im) (Rmul_zero (dlimInner u v).im)
  have hcmulre :
      Req (Cmul (⟨ofQ lam hlam, zero⟩ : Complex) (dlimInner u v)).re
          (Rmul (ofQ lam hlam) (dlimInner u v).re) := by
    show Req (Rsub (Rmul (ofQ lam hlam) (dlimInner u v).re) (Rmul zero (dlimInner u v).im))
             (Rmul (ofQ lam hlam) (dlimInner u v).re)
    exact Req_trans (Rsub_congr (Req_refl _) hz) (Rsub_zero _)
  have haInneruX :
      Req (dlimInner u (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)).re
          (Rmul (ofQ lam hlam) (dlimInner u v).re) :=
    Req_trans (dlimInner_smul_right (⟨ofQ lam hlam, zero⟩ : Complex) u v).1 hcmulre
  have haInnerXu :
      Req (dlimInner (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v) u).re
          (Rmul (ofQ lam hlam) (dlimInner u v).re) :=
    Req_trans (dlimInner_conj (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v) u).1 haInneruX
  have haA :
      Req (dlimInner (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)) u).re
          (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re)) :=
    Req_trans (dlimInner_neg_left (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v) u).1
      (Rneg_congr haInnerXu)
  have haB :
      Req (dlimInner u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))).re
          (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re)) :=
    Req_trans (dlimInner_neg_right u (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)).1
      (Rneg_congr haInneruX)
  have hcnsq :
      Req (cNormSq (⟨ofQ lam hlam, zero⟩ : Complex))
          (Rmul (ofQ lam hlam) (ofQ lam hlam)) := by
    show Req (Radd (Rmul (ofQ lam hlam) (ofQ lam hlam)) (Rmul zero zero))
             (Rmul (ofQ lam hlam) (ofQ lam hlam))
    exact Req_trans (Radd_congr (Req_refl _) (Rmul_zero zero)) (Radd_zero _)
  have haC :
      Req (dlimNormSq (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)))
          (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v)) :=
    Req_trans (dlimNormSq_neg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))
      (Req_trans (dlimNormSq_smul (⟨ofQ lam hlam, zero⟩ : Complex) v)
        (Rmul_congr hcnsq (Req_refl (dlimNormSq v))))
  have expand :
      Req (dlimNormSq (dlimAdd u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))))
          (Radd (Radd (dlimNormSq u)
                  (dlimInner (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)) u).re)
                (Radd (dlimInner u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))).re
                  (dlimNormSq (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))))) :=
    dlimNormSq_add u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))
  have hbig :
      Req (dlimNormSq (dlimAdd u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v))))
          (Radd (Radd (dlimNormSq u) (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re)))
                (Radd (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re))
                  (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v)))) :=
    Req_trans expand
      (Radd_congr (Radd_congr (Req_refl (dlimNormSq u)) haA) (Radd_congr haB haC))
  have hdist :
      Req (Rmul (Radd (ofQ lam hlam) (ofQ lam hlam)) (dlimInner u v).re)
          (Radd (Rmul (ofQ lam hlam) (dlimInner u v).re)
                (Rmul (ofQ lam hlam) (dlimInner u v).re)) :=
    Rmul_distrib_right (ofQ lam hlam) (ofQ lam hlam) (dlimInner u v).re
  have hfinal :
      Req (Radd (Radd (dlimNormSq u) (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re)))
                (Radd (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re))
                  (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v))))
          (Rsub (Radd (dlimNormSq u)
                  (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v)))
                (Rmul (Radd (ofQ lam hlam) (ofQ lam hlam)) (dlimInner u v).re)) :=
    Req_trans
      (Radd_congr (Req_refl _)
        (Radd_comm (Rneg (Rmul (ofQ lam hlam) (dlimInner u v).re))
          (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v))))
      (Req_trans
        (Req_symm (Rsub_Radd_Radd (dlimNormSq u)
          (Rmul (Rmul (ofQ lam hlam) (ofQ lam hlam)) (dlimNormSq v))
          (Rmul (ofQ lam hlam) (dlimInner u v).re)
          (Rmul (ofQ lam hlam) (dlimInner u v).re)))
        (Rsub_congr (Req_refl _) (Req_symm hdist)))
  have hnn : Rnonneg (dlimNormSq (dlimAdd u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)))) :=
    dlimNormSq_nonneg (dlimAdd u (dlimNeg (dlimSmul (⟨ofQ lam hlam, zero⟩ : Complex) v)))
  exact Rle_of_Rnonneg_Rsub_loc (Rnonneg_congr_loc (Req_trans hbig hfinal) hnn)

/-- `ofQ cinv · (ofQ c · X) ≈ X` when `cinv · c = 1` (`one` is `ofQ ⟨1,1⟩`, so the bridge is by `rfl`
    on the constant sequence). -/
private theorem cancel_simp {c cinv : Q} (hc : 0 < c.den) (hci : 0 < cinv.den)
    (hprod : Qeq (mul cinv c) (⟨1, 1⟩ : Q)) (X : Real) :
    Req (Rmul (ofQ cinv hci) (Rmul (ofQ c hc) X)) X :=
  Req_trans (Req_symm (Rmul_assoc (ofQ cinv hci) (ofQ c hc) X))
    (Req_trans (Rmul_congr (Rmul_ofQ_ofQ_loc hci hc) (Req_refl X))
      (Req_trans (Rmul_congr (Req_of_seq_Qeq (y := one) (fun _ => hprod)) (Req_refl X))
        (Req_trans (Rmul_comm one X) (Rmul_one X))))

/-- **Positive-rational left-cancellation for `Rle`**: a common positive rational factor `c` may be
    cancelled by its inverse `cinv` (with `cinv · c = 1`). The sqrt-free "divide the AM-GM by `2λ`" step —
    it multiplies through by the rational inverse, using only `Rmul` monotonicity, NO `Pos`/√ machinery. -/
theorem Rmul_le_cancel_ofQ {c cinv : Q} (hc : 0 < c.den) (hci : 0 < cinv.den)
    (hcinv_nn : 0 ≤ cinv.num) (hprod : Qeq (mul cinv c) (⟨1, 1⟩ : Q))
    {A B : Real} (h : Rle (Rmul (ofQ c hc) A) (Rmul (ofQ c hc) B)) : Rle A B :=
  Rle_trans (Rle_of_Req (Req_symm (cancel_simp hc hci hprod A)))
    (Rle_trans (Rmul_le_Rmul_left_loc (Rnonneg_ofQ_loc hci hcinv_nn) h)
      (Rle_of_Req (cancel_simp hc hci hprod B)))

/-- `−0 ≈ 0` in the colimit (both are the empty-stage zero vector). -/
private theorem dlimNeg_zero_eq : DLimEq (dlimNeg dlimZero) dlimZero :=
  ⟨0, Nat.le_refl _, Nat.le_refl _, fun i => i.elim0⟩

/-- `‖a − 0‖² ≈ ‖a‖²` — the squared distance to the colimit zero is the squared norm. -/
private theorem dlimDist2_zero_eq (a : DLimRaw) :
    Req (dlimDist2 a dlimZero) (dlimNormSq a) :=
  dlimNormSq_wd (DLimEq_trans (dlimAdd_wd (DLimEq_refl a) dlimNeg_zero_eq) (dlimAdd_zero a))

/-- `M(n,0) = (1/(n+1)+1)² ≤ 4`. -/
private theorem dlimCauchyMod_n0_bound (n : Nat) :
    Rle (dlimCauchyModR n 0) (ofQ (⟨4, 1⟩ : Q) Nat.one_pos) := by
  unfold dlimCauchyModR
  apply Rle_ofQ_of_Qle_loc _ Nat.one_pos
  refine Qle_congr_left
    (a := (⟨((n : Int) + 2) * ((n : Int) + 2), (n + 1) * (n + 1)⟩ : Q)) ?_ ?_ ?_
  · exact Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)
  · simp only [Qeq, mul, add]; push_cast; ring_uor
  · show ((n : Int) + 2) * ((n : Int) + 2) * ((1 : Nat) : Int)
        ≤ (4 : Int) * (((n + 1) * (n + 1) : Nat) : Int)
    push_cast
    have hkey : (0 : Int) ≤ 4 * (((n : Int) + 1) * ((n : Int) + 1))
        - ((n : Int) + 2) * ((n : Int) + 2) := by
      have e : 4 * (((n : Int) + 1) * ((n : Int) + 1))
          - ((n : Int) + 2) * ((n : Int) + 2) = (n : Int) * (3 * (n : Int) + 4) := by ring_uor
      rw [e]; exact Int.mul_nonneg (by omega) (by omega)
    omega

/-- `x ≤ xBound x` (the explicit choice-free Archimedean bound — the witness of `exists_nat_ge_loc`,
    exposed so the uniform norm factor can be a computable function of the representative). -/
theorem Rle_ofQ_xBound (x : Real) : Rle x (ofQ (⟨(xBound x : Int), 1⟩ : Q) Nat.one_pos) := by
  intro n
  show Qle (x.seq n) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩)
  have h1 : Qle (x.seq n) (Qabs (x.seq n)) := by
    show (x.seq n).num * ((Qabs (x.seq n)).den : Int) ≤ (Qabs (x.seq n)).num * ((x.seq n).den : Int)
    simp only [Qabs]
    exact Int.mul_le_mul_of_nonneg_right Int.le_natAbs (by omega)
  have h2 : Qle (Qabs (x.seq n)) (⟨(xBound x : Int), 1⟩ : Q) := canon_bound x n
  have h3 : Qle (⟨(xBound x : Int), 1⟩ : Q) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_self_add (by show (0 : Int) ≤ 2; decide)
  have h23 : Qle (Qabs (x.seq n)) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_trans (b := (⟨(xBound x : Int), 1⟩ : Q)) (by show (0 : Nat) < 1; decide) h2 h3
  exact Qle_trans (b := Qabs (x.seq n)) (x.den_pos n) h1 h23

/-- **The choice-free uniform squared-norm bound factor** for a completion representative:
    `8 + 2·xBound ‖X₀‖²`. Being a computable `Nat`-valued function of `X` (not an `∃`-witness), it can
    parametrize the inner-product-sequence reschedule. -/
def normBound (X : DLimCompletionRaw) : Nat := 8 + 2 * xBound (dlimNormSq (X.seq 0))

/-- **Uniform squared-norm bound**: `‖Xₙ‖² ≤ normBound X` for every `n`. Quasi-triangle:
    `‖Xₙ‖² = ‖Xₙ − 0‖² ≤ 2‖Xₙ − X₀‖² + 2‖X₀ − 0‖² ≤ 2·M(n,0) + 2‖X₀‖² ≤ 8 + 2·xBound‖X₀‖²`. -/
theorem normBound_spec (X : DLimCompletionRaw) (n : Nat) :
    Rle (dlimNormSq (X.seq n)) (ofQ (⟨(normBound X : Int), 1⟩ : Q) Nat.one_pos) := by
  have hd_n0 : Rle (dlimDist2 (X.seq n) (X.seq 0)) (ofQ (⟨4, 1⟩ : Q) Nat.one_pos) :=
    Rle_trans (X.reg n 0) (dlimCauchyMod_n0_bound n)
  have hd_0z : Rle (dlimDist2 (X.seq 0) dlimZero)
      (ofQ (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q) Nat.one_pos) :=
    Rle_trans (Rle_of_Req (dlimDist2_zero_eq (X.seq 0))) (Rle_ofQ_xBound (dlimNormSq (X.seq 0)))
  have hsumle :
      Rle (Radd (Radd (dlimDist2 (X.seq n) (X.seq 0)) (dlimDist2 (X.seq n) (X.seq 0)))
                (Radd (dlimDist2 (X.seq 0) dlimZero) (dlimDist2 (X.seq 0) dlimZero)))
          (Radd (Radd (ofQ (⟨4, 1⟩ : Q) Nat.one_pos) (ofQ (⟨4, 1⟩ : Q) Nat.one_pos))
                (Radd (ofQ (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q) Nat.one_pos)
                      (ofQ (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q) Nat.one_pos))) :=
    Radd_le_add_loc (Radd_le_add_loc hd_n0 hd_n0) (Radd_le_add_loc hd_0z hd_0z)
  have hqeq : Qeq (add (add (⟨4, 1⟩ : Q) (⟨4, 1⟩ : Q))
                       (add (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q)
                            (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q)))
                  (⟨(normBound X : Int), 1⟩ : Q) := by
    simp only [normBound, Qeq, add]; push_cast; ring_uor
  have hsum_eq :
      Req (Radd (Radd (ofQ (⟨4, 1⟩ : Q) Nat.one_pos) (ofQ (⟨4, 1⟩ : Q) Nat.one_pos))
                (Radd (ofQ (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q) Nat.one_pos)
                      (ofQ (⟨(xBound (dlimNormSq (X.seq 0)) : Int), 1⟩ : Q) Nat.one_pos)))
          (ofQ (⟨(normBound X : Int), 1⟩ : Q) Nat.one_pos) :=
    Req_trans
      (Radd_congr (Radd_ofQ_loc Nat.one_pos Nat.one_pos) (Radd_ofQ_loc Nat.one_pos Nat.one_pos))
      (Req_trans (Radd_ofQ_loc (add_den_pos Nat.one_pos Nat.one_pos)
                               (add_den_pos Nat.one_pos Nat.one_pos))
        (ofQ_respects _ Nat.one_pos hqeq))
  refine Rle_trans (Rle_of_Req (Req_symm (dlimDist2_zero_eq (X.seq n)))) ?_
  refine Rle_trans (dlimDist2_quasitriangle (X.seq n) (X.seq 0) dlimZero) ?_
  exact Rle_trans hsumle (Rle_of_Req hsum_eq)

/-- **Uniform squared-norm bound (`∃` form)**: `∃ B, ∀ n, ‖Xₙ‖² ≤ B` — the choice-free `normBound`
    witnesses it. -/
theorem dlimNormSq_uniform_bound (X : DLimCompletionRaw) :
    ∃ B : Nat, ∀ n : Nat, Rle (dlimNormSq (X.seq n)) (ofQ (⟨(B : Int), 1⟩ : Q) Nat.one_pos) :=
  ⟨normBound X, normBound_spec X⟩

-- ===========================================================================
-- THE SINGLE-TERM CAUCHY–SCHWARZ BOUND (reused once per split term, four times total across the two
-- coordinates): if `‖u‖² ≤ e²` and `‖v‖² ≤ B` then `Re⟨u,v⟩ ≤ e·(1+B)/2`. Assembled from the AM-GM
-- core (`dlimInner_re_amgm`) — divide by `2e` via the rational-inverse cancellation. The perfect-square
-- modulus `M(j,k) = (1/(j+1)+1/(k+1))²` means `‖u‖² ≤ M(σj,σk)` IS the hypothesis `‖u‖² ≤ e²` with
-- `e = 1/(σj+1)+1/(σk+1)`, so no `√` is ever taken.
-- ===========================================================================

/-- `(1/a)·a = 1` as a ℚ-value equality for `a` with positive numerator (the inverse written inline as its
    definitional form `⟨a.den, a.num.toNat⟩`, i.e. `Qinv a`). -/
private theorem Qinv_mul_self {a : Q} (ha : 0 < a.num) :
    Qeq (mul (⟨(a.den : Int), a.num.toNat⟩ : Q) a) (⟨1, 1⟩ : Q) := by
  have ht : (a.num.toNat : Int) = a.num := Int.toNat_of_nonneg (by omega)
  simp only [Qeq, mul]
  push_cast
  rw [ht, Int.mul_one, Int.one_mul, Int.mul_comm]

/-- **The single-term Cauchy–Schwarz bound** — the reusable heart of inner-product regularity:
    if `‖u‖² ≤ e²` and `‖v‖² ≤ B` (positive rational `e`, `Nat` `B`), then `Re⟨u,v⟩ ≤ e·(1+B)/2`.
    Sqrt-free: AM-GM gives `2e·Re⟨u,v⟩ ≤ ‖u‖² + e²‖v‖² ≤ e²(1+B)`, then divide by `2e`
    (`Rmul_le_cancel_ofQ`). NO discriminant, NO sqrt-monotonicity. -/
theorem dlimInner_re_termBound {e : Q} (hed : 0 < e.den) (hen : 0 < e.num) (B : Nat)
    (u v : DLimRaw)
    (hu : Rle (dlimNormSq u) (ofQ (mul e e) (Qmul_den_pos hed hed)))
    (hv : Rle (dlimNormSq v) (ofQ (⟨(B : Int), 1⟩ : Q) Nat.one_pos)) :
    Rle (dlimInner u v).re
      (ofQ (⟨e.num * (1 + (B : Int)), e.den * 2⟩ : Q) (Nat.mul_pos hed (by decide))) := by
  have heed : 0 < (mul e e).den := Qmul_den_pos hed hed
  have hEBd : 0 < (mul (mul e e) (⟨(B : Int), 1⟩ : Q)).den := Qmul_den_pos heed Nat.one_pos
  have hDd : 0 < (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q))).den :=
    add_den_pos heed hEBd
  have hcd : 0 < (add e e).den := add_den_pos hed hed
  have hbd : 0 < (⟨e.num * (1 + (B : Int)), e.den * 2⟩ : Q).den := Nat.mul_pos hed (by decide)
  have hee_nn : (0 : Int) ≤ (mul e e).num :=
    Int.mul_nonneg (by omega) (by omega)
  have amgm := dlimInner_re_amgm hed u v
  have term2bound :
      Rle (Rmul (Rmul (ofQ e hed) (ofQ e hed)) (dlimNormSq v))
          (ofQ (mul (mul e e) (⟨(B : Int), 1⟩ : Q)) hEBd) :=
    Rle_trans
      (Rle_of_Req (Rmul_congr (Rmul_ofQ_ofQ_loc hed hed) (Req_refl (dlimNormSq v))))
      (Rle_trans
        (Rmul_le_Rmul_left_loc (Rnonneg_ofQ_loc heed hee_nn) hv)
        (Rle_of_Req (Rmul_ofQ_ofQ_loc heed Nat.one_pos)))
  have rhsbound :
      Rle (Radd (dlimNormSq u) (Rmul (Rmul (ofQ e hed) (ofQ e hed)) (dlimNormSq v)))
          (ofQ (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q))) hDd) :=
    Rle_trans (Radd_le_add_loc hu term2bound) (Rle_of_Req (Radd_ofQ_loc heed hEBd))
  have amgmChain :
      Rle (Rmul (Radd (ofQ e hed) (ofQ e hed)) (dlimInner u v).re)
          (ofQ (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q))) hDd) :=
    Rle_trans amgm rhsbound
  have step3 :
      Rle (Rmul (ofQ (add e e) hcd) (dlimInner u v).re)
          (ofQ (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q))) hDd) :=
    Rle_trans
      (Rle_of_Req (Req_symm (Rmul_congr (Radd_ofQ_loc hed hed)
        (Req_refl (dlimInner u v).re))))
      amgmChain
  have hqeq :
      Qeq (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q)))
          (mul (add e e) (⟨e.num * (1 + (B : Int)), e.den * 2⟩ : Q)) := by
    simp only [Qeq, mul, add]; push_cast; ring_uor
  have hDeq :
      Req (ofQ (add (mul e e) (mul (mul e e) (⟨(B : Int), 1⟩ : Q))) hDd)
          (Rmul (ofQ (add e e) hcd)
                (ofQ (⟨e.num * (1 + (B : Int)), e.den * 2⟩ : Q) hbd)) :=
    Req_trans (ofQ_respects hDd (Qmul_den_pos hcd hbd) hqeq)
      (Req_symm (Rmul_ofQ_ofQ_loc hcd hbd))
  have step4 :
      Rle (Rmul (ofQ (add e e) hcd) (dlimInner u v).re)
          (Rmul (ofQ (add e e) hcd)
                (ofQ (⟨e.num * (1 + (B : Int)), e.den * 2⟩ : Q) hbd)) :=
    Rle_trans step3 (Rle_of_Req hDeq)
  have hdI : (0 : Int) < (e.den : Int) := by exact_mod_cast hed
  have hcnum : 0 < (add e e).num := by
    show 0 < e.num * (e.den : Int) + e.num * (e.den : Int)
    have hp : 0 < e.num * (e.den : Int) := Int.mul_pos hen hdI
    omega
  have hcid : 0 < (⟨((add e e).den : Int), (add e e).num.toNat⟩ : Q).den := by
    show 0 < (add e e).num.toNat
    omega
  have hcinv_nn : (0 : Int) ≤ (⟨((add e e).den : Int), (add e e).num.toNat⟩ : Q).num := by
    show (0 : Int) ≤ ((add e e).den : Int)
    omega
  exact Rmul_le_cancel_ofQ hcd hcid hcinv_nn (Qinv_mul_self hcnum) step4

-- ===========================================================================
-- IMAGINARY-COORDINATE REDUCTION: `Im⟨u,v⟩ = Re⟨u, (−i)·v⟩` and `‖(−i)·v‖² = ‖v‖²`, so the single-term
-- bound above covers the imaginary coordinate of the inner-product sequence verbatim (apply it with `v`
-- replaced by `(−i)·v`).
-- ===========================================================================

/-- The scalar `−i` as a `Complex` literal. -/
def NEGI : Complex := ⟨zero, Rneg one⟩

/-- `0 + x ≈ x`. -/
private theorem zero_Radd_loc (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- **`Im⟨u,v⟩ = Re⟨u, (−i)·v⟩`** — the imaginary part is a real part after the `−i` twist. -/
theorem dlimInner_im_eq_re (u v : DLimRaw) :
    Req (dlimInner u v).im (dlimInner u (dlimSmul NEGI v)).re := by
  have h1 := (dlimInner_smul_right NEGI u v).1
  have stepA : Req (Rmul zero (dlimInner u v).re) zero :=
    Req_trans (Rmul_comm zero (dlimInner u v).re) (Rmul_zero (dlimInner u v).re)
  have stepB : Req (Rmul (Rneg one) (dlimInner u v).im) (Rneg (dlimInner u v).im) :=
    Req_trans (Rmul_neg_left one (dlimInner u v).im)
      (Rneg_congr (Req_trans (Rmul_comm one (dlimInner u v).im) (Rmul_one (dlimInner u v).im)))
  have key : Req (Cmul NEGI (dlimInner u v)).re (dlimInner u v).im := by
    show Req (Rsub (Rmul zero (dlimInner u v).re) (Rmul (Rneg one) (dlimInner u v).im))
              (dlimInner u v).im
    refine Req_trans (Rsub_congr stepA stepB) ?_
    exact Req_trans (Radd_congr (Req_refl zero) (Rneg_Rneg_loc (dlimInner u v).im))
      (zero_Radd_loc (dlimInner u v).im)
  exact Req_symm (Req_trans h1 key)

/-- **`‖(−i)·v‖² = ‖v‖²`** (`|−i|² = 1`), so the `−i` twist preserves the norm bound. -/
theorem dlimNormSq_smul_negI (v : DLimRaw) :
    Req (dlimNormSq (dlimSmul NEGI v)) (dlimNormSq v) := by
  have hsq : Req (Rmul (Rneg one) (Rneg one)) one :=
    Req_trans (Rmul_neg_left one (Rneg one))
      (Req_trans (Rneg_congr (Req_trans (Rmul_comm one (Rneg one)) (Rmul_one (Rneg one))))
        (Rneg_Rneg_loc one))
  have hcn : Req (cNormSq NEGI) one := by
    show Req (Radd (Rmul zero zero) (Rmul (Rneg one) (Rneg one))) one
    exact Req_trans (Radd_congr (Rmul_zero zero) hsq) (zero_Radd_loc one)
  exact Req_trans (dlimNormSq_smul NEGI v)
    (Req_trans (Rmul_congr hcn (Req_refl (dlimNormSq v)))
      (Req_trans (Rmul_comm one (dlimNormSq v)) (Rmul_one (dlimNormSq v))))

end UOR.Bridge.F1Square.Square
