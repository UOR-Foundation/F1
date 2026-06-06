/-
F1 square — the second analysis brick: constructive ℝ as Bishop regular sequences over our exact ℚ
(the v0.3.0 continuation of the analysis roadmap).

Per the standing directive, the analytic substrate is built from first principles the UOR way. Brick
one was exact ℚ (`Analysis.Rat`); this is brick two: the real numbers as **regular sequences of
rationals** (Bishop), the constructive encoding that bakes the modulus of convergence into the data
so no choice principle is needed:

  a sequence `x : ℕ → ℚ` is *regular* iff `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`.

The index *is* the modulus. A real number is a regular sequence; equality is the (undecidable, but
Prop-valued) Bishop relation `x ≈ y  ⟺  |xₙ − yₙ| ≤ 2/(n+1) ∀ n`; positivity is the witnessed
`∃ n, xₙ > 1/(n+1)`. This is the standard no-Mathlib encoding (cf. Bishop–Bridges; the Agda
constructive-analysis development arXiv:2205.08354).

Scope (honest, one brick per release): this release establishes the TYPE, the regularity predicate,
the order/positivity predicates, the canonical embedding ℚ ↪ ℝ (proved regular and value-respecting),
and the equality setoid's reflexivity and symmetry. Field ARITHMETIC on ℝ (`+`, `·` with their
reindexing-and-regularity proofs, which need the ℚ triangle inequality and `Qle` monotonicity) and
the completeness/limit lemmas (including `≈`-transitivity, which is a genuine limiting argument) are
the v0.4.0 continuation — they need a small library of ℚ order lemmas built on the v0.3.0 ring
normalizer. None of this is the crux: making ζ/λₙ exact-bounded objects is statable here; proving
`λₙ ≥ 0 ∀n` is RH.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Rat

namespace UOR.Bridge.F1Square.Analysis

/-- Subtraction on ℚ: `a − b := a + (−b)`. -/
def Qsub (a b : Q) : Q := add a (neg b)

/-- Absolute value on ℚ: keep the denominator, take `|numerator|`. -/
def Qabs (a : Q) : Q := ⟨(a.num.natAbs : Int), a.den⟩

/-- Strict order on ℚ: `a < b ⟺ a·d_b < b·d_a`. -/
def Qlt (a b : Q) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)

instance (a b : Q) : Decidable (Qlt a b) := by unfold Qlt; infer_instance

/-- The modulus rational `1/(n+1) > 0` — both the regularity bound and the positivity threshold. -/
def Qbound (n : Nat) : Q := ⟨1, n + 1⟩

/-- The numerator of `a − a` is `0` (exact cancellation; via the additive structure). -/
theorem Qsub_self_num (a : Q) : (Qsub a a).num = 0 := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul]; omega

/-- `b − a` has the negated numerator of `a − b`. -/
theorem Qsub_swap_num (a b : Q) : (Qsub b a).num = -(Qsub a b).num := by
  simp only [Qsub, add, neg]; rw [Int.neg_mul, Int.neg_mul]; omega

/-- `b − a` and `a − b` share a denominator (it is `dₐ·d_b` either way). -/
theorem Qsub_swap_den (a b : Q) : (Qsub b a).den = (Qsub a b).den := by
  simp only [Qsub, add, neg]; exact Nat.mul_comm b.den a.den

/-- **Regularity** (Bishop): `|xₘ − xₙ| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`. -/
def IsRegular (x : Nat → Q) : Prop :=
  ∀ m n : Nat, Qle (Qabs (Qsub (x m) (x n))) (add (Qbound m) (Qbound n))

/-- A **constructive real number**: a regular sequence of rationals. -/
structure Real where
  seq : Nat → Q
  reg : IsRegular seq

/-- The constant sequence at `q` is regular (its gaps are `0 ≤` a positive bound). -/
theorem const_regular (q : Q) : IsRegular (fun _ => q) := by
  intro m n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  -- 0 ≤ (1/(m+1) + 1/(n+1)).num · (denominator)
  have hden : (0 : Int) ≤ ((Qsub q q).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (Qbound m) (Qbound n)).num := by
    simp only [add, Qbound]; omega
  exact Int.mul_nonneg hnum hden

/-- The canonical embedding ℚ ↪ ℝ as the constant sequence. -/
def ofQ (q : Q) : Real := ⟨fun _ => q, const_regular q⟩

/-- Zero and one in ℝ. -/
def zero : Real := ofQ ⟨0, 1⟩
def one : Real := ofQ ⟨1, 1⟩

/-- **Bishop equality** on ℝ: `x ≈ y ⟺ |xₙ − yₙ| ≤ 2/(n+1)` for all `n`. -/
def Req (x y : Real) : Prop :=
  ∀ n : Nat, Qle (Qabs (Qsub (x.seq n) (y.seq n))) ⟨2, n + 1⟩

/-- `≈` is reflexive. -/
theorem Req_refl (x : Real) : Req x x := by
  intro n
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (x.seq n) (x.seq n)).den : Int) := Int.ofNat_nonneg _
  omega

/-- `≈` is symmetric (`|xₙ − yₙ| = |yₙ − xₙ|`). -/
theorem Req_symm {x y : Real} (h : Req x y) : Req y x := by
  intro n
  have hnum := Qsub_swap_num (x.seq n) (y.seq n)
  have hden := Qsub_swap_den (x.seq n) (y.seq n)
  have hx := h n
  unfold Qle Qabs at hx ⊢
  rw [hnum, Int.natAbs_neg, hden]
  exact hx

/-- The embedding respects ℚ value-equality: `q = r` (as rationals) ⟹ `ofQ q ≈ ofQ r`. -/
theorem ofQ_respects {q r : Q} (h : Qeq q r) : Req (ofQ q) (ofQ r) := by
  intro n
  unfold Qle Qabs ofQ
  simp only
  -- |q − r| = 0 since q = r (value), so ≤ 2/(n+1)
  have h0 : (Qsub q r).num = 0 := by
    simp only [Qsub, add, neg]; rw [Int.neg_mul]
    have := h; unfold Qeq at this; omega
  rw [h0]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub q r).den : Int) := Int.ofNat_nonneg _
  omega

/-- **Positivity** (Bishop): `x > 0 ⟺ ∃ n, xₙ > 1/(n+1)`. -/
def Pos (x : Real) : Prop := ∃ n : Nat, Qlt (Qbound n) (x.seq n)

/-- `1/2`, as a constructive real. -/
def half : Real := ofQ ⟨1, 2⟩

/-- `half` is positive — witnessed at `n = 2` (`1/3 < 1/2`). -/
theorem Pos_half : Pos half := ⟨2, by decide⟩

end UOR.Bridge.F1Square.Analysis
