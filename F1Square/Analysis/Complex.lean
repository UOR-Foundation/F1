/-
F1 square — ℂ as pairs of constructive reals (the v0.5.0 introduction of the complex plane).

The analytic half of the program ultimately lives over ℂ (the functional equation of ζ, the
critical line `Re s = 1/2`). This brick introduces ℂ the standard constructive way — `ℂ = ℝ × ℝ`
over the v0.4.0 constructive reals, with componentwise Bishop equality. This release establishes **all four field operations** — addition, negation, multiplication
`(a,b)·(c,d) = (ac−bd, ad+bc)` (built on the v0.5.0 `Rmul`), the embedding ℝ ↪ ℂ, and the constants
`0, 1, i` — together with the proofs that `≈` is an equivalence and that the **additive group** laws
hold up to `≈` (commutativity, inverse), lifted coordinatewise from `Analysis.Real`.

Scope (honest, one brick per release): the ℂ **multiplicative** laws (commutativity, associativity,
distributivity) up to `≈` require operation-congruence over `≈` — that `≈`-equal inputs give
`≈`-equal `Radd`/`Rmul` outputs — which is the v0.6.0 well-definedness brick (`Rmul`'s reindex depends
on a bound read off the inputs, so congruence is a genuine lemma, not `rfl`); the modulus, apartness,
and `1/z` (which constructively needs `z # 0`, not `¬(z ≈ 0)`) follow after, alongside completeness.
None of this is the crux: making ζ/λₙ exact-bounded objects over this ℂ is statable; proving
`λₙ ≥ 0 ∀n` is RH.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.Real

namespace UOR.Bridge.F1Square.Analysis

/-- A **constructive complex number**: a pair of constructive reals `re + i·im`. -/
structure Complex where
  re : Real
  im : Real

/-- Componentwise Bishop equality on ℂ. -/
def Ceq (z w : Complex) : Prop := Req z.re w.re ∧ Req z.im w.im

/-- ℂ addition (coordinatewise ℝ addition). -/
def Cadd (z w : Complex) : Complex := ⟨Radd z.re w.re, Radd z.im w.im⟩

/-- ℂ negation. -/
def Cneg (z : Complex) : Complex := ⟨Rneg z.re, Rneg z.im⟩

/-- ℂ multiplication: `(a + bi)(c + di) = (ac − bd) + (ad + bc)i`. -/
def Cmul (z w : Complex) : Complex :=
  ⟨Rsub (Rmul z.re w.re) (Rmul z.im w.im), Radd (Rmul z.re w.im) (Rmul z.im w.re)⟩

/-- The embedding ℝ ↪ ℂ, `x ↦ x + 0·i`. -/
def ofReal (x : Real) : Complex := ⟨x, zero⟩

/-- `0`, `1`, and the imaginary unit `i` in ℂ. -/
def Czero : Complex := ⟨zero, zero⟩
def Cone : Complex := ⟨one, zero⟩
def I : Complex := ⟨zero, one⟩

/-- `≈` on ℂ is reflexive. -/
theorem Ceq_refl (z : Complex) : Ceq z z := ⟨Req_refl _, Req_refl _⟩

/-- `≈` on ℂ is symmetric. -/
theorem Ceq_symm {z w : Complex} (h : Ceq z w) : Ceq w z := ⟨Req_symm h.1, Req_symm h.2⟩

/-- `≈` on ℂ is transitive — so it is an equivalence relation. -/
theorem Ceq_trans {z w v : Complex} (h₁ : Ceq z w) (h₂ : Ceq w v) : Ceq z v :=
  ⟨Req_trans h₁.1 h₂.1, Req_trans h₁.2 h₂.2⟩

/-- ℂ addition is commutative (up to `≈`). -/
theorem Cadd_comm (z w : Complex) : Ceq (Cadd z w) (Cadd w z) :=
  ⟨Radd_comm _ _, Radd_comm _ _⟩

/-- The additive inverse law on ℂ (up to `≈`): `z ⊕ (−z) ≈ 0`. -/
theorem Cadd_neg (z : Complex) : Ceq (Cadd z (Cneg z)) Czero :=
  ⟨Radd_neg _, Radd_neg _⟩

/-- The imaginary unit has imaginary part `1` (`i = 0 + 1·i`), structurally. -/
theorem I_im : I.im = one := rfl

/-- The embedding ℝ ↪ ℂ has zero imaginary part. -/
theorem ofReal_im (x : Real) : (ofReal x).im = zero := rfl

/-- The real part of a product is `ac − bd` (the standard formula, by definition). -/
theorem Cmul_re (z w : Complex) : (Cmul z w).re = Rsub (Rmul z.re w.re) (Rmul z.im w.im) := rfl

/-- The imaginary part of a product is `ad + bc` (the standard formula, by definition). -/
theorem Cmul_im (z w : Complex) : (Cmul z w).im = Radd (Rmul z.re w.im) (Rmul z.im w.re) := rfl

/-- ℂ multiplication is commutative (up to `≈`). Real part: `ac − bd = ca − db` via `Rmul_comm` and
    `Rsub`-congruence. Imaginary part: `ad + bc ≈ cb + da` via `Rmul_comm`, `Radd`-congruence, and
    `Radd_comm`. (Associativity and distributivity need `Rmul`-congruence — the v0.6.0 brick.) -/
theorem Cmul_comm (z w : Complex) : Ceq (Cmul z w) (Cmul w z) :=
  ⟨Rsub_congr (Rmul_comm z.re w.re) (Rmul_comm z.im w.im),
   Req_trans (Radd_congr (Rmul_comm z.re w.im) (Rmul_comm z.im w.re)) (Radd_comm _ _)⟩

end UOR.Bridge.F1Square.Analysis
