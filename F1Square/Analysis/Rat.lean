/-
F1 square — the first analysis brick: exact rationals ℚ, built the UOR way (Thrust C).

Per the standing directive, the analytic substrate is built from first principles on the UOR
pattern (canonical form + exact arithmetic + realization), NOT imported from Mathlib. This is brick
one: exact rationals from ℤ, whose **canonical form is reduce-to-lowest-terms** — ℚ's content-address
(the uor-addr κ, one level down): two fractions mean the same number iff they share a canonical form.
Pure Lean 4, no Mathlib, no `sorry`.

Scope (honest): the TYPE, the OPERATIONS, the canonical form, and DECIDABLE exact equality/order are
built and verified; these already give exact cycle-means and exact signature comparisons. The
*general* field axioms and general idempotence of `reduce` need a commutative-ring normalizer for ℤ
(there is no `ring` tactic without Mathlib) — that normalizer is itself a UOR-consistent analysis
tool and is the first task of the v0.3.0 analysis work. Here the laws are verified concretely.

Roadmap (one brick per release): ℚ (here) → constructive ℝ (Cauchy-with-modulus / intervals) → ℂ +
transcendentals (exp/log/cos via convergent series with rigorous error bounds) → ζ and λₙ as
exact-bounded objects. Each brick makes more of the analytic half statable and checkable — never the
crux (proving `λₙ ≥ 0 ∀n` / the Hodge index on 𝕊 is RH).
-/

namespace UOR.Bridge.F1Square.Analysis

/-- A rational as a raw fraction `num / den` (denominator intended `> 0`). -/
structure Q where
  num : Int
  den : Nat
deriving DecidableEq, Repr

/-- Cross-multiplication equality: `a/b = c/d ⟺ a·d = c·b`. -/
def Qeq (a b : Q) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)

instance (a b : Q) : Decidable (Qeq a b) := by unfold Qeq; infer_instance

/-- Order: `a/b ≤ c/d ⟺ a·d ≤ c·b` (for positive denominators). -/
def Qle (a b : Q) : Prop := a.num * (b.den : Int) ≤ b.num * (a.den : Int)

instance (a b : Q) : Decidable (Qle a b) := by unfold Qle; infer_instance

/-- Addition `a/b + c/d = (ad + cb)/(bd)`. -/
def add (a b : Q) : Q := ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den⟩

/-- Multiplication `a/b · c/d = (ac)/(bd)`. -/
def mul (a b : Q) : Q := ⟨a.num * b.num, a.den * b.den⟩

/-- Negation. -/
def neg (a : Q) : Q := ⟨-a.num, a.den⟩

/-- The canonical form: reduce to lowest terms via `gcd` — ℚ's content-address. -/
def reduce (a : Q) : Q :=
  let g : Nat := Nat.gcd a.num.natAbs a.den
  if g = 0 then ⟨0, 1⟩ else ⟨a.num / (g : Int), a.den / g⟩

-- General, reachable without a ring normalizer:

/-- `Qeq` is reflexive. -/
theorem Qeq_refl (a : Q) : Qeq a a := rfl

/-- `Qeq` is symmetric. -/
theorem Qeq_symm {a b : Q} (h : Qeq a b) : Qeq b a := h.symm

-- Concrete verification of the canonical form (= content-address) and the operations:

/-- `6/8` reduces to its canonical form `3/4`. -/
theorem reduce_6_8 : reduce ⟨6, 8⟩ = ⟨3, 4⟩ := by decide

/-- The canonical form is IDEMPOTENT — the ℚ analogue of the κ-idempotence (R2). -/
theorem reduce_idem : reduce (reduce ⟨6, 8⟩) = reduce ⟨6, 8⟩ := by decide
theorem reduce_idem_neg : reduce (reduce ⟨-12, 18⟩) = reduce ⟨-12, 18⟩ := by decide

/-- Reduction preserves the value (`Qeq`). -/
theorem reduce_preserves_value : Qeq (reduce ⟨6, 8⟩) ⟨6, 8⟩ := by decide

/-- Same meaning ⟺ same canonical address (the content-address property), on a sample. -/
theorem same_address_iff_eq :
    (reduce ⟨2, 4⟩ = reduce ⟨3, 6⟩) ∧ Qeq ⟨2, 4⟩ ⟨3, 6⟩ := by decide

/-- `1/2 + 1/3 = 5/6` (exact). -/
theorem add_sample : reduce (add ⟨1, 2⟩ ⟨1, 3⟩) = ⟨5, 6⟩ := by decide

/-- `2/3 · 3/4 = 1/2` (exact). -/
theorem mul_sample : reduce (mul ⟨2, 3⟩ ⟨3, 4⟩) = ⟨1, 2⟩ := by decide

/-- Exact order: `1/3 ≤ 1/2`. -/
theorem Qle_sample : Qle ⟨1, 3⟩ ⟨1, 2⟩ := by decide

end UOR.Bridge.F1Square.Analysis
