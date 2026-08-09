/-
F1 square — the **Hilbert–Pólya NOMINAL contract** (the QUARANTINED shadow API), stated as named
obligations over an abstract bundle (the zeta-FREE layer).

★ QUARANTINE NOTICE. Every predicate in this file now carries a `Nominal` prefix, because on the
axiom-free `HilbertPolyaSpec` bundle these are the STATED EQUATIONS ONLY, not the operator-theoretic
notions their bare names would claim. `zeroBundle_NominalSelfAdjoint` PROVES the degenerate
`inner ≡ 0` bundle satisfies `NominalSelfAdjoint`, so — for instance — `NominalEssSelfAdjoint :=
NominalSymmetric ∧ NominalClosable` does NOT denote essential self-adjointness and must never be read
as such. The genuine operator theory (a real complex inner-product space with sesquilinear
positive-definite pairing, a completion, a densely-defined operator with a genuine adjoint domain and
self-adjoint closure, and an Atlas-derived generator with a noncircular zero correspondence) is being
built as a SEPARATE, honestly-named programme, starting from `FinInnerProduct.lean`; this file is the
target contract that construction must eventually discharge, kept only as a checklist and explicitly
NOT as evidence.

The Hilbert–Pólya heuristic asks for a self-adjoint operator whose spectrum is the imaginary parts
`μ` of the nontrivial zeros `ρ = ½ + iμ`; self-adjointness forces `μ` real, hence `Re ρ = ½`. The
`Nominal*` predicates below name the pieces such an operator must satisfy — a dense domain, symmetry,
the adjoint-domain equality, closability/closedness, essential/actual self-adjointness, a reversible
(Stone-type) flow, and the transform `μ ↦ ½ + iμ` — WITHOUT asserting that any concrete bundle
discharges them, and without pretending the abstract bundle has the structure the words require.

What IS proved here is purely structural and honestly named: the canonical Frobenius/orbit action of
the operator on a chosen basis is the free `H¹` action (`specMap_orbit`, via
`Cohomology.H1_universal`). The bridge to the actual zeros lives in the SEPARATE
`HilbertPolyaBridge`; nothing in this file touches `RiemannZero`.

FENCE. This is the zeta-free layer: its transitive import cone is free of the RH-bearing zeta and
its zero/Li/spectral stack. Pure Lean 4 core, no Mathlib, no `sorry`, choice-free. Crux fields `none`.
-/

import F1Square.Square.Cohomology
import F1Square.Analysis.Complex
import F1Square.Analysis.ROrder

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The Hilbert–Pólya bundle** — DATA ONLY, no axioms. A carrier `H` with a pairing
    `inner : H → H → ℝ`, a domain predicate, and maps `op`/`adj`. **CAVEAT: `H` has no vector-space
    structure and `inner` satisfies no inner-product laws** (no bilinearity, symmetry, or
    positive-definiteness), so the `Nominal*` predicates below are the stated equations, NOT the
    operator-theoretic notions — `zeroBundle_NominalSelfAdjoint` proves `inner ≡ 0` satisfies
    `NominalSelfAdjoint`. The genuine object (with those axioms and completeness) is the separate
    programme begun in `FinInnerProduct.lean`. -/
structure HilbertPolyaSpec where
  /-- the carrier (the abstract Hilbert space) -/
  H : Type
  /-- the (real) pairing `⟨x, y⟩` (NO inner-product axioms are imposed) -/
  inner : H → H → Real
  /-- the operator domain `D(op)` -/
  dom : H → Prop
  /-- the (unbounded) operator -/
  op : H → H
  /-- the formal adjoint -/
  adj : H → H

/-- Utility (NOT a contract predicate): `a` and `b` agree to within `1/(n+1)`. The abs-free rendering
    of `|a − b| ≤ 1/(n+1)` as `a − b ≤ 1/(n+1) ∧ b − a ≤ 1/(n+1)` (`Rabs` lives outside this file's
    minimal zeta-free import cone). The index `n` is the Bishop modulus. -/
def RcloseN (a b : Real) (n : Nat) : Prop :=
  Rle (Rsub a b) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)) ∧
  Rle (Rsub b a) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))

/-- NOMINAL OBLIGATION — **dense domain** (name in quarantine): for every `y` and precision `1/(n+1)`
    there is a domain `x` whose pairing `⟨x, y⟩` approximates `⟨y, y⟩`. On the axiom-free bundle this
    is the stated equation only, not genuine density; NOT discharged here. -/
def NominalDense (K : HilbertPolyaSpec) : Prop :=
  ∀ y : K.H, ∀ n : Nat, ∃ x : K.H, K.dom x ∧ RcloseN (K.inner x y) (K.inner y y) n

/-- NOMINAL OBLIGATION — **symmetry equation** `⟨op x, y⟩ = ⟨x, op y⟩` on `D(op)`. A genuine `Prop`
    over the bundle, but with no inner-product axioms it is not operator symmetry; NOT discharged. -/
def NominalSymmetric (K : HilbertPolyaSpec) : Prop :=
  ∀ x y : K.H, K.dom x → K.dom y → Req (K.inner (K.op x) y) (K.inner x (K.op y))

/-- NOMINAL OBLIGATION — **the adjoint-domain equation** `D(op) = D(op*)`: `x ∈ D(op)` iff for every
    domain `y` the identity `⟨op y, x⟩ = ⟨y, adj x⟩` holds. Nominal only (no adjoint theory backs it);
    NOT discharged. -/
def NominalAdjointDomainEq (K : HilbertPolyaSpec) : Prop :=
  ∀ x : K.H, K.dom x ↔ (∀ y : K.H, K.dom y → Req (K.inner (K.op y) x) (K.inner y (K.adj x)))

/-- NOMINAL OBLIGATION — **graph closability**, written through pairings: if for every precision a
    domain `x` is norm-negligible (`⟨x, x⟩ ≤ 1/(n+1)`) yet its image pairs like a fixed `w`, then `w`
    is null. Nominal only; NOT discharged. -/
def NominalClosable (K : HilbertPolyaSpec) : Prop :=
  ∀ w : K.H,
    (∀ n : Nat, ∃ x : K.H, K.dom x ∧
      Rle (K.inner x x) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)) ∧
      ∀ z : K.H, RcloseN (K.inner (K.op x) z) (K.inner w z) n) →
    ∀ z : K.H, Req (K.inner w z) zero

/-- NOMINAL OBLIGATION — **graph closedness**, written through pairings: weak limits of graph points
    stay in the graph. Nominal only; NOT discharged. -/
def NominalClosed (K : HilbertPolyaSpec) : Prop :=
  ∀ u w : K.H,
    (∀ n : Nat, ∃ x : K.H, K.dom x ∧
      ∀ z : K.H, RcloseN (K.inner x z) (K.inner u z) n ∧ RcloseN (K.inner (K.op x) z) (K.inner w z) n) →
    K.dom u ∧ ∀ z : K.H, Req (K.inner (K.op u) z) (K.inner w z)

/-- NOMINAL OBLIGATION — the conjunction `NominalSymmetric ∧ NominalClosable`. **This is NOT essential
    self-adjointness** (the reason the name is quarantined): the bundle carries no inner-product
    axioms, so both conjuncts are stated equations and `zeroBundle_NominalSelfAdjoint` makes the
    vacuity kernel-explicit. -/
def NominalEssSelfAdjoint (K : HilbertPolyaSpec) : Prop := NominalSymmetric K ∧ NominalClosable K

/-- NOMINAL OBLIGATION — the conjunction `NominalSymmetric ∧ NominalClosed ∧ NominalAdjointDomainEq`.
    **This does NOT denote self-adjointness**: on the axiom-free bundle the clauses are the stated
    equations only, and `zeroBundle_NominalSelfAdjoint` proves the degenerate `inner ≡ 0` bundle
    satisfies it. Read it as "these three equations hold", never as "the operator is self-adjoint". -/
def NominalSelfAdjoint (K : HilbertPolyaSpec) : Prop :=
  NominalSymmetric K ∧ NominalClosed K ∧ NominalAdjointDomainEq K

-- ===========================================================================
-- The `Nominal*` names do NOT denote their operator-theoretic meaning: on the
-- axiom-free bundle they are vacuous. Kernel-proven witness.
-- ===========================================================================

/-- A DEGENERATE bundle with `inner ≡ 0`: carrier `Nat`, zero pairing, full domain, `op = adj = id`.
    It is NOT an inner-product space — positive-definiteness fails (`⟨x,x⟩ = 0` for every `x`) — but
    the axiom-free `HilbertPolyaSpec` admits it, which is exactly why the bare predicate names cannot
    be trusted. -/
def zeroBundle : HilbertPolyaSpec where
  H := Nat
  inner := fun _ _ => zero
  dom := fun _ => True
  op := id
  adj := id

/-- **THE VACUITY WITNESS — the quarantined names do not denote.** The degenerate zero-inner bundle
    satisfies `NominalSelfAdjoint` (every clause reduces to `Req zero zero`). So `NominalSelfAdjoint`
    — and likewise `NominalSymmetric`, `NominalClosed`, `NominalAdjointDomainEq`,
    `NominalEssSelfAdjoint`, `NominalDense` — are the STATED EQUATIONS on an axiom-free bundle, NOT
    the analytic notions: `inner ≡ 0` is not an inner product, `op = id` is not a self-adjoint
    unbounded operator, yet the predicate holds. A genuine contract needs vector-space +
    inner-product AXIOMS on `H` (bilinearity, symmetry, positive-definiteness, completeness) — the
    separate programme begun in `FinInnerProduct.lean`. This theorem makes the gap kernel-explicit. -/
theorem zeroBundle_NominalSelfAdjoint : NominalSelfAdjoint zeroBundle := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ _; exact Req_refl _
  · intro _ _ _; exact ⟨trivial, fun _ => Req_refl _⟩
  · intro _; exact ⟨fun _ _ _ => Req_refl _, fun _ => trivial⟩

/-- The **canonical Frobenius system carried by the operator** on a chosen basis: carrier `H`,
    Frobenius/scaling action `op`, base point `basis 0`, packaged as a `FrobSys` so the free-`H¹`
    universal property applies. -/
def specFrobSys (K : HilbertPolyaSpec) (basis : Nat → K.H) : FrobSys :=
  FrobSys.mk K.H K.op (basis 0)

/-- The **canonical mediating morphism** `H1 → specFrobSys K basis` (the orbit map), from the
    freeness of `H1`. -/
def specMap (K : HilbertPolyaSpec) (basis : Nat → K.H) : FrobHom H1 (specFrobSys K basis) :=
  H1.mediate (specFrobSys K basis)

/-- PROVED (structural, not spectral, HONESTLY named) — **the operator's orbit action is the
    canonical free `H¹` action**: the mediating map sends `n` to `opⁿ (basis 0)`. This is
    `Cohomology.H1_universal` specialized to the operator's Frobenius system; it says the
    orbit-indexed iteration of `op` is canonical, nothing about self-adjointness or zeros. -/
theorem specMap_orbit (K : HilbertPolyaSpec) (basis : Nat → K.H) :
    ∀ n, (specMap K basis).map n = (specFrobSys K basis).orbit n :=
  H1_universal (specFrobSys K basis) (specMap K basis)

/-- A **reversible (Stone-type) flow** on the bundle: a family `U t` of pairing-preserving maps
    (`isom`), each with a two-sided adjoint `V` (`reversible`) — the structural trace of a unitary
    group. NOTE the conditions are stated over the axiom-free pairing, so like the `Nominal*`
    predicates they are nominal until a genuine inner product backs them. -/
structure ReversibleFlow (K : HilbertPolyaSpec) where
  /-- the one-parameter family of maps -/
  U : Real → (K.H → K.H)
  /-- each `U t` preserves the pairing (nominal isometry) -/
  isom : ∀ t x y, Req (K.inner (U t x) (U t y)) (K.inner x y)
  /-- each `U t` has a two-sided adjoint (nominal reversibility) -/
  reversible : ∀ t, ∃ V : K.H → K.H, ∀ x y, Req (K.inner (U t x) y) (K.inner x (V y))

/-- NOMINAL OBLIGATION — **Stone's theorem for this flow**: the reversible flow `F` has a
    self-adjoint generator equal to `op`. Reduces to `NominalSelfAdjoint K`; the identification
    "generator = `op`" is kept abstract. Nominal only; NOT discharged. -/
def NominalHasSelfAdjointGenerator (K : HilbertPolyaSpec) (_F : ReversibleFlow K) : Prop :=
  NominalSelfAdjoint K

/-- **The Hilbert–Pólya transform** `μ ↦ ½ + iμ`: a real spectral value `μ` in `spec` is carried to
    `ρ = ½ + iμ`. `transformedSpectrum spec ρ` holds iff `ρ` is the image of some spectral value — by
    construction its real part is `½`. (Genuine construction, not quarantined.) -/
def transformedSpectrum (spec : Real → Prop) (rho : Complex) : Prop :=
  ∃ mu : Real, spec mu ∧ Ceq rho (Complex.mk half mu)

/-- NOMINAL OBLIGATION — **the trace-formula symmetry facet** `μ ↦ −μ` of the spectrum (the discrete
    image of `ρ ↔ 1 − ρ`). The full analytic trace identity is not expressible over the abstract
    bundle; this names its symmetry facet. Nominal only; NOT discharged. -/
def NominalTraceFormula (spec : Real → Prop) : Prop :=
  ∀ mu : Real, spec mu → ∃ mu' : Real, spec mu' ∧ Req mu' (Rneg mu)

end UOR.Bridge.F1Square.Square
