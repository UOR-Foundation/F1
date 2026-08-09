/-
F1 square — the **Hilbert–Pólya operator CONTRACT**, stated as named obligations over an abstract
self-adjoint-operator bundle (the zeta-FREE construction layer).

The Hilbert–Pólya heuristic asks for a self-adjoint operator whose spectrum is the imaginary parts
`μ` of the nontrivial zeros `ρ = ½ + iμ`; self-adjointness forces `μ` real, hence `Re ρ = ½`. This
file lays down the CONTRACT such an operator must satisfy — a dense domain, symmetry, the
adjoint-domain equality, closability/closedness, essential/actual self-adjointness, a reversible
(Stone-type) unitary flow, and the transform `μ ↦ ½ + iμ` carrying the spectrum onto the critical
line — WITHOUT asserting that any concrete bundle discharges them.

HONEST SCOPE. This repository builds no unbounded-operator / spectral theory, so the analytic
predicates here (`IsDense`, `Symmetric`, `AdjointDomainEq`, `Closable`, `Closed`, `EssSelfAdjoint`,
`SelfAdjoint`, `HasSelfAdjointGenerator`, `TraceFormula`) are NAMED OBLIGATIONS — genuine `Prop`s
over the bundle, none of them discharged here. What IS proved is purely structural: the canonical
Frobenius/orbit action of the operator on a chosen basis is the free `H¹` action (`specMap_orbit`,
via `Cohomology.H1_universal`). The bridge to the actual zeros lives in the SEPARATE
`HilbertPolyaBridge`; nothing in this file touches `RiemannZero`.

FENCE. This is the zeta-free layer: its transitive import cone is free of the RH-bearing zeta and
its zero/Li/spectral stack — `RiemannZero`, `CzetaStrip`, `GenuineLi`, `genuineLamSeq`, `Rlambda`,
`liRatio`, `CayleyMap`, `WeilLattice`, `Spectral`, `StieltjesEta`. (The convergent-regime `ζ(s≥2)`
arithmetic brick — which has no zeros and is not a route to RH — enters only transitively through
`Cohomology`'s prime-power pencil, and no zero object is ever in scope.)

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free. The crux fields stay `none`.
-/

import F1Square.Square.Cohomology
import F1Square.Analysis.Complex
import F1Square.Analysis.ROrder

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The Hilbert–Pólya operator bundle** — DATA ONLY, no axioms. A carrier `H` with a pairing
    `inner : H → H → ℝ`, a domain predicate, and maps `op`/`adj`. **CAVEAT: `H` has no vector-space
    structure and `inner` satisfies no inner-product laws** (no bilinearity, symmetry, or
    positive-definiteness), so the predicates below are the stated equations, NOT the operator-theoretic
    notions their names suggest — `zeroBundle_SelfAdjoint` proves `inner ≡ 0` satisfies `SelfAdjoint`.
    A genuine operator bundle (with those axioms and completeness) is a separate programme this file
    does not build. -/
structure HilbertPolyaSpec where
  /-- the carrier (the abstract Hilbert space) -/
  H : Type
  /-- the (real) inner product `⟨x, y⟩` -/
  inner : H → H → Real
  /-- the operator domain `D(op)` -/
  dom : H → Prop
  /-- the (unbounded) operator -/
  op : H → H
  /-- the formal adjoint -/
  adj : H → H

/-- Utility (NOT a contract predicate): `a` and `b` agree to within `1/(n+1)`. This is the abs-free
    rendering of `|a − b| ≤ 1/(n+1)` as the two-sided `a − b ≤ 1/(n+1) ∧ b − a ≤ 1/(n+1)`, using
    only `Rle`/`Rsub`/`ofQ` — `Rabs` lives outside this file's minimal zeta-free import cone, and the
    two formulations are equivalent. The index `n` is the Bishop modulus. -/
def RcloseN (a b : Real) (n : Nat) : Prop :=
  Rle (Rsub a b) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)) ∧
  Rle (Rsub b a) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n))

/-- OBLIGATION — **dense domain**: for every vector `y` and every precision `1/(n+1)` there is a
    domain element `x` whose pairing `⟨x, y⟩` approximates `⟨y, y⟩` to that precision. This is the
    inner-product shadow of `D(op)` being dense (the abstract carrier has no norm/limit structure to
    state density directly). NOT discharged here. -/
def IsDense (K : HilbertPolyaSpec) : Prop :=
  ∀ y : K.H, ∀ n : Nat, ∃ x : K.H, K.dom x ∧ RcloseN (K.inner x y) (K.inner y y) n

/-- OBLIGATION — **symmetry** of `op` on its domain: `⟨op x, y⟩ = ⟨x, op y⟩` for `x, y ∈ D(op)`. A
    genuine `Prop` over the bundle; NOT discharged here. -/
def Symmetric (K : HilbertPolyaSpec) : Prop :=
  ∀ x y : K.H, K.dom x → K.dom y → Req (K.inner (K.op x) y) (K.inner x (K.op y))

/-- OBLIGATION — **the adjoint-domain equality** `D(op) = D(op*)`, the analytic heart of essential
    self-adjointness: `x ∈ D(op)` iff `x` is an admissible adjoint vector, i.e. for every domain `y`
    the adjoint identity `⟨op y, x⟩ = ⟨y, adj x⟩` holds. NOT discharged here. -/
def AdjointDomainEq (K : HilbertPolyaSpec) : Prop :=
  ∀ x : K.H, K.dom x ↔ (∀ y : K.H, K.dom y → Req (K.inner (K.op y) x) (K.inner y (K.adj x)))

/-- OBLIGATION — **graph closability**: the closure of the graph of `op` contains no vertical vector
    `(0, w)` with `w ≠ 0`. Stated through inner products (the carrier lacks subtraction/limits): if
    for every precision there is a domain `x` that is negligible in norm (`⟨x, x⟩ ≤ 1/(n+1)`) yet
    whose image pairs with every test `z` like a fixed `w` (`⟨op x, z⟩ ≈ ⟨w, z⟩`), then `w` is null
    (`⟨w, z⟩ ≈ 0` for all `z`). This is exactly "`xₖ → 0` and `op xₖ → w` force `w = 0`". A named
    abstract `Prop`; NOT discharged here. -/
def Closable (K : HilbertPolyaSpec) : Prop :=
  ∀ w : K.H,
    (∀ n : Nat, ∃ x : K.H, K.dom x ∧
      Rle (K.inner x x) (ofQ ⟨1, n + 1⟩ (Nat.succ_pos n)) ∧
      ∀ z : K.H, RcloseN (K.inner (K.op x) z) (K.inner w z) n) →
    ∀ z : K.H, Req (K.inner w z) zero

/-- OBLIGATION — **graph closedness**: the graph of `op` already contains its limit points. Stated
    through inner products: if for every precision there is a domain `x` with `⟨x, z⟩ ≈ ⟨u, z⟩` and
    `⟨op x, z⟩ ≈ ⟨w, z⟩` against every test `z` (so `x → u`, `op x → w` weakly), then `u ∈ D(op)`
    and `op u = w` (`⟨op u, z⟩ ≈ ⟨w, z⟩` for all `z`). A named abstract `Prop`, distinct from
    `Closable`; NOT discharged here. -/
def Closed (K : HilbertPolyaSpec) : Prop :=
  ∀ u w : K.H,
    (∀ n : Nat, ∃ x : K.H, K.dom x ∧
      ∀ z : K.H, RcloseN (K.inner x z) (K.inner u z) n ∧ RcloseN (K.inner (K.op x) z) (K.inner w z) n) →
    K.dom u ∧ ∀ z : K.H, Req (K.inner (K.op u) z) (K.inner w z)

/-- OBLIGATION — **essential self-adjointness**: `op` is symmetric and closable (its closure is
    self-adjoint). A conjunction of two obligations; NOT discharged here. -/
def EssSelfAdjoint (K : HilbertPolyaSpec) : Prop := Symmetric K ∧ Closable K

/-- OBLIGATION — the conjunction `Symmetric ∧ Closed ∧ AdjointDomainEq`. **CAVEAT: this predicate does
    NOT denote self-adjointness** — the bundle carries no inner-product axioms, so the clauses are the
    stated equations only, and `zeroBundle_SelfAdjoint` below proves the degenerate `inner ≡ 0` bundle
    satisfies it. Read it as "these three equations hold", never as "the operator is self-adjoint".
    The name is retained for the contract slot; the honest content is the caveat. -/
def SelfAdjoint (K : HilbertPolyaSpec) : Prop := Symmetric K ∧ Closed K ∧ AdjointDomainEq K

-- ===========================================================================
-- CAVEAT — the predicate names above do NOT denote their operator-theoretic
-- meaning: on the axiom-free bundle they are vacuous. Kernel-proven witness.
-- ===========================================================================

/-- A DEGENERATE bundle with `inner ≡ 0`: carrier `Nat`, zero inner product, full domain,
    `op = adj = id`. It is NOT an inner-product space — positive-definiteness fails (`⟨x,x⟩ = 0` for
    every `x`) — but the axiom-free `HilbertPolyaSpec` admits it, which is the whole problem. -/
def zeroBundle : HilbertPolyaSpec where
  H := Nat
  inner := fun _ _ => zero
  dom := fun _ => True
  op := id
  adj := id

/-- **THE VACUITY WITNESS — the names do not denote.** The degenerate zero-inner bundle satisfies
    `SelfAdjoint` (every clause reduces to `Req zero zero`). So `SelfAdjoint` — and likewise
    `Symmetric`, `Closed`, `AdjointDomainEq`, `EssSelfAdjoint`, `IsDense` — are the STATED EQUATIONS on
    an axiom-free bundle, NOT the analytic notions their names suggest: `inner ≡ 0` is not an inner
    product, `op = id` is not a self-adjoint unbounded operator, yet the predicate holds. A genuine
    contract needs vector-space + inner-product-space AXIOMS on `H` (bilinearity, symmetry,
    positive-definiteness, completeness) — the separate operator-theory programme — none of which this
    file builds. This theorem makes that gap kernel-explicit, so no green build can disguise it. -/
theorem zeroBundle_SelfAdjoint : SelfAdjoint zeroBundle := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ _; exact Req_refl _
  · intro _ _ _; exact ⟨trivial, fun _ => Req_refl _⟩
  · intro _; exact ⟨fun _ _ _ => Req_refl _, fun _ => trivial⟩

/-- The **canonical Frobenius system carried by the operator** on a chosen basis: carrier `H`,
    Frobenius/scaling action `op`, base point `basis 0`. This packages `(H, op, basis 0)` as a
    `FrobSys` so the free-`H¹` universal property applies to it. -/
def specFrobSys (K : HilbertPolyaSpec) (basis : Nat → K.H) : FrobSys :=
  FrobSys.mk K.H K.op (basis 0)

/-- The **canonical mediating morphism** `H1 → specFrobSys K basis` (the orbit map of the operator
    system), from the freeness of `H1`. -/
def specMap (K : HilbertPolyaSpec) (basis : Nat → K.H) : FrobHom H1 (specFrobSys K basis) :=
  H1.mediate (specFrobSys K basis)

/-- PROVED (structural, not spectral) — **the operator's orbit action is the canonical free `H¹`
    action**: the mediating map sends the index `n` to `opⁿ (basis 0)`, the `n`-th orbit class. This
    is `Cohomology.H1_universal` specialized to the operator's Frobenius system; it says the
    orbit-indexed iteration of `op` is canonical/unique, nothing about self-adjointness or zeros. -/
theorem specMap_orbit (K : HilbertPolyaSpec) (basis : Nat → K.H) :
    ∀ n, (specMap K basis).map n = (specFrobSys K basis).orbit n :=
  H1_universal (specFrobSys K basis) (specMap K basis)

/-- A **reversible (Stone-type) unitary flow** on the bundle: a one-parameter family `U t` of
    inner-product-preserving maps (`isom`), each of which admits a two-sided adjoint `V`
    (`reversible`) — the structural trace of a strongly-continuous unitary group `U t = exp(i t A)`
    whose generator `A` is the (self-adjoint) operator. The carrier lacks the topology to state
    strong continuity or that the generator IS `op`; those stay in the obligation below. -/
structure ReversibleFlow (K : HilbertPolyaSpec) where
  /-- the one-parameter family of maps -/
  U : Real → (K.H → K.H)
  /-- each `U t` preserves the inner product (isometry) -/
  isom : ∀ t x y, Req (K.inner (U t x) (U t y)) (K.inner x y)
  /-- each `U t` has a two-sided adjoint (reversibility / unitarity) -/
  reversible : ∀ t, ∃ V : K.H → K.H, ∀ x y, Req (K.inner (U t x) y) (K.inner x (V y))

/-- OBLIGATION — **Stone's theorem for this flow**: the reversible unitary flow `F` has a
    self-adjoint generator equal to `op`. What is mechanizable of the conclusion — that the bundle
    is self-adjoint — is named here; the identification "generator = `op`" is kept abstract (the
    carrier has no differentiation to state `d/dt U t = i·op`). NOT discharged here. Note the free
    `H¹` shift `succ` is not reversible (it has no left inverse), so `H1` itself is not such a
    carrier — reversibility is a genuine additional demand. -/
def HasSelfAdjointGenerator (K : HilbertPolyaSpec) (_F : ReversibleFlow K) : Prop := SelfAdjoint K

/-- **The Hilbert–Pólya transform** `μ ↦ ½ + iμ`: a real spectral value `μ` in `spec` is carried to
    the critical-line point `ρ = ½ + iμ`. `transformedSpectrum spec ρ` holds iff `ρ` is the image of
    some spectral value — by construction its real part is `½`, which is what the bridge exploits. -/
def transformedSpectrum (spec : Real → Prop) (rho : Complex) : Prop :=
  ∃ mu : Real, spec mu ∧ Ceq rho (Complex.mk half mu)

/-- OBLIGATION — **the explicit-formula / trace side**, in its mechanizable shadow: the reflection
    symmetry `μ ↦ −μ` of the spectrum (the discrete image of the functional-equation symmetry
    `ρ ↔ 1 − ρ`, i.e. `½ + iμ ↔ ½ − iμ`, that the explicit/trace formula encodes). The full analytic
    trace identity `Σ h(μ) = (arithmetic side)` is not expressible over the abstract bundle (no sums
    over `spec`), so this names its symmetry facet as a universally-quantified `Prop` over `spec`.
    NOT discharged here. -/
def TraceFormula (spec : Real → Prop) : Prop :=
  ∀ mu : Real, spec mu → ∃ mu' : Real, spec mu' ∧ Req mu' (Rneg mu)

end UOR.Bridge.F1Square.Square
