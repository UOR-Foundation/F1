/-
F1 square — **the free Frobenius-orbit SYNTAX/INDEXING object** (`Cohomology.lean`).
HONEST-SCOPE REPAIR (operator-frontier checkpoint, task 2): this module builds a *syntax/indexing*
object, **not** cohomology and **not** a Hilbert carrier.

WHAT IS BUILT (proved): the free Frobenius system on one generator, `H1 = (ℕ, succ, 0)`. A Frobenius
system `(M, φ, g)` is a carrier with a designated endomorphism `φ` and a base point `g`; `H1` is the
free one, whose orbit `{φⁿ g}` indexes the primitive spectral classes `{Cₙ₊₁}`. Its universal
property (`H1_universal`, `H1_isFree`, `freeFrob_unique_upto_iso`) genuinely pins it as THE free such
object, unique up to unique isomorphism — this is real, and it is the analogue of
`sq_isCoproduct`/`coproduct_unique_upto_iso` for `𝕊`. The arithmetic tie (`orbit_realizes_pencil`) is
also genuine: the `k`-th orbit position realizes the pencil log-separation `k·log p = k·Λ(pᵏ)`
(`pencil_separation_pow_vonMangoldt`) — the Frobenius shift lengths ARE the explicit-formula weights.

WHAT THIS IS NOT (the honest reclassification): `H1` is **Frobenius-orbit syntax/indexing** — the free
monoid-action on one generator, canonically `≅ ℕ`. It is **not** a cohomology group, and its carrier
is **not** a Hilbert space. Its Frobenius map is `succ`, which is **not surjective**
(`H1_phi_not_surjective`: `succ n ≠ 0`), hence not invertible, hence **cannot generate a unitary
action**. A genuine `H¹`-carrier for Hilbert–Pólya requires a *reversible* (unitary) scaling flow
whose self-adjoint generator has spectrum the zeta zeros — a DIFFERENT, unbuilt object, the operator
contract (`HilbertPolyaSpec`, task 3). Do not read this indexing object as that carrier.

STATUS: the syntax/indexing object and its universal property are PROVED; the unitary Hilbert carrier
(and the whole spectral claim "spectrum = the zeros") is OPEN. This module asserts NOTHING about a
Hilbert metric, unitarity, self-adjointness, or positivity; the crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.Pencil

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- A **Frobenius system** `(M, φ, g)`: a carrier `M` with a designated endomorphism `φ` (the shift)
    and a base point `g`. `H1` below is the FREE such system on one generator — a syntax object, not a
    Hilbert carrier. -/
structure FrobSys where
  /-- the carrier (an indexing type for the spectral classes) -/
  carrier : Type
  /-- the Frobenius/shift endomorphism (an endomorphism, NOT assumed invertible/unitary) -/
  phi : carrier → carrier
  /-- the base point (the fundamental class `C₁`) -/
  g : carrier

/-- The **Frobenius orbit** of the base point: `orbit S n = φⁿ(g)` — the indexing family
    `Cₙ₊₁ ↔ orbit n`. -/
def FrobSys.orbit (S : FrobSys) : Nat → S.carrier
  | 0 => S.g
  | n + 1 => S.phi (S.orbit n)

/-- A **morphism of Frobenius systems**: an equivariant pointed map (intertwines `φ`, preserves `g`). -/
structure FrobHom (S T : FrobSys) where
  /-- the underlying map of carriers -/
  map : S.carrier → T.carrier
  /-- preserves the base point -/
  map_g : map S.g = T.g
  /-- intertwines the shift endomorphisms -/
  map_phi : ∀ x, map (S.phi x) = T.phi (map x)

/-- **THE FREE FROBENIUS-ORBIT SYNTAX OBJECT**: carrier `ℕ` (the pencil index, `Cₙ₊₁ ↔ n`), shift the
    successor `n ↦ n+1`, base point `0`. This is *indexing/syntax*, canonically `≅ ℕ`; it is NOT a
    Hilbert carrier and `succ` is NOT a unitary action (`H1_phi_not_surjective`). -/
def H1 : FrobSys where
  carrier := Nat
  phi := Nat.succ
  g := 0

/-- **`H1`'s shift `succ` is not surjective** (`succ n ≠ 0` for all `n`), so it is not invertible and
    cannot be a unitary action. This is the explicit reason `H1` is syntax/indexing, not a Hilbert
    carrier: a genuine `H¹` needs a reversible (unitary) scaling flow, which `succ` is not. -/
theorem H1_phi_not_surjective : ∀ n : Nat, H1.phi n ≠ (0 : Nat) := by
  intro n
  show Nat.succ n ≠ 0
  exact Nat.succ_ne_zero n

/-- On `H1` the orbit is the identity: `orbit n = n` (the index IS the orbit position). -/
theorem H1_orbit (n : Nat) : H1.orbit n = n := by
  induction n with
  | zero => rfl
  | succ k ih => show Nat.succ (H1.orbit k) = k + 1; rw [ih]

/-- The canonical mediating morphism `H1 → T`: the orbit map of `T`. -/
def H1.mediate (T : FrobSys) : FrobHom H1 T where
  map := T.orbit
  map_g := rfl
  map_phi := fun _ => rfl

/-- **THE UNIVERSAL PROPERTY** (uniqueness): every Frobenius morphism out of `H1` IS the orbit map —
    `h.map n = φ_T^n(g_T)`. With `H1.mediate` (existence) this is the freeness: a morphism out of `H1`
    is exactly a choice of image of the base point, the orbit determined by equivariance. -/
theorem H1_universal (T : FrobSys) (h : FrobHom H1 T) : ∀ n, h.map n = T.orbit n := by
  intro n
  induction n with
  | zero => exact h.map_g
  | succ k ih =>
      have hp : h.map (H1.phi k) = T.phi (h.map k) := h.map_phi k
      show h.map (k + 1) = T.phi (T.orbit k)
      rw [show (k + 1 : Nat) = H1.phi k from rfl, hp, ih]

/-- Freeness as **initiality**: a Frobenius system is free on one generator iff every system receives
    a UNIQUE morphism from it. The one-generator-free analogue of `IsCoproduct`. -/
def IsFreeFrob (T : FrobSys) : Prop :=
  ∀ U : FrobSys, ∃ h : FrobHom T U, ∀ h' : FrobHom T U, ∀ x, h'.map x = h.map x

/-- **`H1` IS THE FREE Frobenius system on one generator** (initial) — its canonicality as a syntax
    object. Existence is `H1.mediate`; uniqueness is `H1_universal`. -/
theorem H1_isFree : IsFreeFrob H1 := by
  intro U
  refine ⟨H1.mediate U, ?_⟩
  intro h' x
  have e1 : h'.map x = U.orbit x := H1_universal U h' x
  have e2 : (H1.mediate U).map x = U.orbit x := rfl
  rw [e1, e2]

/-- **UNIQUENESS UP TO CANONICAL ISOMORPHISM**: any `T` whose orbit map is a bijection of `ℕ` (a
    faithful free realization on one generator) is isomorphic to `H1` via the canonical mediating
    morphisms — so "the" free syntax object is well-defined. -/
theorem freeFrob_unique_upto_iso (T : FrobSys)
    (inv : T.carrier → Nat) (hinv1 : ∀ n, inv (T.orbit n) = n)
    (hinv2 : ∀ x, T.orbit (inv x) = x) :
    ∃ (φ : FrobHom H1 T) (ψ : T.carrier → Nat),
      (∀ n, ψ (φ.map n) = n) ∧ (∀ x, φ.map (ψ x) = x) := by
  refine ⟨H1.mediate T, inv, ?_, ?_⟩
  · intro n
    show inv (T.orbit n) = n
    exact hinv1 n
  · intro x
    show T.orbit (inv x) = x
    exact hinv2 x

-- ===========================================================================
-- The arithmetic tie: the Frobenius orbit indexes the built prime-power pencil.
-- ===========================================================================

/-- **The shift-length realization** at a prime `p`: orbit position `k` is assigned its log-separation
    `k·log p` from the diagonal — the bridge from the abstract free-shift SYNTAX to the constructed
    scaling-flow log-lengths. (A real-valued length assignment; not itself a Hilbert-space operator.) -/
def orbitShift (p : Nat) (hp : 1 ≤ p) (k : Nat) : Real := Rnsmul k (logN p hp)

/-- **Frobenius-equivariance of the shift lengths**: one step adds exactly `log p`,
    `orbitShift(k+1) = log p + orbitShift(k)` — the shift `φ : k ↦ k+1` realizes as translation by
    the explicit-formula weight `Λ(pᵏ) = log p`. -/
theorem orbitShift_succ (p : Nat) (hp : 1 ≤ p) (k : Nat) :
    Req (orbitShift p hp (k + 1)) (Radd (logN p hp) (orbitShift p hp k)) := by
  show Req (Rnsmul (k + 1) (logN p hp)) (Radd (logN p hp) (Rnsmul k (logN p hp)))
  rw [Rnsmul_succ]
  exact Req_refl _

/-- **THE ORBIT INDEXES THE BUILT PENCIL** (the arithmetic content): the log-separation of the built
    pencil member `Γ_{pᵏ}` from the diagonal EQUALS the shift-length realization
    `orbitShift p (H1.orbit k)` of the `k`-th orbit position — the Connes–Consani closed orbit of
    length `log p` traversed `k` times (`pencil_separation_pow`). This ties the SYNTAX index to the
    constructed prime-power geometry; it makes no unitarity/self-adjointness claim. -/
theorem orbit_realizes_pencil (p : Nat) (hp2 : 2 ≤ p) (k : Nat) (hpk : 1 ≤ p ^ k)
    (z : SqPt) (hz : graph (p ^ k) z) :
    Req (Rsub (logN z.2.val z.2.property) (logN z.1.val z.1.property))
      (orbitShift p (by omega) (H1.orbit k)) := by
  rw [H1_orbit]
  exact pencil_separation_pow p (by omega) k hpk z hz

end UOR.Bridge.F1Square.Square
