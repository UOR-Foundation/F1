/-
# The direct-limit completion packaged as a Bishop-complete pre-Hilbert space

`BishopCompleteFinPreHilbert` bundles a `FinPreHilbert` with a SQUARED-distance function (setoid
congruence, positive-definiteness, symmetry, the factor-2 quasi-triangle) and a completeness operation
(fixed-modulus Bishop-Cauchy sequences have limit members with an explicit convergence modulus).

`dlimCompletionSpace` is the instance: the finite-support direct-limit completion, with `completedInner`,
`completedDist2`, and `completionLim`/`completion_complete`.

HONESTY (per review): `completedDist2` is the SQUARED distance and the triangle law is the factor-2
quasi-triangle `d²(x,z) ≤ 2d²(x,y)+2d²(y,z)` — this is the constructive sqrt-free fixed-modulus notion,
NOT a genuine metric and NOT a Hilbert space (no `√`-norm, no ordinary triangle inequality).
-/
import F1Square.Square.DlimCompletionCauchy

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

/-- Group recovery: `X ⊖ Y ≈ 0 ⟹ X ≈ Y` in the completion. -/
theorem dlimCompletionEq_of_sub_zero {X Y : DLimCompletionRaw}
    (h : DLimCompletionEq (dlimCompletionSub X Y) dlimCompletionZero) : DLimCompletionEq X Y := by
  have hnegY : DLimCompletionEq (dlimCompletionAdd (dlimCompletionNeg Y) Y) dlimCompletionZero :=
    DLimCompletionEq_trans (dlimCompletionAdd_comm (dlimCompletionNeg Y) Y) (dlimCompletionAdd_neg Y)
  have hL : DLimCompletionEq (dlimCompletionAdd (dlimCompletionSub X Y) Y) X :=
    DLimCompletionEq_trans (dlimCompletionAdd_assoc X (dlimCompletionNeg Y) Y)
      (DLimCompletionEq_trans (dlimCompletionAdd_congr (DLimCompletionEq_refl X) hnegY)
        (dlimCompletionAdd_zero X))
  have hzeroY : DLimCompletionEq (dlimCompletionAdd dlimCompletionZero Y) Y :=
    DLimCompletionEq_trans (dlimCompletionAdd_comm dlimCompletionZero Y) (dlimCompletionAdd_zero Y)
  have hR : DLimCompletionEq (dlimCompletionAdd (dlimCompletionSub X Y) Y) Y :=
    DLimCompletionEq_trans (dlimCompletionAdd_congr h (DLimCompletionEq_refl Y)) hzeroY
  exact DLimCompletionEq_trans (DLimCompletionEq_symm hL) hR

/-- **Squared-distance CONGRUENCE**: `d²` descends to the completion setoid. -/
theorem completedDist2_congr {X X' Y Y' : DLimCompletionRaw}
    (hX : DLimCompletionEq X X') (hY : DLimCompletionEq Y Y') :
    Req (completedDist2 X Y) (completedDist2 X' Y') :=
  completedNormSq_congr_cpl (dlimCompletionAdd_congr hX (dlimCompletionNeg_congr hY))

/-- **Squared-distance to self is 0**: `d²(X,X) ≈ 0`. -/
theorem completedDist2_self (X : DLimCompletionRaw) : Req (completedDist2 X X) zero :=
  Req_trans (completedNormSq_congr_cpl (dlimCompletionAdd_neg X))
    (Req_trans (completedInner_of dlimZero dlimZero).1 dlimNormSq_zero)

/-- **DEFINITENESS**: `d²(X,Y) ≈ 0 ⟹ X ≈ Y` (positive-definiteness of the squared distance). -/
theorem completedDist2_definite {X Y : DLimCompletionRaw}
    (h : Req (completedDist2 X Y) zero) : DLimCompletionEq X Y := by
  have hre : Req (completedInner (dlimCompletionSub X Y) (dlimCompletionSub X Y)).re zero := h
  have him : Req (completedInner (dlimCompletionSub X Y) (dlimCompletionSub X Y)).im zero :=
    completedInner_self_im _
  exact dlimCompletionEq_of_sub_zero (completedInner_self_definite ⟨hre, him⟩)

/-- The **canonical fixed-modulus Bishop-Cauchy predicate** derived FROM the squared distance `d²` of a
    `FinPreHilbert`-with-`dist2`: `‖Z_j − Z_k‖² ≤ M(j,k)`. This ties "Cauchy" to `dist2` (no free choice),
    closing the vacuity hole where a generic instance could pick `cauchy := False`. -/
def bishopCauchy {V : Type} (dist2 : V → V → Real) (Z : Nat → V) : Prop :=
  ∀ j k : Nat, Rle (dist2 (Z j) (Z k)) (dlimCauchyModR j k)

/-- **A Bishop-complete pre-Hilbert space** (with SQUARED distance).  Bundles a `FinPreHilbert` with a
    squared-distance function `dist2` that IS the inner product's squared distance (`dist2_eq_inner`,
    tying `dist2` to the inherited inner product — no free choice), together with its metric laws and a
    completeness operation for the CANONICAL `bishopCauchy dist2` predicate (tying Cauchy to `dist2`).

    HONESTY: `dist2` is the SQUARED distance and the triangle law is the factor-2 quasi-triangle
    `d²(x,z) ≤ 2d²(x,y)+2d²(y,z)` — NOT a genuine metric (no `√`, no ordinary triangle inequality) and
    NOT a Hilbert space; it is the constructive, sqrt-free, fixed-modulus notion the development uses. -/
structure BishopCompleteFinPreHilbert extends FinPreHilbert where
  dist2 : V → V → Real
  /-- **`dist2` IS the inner product's squared distance**: `d²(x,y) = Re⟨x−y, x−y⟩`. Forbids a `dist2`
      disconnected from the bundled inner product. -/
  dist2_eq_inner : ∀ x y, Req (dist2 x y) (inner (add x (vneg y)) (add x (vneg y))).re
  dist2_congr : ∀ {x x' y y'}, veq x x' → veq y y' → Req (dist2 x y) (dist2 x' y')
  dist2_nonneg : ∀ x y, Rnonneg (dist2 x y)
  dist2_self : ∀ x, Req (dist2 x x) zero
  dist2_definite : ∀ x y, Req (dist2 x y) zero → veq x y
  dist2_symm : ∀ x y, Req (dist2 x y) (dist2 y x)
  dist2_quasitriangle : ∀ x y z,
    Rle (dist2 x z) (Radd (Radd (dist2 x y) (dist2 x y)) (Radd (dist2 y z) (dist2 y z)))
  /-- The limit of a `bishopCauchy dist2` sequence — the CANONICAL predicate, so completeness cannot be
      made vacuous by a degenerate `cauchy`. -/
  lim : ∀ Z : Nat → V, bishopCauchy dist2 Z → V
  complete : ∀ (Z : Nat → V) (hZ : bishopCauchy dist2 Z) (k : Nat), ∃ N : Nat, ∀ m : Nat, N ≤ m →
    Rle (dist2 (Z m) (lim Z hZ)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))

/-- **The direct-limit completion as a Bishop-complete pre-Hilbert space.** Packages
    `dlimCompletionPreHilbert` (the inner product) with `completedDist2` (squared distance, DEFINITIONALLY
    `Re⟨X−Y, X−Y⟩` so `dist2_eq_inner` is `rfl`) and `completionLim`/`completion_complete` (Bishop
    completeness). `CompletionCauchyU` IS `bishopCauchy completedDist2` (definitionally). -/
def dlimCompletionSpace : BishopCompleteFinPreHilbert where
  toFinPreHilbert := dlimCompletionPreHilbert
  dist2 := completedDist2
  dist2_eq_inner := fun _ _ => Req_refl _
  dist2_congr := completedDist2_congr
  dist2_nonneg := completedDist2_nonneg
  dist2_self := completedDist2_self
  dist2_definite := fun _ _ h => completedDist2_definite h
  dist2_symm := completedDist2_symm_cpl
  dist2_quasitriangle := completedDist2_quasitriangle_cpl
  lim := completionLim
  complete := completion_complete

/-- **The completion RELATIONSHIP**: `target` is a Bishop-complete space, `embed` an inner-preserving
    linear map from the `source` pre-Hilbert, `reflect` says `embed` reflects equality (injective up to
    the setoids), and `dense` says the `embed`-image is dense (with explicit squared-distance modulus).
    This packages "`target` is a completion of `source`" — not just an abstract complete space. -/
structure CompletionOf (source : FinPreHilbert) where
  target : BishopCompleteFinPreHilbert
  embed : FinPreHilbertHom source target.toFinPreHilbert
  reflect : ∀ a b, target.veq (embed.toFun a) (embed.toFun b) → source.veq a b
  dense : ∀ (X : target.V) (k : Nat), ∃ a : source.V,
    Rle (target.dist2 X (embed.toFun a)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))

/-- **The finite-support direct limit's completion, as a completion relationship.** `embed = ofHom`
    (inner-preserving), reflection is `DLimCompletionEq_of_iff`, density is `completion_dense` with
    representative `a := X.seq N`. -/
def dlimIsCompletion : CompletionOf dlimPreHilbert where
  target := dlimCompletionSpace
  embed := ofHom
  reflect := fun a b h => (DLimCompletionEq_of_iff a b).mp h
  dense := fun X k => by obtain ⟨N, hN⟩ := completion_dense X k; exact ⟨X.seq N, hN⟩

end UOR.Bridge.F1Square.Square

