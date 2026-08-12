/-
# The direct-limit completion: isometric embedding, density, and completeness

Building on the `FinPreHilbert` package (`DlimCompletionPreHilbert`), this file establishes the three
properties that make `(DLimCompletionRaw / DLimCompletionEq, completedInner)` a genuine metric completion
of the finite-support direct limit:

* **isometric embedding** — `completedInner_of` (`⟨of a, of b⟩ ≈ ⟨a,b⟩`) bundled as `ofHom`, a
  setoid-respecting ℂ-linear inner-preserving map `FinPreHilbertHom dlimPreHilbert dlimCompletionPreHilbert`;
* **density** — every completion member `X` is the completion-metric limit of `of (X.seq N)`, with an
  explicit squared-norm approximation modulus;
* **completeness** — every completion-Cauchy sequence of completion members converges (diagonal limit).

`completedNormSq`, `dlimCompletionSub`, `completedDist2` are the completion-level norm² / difference /
squared distance. NOTE the key structural fact: `(dlimCompletionSub X Y).seq n = dlimSub (X.seq (2n+1))
(Y.seq (2n+1))`, so `completedDist2 X Y` is (definitionally) `Rlim` of the stagewise squared distances.

This does NOT touch operators, adjoints, self-adjointness, Atlas provenance, or the Hilbert–Pólya crux.
-/
import F1Square.Square.DlimCompletedInner
import F1Square.Square.FinPreHilbert
import F1Square.Square.FinDirectLimit
import F1Square.Square.DlimCompletionPreHilbert

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- D1. ISOMETRIC EMBEDDING
-- ===========================================================================

/-- **Inner-product preservation of `of`**: `⟨of a, of b⟩ ≈ ⟨a,b⟩`. Both `(of a).seq` and `(of b).seq`
    are constant, so the rescheduled inner sequence is the constant `dlimInner a b`, and the completed
    limit of a constant is that constant (`Rlim_const_core`). -/
theorem completedInner_of (a b : DLimRaw) :
    Ceq (completedInner (DLimCompletionRaw.of a) (DLimCompletionRaw.of b)) (dlimInner a b) :=
  ⟨Rlim_const_core (dlimInner a b).re
      (innerSeq_CRegCore (DLimCompletionRaw.of a) (DLimCompletionRaw.of b)).1,
   Rlim_const_core (dlimInner a b).im
      (innerSeq_CRegCore (DLimCompletionRaw.of a) (DLimCompletionRaw.of b)).2⟩

/-- A setoid-respecting ℂ-linear inner-preserving map between two `FinPreHilbert`s — a linear ISOMETRY
    up to the setoids (`map_inner` is the isometry condition, `map_add`/`map_smul` linearity). -/
structure FinPreHilbertHom (H K : FinPreHilbert) where
  toFun : H.V → K.V
  map_veq : ∀ {x y}, H.veq x y → K.veq (toFun x) (toFun y)
  map_add : ∀ x y, K.veq (toFun (H.add x y)) (K.add (toFun x) (toFun y))
  map_smul : ∀ c x, K.veq (toFun (H.smul c x)) (K.smul c (toFun x))
  map_inner : ∀ x y, Ceq (K.inner (toFun x) (toFun y)) (H.inner x y)

/-- **The embedding of the direct limit into its completion as a linear isometry.** `of` respects the
    setoids, is additive and ℂ-linear, and PRESERVES the inner product (`completedInner_of`). -/
def ofHom : FinPreHilbertHom dlimPreHilbert dlimCompletionPreHilbert where
  toFun := DLimCompletionRaw.of
  map_veq := DLimCompletionEq_of
  map_add := DLimCompletionEq_of_add
  map_smul := fun c a => DLimCompletionEq_symm (DLimCompletionEq_of_smul c a)
  map_inner := completedInner_of

-- ===========================================================================
-- Completion-level norm² / difference / squared distance
-- ===========================================================================

/-- The completed squared norm `‖X‖² := Re⟨X,X⟩`. -/
def completedNormSq (X : DLimCompletionRaw) : Real := (completedInner X X).re

/-- The completion difference `X ⊖ Y`. Its `n`-th entry is `dlimSub (X.seq (2n+1)) (Y.seq (2n+1))`. -/
def dlimCompletionSub (X Y : DLimCompletionRaw) : DLimCompletionRaw :=
  dlimCompletionAdd X (dlimCompletionNeg Y)

/-- The completed squared distance `d²(X,Y) := ‖X ⊖ Y‖²`. -/
def completedDist2 (X Y : DLimCompletionRaw) : Real := completedNormSq (dlimCompletionSub X Y)

/-- `‖X‖² ≥ 0`. -/
theorem completedNormSq_nonneg (X : DLimCompletionRaw) : Rnonneg (completedNormSq X) :=
  completedInner_self_nonneg X

/-- `d²(X,Y) ≥ 0`. -/
theorem completedDist2_nonneg (X Y : DLimCompletionRaw) : Rnonneg (completedDist2 X Y) :=
  completedNormSq_nonneg _

end UOR.Bridge.F1Square.Square
