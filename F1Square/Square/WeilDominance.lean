/-
F1 square — **the fixed core and the algebraic sign equivalence** (`WeilDominance.lean`, AC-15 step 0):

  `ClosedCore C = { f : L2Test // CoreTest C.geom f }`,
  `CurrentArchDominatesPrime C = ∀ f : ClosedCore C, PrimeForm(f,f) ≤ ArchForm(f,f)`,

and the PROVED algebraic equivalences from `CoupledForm = ArchForm − PrimeForm`:
  `PrimeForm(f,f) ≤ ArchForm(f,f) ⟺ 0 ≤ CoupledForm(f,f)`   (pointwise),
  `CurrentArchDominatesPrime C ⟺ ∀ f, 0 ≤ CoupledForm(f,f)`,
  `CurrentArchDominatesPrime C ⟺ ∀ f, 0 ≤ closedWeilBilin(f,f)`.
HONEST SCOPE: these are sign bookkeeping identities.  NOTHING here asserts that `PrimeForm` is PSD, that
`CoupledForm` is non-negative, or dominance — the predicate `CurrentArchDominatesPrime` is DEFINED, not
proved; its truth is the open crux (positivity of the closed Weil form on the core).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilCoupledForm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The fixed core**: tests with the context's support certificates. -/
def ClosedCore (C : NormCtx) := { f : L2Test // CoreTest C.geom f }

/-- **The dominance predicate** (DEFINED, not proved): the prime form is bounded by the archimedean
    form on every diagonal of the core. -/
def CurrentArchDominatesPrime (C : NormCtx) : Prop :=
  ∀ f : ClosedCore C,
    Rle (PrimeForm C.X f.1 f.1 C.a C.han C.had C.w C.hw C.hwn)
        (ArchForm C.geom f.1 f.1 f.2 f.2)

/-- **Pointwise sign equivalence**: `PrimeForm(f,f) ≤ ArchForm(f,f) ⟺ 0 ≤ CoupledForm(f,f)`. -/
theorem dominance_iff_coupled_nonneg (C : NormCtx) (f : ClosedCore C) :
    Rle (PrimeForm C.X f.1 f.1 C.a C.han C.had C.w C.hw C.hwn) (ArchForm C.geom f.1 f.1 f.2 f.2)
      ↔ Rnonneg (CoupledForm C.geom C.X f.1 f.1 f.2 f.2) :=
  ⟨fun h => Rnonneg_Rsub_of_Rle h, fun h => Rle_of_Rnonneg_Rsub h⟩

/-- **Universal sign equivalence** over the core. -/
theorem CurrentArchDominatesPrime_iff (C : NormCtx) :
    CurrentArchDominatesPrime C ↔ ∀ f : ClosedCore C, Rnonneg (CoupledForm C.geom C.X f.1 f.1 f.2 f.2) :=
  ⟨fun h f => (dominance_iff_coupled_nonneg C f).1 (h f),
   fun h f => (dominance_iff_coupled_nonneg C f).2 (h f)⟩

/-- The same, through the exact identity with `closedWeilBilin`. -/
theorem CurrentArchDominatesPrime_iff_closed (C : NormCtx) :
    CurrentArchDominatesPrime C ↔ ∀ f : ClosedCore C, Rnonneg (closedWeilBilin C.geom C.X f.1 f.1 f.2 f.2) := by
  refine (CurrentArchDominatesPrime_iff C).trans ⟨fun h f => ?_, fun h f => ?_⟩
  · exact Rnonneg_congr (CoupledForm_eq_closedWeilBilin C.geom C.X f.1 f.1 f.2 f.2) (h f)
  · exact Rnonneg_congr (Req_symm (CoupledForm_eq_closedWeilBilin C.geom C.X f.1 f.1 f.2 f.2)) (h f)

end UOR.Bridge.F1Square.Square
