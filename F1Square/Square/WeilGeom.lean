/-
F1 square — **the fixed core of a context** (`WeilGeom.lean`): `ClosedCore C = {f // CoreTest C.geom f}`,
split out of `WeilDominance` so that constructions on the core (the Atlas fibers, carriers and transfer)
do not import the dominance predicate or `CoupledForm` into their dependency cone.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.ClosedWeilBilin

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **The fixed core**: tests with the context's support certificates. -/
def ClosedCore (C : NormCtx) := { f : L2Test // CoreTest C.geom f }

end UOR.Bridge.F1Square.Square
