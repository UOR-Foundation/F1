/-
F1 square — **the clean, reusable ζ-free coordinatewise COMPLEX-LIMIT core** (`ComplexLimitCore.lean`).

The ℓ² completion's completed inner product `⟨X, Y⟩ := lim ⟨X_n, Y_n⟩` needs a genuine limit of a Cauchy
sequence of complex numbers. This module lifts the Zeta-free real completeness engine `Analysis.Complete`
(`RReg` / `Rlim` / `Rlim_tendsTo` / `RTendsTo_unique`) to ℂ COORDINATEWISE: a complex sequence is regular
iff both its real and imaginary coordinate-sequences are regular, and its limit is the pair of the two real
limits. Everything is a one-line reduction to the real side, so the constructive-analysis content is reused,
not re-proved.

WHY A SEPARATE `…Core` FAMILY: the existing `Analysis.ComplexLimit` already defines `CReg`/`Clim`/… with the
SAME meaning, but it imports `RlimProps`, whose cone transitively reaches `Analysis.Zeta` (the ζ / crux side);
the completion's import-only-`FinDirectLimit` fence forbids it. This core re-proves ONLY the basic
coordinatewise-limit facts (which need `Complete` alone, not the Zeta-tainted `RlimProps` arithmetic), under
the `…Core` names so every leaf name stays globally UNIQUE — distinct from `ComplexLimit`'s `Clim` / `CReg` /
… — which the mechanized-honesty coverage gate requires (leaf-name match + dups guard).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; Zeta-free cone. Crux `none`.
-/

import F1Square.Analysis.Complete
import F1Square.Analysis.Complex

namespace UOR.Bridge.F1Square.Analysis

/-- **Regularity of a complex sequence**: both coordinate real-sequences are regular (Cauchy with the
    canonical modulus). The ζ-free-core mirror of `RReg`. -/
def CRegCore (Z : Nat → Complex) : Prop :=
  RReg (fun n => (Z n).re) ∧ RReg (fun n => (Z n).im)

/-- **The coordinatewise complex limit** `lim Z := ⟨lim Re Z, lim Im Z⟩`. The ζ-free-core mirror of `Rlim`. -/
def ClimCore (Z : Nat → Complex) (h : CRegCore Z) : Complex :=
  ⟨Rlim (fun n => (Z n).re) h.1, Rlim (fun n => (Z n).im) h.2⟩

/-- The real part of the complex limit is the real limit of the real parts (definitional). -/
theorem ClimCore_re (Z : Nat → Complex) (h : CRegCore Z) :
    (ClimCore Z h).re = Rlim (fun n => (Z n).re) h.1 := rfl

/-- The imaginary part of the complex limit is the real limit of the imaginary parts (definitional). -/
theorem ClimCore_im (Z : Nat → Complex) (h : CRegCore Z) :
    (ClimCore Z h).im = Rlim (fun n => (Z n).im) h.2 := rfl

/-- **Complex convergence** `Z k → L`: both coordinate sequences converge (as reals). ζ-free-core mirror of
    `RTendsTo`. -/
def CTendsToCore (Z : Nat → Complex) (L : Complex) : Prop :=
  RTendsTo (fun n => (Z n).re) L.re ∧ RTendsTo (fun n => (Z n).im) L.im

/-- **Completeness of ℂ** (coordinatewise): every regular complex sequence converges to its complex limit. -/
theorem ClimCore_tendsTo (Z : Nat → Complex) (h : CRegCore Z) : CTendsToCore Z (ClimCore Z h) :=
  ⟨Rlim_tendsTo (fun n => (Z n).re) h.1, Rlim_tendsTo (fun n => (Z n).im) h.2⟩

/-- **Complex limits are unique up to `≈`**: if `Z → L` and `Z → L'` then `L ≈ L'` (`Ceq`), coordinatewise
    from `RTendsTo_unique`. -/
theorem CTendsToCore_unique {Z : Nat → Complex} {L L' : Complex}
    (hL : CTendsToCore Z L) (hL' : CTendsToCore Z L') : Ceq L L' :=
  ⟨RTendsTo_unique hL.1 hL'.1, RTendsTo_unique hL.2 hL'.2⟩

end UOR.Bridge.F1Square.Analysis
