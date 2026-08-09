/-
F1 square — the **Hilbert–Pólya bridge** (the SEPARATE zero-touching module): from the operator
CONTRACT of `HilbertPolyaSpec` to the genuine Riemann Hypothesis for the constructed ζ.

This is the ONLY Hilbert–Pólya module that imports `RiemannZero` — the architectural fence of the
program is that the zeros live here and nowhere in the construction layer. It ties the abstract
spectral transform `μ ↦ ½ + iμ` (`transformedSpectrum`, zeta-free) to `NontrivialZero`, and proves
the CONDITIONAL implication the heuristic promises: if every nontrivial zero is realized as a
transformed spectral value, then RH-strip holds.

WHAT IS PROVED, AND ON WHAT. `transformedSpectrum_onLine` is unconditional and structural: a
transformed spectral value sits on `Re = ½` by construction (`½ + iμ`). The RH conclusions are
CONDITIONAL on named hypotheses:

  • `riemannHypothesis_of_zeroInclusion` assumes `ZeroInclusion spec` — every zero is SOME
    transformed spectral value. This is the substantive Hilbert–Pólya input (spectrum ⊇ zeros); it
    is exactly what a constructed self-adjoint operator would have to deliver, and it is NOT proved
    here (no operator is exhibited, no zero is located — that is RH).
  • `rh_of_selfadjoint_and_inclusion` weakens the "on-line" step to any hypothesis placing every
    transformed value on the line, showing the inclusion is what carries the argument.

HONEST DELIMITERS. Self-adjointness ALONE is insufficient: it makes the spectrum real, but says
nothing about which reals appear — the zero-INCLUSION (surjectivity of the transform onto the zero
set) is the missing content. And `SpectralCompleteness` (the exact equality spectrum ↔ zeros) is
STRICTLY STRONGER than what the bridge uses: it additionally excludes spurious spectrum, which the
implication to RH does not need — so it is stated but deliberately NOT invoked. The crux fields stay
`none`.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free.
-/

import F1Square.Square.HilbertPolyaSpec
import F1Square.Analysis.RiemannZero

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- **Zero inclusion** (the substantive Hilbert–Pólya hypothesis): every nontrivial zero `Z` of the
    constructed ζ is realized as a transformed spectral value — `Z.s = ½ + iμ` for some `μ ∈ spec`.
    This is "spectrum ⊇ zeros" (the transform is onto the zero set); the constructed operator would
    have to deliver it. A named hypothesis, NOT proved here. -/
def ZeroInclusion (spec : Real → Prop) : Prop := ∀ Z : NontrivialZero, transformedSpectrum spec Z.s

/-- **Spectral completeness** (the exact spectrum ↔ zeros correspondence): a point `ρ` is a
    transformed spectral value iff it is a zero of the constructed ζ. This is STRICTLY STRONGER than
    `ZeroInclusion` — it additionally excludes spurious spectrum — and is deliberately NOT used by
    the bridge below; the implication to RH needs only the inclusion. Stated for the record. -/
def SpectralCompleteness (spec : Real → Prop) : Prop :=
  ∀ rho : Complex, transformedSpectrum spec rho ↔ isZeroOfZeta rho

/-- PROVED (unconditional, structural) — **a transformed spectral value lies on the critical line**:
    if `ρ` is `½ + iμ` for some spectral `μ`, then `Re ρ = ½`. This is definitional — the transform
    puts `½` in the real slot — and needs no self-adjointness; it is the geometric content the
    Hilbert–Pólya construction is engineered to produce. -/
theorem transformedSpectrum_onLine (spec : Real → Prop) (rho : Complex)
    (h : transformedSpectrum spec rho) : OnCriticalLine rho := by
  obtain ⟨_, _, hmu⟩ := h
  exact hmu.1

/-- **CAVEAT — this is a REPACKAGING, not an operator-derived reduction.** `ZeroInclusion spec` says
    every zero equals `½ + iμ` for a REAL `μ` — which already places every zero on the critical line.
    So the hypothesis is equivalent to RH itself (see `zeroInclusion_of_rh` for the reverse), not a
    weaker spectral premise: the Real typing of `μ` silently does the work a spectral theorem would
    have to do (self-adjoint ⇒ real spectrum). This "conditional" therefore derives RH from a
    hypothesis that already contains it. A GENUINE reduction would take `spec` as the spectrum of a
    PROVEN self-adjoint operator and DERIVE spectral reality; nothing here does, and `spec` mentions
    no operator. Kept only to record the (trivial) forward implication; the crux does not use it. -/
theorem riemannHypothesis_of_zeroInclusion (spec : Real → Prop) (hZI : ZeroInclusion spec) :
    RiemannHypothesisStrip := by
  intro Z
  exact transformedSpectrum_onLine spec Z.s (hZI Z)

/-- **THE REPACKAGING, MADE EXPLICIT (reverse direction)**: RH *implies* `ZeroInclusion` for the
    spectrum-candidate `spec := {the imaginary parts of the zeros}`. Together with
    `riemannHypothesis_of_zeroInclusion` this shows `(∃ spec, ZeroInclusion spec) ↔ RH` — the
    "hypothesis" of the bridge is exactly as strong as its conclusion, confirming it is a restatement
    of the target and not a genuine spectral reduction. -/
theorem zeroInclusion_of_rh (h : RiemannHypothesisStrip) :
    ZeroInclusion (fun μ => ∃ Z : NontrivialZero, Req Z.s.im μ) := by
  intro Z
  exact ⟨Z.s.im, ⟨Z, Req_refl _⟩, ⟨h Z, Req_refl _⟩⟩

/-- CONDITIONAL — **the inclusion is what carries the argument**: with the "on-line" step abstracted
    to ANY hypothesis `hLine` placing every transformed value on the critical line, zero inclusion
    still yields RH-strip. This isolates that self-adjointness (which would justify `hLine`) is not
    by itself enough — the zero-INCLUSION `hZI` is the indispensable second premise. -/
theorem rh_of_selfadjoint_and_inclusion (spec : Real → Prop)
    (hLine : ∀ rho : Complex, transformedSpectrum spec rho → OnCriticalLine rho)
    (hZI : ZeroInclusion spec) : RiemannHypothesisStrip :=
  fun Z => hLine Z.s (hZI Z)

end UOR.Bridge.F1Square.Square
