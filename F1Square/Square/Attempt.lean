/-
F1 square — v0.18.0 stage D, brick 4: **THE CRUX ATTEMPT, under the gate** — run, recorded,
and honestly concluded. RH stays OPEN; the crux fields stay `none`.

THE ATTEMPT (ROADMAP stage D: "the Hodge-index / Li-positivity attempt on canonical 𝕊 under
the gate — fields flip none → some true iff a genuine, audited, axiom-clean proof lands").
With the bridge in place (`crux_faces_equivalent`: the geometric and analytic faces are the
same proposition), the attempt is on `λₙ > 0 ∀ n ≥ 1`. What this program can certify today,
it has certified:

  • `n = 1`: `Pos λ₁` (v0.14.0, `Rlambda1_pos`, `λ₁ ≈ 0.0231`) — via the accelerated
    Euler–Mascheroni bracket `γ ∈ [0.54, 0.66]` and the kernel-certified logs.
  • `n = 2`: `Pos λ₂` (v0.16.0, `Rlambda2_pos`, `λ₂ ≈ 0.0043`, razor-thin) — via the
    parabola trick for `γ − γ²`, the γ₁ bracket (`Rgamma1_le_neg445`, the program's hardest
    analytic mechanization), `ζ(2) ≥ 1.63`, `log 4π ≤ 2.5316`.
  • Both transfer to the geometric face through the bridge (`spectral_evidence_two`:
    `⟨C₁,C₁⟩ < 0`, `⟨C₂,C₂⟩ < 0`), and the up-to-2 strict negativity is packaged below
    (`spectral_strict_upTo_two`).

THE FRONTIER, made exact (`crux_attempt_frontier`): given the two certified slices, the
crux is EQUIVALENT to `∀ n ≥ 3, λₙ > 0`. The next certifiable slice (`λ₃`) needs the second
Stieltjes constant `γ₂` (a fresh `GammaOne`-scale dyadic mechanization); each further slice
needs the next `γⱼ`. No finite run reaches the crux (`liPositive_iff_all_upTo`,
`spectral_iff_all_upTo`) — the universal `∀ n` is the open content.

WHY NO GENERAL ROUTE CLOSED (the attempt's honest post-mortem, with the program's own
controls as evidence):
  • Manifestly-positive routes are VACUOUS: any kernel of the form `Σ cos·cos + sin·sin`
    is PSD for an arbitrary real spectrum (`Bridge.control_psd`, the §2.3 control) — its
    positivity is equivalent to the spectrum being real, i.e. it IS the conclusion.
  • The coarse geometry of canonical `𝕊` cannot see the crux: its lattice Hodge index
    holds AND is pencil-blind (`Square.square_hodge_pencil_blind`) — no spectral input.
  • Finite certification cannot reach it: `spectralTwoSlice_not_crux` PROVES the
    two-slice instance fails the crux — positivity of any finite batch of `λₙ` (the
    literature's `n ≤ 10⁵`) is not the theorem.
  • The BL decomposition relocates, not removes, the difficulty: `λₙ = λₙ^{arith} + λₙ^{∞}`
    with opposite-sign parts (`li_decomposition_two_realized` realizes it at `n = 1, 2`);
    positivity is a CANCELLATION statement (companion `missing_object_over_Q.md` §8.1), and
    positivity reformulations do not make RH easier (Conrey–Li, IMRN 2000; the de Branges
    precedent, companion §2.1).
  • What WOULD close it: the genuine spectral instance — the `H¹` pairing with spectrum =
    the zeta zeros (T4/§3.4, the Hilbert–Pólya face; Connes–Consani's archimedean/semilocal
    Weil positivity, Selecta Math. 27 (2021), is the strongest partial result, and global
    is exactly what is open).

CONCLUSION OF THE ATTEMPT: no genuine, audited, axiom-clean proof of the universal landed.
Per the bright line, `hodgeIndexHolds` and `liPositivityHolds` STAY `none`; the release
ships the bridge substrate. This module is the attempt's record — honest, mechanized where
mechanizable, and explicit about the single remaining object.

Pure Lean 4 core, no Mathlib, no `sorry`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Square.Spectral

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open UOR.Bridge.F1Square.Li

/-- **The attempt's exact frontier**: for any spectral square whose first two Li slices are
    certified positive (as the genuine instance's are, via `Rlambda1_pos`/`Rlambda2_pos`),
    the crux is equivalent to the positivity of the slices from `n = 3` on. This is the
    precise statement of where the v0.18.0 attempt stands — the certified part is done,
    and the open content is the (still universal, still RH-strength) tail. -/
theorem crux_attempt_frontier (S : SpectralSquare)
    (h1 : Pos (S.lam 1)) (h2 : Pos (S.lam 2)) :
    LiCrux S.lam ↔ (∀ n : Nat, 3 ≤ n → Pos (S.lam n)) := by
  constructor
  · intro h n hn
    exact h n (by omega)
  · intro h n hn
    by_cases hn1 : n = 1
    · subst hn1; exact h1
    · by_cases hn2 : n = 2
      · subst hn2; exact h2
      · exact h n (by omega)

/-- The geometric face of the frontier: through the bridge, the crux of a two-slice-certified
    spectral square is equivalent to the negativity `⟨Cₙ,Cₙ⟩ < 0` of the primitive classes
    from `n = 3` on. -/
theorem crux_attempt_frontier_geometric (S : SpectralSquare)
    (h1 : Pos (S.lam 1)) (h2 : Pos (S.lam 2)) :
    SpectralCrux S ↔ (∀ n : Nat, 3 ≤ n → Pos (Rneg (S.cSq n))) := by
  rw [crux_faces_equivalent S, crux_attempt_frontier S h1 h2]
  constructor
  · intro h n hn
    exact (spectral_bridge_pos_slice S n (by omega)).mpr (h n hn)
  · intro h n hn
    exact (spectral_bridge_pos_slice S n (by omega)).mp (h n hn)

/-- The certified slice of the attempt, packaged: strict Hodge-index negativity holds on
    the two-slice instance UP TO `n = 2` — the furthest any certified, axiom-clean run has
    reached in this substrate. (The guard `spectralTwoSlice_not_crux` proves this is NOT
    the crux.) -/
theorem spectral_strict_upTo_two :
    ∀ n : Nat, 0 < n → n ≤ 2 → Pos (Rneg (spectralTwoSlice.cSq n)) := by
  intro n hn hn2
  by_cases h1 : n = 1
  · subst h1; exact spectral_evidence_two.1
  · have h2 : n = 2 := by omega
    subst h2; exact spectral_evidence_two.2

end UOR.Bridge.F1Square.Square
