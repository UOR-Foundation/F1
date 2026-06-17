/-
F1 square — the frontier construction: **the archimedean kernel `Re ψ(1/4 + iτ/2)` ASSEMBLED as a
constructive real at a frontier point**, and the consequence — the Riemann–Siegel angle is
non-monotone TWO-SIDEDLY.

`DigammaWindow.lean` built the `τ`-parameterized kernel TERM `windowTerm n s = 1/(n+1) −
(n+1/4)/((n+1/4)² + s)` (`s = τ²/4`) and its monotonicity, and recorded — honestly — that the
multiplier `α(τ)` is indefinite and that the assembled kernel was not yet built. THIS FILE builds the
assembled kernel at the concrete frontier point `τ = 10` (`s = 25`), the first value of `Re ψ` along
the critical line away from the center `ψ(1/4)`.

THE DECOMPOSITION. The window term splits EXACTLY into the center term and a positive correction:
    `windowTerm n 25 = windowTerm n 0 + cₙ`,   `cₙ = s/((n+1/4)((n+1/4)²+s)) = 1600/((4n+1)((4n+1)²+400)) ≥ 0`,
and `windowTerm n 0 = −3/[(n+1)(4n+1)]` is exactly `ψ(1/4)`'s summand (`DigammaWindow.windowTerm_zero`).
So `Re ψ(1/4 + 5i) = −γ + Σ windowTerm n 25 = ψ(1/4) + Σ cₙ`. We build `Σ cₙ` (`corrCore`) as a
genuine constructive real — a manifestly POSITIVE convergent series — and set
`psiLineRe5 := ψ(1/4) + corrCore`.

THE TELESCOPING (regularity, from scratch). `cₙ ≤ tel(n) − tel(n+1)` with `tel(n) = 100/(4n+1)`,
for ALL `n` — the comparison reduces to `(4n−1)² + 380 ≥ 0` (a manifest square). So the partial
sums are Cauchy with the depth schedule `j ↦ 25(j+1)` (`tail ≤ tel(25(j+1)) = 100/(100j+101) ≤
1/(j+1)`), giving a regular sequence in the Bishop sense.

THE CONSEQUENCE. `Re ψ(1/4 + 5i) ≥ −4.32 + Σ_{n<12} cₙ ≥ −4.32 + 5.6 = 1.28 > log π`, so the
Riemann–Siegel center slope `θ′(0) = ½(ψ(1/4) − log π) < 0` (`RiemannSiegel.rsCenterSlope_neg`) is
matched by a POSITIVE slope out at `τ = 10`: `θ′(10) = ½(Re ψ(1/4+5i) − log π) > 0`. The angle
DECREASES through the center and INCREASES out on the line — non-monotone, two-sided, an axiom-clean
theorem. This is exactly the bounded-negative-band structure Burnol / Connes–Consani must work
around; it is the obstruction, sharpened, NOT a route through it. Crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.PsiQuarter
import F1Square.Analysis.DigammaWindow
import F1Square.Analysis.RiemannSiegel

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The positive correction term cₙ = s/((n+1/4)((n+1/4)²+s)) at s = 25 (τ = 10),
-- in exact-rational form 1600/((4n+1)((4n+1)²+400)), and its telescoping bound.
-- ===========================================================================

/-- The positive correction `cₙ = 1600/[(4n+1)((4n+1)²+400)]` — the gain of `Re ψ(1/4+iτ/2)` over
    `ψ(1/4)` at `s = τ²/4 = 25`, summand by summand. -/
private def corrT (n : Nat) : Q := ⟨1600, (4 * n + 1) * ((4 * n + 1) * (4 * n + 1) + 400)⟩

private theorem corrT_den_pos (n : Nat) : 0 < (corrT n).den :=
  Nat.mul_pos (by omega) (by omega)

/-- The telescoping comparison value `tel(n) = 100/(4n+1)`. -/
private def corrTel (n : Nat) : Q := ⟨100, 4 * n + 1⟩

private theorem corrTel_den_pos (n : Nat) : 0 < (corrTel n).den := by
  show 0 < 4 * n + 1; omega

/-- The positive partial sums `S(N) = Σ_{i<N} cᵢ`. -/
private def corrP : Nat → Q
  | 0 => ⟨0, 1⟩
  | (N + 1) => add (corrP N) (corrT N)

private theorem corrP_den_pos : ∀ N, 0 < (corrP N).den
  | 0 => by decide
  | (N + 1) => add_den_pos (corrP_den_pos N) (corrT_den_pos N)

/-- **The per-term telescoping bound** `cₙ ≤ tel(n) − tel(n+1)` for ALL `n` — the comparison reduces
    to `(4n−1)² + 380 ≥ 0`, a manifest square (with `K = 100`). -/
private theorem corrT_le_teldiff (n : Nat) :
    Qle (corrT n) (Qsub (corrTel n) (corrTel (n + 1))) := by
  simp only [corrT, corrTel, Qsub, Qle, add, neg]
  push_cast
  have key :
      (100 * (4 * ((n : Int) + 1) + 1) + -100 * (4 * (n : Int) + 1))
        * ((4 * (n : Int) + 1) * ((4 * (n : Int) + 1) * (4 * (n : Int) + 1) + 400))
      = 1600 * ((4 * (n : Int) + 1) * (4 * ((n : Int) + 1) + 1))
        + 400 * (4 * (n : Int) + 1) * ((4 * (n : Int) - 1) * (4 * (n : Int) - 1) + 380) := by
    ring_uor
  rw [key]
  have hnn : (0 : Int) ≤ 400 * (4 * (n : Int) + 1)
      * ((4 * (n : Int) - 1) * (4 * (n : Int) - 1) + 380) := by
    refine Int.mul_nonneg (Int.mul_nonneg (by decide) (by omega)) ?_
    have hsq : (0 : Int) ≤ (4 * (n : Int) - 1) * (4 * (n : Int) - 1) := by
      rcases Int.le_total 0 (4 * (n : Int) - 1) with h | h
      · exact Int.mul_nonneg h h
      · have h' : (0 : Int) ≤ -(4 * (n : Int) - 1) := by omega
        have hh : (0 : Int) ≤ (-(4 * (n : Int) - 1)) * (-(4 * (n : Int) - 1)) := Int.mul_nonneg h' h'
        simpa using hh
    omega
  omega

-- ===========================================================================
-- The monotone auxiliary g(m) = S(m) + tel(m), and the tail bound.
-- ===========================================================================

/-- `g(m) = S(m) + tel(m)`. -/
private def corrG (m : Nat) : Q := add (corrP m) (corrTel m)

private theorem corrG_den_pos (m : Nat) : 0 < (corrG m).den :=
  add_den_pos (corrP_den_pos m) (corrTel_den_pos m)

/-- `cₘ + tel(m+1) ≤ tel(m)` (the telescoping step, rearranged). -/
private theorem corrT_tel_le (m : Nat) :
    Qle (add (corrT m) (corrTel (m + 1))) (corrTel m) := by
  have hadd := Qadd_le_add (corrT_le_teldiff m) (Qle_refl (corrTel (m + 1)))
  have e3 : Qeq (add (Qsub (corrTel m) (corrTel (m + 1))) (corrTel (m + 1))) (corrTel m) := by
    simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor
  refine Qle_trans ?_ hadd (Qeq_le e3)
  exact add_den_pos (Qsub_den_pos (corrTel_den_pos m) (corrTel_den_pos (m + 1)))
    (corrTel_den_pos (m + 1))

/-- One step: `g(m+1) ≤ g(m)`. -/
private theorem corrG_step (m : Nat) : Qle (corrG (m + 1)) (corrG m) := by
  show Qle (add (add (corrP m) (corrT m)) (corrTel (m + 1))) (add (corrP m) (corrTel m))
  have e1 : Qeq (add (add (corrP m) (corrT m)) (corrTel (m + 1)))
      (add (corrP m) (add (corrT m) (corrTel (m + 1)))) := by
    simp only [Qeq, add]; push_cast; ring_uor
  refine Qle_trans ?_ (Qeq_le e1) (Qadd_le_add (Qle_refl (corrP m)) (corrT_tel_le m))
  exact add_den_pos (corrP_den_pos m) (add_den_pos (corrT_den_pos m) (corrTel_den_pos (m + 1)))

/-- `g(a+b) ≤ g(a)` (monotone descent, from `m = 0`). -/
private theorem corrG_mono : ∀ a b, Qle (corrG (a + b)) (corrG a)
  | _, 0 => Qle_refl _
  | a, (b + 1) => by
    have h := corrG_mono a b
    have hstep := corrG_step (a + b)
    have e : a + (b + 1) = (a + b) + 1 := by omega
    rw [e]
    exact Qle_trans (corrG_den_pos (a + b)) hstep h

/-- `S` is monotone (positive terms). -/
private theorem corrP_mono {a b : Nat} (hab : a ≤ b) : Qle (corrP a) (corrP b) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hab
  clear hab
  induction d with
  | zero => exact Qle_refl _
  | succ k ih =>
    have e : a + (k + 1) = (a + k) + 1 := by omega
    rw [e]
    show Qle (corrP a) (add (corrP (a + k)) (corrT (a + k)))
    exact Qle_trans (corrP_den_pos (a + k)) ih (Qle_self_add (by show (0 : Int) ≤ 1600; decide))

-- ===========================================================================
-- The correction series as a constructive real (depth schedule j ↦ 25(j+1)).
-- ===========================================================================

/-- The correction sequence `S(25(j+1))` (depth schedule `j ↦ 25(j+1)`). -/
private def corrseq (j : Nat) : Q := corrP (25 * (j + 1))

private theorem corrseq_den_pos (j : Nat) : 0 < (corrseq j).den :=
  corrP_den_pos (25 * (j + 1))

/-- **The regularity tail bound** `|S(25(k+1)) − S(25(j+1))| ≤ 1/(j+1)` for `j ≤ k`. -/
private theorem corrseq_reg_le {j k : Nat} (hjk : j ≤ k) :
    Qle (Qabs (Qsub (corrseq j) (corrseq k))) (Qbound j) := by
  rw [Qabs_Qsub_comm]
  obtain ⟨d, hd⟩ := Nat.le.dest hjk
  have hge : Qle (corrP (25 * (j + 1))) (corrP (25 * (k + 1))) := corrP_mono (by omega)
  have hnn : (0 : Int) ≤ (Qsub (corrP (25 * (k + 1))) (corrP (25 * (j + 1)))).num :=
    num_nonneg_of_Qzero_le (Qsub_nonneg_of_le hge)
  have htail : Qle (Qsub (corrP (25 * (k + 1))) (corrP (25 * (j + 1)))) (corrTel (25 * (j + 1))) := by
    have hgm : Qle (corrG (25 * (k + 1))) (corrG (25 * (j + 1))) := by
      have e : 25 * (k + 1) = 25 * (j + 1) + 25 * d := by omega
      rw [e]; exact corrG_mono (25 * (j + 1)) (25 * d)
    have hSg : Qle (corrP (25 * (k + 1))) (corrG (25 * (k + 1))) := by
      show Qle (corrP (25 * (k + 1))) (add (corrP (25 * (k + 1))) (corrTel (25 * (k + 1))))
      exact Qle_self_add (by show (0 : Int) ≤ 100; decide)
    have hchain : Qle (corrP (25 * (k + 1))) (add (corrP (25 * (j + 1))) (corrTel (25 * (j + 1)))) :=
      Qle_trans (corrG_den_pos (25 * (k + 1))) hSg hgm
    exact Qsub_le_of_le_add (corrP_den_pos (25 * (j + 1))) (corrTel_den_pos (25 * (j + 1))) hchain
  have hbnd : Qle (corrTel (25 * (j + 1))) (Qbound j) := by
    show (100 : Int) * ((j + 1 : Nat) : Int) ≤ (1 : Int) * ((4 * (25 * (j + 1)) + 1 : Nat) : Int)
    push_cast; omega
  -- `corrseq k ≡ corrP (25(k+1))` definitionally, so `habs` already has the goal's type.
  exact Qle_trans (corrTel_den_pos (25 * (j + 1))) (Qabs_le_of_nonneg hnn htail) hbnd

private theorem corrseq_regular : IsRegular corrseq := by
  intro m n
  rcases Nat.le_total m n with h | h
  · exact Qle_trans (Qbound_den_pos m) (corrseq_reg_le h) (Qle_self_add (by show (0 : Int) ≤ 1; decide))
  · rw [Qabs_Qsub_comm]
    exact Qle_trans (Qbound_den_pos n) (corrseq_reg_le h) (Qle_add_self (by show (0 : Int) ≤ 1; decide))

/-- **The correction series** `Σ_{n≥0} cₙ = Σ 1600/[(4n+1)((4n+1)²+400)]` as a genuine constructive
    real — the gain of `Re ψ(1/4 + 5i)` over `ψ(1/4)`. Manifestly positive (sum of positives). -/
def corrCore : Real := ⟨corrseq, corrseq_regular, corrseq_den_pos⟩

/-- **`corrCore ≥ S(12)`**: the limit dominates the 12-term partial sum (the depth schedule starts at
    `25 > 12`, so every approximant `S(25(j+1))` already dominates `S(12)` by monotonicity). -/
theorem corrCore_ge_twelve : Rle (ofQ (corrP 12) (corrP_den_pos 12)) corrCore := by
  intro j
  show Qle (corrP 12) (add (corrP (25 * (j + 1))) ⟨2, j + 1⟩)
  exact Qle_trans (corrP_den_pos (25 * (j + 1))) (corrP_mono (by omega))
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **`S(12) ≥ 5.6`**: the 12-term partial sum, certified (true value `≈ 5.7534`). -/
theorem corrP_twelve_lower : Rle (ofQ (⟨56, 10⟩ : Q) (by decide)) (ofQ (corrP 12) (corrP_den_pos 12)) :=
  Rle_ofQ_ofQ (by decide) (corrP_den_pos 12) (by decide)

/-- **`corrCore ≥ 5.6`**, the certified lower bracket of the correction series. -/
theorem corrCore_lower : Rle (ofQ (⟨56, 10⟩ : Q) (by decide)) corrCore :=
  Rle_trans corrP_twelve_lower corrCore_ge_twelve

-- ===========================================================================
-- The assembled archimedean kernel Re ψ(1/4 + 5i) and its lower bracket.
-- ===========================================================================

/-- **`Re ψ(1/4 + 5i)`** — the archimedean kernel at the frontier point `τ = 10` (`s = τ²/4 = 25`),
    `= ψ(1/4) + Σ cₙ`. The first assembled value of `Re ψ` along the critical line off-center. -/
def psiLineRe5 : Real := Radd psiQuarter corrCore

/-- **The faithfulness bridge**: the correction term `cₙ` IS the gain of the `DigammaWindow` kernel
    term over its center value, `windowTerm n 25 1 = windowTerm n 0 1 + cₙ` — i.e. `psiLineRe5` is
    built from exactly `DigammaWindow`'s `Re ψ` summands at `s = 25`. -/
theorem corrT_eq_windowTerm_gain (n : Nat) :
    Qeq (corrT n) (Qsub (windowTerm n 25 1) (windowTerm n 0 1)) := by
  simp only [corrT, windowTerm, windowKernel, Qsub, Qeq, add, neg]; push_cast; ring_uor

/-- **The lower bracket `Re ψ(1/4 + 5i) ≥ 1.28`** (true value `≈ 1.61`), from `ψ(1/4) ≥ −4.32`
    (`psiQuarter_lower`) and `Σ cₙ ≥ 5.6` (`corrCore_lower`). Comfortably above `log π ≈ 1.1447` —
    the climb of the archimedean kernel out along the critical line. -/
theorem psiLineRe5_lower : Rle (ofQ (⟨128, 100⟩ : Q) (by decide)) psiLineRe5 := by
  have hsum := Radd_le_add psiQuarter_lower corrCore_lower
  refine Rle_trans ?_ hsum
  refine Rle_trans (Rle_of_Req (ofQ_congr (by decide)
    (add_den_pos (by decide) (by decide)) ?_)) (Rle_ofQ_add_Radd (by decide) (by decide))
  decide

-- ===========================================================================
-- The capstone: the Riemann–Siegel angle is non-monotone, two-sided.
-- ===========================================================================

/-- **`θ′(10) > 0` — the Riemann–Siegel angle INCREASES out at `τ = 10`.** `Re ψ(1/4 + 5i) − log π >
    0`, from `Re ψ(1/4 + 5i) ≥ 1.28` (`psiLineRe5_lower`) and `log π ≤ 1.1453` (`Rlogπc_le`): the
    line slope discriminant `≥ 1.28 − 1.15 = 0.13 > 0`. (Same `log π = Rlogπc` as the center slope.) -/
theorem rsLineSlope10_pos : Pos (Rsub psiLineRe5 Rlogπc) := by
  have hlogle : Rle Rlogπc (ofQ (⟨115, 100⟩ : Q) (by decide)) :=
    Rle_trans Rlogπc_le (Rle_ofQ_ofQ _ (by decide) (by decide))
  have hstep : Rle (Rsub (ofQ (⟨128, 100⟩ : Q) (by decide)) (ofQ (⟨115, 100⟩ : Q) (by decide)))
      (Rsub psiLineRe5 Rlogπc) :=
    Rsub_le_sub psiLineRe5_lower hlogle
  refine Pos_of_Rle_ofQ (c := (⟨13, 100⟩ : Q)) (by decide) (by decide) (Rle_trans ?_ hstep)
  intro n
  show Qle (⟨13, 100⟩ : Q) (add (add (⟨128, 100⟩ : Q) (neg (⟨115, 100⟩ : Q))) ⟨2, n + 1⟩)
  simp only [Qle, add, neg]
  push_cast
  omega

/-- **THE RIEMANN–SIEGEL ANGLE IS NON-MONOTONE — TWO-SIDED, an axiom-clean theorem.** For the same
    angle `θ(t) = arg Γ(1/4 + i t/2) − (t/2)·log π` (one `log π = Rlogπc`):
    * `θ′(0) < 0` — the center slope is negative (`rsCenterSlope_neg`); `θ` DECREASES through the
      symmetry point `t = 0`;
    * `θ′(10) > 0` — out at `τ = 10` the line slope is positive (`rsLineSlope10_pos`); `θ` INCREASES.
    The slope changes sign, so `θ` is genuinely non-monotone — the bounded-negative-band structure
    Burnol / Connes–Consani must work around. The obstruction, completed as a two-sided theorem from
    the FIRST assembled value of the archimedean kernel `Re ψ(1/4 + iτ/2)` off-center (`psiLineRe5`,
    `= ψ(1/4) + Σ cₙ`). This sharpens the barrier; it does NOT cross it. The crux fields stay `none`. -/
theorem rsAngle_non_monotone : Pos (Rneg rsCenterSlope) ∧ Pos (Rsub psiLineRe5 Rlogπc) :=
  ⟨rsCenterSlope_neg, rsLineSlope10_pos⟩

end UOR.Bridge.F1Square.Analysis
