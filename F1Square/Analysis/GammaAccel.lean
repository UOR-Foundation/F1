/-
F1 square — the **Euler–Mascheroni constant γ via the convergence-accelerated harmonic route**, whose
approximants have small denominators so that `Pos λ₁` is kernel-certifiable.

Standard definition, realized in *telescoped* form (so no log-additivity lemma is needed):

  γ = Σ_{i≥1} cᵢ,   cᵢ = 1/i − log((i+1)/i) = 1/i − 2·artanh(1/(2i+1)),   0 ≤ cᵢ ≤ 1/(i(i+1)).

Each consecutive-ratio log has a *small* artanh argument `1/(2i+1)` (fast geometric convergence),
unlike `log(n+1)` directly (argument `→ 1`). The series is built as a single rational diagonal (à la
`Rpi`, `gammaSeq`), reusing the artanh partial sum `artSum` (Log.lean); its termwise bracket
`0 ≤ cᵢ ≤ 1/(i(i+1))` rests on the two analytic facts `t ≤ artanh t ≤ t/(1−t²)`, mechanized here as
rational bounds on `artSum`.

This file builds the analytic foundation (the `artSum` bounds). The diagonal, its regularity, the
γ-lower bracket, and `Pos λ₁` follow. Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.Log
import F1Square.Analysis.Euler

namespace UOR.Bridge.F1Square.Analysis

/-! ### Rational lower bound: `artSum t N ≥ t` (the first series term, for `t ≥ 0`) -/

/-- Each artanh term is non-negative for a non-negative base. -/
theorem artTerm_num_nonneg {t : Q} (ht0 : 0 ≤ t.num) (n : Nat) : 0 ≤ (artTerm t n).num := by
  show 0 ≤ (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩).num
  simp only [mul]
  have := qpow_nonneg ht0 (2 * n + 1)
  omega

/-- The artanh partial sums are monotone (one step), for a non-negative base. -/
theorem artSum_step {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (artSum t N) (artSum t (N + 1)) := by
  show Qle (artSum t N) (add (artSum t N) (artTerm t (N + 1)))
  exact Qle_self_add (artTerm_num_nonneg ht0 (N + 1))

/-- The artanh partial sums are monotone, for a non-negative base. -/
theorem artSum_mono {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) {a b : Nat} (hab : a ≤ b) :
    Qle (artSum t a) (artSum t b) := by
  induction hab with
  | refl => exact Qle_refl _
  | step _ ih => exact Qle_trans (artSum_den_pos htd _) ih (artSum_step ht0 htd _)

/-- The first partial sum is the base: `artSum t 0 ≈ t`. -/
theorem artSum_zero_eq (t : Q) : Qeq (artSum t 0) t := by
  show Qeq (mul (qpow t (2 * 0 + 1)) ⟨1, 2 * 0 + 1⟩) t
  have hq : qpow t 1 = mul t (qpow t 0) := qpow_succ t 0
  show Qeq (mul (qpow t 1) ⟨1, 1⟩) t
  rw [hq]
  simp only [Qeq, mul, qpow]; push_cast; ring_uor

/-- **`artSum t N ≥ t`** for a non-negative base — the artanh lower bound at the rational level. -/
theorem artSum_ge_arg {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle t (artSum t N) :=
  Qle_trans (artSum_den_pos htd 0) (Qeq_le (Qeq_symm (artSum_zero_eq t)))
    (artSum_mono ht0 htd (Nat.zero_le N))

/-! ### Rational geometric upper bound: `artSum t N · (1−t²) ≤ t` -/

/-- Each artanh term is `≤` the geometric term (since `1/(2n+1) ≤ 1`). -/
theorem artTerm_le_geoTerm {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (n : Nat) :
    Qle (artTerm t n) (geoTerm t n) := by
  show Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (qpow t (2 * n + 1))
  have h1 : Qle (⟨1, 2 * n + 1⟩ : Q) ⟨1, 1⟩ := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((2 * n + 1 : Nat) : Int); push_cast; omega
  have h2 : Qle (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩) (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) :=
    Qmul_le_mul_left (qpow_nonneg ht0 _) h1
  have h3 : Qeq (mul (qpow t (2 * n + 1)) ⟨1, 1⟩) (qpow t (2 * n + 1)) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  exact Qle_trans (Qmul_den_pos (qpow_den_pos htd _) Nat.one_pos) h2 (Qeq_le h3)

/-- The artanh partial sum is `≤` the geometric partial sum. -/
theorem artSum_le_geoSum {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) :
    ∀ N, Qle (artSum t N) (geoSum t N)
  | 0 => artTerm_le_geoTerm ht0 htd 0
  | (N + 1) => by
      show Qle (add (artSum t N) (artTerm t (N + 1))) (add (geoSum t N) (geoTerm t (N + 1)))
      exact Qadd_le_add (artSum_le_geoSum ht0 htd N) (artTerm_le_geoTerm ht0 htd (N + 1))

/-- Cleared geometric closed bound: `geoSum t N · (1−t²) ≤ t` (drop the non-negative `t^{2N+3}`). -/
theorem geoSum_cleared_le {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den) (N : Nat) :
    Qle (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have hU := geoU_eq htd N
  exact Qle_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos htd N)
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) (qpow_den_pos htd _))
    (Qle_self_add (qpow_nonneg ht0 _)) (Qeq_le hU)

/-- **The cleared artanh geometric upper bound**: `artSum t N · (1−t²) ≤ t`. -/
theorem artSum_le_geo {t : Q} (ht0 : 0 ≤ t.num) (htd : 0 < t.den)
    (hWnn : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul t t)).num) (N : Nat) :
    Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t))) t := by
  have h1 : Qle (mul (artSum t N) (Qsub ⟨1, 1⟩ (mul t t)))
      (mul (geoSum t N) (Qsub ⟨1, 1⟩ (mul t t))) :=
    Qmul_le_mul_right hWnn (artSum_le_geoSum ht0 htd N)
  exact Qle_trans (Qmul_den_pos (geoSum_den_pos htd N)
    (Qsub_den_pos Nat.one_pos (Nat.mul_pos htd htd))) h1 (geoSum_cleared_le ht0 htd N)

/-! ### Step 2: the γ-term bracket `0 ≤ 1/(n+1) − 2·artSum(1/(2n+3),T) ≤ 1/((n+1)(n+2))` -/

/-- `2·artSum ≥ 1/(n+2)` (from `artSum ≥` its argument `1/(2n+3)`). -/
theorem two_artSum_ge (n T : Nat) :
    Qle (⟨1, n + 2⟩ : Q) (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T)) := by
  have htd : 0 < (⟨1, 2 * n + 3⟩ : Q).den := by show 0 < 2 * n + 3; omega
  have ht0 : (0 : Int) ≤ (⟨1, 2 * n + 3⟩ : Q).num := by show (0 : Int) ≤ 1; decide
  have h1 : Qle (⟨1, 2 * n + 3⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T) := artSum_ge_arg ht0 htd T
  have h2 := Qmul_le_mul_left (show (0 : Int) ≤ (⟨2, 1⟩ : Q).num by decide) h1
  refine Qle_trans (Qmul_den_pos (by decide) htd) ?_ h2
  simp only [Qle, mul]; push_cast; omega

/-- `2·artSum ≤ 1/(n+1)` (from the geometric bound `artSum·(1−t²) ≤ t`, then cancel `1−t²`). -/
theorem two_artSum_le (n T : Nat) :
    Qle (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T)) (⟨1, n + 1⟩ : Q) := by
  have htd : 0 < (⟨1, 2 * n + 3⟩ : Q).den := by show 0 < 2 * n + 3; omega
  have ht0 : (0 : Int) ≤ (⟨1, 2 * n + 3⟩ : Q).num := by show (0 : Int) ≤ 1; decide
  have hWn : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).num := by
    show 0 < (add (⟨1, 1⟩ : Q) (neg (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩))).num
    simp only [add, neg, mul]
    have h9 : ((9 : Nat) : Int) ≤ (((2 * n + 3) * (2 * n + 3) : Nat) : Int) := by
      exact_mod_cast Nat.mul_le_mul (show 3 ≤ 2 * n + 3 by omega) (show 3 ≤ 2 * n + 3 by omega)
    push_cast at h9 ⊢; omega
  have hWd : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)).den :=
    Qsub_den_pos Nat.one_pos (Qmul_den_pos htd htd)
  refine Qmul_le_cancel_right hWn hWd ?_
  have hge := artSum_le_geo (t := ⟨1, 2 * n + 3⟩) ht0 htd (Int.le_of_lt hWn) T
  have hassoc : Qeq
      (mul (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q)
        (mul (artSum ⟨1, 2 * n + 3⟩ T) (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))) := by
    simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor
  have hLHS : Qle
      (mul (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))
        (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
      (mul (⟨2, 1⟩ : Q) ⟨1, 2 * n + 3⟩) :=
    Qle_trans (Qmul_den_pos (by decide) (Qmul_den_pos (artSum_den_pos htd T) hWd))
      (Qeq_le hassoc) (Qmul_le_mul_left (by decide) hge)
  refine Qle_trans (Qmul_den_pos (by decide) htd) hLHS ?_
  have hmono : (2 * (n : Int) + 3) ≤ 2 * (n + 2) := by omega
  have hnn : (0 : Int) ≤ 2 * ((n : Int) + 1) * (2 * n + 3) :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hstep := Int.mul_le_mul_of_nonneg_left hmono hnn
  have hkey : (2 : Int) * ((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3))
      ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) - 1) * (2 * (n : Int) + 3) := by
    calc (2 : Int) * ((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3))
        = (2 * ((n : Int) + 1) * (2 * (n : Int) + 3)) * (2 * (n : Int) + 3) := by ring_uor
      _ ≤ (2 * ((n : Int) + 1) * (2 * (n : Int) + 3)) * (2 * ((n : Int) + 2)) := hstep
      _ = ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) - 1) * (2 * (n : Int) + 3) := by ring_uor
  have hcmp_int : 2 * (((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)))
      ≤ ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * (2 * (n : Int) + 3) := by
    have hid : ((2 * (n : Int) + 3) * (2 * (n : Int) + 3) + -1) * (2 * (n : Int) + 3)
        - 2 * (((n : Int) + 1) * ((2 * (n : Int) + 3) * (2 * (n : Int) + 3)))
        = 2 * ((n : Int) + 1) * (2 * (n : Int) + 3) := by ring_uor
    have hpos : (0 : Int) ≤ 2 * ((n : Int) + 1) * (2 * (n : Int) + 3) :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
    omega
  show Qle (mul (⟨2, 1⟩ : Q) ⟨1, 2 * n + 3⟩)
    (mul (⟨1, n + 1⟩ : Q) (Qsub ⟨1, 1⟩ (mul ⟨1, 2 * n + 3⟩ ⟨1, 2 * n + 3⟩)))
  simp only [Qle, mul, Qsub, add, neg]
  push_cast
  simp only [Int.one_mul]
  exact hcmp_int

/-- The `n`-th γ-term approximant `cApprox(n,T) = 1/(n+1) − 2·artSum(1/(2n+3),T)` (harmonic index
    `i = n+1`). Bracketed in `[0, 1/((n+1)(n+2))]` **uniformly in the artanh depth `T`**. -/
def cApprox (n T : Nat) : Q := Qsub ⟨1, n + 1⟩ (mul ⟨2, 1⟩ (artSum ⟨1, 2 * n + 3⟩ T))

theorem cApprox_den_pos (n T : Nat) : 0 < (cApprox n T).den :=
  Qsub_den_pos (by show 0 < n + 1; omega)
    (Qmul_den_pos (by decide) (artSum_den_pos (by show 0 < 2 * n + 3; omega) T))

theorem cApprox_num_nonneg (n T : Nat) : 0 ≤ (cApprox n T).num :=
  num_nonneg_of_Qzero_le (Qsub_nonneg_of_le (two_artSum_le n T))

theorem cApprox_ub (n T : Nat) : Qle (cApprox n T) (⟨1, (n + 1) * (n + 2)⟩ : Q) := by
  have hneg : Qle (neg (mul (⟨2, 1⟩ : Q) (artSum ⟨1, 2 * n + 3⟩ T))) (neg ⟨1, n + 2⟩) :=
    Qneg_le_neg (two_artSum_ge n T)
  have hstep : Qle (cApprox n T) (Qsub (⟨1, n + 1⟩ : Q) ⟨1, n + 2⟩) := by
    show Qle (add (⟨1, n + 1⟩ : Q) (neg (mul ⟨2, 1⟩ (artSum ⟨1, 2 * n + 3⟩ T))))
      (add ⟨1, n + 1⟩ (neg ⟨1, n + 2⟩))
    exact Qadd_le_add (Qle_refl _) hneg
  have heq : Qeq (Qsub (⟨1, n + 1⟩ : Q) ⟨1, n + 2⟩) (⟨1, (n + 1) * (n + 2)⟩ : Q) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  exact Qle_trans (Qsub_den_pos (by show 0 < n + 1; omega) (by show 0 < n + 2; omega)) hstep
    (Qeq_le heq)

end UOR.Bridge.F1Square.Analysis
