/-
F1 square — `log` on the positive reals (v0.13.0 transcendental).

`log(x) = 2·artanh(t)`, `t = (x−1)/(x+1)`, `artanh(t) = Σₙ t^{2n+1}/(2n+1)` for `|t| < 1`. Unlike the
exp/cos/sin series (factorial tails), the artanh series is **geometric**: for `|t| ≤ ρ < 1` the tail is
`Σ_{n>N} ρ^{2n+1}/(2n+1) ≤ ρ^{2N+3}/(1−ρ²)`, which → 0 geometrically; a Bernoulli estimate turns it into
a `1/(j+1)` reindex. This file builds that geometric machinery (the telescoping invariant, the tail
bound) — the foundation for `artanh` and hence `log`.

Pure Lean 4, no Mathlib, no `sorry`.
-/

import F1Square.Analysis.CosSin

namespace UOR.Bridge.F1Square.Analysis

/-- `ρ^{2n+1}`, the `n`-th geometric term. -/
def geoTerm (ρ : Q) (n : Nat) : Q := qpow ρ (2 * n + 1)

/-- `Σ_{n=0}^N ρ^{2n+1}`. -/
def geoSum (ρ : Q) : Nat → Q
  | 0 => geoTerm ρ 0
  | (n + 1) => add (geoSum ρ n) (geoTerm ρ (n + 1))

theorem geoSum_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ N, 0 < (geoSum ρ N).den
  | 0 => qpow_den_pos hρd _
  | (n + 1) => add_den_pos (geoSum_den_pos hρd n) (qpow_den_pos hρd _)

-- The telescoping ring identity `(G+P)(1−R²) + R²P ≈ G(1−R²) + P`.
private theorem geo_step_eq (G P R : Q) :
    Qeq (add (mul (add G P) (Qsub ⟨1, 1⟩ (mul R R))) (mul R (mul R P)))
      (add (mul G (Qsub ⟨1, 1⟩ (mul R R))) P) := by
  simp only [Qeq, add, mul, Qsub, neg]; push_cast; ring_uor

/-- **The geometric telescoping invariant**: `S_N·(1−ρ²) + ρ^{2N+3} = ρ` for every `N`. -/
theorem geoU_eq {ρ : Q} (hρd : 0 < ρ.den) : ∀ N,
    Qeq (add (mul (geoSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * N + 3))) ρ
  | 0 => by
      show Qeq (add (mul (geoTerm ρ 0) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 3)) ρ
      simp only [geoTerm, qpow, Qeq, add, mul, Qsub, neg]; push_cast; ring_uor
  | (N + 1) => by
      refine Qeq_trans (add_den_pos (Qmul_den_pos (geoSum_den_pos hρd N)
          (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd (2 * N + 3)))
        ?_ (geoU_eq hρd N)
      have hgs : geoSum ρ (N + 1) = add (geoSum ρ N) (qpow ρ (2 * N + 3)) := by
        show add (geoSum ρ N) (geoTerm ρ (N + 1)) = add (geoSum ρ N) (qpow ρ (2 * N + 3))
        unfold geoTerm; rw [show 2 * (N + 1) + 1 = 2 * N + 3 from by omega]
      have hpw : qpow ρ (2 * (N + 1) + 3) = mul ρ (mul ρ (qpow ρ (2 * N + 3))) := by
        rw [show 2 * (N + 1) + 3 = (2 * N + 3) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hgs, hpw]
      exact geo_step_eq (geoSum ρ N) (qpow ρ (2 * N + 3)) ρ

-- `P·(1−R²) ≈ P − R²·P`  and the 3-point telescoping `(A−B)+(B−C) ≈ A−C` (abstract ring identities).
private theorem geo_term_id (P R : Q) :
    Qeq (mul P (Qsub ⟨1, 1⟩ (mul R R))) (Qsub P (mul R (mul R P))) := by
  simp only [Qeq, mul, Qsub, add, neg]; push_cast; ring_uor

private theorem Qsub_telescope (A B C : Q) :
    Qeq (add (Qsub A B) (Qsub B C)) (Qsub A C) := by
  simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor

/-- **The exact geometric difference**: `(S_b − S_a)·(1−ρ²) = ρ^{2a+3} − ρ^{2b+3}` for `a ≤ b`. -/
theorem geo_diff_eq {ρ : Q} (hρd : 0 < ρ.den) (a : Nat) : ∀ {b}, a ≤ b →
    Qeq (mul (Qsub (geoSum ρ b) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (Qsub (qpow ρ (2 * a + 3)) (qpow ρ (2 * b + 3))) := by
  have hW : 0 < (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).den := Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)
  intro b hab
  induction hab with
  | refl =>
      have h1 : (mul (Qsub (geoSum ρ a) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ))).num = 0 := by
        show (Qsub (geoSum ρ a) (geoSum ρ a)).num * (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num = 0
        rw [Qsub_self_num]; exact Int.zero_mul _
      have h2 : (Qsub (qpow ρ (2 * a + 3)) (qpow ρ (2 * a + 3))).num = 0 := Qsub_self_num _
      unfold Qeq; rw [h1, h2]; simp
  | @step k hk ih =>
      -- regroup S_{k+1} − S_a = (S_k − S_a) + ρ^{2k+3}
      have hgs : Qeq (Qsub (geoSum ρ (k + 1)) (geoSum ρ a))
          (add (Qsub (geoSum ρ k) (geoSum ρ a)) (qpow ρ (2 * k + 3))) := by
        have h := Qsub_add_right (geoSum ρ k) (geoTerm ρ (k + 1)) (geoSum ρ a)
        rw [show geoTerm ρ (k + 1) = qpow ρ (2 * k + 3) by
          unfold geoTerm; rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]] at h
        exact h
      have hpw : qpow ρ (2 * (k + 1) + 3) = mul ρ (mul ρ (qpow ρ (2 * k + 3))) := by
        rw [show 2 * (k + 1) + 3 = (2 * k + 3) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hpw]
      have d1 := Qmul_den_pos (add_den_pos (Qsub_den_pos (geoSum_den_pos hρd k)
        (geoSum_den_pos hρd a)) (qpow_den_pos hρd (2 * k + 3))) hW
      have d2 := add_den_pos (Qmul_den_pos (Qsub_den_pos (geoSum_den_pos hρd k)
        (geoSum_den_pos hρd a)) hW) (Qmul_den_pos (qpow_den_pos hρd (2 * k + 3)) hW)
      have d3 := add_den_pos (Qsub_den_pos (qpow_den_pos hρd (2 * a + 3)) (qpow_den_pos hρd (2 * k + 3)))
        (Qsub_den_pos (qpow_den_pos hρd (2 * k + 3))
          (Qmul_den_pos hρd (Qmul_den_pos hρd (qpow_den_pos hρd (2 * k + 3)))))
      exact Qeq_trans d1 (Qmul_congr hgs (Qeq_refl _))
        (Qeq_trans d2 (Qmul_add_right (Qsub (geoSum ρ k) (geoSum ρ a)) (qpow ρ (2 * k + 3))
          (Qsub ⟨1, 1⟩ (mul ρ ρ)))
          (Qeq_trans d3 (Qadd_congr ih (geo_term_id (qpow ρ (2 * k + 3)) ρ))
            (Qsub_telescope (qpow ρ (2 * a + 3)) (qpow ρ (2 * k + 3))
              (mul ρ (mul ρ (qpow ρ (2 * k + 3)))))))

/-- `Qsub a b ≤ a` when `0 ≤ b.num`. -/
theorem Qsub_le_self {a b : Q} (hb : 0 ≤ b.num) : Qle (Qsub a b) a := by
  show (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      ≤ a.num * ((a.den : Int) * (b.den : Int))
  have hd : (0 : Int) ≤ (a.den : Int) * (a.den : Int) :=
    Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)
  have hbn : 0 ≤ b.num * ((a.den : Int) * (a.den : Int)) := Int.mul_nonneg hb hd
  have e : a.num * ((a.den : Int) * (b.den : Int))
      - (a.num * (b.den : Int) + (-b.num) * (a.den : Int)) * (a.den : Int)
      = b.num * ((a.den : Int) * (a.den : Int)) := by ring_uor
  omega

/-- **The geometric tail bound**: `(S_b − S_a)·(1−ρ²) ≤ ρ^{2a+3}` for `a ≤ b`. -/
theorem geo_diff_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) {a b : Nat} (hab : a ≤ b) :
    Qle (mul (Qsub (geoSum ρ b) (geoSum ρ a)) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * a + 3)) :=
  Qle_trans (Qsub_den_pos (qpow_den_pos hρd _) (qpow_den_pos hρd _))
    (Qeq_le (geo_diff_eq hρd a hab))
    (Qsub_le_self (qpow_nonneg hρ0 _))

-- ===========================================================================
-- The artanh series Σ t^{2n+1}/(2n+1), dominated by the geometric series.
-- ===========================================================================

/-- The `n`-th artanh term `t^{2n+1}/(2n+1)`. -/
def artTerm (t : Q) (n : Nat) : Q := mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩

theorem artTerm_den_pos {t : Q} (htd : 0 < t.den) (n : Nat) : 0 < (artTerm t n).den :=
  Qmul_den_pos (qpow_den_pos htd _) (Nat.succ_pos _)

/-- The artanh partial sum `Σ_{n=0}^N t^{2n+1}/(2n+1)`. -/
def artSum (t : Q) : Nat → Q
  | 0 => artTerm t 0
  | (n + 1) => add (artSum t n) (artTerm t (n + 1))

theorem artSum_den_pos {t : Q} (htd : 0 < t.den) : ∀ N, 0 < (artSum t N).den
  | 0 => artTerm_den_pos htd 0
  | (n + 1) => add_den_pos (artSum_den_pos htd n) (artTerm_den_pos htd (n + 1))

/-- **Per-term domination**: `|t^{2n+1}/(2n+1)| ≤ ρ^{2n+1}` when `|t| ≤ ρ`. -/
theorem artTerm_abs_le {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (n : Nat) : Qle (Qabs (artTerm t n)) (geoTerm ρ n) := by
  have hpw : Qle (Qabs (qpow t (2 * n + 1))) (qpow ρ (2 * n + 1)) :=
    Qle_trans (qpow_den_pos (Qabs_den_pos htd) _) (Qeq_le (qpow_abs t (2 * n + 1)))
      (qpow_base_mono (Qabs_den_pos htd) hρd (Qabs_num_nonneg t) htρ (2 * n + 1))
  have h1 : Qabs (artTerm t n) = mul (Qabs (qpow t (2 * n + 1))) ⟨1, 2 * n + 1⟩ := by
    unfold artTerm; rw [Qabs_mul]; rfl
  rw [h1]
  refine Qle_trans (Qmul_den_pos (qpow_den_pos hρd _) (Nat.succ_pos _))
    (Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) hpw) ?_
  -- mul (qpow ρ (2n+1)) ⟨1,2n+1⟩ ≤ qpow ρ (2n+1) = geoTerm ρ n
  refine Qle_trans (Qmul_den_pos (qpow_den_pos hρd _) (Nat.succ_pos _))
    (Qmul_le_mul_left (qpow_nonneg hρ0 _) (show Qle (⟨1, 2 * n + 1⟩ : Q) ⟨1, 1⟩ by
      show (1 : Int) * 1 ≤ 1 * ((2 * n + 1 : Nat) : Int); push_cast; omega))
    (Qeq_le (mul_one (qpow ρ (2 * n + 1))))

/-- **Truncation domination**: `|artSum gap| ≤ S_b − S_a` (geometric). -/
theorem artSum_abs_diff_le {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) {a b : Nat} (hab : a ≤ b) :
    Qle (Qabs (Qsub (artSum t b) (artSum t a))) (Qsub (geoSum ρ b) (geoSum ρ a)) := by
  induction hab with
  | refl =>
      have h := Qsub_self_num (artSum t a)
      have h' := Qsub_self_num (geoSum ρ a)
      unfold Qle Qabs; rw [h, h']; simp
  | @step k _ ih =>
      have hstep : Qle (Qabs (Qsub (artSum t (k + 1)) (artSum t a)))
          (add (Qabs (Qsub (artSum t k) (artSum t a))) (Qabs (artTerm t (k + 1)))) := by
        have heqabs := Qabs_Qeq (Qsub_add_right (artSum t k) (artTerm t (k + 1)) (artSum t a))
        refine Qle_congr_left (Qabs_den_pos (add_den_pos (Qsub_den_pos (artSum_den_pos htd k)
          (artSum_den_pos htd a)) (artTerm_den_pos htd (k + 1)))) (Qeq_symm heqabs) (Qabs_add_le _ _)
      have hbound : Qle (add (Qabs (Qsub (artSum t k) (artSum t a))) (Qabs (artTerm t (k + 1))))
          (add (Qsub (geoSum ρ k) (geoSum ρ a)) (geoTerm ρ (k + 1))) :=
        Qadd_le_add ih (artTerm_abs_le htd hρ0 hρd htρ (k + 1))
      have hregroup : Qeq (add (Qsub (geoSum ρ k) (geoSum ρ a)) (geoTerm ρ (k + 1)))
          (Qsub (geoSum ρ (k + 1)) (geoSum ρ a)) :=
        Qeq_symm (Qsub_add_right (geoSum ρ k) (geoTerm ρ (k + 1)) (geoSum ρ a))
      refine Qle_trans
        (add_den_pos (Qabs_den_pos (Qsub_den_pos (artSum_den_pos htd k) (artSum_den_pos htd a)))
          (Qabs_den_pos (artTerm_den_pos htd (k + 1))))
        hstep
        (Qle_trans (add_den_pos (Qsub_den_pos (geoSum_den_pos hρd k) (geoSum_den_pos hρd a))
          (qpow_den_pos hρd _)) hbound (Qeq_le hregroup))

/-- **The artanh truncation tail**: `|artSum gap|·(1−ρ²) ≤ ρ^{2a+3}` for `|t| ≤ ρ`, `a ≤ b`. -/
theorem artSum_trunc {t ρ : Q} (htd : 0 < t.den) (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (hW : 0 ≤ (Qsub (⟨1, 1⟩ : Q) (mul ρ ρ)).num) {a b : Nat} (hab : a ≤ b) :
    Qle (mul (Qabs (Qsub (artSum t b) (artSum t a))) (Qsub ⟨1, 1⟩ (mul ρ ρ)))
      (qpow ρ (2 * a + 3)) :=
  Qle_trans (Qmul_den_pos (Qsub_den_pos (geoSum_den_pos hρd b) (geoSum_den_pos hρd a))
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd)))
    (Qmul_le_mul_right hW (artSum_abs_diff_le htd hρ0 hρd htρ hab))
    (geo_diff_bound hρ0 hρd hab)

-- ===========================================================================
-- The rational-base per-power difference bound (the ρ^{2n} decay the artanh Lipschitz needs).
-- ===========================================================================

/-- `|tⁱ| ≤ ρⁱ` when `|t| ≤ ρ` (rational base). -/
theorem qpow_abs_le_rat {t ρ : Q} (htd : 0 < t.den) (hρd : 0 < ρ.den) (htρ : Qle (Qabs t) ρ)
    (i : Nat) : Qle (Qabs (qpow t i)) (qpow ρ i) :=
  Qle_trans (qpow_den_pos (Qabs_den_pos htd) i) (Qeq_le (qpow_abs t i))
    (qpow_base_mono (Qabs_den_pos htd) hρd (Qabs_num_nonneg t) htρ i)

/-- The rational Lipschitz coefficient `i·ρ^{i-1}` (recursively, `P(0)=0`, `P(i+1)=ρ·P(i)+ρⁱ`). -/
def Pcoef (ρ : Q) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (i + 1) => add (mul ρ (Pcoef ρ i)) (qpow ρ i)

theorem Pcoef_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ i, 0 < (Pcoef ρ i).den
  | 0 => Nat.one_pos
  | (i + 1) => add_den_pos (Qmul_den_pos hρd (Pcoef_den_pos hρd i)) (qpow_den_pos hρd i)

theorem Pcoef_num_nonneg {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) : ∀ i, 0 ≤ (Pcoef ρ i).num
  | 0 => by show (0 : Int) ≤ 0; decide
  | (i + 1) => by
      show 0 ≤ (add (mul ρ (Pcoef ρ i)) (qpow ρ i)).num
      show (0 : Int) ≤ ρ.num * (Pcoef ρ i).num * ((qpow ρ i).den : Int)
        + (qpow ρ i).num * ((ρ.den : Int) * (Pcoef ρ i).den)
      exact Int.add_nonneg
        (Int.mul_nonneg (Int.mul_nonneg hρ0 (Pcoef_num_nonneg hρ0 hρd i)) (Int.ofNat_nonneg _))
        (Int.mul_nonneg (qpow_nonneg hρ0 i) (Int.mul_nonneg (Int.ofNat_nonneg _) (Int.ofNat_nonneg _)))

-- `ρ·(C·D) + D·P ≈ (ρ·C + P)·D` (abstract).
private theorem pcoef_factor (R C D P : Q) :
    Qeq (add (mul R (mul C D)) (mul D P)) (mul (add (mul R C) P) D) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- **Rational per-power difference bound**: `|tⁱ − t'ⁱ| ≤ (i·ρ^{i-1})·|t − t'|` for `|t|,|t'| ≤ ρ`. -/
theorem qpow_diff_bound_rat {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) :
    ∀ i, Qle (Qabs (Qsub (qpow t i) (qpow t' i))) (mul (Pcoef ρ i) (Qabs (Qsub t t')))
  | 0 => by
      show Qle (Qabs (Qsub (qpow t 0) (qpow t' 0))) (mul (⟨0, 1⟩ : Q) (Qabs (Qsub t t')))
      have h0 : (Qsub (qpow t 0) (qpow t' 0)).num = 0 := rfl
      unfold Qle Qabs mul
      rw [h0]; simp
  | (i + 1) => by
      have ihh := qpow_diff_bound_rat htd ht'd hρd htρ ht'ρ i
      have hqpid : 0 < (qpow t i).den := qpow_den_pos htd i
      have hqp'id : 0 < (qpow t' i).den := qpow_den_pos ht'd i
      have hid : Qeq (Qsub (qpow t (i + 1)) (qpow t' (i + 1)))
          (add (mul t (Qsub (qpow t i) (qpow t' i))) (mul (Qsub t t') (qpow t' i))) := by
        show Qeq (Qsub (mul t (qpow t i)) (mul t' (qpow t' i)))
          (add (mul t (Qsub (qpow t i) (qpow t' i))) (mul (Qsub t t') (qpow t' i)))
        simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
      have htri : Qle (Qabs (Qsub (qpow t (i + 1)) (qpow t' (i + 1))))
          (add (Qabs (mul t (Qsub (qpow t i) (qpow t' i)))) (Qabs (mul (Qsub t t') (qpow t' i)))) :=
        Qle_congr_left (Qabs_den_pos (add_den_pos (Qmul_den_pos htd (Qsub_den_pos hqpid hqp'id))
          (Qmul_den_pos (Qsub_den_pos htd ht'd) hqp'id))) (Qeq_symm (Qabs_Qeq hid)) (Qabs_add_le _ _)
      have hP1 : Qle (Qabs (mul t (Qsub (qpow t i) (qpow t' i))))
          (mul ρ (mul (Pcoef ρ i) (Qabs (Qsub t t')))) := by
        rw [Qabs_mul]
        exact Qmul_le_mul (Qabs_den_pos htd) hρd (Qabs_den_pos (Qsub_den_pos hqpid hqp'id))
          (Qabs_num_nonneg t) (Qabs_num_nonneg _) htρ ihh
      have hP2 : Qle (Qabs (mul (Qsub t t') (qpow t' i)))
          (mul (Qabs (Qsub t t')) (qpow ρ i)) := by
        rw [Qabs_mul]
        exact Qmul_le_mul_left (Qabs_num_nonneg _) (qpow_abs_le_rat ht'd hρd ht'ρ i)
      have hsum := Qadd_le_add hP1 hP2
      have hfactor : Qeq (add (mul ρ (mul (Pcoef ρ i) (Qabs (Qsub t t'))))
            (mul (Qabs (Qsub t t')) (qpow ρ i)))
          (mul (Pcoef ρ (i + 1)) (Qabs (Qsub t t'))) :=
        pcoef_factor ρ (Pcoef ρ i) (Qabs (Qsub t t')) (qpow ρ i)
      refine Qle_trans ?_ htri (Qle_trans ?_ hsum (Qeq_le hfactor))
      · exact add_den_pos (Qabs_den_pos (Qmul_den_pos htd (Qsub_den_pos hqpid hqp'id)))
          (Qabs_den_pos (Qmul_den_pos (Qsub_den_pos htd ht'd) hqp'id))
      · exact add_den_pos (Qmul_den_pos hρd (Qmul_den_pos (Pcoef_den_pos hρd i)
          (Qabs_den_pos (Qsub_den_pos htd ht'd))))
          (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos htd ht'd)) (qpow_den_pos hρd i))

-- ===========================================================================
-- The artanh Lipschitz bound (geometric, with the 1/(2n+1) weight cancelled).
-- ===========================================================================

/-- `Σ_{n=0}^N ρ^{2n}` (even powers). -/
def geoEvenSum (ρ : Q) : Nat → Q
  | 0 => qpow ρ 0
  | (n + 1) => add (geoEvenSum ρ n) (qpow ρ (2 * (n + 1)))

theorem geoEvenSum_den_pos {ρ : Q} (hρd : 0 < ρ.den) : ∀ N, 0 < (geoEvenSum ρ N).den
  | 0 => qpow_den_pos hρd 0
  | (n + 1) => add_den_pos (geoEvenSum_den_pos hρd n) (qpow_den_pos hρd _)

/-- Even telescoping invariant: `E_N·(1−ρ²) + ρ^{2N+2} = 1`. -/
theorem geoEven_eq {ρ : Q} (hρd : 0 < ρ.den) : ∀ N,
    Qeq (add (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ (2 * N + 2))) ⟨1, 1⟩
  | 0 => by
      show Qeq (add (mul (qpow ρ 0) (Qsub ⟨1, 1⟩ (mul ρ ρ))) (qpow ρ 2)) ⟨1, 1⟩
      simp only [qpow, Qeq, add, mul, Qsub, neg]; push_cast; ring_uor
  | (N + 1) => by
      refine Qeq_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
          (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd (2 * N + 2)))
        ?_ (geoEven_eq hρd N)
      have hgs : geoEvenSum ρ (N + 1) = add (geoEvenSum ρ N) (qpow ρ (2 * N + 2)) := by
        show add (geoEvenSum ρ N) (qpow ρ (2 * (N + 1))) = add (geoEvenSum ρ N) (qpow ρ (2 * N + 2))
        rw [show 2 * (N + 1) = 2 * N + 2 from by omega]
      have hpw : qpow ρ (2 * (N + 1) + 2) = mul ρ (mul ρ (qpow ρ (2 * N + 2))) := by
        rw [show 2 * (N + 1) + 2 = (2 * N + 2) + 1 + 1 from by omega, qpow_succ, qpow_succ]
      rw [hgs, hpw]
      exact geo_step_eq (geoEvenSum ρ N) (qpow ρ (2 * N + 2)) ρ

/-- `E_N·(1−ρ²) ≤ 1`. -/
theorem geoEven_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (N : Nat) :
    Qle (mul (geoEvenSum ρ N) (Qsub ⟨1, 1⟩ (mul ρ ρ))) ⟨1, 1⟩ :=
  Qle_trans (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
      (Qsub_den_pos Nat.one_pos (Nat.mul_pos hρd hρd))) (qpow_den_pos hρd _))
    (Qle_self_add (qpow_nonneg hρ0 _)) (Qeq_le (geoEven_eq hρd N))

-- `(k·P)·... ` cancellation:  `((k·P)·D)·(1/k) ≈ P·D`.
private theorem cancel_k (k : Nat) (P D : Q) :
    Qeq (mul (mul (mul ⟨(k : Int), 1⟩ P) D) ⟨1, k⟩) (mul P D) := by
  simp only [Qeq, mul]; push_cast; ring_uor

-- `ρ·(k·Pi) + ρ·Pi ≈ (k+1)·(ρ·Pi)` (abstract).
private theorem pcoef_step_eq (R Pi : Q) (k : Nat) :
    Qeq (add (mul R (mul ⟨(k : Int), 1⟩ Pi)) (mul R Pi))
      (mul ⟨((k + 1 : Nat) : Int), 1⟩ (mul R Pi)) := by
  simp only [Qeq, add, mul]; push_cast; ring_uor

/-- Closed form `Pcoef ρ (i+1) = (i+1)·ρⁱ`. -/
theorem Pcoef_closed {ρ : Q} (hρd : 0 < ρ.den) : ∀ i,
    Qeq (Pcoef ρ (i + 1)) (mul ⟨((i + 1 : Nat) : Int), 1⟩ (qpow ρ i))
  | 0 => by
      show Qeq (add (mul ρ ⟨0, 1⟩) (qpow ρ 0)) (mul ⟨1, 1⟩ (qpow ρ 0))
      simp only [qpow, Qeq, add, mul]; push_cast; ring_uor
  | (i + 1) => by
      show Qeq (add (mul ρ (Pcoef ρ (i + 1))) (qpow ρ (i + 1)))
        (mul ⟨((i + 1 + 1 : Nat) : Int), 1⟩ (qpow ρ (i + 1)))
      have ih := Pcoef_closed hρd i
      rw [qpow_succ ρ i]
      refine Qeq_trans
        (add_den_pos (Qmul_den_pos hρd (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd i)))
          (Qmul_den_pos hρd (qpow_den_pos hρd i)))
        (Qadd_congr (Qmul_congr (Qeq_refl ρ) ih) (Qeq_refl (mul ρ (qpow ρ i))))
        (pcoef_step_eq ρ (qpow ρ i) (i + 1))

/-- **Per-term artanh Lipschitz**: `|t^{2n+1}/(2n+1) − t'^{2n+1}/(2n+1)| ≤ ρ^{2n}·|t − t'|`
    (the `(2n+1)` coefficient cancels the `1/(2n+1)` weight). -/
theorem artTerm_diff_bound {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) (n : Nat) :
    Qle (Qabs (Qsub (artTerm t n) (artTerm t' n))) (mul (qpow ρ (2 * n)) (Qabs (Qsub t t'))) := by
  have hfac : Qeq (Qsub (artTerm t n) (artTerm t' n))
      (mul (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))) ⟨1, 2 * n + 1⟩) := by
    show Qeq (Qsub (mul (qpow t (2 * n + 1)) ⟨1, 2 * n + 1⟩)
        (mul (qpow t' (2 * n + 1)) ⟨1, 2 * n + 1⟩))
      (mul (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))) ⟨1, 2 * n + 1⟩)
    simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
  have heq1 : Qeq (Qabs (Qsub (artTerm t n) (artTerm t' n)))
      (mul (Qabs (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1)))) ⟨1, 2 * n + 1⟩) := by
    have h := Qabs_Qeq hfac
    rw [Qabs_mul, show Qabs (⟨1, 2 * n + 1⟩ : Q) = ⟨1, 2 * n + 1⟩ from rfl] at h; exact h
  have hb1 := Qmul_le_mul_right (a := Qabs (Qsub (qpow t (2 * n + 1)) (qpow t' (2 * n + 1))))
    (b := mul (Pcoef ρ (2 * n + 1)) (Qabs (Qsub t t'))) (c := ⟨1, 2 * n + 1⟩)
    (by show (0 : Int) ≤ 1; decide) (qpow_diff_bound_rat htd ht'd hρd htρ ht'ρ (2 * n + 1))
  have hmid : Qeq (mul (mul (Pcoef ρ (2 * n + 1)) (Qabs (Qsub t t'))) ⟨1, 2 * n + 1⟩)
      (mul (mul (mul ⟨((2 * n + 1 : Nat) : Int), 1⟩ (qpow ρ (2 * n))) (Qabs (Qsub t t')))
        ⟨1, 2 * n + 1⟩) :=
    Qmul_congr (Qmul_congr (Pcoef_closed hρd (2 * n)) (Qeq_refl _)) (Qeq_refl _)
  exact Qle_trans
    (Qmul_den_pos (Qabs_den_pos (Qsub_den_pos (qpow_den_pos htd _) (qpow_den_pos ht'd _)))
      (Nat.succ_pos _))
    (Qeq_le heq1)
    (Qle_trans (Qmul_den_pos (Qmul_den_pos (Pcoef_den_pos hρd _)
        (Qabs_den_pos (Qsub_den_pos htd ht'd))) (Nat.succ_pos _)) hb1
      (Qle_trans (Qmul_den_pos (Qmul_den_pos (Qmul_den_pos Nat.one_pos (qpow_den_pos hρd _))
          (Qabs_den_pos (Qsub_den_pos htd ht'd))) (Nat.succ_pos _))
        (Qeq_le hmid) (Qeq_le (cancel_k (2 * n + 1) (qpow ρ (2 * n)) (Qabs (Qsub t t'))))))

/-- **The artanh Lipschitz sum bound**: `|artSum_t(N) − artSum_{t'}(N)| ≤ E_N·|t − t'|`. -/
theorem artSum_Lip_le {t t' ρ : Q} (htd : 0 < t.den) (ht'd : 0 < t'.den) (hρd : 0 < ρ.den)
    (htρ : Qle (Qabs t) ρ) (ht'ρ : Qle (Qabs t') ρ) :
    ∀ N, Qle (Qabs (Qsub (artSum t N) (artSum t' N))) (mul (geoEvenSum ρ N) (Qabs (Qsub t t')))
  | 0 => artTerm_diff_bound htd ht'd hρd htρ ht'ρ 0
  | (N + 1) => by
      have ih := artSum_Lip_le htd ht'd hρd htρ ht'ρ N
      have hAd : 0 < (artSum t N).den := artSum_den_pos htd N
      have hCd : 0 < (artSum t' N).den := artSum_den_pos ht'd N
      have hBd : 0 < (artTerm t (N + 1)).den := artTerm_den_pos htd (N + 1)
      have hDd : 0 < (artTerm t' (N + 1)).den := artTerm_den_pos ht'd (N + 1)
      refine Qle_trans
        (add_den_pos (Qabs_den_pos (Qsub_den_pos hAd hCd)) (Qabs_den_pos (Qsub_den_pos hBd hDd)))
        (Qabs_sub_add4 hAd hBd hCd hDd)
        (Qle_trans
          (add_den_pos (Qmul_den_pos (geoEvenSum_den_pos hρd N)
            (Qabs_den_pos (Qsub_den_pos htd ht'd)))
            (Qmul_den_pos (qpow_den_pos hρd _) (Qabs_den_pos (Qsub_den_pos htd ht'd))))
          (Qadd_le_add ih (artTerm_diff_bound htd ht'd hρd htρ ht'ρ (N + 1)))
          (Qeq_le (Qeq_symm (Qmul_add_right (geoEvenSum ρ N) (qpow ρ (2 * (N + 1)))
            (Qabs (Qsub t t'))))))

-- ===========================================================================
-- The geometric reindex for ρ ≤ 1/2:  ρᵐ ≤ 1/(m+1).
-- ===========================================================================

/-- `(1/2)ᵐ = 1/2ᵐ`. -/
theorem qpow_half_value : ∀ m, qpow (⟨1, 2⟩ : Q) m = ⟨1, npow 2 m⟩
  | 0 => rfl
  | (m + 1) => by
      show mul (⟨1, 2⟩ : Q) (qpow (⟨1, 2⟩ : Q) m) = ⟨1, npow 2 (m + 1)⟩
      rw [qpow_half_value m]; rfl

/-- For `0 ≤ ρ ≤ 1/2`: `ρᵐ ≤ 1/(m+1)`. -/
theorem qpow_half_le {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den) (hρ12 : Qle ρ ⟨1, 2⟩) (m : Nat) :
    Qle (qpow ρ m) ⟨1, m + 1⟩ := by
  have h1 : Qle (qpow ρ m) (qpow (⟨1, 2⟩ : Q) m) :=
    qpow_base_mono hρd (by decide) hρ0 hρ12 m
  rw [qpow_half_value m] at h1
  refine Qle_trans (npow_pos (by decide) m) h1 ?_
  show (1 : Int) * ((m + 1 : Nat) : Int) ≤ 1 * ((npow 2 m : Nat) : Int)
  rw [Int.one_mul, Int.one_mul]; exact_mod_cast two_pow_ge m

/-- **The general Bernoulli bound**: for `0 ≤ ρ < 1` (i.e. `p = ρ.num.toNat ≤ q = ρ.den`),
    `ρᵐ ≤ q/(q + m(q−p))` — a `1/(linear)` decay, the engine of the geometric reindex. -/
theorem qpow_geom_bound {ρ : Q} (hρ0 : 0 ≤ ρ.num) (hρd : 0 < ρ.den)
    (hple : ρ.num.toNat ≤ ρ.den) :
    ∀ m, Qle (qpow ρ m) ⟨(ρ.den : Int), ρ.den + m * (ρ.den - ρ.num.toNat)⟩
  | 0 => by
      show (1 : Int) * ((ρ.den + 0 * (ρ.den - ρ.num.toNat) : Nat) : Int) ≤ (ρ.den : Int) * 1
      omega
  | (m + 1) => by
      have ih := qpow_geom_bound hρ0 hρd hple m
      have hsc : ρ.num.toNat + (ρ.den - ρ.num.toNat) = ρ.den := Nat.add_sub_cancel' hple
      have h2 : (ρ.num.toNat : Int) + ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) := by
        exact_mod_cast hsc
      have hcs : ((ρ.den - ρ.num.toNat : Nat) : Int) = (ρ.den : Int) - (ρ.num.toNat : Int) := by
        rw [← h2]; ring_uor
      have hp : ((ρ.num.toNat : Nat) : Int) = ρ.num := Int.toNat_of_nonneg hρ0
      have hqp : (0 : Int) ≤ (ρ.den : Int) - ρ.num := by
        have h1 : (ρ.num.toNat : Int) ≤ (ρ.den : Int) := by exact_mod_cast hple
        omega
      have hstep : Qle (mul ρ ⟨(ρ.den : Int), ρ.den + m * (ρ.den - ρ.num.toNat)⟩)
          ⟨(ρ.den : Int), ρ.den + (m + 1) * (ρ.den - ρ.num.toNat)⟩ := by
        show (ρ.num * (ρ.den : Int)) * ((ρ.den + (m + 1) * (ρ.den - ρ.num.toNat) : Nat) : Int)
            ≤ (ρ.den : Int) * ((ρ.den * (ρ.den + m * (ρ.den - ρ.num.toNat)) : Nat) : Int)
        have hdiff : (ρ.den : Int)
              * ((ρ.den * (ρ.den + m * (ρ.den - ρ.num.toNat)) : Nat) : Int)
            - (ρ.num * (ρ.den : Int))
              * ((ρ.den + (m + 1) * (ρ.den - ρ.num.toNat) : Nat) : Int)
            = (ρ.den : Int) * (((ρ.den : Int) - ρ.num)
              * ((ρ.den : Int) - ρ.num) * ((m : Int) + 1)) := by
          push_cast [hcs, hp]; ring_uor
        have hnn : (0 : Int) ≤ (ρ.den : Int) * (((ρ.den : Int) - ρ.num)
            * ((ρ.den : Int) - ρ.num) * ((m : Int) + 1)) :=
          Int.mul_nonneg (Int.ofNat_nonneg _)
            (Int.mul_nonneg (Int.mul_nonneg hqp hqp) (by omega))
        omega
      exact Qle_trans (Qmul_den_pos hρd (Nat.lt_of_lt_of_le hρd (Nat.le_add_right _ _)))
        (Qmul_le_mul_left hρ0 ih) hstep

end UOR.Bridge.F1Square.Analysis
