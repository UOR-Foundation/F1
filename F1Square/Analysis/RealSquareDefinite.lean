/-
F1 square — **real square-definiteness (the Bishop metric kernels), zeta-free**. The elementary
facts that make a sum of real squares a genuine positive-definite form: a square is nonnegative,
two nonnegatives summing to zero are each zero, and `x·x ≈ 0 ⟹ x ≈ 0` (Bishop square-definiteness,
via an Archimedean/√-monotone argument, sqrt-free). Extracted here so consumers — the real metric
`posForm` (`HilbertPolyaMetric`) and the complex inner-product space (`FinInnerProduct`) — reuse the
positive-definiteness kernel from a foundational module whose import cone is `ROrder`/`Real`/`QOrder`
alone: provably free of `RSum`/`Pi` and therefore of ζ, the zeros, and the Li stack.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ROrder
import F1Square.Analysis.Real
import F1Square.Analysis.QOrder

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Local ℚ / ℝ substrate.
-- These are verbatim replicas of lemmas that live in zeta-tainted modules
-- (`Analysis.SqrtRealSq`, `Analysis.CosSinBound`); kept local so the import cone
-- stays minimal and free of the named RH-observable modules.
-- ===========================================================================

/-- `√` is monotone on `Q₊` (replica of `Analysis.SqrtRealSq.Qle_of_sq_le`): `0 ≤ x`, `0 ≤ y`,
    `x² ≤ y²` ⟹ `x ≤ y`. Constructive: factor `y² − x² = (y−x)(y+x)` and split on the sign of `y+x`. -/
private theorem Qle_of_sq_le_loc {x y : Q} (hx : 0 ≤ x.num) (hy : 0 ≤ y.num)
    (h : Qle (mul x x) (mul y y)) : Qle x y := by
  simp only [Qle, mul] at h ⊢
  push_cast at h
  have hxd : (0 : Int) ≤ (x.den : Int) := Int.ofNat_nonneg _
  have hyd : (0 : Int) ≤ (y.den : Int) := Int.ofNat_nonneg _
  have hna : 0 ≤ x.num * (y.den : Int) := Int.mul_nonneg hx hyd
  have hnb : 0 ≤ y.num * (x.den : Int) := Int.mul_nonneg hy hxd
  have hsq : (x.num * (y.den : Int)) * (x.num * (y.den : Int))
      ≤ (y.num * (x.den : Int)) * (y.num * (x.den : Int)) := by
    have e1 : (x.num * (y.den : Int)) * (x.num * (y.den : Int))
        = x.num * x.num * ((y.den : Int) * (y.den : Int)) := by ring_uor
    have e2 : (y.num * (x.den : Int)) * (y.num * (x.den : Int))
        = y.num * y.num * ((x.den : Int) * (x.den : Int)) := by ring_uor
    rw [e1, e2]; exact h
  have hprod : (0 : Int) ≤ ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
      * ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) := by
    have e : ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
          * ((y.num * (x.den : Int)) + (x.num * (y.den : Int)))
        = (y.num * (x.den : Int)) * (y.num * (x.den : Int))
          - (x.num * (y.den : Int)) * (x.num * (y.den : Int)) := by ring_uor
    rw [e]; omega
  rcases Int.lt_trichotomy 0 ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) with hlt | heq | hgt
  · have hh : (0 : Int) * ((y.num * (x.den : Int)) + (x.num * (y.den : Int)))
        ≤ ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
          * ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) := by simpa using hprod
    have hcancel := Int.le_of_mul_le_mul_right hh hlt
    omega
  · omega
  · omega

/-- A Bishop square is non-negative (replica of `Analysis.CosSinBound.Rnonneg_Rmul_self`): `0 ≤ y·y`. -/
theorem Rnonneg_Rmul_self_loc (y : Real) : Rnonneg (Rmul y y) := by
  intro n
  show Qle (neg (Qbound n)) (mul (y.seq (Ridx y y n)) (y.seq (Ridx y y n)))
  have hsq : 0 ≤ (y.seq (Ridx y y n)).num * (y.seq (Ridx y y n)).num := by
    rcases Int.le_total 0 (y.seq (Ridx y y n)).num with h | h
    · exact Int.mul_nonneg h h
    · have h' : (0 : Int) ≤ -(y.seq (Ridx y y n)).num := by omega
      have hp := Int.mul_nonneg h' h'
      have he : -(y.seq (Ridx y y n)).num * -(y.seq (Ridx y y n)).num
          = (y.seq (Ridx y y n)).num * (y.seq (Ridx y y n)).num := by ring_uor
      omega
  refine Qle_trans (b := (⟨0, 1⟩ : Q)) (by decide) ?_ ?_
  · simp only [Qle, Qbound, neg]; omega
  · simp only [Qle, mul]; omega

/-- `a ≤ a + b` when `b ≥ 0` (replica of `Analysis.CosSinBound.Rle_self_Radd_right`). -/
private theorem Rle_self_Radd_right_loc {a b : Real} (hb : Rnonneg b) : Rle a (Radd a b) := by
  intro n
  show Qle (a.seq n) (add (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1))) ⟨2, n + 1⟩)
  have s1 : Qle (a.seq n) (add (a.seq (2 * n + 1)) (add (Qbound n) (Qbound (2 * n + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos (2 * n + 1))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos (2 * n + 1))) (a.reg n (2 * n + 1))
  refine Qle_trans (add_den_pos (a.den_pos (2 * n + 1))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos (2 * n + 1)))) s1 ?_
  refine Qle_trans (b := add (a.seq (2 * n + 1)) (add (b.seq (2 * n + 1)) ⟨2, n + 1⟩))
    (add_den_pos (a.den_pos (2 * n + 1)) (add_den_pos (b.den_pos (2 * n + 1)) (Nat.succ_pos _)))
    ?_ (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  refine Qadd_le_add (Qle_refl _) ?_
  exact Qle_trans (b := add (neg (Qbound (2 * n + 1))) ⟨2, n + 1⟩)
    (add_den_pos (neg_den_pos (Qbound_den_pos _)) (Nat.succ_pos _))
    (Qeq_le (by simp only [Qeq, add, Qbound, neg]; push_cast; ring_uor))
    (Qadd_le_add (hb (2 * n + 1)) (Qle_refl _))

/-- `b ≤ a + b` when `a ≥ 0` (replica of `Analysis.CosSinBound.Rle_self_Radd_left`). -/
private theorem Rle_self_Radd_left_loc {a b : Real} (ha : Rnonneg a) : Rle b (Radd a b) :=
  Rle_trans (Rle_self_Radd_right_loc ha) (Rle_of_Req (Radd_comm b a))

-- ===========================================================================
-- Positive-definiteness kernels.
-- ===========================================================================

/-- Two non-negative reals summing to `0` are each `0` — antisymmetry of `≤`: `a ≤ a+b ≈ 0` and
    `a ≥ 0`, likewise for `b`. -/
theorem Radd_eq_zero_split {a b : Real} (ha : Rnonneg a) (hb : Rnonneg b)
    (h : Req (Radd a b) zero) : Req a zero ∧ Req b zero :=
  ⟨Rle_antisymm (Rle_trans (Rle_self_Radd_right_loc hb) (Rle_of_Req h)) (Rle_zero_of_Rnonneg ha),
   Rle_antisymm (Rle_trans (Rle_self_Radd_left_loc ha) (Rle_of_Req h)) (Rle_zero_of_Rnonneg hb)⟩

/-- **Bishop square-definiteness**: `x·x ≈ 0 ⟹ x ≈ 0`. Fix a target index `m`; the generalized
    Archimedean lemma reduces `|xₘ| ≤ 2/(m+1)` to a family (over `k`) of slacker bounds. For the
    auxiliary Bishop index `n = (k+1)²`, `√`-monotonicity turns `x_{r(n)}² ≤ 2/(n+1)` (from the
    hypothesis, `r = Ridx x x n`) into `|x_{r(n)}| ≤ 2/(k+1)`; the triangle inequality plus regularity
    then bound `|xₘ|` by `2/(m+1) + 3/(k+1)`, and the Archimedean tail vanishes. -/
theorem Rmul_self_eq_zero_imp {x : Real} (hsq : Req (Rmul x x) zero) : Req x zero := by
  intro m
  refine Qarch_gen (C := 3)
    (Qabs_den_pos (Qsub_den_pos (x.den_pos m) (by rw [zero_seq]; decide)))
    (Nat.succ_pos m) ?_
  intro k
  -- `k ≤ Ridx x x n` for the auxiliary Bishop index `n = (k+1)²` (the reindex only grows the index).
  have hkn : k ≤ (k + 1) * (k + 1) := by
    have he : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := Nat.succ_mul k (k + 1)
    omega
  have hkr : k ≤ Ridx x x ((k + 1) * (k + 1)) :=
    Nat.le_trans hkn (Ridx_ge x x ((k + 1) * (k + 1)))
  have hden_r : 0 < (x.seq (Ridx x x ((k + 1) * (k + 1)))).den := x.den_pos _
  -- Sub-claim 1: `|x_r · x_r| ≤ 2/(n+1)` (the hypothesis at `n`, `−0` removed).
  have hsq_n : Qle (Qabs (mul (x.seq (Ridx x x ((k + 1) * (k + 1))))
      (x.seq (Ridx x x ((k + 1) * (k + 1)))))) (⟨2, (k + 1) * (k + 1) + 1⟩ : Q) := by
    have hh : Qle (Qabs (Qsub (mul (x.seq (Ridx x x ((k + 1) * (k + 1))))
        (x.seq (Ridx x x ((k + 1) * (k + 1))))) (zero.seq ((k + 1) * (k + 1)))))
        (⟨2, (k + 1) * (k + 1) + 1⟩ : Q) := hsq ((k + 1) * (k + 1))
    refine Qle_congr_left
      (Qabs_den_pos (Qsub_den_pos (Qmul_den_pos hden_r hden_r) (by rw [zero_seq]; decide)))
      (Qabs_Qeq ?_) hh
    rw [zero_seq]; simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  -- Sub-claim 2: `|x_r| ≤ 2/(k+1)` (√-monotone against `2/(n+1) ≤ (2/(k+1))²`).
  have hsub2 : Qle (Qabs (x.seq (Ridx x x ((k + 1) * (k + 1))))) (⟨2, k + 1⟩ : Q) := by
    refine Qle_of_sq_le_loc (Qabs_num_nonneg _) (by show (0 : Int) ≤ 2; decide) ?_
    rw [← Qabs_mul]
    refine Qle_trans (b := (⟨2, (k + 1) * (k + 1) + 1⟩ : Q)) (Nat.succ_pos _) hsq_n ?_
    have harith : 2 * ((k + 1) * (k + 1)) ≤ 2 * 2 * ((k + 1) * (k + 1) + 1) := by
      generalize (k + 1) * (k + 1) = P; omega
    simp only [Qle, mul]
    exact_mod_cast harith
  -- Triangle + regularity assembly.
  have hA : Qle (Qabs (Qsub (x.seq m) (x.seq (Ridx x x ((k + 1) * (k + 1))))))
      (add (Qbound m) (Qbound (Ridx x x ((k + 1) * (k + 1))))) := x.reg m (Ridx x x ((k + 1) * (k + 1)))
  have hB : Qle (Qabs (Qsub (x.seq (Ridx x x ((k + 1) * (k + 1)))) (zero.seq m))) (⟨2, k + 1⟩ : Q) := by
    have h0 : Qeq (Qsub (x.seq (Ridx x x ((k + 1) * (k + 1)))) (zero.seq m))
        (x.seq (Ridx x x ((k + 1) * (k + 1)))) := by
      rw [zero_seq]; simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    exact Qle_congr_left (Qabs_den_pos (x.den_pos _)) (Qabs_Qeq (Qeq_symm h0)) hsub2
  have Tri : Qle (Qabs (Qsub (x.seq m) (zero.seq m)))
      (add (Qabs (Qsub (x.seq m) (x.seq (Ridx x x ((k + 1) * (k + 1))))))
        (Qabs (Qsub (x.seq (Ridx x x ((k + 1) * (k + 1)))) (zero.seq m)))) :=
    Qabs_sub_triangle (x.den_pos m) (x.den_pos (Ridx x x ((k + 1) * (k + 1)))) (by rw [zero_seq]; decide)
  have step1 : Qle (Qabs (Qsub (x.seq m) (zero.seq m)))
      (add (add (Qbound m) (Qbound (Ridx x x ((k + 1) * (k + 1))))) (⟨2, k + 1⟩ : Q)) :=
    Qle_trans (add_den_pos
        (Qabs_den_pos (Qsub_den_pos (x.den_pos m) (x.den_pos _)))
        (Qabs_den_pos (Qsub_den_pos (x.den_pos _) (by rw [zero_seq]; decide))))
      Tri (Qadd_le_add hA hB)
  -- Final ℚ collapse: `1/(m+1) + 1/(r+1) + 2/(k+1) ≤ 2/(m+1) + 3/(k+1)`.
  have hbm : Qle (Qbound m) (⟨2, m + 1⟩ : Q) := Qscale_le (by decide) (by decide) (Nat.le_refl m)
  have hbr : Qle (Qbound (Ridx x x ((k + 1) * (k + 1)))) (⟨1, k + 1⟩ : Q) :=
    Qscale_le (by decide) (by decide) hkr
  have h3 : Qeq (add (⟨1, k + 1⟩ : Q) (⟨2, k + 1⟩ : Q)) (⟨3, k + 1⟩ : Q) := by
    simp only [Qeq, add]; push_cast; ring_uor
  have hfin : Qle (add (add (Qbound m) (Qbound (Ridx x x ((k + 1) * (k + 1))))) (⟨2, k + 1⟩ : Q))
      (add (⟨2, m + 1⟩ : Q) (⟨3, k + 1⟩ : Q)) := by
    have h1 : Qle (add (add (Qbound m) (Qbound (Ridx x x ((k + 1) * (k + 1))))) (⟨2, k + 1⟩ : Q))
        (add (add (⟨2, m + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨2, k + 1⟩ : Q)) :=
      Qadd_le_add (Qadd_le_add hbm hbr) (Qle_refl _)
    have h2 : Qeq (add (add (⟨2, m + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨2, k + 1⟩ : Q))
        (add (⟨2, m + 1⟩ : Q) (add (⟨1, k + 1⟩ : Q) (⟨2, k + 1⟩ : Q))) := add_assoc _ _ _
    have h4 : Qle (add (⟨2, m + 1⟩ : Q) (add (⟨1, k + 1⟩ : Q) (⟨2, k + 1⟩ : Q)))
        (add (⟨2, m + 1⟩ : Q) (⟨3, k + 1⟩ : Q)) :=
      Qadd_le_add (Qle_refl _) (Qeq_le h3)
    exact Qle_trans (add_den_pos (add_den_pos (Nat.succ_pos m) (Nat.succ_pos k)) (Nat.succ_pos k))
      h1 (Qle_trans (add_den_pos (Nat.succ_pos m) (add_den_pos (Nat.succ_pos k) (Nat.succ_pos k)))
        (Qeq_le h2) h4)
  exact Qle_trans
    (add_den_pos (add_den_pos (Qbound_den_pos m) (Qbound_den_pos (Ridx x x ((k + 1) * (k + 1)))))
      (Nat.succ_pos k))
    step1 hfin

end UOR.Bridge.F1Square.Analysis
