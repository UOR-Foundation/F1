/-
F1 square — **the improper integral of a compactly supported integrand is a finite integral**
(`ImproperFinite.lean`): if the unit-interval terms `∫_{[m+1,m+2]} f` vanish for `m ≥ M` (`M ≥ 1`),
then `improperIntegral1 f = ∫_{[1, M+1]} f` — the partial sums stabilize (`genSum_stable`), the
Bishop limit of an eventually constant sequence is that constant (`Rlim_eq_of_close`), and the
finite window splits along the integer partition (`partition_split`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.IntegralInversion
import F1Square.Analysis.ComplexDigammaConj
import F1Square.Analysis.ComplexLimitCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Partial sums of an eventually-zero sequence stabilize.
-- ===========================================================================

/-- `Σ_{m<n} T = Σ_{m<M} T` for `n ≥ M` when `T m = 0` for `m ≥ M`. -/
theorem genSum_stable (T : Nat → Real) (M : Nat) (hvan : ∀ m, M ≤ m → Req (T m) zero) :
    ∀ d, Req (genSum T (M + d)) (genSum T M)
  | 0 => Req_refl _
  | (d + 1) => by
      show Req (Radd (genSum T (M + d)) (T (M + d))) (genSum T M)
      refine Req_trans (Radd_congr (genSum_stable T M hvan d) (hvan (M + d) (Nat.le_add_right M d))) ?_
      exact Radd_zero _

-- ===========================================================================
-- (2) A unit-interval term vanishes when the integrand vanishes on its window.
-- ===========================================================================

/-- `∫_{[a,a+w]} f = 0` when `f` vanishes on the window (via the zero constant at modulus `0`). -/
theorem riemannIntegralI_window_zero {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hz : ∀ x, Rle zero x → Rle x one → Req (f (affineMap a w ha hw x)) zero) :
    Req (riemannIntegralI hLd hLn hlip hfc a w ha hw hwn) zero := by
  refine Req_trans (riemannIntegralI_congr_unit_mod hLd hLn hlip hfc (by decide) (by decide)
    (const_lip0 zero) (fun _ _ _ => Req_refl zero) a w ha hw hwn hz) ?_
  exact Req_trans (riemannIntegralI_const zero a w ha hw hwn) (Rmul_zero _)

/-- The unit-interval term `∫_{[m+1, m+2]} f` vanishes when `f` vanishes on `[m+1, ∞)`. -/
theorem integralTerm_vanish {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (m : Nat)
    (hz : ∀ x, Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x → Req (f x) zero) :
    Req (integralTerm hLd hLn hlip hfc m) zero :=
  riemannIntegralI_window_zero hLd hLn hlip hfc _ _ Nat.one_pos (by decide) (by decide)
    (fun t h0 _ => hz _ (Rle_self_Radd_right
      (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_of_Rle_zero h0))))

-- ===========================================================================
-- (3) The finite window `[1, M+2]` is the sum of the first `M+1` unit terms.
-- ===========================================================================

/-- The integer partition `p i = i + 1`. -/
def intPt (i : Nat) : Q := ⟨(i : Int) + 1, 1⟩

theorem intPt_den (i : Nat) : 0 < (intPt i).den := Nat.one_pos

theorem intPt_zero_lt (i : Nat) : Qlt (intPt 0) (intPt (i + 1)) := by
  show (((0 : Nat) : Int) + 1) * ((1 : Nat) : Int) < (((i + 1 : Nat) : Int) + 1) * ((1 : Nat) : Int)
  push_cast; omega

theorem intPt_step_le (i : Nat) : Qle (intPt i) (intPt (i + 1)) := by
  show ((i : Int) + 1) * ((1 : Nat) : Int) ≤ (((i + 1 : Nat) : Int) + 1) * ((1 : Nat) : Int)
  push_cast; omega

theorem intPt_step_sub (i : Nat) : Qeq (Qsub (intPt (i + 1)) (intPt i)) (⟨1, 1⟩ : Q) := by
  simp only [Qeq, Qsub, add, neg, intPt]; push_cast; ring_uor

theorem intPt_top_sub (M : Nat) :
    Qeq (Qsub (intPt (M + 1)) (intPt 0)) (⟨((M + 1 : Nat) : Int), 1⟩ : Q) := by
  simp only [Qeq, Qsub, add, neg, intPt]; push_cast; ring_uor

theorem intPt_zero_eq : Qeq (⟨1, 1⟩ : Q) (intPt 0) := by
  show Qeq (⟨1, 1⟩ : Q) ⟨((0 : Nat) : Int) + 1, 1⟩; decide

/-- Cell `i` of the integer partition is the unit term `∫_{[i+1, i+2]} f`. -/
theorem intPt_cell_eq {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (i : Nat) :
    Req (riemannIntegralI hLd hLn hlip hfc (intPt i) (Qsub (intPt (i + 1)) (intPt i)) (intPt_den i)
          (Qsub_den_pos (intPt_den _) (intPt_den i)) (Qsub_num_nonneg (intPt_step_le i)))
        (integralTerm hLd hLn hlip hfc i) :=
  riemannIntegralI_congr_Q hLd hLn hlip hfc (intPt i) (Qsub (intPt (i + 1)) (intPt i))
    (⟨(i : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (intPt_den i) (Qsub_den_pos (intPt_den _) (intPt_den i))
    (Qsub_num_nonneg (intPt_step_le i)) Nat.one_pos (by decide) (by decide)
    (Qeq_refl _) (intPt_step_sub i)

/-- The window `[1, M+2]` is `[intPt 0, intPt (M+1)]`. -/
theorem intPt_window_eq {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (M : Nat) :
    Req (riemannIntegralI hLd hLn hlip hfc (⟨1, 1⟩ : Q) (⟨((M + 1 : Nat) : Int), 1⟩ : Q)
          Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _))
        (riemannIntegralI hLd hLn hlip hfc (intPt 0) (Qsub (intPt (M + 1)) (intPt 0)) (intPt_den 0)
          (Qsub_den_pos (intPt_den _) (intPt_den 0)) (Qsub_num_nonneg (Qle_of_Qlt_loc (intPt_zero_lt M)))) :=
  riemannIntegralI_congr_Q hLd hLn hlip hfc (⟨1, 1⟩ : Q) (⟨((M + 1 : Nat) : Int), 1⟩ : Q)
    (intPt 0) (Qsub (intPt (M + 1)) (intPt 0)) Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _)
    (intPt_den 0) (Qsub_den_pos (intPt_den _) (intPt_den 0))
    (Qsub_num_nonneg (Qle_of_Qlt_loc (intPt_zero_lt M)))
    intPt_zero_eq (Qeq_symm (intPt_top_sub M))

/-- `∫_{[1, M+2]} f = Σ_{m ≤ M} ∫_{[m+1, m+2]} f`. -/
theorem window_eq_genSum_terms {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (M : Nat) :
    Req (riemannIntegralI hLd hLn hlip hfc (⟨1, 1⟩ : Q) (⟨((M + 1 : Nat) : Int), 1⟩ : Q)
          Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _))
        (genSum (integralTerm hLd hLn hlip hfc) (M + 1)) := by
  have hsplit := partition_split hLd hLn hlip hfc intPt intPt_den intPt_zero_lt intPt_step_le M
  refine Req_trans (intPt_window_eq hLd hLn hlip hfc M) (Req_trans hsplit ?_)
  exact genSum_congr _ _ (fun i => intPt_cell_eq hLd hLn hlip hfc i) (M + 1)

-- ===========================================================================
-- (4) THE IMPROPER INTEGRAL OF A COMPACTLY SUPPORTED INTEGRAND IS FINITE.
-- ===========================================================================

theorem RReg_const_fin (c : Real) : RReg (fun _ => c) := by
  intro j k n
  show Qle (Qabs (Qsub (c.seq n) (c.seq n))) (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩)
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (c.seq n) (c.seq n)).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩).num := by
    simp only [add]
    exact Int.add_nonneg (Int.mul_nonneg (by omega) (by omega))
      (Int.mul_nonneg (by omega) (by omega))
  exact Int.mul_nonneg hnum hden

/-- **THE FINITE-SUPPORT FOLD** `improperIntegral1 f = ∫_{[1, M+2]} f` when the unit terms vanish
    for `m ≥ M+1` (the partial sums stabilize; the Bishop limit of an eventually constant sequence is
    that constant). -/
theorem improperIntegral1_eq_finite {f : Real → Real} {L K : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (hKd : 0 < K.den) (hK0 : 0 ≤ K.num)
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hLd hLn hlip hfc m)
      ∧ Rle (integralTerm hLd hLn hlip hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
    (M : Nat) (hvan : ∀ m, M + 1 ≤ m → Req (integralTerm hLd hLn hlip hfc m) zero) :
    Req (improperIntegral1 hLd hLn hlip hfc hKd hK0 hb)
        (riemannIntegralI hLd hLn hlip hfc (⟨1, 1⟩ : Q) (⟨((M + 1 : Nat) : Int), 1⟩ : Q)
          Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _)) := by
  refine Req_trans ?_ (Req_symm (window_eq_genSum_terms hLd hLn hlip hfc M))
  -- the partial sums are eventually the finite sum
  have hstab : ∀ n, M ≤ n →
      Req (genSum (integralTerm hLd hLn hlip hfc) (digammaMidx K n))
          (genSum (integralTerm hLd hLn hlip hfc) (M + 1)) := by
    intro n hn
    have hge : M + 1 ≤ digammaMidx K n := Nat.le_trans (Nat.succ_le_succ hn) (digammaMidx_ge K n)
    have hd : digammaMidx K n = (M + 1) + (digammaMidx K n - (M + 1)) :=
      (Nat.add_sub_cancel' hge).symm
    rw [hd]
    exact genSum_stable _ (M + 1) hvan _
  show Req (Rlim (fun j => genSum (integralTerm hLd hLn hlip hfc) (digammaMidx K j)) _) _
  refine Req_trans (Rlim_eq_of_close _ (RReg_const_fin (genSum (integralTerm hLd hLn hlip hfc) (M + 1)))
    (fun k => ⟨M, fun n hn => Rle_trans (Rle_of_Req (hstab n hn))
      (Rle_self_Radd_right (Rnonneg_ofQ (Nat.succ_pos k) (show (0 : Int) ≤ 1 by decide)))⟩)
    (fun k => ⟨M, fun n hn => Rle_trans (Rle_of_Req (Req_symm (hstab n hn)))
      (Rle_self_Radd_right (Rnonneg_ofQ (Nat.succ_pos k) (show (0 : Int) ≤ 1 by decide)))⟩)) ?_
  exact Rlim_const_core _ _

end UOR.Bridge.F1Square.Square
