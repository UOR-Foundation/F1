/-
F1 square — **Lipschitz cell estimates and the rational-partition split of the certified integral**
(`IntegralCell.lean`) — substrate for nonlinear changes of variable under the certified (dyadic)
integral, which knows only uniform dyadic refinement:

  • `cell_est_left`  — `|∫_{[a,a+w]} φ − w·φ(a)| ≤ w·(L·w)` for an `L2Test` φ (the difference test
    `φ − φ(a)` is bounded by `L·w` on the window; `riemannIntegralI_abs_le_window_real`);
  • `partition_split` — for ANY rational partition `p 0 < p (i+1)`, `p i ≤ p (i+1)`,
    `∫_{[p 0, p (m+1)]} f = Σ_{i≤m} ∫_{[p i, p (i+1)]} f` (iterated `riemannIntegralI_split_at`).

Together they bound `|∫ f − Σ_i f(p i)(p(i+1) − p i)| ≤ L·Σ_i (p(i+1) − p i)²` along an arbitrary
rational partition — Riemann sums along NON-uniform partitions converge to the certified integral.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilRecipCanon
import F1Square.Square.IntegralDist
import F1Square.Analysis.WindowBoundReal

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Real rearrangement helpers.
-- ===========================================================================

theorem Rsub_add_cancel_left (A B : Real) : Req (Rsub (Radd A B) A) B :=
  Req_trans (Rsub_congr (Radd_comm A B) (Req_refl _)) (Radd_sub_cancel_right B A)

/-- `affineMap a w t − a = w·t`. -/
theorem affineMap_sub_lo (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (t : Real) :
    Req (Rsub (affineMap a w ha hw t) (ofQ a ha)) (Rmul (ofQ w hw) t) :=
  Rsub_add_cancel_left _ _

/-- `0 ≤ t ≤ 1 ⟹ |t| ≤ 1`. -/
theorem unit_abs_le_one {t : Real} (h0 : Rle zero t) (h1 : Rle t one) : Rle (Rabs t) one :=
  Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_of_Rle_zero h0))) h1

-- ===========================================================================
-- (2) The LEFT-endpoint Lipschitz cell estimate.
-- ===========================================================================

/-- The difference test `φ − c` (a constant within `φ`'s bound subtracted), an `L2Test`. -/
def diffTest (φ : L2Test) (c : Real) (hc : Rle (Rabs c) (ofQ φ.M φ.hMd)) : L2Test :=
  L2Test.sub φ (constTest c φ.M φ.hMd φ.hMn hc)

theorem diffTest_f (φ : L2Test) (c : Real) (hc : Rle (Rabs c) (ofQ φ.M φ.hMd)) (x : Real) :
    (diffTest φ c hc).f x = Rsub (φ.f x) c := rfl

/-- `∫ (φ − c) = ∫ φ − w·c`. -/
theorem diffTest_integral (φ : L2Test) (c : Real) (hc : Rle (Rabs c) (ofQ φ.M φ.hMd))
    (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI (diffTest φ c hc).hLd (diffTest φ c hc).hLn (diffTest φ c hc).hlip
          (diffTest φ c hc).hfc a w ha hw hwn)
        (Rsub (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc a w ha hw hwn) (Rmul (ofQ w hw) c)) := by
  refine Req_trans (riemannIntegralI_addTest φ (L2Test.neg (constTest c φ.M φ.hMd φ.hMn hc))
    a w ha hw hwn) ?_
  refine Radd_congr (Req_refl _) ?_
  refine Req_trans (riemannIntegralI_negTest (constTest c φ.M φ.hMd φ.hMn hc) a w ha hw hwn) ?_
  exact Rneg_congr (riemannIntegralI_const c a w ha hw hwn)

/-- **THE LEFT-ENDPOINT CELL ESTIMATE** `|∫_{[a,a+w]} φ − w·φ(a)| ≤ w·(L·w)`. -/
theorem cell_est_left (φ : L2Test) (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Rle (Rabs (Rsub (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc a w ha hw hwn)
                    (Rmul (ofQ w hw) (φ.f (ofQ a ha)))))
        (Rmul (ofQ w hw) (Rmul (ofQ φ.L φ.hLd) (ofQ w hw))) := by
  have hc := φ.hbd (ofQ a ha)
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (diffTest_integral φ _ hc a w ha hw hwn)))) ?_
  refine riemannIntegralI_abs_le_window_real (diffTest φ _ hc).hLd (diffTest φ _ hc).hLn
    (diffTest φ _ hc).hlip (diffTest φ _ hc).hfc a w (Rmul (ofQ φ.L φ.hLd) (ofQ w hw))
    ha hw hwn ?_
  intro t h0 h1
  rw [diffTest_f]
  refine Rle_trans (φ.hlip _ _) ?_
  refine Rmul_le_Rmul_left (Rnonneg_ofQ φ.hLd φ.hLn) ?_
  refine Rle_trans (Rle_of_Req (Rabs_congr (affineMap_sub_lo a w ha hw t))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg hw hwn t)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hw hwn) (unit_abs_le_one h0 h1)) ?_
  exact Rle_of_Req (Rmul_one _)

-- ===========================================================================
-- (3) Rational partition bookkeeping.
-- ===========================================================================

theorem Qle_of_Qlt_loc {a b : Q} (h : Qlt a b) : Qle a b := by
  simp only [Qlt] at h; simp only [Qle]; omega

/-- `p0 + (p1 − p0) = p1`. -/
theorem Qadd_Qsub_cancel (p0 p1 : Q) : Qeq (add p0 (Qsub p1 p0)) p1 := by
  simp only [Qeq, add, Qsub, neg]
  push_cast
  ring_uor

/-- `(p2 − p0) − (p1 − p0) = p2 − p1`. -/
theorem Qsub_Qsub_Qsub (p0 p1 p2 : Q) :
    Qeq (Qsub (Qsub p2 p0) (Qsub p1 p0)) (Qsub p2 p1) := by
  simp only [Qeq, add, Qsub, neg]
  push_cast
  ring_uor

-- ===========================================================================
-- (4) THE RATIONAL-PARTITION SPLIT.
-- ===========================================================================

/-- **THE RATIONAL-PARTITION SPLIT** `∫_{[p 0, p (m+1)]} f = Σ_{i ≤ m} ∫_{[p i, p (i+1)]} f` for ANY
    rational partition with `p 0 < p (i+1)` and `p i ≤ p (i+1)` (iterated `riemannIntegralI_split_at`
    — the partition need not be uniform or dyadic). -/
theorem partition_split {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (p : Nat → Q) (hpd : ∀ i, 0 < (p i).den)
    (hp0 : ∀ i, Qlt (p 0) (p (i + 1))) (hpc : ∀ i, Qle (p i) (p (i + 1))) :
    ∀ m, Req (riemannIntegralI hLd hLn hlip hfc (p 0) (Qsub (p (m + 1)) (p 0)) (hpd 0)
                (Qsub_den_pos (hpd _) (hpd 0)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hp0 m))))
             (genSum (fun i => riemannIntegralI hLd hLn hlip hfc (p i) (Qsub (p (i + 1)) (p i)) (hpd i)
                (Qsub_den_pos (hpd _) (hpd i)) (Qsub_num_nonneg (hpc i))) (m + 1))
  | 0 => Req_symm (Req_trans (Radd_comm _ _) (Radd_zero _))
  | (m + 1) => by
      have hsplit := riemannIntegralI_split_at hLd hLn hlip hfc (p 0)
        (Qsub (p (m + 2)) (p 0)) (Qsub (p (m + 1)) (p 0)) (hpd 0)
        (Qsub_den_pos (hpd _) (hpd 0)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hp0 (m + 1))))
        (Qsub_den_pos (hpd _) (hpd 0)) (Qsub_num_pos_of_lt (hp0 m))
        (Qsub_le_sub (hpc (m + 1)))
        (Qsub_num_nonneg (Qsub_le_sub (hpc (m + 1))))
      refine Req_trans hsplit ?_
      refine Radd_congr (partition_split hLd hLn hlip hfc p hpd hp0 hpc m) ?_
      exact riemannIntegralI_congr_Q hLd hLn hlip hfc _ _ (p (m + 1)) (Qsub (p (m + 2)) (p (m + 1)))
        _ _ _ (hpd _) (Qsub_den_pos (hpd _) (hpd _)) (Qsub_num_nonneg (hpc (m + 1)))
        (Qadd_Qsub_cancel (p 0) (p (m + 1))) (Qsub_Qsub_Qsub (p 0) (p (m + 1)) (p (m + 2)))

-- ===========================================================================
-- (5) THE DECREASING-PARTITION SPLIT (cells `[q (i+1), q i]`, no sum reversal needed).
-- ===========================================================================

/-- **THE DECREASING-PARTITION SPLIT** `∫_{[q (m+1), q 0]} f = Σ_{i ≤ m} ∫_{[q (i+1), q i]} f` for ANY
    strictly decreasing rational partition (`q (i+1) < q i`, `q (i+1) < q 0`). -/
theorem partition_split_dec {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (q : Nat → Q) (hqd : ∀ i, 0 < (q i).den)
    (hq0 : ∀ i, Qlt (q (i + 1)) (q 0)) (hqs : ∀ i, Qlt (q (i + 1)) (q i)) :
    ∀ m, Req (riemannIntegralI hLd hLn hlip hfc (q (m + 1)) (Qsub (q 0) (q (m + 1))) (hqd _)
                (Qsub_den_pos (hqd 0) (hqd _)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hq0 m))))
             (genSum (fun i => riemannIntegralI hLd hLn hlip hfc (q (i + 1)) (Qsub (q i) (q (i + 1)))
                (hqd _) (Qsub_den_pos (hqd i) (hqd _)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hqs i))))
                (m + 1))
  | 0 => Req_symm (Req_trans (Radd_comm _ _) (Radd_zero _))
  | (m + 1) => by
      -- split [q(m+2), q 0] at width q(m+1) − q(m+2): first the NEW cell, then the IH window
      have hsplit := riemannIntegralI_split_at hLd hLn hlip hfc (q (m + 2))
        (Qsub (q 0) (q (m + 2))) (Qsub (q (m + 1)) (q (m + 2))) (hqd _)
        (Qsub_den_pos (hqd 0) (hqd _)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hq0 (m + 1))))
        (Qsub_den_pos (hqd _) (hqd _)) (Qsub_num_pos_of_lt (hqs (m + 1)))
        (Qsub_le_sub (Qle_of_Qlt_loc (hq0 m)))
        (Qsub_num_nonneg (Qsub_le_sub (Qle_of_Qlt_loc (hq0 m))))
      refine Req_trans hsplit ?_
      refine Req_trans (Radd_comm _ _) ?_
      refine Radd_congr ?_ (Req_refl _)
      refine Req_trans ?_ (partition_split_dec hLd hLn hlip hfc q hqd hq0 hqs m)
      exact riemannIntegralI_congr_Q hLd hLn hlip hfc _ _ (q (m + 1)) (Qsub (q 0) (q (m + 1)))
        _ _ _ (hqd _) (Qsub_den_pos (hqd 0) (hqd _)) (Qsub_num_nonneg (Qle_of_Qlt_loc (hq0 m)))
        (Qadd_Qsub_cancel (q (m + 2)) (q (m + 1))) (Qsub_Qsub_Qsub (q (m + 2)) (q (m + 1)) (q 0))

-- ===========================================================================
-- (6) `genSum` helpers and strict `Qinv` antitonicity.
-- ===========================================================================

/-- `Σ T − Σ U = Σ (T − U)`. -/
theorem genSum_Rsub_cells (T U : Nat → Real) :
    ∀ N, Req (Rsub (genSum T N) (genSum U N)) (genSum (fun i => Rsub (T i) (U i)) N)
  | 0 => Req_trans (Radd_congr (Req_refl _) (Rneg_congr (Req_refl _))) (Radd_neg zero)
  | (N + 1) => by
      show Req (Rsub (Radd (genSum T N) (T N)) (Radd (genSum U N) (U N)))
        (Radd (genSum (fun i => Rsub (T i) (U i)) N) (Rsub (T N) (U N)))
      refine Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _)) ?_
      refine Req_trans (Radd_add_add_comm _ _ _ _) ?_
      exact Radd_congr (genSum_Rsub_cells T U N) (Req_refl _)

/-- `|Σ T| ≤ Σ |T|`. -/
theorem genSum_Rabs_le (T : Nat → Real) :
    ∀ N, Rle (Rabs (genSum T N)) (genSum (fun i => Rabs (T i)) N)
  | 0 => Rle_of_Req Rabs_zero
  | (N + 1) => Rle_trans (Rabs_Radd (genSum T N) (T N))
      (Radd_le_add (genSum_Rabs_le T N) (Rle_refl _))

/-- `Σ_{i<N} c = N·c`. -/
theorem genSum_const_eq (c : Real) :
    ∀ N, Req (genSum (fun _ => c) N) (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) c)
  | 0 => Req_symm (Req_trans (Rmul_congr (Req_of_seq_Qeq (fun _ => Qeq_refl _)) (Req_refl c))
      (Req_trans (Rmul_comm _ c) (Rmul_zero c)))
  | (N + 1) => by
      show Req (Radd (genSum (fun _ => c) N) c) _
      refine Req_trans (Radd_congr (genSum_const_eq c N) (Req_symm (Rone_mul c))) ?_
      refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) ?_
      refine Rmul_congr ?_ (Req_refl c)
      refine Req_trans (Radd_ofQ_ofQ Nat.one_pos (by decide)) ?_
      exact ofQ_congr _ _ (by simp only [Qeq, add]; push_cast; ring_uor)

/-- `(∀ i, T i ≤ c) ⟹ Σ_{i<N} T i ≤ N·c`. -/
theorem genSum_le_const {T : Nat → Real} {c : Real} (h : ∀ i, Rle (T i) c) (N : Nat) :
    Rle (genSum T N) (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) c) :=
  Rle_trans (genSum_le (fun i => h i) N) (Rle_of_Req (genSum_const_eq c N))

/-- Strict antitonicity of `Qinv` on the positive cone. -/
theorem Qinv_lt_of_lt {a b : Q} (han : 0 < a.num) (hbn : 0 < b.num) (h : Qlt a b) :
    Qlt (Qinv b) (Qinv a) := by
  simp only [Qlt] at h
  show (b.den : Int) * ((a.num.toNat : Nat) : Int) < (a.den : Int) * ((b.num.toNat : Nat) : Int)
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt han), Int.toNat_of_nonneg (Int.le_of_lt hbn)]
  have e1 : (b.den : Int) * a.num = a.num * (b.den : Int) := Int.mul_comm _ _
  have e2 : (a.den : Int) * b.num = b.num * (a.den : Int) := Int.mul_comm _ _
  omega

end UOR.Bridge.F1Square.Square
