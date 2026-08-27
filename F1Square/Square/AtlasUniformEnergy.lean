/-
F1 square — **THE k-UNIFORM ENERGY BOUND OF THE CUT ANALYSES** (`AtlasUniformEnergy.lean`, target side).

The five-channel energy `energy5_k(A_k f)` of a fixed test is bounded uniformly in the truncation `k ≥ 1`:

  * the pole, prime and constant Grams do not depend on `k`;
  * on the compact tail `|Z_{k,x̄}| = x̄·K_k(x̄)·|D_{x̄}| ≤ B·L_D` because `K_k(x̄)·(x̄ − 1) ≤ 1` for every `k`
    (`Kfl_mul_dist_le_one`: the floored kernel `1/max(x̄ − 1/x̄, 2^{-k})` times `x̄ − 1 ≤ x̄ − 1/x̄`) and
    `|D_x| ≤ L_D·|x − 1|` (`Dc_abs_le_dist_one`), so the tail Gram is at most `B·(8w/a)·M_tail²`;
  * the far coefficient satisfies `farCoef_k ≤ 2` for every `k` (`farCoef_le_two`: the first unit term is at
    most `1` since `K_k ≤ 1` beyond `2`, and the tail of the improper integral is at most `1` by the decay
    bound `1/((m+1)m)` and `genSum_gap`).

`energy5_cutAnalysis5_le`: `energy5_k(A_k f) ≤ E_f` with `E_f` explicit and independent of `k`.  This is the
bounded-analysis hypothesis of the controlled-asymptotic readback; no sign is involved.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitFiber
import F1Square.Square.AtlasTailSplit
import F1Square.Square.WeilArchKern
import F1Square.Square.AtlasFullCoherent5

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) `farCoef_k ≤ 2` uniformly in `k`.
-- ===========================================================================

/-- The first unit term `∫_{[1,2]} farKer_k ≤ 1` (`farKer_k(u) ≤ 1·K_k(u + B − 1) ≤ 1` since `u + B − 1 ≥ 2`). -/
theorem farKer_term_zero_le (C : NormCtx) (k : Nat) :
    Rle (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc 0) one := by
  unfold integralTerm
  have hbd : ∀ x, Rle zero x → Rle x one →
      Rle (Rabs ((farKer C k).f (affineMap (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x))) one := by
    intro x hx0 _
    rw [farKer_f]
    have hu : Rle (ofQ (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos) (affineMap (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) :=
      affineMap_ge_lo_c5 _ _ _ _ (by decide) x hx0
    have hs : Rle (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (ofQ (farShift C k) (farShift_den C k)) := Rle_ofQ_ofQ _ _ (one_le_farShift C k)
    have hy : Rle (ofQ (⟨((1 : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) (ofQ (farShift C k) (farShift_den C k))) :=
      Rle_trans (Rle_of_Req (Req_symm (Req_trans (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos) (ofQ_congr _ _ (by decide))))) (Radd_le_add hu hs)
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    have hK : Rle (Rabs (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) _)) one :=
      Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _)))
        (Rle_trans (archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) 1 (Nat.le_refl 1) _ hy)
          (Rle_of_Req (ofQ_congr _ (by decide) (by decide))))
    have hr : Rle (Rabs (rOne (Radd (affineMap (⟨((0 : Nat) : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) (ofQ (farShift C k) (farShift_den C k))))) one :=
      Rle_trans (rOne_bd _) (Rle_of_Req (ofQ_congr _ (by decide) (by decide)))
    exact Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) Rnonneg_one hr hK) (Rle_of_Req (Rmul_one _))
  refine Rle_trans (Rle_Rabs_self _) ?_
  refine Rle_trans (riemannIntegralI_abs_le_window_real (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc
    _ _ one Nat.one_pos (by decide) (by decide) hbd) ?_
  exact Rle_of_Req (Rone_mul _)

/-- **★ `farCoef_k ≤ 2` for every `k`**: `T_0 ≤ 1` and the tail of the partial sums is at most `1` (`genSum_gap`). -/
theorem farCoef_le_two (C : NormCtx) (k : Nat) : Rle (farCoef C k) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) := by
  unfold farCoef improperIntegral1
  refine Rlim_le_const _ ?_
  intro j
  have hT : ∀ m (hm : 1 ≤ m), Rle (Rabs (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc m))
      (ofQ (mul (⟨1, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos Nat.one_pos (digamma_succ_mul_pos hm))) := by
    intro m hm
    obtain ⟨h1, h2⟩ := farKer_decay C k m hm
    exact Rabs_le_of_both h2 (Rle_trans (Rle_Rneg h1) (Rle_of_Req (Rneg_neg _)))
  obtain ⟨d, hd⟩ : ∃ d, digammaMidx (⟨1, 1⟩ : Q) j = 1 + d :=
    ⟨digammaMidx (⟨1, 1⟩ : Q) j - 1, by have := digammaMidx_ge_one (⟨1, 1⟩ : Q) j; omega⟩
  rw [hd]
  have hgap := genSum_gap (T := integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc)
    Nat.one_pos (by decide) hT (M := 1) (Nat.le_refl 1) d
  have h1 : Rle (genSum (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc) 1) one := by
    show Rle (Radd zero _) one
    exact Rle_trans (Rle_of_Req (Req_trans (Radd_comm _ _) (Radd_zero _))) (farKer_term_zero_le C k)
  -- genSum (1+d) = genSum 1 + (genSum (1+d) − genSum 1) ≤ 1 + 1
  have hsplit : Req (genSum (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc) (1 + d))
      (Radd (genSum (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc) 1)
            (Rsub (genSum (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc) (1 + d))
                  (genSum (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc) 1))) :=
    Req_symm (Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc _ _ _)
      (Req_trans (Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_neg _))) (Radd_zero _))))
  refine Rle_trans (Rle_of_Req hsplit) ?_
  refine Rle_trans (Radd_le_add h1 (Rle_of_Rabs_le hgap)) ?_
  refine Rle_of_Req (Req_trans (Radd_congr (Req_refl one)
    (ofQ_congr (a := mul (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q)) (b := (⟨1, 1⟩ : Q)) (Qmul_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos (by decide))) ?_)
  exact Req_trans (Radd_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr (a := add (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q)) (b := (⟨2, 1⟩ : Q)) (add_den_pos (by decide) Nat.one_pos) Nat.one_pos (by decide))

-- ===========================================================================
-- (2) `K_k(x̄)·(x̄ − 1) ≤ 1` for every `k`, and the uniform bound of the tail cut coordinate.
-- ===========================================================================

theorem rOne_le_one_ue (x : Real) : Rle (rOne x) one :=
  Rle_trans (Rle_of_Rabs_le (rOne_bd x)) (Rle_of_Req (ofQ_congr (Qinv_den_pos (by decide)) (by decide) (by decide)))

/-- `x̄ − 1 ≤ x̄ − 1/max(x̄,1) = innerXm x̄`. -/
theorem dist_one_le_innerXm {x : Real} (hx1 : Rle one x) : Rle (Rsub x one) (innerXm x) :=
  Radd_le_add (Rle_refl x) (Rle_Rneg (rOne_le_one_ue x))

/-- **`K_k(x̄)·(x̄ − 1) ≤ 1`** for `x̄ ≥ 1` and every floor `c`. -/
theorem Kfl_mul_dist_le_one (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) {x : Real} (hx1 : Rle one x) :
    Rle (Rmul (Kfl c hcn hcd x) (Rsub x one)) one := by
  have hK : Rnonneg (Kfl c hcn hcd x) := Rnonneg_clampedInv c hcn hcd _
  have hle : Rle (Rsub x one) (qClampQ c hcd (innerXm x)) :=
    Rle_trans (dist_one_le_innerXm hx1) (Rle_self_qClampQ c hcd _)
  refine Rle_trans (Rmul_le_Rmul_left hK hle) (Rle_of_Req ?_)
  show Req (Rmul (clampedInv c hcn hcd (innerXm x)) (qClampQ c hcd (innerXm x))) one
  exact Req_trans (Rmul_comm _ _) (qClampQ_mul_clampedInv c hcn hcd (innerXm x))

/-- The uniform bound `M_Z = B·L_D` of `|Z_{k,x̄}(f,t)| = |x̄·K_k(x̄)·D_{x̄}(f,t)|`. -/
def zBoundQ (C : NormCtx) (f : L2Test) : Q := mul (canonB C) (DcL C f)
theorem zBoundQ_den (C : NormCtx) (f : L2Test) : 0 < (zBoundQ C f).den := Qmul_den_pos (canonB_den C) (DcL_den C f)
theorem zBoundQ_num (C : NormCtx) (f : L2Test) : 0 ≤ (zBoundQ C f).num := Qmul_num_nonneg (Int.le_of_lt (canonB_num C)) (DcL_num C f)

/-- **`|Z_{k,x̄}(f,t)| ≤ B·L_D` uniformly in `k`.** -/
theorem Zc_abs_le_uniform (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Rle (Rabs (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t)) (ofQ (zBoundQ C f) (zBoundQ_den C f)) := by
  unfold Zc
  -- |x̄·K·D| = x̄·(K·|D|) ≤ B·(K·L_D·|x̄ − 1|) = B·(L_D·(K·|x̄−1|)) ≤ B·L_D
  have hx1 := xcl_ge_one C x
  have hxB := xcl_le_B C x
  have hxnn : Rnonneg (xcl C x) := Rnonneg_of_Rle_zero (xcl_zero_le C x)
  have hK : Rnonneg (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x)) := Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _
  have hD := Dc_abs_le_dist_one C f (xcl C x) t
  -- |x̄ − 1| = x̄ − 1
  have hdist : Req (Rabs (Rsub (xcl C x) one)) (Rsub (xcl C x) one) := Rabs_of_nonneg (Rnonneg_Rsub_of_Rle hx1)
  have hKD : Rle (Rmul (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x)) (Rabs (Dc C (xcl C x) f t))) (ofQ (DcL C f) (DcL_den C f)) := by
    refine Rle_trans (Rmul_le_Rmul_left hK hD) ?_
    refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) hdist))) ?_
    -- K·(L·(x̄−1)) = L·(K·(x̄−1)) ≤ L·1
    refine Rle_trans (Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))) ?_
    refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (DcL_den C f) (DcL_num C f)) (Kfl_mul_dist_le_one (dyQ k) (dyQ_num k) (dyQ_den k) hx1)) ?_
    exact Rle_of_Req (Rmul_one _)
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Rabs_Rmul _ _) (Req_refl _))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_assoc _ _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (DcL_den C f) (DcL_num C f))
    (Rle_trans (Rle_of_Req (Rabs_of_nonneg hxnn)) hxB)
    (Rle_trans (Rle_of_Req (Rmul_congr (Rabs_of_nonneg hK) (Req_refl _))) hKD)) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (canonB_den C) (DcL_den C f))

-- ===========================================================================
-- (3) Gram bounds by width × pointwise sup, and the bounds of the tail and far cut coordinates.
-- ===========================================================================

/-- `|∫₀¹ z(x, a + w·y) dy| ≤ K` from a pointwise bound on the Haar window. -/
theorem intT_abs_le_pt (C : NormCtx) (z : CField) (x : Real) (K : Real)
    (h : ∀ y, Rle zero y → Rle y one → Rle (Rabs (z.F x (affineMap C.a C.w C.had C.hw y))) K) :
    Rle (Rabs (intT C z x)) K :=
  riemannIntegral_abs_le_unit_real _ _ _ _ K h

/-- `|∫_{[lo,lo+w]} ∫₀¹ z| ≤ w·K` from a pointwise bound on both windows. -/
theorem intX_abs_le_pt (C : NormCtx) (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (K : Real)
    (h : ∀ s, Rle zero s → Rle s one → ∀ y, Rle zero y → Rle y one →
      Rle (Rabs (z.F (affineMap lo w hlo hw s) (affineMap C.a C.w C.had C.hw y))) K) :
    Rle (Rabs (intX C z lo w hlo hw hwn)) (Rmul (ofQ w hw) K) := by
  unfold intX
  exact riemannIntegralI_abs_le_window_real _ _ _ _ lo w K hlo hw hwn (fun s hs0 hs1 => intT_abs_le_pt C z _ K (h s hs0 hs1))

/-- `|A| ≤ ¼·(M_u + M_v)` for `A = aCoefGa one u v`. -/
theorem aCoefGa_abs_le {u v Mu Mv : Real} (hu : Rle (Rabs u) Mu) (hv : Rle (Rabs v) Mv) :
    Rle (Rabs (aCoefGa one u v)) (Rmul cQ (Radd Mu Mv)) := by
  unfold aCoefGa
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_Rabs _) (Rle_trans (Rabs_Radd _ _)
    (Radd_le_add (Rle_trans (Rle_of_Req (Rabs_congr (Rone_mul u))) hu) (Rle_trans (Rle_of_Req (Rabs_Rneg v)) hv)))) ?_
  exact Rle_of_Req (Rmul_congr (Rabs_of_nonneg (Rnonneg_ofQ (by decide) (by decide))) (Req_refl _))

/-- The uniform bound `M_tail = ¼·(B·L_D + M_f)` of the tail cut coordinate. -/
def tailCutBound (C : NormCtx) (f : L2Test) : Real :=
  Rmul cQ (Radd (ofQ (zBoundQ C f) (zBoundQ_den C f)) (ofQ f.M f.hMd))

/-- **`|A_tail(x̄,t)| ≤ M_tail` uniformly in `k`** (at every real scale, every `t`). -/
theorem tail_cut_abs_le (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Rle (Rabs ((cutAnalysis5 C k f).tail.F x t)) (tailCutBound C f) := by
  rw [cutAnalysis5_tail]
  refine aCoefGa_abs_le (Zc_abs_le_uniform C k f x t) ?_
  -- |W| = |r(x̄)·V| ≤ 1·M_f
  unfold Wc
  have hr : Rle (Rabs (rOne (xcl C x))) one :=
    Rle_trans (rOne_bd _) (Rle_of_Req (ofQ_congr (Qinv_den_pos (by decide)) (by decide) (by decide)))
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ f.hMd f.hMn) hr (Vc_bd C f t)) ?_
  exact Rle_of_Req (Rone_mul _)

/-- `|A_far(t)| ≤ ½·M_f`. -/
theorem far_cut_abs_le (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Rle (Rabs ((cutAnalysis5 C k f).far.F x t)) (Rmul cH (ofQ f.M f.hMd)) := by
  rw [cutAnalysis5_far]
  refine Rle_trans (Rle_of_Req (Rabs_congr (posFiber_VV_cut _))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  exact Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ f.hMd f.hMn)
    (Rle_of_Req (Rabs_of_nonneg (Rnonneg_ofQ (by decide) (by decide)))) (Vc_bd C f t)

/-- `|4·2·w·r| ≤ 8·w·(1/a)` (the tail density). -/
def densBoundQ (C : NormCtx) : Q := mul (⟨8, 1⟩ : Q) (mul C.w (Qinv C.a))
theorem densBoundQ_den (C : NormCtx) : 0 < (densBoundQ C).den := Qmul_den_pos Nat.one_pos (Qmul_den_pos C.hw (Qinv_den_pos C.han))
theorem densBoundQ_num (C : NormCtx) : 0 ≤ (densBoundQ C).num := Qmul_num_nonneg (by decide) (wa_num C)

theorem tailDens5_abs_le (C : NormCtx) (x t : Real) : Rle (Rabs ((tailDens5 C).F x t)) (ofQ (densBoundQ C) (densBoundQ_den C)) := by
  show Rle (Rabs (Rmul (ofQ q4 Nat.one_pos) (Rmul (ofQ q2 Nat.one_pos) (Rmul (ofQ C.w C.hw) (rEv C t))))) _
  have h2 : Rle (Rabs (Rmul (ofQ q2 Nat.one_pos) (Rmul (ofQ C.w C.hw) (rEv C t))))
      (ofQ (mul q2 (mul C.w (Qinv C.a))) (Qmul_den_pos Nat.one_pos (Qmul_den_pos C.hw (Qinv_den_pos C.han)))) :=
    abs_mul_bd Nat.one_pos _ (wa_num C) (Rle_of_Req (Rabs_ofQ_nonneg Nat.one_pos (by decide))) (wr_bd C t)
  refine Rle_trans (abs_mul_bd Nat.one_pos _ (Qmul_num_nonneg (by decide) (wa_num C))
    (Rle_of_Req (Rabs_ofQ_nonneg Nat.one_pos (by decide))) h2) ?_
  exact Rle_ofQ_ofQ _ _ (Qeq_le (by simp only [Qeq, mul, q4, q2, densBoundQ]; push_cast; ring_uor))

/-- `|4·(2·fc)·w·r| ≤ 2·(8·w/a)` for `0 ≤ fc ≤ 2`. -/
theorem farDens5_abs_le (C : NormCtx) {fc : Real} (hfc0 : Rnonneg fc) (hfc2 : Rle fc (ofQ (⟨2, 1⟩ : Q) Nat.one_pos)) (x t : Real) :
    Rle (Rabs ((farDens5 C fc).F x t)) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (densBoundQ C) (densBoundQ_den C))) := by
  show Rle (Rabs (Rmul (ofQ q4 Nat.one_pos) (Rmul (Rmul cTwo fc) (Rmul (ofQ C.w C.hw) (rEv C t))))) _
  have hfcab : Rle (Rabs (Rmul cTwo fc)) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos)) :=
    Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ Nat.one_pos (by decide))
      (Rle_of_Req (Rabs_ofQ_nonneg Nat.one_pos (by decide))) (Rle_trans (Rle_of_Req (Rabs_of_nonneg hfc0)) hfc2))
  have hwr : Rle (Rabs (Rmul (ofQ C.w C.hw) (rEv C t))) (ofQ (mul C.w (Qinv C.a)) (Qmul_den_pos C.hw (Qinv_den_pos C.han))) := wr_bd C t
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_ofQ _ (by decide)) (Rnonneg_ofQ _ (by decide)))
    (Rnonneg_ofQ _ (wa_num C))) (Rle_of_Req (Rabs_ofQ_nonneg Nat.one_pos (by decide)))
    (Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ (wa_num C)) hfcab hwr))) ?_
  -- 4·((2·2)·(w/a)) = 2·(8·(w/a))
  refine Rle_of_Req ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Rmul_ofQ_ofQ _ _) (Req_refl _)) (Rmul_ofQ_ofQ _ _))) ?_
  refine Req_trans (Rmul_ofQ_ofQ _ _) ?_
  refine Req_trans (ofQ_congr _ (Qmul_den_pos Nat.one_pos (densBoundQ_den C)) ?_) (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (densBoundQ_den C)))
  simp only [Qeq, mul, q4, densBoundQ]; push_cast; ring_uor

-- ===========================================================================
-- (4) ★ THE k-UNIFORM ENERGY BOUND.
-- ===========================================================================

/-- The `k`-free bound of the tail Gram: `B·(8w/a)·M_tail²`. -/
def tailGramBound (C : NormCtx) (f : L2Test) : Real :=
  Rmul (ofQ (canonB C) (canonB_den C)) (Rmul (ofQ (densBoundQ C) (densBoundQ_den C)) (Rmul (tailCutBound C f) (tailCutBound C f)))
/-- The `k`-free bound of the far Gram: `2·(8w/a)·(M_f/2)²`. -/
def farGramBound (C : NormCtx) (f : L2Test) : Real :=
  Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (ofQ (densBoundQ C) (densBoundQ_den C))) (Rmul (Rmul cH (ofQ f.M f.hMd)) (Rmul cH (ofQ f.M f.hMd)))

/-- **The `k`-independent energy bound** `E_f`: the pole, prime and constant Grams of the analysis (which do not
    depend on `k`) plus the tail and far bounds. -/
def energyBound (C : NormCtx) (f : L2Test) : Real :=
  Radd (Radd (Radd (Radd
    (poleG C (aCoefF (UF C f) (negF (VF C f))) (aCoefF (UF C f) (negF (VF C f))))
    (RsumN (fun m => primeG C m (aCoefF (UFix C (upR m) f) (VF C f)) (aCoefF (UFix C (upR m) f) (VF C f))) C.X))
    (constG C (aCoefF (VF C f) (VF C f)) (aCoefF (VF C f) (VF C f))))
    (tailGramBound C f))
    (farGramBound C f)

/-- `Qle (tailGap C k) (canonB C)` (`tailGap = B − (1 + 2^{-k})`, `1 + 2^{-k} ≥ 0`). -/
theorem tailGap_le_B (C : NormCtx) (k : Nat) : Qle (tailGap C k) (canonB C) := by
  refine Qle_of_Rle_ofQ_of (tailGap_den C k) (canonB_den C) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rsub_ofQ_ofQ (canonB_den C) (tailLo_den k)))) ?_
  refine Rle_trans (Radd_le_add (Rle_refl _) (Rle_Rneg (Rle_ofQ_ofQ (by decide) (tailLo_den k) (Qle_zero_of_num_of (tailLo_num k))))) ?_
  refine Rle_of_Req (Req_trans (Radd_congr (Req_refl _) (Rneg_ofQ _ _)) ?_)
  exact Req_trans (Radd_ofQ_ofQ _ _) (ofQ_congr _ _ (by simp only [Qeq, add, neg, canonB]; push_cast; ring_uor))

/-- The tail Gram is at most `tailGramBound` for every `k ≥ 1`. -/
theorem tailG_le_bound (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) :
    Rle (tailG C k hk (cutAnalysis5 C k f).tail (cutAnalysis5 C k f).tail) (tailGramBound C f) := by
  unfold tailG gramX tailGramBound
  have hnnK : Rnonneg (Rmul (ofQ (densBoundQ C) (densBoundQ_den C)) (Rmul (tailCutBound C f) (tailCutBound C f))) :=
    Rnonneg_Rmul (Rnonneg_ofQ _ (densBoundQ_num C)) (Rnonneg_Rmul_self _)
  refine Rle_trans (Rle_Rabs_self _) ?_
  refine Rle_trans (intX_abs_le_pt C _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
    (Rmul (ofQ (densBoundQ C) (densBoundQ_den C)) (Rmul (tailCutBound C f) (tailCutBound C f))) ?_) ?_
  · intro s _ _ y _ _
    rw [mulF_F, mulF_F]
    have hMnn : Rnonneg (tailCutBound C f) :=
      Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_Rabs _)) (tail_cut_abs_le C k f one one))
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) hMnn ?_ (tail_cut_abs_le C k f _ _)) (Rle_of_Req (Rmul_assoc _ _ _))
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    exact Rmul_le_Rmul_both (Rnonneg_Rabs _) hMnn (tailDens5_abs_le C _ _) (tail_cut_abs_le C k f _ _)
  · exact Rmul_le_Rmul_right hnnK (Rle_ofQ_ofQ _ _ (tailGap_le_B C k))

/-- The far Gram is at most `farGramBound` for every `k`. -/
theorem farG_le_bound (C : NormCtx) (k : Nat) (f : L2Test) :
    Rle (farG C (farCoef C k) (cutAnalysis5 C k f).far (cutAnalysis5 C k f).far) (farGramBound C f) := by
  unfold farG gramT farGramBound
  refine Rle_trans (Rle_Rabs_self _) ?_
  refine intT_abs_le_pt C _ one _ ?_
  intro y _ _
  rw [mulF_F, mulF_F]
  have hA := far_cut_abs_le C k f one (affineMap C.a C.w C.had C.hw y)
  have hAnn : Rnonneg (Rmul cH (ofQ f.M f.hMd)) := Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_Rabs _)) hA)
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) hAnn ?_ hA) (Rle_of_Req (Rmul_assoc _ _ _))
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  exact Rmul_le_Rmul_both (Rnonneg_Rabs _) hAnn (farDens5_abs_le C (farCoef_nonneg C k) (farCoef_le_two C k) _ _) hA

/-- **★ THE k-UNIFORM ENERGY BOUND**: `energy5_k(A_k f) ≤ E_f` for every `k ≥ 1`, `E_f` independent of `k`. -/
theorem energy5_cutAnalysis5_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) :
    Rle (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f)) (energyBound C f) := by
  unfold energy5 inner5 inner4 energyBound
  refine Radd_le_add (Radd_le_add (Rle_refl _) (tailG_le_bound C k hk f)) (farG_le_bound C k f)

end UOR.Bridge.F1Square.Square
