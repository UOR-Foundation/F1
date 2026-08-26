/-
F1 square — **THE FIVE-CHANNEL SPLIT AND THE UNIVERSAL RANGE-BOUND OBSTRUCTION** (`AtlasFiveSplit.lean`).

Target-side readback of the five-channel carrier (`AtlasCarrier5`, `AtlasColligation5`):

 * `farTailGram_split` — the far tail Gram is the far channel of the five-channel form with scalar mass
   `fc = farCoef`: `farTailGram_k(f,g) = farG(A_far f, A_far g) − farG(B_far f, B_far g)` (the cycle far
   coordinate is `0`: `posFiber_VV_cycle_zero`; the cut far coordinate is `V/2`, and `4·(1/2)·(1/2) = 1`);
 * `source5_split_fixed` — THE ALL-PAIRS FIVE-CHANNEL NORMALIZATION:
       `atlasDefectGram_k(f,g) + farTailGram_k(f,g) = inner5(A_k f, A_k g) − inner5(B_k f, B_k g)`;
 * `atlasMatrix_range_bound_iff_defect` — the contraction of the explicit `atlasMatrix` on the range,
   `‖atlasMatrix(A_k f)‖² ≤ ‖A_k f‖²`, is EQUIVALENT to `atlasDefectGram_k(f,f) + farTailGram_k(f,f) ≥ 0`;
 * `colligation_range_bound_imp_defect` — the same implication for EVERY map `T : Carrier5 → Carrier5`
   reproducing `B_k f` on the measured supports;
 * `colligation_family_imp_dominance` — a family of such maps bounded on the range at every `k ≥ 1` (in
   particular at the scheduled `k = j + archCNC`) gives `CurrentArchDominatesPrime` through
   `defectSeq_nonneg_imp_dominance` and `CoupledForm_eq_lim_defect`; `atlasMatrix_family_imp_dominance` is the
   instance for the explicit matrix.

HONEST SCOPE.  Nothing here proves the bound.  `atlasMatrix_range_bound_iff_defect` shows that for the
explicit signed five-channel colligation (exact reproduction, no refinement parameter, no error term) the
bound on the range IS the sign of the defect Gram at level `k`, and `colligation_range_bound_imp_defect`
shows that no other reproducing colligation — whatever its locality, boundary routing, or asymptotics — can
have an easier range bound: the bound is not a property of the colligation.  `CurrentArchDominatesPrime` is
NOT claimed.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasColligation5
import F1Square.Square.AtlasDefectReadback

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The far channel.
-- ===========================================================================

/-- `(a·b)·(c·d) ≈ (a·c)·(b·d)`. -/
theorem mul_mul_mul_comm_fs (a b c d : Real) : Req (Rmul (Rmul a b) (Rmul c d)) (Rmul (Rmul a c) (Rmul b d)) := by
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl a) ?_) (Req_symm (Rmul_assoc _ _ _)))
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl d)) (Rmul_assoc _ _ _))

/-- `(½·½)·4 = 1`. -/
theorem quarter_four_fs : Req (Rmul (Rmul cH cH) c4) one :=
  Req_trans (Rmul_congr (Rmul_ofQ_ofQ (by decide) (by decide)) (Req_refl _))
    (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos (by decide) (by decide)) Nat.one_pos)
      (ofQ_congr (a := mul (mul (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)) (⟨4, 1⟩ : Q)) (b := (⟨1, 1⟩ : Q))
        (Qmul_den_pos (Qmul_den_pos (by decide) (by decide)) Nat.one_pos) Nat.one_pos (by decide)))

/-- The far pointwise bookkeeping: `((4·(A·(w·r)))·(½V_f))·(½V_g) = (A·w)·((V_f·V_g)·r)`. -/
theorem far_alg (A w r Vf Vg : Real) :
    Req (Rmul (Rmul (Rmul c4 (Rmul A (Rmul w r))) (Rmul cH Vf)) (Rmul cH Vg)) (Rmul (Rmul A w) (Rmul (Rmul Vf Vg) r)) := by
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (mul_mul_mul_comm_fs cH Vf cH Vg)) ?_
  refine Req_trans (mul_mul_mul_comm_fs c4 _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) quarter_four_fs) (Req_refl _)) ?_
  refine Req_trans (Rone_mul _) ?_
  -- (A·(w·r))·(Vf·Vg) ≈ (A·w)·((Vf·Vg)·r)
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl A) (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Req_refl _) (Rmul_comm _ _))

/-- **The far cut Gram** with `fc = farCoef`: `farG(A_far f, A_far g) = ((2·farCoef)·w)·∫₀¹ V(f)V(g)r`. -/
theorem farG_cut_eq (C : NormCtx) (k : Nat) (f g : L2Test) :
    Req (farG C (farCoef C k) (cutAnalysis5 C k f).far (cutAnalysis5 C k g).far)
        (Rmul (Rmul (Rmul cTwo (farCoef C k)) (ofQ C.w C.hw))
          (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g))) := by
  unfold farG gramT CField.intT
  refine intU_smul_free _ (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g) _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, cutAnalysis5_far, cutAnalysis5_far]
  refine Req_trans (Rmul_congr (Rmul_congr (farDens5_F C _ one _) (posFiber_VV_cut _)) (posFiber_VV_cut _)) ?_
  unfold vvInt prodInt affC
  exact far_alg _ _ _ _ _

/-- **The far cycle Gram vanishes** (the far cycle coordinate is `0`). -/
theorem farG_cyc_zero (C : NormCtx) (k : Nat) (fc : Real) (f g : L2Test) :
    Req (farG C fc (cycleAnalysis5 C k f).far (cycleAnalysis5 C k g).far) zero := by
  unfold farG gramT CField.intT
  refine intU_zero_free _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, cycleAnalysis5_far, cycleAnalysis5_far]
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (posFiber_VV_cycle_zero _)) (Req_refl _)) ?_
  exact Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))

/-- **★ FAR SPLIT**: `farTailGram_k(f,g) = farG(A_far f, A_far g) − farG(B_far f, B_far g)` with `fc = farCoef`. -/
theorem farTailGram_split (C : NormCtx) (k : Nat) (f g : L2Test) :
    Req (farTailGram C f g k)
        (Rsub (farG C (farCoef C k) (cutAnalysis5 C k f).far (cutAnalysis5 C k g).far)
              (farG C (farCoef C k) (cycleAnalysis5 C k f).far (cycleAnalysis5 C k g).far)) := by
  refine Req_symm (Req_trans (Rsub_congr (farG_cut_eq C k f g) (farG_cyc_zero C k _ f g)) (Req_trans (Rsub_zero _) ?_))
  unfold farTailGram
  exact Rmul_assoc _ _ _

-- ===========================================================================
-- (2) THE ALL-PAIRS FIVE-CHANNEL NORMALIZATION.
-- ===========================================================================

/-- **★ `atlasDefectGram_k(f,g) + farTailGram_k(f,g) = inner5(A_k f, A_k g) − inner5(B_k f, B_k g)`** (all pairs of tests). -/
theorem source5_split_fixed (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : L2Test) :
    Req (Radd (atlasDefectGram C k hk f g) (farTailGram C f g k))
        (Rsub (inner5 C k hk (farCoef C k) (cutAnalysis5 C k f) (cutAnalysis5 C k g))
              (inner5 C k hk (farCoef C k) (cycleAnalysis5 C k f) (cycleAnalysis5 C k g))) := by
  refine Req_trans (Radd_congr (atlasDefectGram_split C k hk f g) (farTailGram_split C k f g)) ?_
  exact add_sub_add_c5 _ _ _ _

-- ===========================================================================
-- (3) The range bound of the explicit matrix, and of every reproducing colligation, is the defect sign.
-- ===========================================================================

/-- **★ THE RANGE BOUND OF `atlasMatrix` IS THE DEFECT SIGN** at level `k`. -/
theorem atlasMatrix_range_bound_iff_defect (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) :
    Rle (energy5 C k hk (farCoef C k) (atlasMatrix C k (cutAnalysis5 C k f))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f)) ↔
      Rnonneg (Radd (atlasDefectGram C k hk f f) (farTailGram C f f k)) := by
  refine Iff.trans (atlasMatrix_range_bound_iff C k hk (farCoef C k) f) ?_
  exact ⟨fun h => Rnonneg_congr (Req_symm (source5_split_fixed C k hk f f)) h,
         fun h => Rnonneg_congr (source5_split_fixed C k hk f f) h⟩

/-- **★ THE UNIVERSAL OBSTRUCTION**: EVERY map `T : Carrier5 → Carrier5` reproducing `B_k f` on the measured
    supports and bounded on the range forces `atlasDefectGram_k(f,f) + farTailGram_k(f,f) ≥ 0`. -/
theorem colligation_range_bound_imp_defect (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (T : Carrier5 → Carrier5) (f : L2Test)
    (hrep : EqOnSupport5 C k (cycleAnalysis5 C k f) (T (cutAnalysis5 C k f)))
    (hbd : Rle (energy5 C k hk (farCoef C k) (T (cutAnalysis5 C k f))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f))) :
    Rnonneg (Radd (atlasDefectGram C k hk f f) (farTailGram C f f k)) :=
  Rnonneg_congr (Req_symm (source5_split_fixed C k hk f f)) (colligation_range_bound_imp C k hk (farCoef C k) T f hrep hbd)

/-- **A family of reproducing colligations bounded on the range at every level gives dominance** (through the
    scheduled levels `k = j + archCNC(C,f,f)`, `defectSeq_nonneg_imp_dominance`, `CoupledForm_eq_lim_defect`). -/
theorem colligation_family_imp_dominance (C : NormCtx) (T : ∀ k, 1 ≤ k → Carrier5 → Carrier5)
    (hrep : ∀ k (hk : 1 ≤ k) (f : L2Test), EqOnSupport5 C k (cycleAnalysis5 C k f) (T k hk (cutAnalysis5 C k f)))
    (hbd : ∀ k (hk : 1 ≤ k) (f : ClosedCore C),
      Rle (energy5 C k hk (farCoef C k) (T k hk (cutAnalysis5 C k f.1))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f.1))) :
    CurrentArchDominatesPrime C :=
  defectSeq_nonneg_imp_dominance C (fun f j =>
    colligation_range_bound_imp_defect C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (T _ _) f.1
      (hrep _ _ f.1) (hbd _ _ f))

/-- The instance for the explicit matrix: its range bound at every level `k ≥ 1` on the core gives dominance. -/
theorem atlasMatrix_family_imp_dominance (C : NormCtx)
    (hbd : ∀ k (hk : 1 ≤ k) (f : ClosedCore C),
      Rle (energy5 C k hk (farCoef C k) (atlasMatrix C k (cutAnalysis5 C k f.1))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f.1))) :
    CurrentArchDominatesPrime C :=
  colligation_family_imp_dominance C (fun k _ => atlasMatrix C k) (fun k _ f => atlasMatrix_reproduces C k f) hbd

end UOR.Bridge.F1Square.Square
