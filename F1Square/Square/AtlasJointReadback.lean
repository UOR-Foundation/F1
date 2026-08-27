/-
F1 square — **THE JOINT MATRIX READ BACK ON THE TARGET** (`AtlasJointReadback.lean`, target side).

On the range of the cut analysis the cross form of the joint matrix is minus the level-`k` defect:

    `crossForm5_k(A_k f) = −(atlasDefectGram_k(f,f) + farTailGram_k(f,f))`          (`crossForm5_range`),

so the joint contraction `energy5(atlasMatrixJoint (A_k f)) ≤ energy5(A_k f)` is EQUIVALENT to the level-`k`
defect sign (`jointMatrix_bound_iff_defect`) — the fixed-`k` truncated Weil positivity.  The asymptotic
readback: a family bounded up to a VANISHING slack `δ_j` along the repository schedule `k = j + archCNC`
forces `CoupledForm ≥ 0`, i.e. `CurrentArchDominatesPrime` (`vanishing_slack_imp_dominance`), and the
`(1 + ε_j)²`-bound with bounded analyses produces such a slack pointwise (`slack_of_eps_bound`).

HONEST SCOPE: no bound, no slack sequence, and no sign is asserted here for any `k`.  Every theorem is an
exact identity or an implication whose hypothesis is the sign (or its vanishing-slack relaxation).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasJoint5
import F1Square.Square.AtlasFiveSplit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- The joint matrix reproduces `B_k f`, so its energy on `A_k f` is the cycle energy. -/
theorem energy5_joint_matrix_eq (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) (f : L2Test) :
    Req (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f))) (energy5 C k hk fc (cycleAnalysis5 C k f)) :=
  Req_symm (inner5_congr_support C k hk fc (atlasMatrixJoint_reproduces C k hw0 hk f) (atlasMatrixJoint_reproduces C k hw0 hk f))

/-- **★ THE CROSS FORM ON THE RANGE IS MINUS THE DEFECT**: `crossForm5_k(A_k f) = −(D_k(f,f) + far_k(f,f))`. -/
theorem crossForm5_range (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (f : L2Test) :
    Req (crossForm5 C k hw0 hk (farCoef C k) (cutAnalysis5 C k f))
        (Rneg (Radd (atlasDefectGram C k hk f f) (farTailGram C f f k))) := by
  have hE := energy5_joint_eq C k hw0 hk (farCoef C k) (cutAnalysis5_jointSyn C k hw0 hk f)
  have hB := energy5_joint_matrix_eq C k hw0 hk (farCoef C k) f
  have hS := source5_split_fixed C k hk f f
  -- cross ≈ e(T A) − e(A) ≈ e(B) − e(A) ≈ −(e(A) − e(B)) ≈ −(D + far)
  have h1 : Req (crossForm5 C k hw0 hk (farCoef C k) (cutAnalysis5 C k f))
      (Rsub (energy5 C k hk (farCoef C k) (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f))) :=
    Req_symm (Req_trans (Rsub_congr hE (Req_refl _)) (Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _))
      (Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _)))))
  refine Req_trans h1 (Req_trans (Rsub_congr hB (Req_refl _)) ?_)
  refine Req_trans (neg_sub_eq_j _ _) (Rneg_congr ?_)
  exact Req_symm hS

theorem neg_zero_j : Req (Rneg zero) zero :=
  Req_trans (Req_symm (Radd_zero _)) (Req_trans (Radd_comm _ _) (Radd_neg zero))

/-- **★ THE JOINT BOUND ON THE RANGE IS THE DEFECT SIGN** at level `k`. -/
theorem jointMatrix_bound_iff_defect (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (f : L2Test) :
    Rle (energy5 C k hk (farCoef C k) (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f))
      ↔ Rnonneg (Radd (atlasDefectGram C k hk f f) (farTailGram C f f k)) := by
  refine Iff.trans (joint_bound_iff C k hw0 hk (farCoef C k) (cutAnalysis5_jointSyn C k hw0 hk f)) ?_
  have hc := crossForm5_range C k hw0 hk f
  constructor
  · intro h
    -- D + far ≈ −cross ≥ 0
    refine Rnonneg_congr (Req_trans (Rneg_congr hc) (Rneg_neg _)) ?_
    exact Rnonneg_of_Rle_zero (Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rneg_congr (Req_refl zero)) neg_zero_j))) (Rle_Rneg h))
  · intro h
    refine Rle_trans (Rle_of_Req hc) ?_
    exact Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg h)) (Rle_of_Req neg_zero_j)

/-- **The exact family**: the joint matrix bounded on the range at every level `k ≥ 1` on the core gives
    `CurrentArchDominatesPrime` (through the scheduled levels and `CoupledForm_eq_lim_defect`). -/
theorem jointMatrix_family_imp_dominance (C : NormCtx) (hw0 : 0 < C.w.num)
    (hbd : ∀ k (hk : 1 ≤ k) (f : ClosedCore C),
      Rle (energy5 C k hk (farCoef C k) (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f.1))) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f.1))) :
    CurrentArchDominatesPrime C :=
  colligation_family_imp_dominance C (fun k hk => atlasMatrixJoint C k hw0 hk) (fun k hk f => atlasMatrixJoint_reproduces C k hw0 hk f) hbd

-- ===========================================================================
-- The asymptotic readback: vanishing slack along the schedule.
-- ===========================================================================

/-- **★ VANISHING SLACK ⟹ DOMINANCE**: if along the schedule `k_j = j + archCNC(C,f,f)` the level-`k_j` defect of
    every core test is bounded below by `−δ_j` with a regular slack `δ_j → 0`, then `CoupledForm(f,f) ≥ 0`, i.e.
    `CurrentArchDominatesPrime`. -/
theorem vanishing_slack_imp_dominance (C : NormCtx) (δ : ClosedCore C → Nat → Real) (hδ : ∀ f, RReg (δ f))
    (hδ0 : ∀ f, Req (Rlim (δ f) (hδ f)) zero)
    (hslack : ∀ (f : ClosedCore C) (j : Nat), Rle (Rneg (δ f j)) (defectSeq C f f j)) :
    CurrentArchDominatesPrime C := by
  intro f
  refine (dominance_iff_coupled_nonneg C f).2 ?_
  refine Rnonneg_congr (Req_symm (CoupledForm_eq_lim_defect C f f)) ?_
  refine Rnonneg_of_Rle_zero ?_
  have hneg : RReg (fun j => Rneg (δ f j)) := RReg_neg _ (hδ f)
  have hlim : Req (Rlim (fun j => Rneg (δ f j)) hneg) zero :=
    Req_trans (Rlim_neg (δ f) (hδ f) hneg) (Req_trans (Rneg_congr (hδ0 f))
      (Req_trans (Req_symm (Radd_zero _)) (Req_trans (Radd_comm _ _) (Radd_neg zero))))
  exact Rle_trans (Rle_of_Req (Req_symm hlim)) (Rlim_le_Rlim hneg (defectSeq_RReg C f f) (fun j => hslack f j))

/-- `(1+ε)² = 1 + (2ε + ε²)`. -/
theorem one_add_sq_expand_j (ε : Real) :
    Req (Rmul (Radd one ε) (Radd one ε)) (Radd one (Radd (Rmul cTwo ε) (Rmul ε ε))) := by
  refine Req_trans (Rmul_distrib_right _ _ _) ?_
  refine Req_trans (Radd_congr (Rone_mul _) (Rmul_distrib _ _ _)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Rmul_one _) (Req_refl _))) ?_
  -- (1 + ε) + (ε + ε·ε) ≈ 1 + ((ε + ε) + ε·ε) ≈ 1 + (2ε + ε²)
  refine Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl _) ?_)
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Radd_congr (Req_symm (cTwo_mul ε)) (Req_refl _))

/-- `E − (1+ε)²·E = −((2ε + ε²)·E)`. -/
theorem one_add_sq_slack (ε E : Real) :
    Req (Rsub E (Rmul (Rmul (Radd one ε) (Radd one ε)) E)) (Rneg (Rmul (Radd (Rmul cTwo ε) (Rmul ε ε)) E)) := by
  refine Req_trans (Rsub_congr (Req_refl _) (Rmul_congr (one_add_sq_expand_j ε) (Req_refl _))) ?_
  refine Req_trans (Rsub_congr (Req_refl _) (Req_trans (Rmul_distrib_right _ _ _) (Radd_congr (Rone_mul _) (Req_refl _)))) ?_
  -- E + −(E + T) ≈ −T
  refine Req_trans (Radd_congr (Req_refl _) (Rneg_Radd _ _)) ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  exact Req_trans (Radd_congr (Radd_neg _) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

/-- **The pointwise slack of a `(1+ε)²`-bound with bounded analysis**: at level `k`, if
    `energy5(atlasMatrixJoint (A_k f)) ≤ (1+ε)²·energy5(A_k f)`, `ε ≥ 0` and `energy5(A_k f) ≤ E`, then
    `D_k(f,f) + far_k(f,f) ≥ −((2ε + ε²)·E)`. -/
theorem slack_of_eps_bound (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (f : L2Test) (ε E : Real) (hε : Rnonneg ε)
    (hbd : Rle (energy5 C k hk (farCoef C k) (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f)))
               (Rmul (Rmul (Radd one ε) (Radd one ε)) (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f))))
    (hE : Rle (energy5 C k hk (farCoef C k) (cutAnalysis5 C k f)) E) :
    Rle (Rneg (Rmul (Radd (Rmul cTwo ε) (Rmul ε ε)) E)) (Radd (atlasDefectGram C k hk f f) (farTailGram C f f k)) := by
  have hS := source5_split_fixed C k hk f f
  have hB := energy5_joint_matrix_eq C k hw0 hk (farCoef C k) f
  have hT : Rnonneg (Radd (Rmul cTwo ε) (Rmul ε ε)) :=
    Rnonneg_Radd (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) hε) (Rnonneg_Rmul hε hε)
  -- D + far = e(A) − e(B) = e(A) − e(TA) ≥ e(A) − (1+ε)²e(A) = −((2ε+ε²)e(A)) ≥ −((2ε+ε²)E)
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hS))
  refine Rle_trans ?_ (Rsub_le_Rsub_of (Rle_refl _) (Rle_trans (Rle_of_Req (Req_symm hB)) hbd))
  refine Rle_trans ?_ (Rle_of_Req (Req_symm (one_add_sq_slack ε _)))
  exact Rle_Rneg (Rmul_le_Rmul_left hT hE)

/-- **★ THE ASYMPTOTIC FAMILY READBACK**: if along the schedule the joint matrix is bounded on the core up to
    slacks `ε_{f,j} ≥ 0` with bounded analyses `energy5(A_{k_j} f) ≤ E_f`, and the induced slack sequences
    `(2ε + ε²)·E_f` are regular and tend to `0`, then `CurrentArchDominatesPrime`.  (No slack, no energy bound
    and no limit is asserted here — they are the hypotheses of the controlled-asymptotic route.) -/
theorem jointMatrix_asymptotic_imp_dominance (C : NormCtx) (hw0 : 0 < C.w.num)
    (ε : ClosedCore C → Nat → Real) (E : ClosedCore C → Real)
    (hε : ∀ f j, Rnonneg (ε f j))
    (hE : ∀ (f : ClosedCore C) (j : Nat),
      Rle (energy5 C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (farCoef C (j + archCNC C f.1 f.1))
            (cutAnalysis5 C (j + archCNC C f.1 f.1) f.1)) (E f))
    (hbd : ∀ (f : ClosedCore C) (j : Nat),
      Rle (energy5 C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (farCoef C (j + archCNC C f.1 f.1))
            (atlasMatrixJoint C (j + archCNC C f.1 f.1) hw0 (archCNC_pos C f.1 f.1 j) (cutAnalysis5 C (j + archCNC C f.1 f.1) f.1)))
          (Rmul (Rmul (Radd one (ε f j)) (Radd one (ε f j)))
            (energy5 C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (farCoef C (j + archCNC C f.1 f.1))
              (cutAnalysis5 C (j + archCNC C f.1 f.1) f.1))))
    (hreg : ∀ f, RReg (fun j => Rmul (Radd (Rmul cTwo (ε f j)) (Rmul (ε f j) (ε f j))) (E f)))
    (hlim : ∀ f, Req (Rlim (fun j => Rmul (Radd (Rmul cTwo (ε f j)) (Rmul (ε f j) (ε f j))) (E f)) (hreg f)) zero) :
    CurrentArchDominatesPrime C :=
  vanishing_slack_imp_dominance C (fun f j => Rmul (Radd (Rmul cTwo (ε f j)) (Rmul (ε f j) (ε f j))) (E f)) hreg hlim
    (fun f j => slack_of_eps_bound C _ hw0 _ f.1 (ε f j) (E f) (hε f j) (hbd f j) (hE f j))

end UOR.Bridge.F1Square.Square
