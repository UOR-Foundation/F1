/-
F1 square — **THE JOINT SIGNED FIVE-CHANNEL MATRIX** (`AtlasJoint5.lean`, target-free).

`atlasMatrixJoint C k : Carrier5 → Carrier5` consumes the anchor and the orbit kernel jointly:

  * THE METRIC-DUAL ANCHOR `anchorDual`: the scale average over `[1+2^{-k}, B]` of the exact recovery
    `4·(q_k·A_pole − A_tail)/P_k` against the metric-dual weight `a_V(x̄)^{-1} = P_k²/(2(q_k²/(1+r) + 1))`
    (the dual constant of the recovery functional in the pole/tail metric with densities `8(1+r)wr`, `8wr`),
    normalized by the test-independent constant `∫ a_V^{-1} ≥ gap_k/(B²·D_max)`; exact on every analysis
    (`anchorDual_source`), every reciprocal certified at an explicit witness;
  * THE FIBER READING `readFiber` of `AtlasOrbitFiber` at every active place `1 ≤ m < X` (the normalized
    `dx/x` integral over the measured fiber `J_{k,n,t}`), and `U_1 = V` at the place `n = 1` (`Λ(1) = 0`);
  * the pole, tail, constant and far cycle coordinates of the source recovered from the ports, with the
    joint anchor as `V` throughout.

`atlasMatrixJoint_reproduces`: on every core test, `atlasMatrixJoint (A_k f)` agrees with `B_k f` on all
five measured supports EXACTLY (no refinement parameter, error identically zero).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitFiber
import F1Square.Square.AtlasAnchorExtract
import F1Square.Square.AtlasFullCoherent5

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The metric-dual weight `a_V(x̄)^{-1} = P_k(x̄)² / (2·(q_k(x̄)²/(1 + r(x̄)) + 1))`.
-- ===========================================================================

/-- `1 + r(x̄) ≥ 1`. -/
def onePlusRF (C : NormCtx) : CField := addF oneConstF (rOneClF C)
/-- `1/(1 + r(x̄))` (exact: `1 + r ≥ 1`). -/
def invOnePlusRF (C : NormCtx) : CField := clampInv (⟨1, 1⟩ : Q) (by decide) (by decide) (onePlusRF C)
/-- `q_k(x̄)²`. -/
def qqF (C : NormCtx) (k : Nat) : CField := mulF (qkClF C k) (qkClF C k)
/-- `D = 2·(q²/(1+r) + 1) ≥ 2`. -/
def dualDenF (C : NormCtx) (k : Nat) : CField :=
  smulQF (⟨2, 1⟩ : Q) Nat.one_pos (by decide) (addF (mulF (qqF C k) (invOnePlusRF C)) oneConstF)
/-- `1/D` (exact: `D ≥ 2`). -/
def invDualDenF (C : NormCtx) (k : Nat) : CField := clampInv (⟨2, 1⟩ : Q) (by decide) Nat.one_pos (dualDenF C k)
/-- **The metric-dual weight** `a_V^{-1} = P²·(1/D)`. -/
def dualWF (C : NormCtx) (k : Nat) : CField := mulF (mulF (PkClF C k) (PkClF C k)) (invDualDenF C k)

theorem dualWF_F (C : NormCtx) (k : Nat) (x t : Real) :
    (dualWF C k).F x t = Rmul (Rmul (Pk k (xcl C x)) (Pk k (xcl C x))) ((invDualDenF C k).F x t) := rfl

/-- The bound `q_M = B·M_K` of `q_k(x̄)` (the field's own bound). -/
def qMQ (C : NormCtx) (k : Nat) : Q := (qkClF C k).M
theorem qMQ_den (C : NormCtx) (k : Nat) : 0 < (qMQ C k).den := (qkClF C k).hMd
theorem qMQ_num (C : NormCtx) (k : Nat) : 0 ≤ (qMQ C k).num := (qkClF C k).hMn
/-- `D_max = 2·(q_M² + 1) ≥ 2`. -/
def dMaxQ (C : NormCtx) (k : Nat) : Q := mul (⟨2, 1⟩ : Q) (add (mul (qMQ C k) (qMQ C k)) (⟨1, 1⟩ : Q))
theorem dMaxQ_den (C : NormCtx) (k : Nat) : 0 < (dMaxQ C k).den :=
  Qmul_den_pos Nat.one_pos (add_den_pos (Qmul_den_pos (qMQ_den C k) (qMQ_den C k)) Nat.one_pos)
theorem Qadd_one_num_pos_j {p : Q} (hp : 0 ≤ p.num) (hpd : 0 < p.den) : 0 < (add p (⟨1, 1⟩ : Q)).num := by
  show 0 < p.num * ((1 : Nat) : Int) + 1 * (p.den : Int)
  have : (0 : Int) < (p.den : Int) := Int.ofNat_pos.mpr hpd
  have h1 : 0 ≤ p.num * ((1 : Nat) : Int) := Int.mul_nonneg hp (Int.ofNat_nonneg _)
  push_cast at h1 ⊢; omega
theorem dMaxQ_num_pos (C : NormCtx) (k : Nat) : 0 < (dMaxQ C k).num :=
  Int.mul_pos (by decide) (Qadd_one_num_pos_j (Qmul_num_nonneg (qMQ_num C k) (qMQ_num C k)) (Qmul_den_pos (qMQ_den C k) (qMQ_den C k)))
theorem two_le_dMaxQ (C : NormCtx) (k : Nat) : Qle (⟨2, 1⟩ : Q) (dMaxQ C k) := by
  refine Qle_of_Rle_ofQ_of Nat.one_pos (dMaxQ_den C k) ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_one _))) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide))
    (Rle_trans (Rle_self_Radd_left (Rnonneg_Rmul (Rnonneg_ofQ (qMQ_den C k) (qMQ_num C k)) (Rnonneg_ofQ (qMQ_den C k) (qMQ_num C k))))
      (Rle_of_Req (Radd_congr (Rmul_ofQ_ofQ _ _) (Req_refl _))))) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) (Radd_ofQ_ofQ _ Nat.one_pos)) (Rmul_ofQ_ofQ Nat.one_pos _))

/-- `D(x̄) ≤ D_max`. -/
theorem dualDenF_le (C : NormCtx) (k : Nat) (x t : Real) : Rle ((dualDenF C k).F x t) (ofQ (dMaxQ C k) (dMaxQ_den C k)) := by
  show Rle (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (Radd (Rmul (Rmul (qk k (xcl C x)) (qk k (xcl C x))) (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) ((onePlusRF C).F x t))) one)) _
  have hq : Rle (Rabs (qk k (xcl C x))) (ofQ (qMQ C k) (qMQ_den C k)) := (qkClF C k).hbd x t
  have hqq : Rle (Rmul (qk k (xcl C x)) (qk k (xcl C x))) (Rmul (ofQ (qMQ C k) (qMQ_den C k)) (ofQ (qMQ C k) (qMQ_den C k))) :=
    Rle_trans (Rle_Rabs_self _) (Rle_trans (Rle_of_Req (Rabs_Rmul _ _))
      (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (qMQ_den C k) (qMQ_num C k)) hq hq))
  have hinv : Rle (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) ((onePlusRF C).F x t)) one :=
    Rle_of_Rabs_le ((recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)).hbd _)
  have hprod : Rle (Rmul (Rmul (qk k (xcl C x)) (qk k (xcl C x))) (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) ((onePlusRF C).F x t)))
      (Rmul (ofQ (qMQ C k) (qMQ_den C k)) (ofQ (qMQ C k) (qMQ_den C k))) :=
    Rle_trans (Rmul_le_Rmul_left (Rnonneg_Rmul_self _) hinv) (Rle_trans (Rle_of_Req (Rmul_one _)) hqq)
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide)) (Radd_le_add hprod (Rle_refl one))) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) (Req_trans (Radd_congr (Rmul_ofQ_ofQ _ _) (Req_refl _)) (Radd_ofQ_ofQ _ Nat.one_pos)))
    (Rmul_ofQ_ofQ Nat.one_pos _))

/-- The explicit positive lower bound `(1/B)²·(1/D_max)` of the dual weight. -/
def dualLoQ (C : NormCtx) (k : Nat) : Q := mul (mul (invBQ C) (invBQ C)) (Qinv (dMaxQ C k))
theorem dualLoQ_den (C : NormCtx) (k : Nat) : 0 < (dualLoQ C k).den :=
  Qmul_den_pos (Qmul_den_pos (invBQ_den C) (invBQ_den C)) (Qinv_den_pos (dMaxQ_num_pos C k))
theorem dualLoQ_num_pos (C : NormCtx) (k : Nat) : 0 < (dualLoQ C k).num :=
  Int.mul_pos (Int.mul_pos (invBQ_num C) (invBQ_num C)) (Qinv_num_pos (dMaxQ_den C k))

/-- **`a_V(x̄)^{-1} ≥ (1/B)²/D_max`** at every scale. -/
theorem dualWF_ge (C : NormCtx) (k : Nat) (x t : Real) : Rle (ofQ (dualLoQ C k) (dualLoQ_den C k)) ((dualWF C k).F x t) := by
  rw [dualWF_F]
  have hP : Rle (ofQ (invBQ C) (invBQ_den C)) (Pk k (xcl C x)) := Pk_ge_invB C k (xcl_zero_le C x) (xcl_le_B C x)
  have hPP : Rle (Rmul (ofQ (invBQ C) (invBQ_den C)) (ofQ (invBQ C) (invBQ_den C))) (Rmul (Pk k (xcl C x)) (Pk k (xcl C x))) :=
    Rmul_le_Rmul_both (Rnonneg_ofQ (invBQ_den C) (Int.le_of_lt (invBQ_num C)))
      (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ (invBQ_den C) (Int.le_of_lt (invBQ_num C)))) hP)) hP hP
  have hinv : Rle (ofQ (Qinv (dMaxQ C k)) (Qinv_den_pos (dMaxQ_num_pos C k))) ((invDualDenF C k).F x t) :=
    ofQ_inv_le_clampedInv (by decide) Nat.one_pos (dMaxQ_den C k) (dMaxQ_num_pos C k) (dualDenF_le C k x t) (two_le_dMaxQ C k)
  refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Rmul_congr (Rmul_ofQ_ofQ (invBQ_den C) (invBQ_den C)) (Req_refl (ofQ (Qinv (dMaxQ C k)) (Qinv_den_pos (dMaxQ_num_pos C k)))))
    (Rmul_ofQ_ofQ (Qmul_den_pos (invBQ_den C) (invBQ_den C)) (Qinv_den_pos (dMaxQ_num_pos C k)))))) ?_
  exact Rmul_le_Rmul_both (Rnonneg_Rmul (Rnonneg_ofQ _ (Int.le_of_lt (invBQ_num C))) (Rnonneg_ofQ _ (Int.le_of_lt (invBQ_num C))))
    (Rnonneg_clampedInv (⟨2, 1⟩ : Q) (by decide) Nat.one_pos _) hPP hinv

-- ===========================================================================
-- (2) The metric-dual anchor.
-- ===========================================================================

/-- The dual denominator `∫_{[1+2^{-k},B]} a_V(x̄)^{-1} dx` (test-independent). -/
def dualDen (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real :=
  anchorXInt (dualWF C k) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) one

def dualDenLo (C : NormCtx) (k : Nat) : Q := mul (tailGap C k) (dualLoQ C k)
theorem dualDenLo_den (C : NormCtx) (k : Nat) : 0 < (dualDenLo C k).den := Qmul_den_pos (tailGap_den C k) (dualLoQ_den C k)
theorem dualDenLo_num_pos (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : 0 < (dualDenLo C k).num :=
  Int.mul_pos (tailGap_num_pos C k hk) (dualLoQ_num_pos C k)

/-- **`dualDen ≥ gap_k·(1/B)²/D_max`**. -/
theorem dualDen_ge (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Rle (ofQ (dualDenLo C k) (dualDenLo_den C k)) (dualDen C k hk) := by
  unfold dualDen anchorXInt
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (tailGap_den C k) (dualLoQ_den C k)))) ?_
  exact riemannIntegralI_ge_const _ _ _ _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
    (fun x _ _ => dualWF_ge C k _ one)

/-- The reciprocal of the dual denominator at the explicit witness `3·(dualDenLo).den`. -/
def dualDenInv (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real :=
  Rinv (dualDen C k hk) (3 * (dualDenLo C k).den)
    (Rlt_Qbound_of_Rle_ofQ (dualDenLo_num_pos C k hk) (dualDenLo_den C k) (dualDen_ge C k hk))
theorem dualDen_mul_inv (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Req (Rmul (dualDen C k hk) (dualDenInv C k hk)) one := Rmul_Rinv_self _

/-- The recovery integrand `a_V^{-1}·(4·(q·A_pole − A_tail)·(1/P))`. -/
def dualNumF (C : NormCtx) (k : Nat) (z : Carrier5) : CField :=
  mulF (dualWF C k) (mulF (smulQF q4 Nat.one_pos (by decide) (numAx C k z)) (PkInvF C k))

/-- **★ THE METRIC-DUAL ANCHOR** `V̂(t) = (∫ a_V^{-1}·4·numAx/P_k dx)/(∫ a_V^{-1} dx)`. -/
def anchorDual (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  smulR (dualDenInv C k hk) (anchorXIntF (dualNumF C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
theorem anchorDual_F (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (anchorDual C k hk z).F x t
      = Rmul (dualDenInv C k hk) (anchorXInt (dualNumF C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t) := rfl

theorem four_quarter_j : Req (Rmul (ofQ q4 Nat.one_pos) cQ) one :=
  Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr (a := mul q4 (⟨1, 4⟩ : Q)) (b := (⟨1, 1⟩ : Q)) (Qmul_den_pos Nat.one_pos (by decide)) Nat.one_pos (by decide))

/-- On the analysis the recovery integrand is `a_V^{-1}·V`. -/
theorem dualNumF_source (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((dualNumF C k (cutAnalysis5 C k f)).F x t) (Rmul ((dualWF C k).F x t) (Vc C f t)) := by
  refine Rmul_congr (Req_refl _) ?_
  show Req (Rmul (Rmul (ofQ q4 Nat.one_pos) ((numAx C k (cutAnalysis5 C k f)).F x t)) ((PkInvF C k).F x t)) (Vc C f t)
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (numAx_source C k f x t)) (PkInvF_F C k x t)) ?_
  rw [densAx_F]
  -- (4·((¼·P)·V))·(1/P) ≈ V
  refine Req_trans (Rmul_congr (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Req_trans (Req_symm (Rmul_assoc _ _ _))
    (Rmul_congr four_quarter_j (Req_refl _))) (Req_refl _))) (Req_refl _)) ?_
  refine Req_trans (Rmul_congr (Rmul_congr (Rone_mul _) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_))
  exact Req_trans (Rmul_congr (Pk_mul_PkInv C k (xcl C x) (xcl_zero_le C x) (xcl_le_B C x)) (Req_refl _)) (Rone_mul _)

/-- **★ THE METRIC-DUAL ANCHOR IS EXACT ON EVERY ANALYSIS**: `anchorDual (A_k f)(t) = V(f,t)` (no window hypothesis). -/
theorem anchorDual_source (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) (x t : Real) :
    Req ((anchorDual C k hk (cutAnalysis5 C k f)).F x t) (Vc C f t) := by
  rw [anchorDual_F]
  have hI : Req (anchorXInt (dualNumF C k (cutAnalysis5 C k f)) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)
      (Rmul (Vc C f t) (dualDen C k hk)) := by
    unfold dualDen anchorXInt
    refine intI_smul_ax (Vc C f t) _ _ _ _ _ _ _ _ ?_ _ _ _ _ _
    intro x
    exact Req_trans (dualNumF_source C k f x t) (Rmul_comm _ _)
  refine Req_trans (Rmul_congr (Req_refl _) hI) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (dualDen_mul_inv C k hk)) (Req_refl _)) (Rone_mul _)

-- ===========================================================================
-- (3) ★ THE JOINT SIGNED MATRIX.
-- ===========================================================================

/-- The prime cycle channel: the fiber reading at the active places `1 ≤ m < X`, `U_1 = V` at `m = 0`, `0` beyond `X`. -/
def matPrimeJ (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) : CField :=
  if hm : m < C.X then
    (if hm1 : 1 ≤ m then bCoefF (readFiber C k m hw0 hk z) (anchorDual C k hk z)
     else bCoefF (anchorDual C k hk z) (anchorDual C k hk z))
  else zeroF

/-- `Z^{rec} = x̄K(x̄)·(U^{rec} − r·V̂)` and `W^{rec} = r·V̂` with the joint anchor. -/
def ZrecJ (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  mulF (mulF (xclF C) (KxF C k)) (subF (recUF C k z) (mulF (rOneClF C) (anchorDual C k hk z)))
def WrecJ (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : CField := mulF (rOneClF C) (anchorDual C k hk z)

/-- **★ THE JOINT ATLAS MATRIX** `CutCarrier → CycleCarrier`. -/
def atlasMatrixJoint (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) : Carrier5 where
  pole := bCoefF (recUF C k z) (negF (anchorDual C k hk z))
  prime := matPrimeJ C k hw0 hk z
  const := bCoefF (anchorDual C k hk z) (anchorDual C k hk z)
  tail := bCoefF (ZrecJ C k hk z) (WrecJ C k hk z)
  far := bCoefF (anchorDual C k hk z) (negF (anchorDual C k hk z))

theorem atlasMatrixJoint_pole_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (atlasMatrixJoint C k hw0 hk z).pole.F x t = bCoefGa one ((recUF C k z).F x t) (Rneg ((anchorDual C k hk z).F x t)) := rfl
theorem atlasMatrixJoint_prime_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) (hm : m < C.X)
    (hm1 : 1 ≤ m) (x t : Real) :
    ((atlasMatrixJoint C k hw0 hk z).prime m).F x t = bCoefGa one ((readFiber C k m hw0 hk z).F x t) ((anchorDual C k hk z).F x t) := by
  show (matPrimeJ C k hw0 hk z m).F x t = _
  unfold matPrimeJ
  rw [dif_pos hm, dif_pos hm1]
  rfl
theorem atlasMatrixJoint_prime0_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (hm : 0 < C.X) (x t : Real) :
    ((atlasMatrixJoint C k hw0 hk z).prime 0).F x t = bCoefGa one ((anchorDual C k hk z).F x t) ((anchorDual C k hk z).F x t) := by
  show (matPrimeJ C k hw0 hk z 0).F x t = _
  unfold matPrimeJ
  rw [dif_pos hm, dif_neg (by omega)]
  rfl
theorem atlasMatrixJoint_const_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (atlasMatrixJoint C k hw0 hk z).const.F x t = bCoefGa one ((anchorDual C k hk z).F x t) ((anchorDual C k hk z).F x t) := rfl
theorem ZrecJ_F (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (ZrecJ C k hk z).F x t
      = Rmul (Rmul (xcl C x) (Kx C k x)) (Rsub ((recUF C k z).F x t) (Rmul (rOne (xcl C x)) ((anchorDual C k hk z).F x t))) := rfl
theorem WrecJ_F (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (WrecJ C k hk z).F x t = Rmul (rOne (xcl C x)) ((anchorDual C k hk z).F x t) := rfl
theorem atlasMatrixJoint_tail_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (atlasMatrixJoint C k hw0 hk z).tail.F x t = bCoefGa one ((ZrecJ C k hk z).F x t) ((WrecJ C k hk z).F x t) := rfl
theorem atlasMatrixJoint_far_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (atlasMatrixJoint C k hw0 hk z).far.F x t = bCoefGa one ((anchorDual C k hk z).F x t) (Rneg ((anchorDual C k hk z).F x t)) := rfl

theorem upR_zero_eq_one : Req (upR 0) one := Req_refl one

/-- **★ EXACT REPRODUCTION**: `atlasMatrixJoint (A_k f) = B_k f` on every measured support (`w > 0`, `k ≥ 1`). -/
theorem atlasMatrixJoint_reproduces (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (f : L2Test) :
    EqOnSupport5 C k (cycleAnalysis5 C k f) (atlasMatrixJoint C k hw0 hk (cutAnalysis5 C k f)) where
  pole := fun x t h1 hB _ => by
    rw [cycleAnalysis5_pole, atlasMatrixJoint_pole_F]
    exact bCoefGa_congr (Req_symm (recUF_source_band C k f h1 hB t)) (Rneg_congr (Req_symm (anchorDual_source C k hk f x t)))
  prime := fun m hm x t ht => by
    rw [cycleAnalysis5_prime]
    by_cases hm1 : 1 ≤ m
    · rw [atlasMatrixJoint_prime_F C k hw0 hk _ m hm hm1]
      exact bCoefGa_congr (Req_symm (readFiber_source C k m hw0 hk hm hm1 f x t ht)) (Req_symm (anchorDual_source C k hk f x t))
    · have hm0 : m = 0 := by omega
      subst hm0
      rw [atlasMatrixJoint_prime0_F C k hw0 hk _ hm]
      refine bCoefGa_congr ?_ (Req_symm (anchorDual_source C k hk f x t))
      exact Req_trans (Uc_congr_x C upR_zero_eq_one f t) (Req_trans (Uc_one_eq_Vc C f t) (Req_symm (anchorDual_source C k hk f x t)))
  const := fun x t _ => by
    rw [cycleAnalysis5_const, atlasMatrixJoint_const_F]
    exact bCoefGa_congr (Req_symm (anchorDual_source C k hk f x t)) (Req_symm (anchorDual_source C k hk f x t))
  tail := fun x t _ _ _ => by
    rw [cycleAnalysis5_tail, atlasMatrixJoint_tail_F, ZrecJ_F, WrecJ_F]
    refine bCoefGa_congr ?_ ?_
    · exact Rmul_congr (Req_refl _) (Rsub_congr (Req_symm (recUF_source C k f x t))
        (Rmul_congr (Req_refl _) (Req_symm (anchorDual_source C k hk f x t))))
    · exact Rmul_congr (Req_refl _) (Req_symm (anchorDual_source C k hk f x t))
  far := fun x t _ => by
    rw [cycleAnalysis5_far, atlasMatrixJoint_far_F]
    exact bCoefGa_congr (Req_symm (anchorDual_source C k hk f x t)) (Rneg_congr (Req_symm (anchorDual_source C k hk f x t)))

-- ===========================================================================
-- (4) The resynthesis law `z = A(source recovered from z)` on the supports.
-- ===========================================================================

/-- The prime cut channel of the resynthesis (mirror of `matPrimeJ` with the cut coordinate). -/
def synPrimeJ (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) : CField :=
  if hm : m < C.X then
    (if hm1 : 1 ≤ m then aCoefF (readFiber C k m hw0 hk z) (anchorDual C k hk z)
     else aCoefF (anchorDual C k hk z) (anchorDual C k hk z))
  else zeroF

/-- **The resynthesis of `z`**: the cut coordinates `A = (u − v)/4` of the source recovered from the ports of `z`. -/
def synthJ (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) : Carrier5 where
  pole := aCoefF (recUF C k z) (negF (anchorDual C k hk z))
  prime := synPrimeJ C k hw0 hk z
  const := aCoefF (anchorDual C k hk z) (anchorDual C k hk z)
  tail := aCoefF (ZrecJ C k hk z) (WrecJ C k hk z)
  far := aCoefF (anchorDual C k hk z) (negF (anchorDual C k hk z))

theorem synthJ_pole_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (synthJ C k hw0 hk z).pole.F x t = aCoefGa one ((recUF C k z).F x t) (Rneg ((anchorDual C k hk z).F x t)) := rfl
theorem synthJ_prime_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) (hm : m < C.X)
    (hm1 : 1 ≤ m) (x t : Real) :
    ((synthJ C k hw0 hk z).prime m).F x t = aCoefGa one ((readFiber C k m hw0 hk z).F x t) ((anchorDual C k hk z).F x t) := by
  show (synPrimeJ C k hw0 hk z m).F x t = _
  unfold synPrimeJ
  rw [dif_pos hm, dif_pos hm1]
  rfl
theorem synthJ_prime0_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (hm : 0 < C.X) (x t : Real) :
    ((synthJ C k hw0 hk z).prime 0).F x t = aCoefGa one ((anchorDual C k hk z).F x t) ((anchorDual C k hk z).F x t) := by
  show (synPrimeJ C k hw0 hk z 0).F x t = _
  unfold synPrimeJ
  rw [dif_pos hm, dif_neg (by omega)]
  rfl
theorem synthJ_const_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (synthJ C k hw0 hk z).const.F x t = aCoefGa one ((anchorDual C k hk z).F x t) ((anchorDual C k hk z).F x t) := rfl
theorem synthJ_tail_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (synthJ C k hw0 hk z).tail.F x t = aCoefGa one ((ZrecJ C k hk z).F x t) ((WrecJ C k hk z).F x t) := rfl
theorem synthJ_far_F (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (synthJ C k hw0 hk z).far.F x t = aCoefGa one ((anchorDual C k hk z).F x t) (Rneg ((anchorDual C k hk z).F x t)) := rfl

/-- **THE RESYNTHESIS LAW** (target-free, intrinsic): `z` agrees on the five measured supports with the cut
    coordinates of the source recovered from its own ports through the joint anchor and the fiber reading. -/
def JointSyn5 (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) : Prop :=
  EqOnSupport5 C k z (synthJ C k hw0 hk z)

/-- **★ EVERY CORE ANALYSIS SATISFIES THE RESYNTHESIS LAW.** -/
theorem cutAnalysis5_jointSyn (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (f : L2Test) :
    JointSyn5 C k hw0 hk (cutAnalysis5 C k f) where
  pole := fun x t h1 hB _ => by
    rw [cutAnalysis5_pole, synthJ_pole_F]
    exact aCoefGa_congr (Req_symm (recUF_source_band C k f h1 hB t)) (Rneg_congr (Req_symm (anchorDual_source C k hk f x t)))
  prime := fun m hm x t ht => by
    rw [cutAnalysis5_prime]
    by_cases hm1 : 1 ≤ m
    · rw [synthJ_prime_F C k hw0 hk _ m hm hm1]
      exact aCoefGa_congr (Req_symm (readFiber_source C k m hw0 hk hm hm1 f x t ht)) (Req_symm (anchorDual_source C k hk f x t))
    · have hm0 : m = 0 := by omega
      subst hm0
      rw [synthJ_prime0_F C k hw0 hk _ hm]
      refine aCoefGa_congr ?_ (Req_symm (anchorDual_source C k hk f x t))
      exact Req_trans (Uc_congr_x C upR_zero_eq_one f t) (Req_trans (Uc_one_eq_Vc C f t) (Req_symm (anchorDual_source C k hk f x t)))
  const := fun x t _ => by
    rw [cutAnalysis5_const, synthJ_const_F]
    exact aCoefGa_congr (Req_symm (anchorDual_source C k hk f x t)) (Req_symm (anchorDual_source C k hk f x t))
  tail := fun x t _ _ _ => by
    rw [cutAnalysis5_tail, synthJ_tail_F, ZrecJ_F, WrecJ_F]
    refine aCoefGa_congr ?_ ?_
    · exact Rmul_congr (Req_refl _) (Rsub_congr (Req_symm (recUF_source C k f x t))
        (Rmul_congr (Req_refl _) (Req_symm (anchorDual_source C k hk f x t))))
    · exact Rmul_congr (Req_refl _) (Req_symm (anchorDual_source C k hk f x t))
  far := fun x t _ => by
    rw [cutAnalysis5_far, synthJ_far_F]
    exact aCoefGa_congr (Req_symm (anchorDual_source C k hk f x t)) (Rneg_congr (Req_symm (anchorDual_source C k hk f x t)))

-- ===========================================================================
-- (5) ★ THE EXPANDED ENERGY IDENTITY: the atomic `u²` terms cancel, `B² − A² = u·v/4`.
-- ===========================================================================

theorem neg_sub_eq_j (a b : Real) : Req (Rsub b a) (Rneg (Rsub a b)) :=
  Req_symm (Req_trans (Rneg_Radd _ _) (Req_trans (Radd_congr (Req_refl _) (Rneg_neg b)) (Radd_comm _ _)))

theorem quarter_four_j : Req (Rmul cQ c4) one := Req_trans (Rmul_comm _ _) four_quarter_j

/-- `½·(u·v + v·u) ≈ u·v`. -/
theorem half_cross_j (u v : Real) : Req (Rmul cH (Radd (Rmul u v) (Rmul v u))) (Rmul u v) := by
  refine Req_trans (Rmul_congr (Req_refl cH) (Radd_congr (Req_refl _) (Rmul_comm v u))) ?_
  refine Req_trans (Rmul_congr (Req_refl cH) (Req_symm (cTwo_mul _))) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr half_two_eq_one_ax (Req_refl _)) (Rone_mul _))

/-- **★ THE POINTWISE CANCELLATION**: `B² − A² = u·v/4` for `A = (u−v)/4`, `B = (u+v)/4` — the atomic `u²`
    (and `v²`) terms cancel identically. -/
theorem cyc_sq_sub_cut_sq (u v : Real) :
    Req (Rsub (Rmul (bCoefGa one u v) (bCoefGa one u v)) (Rmul (aCoefGa one u v) (aCoefGa one u v))) (Rmul cQ (Rmul u v)) := by
  have h1 := negFiber_split archAddr.1 archAddr.2 archAddr_valid.1 archAddr_valid.2 u v u v
  have h2 := negFiber_readback archAddr.1 archAddr.2 archAddr_valid.1 archAddr_valid.2 u v u v
  -- 4AA − 4BB ≈ −(u·v)
  have h3 : Req (Rsub (Rmul c4 (Rmul (aCoefGa one u v) (aCoefGa one u v))) (Rmul c4 (Rmul (bCoefGa one u v) (bCoefGa one u v))))
      (Rneg (Rmul u v)) :=
    Req_trans (Req_symm h1) (Req_trans h2 (Rneg_congr (half_cross_j u v)))
  -- BB − AA ≈ cQ·(4·(BB − AA)) ≈ cQ·(4BB − 4AA) ≈ cQ·(−(4AA − 4BB)) ≈ cQ·(u·v)
  refine Req_trans (Req_symm (Req_trans (Req_symm (Rmul_assoc cQ c4 _)) (Req_trans (Rmul_congr quarter_four_j (Req_refl _)) (Rone_mul _)))) ?_
  refine Rmul_congr (Req_refl cQ) ?_
  refine Req_trans (Rmul_sub_distrib _ _ _) ?_
  refine Req_trans (neg_sub_eq_j _ _) ?_
  exact Req_trans (Rneg_congr h3) (Rneg_neg _)

/-- `(d·B)·B − (d·A)·A ≈ d·(B·B − A·A)`. -/
theorem dens_sq_alg (d A B : Real) : Req (Rsub (Rmul (Rmul d B) B) (Rmul (Rmul d A) A)) (Rmul d (Rsub (Rmul B B) (Rmul A A))) :=
  Req_trans (Rsub_congr (Rmul_assoc _ _ _) (Rmul_assoc _ _ _)) (Req_symm (Rmul_sub_distrib _ _ _))

/-- The pointwise channel identity under a density: `(d·B)·B − (d·A)·A = d·(¼·(u·v))`. -/
theorem channel_cross_pt (d u v : Real) :
    Req (Rsub (Rmul (Rmul d (bCoefGa one u v)) (bCoefGa one u v)) (Rmul (Rmul d (aCoefGa one u v)) (aCoefGa one u v)))
        (Rmul d (Rmul cQ (Rmul u v))) :=
  Req_trans (dens_sq_alg _ _ _) (Rmul_congr (Req_refl d) (cyc_sq_sub_cut_sq u v))

/-- The cross field `¼·u·v` of a channel. -/
def crossF (u v : CField) : CField := smulQF (⟨1, 4⟩ : Q) (by decide) (by decide) (mulF u v)
theorem crossF_F (u v : CField) (x t : Real) : (crossF u v).F x t = Rmul cQ (Rmul (u.F x t) (v.F x t)) := rfl

/-- The prime-channel recovered `U_n` of the joint matrix (fiber reading at `m ≥ 1`, the anchor at `m = 0`). -/
def primeUJ (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) : CField :=
  if hm1 : 1 ≤ m then readFiber C k m hw0 hk z else anchorDual C k hk z

/-- **The cross form** of the joint matrix: the five channel integrals of `density·¼·u·v` in the recovered
    coordinates — pole `−U^{rec}·V̂`, prime `U_n·V̂`, constant `V̂²`, tail `Z^{rec}·W^{rec}`, far `−V̂²`. -/
def crossForm5 (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) (z : Carrier5) : Real :=
  Radd (Radd (Radd (Radd
    (intX C (mulF (poleDens5 C) (crossF (recUF C k z) (negF (anchorDual C k hk z)))) (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C))
    (RsumN (fun m => intT C (mulF (primeDens5 C m) (crossF (primeUJ C k hw0 hk z m) (anchorDual C k hk z))) one) C.X))
    (intT C (mulF (constDens5 C) (crossF (anchorDual C k hk z) (anchorDual C k hk z))) one))
    (intX C (mulF (tailDens5 C) (crossF (ZrecJ C k hk z) (WrecJ C k hk z))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k)
      (tailGap_num_nonneg C k hk)))
    (intT C (mulF (farDens5 C fc) (crossF (anchorDual C k hk z) (negF (anchorDual C k hk z)))) one)

/-- A channel's cycle Gram minus its cut Gram is the cross integral (scale channels). -/
theorem gramX_cross (C : NormCtx) (d u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (intX C (mulF d (crossF u v)) lo w hlo hw hwn)
        (Rsub (gramX C d (bCoefF u v) (bCoefF u v) lo w hlo hw hwn) (gramX C d (aCoefF u v) (aCoefF u v) lo w hlo hw hwn)) := by
  unfold gramX
  refine intX_sub_pt C _ _ _ lo w hlo hw hwn ?_
  intro x t
  exact Req_symm (channel_cross_pt _ _ _)

/-- The same for the Haar channels. -/
theorem gramT_cross (C : NormCtx) (d u v : CField) :
    Req (intT C (mulF d (crossF u v)) one) (Rsub (gramT C d (bCoefF u v) (bCoefF u v)) (gramT C d (aCoefF u v) (aCoefF u v))) := by
  unfold gramT
  refine intT_sub_pt C _ _ _ one ?_
  intro t
  exact Req_symm (channel_cross_pt _ _ _)

/-- The prime channel at place `m < X`: the matrix/synthesis fields are `bCoefF/aCoefF` of `primeUJ` and the anchor. -/
theorem prime_cross_m (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (z : Carrier5) (m : Nat) (hm : m < C.X) :
    Req (intT C (mulF (primeDens5 C m) (crossF (primeUJ C k hw0 hk z m) (anchorDual C k hk z))) one)
        (Rsub (primeG C m ((atlasMatrixJoint C k hw0 hk z).prime m) ((atlasMatrixJoint C k hw0 hk z).prime m))
              (primeG C m ((synthJ C k hw0 hk z).prime m) ((synthJ C k hw0 hk z).prime m))) := by
  unfold primeG
  by_cases hm1 : 1 ≤ m
  · have e1 : (atlasMatrixJoint C k hw0 hk z).prime m = bCoefF (readFiber C k m hw0 hk z) (anchorDual C k hk z) := by
      show matPrimeJ C k hw0 hk z m = _; unfold matPrimeJ; rw [dif_pos hm, dif_pos hm1]
    have e2 : (synthJ C k hw0 hk z).prime m = aCoefF (readFiber C k m hw0 hk z) (anchorDual C k hk z) := by
      show synPrimeJ C k hw0 hk z m = _; unfold synPrimeJ; rw [dif_pos hm, dif_pos hm1]
    have e3 : primeUJ C k hw0 hk z m = readFiber C k m hw0 hk z := by unfold primeUJ; rw [dif_pos hm1]
    rw [e1, e2, e3]
    exact gramT_cross C _ _ _
  · have e1 : (atlasMatrixJoint C k hw0 hk z).prime m = bCoefF (anchorDual C k hk z) (anchorDual C k hk z) := by
      show matPrimeJ C k hw0 hk z m = _; unfold matPrimeJ; rw [dif_pos hm, dif_neg hm1]
    have e2 : (synthJ C k hw0 hk z).prime m = aCoefF (anchorDual C k hk z) (anchorDual C k hk z) := by
      show synPrimeJ C k hw0 hk z m = _; unfold synPrimeJ; rw [dif_pos hm, dif_neg hm1]
    have e3 : primeUJ C k hw0 hk z m = anchorDual C k hk z := by unfold primeUJ; rw [dif_neg hm1]
    rw [e1, e2, e3]
    exact gramT_cross C _ _ _

/-- **★ THE EXPANDED ENERGY IDENTITY**: for EVERY carrier element `z`,
    `energy5(atlasMatrixJoint z) − energy5(synthJ z) = crossForm5 z` — the block expansion with the atomic
    `u²`, `v²` terms cancelled channel by channel (`B² − A² = u·v/4`), before any estimation. -/
theorem energy5_joint_expand (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) (z : Carrier5) :
    Req (Rsub (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk z)) (energy5 C k hk fc (synthJ C k hw0 hk z)))
        (crossForm5 C k hw0 hk fc z) := by
  unfold energy5 inner5 inner4 crossForm5
  refine Req_symm ?_
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (Radd_congr
    (gramX_cross C (poleDens5 C) (recUF C k z) (negF (anchorDual C k hk z)) _ _ _ _ _)
    (Req_trans (RsumN_congr C.X (fun m hm => prime_cross_m C k hw0 hk z m hm)) (RsumN_sub_f2 _ _ C.X)))
    (gramT_cross C (constDens5 C) _ _))
    (gramX_cross C (tailDens5 C) (ZrecJ C k hk z) (WrecJ C k hk z) _ _ _ _ _))
    (gramT_cross C (farDens5 C fc) _ _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (add_sub_add_c5 _ _ _ _) (Req_refl _)) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (add_sub_add_c5 _ _ _ _) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (add_sub_add_c5 _ _ _ _) (Req_refl _)) ?_
  exact add_sub_add_c5 _ _ _ _

-- ===========================================================================
-- (6) What the joint bound is on the resynthesis-coherent carrier.
-- ===========================================================================

/-- On a resynthesis-coherent element the energy is the energy of its resynthesis. -/
theorem energy5_synth_eq (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) {z : Carrier5}
    (hz : JointSyn5 C k hw0 hk z) : Req (energy5 C k hk fc z) (energy5 C k hk fc (synthJ C k hw0 hk z)) :=
  inner5_congr_support C k hk fc hz hz

/-- **★ THE JOINT ENERGY IDENTITY ON THE COHERENT CARRIER**: `energy5(T z) = energy5(z) + crossForm5 z`. -/
theorem energy5_joint_eq (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) {z : Carrier5}
    (hz : JointSyn5 C k hw0 hk z) :
    Req (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk z)) (Radd (energy5 C k hk fc z) (crossForm5 C k hw0 hk fc z)) := by
  have h := energy5_joint_expand C k hw0 hk fc z
  have hs := energy5_synth_eq C k hw0 hk fc hz
  have h1 : Req (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk z))
      (Radd (energy5 C k hk fc (synthJ C k hw0 hk z))
            (Rsub (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk z)) (energy5 C k hk fc (synthJ C k hw0 hk z)))) :=
    Req_symm (Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc _ _ _)
      (Req_trans (Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_neg _))) (Radd_zero _))))
  exact Req_trans h1 (Radd_congr (Req_symm hs) h)

/-- **★ WHAT THE JOINT BOUND IS**: on every resynthesis-coherent `z`, `energy5(T z) ≤ energy5(z)` is EQUIVALENT to
    `crossForm5 z ≤ 0` — the sign of the cross form in the recovered coordinates.  Not asserted in either direction. -/
theorem joint_bound_iff (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) {z : Carrier5}
    (hz : JointSyn5 C k hw0 hk z) :
    Rle (energy5 C k hk fc (atlasMatrixJoint C k hw0 hk z)) (energy5 C k hk fc z) ↔ Rle (crossForm5 C k hw0 hk fc z) zero := by
  have hE := energy5_joint_eq C k hw0 hk fc hz
  constructor
  · intro h
    -- cross ≈ (e + cross) − e ≤ e − e ≈ 0
    have h1 : Req (crossForm5 C k hw0 hk fc z) (Rsub (Radd (energy5 C k hk fc z) (crossForm5 C k hw0 hk fc z)) (energy5 C k hk fc z)) :=
      Req_symm (Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) (Req_trans (Radd_assoc _ _ _)
        (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _))))
    refine Rle_trans (Rle_of_Req h1) ?_
    refine Rle_trans (Rsub_le_Rsub_of (Rle_trans (Rle_of_Req (Req_symm hE)) h) (Rle_refl _)) ?_
    exact Rle_of_Req (Radd_neg _)
  · intro h
    refine Rle_trans (Rle_of_Req hE) ?_
    exact Rle_trans (Radd_le_add (Rle_refl _) h) (Rle_of_Req (Radd_zero _))

end UOR.Bridge.F1Square.Square
