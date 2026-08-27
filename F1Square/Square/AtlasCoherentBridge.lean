/-
F1 square — **THE COHERENCE BRIDGE: `FullSourceCoherent5 ⟹ JointSyn5`** (`AtlasCoherentBridge.lean`, target-free).

The operative hypothesis of the joint energy identity is the resynthesis law `JointSyn5` (agreement of `z` with
the cut coordinates of the source recovered through the joint anchor and the fiber reading).  Here the
eight-law carrier `FullSourceCoherent5` is shown to imply it:

  * `anchorDual_eq_far_of_fullCoherent` — on the Haar window the metric-dual anchor of a fully coherent
    element IS its far anchor `2·A_far` (the dual average of `V^{rec} = V^{far}` on the band);
  * `readHaar_eq_recU_of_fullCoherent`, `readFiber_eq_recU_of_fullCoherent` — both orbit readings of a fully
    coherent element are the recovered `U^{rec}_n(t)` (orbit covariance + weight law along the fiber, the
    ε-argument for the masked average);
  * `recU_one_eq_far_of_fullCoherent` — `U^{rec}_1(t) = V^{far}(t)` (the piecewise law at `x = 1`);
  * `fullCoherent_jointSyn`.

Also: the REAL-SCALE ZERO LAW `Uc_zero_real` (`U_x(f,t) = 0` for `t ≤ a·x`, real `x ≥ 1`, core tests) and the
UPPER MATE FACT `mate_le_aw_of_mu` (`x̄ ≤ μ(t)` ⟹ mate `≤ a + w`): the mask is supported in the full fiber.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasJoint5

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The metric-dual anchor of a fully coherent element is its far anchor.
-- ===========================================================================

theorem one_le_tailLo (k : Nat) : Qle (⟨1, 1⟩ : Q) (tailLo k) := by
  show (1 : Int) * ((1 * 2 ^ k : Nat) : Int) ≤ (1 * ((2 ^ k : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
  push_cast; omega

/-- The recovery integrand is `a_V^{-1}·V^{rec}` (pointwise, any `z`). -/
theorem dualNumF_eq_recVF (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    Req ((dualNumF C k z).F x t) (Rmul ((dualWF C k).F x t) ((recVF C k z).F x t)) :=
  Req_refl _

/-- **★ `anchorDual z = V^{far}(z)` on the Haar window** for a fully coherent `z`. -/
theorem anchorDual_eq_far_of_fullCoherent (C : NormCtx) (k : Nat) (hk : 1 ≤ k) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (x t : Real) (ht : InWin C t) :
    Req ((anchorDual C k hk z).F x t) ((recVFarF z).F x t) := by
  rw [anchorDual_F]
  have hI : Req (anchorXInt (dualNumF C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)
      (Rmul ((recVFarF z).F x t) (dualDen C k hk)) := by
    unfold dualDen anchorXInt
    -- on the window the integrand is a_V^{-1}·V^{far}(x,t)
    have hpt : ∀ s, Rle zero s → Rle s one →
        Req ((dualNumF C k z).F (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) t)
            (Rmul ((recVFarF z).F x t) ((dualWF C k).F (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) one)) := by
      intro s hs0 hs1
      have h1 : Rle one (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) :=
        Rle_trans (Rle_ofQ_ofQ (by decide) (tailLo_den k) (one_le_tailLo k)) (affine_tail_ge_lo C k hk s hs0)
      have hB := affine_tail_le_B C k hk s hs1
      refine Req_trans (dualNumF_eq_recVF C k z _ t) ?_
      refine Req_trans (Rmul_congr (Req_refl _) (hz.anchor _ t h1 hB ht)) ?_
      refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (hz.far_const _ x t))) (Rmul_comm _ _)
    refine Req_trans (intI_congr_unit_free (dualNumF C k z).hLxd (dualNumF C k z).hLxn ((dualNumF C k z).hlipx t)
      (fun _ _ h => (dualNumF C k z).hfcx t h)
      (Qmul_den_pos Nat.one_pos (dualWF C k).hLxd) (Qmul_num_nonneg (xBQ_num_nonneg _) (dualWF C k).hLxn)
      (lip_smul_fl _ (dualWF C k).hLxd (dualWF C k).hLxn ((dualWF C k).hlipx one)) (fc_smul_fl _ (fun _ _ h => (dualWF C k).hfcx one h))
      (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) hpt) ?_
    exact intI_smul_free _ (dualWF C k).hLxd (dualWF C k).hLxn ((dualWF C k).hlipx one) (fun _ _ h => (dualWF C k).hfcx one h)
      _ _ _ _ (fun _ => Req_refl _) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
  refine Req_trans (Rmul_congr (Req_refl _) hI) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (dualDen_mul_inv C k hk)) (Req_refl _)) (Rone_mul _)

-- ===========================================================================
-- (2) The orbit readings of a fully coherent element are the recovered `U_n`.
-- ===========================================================================

theorem one_le_upR_R (m : Nat) : Rle one (upR m) := Rle_ofQ_ofQ (by decide) Nat.one_pos (one_le_upQ m)
theorem upR_le_B_R (C : NormCtx) (m : Nat) (hm : m < C.X) : Rle (upR m) (ofQ (canonB C) (canonB_den C)) :=
  Rle_ofQ_ofQ Nat.one_pos (canonB_den C) (upQ_le_B C m hm)

/-- **The reading integrand of a fully coherent element on the fiber**: for the mate `≥ a`,
    `readF(x,t) = r(x̄)·U^{rec}_n(t)`. -/
theorem readF_of_fullCoherent (C : NormCtx) (k m : Nat) (hm : m < C.X) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (x t : Real) (hmate : Rle (ofQ C.a C.had) (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))) (ht : InWin C t) :
    Req ((readF C k m z).F x t) (Rmul (rOne (xcl C x)) ((recUF C k z).F (upR m) t)) := by
  rw [readF_F]
  have htb : Req (tBand C t) t := tBand_eq_of_win C ht.1 ht.2
  have hs : Req (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))))
      (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) :=
    Rmul_congr (Req_refl _) (Rmul_congr htb (Req_refl _))
  refine Req_trans (Rmul_congr (Req_refl _) ((recUF C k z).hfct _ hs)) ?_
  have hOrb : Req (Rmul (invSq C (upR m)) ((recUF C k z).F (xcl C x) (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))))
      (Rmul (invSq C (xcl C x)) ((recUF C k z).F (upR m) t)) :=
    hz.orbit (xcl C x) (upR m) _ t (xcl_ge_one C x) (xcl_le_B C x) (one_le_upR_R m) (upR_le_B_R C m hm) hmate ht.1
      (orbit_mate_alg m (xcl C x) t)
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (canonC_num C) (canonC_den C) (c_le_xcl C x)
  have hW := invSq_sq_mul_self C (c_le_xcl C x) (xcl_le_B C x) hkx
  exact read_alg _ _ _ _ _ _ hOrb hW

/-- **★ `readHaar z = U^{rec}_n(t)`** on the Haar window for a fully coherent `z` (`m < X`). -/
theorem readHaar_eq_recU_of_fullCoherent (C : NormCtx) (k m : Nat) (hm : m < C.X) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (x t : Real) (ht : InWin C t) :
    Req ((readHaar C k m hm z).F x t) ((recUF C k z).F (upR m) t) := by
  rw [readHaar_F]
  have hpt : ∀ s, Rle zero s → Rle s one →
      Req ((readF C k m z).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) t)
          (Rmul ((recUF C k z).F (upR m) t) ((rOneClF C).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) one)) := by
    intro s hs0 hs1
    have hxn := win_xcl_ge_n C m hm s hs0 hs1
    exact Req_trans (readF_of_fullCoherent C k m hm hz _ t (mate_ge_a C m hxn ht.1) ht) (Rmul_comm _ _)
  refine Req_trans (Rmul_congr (Req_refl _) (xInt_congr_smul _ _ (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m) _ t one hpt)) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (hMassInv_mul C m hm)) (Req_refl _)) (Rone_mul _)

-- --- the ε-argument on the fiber for a fully coherent element ---

/-- The uniform bound of `|readF − U·r|` for a carrier element with `U = U^{rec}_n(t)`. -/
def diffBoundC (C : NormCtx) (k m : Nat) (z : Carrier5) : Q :=
  add (readF C k m z).M (mul (recUF C k z).M (Qinv (⟨1, 1⟩ : Q)))
theorem diffBoundC_den (C : NormCtx) (k m : Nat) (z : Carrier5) : 0 < (diffBoundC C k m z).den :=
  add_den_pos (readF C k m z).hMd (Qmul_den_pos (recUF C k z).hMd (Qinv_den_pos (by decide)))
theorem diffBoundC_num (C : NormCtx) (k m : Nat) (z : Carrier5) : 0 ≤ (diffBoundC C k m z).num :=
  Qadd_num_nonneg_loc (readF C k m z).hMn (Qmul_num_nonneg (recUF C k z).hMn (Int.le_of_lt (Qinv_num_pos (by decide))))

theorem diff_abs_bdC (C : NormCtx) (k m : Nat) (z : Carrier5) (x t : Real) :
    Rle (Rabs (Rsub ((readF C k m z).F x t) (Rmul ((recUF C k z).F (upR m) t) (rOne (xcl C x)))))
        (ofQ (diffBoundC C k m z) (diffBoundC_den C k m z)) := by
  have h2 : Rle (Rabs (Rneg (Rmul ((recUF C k z).F (upR m) t) (rOne (xcl C x)))))
      (ofQ (mul (recUF C k z).M (Qinv (⟨1, 1⟩ : Q))) (Qmul_den_pos (recUF C k z).hMd (Qinv_den_pos (by decide)))) :=
    Rle_trans (Rle_of_Req (Rabs_Rneg _)) (abs_mul_bd _ (Qinv_den_pos (by decide)) (Int.le_of_lt (Qinv_num_pos (by decide)))
      ((recUF C k z).hbd (upR m) t) (rOne_bd (xcl C x)))
  exact Rle_trans (Rabs_Radd _ _) (Rle_trans (Radd_le_add ((readF C k m z).hbd x t) h2) (Rle_of_Req (Radd_ofQ_ofQ _ _)))

def epsKC (C : NormCtx) (k m : Nat) (z : Carrier5) : Q := mul (invEtaQ C) (diffBoundC C k m z)
theorem epsKC_den (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (z : Carrier5) : 0 < (epsKC C k m z).den :=
  Qmul_den_pos (invEtaQ_den C hw0) (diffBoundC_den C k m z)
def epsNC (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (z : Carrier5) : Nat := xBound (ofQ (epsKC C k m z) (epsKC_den C k m hw0 z))

theorem mask_read_le_epsC (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hm : m < C.X) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (x t : Real) (ht : InWin C t) (j : Nat) :
    Rle (Rabs (Rsub (Rmul ((maskF C k m hw0).F x t) ((readF C k m z).F x t))
                    (Rmul ((recUF C k z).F (upR m) t) (Rmul ((maskF C k m hw0).F x t) (rOne (xcl C x))))))
        (ofQ (⟨((epsNC C k m hw0 z : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (mask_diff_alg _ _ _ _))) ?_
  rcases Rle_or_Rle (x := Rsub (xcl C x) ((lamF C k m).F x t)) (q1 := (⟨0, 1⟩ : Q)) (q2 := (⟨1, j + 1⟩ : Q))
      (by decide) (Nat.succ_pos j) (Qlt_zero_inv_succ j) with hB | hA
  · have hmask : Rle ((maskF C k m hw0).F x t)
        (ofQ (mul (invEtaQ C) (⟨1, j + 1⟩ : Q)) (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j))) := by
      refine Rle_trans (maskF_le_ramp1 C k m hw0 x t) ?_
      refine ramp_le_of_le _ (Qmul_num_nonneg (invEtaQ_num C) (show (0 : Int) ≤ 1 by decide)) ?_
      refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) hB) ?_
      exact Rle_of_Req (Rmul_ofQ_ofQ _ _)
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ (diffBoundC_num C k m z))
      (Rabs_le_of_nonneg_le _ (Qmul_num_nonneg (invEtaQ_num C) (show (0 : Int) ≤ 1 by decide)) (maskF_nonneg C k m hw0 x t) hmask)
      (diff_abs_bdC C k m z x t)) ?_
    refine Rle_trans (Rle_of_Req (Req_trans (Rmul_ofQ_ofQ (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j)) (diffBoundC_den C k m z))
      (ofQ_congr (b := mul (epsKC C k m z) (⟨1, j + 1⟩ : Q)) (Qmul_den_pos (Qmul_den_pos (invEtaQ_den C hw0) (Nat.succ_pos j)) (diffBoundC_den C k m z))
        (Qmul_den_pos (epsKC_den C k m hw0 z) (Nat.succ_pos j))
      (by simp only [Qeq, mul, epsKC]; push_cast; ring_uor)))) ?_
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (epsKC_den C k m hw0 z) (Nat.succ_pos j)))) ?_
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ (Nat.succ_pos j) (show (0 : Int) ≤ 1 by decide))
      (Rle_of_Rabs_le (Rabs_le_ofQ_xBound (ofQ (epsKC C k m z) (epsKC_den C k m hw0 z))))) ?_
    refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (Nat.succ_pos j)) (ofQ_congr _ _ ?_))
    show Qeq (mul (⟨((epsNC C k m hw0 z : Nat) : Int), 1⟩ : Q) (⟨1, j + 1⟩ : Q)) (⟨((epsNC C k m hw0 z : Nat) : Int), j + 1⟩ : Q)
    simp only [Qeq, mul]; push_cast; ring_uor
  · have hxl : Rle ((lamF C k m).F x t) (xcl C x) := Rle_of_Rnonneg_Rsub (Rnonneg_of_Rle_zero hA)
    have hR := readF_of_fullCoherent C k m hm hz x t (mate_ge_a_of_lam C k m hm ht.1 hxl) ht
    have h0 : Req (Rmul ((maskF C k m hw0).F x t)
        (Rsub ((readF C k m z).F x t) (Rmul ((recUF C k z).F (upR m) t) (rOne (xcl C x))))) zero :=
      Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rsub_congr hR (Rmul_comm _ _)) (Radd_neg _))) (Rmul_zero _)
    refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr h0) Rabs_zero)) ?_
    exact Rle_zero_of_Rnonneg (Rnonneg_ofQ (Nat.succ_pos j) (Int.ofNat_nonneg _))

theorem mask_read_eqC (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hm : m < C.X) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (x t : Real) (ht : InWin C t) :
    Req (Rmul ((maskF C k m hw0).F x t) ((readF C k m z).F x t))
        (Rmul ((recUF C k z).F (upR m) t) (Rmul ((maskF C k m hw0).F x t) (rOne (xcl C x)))) := by
  refine Rle_antisymm ?_ ?_
  · exact Rle_of_Rsub_le_eps (C := epsNC C k m hw0 z) (fun j => Rle_trans (Rle_Rabs_self _) (mask_read_le_epsC C k m hw0 hm hz x t ht j))
  · exact Rle_of_Rsub_le_eps (C := epsNC C k m hw0 z) (fun j => Rle_trans (Rle_Rabs_self _)
      (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (mask_read_le_epsC C k m hw0 hm hz x t ht j)))

/-- **★ `readFiber z = U^{rec}_n(t)`** on the Haar window for a fully coherent `z` (`1 ≤ m < X`). -/
theorem readFiber_eq_recU_of_fullCoherent (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (hm : m < C.X) (hm1 : 1 ≤ m)
    {z : Carrier5} (hz : FullSourceCoherent5 C k z) (x t : Real) (ht : InWin C t) :
    Req ((readFiber C k m hw0 hk z).F x t) ((recUF C k z).F (upR m) t) := by
  rw [readFiber_F]
  have hN : Req ((numF C k m hw0 hk z).F x t) (Rmul ((recUF C k z).F (upR m) t) ((massF C k m hw0 hk).F x t)) := by
    rw [numF_F, massF_F]
    exact xInt_congr_smul _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) _ t t
      (fun s _ _ => mask_read_eqC C k m hw0 hm hz _ t ht)
  refine Req_trans (Rmul_congr (Req_refl _) hN) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) (massInvF_mul C k m hw0 hk hm hm1 x t ht)) (Req_refl _)) (Rone_mul _)

-- ===========================================================================
-- (3) `U^{rec}_1 = V^{far}` (the piecewise law at `x = 1`), and the bridge.
-- ===========================================================================

/-- `U^{rec}(1, t) = V^{far}(1, t)` for `t ≥ a`, from the piecewise law at `x = 1`. -/
theorem recU_one_eq_far_of_fullCoherent (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (t : Real) (hta : Rle (ofQ C.a C.had) t) :
    Req ((recUF C k z).F one t) ((recVFarF z).F one t) := by
  obtain ⟨k1, hk1⟩ := Pos_of_Rle_ofQ (by decide) (by decide) (Rle_refl one)
  have hax : Rle (Rmul (ofQ C.a C.had) one) t := Rle_trans (Rle_of_Req (Rmul_one _)) hta
  refine Req_trans (hz.shift one t (Rle_refl one) (Rle_trans (Rle_ofQ_ofQ (by decide) (canonB_den C) (canonB_one C)) (Rle_refl _)) k1 hk1 hax) ?_
  have hinv1 : Req (Rinv one k1 hk1) one := Req_trans (Req_symm (Rone_mul _)) (Rmul_Rinv_self hk1)
  refine Req_trans (Rmul_congr (invSq_one C) ((recVFarF z).hfct one (Req_trans (Rmul_congr (Req_refl t) hinv1) (Rmul_one t)))) ?_
  exact Rone_mul _

/-- **★ THE BRIDGE**: every fully source-coherent element satisfies the resynthesis law of the joint matrix. -/
theorem fullCoherent_jointSyn (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) {z : Carrier5}
    (hz : FullSourceCoherent5 C k z) : JointSyn5 C k hw0 hk z where
  pole := fun x t h1 hB ht => by
    rw [synthJ_pole_F]
    exact Req_trans (hz.pole_syn x t h1 hB ht)
      (aCoefGa_congr (Req_refl _) (Rneg_congr (Req_symm (anchorDual_eq_far_of_fullCoherent C k hk hz x t ht))))
  prime := fun m hm x t ht => by
    by_cases hm1 : 1 ≤ m
    · rw [synthJ_prime_F C k hw0 hk z m hm hm1]
      refine Req_trans (hz.prime_syn m hm x t ht) (aCoefGa_congr ?_ (Req_symm (anchorDual_eq_far_of_fullCoherent C k hk hz x t ht)))
      exact Req_trans (readHaar_eq_recU_of_fullCoherent C k m hm hz x t ht)
        (Req_symm (readFiber_eq_recU_of_fullCoherent C k m hw0 hk hm hm1 hz x t ht))
    · have hm0 : m = 0 := by omega
      subst hm0
      rw [synthJ_prime0_F C k hw0 hk z hm]
      refine Req_trans (hz.prime_syn 0 hm x t ht) (aCoefGa_congr ?_ (Req_symm (anchorDual_eq_far_of_fullCoherent C k hk hz x t ht)))
      refine Req_trans (readHaar_eq_recU_of_fullCoherent C k 0 hm hz x t ht) ?_
      refine Req_trans ((recUF C k z).hfcx t upR_zero_eq_one) ?_
      refine Req_trans (recU_one_eq_far_of_fullCoherent C k hz t ht.1) ?_
      exact Req_trans (Rmul_congr (Req_refl _) (hz.far_const one x t)) (Req_symm (anchorDual_eq_far_of_fullCoherent C k hk hz x t ht))
  const := fun x t ht => by
    rw [synthJ_const_F]
    exact Req_trans (hz.const_zero x t ht) (Req_symm (negFiber_VV_cut_zero _))
  tail := fun x t hlo hB ht => by
    rw [synthJ_tail_F, ZrecJ_F, WrecJ_F]
    have h1 : Rle one x := Rle_trans (Rle_ofQ_ofQ (by decide) (tailLo_den k) (one_le_tailLo k)) hlo
    have hV : Req ((recVF C k z).F x t) ((anchorDual C k hk z).F x t) :=
      Req_trans (hz.anchor x t h1 hB ht) (Req_symm (anchorDual_eq_far_of_fullCoherent C k hk hz x t ht))
    refine Req_trans (hz.tail_syn x t hlo hB ht) ?_
    rw [ZrecF_F, WrecF_F]
    exact aCoefGa_congr (Rmul_congr (Req_refl _) (Rsub_congr (Req_refl _) (Rmul_congr (Req_refl _) hV))) (Rmul_congr (Req_refl _) hV)
  far := fun x t ht => by
    rw [synthJ_far_F]
    -- z.far = ½·(2·z.far) = aCoefGa one V̂ (−V̂)
    have hV : Req ((anchorDual C k hk z).F x t) (Rmul cTwo (z.far.F x t)) := anchorDual_eq_far_of_fullCoherent C k hk hz x t ht
    refine Req_trans ?_ (Req_symm (posFiber_VV_cut _))
    refine Req_trans ?_ (Rmul_congr (Req_refl cH) (Req_symm hV))
    exact Req_symm (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr half_two_eq_one_ax (Req_refl _)) (Rone_mul _)))

-- ===========================================================================
-- (4) The real-scale zero law and the upper mate fact.
-- ===========================================================================

/-- `lo ≤ v ⟹ band_{[lo,hi]}(v) ≤ v`. -/
theorem band_le_self_of_ge (lo hi : Q) (hlo : 0 < lo.den) (hhi : 0 < hi.den) {v : Real} (hv : Rle (ofQ lo hlo) v) :
    Rle (qBandQ lo hi hlo hhi v) v := by
  intro n
  have h1 : Qle lo (add (v.seq n) ⟨2, n + 1⟩) := hv n
  show Qle (Qmin (Qmax (v.seq n) lo) hi) (add (v.seq n) ⟨2, n + 1⟩)
  refine Qle_trans (Qmax_den_pos (v.den_pos n) hlo) (Qmin_le_left _ _) ?_
  exact Qmax_le (Qle_self_add (two_num_nonneg_of n)) h1

/-- **The upper mate fact**: `x̄ ≤ μ(t)` on an active row ⟹ the mate `x̄·t/n ≤ a + w`: the mask is supported in the
    full fiber `J_{k,n,t}` (both edges). -/
theorem mate_le_aw_of_mu (C : NormCtx) (k m : Nat) (hm1 : 1 ≤ m) {x t : Real} (ht : InWin C t)
    (hxu : Rle (xcl C x) ((muF C k m).F x t)) :
    Rle (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) (ofQ (add C.a C.w) (awQ_den C)) := by
  have hnn : Rnonneg (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))) :=
    Rnonneg_Rmul (Rnonneg_of_ge_a C ht.1) (Rnonneg_ofQ (Nat.succ_pos m) (invNQ_num m))
  have hmu : Rle ((muF C k m).F x t) (Rmul (ofQ (awnQ C m) (awnQ_den C m)) (rEv C t)) := by
    rw [muF_F]
    exact band_le_self_of_ge _ _ _ _ (Rle_trans (Rle_ofQ_ofQ (tailLo_den k) Nat.one_pos (tailLo_le_upQ k m hm1)) (awn_r_ge_n C m ht.2))
  refine Rle_trans (Rmul_le_Rmul_right hnn (Rle_trans hxu hmu)) (Rle_of_Req ?_)
  have e1 : Req (ofQ (awnQ C m) (awnQ_den C m)) (Rmul (ofQ (add C.a C.w) (awQ_den C)) (upR m)) :=
    Req_symm (Rmul_ofQ_ofQ (awQ_den C) Nat.one_pos)
  have e2 : Req (Rmul (Rmul (Rmul (ofQ (add C.a C.w) (awQ_den C)) (upR m)) (rEv C t)) (Rmul (ofQ (invNQ m) (Nat.succ_pos m)) t))
      (Rmul (ofQ (add C.a C.w) (awQ_den C)) (Rmul (Rmul (upR m) (ofQ (invNQ m) (Nat.succ_pos m))) (Rmul (rEv C t) t))) :=
    Req_trans (Rmul_congr (Rmul_assoc _ _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) (mul4_swap_ch _ _ _ _)))
  refine Req_trans (Rmul_congr (Rmul_congr e1 (Req_refl _)) (Rmul_comm _ _)) (Req_trans e2 ?_)
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_trans (Rmul_comm _ _) (ofQ_recip_one m)) (rEv_mul_t C ht.1))) ?_
  exact Req_trans (Rmul_congr (Req_refl _) (Rmul_one _)) (Rmul_one _)

end UOR.Bridge.F1Square.Square
