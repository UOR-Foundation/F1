/-
F1 square — **THE LIMITING ANCHOR KERNEL OF A SOURCE ANCHOR IS MINUS THE COUPLED FORM** (`AtlasAnchorLocalize.lean`,
target side; LOCAL DEVELOPMENT).

The genuine source anchor of a core test `f` is `H_f(t) = V(f,t) = f(1/max(t,a))`
(`sourceAnchor C f = anchorOf (cutAnalysis5 C 1 f)`, level-independent: `sourceAnchor_eq_at_level`).  It is a
SOURCE ANCHOR PROFILE (`SourceAnchorProfile`): scale-constant, vanishing below `a` (`hgh`) AND above `1/b` (`hgl`).
Its autocorrelation data are the canonical two-sided correlation: `N_H = F⁺_{f,f}(1)` (`source_NH_eq_FCanon_one`),
`R_H(x) = F⁺_{f,f}(x)` on the band (`source_RH_eq_FCanon`), so the prime term is `2ΣΛ(n)F⁺_{f,f}(n)`.
With the level-free far mass `fcInf C = farCoef C 1` (`farCoef_eq_fcInf`):

    `anchorKernelLimit C (fcInf C) (sourceAnchor C f) = −CoupledForm(f,f)`   (`anchorKernelLimit_source_eq_neg_CoupledForm`)

for every core test (`w > 0`).  THIS IS A GUARDRAIL, NOT A SIGN: it certifies that the limiting anchor kernel has not
hidden the target — the sign theorem `AK_∞ ≤ 0` on source anchors is literally `CoupledForm(f,f) ≥ 0`, i.e.
`CurrentArchDominatesPrime`.  Nothing about that sign is asserted.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasAnchorAutocorr
import F1Square.Square.AtlasFarCoefStable
import F1Square.Square.AtlasJointReadback

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The level-free far mass and the congruences of the anchor kernel.
-- ===========================================================================

/-- **The level-free far mass** `fc_∞ = ∫_B^∞ K(x)/x dx` (all levels agree, `farCoef_eq_of_pos`). -/
def fcInf (C : NormCtx) : Real := farCoef C 1

theorem farCoef_eq_fcInf (C : NormCtx) (k : Nat) : Req (farCoef C k) (fcInf C) := farCoef_eq_of_pos C k 1

/-- The anchor kernel respects `≈` in the far mass. -/
theorem anchorKernel5_congr_fc (C : NormCtx) (k : Nat) (hk : 1 ≤ k) {fc fc' : Real} (h : CField) (e : Req fc fc') :
    Req (anchorKernel5 C k hk fc h) (anchorKernel5 C k hk fc' h) := by
  unfold anchorKernel5
  refine Radd_congr (Req_refl _) (intT_congr_pt C _ _ one (fun t => ?_))
  exact Rmul_congr (Rmul_congr (Req_refl _) (Rmul_congr (Rmul_congr (Req_refl _) e) (Req_refl _))) (Req_refl _)

theorem shiftUF_congr_al (C : NormCtx) {h h' : CField} (e : ∀ x t, Req (h.F x t) (h'.F x t)) (x t : Real) :
    Req ((shiftUF C h).F x t) ((shiftUF C h').F x t) := by
  rw [shiftUF_F, shiftUF_F]; exact Rmul_congr (Req_refl _) (e _ _)
theorem shiftUnF_congr_al (C : NormCtx) (m : Nat) {h h' : CField} (e : ∀ x t, Req (h.F x t) (h'.F x t)) (x t : Real) :
    Req ((shiftUnF C m h).F x t) ((shiftUnF C m h').F x t) := by
  rw [shiftUnF_F, shiftUnF_F]; exact Rmul_congr (Req_refl _) (e _ _)
theorem ZhF_congr_al (C : NormCtx) (k : Nat) {h h' : CField} (e : ∀ x t, Req (h.F x t) (h'.F x t)) (x t : Real) :
    Req ((ZhF C k h).F x t) ((ZhF C k h').F x t) := by
  rw [ZhF_F, ZhF_F]
  exact Rmul_congr (Req_refl _) (Rsub_congr (shiftUF_congr_al C e x t) (Rmul_congr (Req_refl _) (e _ _)))
theorem WhF_congr_al (C : NormCtx) {h h' : CField} (e : ∀ x t, Req (h.F x t) (h'.F x t)) (x t : Real) :
    Req ((WhF C h).F x t) ((WhF C h').F x t) := by
  rw [WhF_F, WhF_F]; exact Rmul_congr (Req_refl _) (e _ _)

/-- The anchor kernel respects pointwise `≈` of the anchor. -/
theorem anchorKernel5_congr_h (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) {h h' : CField}
    (e : ∀ x t, Req (h.F x t) (h'.F x t)) : Req (anchorKernel5 C k hk fc h) (anchorKernel5 C k hk fc h') := by
  unfold anchorKernel5
  refine Radd_congr (Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_) ?_
  · refine intX_congr_pt C _ _ _ _ _ _ _ (fun x t => ?_)
    rw [mulF_crossF_F, mulF_crossF_F, negF_F_ak, negF_F_ak]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (shiftUF_congr_al C e x t) (Rneg_congr (e _ _))))
  · refine RsumN_congr C.X (fun m _ => intT_congr_pt C _ _ one (fun t => ?_))
    rw [mulF_crossF_F, mulF_crossF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (shiftUnF_congr_al C m e one t) (e _ _)))
  · refine intT_congr_pt C _ _ one (fun t => ?_)
    rw [mulF_crossF_F, mulF_crossF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (e _ _) (e _ _)))
  · refine intX_congr_pt C _ _ _ _ _ _ _ (fun x t => ?_)
    rw [mulF_crossF_F, mulF_crossF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (ZhF_congr_al C k e x t) (WhF_congr_al C e x t)))
  · refine intT_congr_pt C _ _ one (fun t => ?_)
    rw [mulF_crossF_F, mulF_crossF_F, negF_F_ak, negF_F_ak]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (e _ _) (Rneg_congr (e _ _))))

-- ===========================================================================
-- (2) The genuine source anchor and its profile.
-- ===========================================================================

/-- **The source anchor** `H_f = V(f,·)` — the anchor of the level-`1` cut analysis. -/
def sourceAnchor (C : NormCtx) (f : ClosedCore C) : CField := anchorOf (cutAnalysis5 C 1 f.1)

theorem sourceAnchor_F (C : NormCtx) (f : ClosedCore C) (x t : Real) : Req ((sourceAnchor C f).F x t) (Vc C f.1 t) :=
  recVFarF_source C 1 f.1 x t

/-- The anchor of the level-`k` cut analysis is the source anchor (level-independent). -/
theorem sourceAnchor_eq_at_level (C : NormCtx) (f : ClosedCore C) (k : Nat) (x t : Real) :
    Req ((anchorOf (cutAnalysis5 C k f.1)).F x t) ((sourceAnchor C f).F x t) :=
  Req_trans (recVFarF_source C k f.1 x t) (Req_symm (sourceAnchor_F C f x t))

/-- **A source anchor profile**: an anchor profile that also vanishes above `1/b`. -/
structure SourceAnchorProfile (C : NormCtx) (h : CField) extends AnchorProfile C h : Prop where
  zero_high : ∀ x s, Rle (ofQ (Qinv C.b) (Qinv_den_pos C.hbnpos)) s → Req (h.F x s) zero

theorem Qinv_Qinv_al (C : NormCtx) : Qeq (Qinv (Qinv C.b)) C.b := by
  simp only [Qeq, Qinv]
  rw [Int.toNat_of_nonneg (Int.le_of_lt C.hbnpos), Int.toNat_ofNat]

/-- **`V(f,s) = 0` for `s ≥ 1/b`**: `1/max(s,a) ≤ 1/s ≤ b` and `hgl`. -/
theorem Vc_zero_high (C : NormCtx) (f : ClosedCore C) {s : Real} (hs : Rle (ofQ (Qinv C.b) (Qinv_den_pos C.hbnpos)) s) :
    Req (Vc C f.1 s) zero := by
  show Req (f.1.f (clampedInv C.a C.han C.had s)) zero
  refine f.2.hgl _ ?_
  have h1 : Rle (clampedInv C.a C.han C.had s) (ofQ (Qinv (Qinv C.b)) (Qinv_den_pos (Qinv_num_pos C.hbd))) :=
    Rinv_le_ofQ_inv (Qinv_num_pos C.hbd) (Qinv_den_pos C.hbnpos) (qClampQ_witness C.a C.han C.had s)
      (Rle_trans hs (Rle_self_qClampQ C.a C.had s))
  exact Rle_trans h1 (Rle_of_Req (ofQ_congr _ C.hbd (Qinv_Qinv_al C)))

/-- **The source anchor is a source anchor profile.** -/
theorem sourceAnchor_profile (C : NormCtx) (f : ClosedCore C) : SourceAnchorProfile C (sourceAnchor C f) where
  scale_const := fun x x' t => Req_trans (sourceAnchor_F C f x t) (Req_symm (sourceAnchor_F C f x' t))
  zero_low := fun x s hs => Req_trans (sourceAnchor_F C f x s) (Vc_zero_low C f.1 f.2 hs)
  zero_high := fun x s hs => Req_trans (sourceAnchor_F C f x s) (Vc_zero_high C f hs)

-- ===========================================================================
-- (3) The autocorrelation data of a source anchor are the canonical correlation `F⁺_{f,f}`.
-- ===========================================================================

/-- **`N_{H_f} = F⁺_{f,f}(1)`**. -/
theorem source_NH_eq_FCanon_one (C : NormCtx) (f : ClosedCore C) :
    Req (NH C (sourceAnchor C f)) ((FCanon C f.1 f.1).f one) := by
  refine Req_trans ?_ (Req_symm (FCanon_one_eq C f.1 f.1))
  unfold NH intT
  refine intU_smul_free (ofQ C.w C.hw) _ _ _ _ _ _ _ _ (fun y => ?_)
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (sourceAnchor_F C f one _) (sourceAnchor_F C f one _))) ?_
  exact Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) (Rmul_comm _ _))

theorem mul_pull_al (X s Y : Real) : Req (Rmul X (Rmul s Y)) (Rmul s (Rmul X Y)) :=
  Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- **`R_{H_f}(x) = F⁺_{f,f}(x)` on the band `1 ≤ x ≤ B`** (`w > 0`; the shift law at every real scale). -/
theorem source_RH_eq_FCanon (C : NormCtx) (f : ClosedCore C) {x : Real} (hx1 : Rle one x)
    (hxB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Req (RH C (sourceAnchor C f) x) ((FCanon C f.1 f.1).f x) := by
  rw [FCanon_f_eq]
  unfold RH intT
  have hz := cutAnalysis5_fullCoherent C 1 f.1 f.2
  refine Req_trans (intU_congr_unit_free _ _ _ _ (Qmul_den_pos Nat.one_pos (crossL_den C x f.1 f.1))
    (Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num C x f.1 f.1))
    (lip_smul_fl (Rmul (invSq C x) (ofQ C.w C.hw)) (crossL_den C x f.1 f.1) (crossL_num C x f.1 f.1) (crossInt_lip C x f.1 f.1))
    (fc_smul_fl _ (crossInt_fc C x f.1 f.1)) (fun y hy0 hy1 => ?_)) ?_
  · have ht := inWin_of_affine C y hy0 hy1
    have hU : Req ((shiftUF C (sourceAnchor C f)).F x (affineMap C.a C.w C.had C.hw y)) (Uc C x f.1 (affineMap C.a C.w C.had C.hw y)) :=
      Req_trans (Req_symm (recU_eq_shiftU C 1 hz hx1 hxB ht)) (recUF_source_band C 1 f.1 hx1 hxB _)
    -- (w r)·(S·A) ≈ (s·w)·((D·V)·r)  with  S ≈ s·D, A ≈ V
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr hU (sourceAnchor_F C f x _))) ?_
    unfold Uc
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_assoc _ _ _)) ?_
    refine Req_trans (mul_pull_al _ _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) (Rmul_comm _ _)))) ?_
    exact Req_symm (Rmul_assoc _ _ _)
  · refine Req_trans (riemannIntegral_smul_real_fl (Rmul (invSq C x) (ofQ C.w C.hw)) (crossL_den C x f.1 f.1) (crossL_num C x f.1 f.1)
      (crossInt_lip C x f.1 f.1) (crossInt_fc C x f.1 f.1)) ?_
    exact Rmul_assoc _ _ _

/-- **The prime term of a source anchor** `2ΣΛ(n)·F⁺_{f,f}(n)`. -/
theorem source_primeAC_eq_FCanon (C : NormCtx) (f : ClosedCore C) :
    Req (primeAC C (sourceAnchor C f))
        (RsumN (fun m => Rmul (Rmul (ofQ q2 Nat.one_pos) (vonMangoldt (m + 1))) ((FCanon C f.1 f.1).f (upR m))) C.X) :=
  RsumN_congr C.X (fun m hm => Rmul_congr (Req_refl _) (source_RH_eq_FCanon C f (one_le_upR_R m) (upR_le_B_R C m hm)))

-- ===========================================================================
-- (4) THE GUARDRAIL: the limiting anchor kernel of a source anchor is minus the coupled form.
-- ===========================================================================

/-- At every level: `AK_k(fc_∞, H_f) = −(atlasDefectGram_k(f,f) + farTailGram_k(f,f))` (`w > 0`). -/
theorem anchorKernel5_source_level (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (hw0 : 0 < C.w.num) (f : ClosedCore C) :
    Req (anchorKernel5 C k hk (fcInf C) (sourceAnchor C f))
        (Rneg (Radd (atlasDefectGram C k hk f.1 f.1) (farTailGram C f.1 f.1 k))) := by
  refine Req_trans (anchorKernel5_congr_fc C k hk (sourceAnchor C f) (Req_symm (farCoef_eq_fcInf C k))) ?_
  refine Req_trans (anchorKernel5_congr_h C k hk (farCoef C k) (fun x t => Req_symm (sourceAnchor_eq_at_level C f k x t))) ?_
  refine Req_trans (Req_symm (crossForm5_eq_anchorKernel C k hw0 hk (farCoef C k) (cutAnalysis5_fullCoherent C k f.1 f.2))) ?_
  exact crossForm5_range C k hw0 hk f.1

/-- `edgeBound` is antitone in the level. -/
theorem edgeBound_mono (C : NormCtx) (h : CField) {k k' : Nat} (hkk : k ≤ k') : Qle (edgeBound C k' h) (edgeBound C k h) := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  have hp : 2 ^ k ≤ 2 ^ (k + d) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right k d)
  unfold edgeBound dyQ
  simp only [Qle, mul]
  generalize hP : (2 : Nat) ^ k = P at hp ⊢
  generalize hQ : (2 : Nat) ^ (k + d) = Q' at hp ⊢
  push_cast
  have hp' : (P : Int) ≤ (Q' : Int) := Int.ofNat_le.mpr hp
  have hc : (0 : Int) ≤ 2 * (regQ C h).num * ((regQ C h).den : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) (regQ_num C h)) (Int.ofNat_nonneg _)
  have e1 : (1 : Int) * (2 * (regQ C h).num) * ((P : Int) * (1 * ((regQ C h).den : Int)))
      = (2 * (regQ C h).num * ((regQ C h).den : Int)) * (P : Int) := by ring_uor
  have e2 : (1 : Int) * (2 * (regQ C h).num) * ((Q' : Int) * (1 * ((regQ C h).den : Int)))
      = (2 * (regQ C h).num * ((regQ C h).den : Int)) * (Q' : Int) := by ring_uor
  rw [e1, e2]
  exact Int.mul_le_mul_of_nonneg_left hp' hc

theorem le_add_of_sub_le_al {A B e : Real} (h : Rle (Rsub A B) e) : Rle A (Radd B e) := by
  have hA : Req A (Radd B (Rsub A B)) := by
    refine Req_symm (Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc _ _ _) ?_))
    exact Req_trans (Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_neg _))) (Radd_zero _)
  exact Rle_trans (Rle_of_Req hA) (Radd_le_add (Rle_refl _) h)

/-- Two schedules `N(j) = sched j` and `M(j) ≥ j + 1` sample the same limit: eventual closeness. -/
theorem akSeq_close_sched (C : NormCtx) (fc : Real) (h : CField) (hp : AnchorProfile C h) (M : Nat → Nat)
    (hM1 : ∀ j, 1 ≤ M j) (hMj : ∀ j, j + 1 ≤ M j) (t : Nat) :
    ∃ N : Nat, ∀ j, N ≤ j →
      Rle (Rabs (Rsub (akSeq C fc h j) (anchorKernel5 C (M j) (hM1 j) fc h))) (ofQ (⟨1, t + 1⟩ : Q) (Nat.succ_pos t)) := by
  refine ⟨sched C h t, fun j hj => ?_⟩
  have hs : sched C h t ≤ sched C h j := by unfold sched at *; omega
  have hm : sched C h t ≤ M j := Nat.le_trans (by unfold sched at *; omega) (hMj j)
  rcases Nat.le_total (sched C h j) (M j) with hle | hle
  · have hb := anchorKernel5_edge_abs C (k := sched C h j) (k' := M j) (Nat.succ_pos _) (hM1 j) hle fc h hp
    refine Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (Rle_trans hb (Rle_ofQ_ofQ _ _ ?_))
    exact Qle_trans (b := edgeBound C (sched C h t) h) (edgeBound_den C _ h) (edgeBound_mono C h hs) (edgeBound_sched_le C h t)
  · have hb := anchorKernel5_edge_abs C (k := M j) (k' := sched C h j) (hM1 j) (Nat.succ_pos _) hle fc h hp
    refine Rle_trans hb (Rle_ofQ_ofQ _ _ ?_)
    exact Qle_trans (b := edgeBound C (sched C h t) h) (edgeBound_den C _ h) (edgeBound_mono C h hm) (edgeBound_sched_le C h t)

/-- **★ THE GUARDRAIL**: `AK_∞(fc_∞, H_f) = −CoupledForm(f,f)` for every core test (`w > 0`). -/
theorem anchorKernelLimit_source_eq_neg_CoupledForm (C : NormCtx) (hw0 : 0 < C.w.num) (f : ClosedCore C) :
    Req (anchorKernelLimit C (fcInf C) (sourceAnchor C f) (sourceAnchor_profile C f).toAnchorProfile)
        (Rneg (CoupledForm C.geom C.X f.1 f.1 f.2 f.2)) := by
  have hp := (sourceAnchor_profile C f).toAnchorProfile
  have hB : ∀ j, Req (anchorKernel5 C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (fcInf C) (sourceAnchor C f))
      (Rneg (defectSeq C f f j)) := fun j => anchorKernel5_source_level C _ _ hw0 f
  have hNeg : RReg (fun j => Rneg (defectSeq C f f j)) := RReg_neg _ (defectSeq_RReg C f f)
  have hBreg : RReg (fun j => anchorKernel5 C (j + archCNC C f.1 f.1) (archCNC_pos C f.1 f.1 j) (fcInf C) (sourceAnchor C f)) :=
    RReg_congr_fl hB hNeg
  have hclose := akSeq_close_sched C (fcInf C) (sourceAnchor C f) hp (fun j => j + archCNC C f.1 f.1)
    (fun j => archCNC_pos C f.1 f.1 j) (fun j => by show j + 1 ≤ j + archCNC C f.1 f.1; unfold archCNC; omega)
  refine Req_trans (Rlim_eq_of_close (akSeq_reg C (fcInf C) (sourceAnchor C f) hp) hBreg ?_ ?_) ?_
  · intro t
    obtain ⟨N, hN⟩ := hclose t
    exact ⟨N, fun n hn => le_add_of_sub_le_al (Rle_trans (Rle_Rabs_self _) (hN n hn))⟩
  · intro t
    obtain ⟨N, hN⟩ := hclose t
    exact ⟨N, fun n hn => le_add_of_sub_le_al (Rle_trans (Rle_Rabs_self _) (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (hN n hn)))⟩
  refine Req_trans (Rlim_congr _ _ hBreg hNeg hB) ?_
  exact Req_trans (Rlim_neg _ (defectSeq_RReg C f f) hNeg) (Rneg_congr (Req_symm (CoupledForm_eq_lim_defect C f f)))

end UOR.Bridge.F1Square.Square
