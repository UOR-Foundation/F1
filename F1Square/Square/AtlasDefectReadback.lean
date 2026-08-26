/-
F1 square — **THE ALL-PAIRS COMPACT GRAM IDENTITY** (`AtlasDefectReadback.lean`, AC-22 items 3–5, target side).

With the source Gram of `AtlasDefectGram` and the compact coupled form

    `atlasCompactCoupled_k(f,g) = PoleForm − PrimeForm − ArchConstForm − compactTail_k`
    (the only sign-bearing term of the truncated coupled form after the exact tail split),

this module proves, for EVERY pair of core tests and every `k ≥ 1`:

    `poleGram = PoleForm`,  `primeFoldGram = −PrimeForm`,  `constGram = −ArchConstForm`,
    `tailGram_k = −compactTail_k`,
    `atlasDefect_readback :  atlasCompactCoupled_k(f,g) = atlasDefectGram_k(f,g)`,
    `coupled_trunc_split  :  CoupledForm + (ArchTailForm − archTrunc_k) = atlasDefectGram_k + farTailGram_k`,
    `CoupledForm_eq_lim_defect : CoupledForm = lim_k (atlasDefectGram_k + farTailGram_k)`,

and the conditional consequence `atlasDefect_nonneg_imp_dominance`: IF the source Gram were diagonally
nonnegative for every core test and every `k ≥ 1`, THEN `CurrentArchDominatesPrime C` (via
`farTailGram_diag_nonneg` and the limit).  The hypothesis is NOT proved and NOT asserted: it is the crux,
now located exactly at the sign of one explicit finite-index source Gram of the indefinite Atlas pairing.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasDefectGram
import F1Square.Square.AtlasTailSplit
import F1Square.Square.WeilDominance
import F1Square.Square.MellinLinear

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The pole channel reads `PoleForm`.
-- ===========================================================================

/-- On `x ≥ 1` the inner pole integral IS the pole integrand `(F_{f,g}+F_{g,f})(1+1/x)`. -/
theorem poleInner_eq_poleIntegrand (C : NormCtx) (x : Real) (hx : Rle one x) (f g : L2Test) :
    Req (poleInner C x f g) ((poleIntegrand C.geom f g).f x) := by
  refine Req_trans (poleInner_eq C x f g) ?_
  rw [poleIntegrand_f, poleDens_f]
  refine Req_trans ?_ (Rmul_congr (Radd_congr (FCanon_eq_FTestG_ge_one C f g x hx) (FCanon_eq_FTestG_ge_one C g f x hx)) (Req_refl _))
  rw [FCanon_f_eq, FCanon_f_eq]
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_distrib _ _ _)
    (Radd_congr (Req_symm (swap_w_ac _ _ _)) (Req_symm (swap_w_ac _ _ _))))) ?_
  exact Rmul_comm _ _

/-- **★ `poleGram = PoleForm`** on core tests (window `[1,B]`, `F⁺ = F` on `x ≥ 1`). -/
theorem poleGram_eq_PoleForm (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    Req (poleGram C f g) (PoleForm C.geom f g hf hg) := by
  have hP := Req_trans (PoleForm_eq_finite C f g hf hg) (pole_window_congr C f g)
  refine Req_trans ?_ (Req_symm hP)
  have hSd : 0 < (add (poleXL C f g) (poleIntegrand C.geom f g).L).den :=
    add_den_pos (poleXL_den C f g) (poleIntegrand C.geom f g).hLd
  have hSn : 0 ≤ (add (poleXL C f g) (poleIntegrand C.geom f g).L).num :=
    Qadd_num_nonneg_loc (poleXL_num C f g) (poleIntegrand C.geom f g).hLn
  have h1 := lip_weaken_fl (poleXL_den C f g) hSd (Qle_add_right_nonneg (poleIntegrand C.geom f g).hLn) (poleInner_lip C f g)
  have h2 := lip_weaken_fl (poleIntegrand C.geom f g).hLd hSd (Qle_add_left_nonneg (poleXL_num C f g)) (poleIntegrand C.geom f g).hlip
  unfold poleGram
  refine Req_trans (riemannIntegralI_certif_irrel _ _ (poleInner_lip C f g) (poleInner_fc C f g) hSd hSn h1 (poleInner_fc C f g)
    (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))) ?_
  refine Req_trans (riemannIntegralI_congr_unit hSd hSn h1 (poleInner_fc C f g) h2 (poleIntegrand C.geom f g).hfc (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))
    (fun y hy0 _ => poleInner_eq_poleIntegrand C _ (affineMap_ge_a (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C)) y hy0) f g)) ?_
  exact riemannIntegralI_certif_irrel _ _ h2 (poleIntegrand C.geom f g).hfc (poleIntegrand C.geom f g).hLd
    (poleIntegrand C.geom f g).hLn (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))

-- ===========================================================================
-- (2) The constant channel reads `−ArchConstForm`.
-- ===========================================================================

theorem constGram_eq_neg_ArchConstForm (C : NormCtx) (f g : L2Test) :
    Req (constGram C f g) (Rneg (ArchConstForm f g C.a C.han C.had C.w C.hw C.hwn)) :=
  Req_trans (constGram_eq C f g) (Rneg_congr (Req_symm (ArchConstForm_eq_vv C f g)))

-- ===========================================================================
-- (3) The compact tail channel reads `−compactTail`.
-- ===========================================================================

/-- The defect integral respects `≈` in the scale. -/
theorem defectIntegral_congr_x (C : NormCtx) {x x' : Real} (h : Req x x') (f g : L2Test) :
    Req (defectIntegral C x f g) (defectIntegral C x' f g) :=
  param_integral_congr (F := fun x y => defInt C x f g y) (L := fun x => asmL C x f g)
    (fun x => asmL_den C x f g) (fun x => asmL_num C x f g) (fun x => defInt_lip C x f g) (fun x => defInt_fc C x f g)
    x x' (fun _ => Rmul_congr (Radd_congr (Rmul_congr (Dc_congr_x C h f _) (Req_refl _))
      (Rmul_congr (Req_refl _) (Dc_congr_x C h g _))) (Req_refl _))

/-- On `[1, B]` the inner tail integral IS `−N⁺(x)·K_k(x)` (the clamp is inert; `N⁺ = w·defectIntegral`). -/
theorem tailInner_eq_neg_fullInt (C : NormCtx) (k : Nat) (x : Real)
    (h1 : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) x) (hB : Rle x (ofQ (canonB C) (canonB_den C))) (f g : L2Test) :
    Req (tailInner C k x f g) (Rneg ((fullInt C f g k).f x)) := by
  refine Req_trans (tailInner_eq C k x f g) (Rneg_congr ?_)
  have hx : Req (xcl C x) x := xcl_eq_of_band C h1 hB
  rw [fullInt_f]
  -- (w·K(x̄))·D(x̄) ≈ (w·K(x))·D(x) ≈ (w·D(x))·K(x) = N⁺(x)·K(x)
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hfc _ _ hx))
    (defectIntegral_congr_x C hx f g)) ?_
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_))
  exact Rmul_congr (Req_symm (archNumC_endpoint_defect C f g x)) (Req_refl _)

/-- `affineMap a w y ≤ a + w` for `y ≤ 1`. -/
theorem affineMap_le_top (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (y : Real) (hy1 : Rle y one) :
    Rle (affineMap a w ha hw y) (ofQ (add a w) (add_den_pos ha hw)) :=
  Rle_trans (Radd_le_add (Rle_refl _) (Rmul_le_Rmul_left (Rnonneg_ofQ hw hwn) hy1))
    (Rle_of_Req (Req_trans (Radd_congr (Req_refl _) (Rmul_one _)) (Radd_ofQ_ofQ ha hw)))

/-- The top of the compact window is `B`: `(1 + 2^{-k}) + tailGap = B`. -/
theorem tail_window_top (C : NormCtx) (k : Nat) : Qeq (add (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k)) (canonB C) := by
  unfold tailGap Qsub canonB dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  ring_uor

/-- **★ `tailGram_k = −compactTail_k`** (`k ≥ 1`). -/
theorem tailGram_eq_neg_compactTail (C : NormCtx) (f g : L2Test) (k : Nat) (hk : 1 ≤ k) :
    Req (tailGram C k hk f g) (Rneg (compactTail C f g k hk)) := by
  have hSd : 0 < (add (tailXL C k f g) (fullInt C f g k).L).den := add_den_pos (tailXL_den C k f g) (fullInt C f g k).hLd
  have hSn : 0 ≤ (add (tailXL C k f g) (fullInt C f g k).L).num := Qadd_num_nonneg_loc (tailXL_num C k f g) (fullInt C f g k).hLn
  have h1 := lip_weaken_fl (tailXL_den C k f g) hSd (Qle_add_right_nonneg (fullInt C f g k).hLn) (tailInner_lip C k f g)
  have hn := lip_neg_pi (fullInt C f g k).hLd (fullInt C f g k).hlip
  have hnfc : ∀ x y, Req x y → Req (Rneg ((fullInt C f g k).f x)) (Rneg ((fullInt C f g k).f y)) :=
    fun x y h => Rneg_congr ((fullInt C f g k).hfc x y h)
  have h2 := lip_weaken_fl (fullInt C f g k).hLd hSd (Qle_add_left_nonneg (tailXL_num C k f g)) hn
  unfold tailGram compactTail
  refine Req_trans (riemannIntegralI_certif_irrel _ _ (tailInner_lip C k f g) (tailInner_fc C k f g) hSd hSn h1 (tailInner_fc C k f g)
    (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk)) ?_
  refine Req_trans (riemannIntegralI_congr_unit hSd hSn h1 (tailInner_fc C k f g) h2 hnfc (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk) (fun y hy0 hy1 => ?_)) ?_
  · refine tailInner_eq_neg_fullInt C k _ ?_ ?_ f g
    · exact Rle_trans (Rle_ofQ_ofQ (by decide) (add_den_pos Nat.one_pos (dyQ_den k)) (Qle_self_add (Int.le_of_lt (dyQ_num k))))
        (affineMap_ge_a (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk) y hy0)
    · exact Rle_trans (affineMap_le_top _ _ _ _ (tailGap_num_nonneg C k hk) y hy1)
        (Rle_of_Req (ofQ_congr _ _ (tail_window_top C k)))
  refine Req_trans (riemannIntegralI_certif_irrel _ _ h2 hnfc (fullInt C f g k).hLd (fullInt C f g k).hLn hn hnfc (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk)) ?_
  exact riemannIntegralI_neg (fullInt C f g k).hLd (fullInt C f g k).hLn (fullInt C f g k).hlip (fullInt C f g k).hfc hn hnfc (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk)

-- ===========================================================================
-- (4) ★ THE ALL-PAIRS COMPACT GRAM IDENTITY.
-- ===========================================================================

/-- **The compact coupled form** `PoleForm − PrimeForm − ArchConstForm − compactTail_k` — the sign-bearing
    term of the truncated coupled form (`archTrunc_k = compactTail_k − farTailGram_k`). -/
def atlasCompactCoupled (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) (hk : 1 ≤ k) : Real :=
  Rsub (Rsub (Rsub (PoleForm C.geom f g hf hg) (PrimeForm C.X f g C.a C.han C.had C.w C.hw C.hwn))
             (ArchConstForm f g C.a C.han C.had C.w C.hw C.hwn))
       (compactTail C f g k hk)

/-- **★★ `atlasCompactCoupled_k(f,g) = atlasDefectGram_k(f,g)`** for every pair of core tests, `k ≥ 1`. -/
theorem atlasDefect_readback (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : ClosedCore C) :
    Req (atlasCompactCoupled C f.1 g.1 f.2 g.2 k hk) (atlasDefectGram C k hk f.1 g.1) :=
  Req_symm (Radd_congr (Radd_congr (Radd_congr (poleGram_eq_PoleForm C f.1 g.1 f.2 g.2)
    (primeFoldGram_eq_neg_PrimeForm C f g)) (constGram_eq_neg_ArchConstForm C f.1 g.1))
    (tailGram_eq_neg_compactTail C f.1 g.1 k hk))

-- --- real rearrangements ---

theorem sub_sub_comm_dr (P a b : Real) : Req (Rsub (Rsub P a) b) (Rsub (Rsub P b) a) :=
  Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) (Req_symm (Radd_assoc _ _ _)))
theorem sub_add_dr (P a b : Real) : Req (Rsub P (Radd a b)) (Rsub (Rsub P a) b) :=
  Req_trans (Radd_congr (Req_refl _) (Rneg_Radd a b)) (Req_symm (Radd_assoc _ _ _))
theorem sub_add_cancel_dr (X a : Real) : Req (Radd (Rsub X a) a) X :=
  Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Req_trans (Radd_comm _ _) (Radd_neg a))) (Radd_zero _))
theorem add_sub_swap_dr (X a b : Real) : Req (Radd (Rsub X a) b) (Rsub (Radd X b) a) :=
  Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) (Req_symm (Radd_assoc _ _ _)))
theorem sub_sub_sub_dr (Y c f : Real) : Req (Rsub Y (Rsub c f)) (Radd (Rsub Y c) f) :=
  Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd c (Rneg f)) (Radd_congr (Req_refl _) (Rneg_neg f))))
    (Req_symm (Radd_assoc _ _ _))

/-- `((P − (Cst + AT)) − Pr) + (AT − (cT − far)) ≈ (((P − Pr) − Cst) − cT) + far`. -/
theorem coupled_alg_dr (P Cst AT Pr cT far : Real) :
    Req (Radd (Rsub (Rsub P (Radd Cst AT)) Pr) (Rsub AT (Rsub cT far)))
        (Radd (Rsub (Rsub (Rsub P Pr) Cst) cT) far) := by
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Req_trans (Radd_congr (add_sub_swap_dr _ _ _) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Rsub_congr (Radd_congr (sub_add_dr _ _ _) (Req_refl _)) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (Rsub_congr (sub_add_cancel_dr _ _) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (sub_sub_comm_dr _ _ _) (Req_refl _)) ?_
  exact sub_sub_sub_dr _ _ _

/-- **★ THE TRUNCATED COUPLED FORM IS THE SOURCE GRAM PLUS THE POSITIVE FAR CHANNEL**:
    `CoupledForm + (ArchTailForm − archTrunc_k) = atlasDefectGram_k + farTailGram_k` (`k ≥ 1`, core). -/
theorem coupled_trunc_split (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : ClosedCore C) :
    Req (Radd (CoupledForm C.geom C.X f.1 g.1 f.2 g.2)
              (Rsub (ArchTailForm C.geom f.1 g.1 f.2 g.2) (archTrunc C f.1 g.1 f.2 g.2 k)))
        (Radd (atlasDefectGram C k hk f.1 g.1) (farTailGram C f.1 g.1 k)) := by
  refine Req_trans (Radd_congr (Req_refl _) (Rsub_congr (Req_refl _) (archTrunc_split C f.1 g.1 f.2 g.2 k hk))) ?_
  refine Req_trans (coupled_alg_dr _ _ _ _ _ _) ?_
  exact Radd_congr (atlasDefect_readback C k hk f g) (Req_refl _)

-- ===========================================================================
-- (5) The limit and the conditional dominance.
-- ===========================================================================

theorem archCNC_pos (C : NormCtx) (f g : L2Test) (j : Nat) : 1 ≤ j + archCNC C f g := by
  unfold archCNC; omega

/-- The reindexed sequence `atlasDefectGram_{j+c} + farTailGram_{j+c}`. -/
def defectSeq (C : NormCtx) (f g : ClosedCore C) (j : Nat) : Real :=
  Radd (atlasDefectGram C (j + archCNC C f.1 g.1) (archCNC_pos C f.1 g.1 j) f.1 g.1)
       (farTailGram C f.1 g.1 (j + archCNC C f.1 g.1))

/-- The comparison sequence `CoupledForm + (ArchTailForm + (−archTrunc_{j+c}))` is regular. -/
theorem cmpSeq_RReg (C : NormCtx) (f g : ClosedCore C) :
    RReg (fun j => Radd (CoupledForm C.geom C.X f.1 g.1 f.2 g.2)
      (Radd (ArchTailForm C.geom f.1 g.1 f.2 g.2) (Rneg (archTrunc C f.1 g.1 f.2 g.2 (j + archCNC C f.1 g.1))))) :=
  RReg_add_const _ _ (RReg_add_const _ _ (RReg_neg _ (archX_RReg C f.1 g.1 f.2 g.2)))

theorem defectSeq_RReg (C : NormCtx) (f g : ClosedCore C) : RReg (defectSeq C f g) :=
  RReg_congr_fl (fun j => Req_symm (coupled_trunc_split C _ (archCNC_pos C f.1 g.1 j) f g)) (cmpSeq_RReg C f g)

/-- **★ `CoupledForm(f,g) = lim_k (atlasDefectGram_k(f,g) + farTailGram_k(f,g))`** on the core. -/
theorem CoupledForm_eq_lim_defect (C : NormCtx) (f g : ClosedCore C) :
    Req (CoupledForm C.geom C.X f.1 g.1 f.2 g.2) (Rlim (defectSeq C f g) (defectSeq_RReg C f g)) := by
  refine Req_symm ?_
  refine Req_trans (Rlim_congr _ _ (defectSeq_RReg C f g) (cmpSeq_RReg C f g)
    (fun j => Req_symm (coupled_trunc_split C _ (archCNC_pos C f.1 g.1 j) f g))) ?_
  have hN := RReg_neg _ (archX_RReg C f.1 g.1 f.2 g.2)
  refine Req_trans (Rlim_add_const _ _ (RReg_add_const _ _ hN) (cmpSeq_RReg C f g)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Rlim_add_const _ _ hN (RReg_add_const _ _ hN))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Rlim_neg _ (archX_RReg C f.1 g.1 f.2 g.2) hN))) ?_
  have hAT : Req (Rlim (fun j => archTrunc C f.1 g.1 f.2 g.2 (j + archCNC C f.1 g.1)) (archX_RReg C f.1 g.1 f.2 g.2))
      (ArchTailForm C.geom f.1 g.1 f.2 g.2) := ArchIntegral_eq_ArchTailForm C f.1 g.1 f.2 g.2
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Req_refl _) (Rneg_congr hAT))) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _)

/-- **★ THE CRUX, LOCATED**: IF the source Gram were diagonally nonnegative on the core at every
    truncation, THEN `CurrentArchDominatesPrime C`.  The hypothesis is NOT proved and NOT asserted. -/
theorem atlasDefect_nonneg_imp_dominance (C : NormCtx)
    (h : ∀ (f : ClosedCore C) (k : Nat) (hk : 1 ≤ k), Rnonneg (atlasDefectGram C k hk f.1 f.1)) :
    CurrentArchDominatesPrime C := by
  intro f
  refine (dominance_iff_coupled_nonneg C f).2 ?_
  refine Rnonneg_congr (Req_symm (CoupledForm_eq_lim_defect C f f)) ?_
  exact Rnonneg_Rlim_seq _ (fun j => Rnonneg_Radd (h f _ _) (farTailGram_diag_nonneg C f.1 _))

end UOR.Bridge.F1Square.Square
