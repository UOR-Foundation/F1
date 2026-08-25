/-
F1 square — **THE INDEPENDENTLY DEFINED MELLIN POLE TERM and its low/high folding**
(`WeilMellinPole.lean`) — bridge item 3.

The pole term of the Weil functional at the two poles of ζ is the pair of full Mellin integrals
`∫₀^∞ F⁺(x) dx + ∫₀^∞ F⁺(x) dx/x = ∫₀^∞ F⁺(x)(1 + 1/x) dx` of the two-sided normalized correlation
`F⁺ = FCanon C f g`.  Over the canonical band `F⁺` is supported in `[1/B, B]` (`B = X+1`; below `1/B`
by `canonC_le_ba`, above `B` by the high support), so the full integral is EXACTLY the low window
`[1/B, 1]` plus the high window `[1, B]`:

    `MellinPole C f g = ∫_{1/B}^{1} F⁺(x)(1+1/x) dx + ∫_{1}^{B} F⁺(x)(1+1/x) dx`.

THE FOLDING (`MellinPole_eq_PoleForm`): the low window is carried to `[1,B]` by the inversion theorem
`riemannIntegralI_inversion` (x = 1/y), where the transpose law `FCanon_recip_real`
(`y⁻¹F⁺_{f,g}(1/y) = F⁺_{g,f}(y)`) turns `F⁺_{f,g}(1/y)(1+y)/y²` into `F⁺_{g,f}(y)(1+1/y)`; the sum
`(F⁺_{f,g} + F⁺_{g,f})(1+1/x)` on `[1,B]` is the `PoleForm` integrand (the one-sided `FTest` agrees
with `F⁺` on `[1,B]`, `FTwo_eq_FTest_high`), and the improper `PoleForm` collapses to the finite
window `[1, B]` (`improperIntegral1_eq_finite`).  Nothing is copied: `MellinPole` is defined without
reference to `PoleForm`; the identity is PROVED.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.ImproperFinite

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The canonical band facts and the two integrands.
-- ===========================================================================

theorem canonB_gt_one (C : NormCtx) : Qlt (⟨1, 1⟩ : Q) (canonB C) := by
  have h := C.hX
  show (1 : Int) * ((1 : Nat) : Int) < ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
  push_cast; omega

/-- The low-side density `1 + 1/max(x, 1/B)` (exactly `1 + 1/x` on `[1/B, 1]`). -/
def lowDens (C : NormCtx) : L2Test :=
  L2Test.add oneTest (recipTest (canonC C) (canonC_num C) (canonC_den C))

/-- The low integrand `F⁺_{f,g}(x)·(1 + 1/x)` on `[1/B, 1]`. -/
def lowInt (C : NormCtx) (f g : L2Test) : L2Test := productTest (FCanon C f g) (lowDens C)

/-- The high integrand `F⁺_{f,g}(x)·(1 + 1/x)` on `[1, B]` (`poleDens = 1 + 1/max(x,1)`). -/
def highInt (C : NormCtx) (f g : L2Test) : L2Test := productTest (FCanon C f g) poleDens

theorem lowInt_f (C : NormCtx) (f g : L2Test) (x : Real) :
    (lowInt C f g).f x
      = Rmul ((FCanon C f g).f x)
          (Radd one (clampedInv (canonC C) (canonC_num C) (canonC_den C) x)) := rfl

theorem highInt_f (C : NormCtx) (f g : L2Test) (x : Real) :
    (highInt C f g).f x = Rmul ((FCanon C f g).f x) (poleDens.f x) := rfl

theorem poleDens_f (x : Real) :
    poleDens.f x = Radd one (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) := by
  unfold poleDens; rfl

-- ===========================================================================
-- (2) THE TWO FULL MELLIN INTEGRALS (low window + high window) and the support facts.
-- ===========================================================================

/-- `∫_{1/B}^{1} F⁺(x)(1+1/x) dx`. -/
def MellinLow (C : NormCtx) (f g : L2Test) : Real :=
  riemannIntegralI (lowInt C f g).hLd (lowInt C f g).hLn (lowInt C f g).hlip (lowInt C f g).hfc
    (canonC C) (Qsub (⟨1, 1⟩ : Q) (canonC C)) (canonC_den C)
    (Qsub_den_pos Nat.one_pos (canonC_den C)) (Qsub_num_nonneg (canonC_le_one C))

/-- `∫_{1}^{B} F⁺(x)(1+1/x) dx`. -/
def MellinHigh (C : NormCtx) (f g : L2Test) : Real :=
  riemannIntegralI (highInt C f g).hLd (highInt C f g).hLn (highInt C f g).hlip (highInt C f g).hfc
    (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos
    (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))

/-- **THE INDEPENDENT MELLIN POLE TERM** `∫₀^∞ F⁺_{f,g}(x)(1 + 1/x) dx`, realized as the low window
    `[1/B,1]` plus the high window `[1,B]` (the integrand vanishes outside: `FCanon_low_vanish`,
    `FCanon_high_vanish`).  Defined WITHOUT reference to `PoleForm`. -/
def MellinPole (C : NormCtx) (f g : L2Test) : Real :=
  Radd (MellinLow C f g) (MellinHigh C f g)

/-- `F⁺_{f,g}` vanishes on `[0, 1/B]` (the canonical lower band edge sits below `b·a`). -/
theorem FCanon_low_vanish (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (x : Real) (hx0 : Rle zero x) (hxc : Rle x (ofQ (canonC C) (canonC_den C))) :
    Req ((FCanon C f g).f x) zero := by
  refine FTwo_low_vanish (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
    (canonB_one C) (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
    f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos hf.hgl x hx0 ?_ ?_
  · exact Rle_trans hxc (Rle_ofQ_ofQ _ _ (Qle_trans (by decide) (canonC_le_one C) C.hS1))
  · exact Rle_trans hxc (Rle_ofQ_ofQ _ _ (canonC_le_ba C))

/-- `F⁺_{f,g}` vanishes on `[B, ∞)`. -/
theorem FCanon_high_vanish (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (x : Real) (hx : Rle (ofQ (canonB C) (canonB_den C)) x) :
    Req ((FCanon C f g).f x) zero := by
  show Req (Rmul (invSqrtTwoF (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
      (canonB_one C) (canonC_le_B C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C) x)
      ((HcrossTest f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn).f x)) zero
  refine Req_trans (Rmul_congr (Req_refl _) (HcrossTest_high_vanish f g C.S C.hSd C.hSn C.a C.han C.had
    C.w C.hw C.hwn (canonB C) (canonB_den C) ?_ C.hTS C.hband_hi hf.hgh x hx)) (Rmul_zero _)
  exact Qle_trans (by decide) (by decide : Qle (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (canonB_one C)

-- ===========================================================================
-- (3) The real reciprocal identities on `[1, B]`.
-- ===========================================================================

/-- `1/B ≤ 1/y` for `1 ≤ y ≤ B`. -/
theorem Rinv_ge_ofQ_inv {B : Q} (hBd : 0 < B.den) (hBn : 0 < B.num) {y : Real} {ky : Nat}
    (hky : Qlt (Qbound ky) (y.seq ky)) (hyB : Rle y (ofQ B hBd)) :
    Rle (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rinv y ky hky) := by
  have hyr : Req (Rmul y (Rinv y ky hky)) one := Rmul_Rinv_self hky
  have hnnx : Rnonneg (Rinv y ky hky) := Rnonneg_Rinv y ky hky
  have hnnQ : Rnonneg (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
    Rnonneg_ofQ (Qinv_den_pos hBn) (Int.le_of_lt (Qinv_num_pos hBd))
  have hQ : Qeq (mul (Qinv B) B) (⟨1, 1⟩ : Q) :=
    Qeq_trans (Qmul_den_pos hBd (Qinv_den_pos hBn)) (Qmul_comm (Qinv B) B) (Qmul_Qinv hBn)
  have hL : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul y (Rinv y ky hky)))
      (ofQ (Qinv B) (Qinv_den_pos hBn)) := Req_trans (Rmul_congr (Req_refl _) hyr) (Rmul_one _)
  have hstep : Rle (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul y (Rinv y ky hky)))
      (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (Rinv y ky hky))) :=
    Rmul_le_Rmul_left hnnQ (Rmul_le_Rmul_right hnnx hyB)
  have hR : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (Rinv y ky hky)))
      (Rinv y ky hky) := by
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hBn) hBd)
      (ofQ_congr (Qmul_den_pos (Qinv_den_pos hBn) hBd) (by decide) hQ)) (Req_refl _)) ?_
    exact Rone_mul _
  exact Rle_trans (Rle_of_Req (Req_symm hL)) (Rle_trans hstep (Rle_of_Req hR))

/-- `1/(1/y) = y`. -/
theorem Rinv_Rinv_eq {y : Real} {ky : Nat} (hky : Qlt (Qbound ky) (y.seq ky)) {ki : Nat}
    (hki : Qlt (Qbound ki) ((Rinv y ky hky).seq ki)) :
    Req (Rinv (Rinv y ky hky) ki hki) y := by
  have h1 : Req (Rmul (Rinv y ky hky) (Rinv (Rinv y ky hky) ki hki)) one := Rmul_Rinv_self hki
  refine Req_symm ?_
  refine Req_trans (Req_symm (Rmul_one y)) ?_
  refine Req_trans (Rmul_congr (Req_refl y) (Req_symm h1)) ?_
  refine Req_trans (Req_symm (Rmul_assoc y (Rinv y ky hky) (Rinv (Rinv y ky hky) ki hki))) ?_
  refine Req_trans (Rmul_congr (Rmul_Rinv_self hky) (Req_refl _)) ?_
  exact Rone_mul _

/-- **`clampedInv (1/B) (clampedInv 1 y) = y`** for real `1 ≤ y ≤ B` (both clamps inert). -/
theorem clampedInv_recip_eq (C : NormCtx) (y : Real) (hy1 : Rle one y)
    (hyB : Rle y (ofQ (canonB C) (canonB_den C))) :
    Req (clampedInv (canonC C) (canonC_num C) (canonC_den C)
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) y)) y := by
  obtain ⟨ky, hky⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hy1
  have hinv : Req (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) y) (Rinv y ky hky) :=
    clampedInv_eq_of_ge hky hy1
  have hc_inv : Rle (ofQ (canonC C) (canonC_den C)) (Rinv y ky hky) :=
    Rinv_ge_ofQ_inv (canonB_den C) (canonB_num C) hky hyB
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ (canonC_num C) (canonC_den C) hc_inv
  refine Req_trans (clampedInv_congr _ _ _ hinv) ?_
  refine Req_trans (clampedInv_eq_of_ge (a := canonC C) (han := canonC_num C) (had := canonC_den C)
    hki hc_inv) ?_
  exact Rinv_Rinv_eq hky hki

/-- `y·(1/y) = 1` with the clamped reciprocal, for `y ≥ 1`. -/
theorem Rmul_clampedInv_one (y : Real) (hy1 : Rle one y) :
    Req (Rmul y (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) y)) one := by
  obtain ⟨ky, hky⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hy1
  exact Req_trans (Rmul_congr (Req_refl _) (clampedInv_eq_of_ge hky hy1)) (Rmul_Rinv_self hky)

-- ===========================================================================
-- (4) THE POINTWISE FOLD IDENTITY on `[1, B]`:
--     `(invPullTest (lowInt f g))(y) = F⁺_{g,f}(y)·(1 + 1/y)`.
-- ===========================================================================

theorem fold_pointwise (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (y : Real) (hy1 : Rle one y) (hyB : Rle y (ofQ (canonB C) (canonB_den C))) :
    Req ((invPullTest (lowInt C f g)).f y) ((highInt C g f).f y) := by
  rw [invPullTest_f, lowInt_f, highInt_f, poleDens_f]
  -- (F(u)·(1 + clampedInv c u))·(u·u)  with u = 1/y;  clampedInv c u = y
  have hcc := clampedInv_recip_eq C y hy1 hyB
  have hF := FCanon_recip_real C f g hf hg y hy1 hyB
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Radd_congr (Req_refl _) hcc)) (Req_refl _)) ?_
  -- (A·D)·(u·u) = (u·A)·(D·u)
  refine Req_trans (Rmul_mul_mul_comm _ _ _ _) ?_
  refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
  refine Rmul_congr hF ?_
  -- (1 + y)·u = u + y·u = u + 1 = 1 + u
  refine Req_trans (Rmul_distrib_right _ _ _) ?_
  refine Req_trans (Radd_congr (Rone_mul _) (Rmul_clampedInv_one y hy1)) ?_
  exact Radd_comm _ _

-- ===========================================================================
-- (5) The window `[1, B]` under the unit pullback.
-- ===========================================================================

theorem affine_one_lo (w : Q) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) (h0 : Rle zero t) :
    Rle one (affineMap (⟨1, 1⟩ : Q) w Nat.one_pos hw t) :=
  Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_of_Rle_zero h0))

theorem affine_one_hi (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B) (t : Real) (h1 : Rle t one) :
    Rle (affineMap (⟨1, 1⟩ : Q) (Qsub B (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos hBd Nat.one_pos) t)
        (ofQ B hBd) := by
  have hwn : 0 ≤ (Qsub B (⟨1, 1⟩ : Q)).num := Qsub_num_nonneg hB1
  refine Rle_trans (Radd_le_add (Rle_refl _)
    (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ hwn) h1) (Rle_of_Req (Rmul_one _)))) ?_
  refine Rle_of_Req (Req_trans (Radd_ofQ_ofQ Nat.one_pos (Qsub_den_pos hBd Nat.one_pos)) ?_)
  exact ofQ_congr _ _ (Qadd_Qsub_cancel (⟨1, 1⟩ : Q) B)

-- ===========================================================================
-- (6) THE LOW/HIGH FOLD.
-- ===========================================================================

/-- **THE LOW FOLD** `∫_{1/B}^{1} F⁺_{f,g}(x)(1+1/x) dx = ∫_{1}^{B} F⁺_{g,f}(y)(1+1/y) dy` — inversion
    `x = 1/y` under the certified integral + the real transpose law. -/
theorem MellinLow_fold (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    Req (MellinLow C f g) (MellinHigh C g f) := by
  refine Req_trans (riemannIntegralI_inversion (lowInt C f g) (canonB C) (canonB_den C) (canonB_gt_one C)) ?_
  refine riemannIntegralI_congr_unit_mod _ _ _ _ _ _ _ _ _ _ _ _ _ (fun t h0 h1 => ?_)
  exact fold_pointwise C f g hf hg _ (affine_one_lo _ _ (Qsub_num_nonneg (canonB_one C)) t h0)
    (affine_one_hi (canonB C) (canonB_den C) (canonB_one C) t h1)

theorem poleIntegrand_f (G : ClosedGeom) (f g : L2Test) (x : Real) :
    (poleIntegrand G f g).f x
      = Rmul (Radd ((FTestG G f g).f x) ((FTestG G g f).f x)) (poleDens.f x) := by
  unfold poleIntegrand; rfl

/-- The one-sided `FTestG` over the canonical geometry is `FTest` at the canonical band. -/
theorem FTestG_geom_f (C : NormCtx) (f g : L2Test) (x : Real) :
    (FTestG C.geom f g).f x
      = (FTest (canonB C) (canonB_den C) (canonB_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
          f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn).f x := by
  unfold FTestG; rfl

/-- **THE HIGH SUM** `∫_1^B F⁺_{g,f}(1+1/x) + ∫_1^B F⁺_{f,g}(1+1/x) = ∫_1^B poleIntegrand` (the one-sided
    `FTest` agrees with `F⁺` on `[1,B]`). -/
theorem MellinHigh_sum (C : NormCtx) (f g : L2Test) :
    Req (Radd (MellinHigh C g f) (MellinHigh C f g))
        (riemannIntegralI (poleIntegrand C.geom f g).hLd (poleIntegrand C.geom f g).hLn
          (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc
          (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos
          (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))) := by
  refine Req_trans (Req_symm (riemannIntegralI_addTest (highInt C g f) (highInt C f g) _ _ _ _ _)) ?_
  refine riemannIntegralI_congr_unit_mod _ _ _ _ _ _ _ _ _ _ _ _ _ (fun t h0 h1 => ?_)
  have hy1 : Rle one (affineMap (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos
      (Qsub_den_pos (canonB_den C) Nat.one_pos) t) :=
    affine_one_lo (Qsub (canonB C) (⟨1, 1⟩ : Q)) (Qsub_den_pos (canonB_den C) Nat.one_pos)
      (Qsub_num_nonneg (canonB_one C)) t h0
  have hyB := affine_one_hi (canonB C) (canonB_den C) (canonB_one C) t h1
  rw [poleIntegrand_f, FTestG_geom_f, FTestG_geom_f]
  show Req (Radd (Rmul ((FCanon C g f).f _) (poleDens.f _)) (Rmul ((FCanon C f g).f _) (poleDens.f _))) _
  refine Req_trans (Radd_comm _ _) ?_
  refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) ?_
  refine Rmul_congr (Radd_congr ?_ ?_) (Req_refl _)
  · exact FTwo_eq_FTest_high (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
      (canonB_one C) (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
      f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn _ hy1 hyB
  · exact FTwo_eq_FTest_high (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
      (canonB_one C) (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
      g f C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn _ hy1 hyB

-- ===========================================================================
-- (7) `PoleForm` is the finite window `[1, B]` (the integrand vanishes past `B = X+1`).
-- ===========================================================================

theorem poleIntegrand_term_vanish (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (hg : CoreTest C.geom g) (m : Nat) (hm : C.X - 1 + 1 ≤ m) :
    Req (integralTerm (poleIntegrand C.geom f g).hLd (poleIntegrand C.geom f g).hLn
          (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc m) zero := by
  refine integralTerm_vanish _ _ _ _ m (fun x hx => poleIntegrand_high_vanish C.geom f g hf hg x ?_)
  refine Rle_trans (Rle_ofQ_ofQ _ Nat.one_pos ?_) hx
  have hX := C.hX
  show ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int)
  push_cast
  omega

/-- `PoleForm = ∫_{[1, X+1]} poleIntegrand` (start `1`, width `X − 1 + 1 = X`). -/
theorem PoleForm_eq_finite (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    Req (PoleForm C.geom f g hf hg)
        (riemannIntegralI (poleIntegrand C.geom f g).hLd (poleIntegrand C.geom f g).hLn
          (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc
          (⟨1, 1⟩ : Q) (⟨((C.X - 1 + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _)) := by
  unfold PoleForm
  exact improperIntegral1_eq_finite _ _ _ _ _ _ _ (C.X - 1) (poleIntegrand_term_vanish C f g hf hg)

/-- The window `[1, X+1]` (width `X`) is `[1, B]` (width `B − 1`). -/
theorem pole_window_congr (C : NormCtx) (f g : L2Test) :
    Req (riemannIntegralI (poleIntegrand C.geom f g).hLd (poleIntegrand C.geom f g).hLn
          (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc
          (⟨1, 1⟩ : Q) (⟨((C.X - 1 + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos Nat.one_pos (Int.ofNat_nonneg _))
        (riemannIntegralI (poleIntegrand C.geom f g).hLd (poleIntegrand C.geom f g).hLn
          (poleIntegrand C.geom f g).hlip (poleIntegrand C.geom f g).hfc
          (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos
          (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))) := by
  refine riemannIntegralI_congr_Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Qeq_refl _) ?_
  have e : C.X - 1 + 1 = C.X := Nat.sub_add_cancel C.hX
  rw [e]
  simp only [Qeq, Qsub, add, neg, canonB]
  push_cast
  omega

-- ===========================================================================
-- (8) THE FOLDING THEOREM and the substantive `PoleForm_diag`.
-- ===========================================================================

/-- **★★ THE FOLDING THEOREM** `MellinPole C f g = PoleForm C.geom f g` — the independently defined
    two-window Mellin pole term IS the candidate folded integral: low window inverted (`x = 1/y`)
    and transposed (`y⁻¹F⁺_{f,g}(1/y) = F⁺_{g,f}(y)`), high windows summed, the improper `PoleForm`
    collapsed to `[1, B]`.  PROVED, not copied. -/
theorem MellinPole_eq_PoleForm (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (hg : CoreTest C.geom g) :
    Req (MellinPole C f g) (PoleForm C.geom f g hf hg) := by
  show Req (Radd (MellinLow C f g) (MellinHigh C f g)) _
  refine Req_trans (Radd_congr (MellinLow_fold C f g hf hg) (Req_refl _)) ?_
  refine Req_trans (MellinHigh_sum C f g) ?_
  refine Req_trans (Req_symm (pole_window_congr C f g)) ?_
  exact Req_symm (PoleForm_eq_finite C f g hf hg)

/-- **THE SUBSTANTIVE `PoleForm_diag`**: on the diagonal, the constructed `PoleForm` equals the
    INDEPENDENTLY defined Mellin pole term of the context's own test (bridge item 5, pole half — no
    reflexivity: `MellinPole` is defined from the two full Mellin windows alone). -/
theorem PoleForm_diag (C : NormCtx) :
    Req (PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)) (MellinPole C C.g C.g) :=
  Req_symm (MellinPole_eq_PoleForm C C.g C.g (normCtx_core C) (normCtx_core C))

-- ===========================================================================
-- (9) The slot with the INDEPENDENT pole field and the acceptance theorem (pole half).
-- ===========================================================================

/-- The constructed slot whose `poles` field is the INDEPENDENT `MellinPole` (not the `PoleForm`
    expression).  HONEST SCOPE: `archTail` is still the constructed `ArchTailForm` itself (bridge
    item 4, the independent archimedean integral, is NOT yet done). -/
def normAutocorrSlotMellin (C : NormCtx) : WeilSlot where
  test := normAutocorrTest C
  poles := MellinPole C C.g C.g
  archTail := ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)

/-- **THE ACCEPTANCE THEOREM, POLE HALF**: `closedWeilBilin` on the diagonal equals the Weil functional
    of the slot whose pole field is the independent Mellin pole — the pole component is discharged by
    the SUBSTANTIVE `PoleForm_diag` (folding theorem), the prime and archimedean-constant components
    by their readbacks; the `archTail` component remains definitional (item 4 pending). -/
theorem closedWeilBilin_diag_mellin (C : NormCtx) :
    Req (closedWeilBilin C.geom C.X C.g C.g (normCtx_core C) (normCtx_core C))
        (weilValue (normAutocorrSlotMellin C)) := by
  show Req
    (Rsub (PoleForm C.geom C.g C.g (normCtx_core C) (normCtx_core C))
      (Radd (PrimeForm C.X C.g C.g C.a C.han C.had C.w C.hw C.hwn)
        (Radd (ArchConstForm C.g C.g C.a C.han C.had C.w C.hw C.hwn)
          (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)))))
    (Rsub (MellinPole C C.g C.g)
      (Radd (weilPrimePart (normAutocorrTest C))
        (Radd (weilArchConst (normAutocorrTest C))
          (ArchTailForm C.geom C.g C.g (normCtx_core C) (normCtx_core C)))))
  exact Rsub_congr (PoleForm_diag C)
    (Radd_congr (PrimeForm_diag_weilPrimePart C)
      (Radd_congr (ArchConstForm_diag C) (Req_refl _)))


end UOR.Bridge.F1Square.Square
