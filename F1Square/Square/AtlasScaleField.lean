/-
F1 square — **the raw single-test archimedean scale field, TARGET-FREE** (`AtlasScaleField.lean`).

The raw single-test coordinates of the window variable `t`, exactly as the code realizes the two-sided
correlation (`invSqrtTwoF` clamp, `[0,S]` band clamp, Haar window):

    `U_x(f,t) = x^{-1/2} · f(x / max(t,a))`      (`Uc`),
    `V(f,t)   = f(1 / max(t,a))`                  (`Vc`),
    `D_x(f,t) = U_x(f,t) − (1/max(x,1)) · V(f,t)`   (`Dc`),

THE RAW ENDPOINT-DEFECT IDENTITY (pointwise in `t`, every real `x`, `endpoint_defect_pt`), the raw
assembled/defect integrands with their certificates and `defectIntegral`, the raw estimates
(`Uc_one_eq_Vc`, `Dc_one_zero`, `Dc_abs_le_dist_one` uniform in `t`, `Uc_high_zero`,
`Dc_high_eq_neg_rOne_Vc`), and THE COMMON-SCALE BRIDGE (`Uc_ofQ_eq_normWeight_uEv`, `Uc_placeData`,
`prime_coherent`).  This module imports NO target form: `FCanon`, `archNumC`, `closedWeilBilin`,
`CoupledForm` and dominance are unreachable from here (see `WeilGeom`).  The readbacks of `F⁺(x)`,
`F⁺(1)` and `N⁺(x)` through these coordinates are in `AtlasArchCoords.lean`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasPrimeDirect
import F1Square.Square.WeilInvSqrtTwo
import F1Square.Analysis.ClampedInvLower

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) The raw coordinates, as the code realizes them.
-- ===========================================================================

/-- The `[0,S]`-band clamp of the real scale (the code's realization of the scale `x` in `H_{f,g}(x)`). -/
def xBand (C : NormCtx) (x : Real) : Real := qBandQ (⟨0, 1⟩ : Q) C.S (by decide) C.hSd x

/-- The certified two-sided `x^{-1/2}` of the canonical band (`invSqrtTwoF`). -/
def invSq (C : NormCtx) (x : Real) : Real :=
  invSqrtTwoF (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C) x

/-- `t ↦ f(x / max(t,a))` — the reflected real-scale dilation of `f`, as an `L2Test`. -/
def dilRef (C : NormCtx) (x : Real) (f : L2Test) : L2Test :=
  reflectTest C.a C.han C.had (dilateTestR (xBand C x) C.S C.hSd C.hSn (clampS_absle C.S C.hSd C.hSn x) f)

/-- **`U_x(f,t) = x^{-1/2}·f(x/max(t,a))`**. -/
def Uc (C : NormCtx) (x : Real) (f : L2Test) (t : Real) : Real := Rmul (invSq C x) ((dilRef C x f).f t)

/-- **`V(f,t) = f(1/max(t,a))`** (the raw reflection evaluation). -/
def Vc (C : NormCtx) (f : L2Test) (t : Real) : Real := vEv C f t

/-- `1/max(x,1)` — the code's `x^{-1}` on `[1,∞)`. -/
def rOne (x : Real) : Real := clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x

/-- **`D_x(f,t) = U_x(f,t) − (1/max(x,1))·V(f,t)`** — the endpoint defect of the single-test coordinate. -/
def Dc (C : NormCtx) (x : Real) (f : L2Test) (t : Real) : Real := Rsub (Uc C x f t) (Rmul (rOne x) (Vc C f t))

-- ===========================================================================
-- (2) THE RAW ENDPOINT-DEFECT IDENTITY (pointwise).
-- ===========================================================================

/-- `(x − y)·z ≈ x·z − y·z`. -/
theorem Rsub_mul_ac (x y z : Real) : Req (Rmul (Rsub x y) z) (Rsub (Rmul x z) (Rmul y z)) :=
  Req_trans (Rmul_distrib_right x (Rneg y) z) (Radd_congr (Req_refl _) (Rmul_neg_left y z))

/-- **The core identity** `(U − r₁V)V' + V(U' − r₁V') ≈ (UV' + VU') − (2r₁)(VV')`. -/
theorem endpoint_defect_core (U V U' V' r₁ : Real) :
    Req (Radd (Rmul (Rsub U (Rmul r₁ V)) V') (Rmul V (Rsub U' (Rmul r₁ V'))))
        (Rsub (Radd (Rmul U V') (Rmul V U')) (Rmul (Rmul cTwo r₁) (Rmul V V'))) := by
  refine Req_trans (Radd_congr (Rsub_mul_ac _ _ _) (Rmul_sub_distrib _ _ _)) ?_
  refine Req_trans (Req_symm (Rsub_Radd_Radd _ _ _ _)) ?_
  refine Rsub_congr (Req_refl _) ?_
  -- (r₁V)V' + V(r₁V') ≈ (2r₁)(VV')
  have h1 : Req (Rmul (Rmul r₁ V) V') (Rmul r₁ (Rmul V V')) := Rmul_assoc _ _ _
  have h2 : Req (Rmul V (Rmul r₁ V')) (Rmul r₁ (Rmul V V')) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm V r₁) (Req_refl _)) (Rmul_assoc _ _ _))
  refine Req_trans (Radd_congr h1 h2) ?_
  exact Req_trans (Req_symm (cTwo_mul _)) (Req_symm (Rmul_assoc _ _ _))

/-- **★ THE RAW ENDPOINT-DEFECT IDENTITY (pointwise, density included)**:
    `(UV')r + (VU')r − ((2r₁)(VV'))r ≈ [(U − r₁V)V' + V(U' − r₁V')]·r`. -/
theorem endpoint_defect_pt (U V U' V' r₁ r : Real) :
    Req (Radd (Radd (Rmul (Rmul U V') r) (Rmul (Rmul V U') r))
              (Rneg (Rmul (Rmul cTwo r₁) (Rmul (Rmul V V') r))))
        (Rmul (Radd (Rmul (Rsub U (Rmul r₁ V)) V') (Rmul V (Rsub U' (Rmul r₁ V')))) r) := by
  refine Req_symm ?_
  refine Req_trans (Rmul_congr (endpoint_defect_core U V U' V' r₁) (Req_refl r)) ?_
  refine Req_trans (Rsub_mul_ac _ _ _) ?_
  refine Radd_congr (Rmul_distrib_right _ _ _) (Rneg_congr (Rmul_assoc _ _ _))

/-- The same identity in the raw coordinates: for every `x` and `t`,
    `U_x(f)V(g) + V(f)U_x(g) − 2(1/max(x,1))V(f)V(g) = D_x(f)V(g) + V(f)D_x(g)` (times the density). -/
theorem endpoint_defect_coords (C : NormCtx) (x : Real) (f g : L2Test) (t : Real) :
    Req (Radd (Radd (Rmul (Rmul (Uc C x f t) (Vc C g t)) (rEv C t)) (Rmul (Rmul (Vc C f t) (Uc C x g t)) (rEv C t)))
              (Rneg (Rmul (Rmul cTwo (rOne x)) (Rmul (Rmul (Vc C f t) (Vc C g t)) (rEv C t)))))
        (Rmul (Radd (Rmul (Dc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C x g t))) (rEv C t)) :=
  endpoint_defect_pt _ _ _ _ _ _

-- ===========================================================================
-- (3) The raw cross/`VV` integrands (the readbacks of `F⁺` are in `AtlasArchCoords`).
-- ===========================================================================

/-- The pulled-back cross-correlation integrand `t ↦ f(x/max(t,a))·g(1/max(t,a))·(1/max(t,a))`. -/
def crossInt (C : NormCtx) (x : Real) (f g : L2Test) : Real → Real :=
  prodInt C (dilRef C x f) (reflectTest C.a C.han C.had g)
def crossL (C : NormCtx) (x : Real) (f g : L2Test) : Q := prodIntL C (dilRef C x f) (reflectTest C.a C.han C.had g)
theorem crossL_den (C : NormCtx) (x : Real) (f g : L2Test) : 0 < (crossL C x f g).den := prodIntL_den _ _ _
theorem crossL_num (C : NormCtx) (x : Real) (f g : L2Test) : 0 ≤ (crossL C x f g).num := prodIntL_num _ _ _
theorem crossInt_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (crossInt C x f g y) (crossInt C x f g z))) (Rmul (ofQ (crossL C x f g) (crossL_den C x f g)) (Rabs (Rsub y z))) :=
  prodInt_lip _ _ _
theorem crossInt_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (crossInt C x f g y) (crossInt C x f g z) :=
  prodInt_fc _ _ _

/-- The pulled-back integrand `V(f)V(g)·(1/max(t,a))`. -/
def vvInt (C : NormCtx) (f g : L2Test) : Real → Real :=
  prodInt C (reflectTest C.a C.han C.had f) (reflectTest C.a C.han C.had g)
def vvL (C : NormCtx) (f g : L2Test) : Q := prodIntL C (reflectTest C.a C.han C.had f) (reflectTest C.a C.han C.had g)
theorem vvL_den (C : NormCtx) (f g : L2Test) : 0 < (vvL C f g).den := prodIntL_den _ _ _
theorem vvL_num (C : NormCtx) (f g : L2Test) : 0 ≤ (vvL C f g).num := prodIntL_num _ _ _
theorem vvInt_lip (C : NormCtx) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (vvInt C f g y) (vvInt C f g z))) (Rmul (ofQ (vvL C f g) (vvL_den C f g)) (Rabs (Rsub y z))) :=
  prodInt_lip _ _ _
theorem vvInt_fc (C : NormCtx) (f g : L2Test) : ∀ y z, Req y z → Req (vvInt C f g y) (vvInt C f g z) :=
  prodInt_fc _ _ _

/-- The place datum of scale `1` (weight irrelevant). -/
def pdOne : PlaceDatum := ⟨(⟨1, 1⟩ : Q), (show (0 : Int) < 1 by decide), Nat.one_pos, zero⟩

/-- `hInt` at scale `1` is `vvInt` pointwise (`f(1·y) ≈ f(y)`). -/
theorem hInt_one_eq_vv (C : NormCtx) (f g : L2Test) (y : Real) :
    Req (hInt C pdOne f g y) (vvInt C f g y) := by
  unfold hInt vvInt prodInt uEv vEv affC
  refine Rmul_congr (Rmul_congr ?_ (Req_refl _)) (Req_refl _)
  show Req (f.f (Rmul (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (clampedInv C.a C.han C.had (affineMap C.a C.w C.had C.hw y))))
           (f.f (clampedInv C.a C.han C.had (affineMap C.a C.w C.had C.hw y)))
  exact f.hfc _ _ (Rone_mul _)

-- ===========================================================================
-- (4) The assembled and defect integrands, their certificates, and `defectIntegral`.
-- ===========================================================================

/-- The assembled integrand `x^{-1/2}·cross_{fg} + x^{-1/2}·cross_{gf} − (2/max(x,1))·vv`. -/
def asmInt (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Radd (Radd (Rmul (invSq C x) (crossInt C x f g y)) (Rmul (invSq C x) (crossInt C x g f y)))
       (Rneg (Rmul (Rmul cTwo (rOne x)) (vvInt C f g y)))

/-- The defect integrand `[D_x(f)V(g) + V(f)D_x(g)]·(1/max(t,a))` (pulled back). -/
def defInt (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Rmul (Radd (Rmul (Dc C x f (affC C y)) (Vc C g (affC C y))) (Rmul (Vc C f (affC C y)) (Dc C x g (affC C y))))
       (rEv C (affC C y))

/-- The assembled integrand IS the defect integrand pointwise (the raw identity, `x^{-1/2}` pulled in). -/
theorem asmInt_eq_defInt (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) :
    Req (asmInt C x f g y) (defInt C x f g y) := by
  unfold asmInt defInt crossInt vvInt prodInt Dc Uc Vc
  -- x^{-1/2}·((d·v)·r) ≈ ((x^{-1/2}·d)·v)·r, then the pointwise identity
  have hpull : ∀ (s d v r : Real), Req (Rmul s (Rmul (Rmul d v) r)) (Rmul (Rmul (Rmul s d) v) r) :=
    fun s d v r => Req_trans (Req_symm (Rmul_assoc s (Rmul d v) r)) (Rmul_congr (Req_symm (Rmul_assoc s d v)) (Req_refl r))
  unfold vEv
  have e1 := hpull (invSq C x) ((dilRef C x f).f (affC C y)) ((reflectTest C.a C.han C.had g).f (affC C y)) (rEv C (affC C y))
  have e2 : Req (Rmul (invSq C x) (Rmul (Rmul ((dilRef C x g).f (affC C y)) ((reflectTest C.a C.han C.had f).f (affC C y)))
        (rEv C (affC C y))))
      (Rmul (Rmul ((reflectTest C.a C.han C.had f).f (affC C y)) (Rmul (invSq C x) ((dilRef C x g).f (affC C y))))
        (rEv C (affC C y))) :=
    Req_trans (hpull _ _ _ _) (Rmul_congr (Rmul_comm _ _) (Req_refl _))
  refine Req_trans (Radd_congr (Radd_congr e1 e2) (Req_refl _)) ?_
  exact endpoint_defect_pt _ _ _ _ _ _

-- moduli of the assembled integrand
def asmL (C : NormCtx) (x : Real) (f g : L2Test) : Q :=
  add (add (mul (xBQ (invSq C x)) (crossL C x f g)) (mul (xBQ (invSq C x)) (crossL C x g f)))
      (mul (xBQ (Rmul cTwo (rOne x))) (vvL C f g))
theorem asmL_den (C : NormCtx) (x : Real) (f g : L2Test) : 0 < (asmL C x f g).den :=
  add_den_pos (add_den_pos (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)))
    (Qmul_den_pos Nat.one_pos (vvL_den _ _ _))
theorem asmL_num (C : NormCtx) (x : Real) (f g : L2Test) : 0 ≤ (asmL C x f g).num :=
  Qadd_num_nonneg_loc (Qadd_num_nonneg_loc (Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _))
    (Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _))) (Qmul_num_nonneg (xBQ_num_nonneg _) (vvL_num _ _ _))

theorem p1_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Rmul (invSq C x) (crossInt C x f g y)) (Rmul (invSq C x) (crossInt C x f g z))))
        (Rmul (ofQ (mul (xBQ (invSq C x)) (crossL C x f g)) (Qmul_den_pos Nat.one_pos (crossL_den C x f g))) (Rabs (Rsub y z))) :=
  lip_smul_fl (invSq C x) (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g)
theorem p3_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Rmul (Rmul cTwo (rOne x)) (vvInt C f g y)) (Rmul (Rmul cTwo (rOne x)) (vvInt C f g z))))
        (Rmul (ofQ (mul (xBQ (Rmul cTwo (rOne x))) (vvL C f g)) (Qmul_den_pos Nat.one_pos (vvL_den C f g))) (Rabs (Rsub y z))) :=
  lip_smul_fl (Rmul cTwo (rOne x)) (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g)

theorem asmInt_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (asmInt C x f g y) (asmInt C x f g z))) (Rmul (ofQ (asmL C x f g) (asmL_den C x f g)) (Rabs (Rsub y z))) :=
  lip_add_fl (add_den_pos (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)))
    (Qmul_den_pos Nat.one_pos (vvL_den _ _ _))
    (lip_add_fl (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _))
      (p1_lip C x f g) (p1_lip C x g f))
    (lip_neg_pd (Qmul_den_pos Nat.one_pos (vvL_den _ _ _)) (p3_lip C x f g))
theorem asmInt_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (asmInt C x f g y) (asmInt C x f g z) :=
  fun y z h => Radd_congr (Radd_congr (fc_smul_fl _ (crossInt_fc C x f g) y z h) (fc_smul_fl _ (crossInt_fc C x g f) y z h))
    (Rneg_congr (fc_smul_fl _ (vvInt_fc C f g) y z h))
theorem defInt_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (defInt C x f g y) (defInt C x f g z))) (Rmul (ofQ (asmL C x f g) (asmL_den C x f g)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (fun y => Req_symm (asmInt_eq_defInt C x f g y)) (asmInt_lip C x f g)
theorem defInt_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (defInt C x f g y) (defInt C x f g z) :=
  fc_of_congr_pd (fun y => Req_symm (asmInt_eq_defInt C x f g y)) (asmInt_fc C x f g)

/-- **The defect integral** `∫₀¹ defInt` (certified). -/
def defectIntegral (C : NormCtx) (x : Real) (f g : L2Test) : Real :=
  riemannIntegral (asmL_den C x f g) (asmL_num C x f g) (defInt_lip C x f g) (defInt_fc C x f g)

/-- `∫ asmInt = x^{-1/2}∫cross_{fg} + x^{-1/2}∫cross_{gf} − (2/max(x,1))∫vv` (finite linearity, moduli reconciled). -/
theorem integral_asm (C : NormCtx) (x : Real) (f g : L2Test) :
    Req (riemannIntegral (asmL_den C x f g) (asmL_num C x f g) (asmInt_lip C x f g) (asmInt_fc C x f g))
        (Radd (Radd (Rmul (invSq C x) (riemannIntegral (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g) (crossInt_fc C x f g)))
                    (Rmul (invSq C x) (riemannIntegral (crossL_den C x g f) (crossL_num C x g f) (crossInt_lip C x g f) (crossInt_fc C x g f))))
              (Rneg (Rmul (Rmul cTwo (rOne x)) (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g))))) := by
  -- moduli
  have hL1d : 0 < (mul (xBQ (invSq C x)) (crossL C x f g)).den := Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)
  have hL1n : 0 ≤ (mul (xBQ (invSq C x)) (crossL C x f g)).num := Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)
  have hL2d : 0 < (mul (xBQ (invSq C x)) (crossL C x g f)).den := Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)
  have hL2n : 0 ≤ (mul (xBQ (invSq C x)) (crossL C x g f)).num := Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)
  have hL3d : 0 < (mul (xBQ (Rmul cTwo (rOne x))) (vvL C f g)).den := Qmul_den_pos Nat.one_pos (vvL_den _ _ _)
  have hL3n : 0 ≤ (mul (xBQ (Rmul cTwo (rOne x))) (vvL C f g)).num := Qmul_num_nonneg (xBQ_num_nonneg _) (vvL_num _ _ _)
  have hL12d : 0 < (add (mul (xBQ (invSq C x)) (crossL C x f g)) (mul (xBQ (invSq C x)) (crossL C x g f))).den := add_den_pos hL1d hL2d
  have hL12n : 0 ≤ (add (mul (xBQ (invSq C x)) (crossL C x f g)) (mul (xBQ (invSq C x)) (crossL C x g f))).num := Qadd_num_nonneg_loc hL1n hL2n
  -- weakened certificates at the total modulus
  have h12S := lip_weaken_fl hL12d (asmL_den C x f g) (Qle_add_right_nonneg hL3n)
    (lip_add_fl hL1d hL2d (p1_lip C x f g) (p1_lip C x g f))
  have h3S := lip_weaken_fl hL3d (asmL_den C x f g) (Qle_add_left_nonneg hL12n) (lip_neg_pd hL3d (p3_lip C x f g))
  have h12_fc : ∀ y z, Req y z → Req (Radd (Rmul (invSq C x) (crossInt C x f g y)) (Rmul (invSq C x) (crossInt C x g f y)))
      (Radd (Rmul (invSq C x) (crossInt C x f g z)) (Rmul (invSq C x) (crossInt C x g f z))) :=
    fun y z h => Radd_congr (fc_smul_fl _ (crossInt_fc C x f g) y z h) (fc_smul_fl _ (crossInt_fc C x g f) y z h)
  have h3_fc : ∀ y z, Req y z → Req (Rneg (Rmul (Rmul cTwo (rOne x)) (vvInt C f g y))) (Rneg (Rmul (Rmul cTwo (rOne x)) (vvInt C f g z))) :=
    fun y z h => Rneg_congr (fc_smul_fl _ (vvInt_fc C f g) y z h)
  refine Req_trans (riemannIntegral_add (asmL_den C x f g) (asmL_num C x f g) h12S h12_fc h3S h3_fc
    (asmInt_lip C x f g) (asmInt_fc C x f g)) ?_
  refine Radd_congr ?_ ?_
  · -- the two cross pieces
    have h1S := lip_weaken_fl hL1d hL12d (Qle_add_right_nonneg hL2n) (p1_lip C x f g)
    have h2S := lip_weaken_fl hL2d hL12d (Qle_add_left_nonneg hL1n) (p1_lip C x g f)
    refine Req_trans (riemannIntegral_certif_irrel _ _ h12S h12_fc hL12d hL12n
      (lip_add_fl hL1d hL2d (p1_lip C x f g) (p1_lip C x g f)) h12_fc) ?_
    refine Req_trans (riemannIntegral_add hL12d hL12n h1S (fc_smul_fl _ (crossInt_fc C x f g)) h2S
      (fc_smul_fl _ (crossInt_fc C x g f)) (lip_add_fl hL1d hL2d (p1_lip C x f g) (p1_lip C x g f)) h12_fc) ?_
    refine Radd_congr ?_ ?_
    · refine Req_trans (riemannIntegral_certif_irrel _ _ h1S _ hL1d hL1n (p1_lip C x f g) (fc_smul_fl _ (crossInt_fc C x f g))) ?_
      exact riemannIntegral_smul_real_fl (invSq C x) (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g) (crossInt_fc C x f g)
    · refine Req_trans (riemannIntegral_certif_irrel _ _ h2S _ hL2d hL2n (p1_lip C x g f) (fc_smul_fl _ (crossInt_fc C x g f))) ?_
      exact riemannIntegral_smul_real_fl (invSq C x) (crossL_den C x g f) (crossL_num C x g f) (crossInt_lip C x g f) (crossInt_fc C x g f)
  · -- the negated `vv` piece
    refine Req_trans (riemannIntegral_certif_irrel _ _ h3S h3_fc hL3d hL3n (lip_neg_pd hL3d (p3_lip C x f g)) h3_fc) ?_
    refine Req_trans (riemannIntegral_neg hL3d hL3n (p3_lip C x f g) (fc_smul_fl _ (vvInt_fc C f g))
      (lip_neg_pd hL3d (p3_lip C x f g)) h3_fc) (Rneg_congr ?_)
    exact riemannIntegral_smul_real_fl (Rmul cTwo (rOne x)) (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)

/-- `s·(w·I) ≈ w·(s·I)`. -/
theorem swap_w_ac (s w I : Real) : Req (Rmul s (Rmul w I)) (Rmul w (Rmul s I)) :=
  Req_trans (Req_symm (Rmul_assoc s w I)) (Req_trans (Rmul_congr (Rmul_comm s w) (Req_refl I)) (Rmul_assoc w s I))

/-- `(2·(w·I))·r₁ ≈ w·((2·r₁)·I)`. -/
theorem two_w_ac (w I r₁ : Real) : Req (Rmul (Rmul cTwo (Rmul w I)) r₁) (Rmul w (Rmul (Rmul cTwo r₁) I)) := by
  refine Req_trans (Rmul_congr (Req_symm (Rmul_assoc cTwo w I)) (Req_refl r₁)) ?_
  refine Req_trans (Rmul_assoc (Rmul cTwo w) I r₁) ?_
  refine Req_trans (Rmul_congr (Rmul_comm cTwo w) (Rmul_comm I r₁)) ?_
  refine Req_trans (Rmul_assoc w cTwo (Rmul r₁ I)) (Rmul_congr (Req_refl w) ?_)
  exact Req_symm (Rmul_assoc cTwo r₁ I)

-- ===========================================================================
-- (5) THE RAW ENDPOINT AND TAIL ESTIMATES.
-- ===========================================================================

/-- `1^{-1/2} = 1` for the certified two-sided weight. -/
theorem invSq_one (C : NormCtx) : Req (invSq C one) one :=
  Req_trans (invSqrtTwoF_ofQ (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C) (⟨1, 1⟩ : Q) Nat.one_pos (canonC_le_one C) (canonB_one C))
    (Req_trans (normWeight_pos_eq (show (0 : Int) < 1 by decide)) Rsqrt_one)

/-- The scale band is inert at `x = 1` (`1 ≤ S`). -/
theorem xBand_one (C : NormCtx) : Req (xBand C one) one :=
  qBandQ_eq_of_band (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) (Rle_ofQ_ofQ (by decide) C.hSd C.hS1)

/-- `1/max(1,1) = 1`. -/
theorem rOne_one : Req (rOne one) one :=
  clampedInv_ofQ (a := (⟨1, 1⟩ : Q)) (q := (⟨1, 1⟩ : Q)) (by decide) (by decide) (by decide) (by decide) (Qle_refl _)

/-- `U_x` respects `≈` in the scale. -/
theorem Uc_congr_x (C : NormCtx) {x y : Real} (h : Req x y) (f : L2Test) (t : Real) :
    Req (Uc C x f t) (Uc C y f t) := by
  unfold Uc invSq dilRef
  refine Rmul_congr (invSqrtTwoF_congr _ _ _ _ _ _ _ _ _ _ h) ?_
  show Req (f.f (Rmul (xBand C x) (clampedInv C.a C.han C.had t))) (f.f (Rmul (xBand C y) (clampedInv C.a C.han C.had t)))
  exact f.hfc _ _ (Rmul_congr (qBandQ_congr _ _ _ _ h) (Req_refl _))

/-- **★ `U_1(f,t) = V(f,t)`**: the raw coordinate at the endpoint is the reflection evaluation. -/
theorem Uc_one_eq_Vc (C : NormCtx) (f : L2Test) (t : Real) : Req (Uc C one f t) (Vc C f t) := by
  unfold Uc Vc vEv dilRef
  show Req (Rmul (invSq C one) (f.f (Rmul (xBand C one) (clampedInv C.a C.han C.had t))))
           (f.f (clampedInv C.a C.han C.had t))
  refine Req_trans (Rmul_congr (invSq_one C) (f.hfc _ _ (Rmul_congr (xBand_one C) (Req_refl _)))) ?_
  exact Req_trans (Rone_mul _) (f.hfc _ _ (Rone_mul _))

/-- **★ `D_1(f,t) = 0`**: the endpoint defect vanishes exactly. -/
theorem Dc_one_zero (C : NormCtx) (f : L2Test) (t : Real) : Req (Dc C one f t) zero := by
  unfold Dc
  refine Req_trans (Rsub_congr (Uc_one_eq_Vc C f t) (Req_trans (Rmul_congr rOne_one (Req_refl _)) (Rone_mul _))) ?_
  exact Radd_neg _

-- --- the uniform-in-`t` Lipschitz modulus of `x ↦ D_x(f,t)` ---

/-- The modulus of `x ↦ x^{-1/2}` (the two-sided certified weight). -/
def invSqL (C : NormCtx) : Q :=
  mul (⟨((C.X + 1 : Nat) : Int), 2⟩ : Q) (mul (Qinv (canonC C)) (Qinv (canonC C)))
theorem invSqL_den (C : NormCtx) : 0 < (invSqL C).den :=
  Qmul_den_pos (Nat.succ_pos 1) (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (Qinv_den_pos (canonC_num C)))
theorem invSqL_num (C : NormCtx) : 0 ≤ (invSqL C).num :=
  Int.mul_nonneg (Int.ofNat_nonneg _)
    (Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) (Int.le_of_lt (Qinv_num_pos (canonC_den C))))

theorem invSq_lip (C : NormCtx) : ∀ x y,
    Rle (Rabs (Rsub (invSq C x) (invSq C y))) (Rmul (ofQ (invSqL C) (invSqL_den C)) (Rabs (Rsub x y))) :=
  invSqrtTwoF_lipschitz (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)
theorem invSq_bd (C : NormCtx) : ∀ x, Rle (Rabs (invSq C x)) (ofQ (Qinv (canonC C)) (Qinv_den_pos (canonC_num C))) :=
  (invSqrtTwoTest (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)).hbd

/-- The modulus of `x ↦ f(x/max(t,a))` (uniform in `t`): `L_f·(1/a)`. -/
def dilL (C : NormCtx) (f : L2Test) : Q := mul f.L (Qinv C.a)
theorem dilL_den (C : NormCtx) (f : L2Test) : 0 < (dilL C f).den := Qmul_den_pos f.hLd (Qinv_den_pos C.han)
theorem dilL_num (C : NormCtx) (f : L2Test) : 0 ≤ (dilL C f).num :=
  Int.mul_nonneg f.hLn (Int.le_of_lt (Qinv_num_pos C.had))

theorem dil_lip (C : NormCtx) (f : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub ((dilRef C x f).f t) ((dilRef C y f).f t))) (Rmul (ofQ (dilL C f) (dilL_den C f)) (Rabs (Rsub x y))) := by
  intro x y
  show Rle (Rabs (Rsub (f.f (Rmul (xBand C x) (clampedInv C.a C.han C.had t)))
                       (f.f (Rmul (xBand C y) (clampedInv C.a C.han C.had t))))) _
  refine Rle_trans (f.hlip _ _) ?_
  have h1 : Req (Rabs (Rsub (Rmul (xBand C x) (clampedInv C.a C.han C.had t)) (Rmul (xBand C y) (clampedInv C.a C.han C.had t))))
      (Rmul (Rabs (Rsub (xBand C x) (xBand C y))) (Rabs (clampedInv C.a C.han C.had t))) :=
    Req_trans (Rabs_congr (Req_symm (Rsub_mul_ac _ _ _))) (Rabs_Rmul _ _)
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ f.hLd f.hLn) (Rle_of_Req h1)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ f.hLd f.hLn)
    (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (Qinv_den_pos C.han) (Int.le_of_lt (Qinv_num_pos C.had)))
      (qBandQ_lipschitz _ _ _ _ x y) ((recipTest C.a C.han C.had).hbd t))) ?_
  refine Rle_of_Req ?_
  refine Req_trans (Rmul_congr (Req_refl (ofQ f.L f.hLd)) (Rmul_comm (Rabs (Rsub x y)) _)) ?_
  refine Req_trans (Req_symm (Rmul_assoc (ofQ f.L f.hLd) _ (Rabs (Rsub x y)))) ?_
  exact Rmul_congr (Rmul_ofQ_ofQ f.hLd (Qinv_den_pos C.han)) (Req_refl _)

theorem dil_bd (C : NormCtx) (f : L2Test) (t : Real) : ∀ x, Rle (Rabs ((dilRef C x f).f t)) (ofQ f.M f.hMd) :=
  fun x => f.hbd _

/-- The modulus of `x ↦ U_x(f,t)`, uniform in `t`: `(1/c)·(L_f/a) + M_f·L_{√}`. -/
def UcL (C : NormCtx) (f : L2Test) : Q :=
  add (mul (Qinv (canonC C)) (dilL C f)) (mul f.M (invSqL C))
theorem UcL_den (C : NormCtx) (f : L2Test) : 0 < (UcL C f).den :=
  add_den_pos (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (dilL_den C f)) (Qmul_den_pos f.hMd (invSqL_den C))

theorem Uc_lip_x (C : NormCtx) (f : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Uc C x f t) (Uc C y f t))) (Rmul (ofQ (UcL C f) (UcL_den C f)) (Rabs (Rsub x y))) :=
  fun x y => Rmul_lipschitz (invSqL_den C) (dilL_den C f) (Qinv_den_pos (canonC_num C)) f.hMd
    (invSqL_num C) (dilL_num C f) (Int.le_of_lt (Qinv_num_pos (canonC_den C))) f.hMn
    (invSq_lip C) (dil_lip C f t) (invSq_bd C) (dil_bd C f t) x y

/-- The modulus of `x ↦ (1/max(x,1))·V(f,t)`: `M_f·1` (the unit clamp is `1`-Lipschitz). -/
def rVL (f : L2Test) : Q :=
  add (mul (Qinv (⟨1, 1⟩ : Q)) (⟨0, 1⟩ : Q)) (mul f.M (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))))
theorem rVL_den (f : L2Test) : 0 < (rVL f).den :=
  add_den_pos (Qmul_den_pos (by decide) Nat.one_pos) (Qmul_den_pos f.hMd (Qmul_den_pos (by decide) (by decide)))

theorem rV_lip_x (C : NormCtx) (f : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Rmul (rOne x) (Vc C f t)) (Rmul (rOne y) (Vc C f t)))) (Rmul (ofQ (rVL f) (rVL_den f)) (Rabs (Rsub x y))) :=
  fun x y => Rmul_lipschitz (f := rOne) (g := fun _ => Vc C f t)
    (Lf := mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (Lg := (⟨0, 1⟩ : Q)) (Mf := Qinv (⟨1, 1⟩ : Q)) (Mg := f.M)
    (by decide) Nat.one_pos (by decide) f.hMd
    (by decide) (by decide) (by decide) f.hMn
    (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide)) (const_lip0 (Vc C f t))
    (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)).hbd (fun _ => f.hbd _) x y

/-- **The uniform modulus of `x ↦ D_x(f,t)`**: `L_D(f) = L_U + L_{rV}`, independent of `t`. -/
def DcL (C : NormCtx) (f : L2Test) : Q := add (UcL C f) (rVL f)
theorem DcL_den (C : NormCtx) (f : L2Test) : 0 < (DcL C f).den := add_den_pos (UcL_den C f) (rVL_den f)

theorem Dc_lip_x (C : NormCtx) (f : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Dc C x f t) (Dc C y f t))) (Rmul (ofQ (DcL C f) (DcL_den C f)) (Rabs (Rsub x y))) :=
  fun x y => lip_add_fl (f := fun x => Uc C x f t) (g := fun x => Rneg (Rmul (rOne x) (Vc C f t)))
    (UcL_den C f) (rVL_den f) (Uc_lip_x C f t) (lip_neg_pd (rVL_den f) (rV_lip_x C f t)) x y

/-- **★ `|D_x(f,t)| ≤ L_D(f)·|x − 1|`, uniformly in the Haar variable `t`.** -/
theorem Dc_abs_le_dist_one (C : NormCtx) (f : L2Test) (x t : Real) :
    Rle (Rabs (Dc C x f t)) (Rmul (ofQ (DcL C f) (DcL_den C f)) (Rabs (Rsub x one))) := by
  have h0 : Req (Dc C x f t) (Rsub (Dc C x f t) (Dc C one f t)) :=
    Req_symm (Req_trans (Rsub_congr (Req_refl _) (Dc_one_zero C f t)) (Rsub_zero _))
  exact Rle_trans (Rle_of_Req (Rabs_congr h0)) (Dc_lip_x C f t x one)

-- --- the high side ---

/-- `1/a ≤ B·(1/(a+w))` — the rational support threshold (`a + w ≤ B·a`, `B = X+1`). -/
theorem inv_a_le_B_inv_aw (C : NormCtx) :
    Qle (Qinv C.a) (mul (canonB C) (Qinv (add C.a C.w))) := by
  have hawn : 0 < (add C.a C.w).num := qnum_pos_of_le C.han (add_den_pos C.had C.hw) (Qle_self_add C.hwn)
  have hb := C.hband_hi
  show ((C.a.den : Int)) * ((((canonB C).den) * (add C.a C.w).num.toNat : Nat) : Int)
      ≤ ((canonB C).num * ((add C.a C.w).den : Int)) * ((C.a.num.toNat : Nat) : Int)
  show ((C.a.den : Int)) * (((1 : Nat) * (add C.a C.w).num.toNat : Nat) : Int)
      ≤ (((C.X + 1 : Nat) : Int) * ((add C.a C.w).den : Int)) * ((C.a.num.toNat : Nat) : Int)
  simp only [Qle, mul] at hb
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hawn), Int.toNat_of_nonneg (Int.le_of_lt C.han)] at *
  -- hb : (a+w).num * (1 * a.den) ≤ (X+1) * a.num * (a+w).den
  have e1 : (C.a.den : Int) * (1 * (add C.a C.w).num) = (add C.a C.w).num * (1 * (C.a.den : Int)) := by ring_uor
  have e2 : ((C.X : Int) + 1) * ((add C.a C.w).den : Int) * C.a.num
      = ((C.X : Int) + 1) * C.a.num * ((add C.a C.w).den : Int) := by ring_uor
  omega

/-- **★ `U_x(f,t) = 0` for `x ≥ B` and `t ≤ a + w`** (core test): the dilated argument exceeds `1/a`. -/
theorem Uc_high_zero (C : NormCtx) (f : L2Test) (hf : CoreTest C.geom f) (x t : Real)
    (hx : Rle (ofQ (canonB C) (canonB_den C)) x) (ht : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req (Uc C x f t) zero := by
  have hawn : 0 < (add C.a C.w).num := qnum_pos_of_le C.han (add_den_pos C.had C.hw) (Qle_self_add C.hwn)
  have hB0 : Qle (⟨0, 1⟩ : Q) (canonB C) := Qle_trans (by decide) (by decide) (canonB_one C)
  have hXge : Rle (ofQ (canonB C) (canonB_den C)) (xBand C x) :=
    qBandQ_ge_real C.S C.hSd (canonB C) (canonB_den C) hB0 C.hTS x hx
  have hcinv : Rle (ofQ (Qinv (add C.a C.w)) (Qinv_den_pos hawn)) (clampedInv C.a C.han C.had t) :=
    ofQ_inv_le_clampedInv C.han C.had (add_den_pos C.had C.hw) hawn ht (Qle_self_add C.hwn)
  have hprod : Rle (Rmul (ofQ (canonB C) (canonB_den C)) (ofQ (Qinv (add C.a C.w)) (Qinv_den_pos hawn)))
      (Rmul (xBand C x) (clampedInv C.a C.han C.had t)) :=
    Rmul_le_Rmul_both (Rnonneg_ofQ (canonB_den C) (Int.le_of_lt (canonB_num C)))
      (Rnonneg_clampedInv C.a C.han C.had t) hXge hcinv
  have harg : Rle (ofQ (Qinv C.a) (Qinv_den_pos C.han)) (Rmul (xBand C x) (clampedInv C.a C.han C.had t)) :=
    Rle_trans (Rle_ofQ_ofQ (Qinv_den_pos C.han) (Qmul_den_pos (canonB_den C) (Qinv_den_pos hawn)) (inv_a_le_B_inv_aw C))
      (Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (canonB_den C) (Qinv_den_pos hawn)))) hprod)
  unfold Uc dilRef
  show Req (Rmul (invSq C x) (f.f (Rmul (xBand C x) (clampedInv C.a C.han C.had t)))) zero
  exact Req_trans (Rmul_congr (Req_refl _) (hf.hgh _ harg)) (Rmul_zero _)

/-- **★ On the high side the defect is the retained tail**: `D_x(f,t) = −(1/max(x,1))·V(f,t)` for
    `x ≥ B`, `t ≤ a + w` (core test). -/
theorem Dc_high_eq_neg_rOne_Vc (C : NormCtx) (f : L2Test) (hf : CoreTest C.geom f) (x t : Real)
    (hx : Rle (ofQ (canonB C) (canonB_den C)) x) (ht : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req (Dc C x f t) (Rneg (Rmul (rOne x) (Vc C f t))) := by
  unfold Dc
  refine Req_trans (Rsub_congr (Uc_high_zero C f hf x t hx ht) (Req_refl _)) ?_
  exact Req_trans (Radd_comm _ _) (Radd_zero _)

-- ===========================================================================
-- (6) THE COMMON-SCALE BRIDGE: the prime evaluations are rational-scale samples of the ONE field `U`.
-- ===========================================================================

/-- **★ `U_q(f,t) = q^{-1/2}·u_q(f)(t)`** at every rational scale `q` of the canonical band (`c ≤ q ≤ B`,
    `q ≤ S`): the pole/tail field `Uc` restricted to a rational scale IS the normalized prime evaluation
    (`invSqrtTwoF_ofQ`, inert band clamp, rational dilation). -/
theorem Uc_ofQ_eq_normWeight_uEv (C : NormCtx) (pd : PlaceDatum)
    (hcq : Qle (canonC C) pd.q) (hqB : Qle pd.q (canonB C)) (hqS : Qle pd.q C.S) (f : L2Test) (t : Real) :
    Req (Uc C (ofQ pd.q pd.hqd) f t) (Rmul (normWeight pd.q) (uEv C pd f t)) := by
  have hq0 : Qle (⟨0, 1⟩ : Q) pd.q := by
    have h := pd.hqn
    show (0 : Int) * (pd.q.den : Int) ≤ pd.q.num * ((1 : Nat) : Int)
    push_cast; omega
  unfold Uc invSq dilRef uEv
  refine Rmul_congr (invSqrtTwoF_ofQ _ _ _ _ _ _ _ _ _ _ pd.q pd.hqd hcq hqB) ?_
  show Req (f.f (Rmul (xBand C (ofQ pd.q pd.hqd)) (clampedInv C.a C.han C.had t)))
           (f.f (Rmul (ofQ pd.q pd.hqd) (clampedInv C.a C.han C.had t)))
  exact f.hfc _ _ (Rmul_congr (qBandQ_eq_of_band (Rle_ofQ_ofQ _ _ hq0) (Rle_ofQ_ofQ _ _ hqS)) (Req_refl _))

/-- The active prime scales `m+1` and `1/(m+1)` (`m < X`) lie in the canonical band and below `S`. -/
theorem placeData_in_band (C : NormCtx) (m : Nat) (hm : m < C.X) : ∀ side,
    Qle (canonC C) (placeData C m side).q ∧ Qle (placeData C m side).q (canonB C) ∧ Qle (placeData C m side).q C.S
  | 0 => by
      have hqB : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (canonB C) := by
        show ((m + 1 : Nat) : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
        push_cast; omega
      have hq1 : Qle (⟨1, 1⟩ : Q) (⟨((m + 1 : Nat) : Int), 1⟩ : Q) := by
        show (1 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int)
        push_cast; omega
      exact ⟨Qle_trans (by decide) (canonC_le_one C) hq1, hqB, Qle_trans (canonB_den C) hqB C.hTS⟩
  | (_ + 1) => by
      have hmB : Qle (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (canonB C) := by
        show ((m + 1 : Nat) : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
        push_cast; omega
      have hq1 : Qle (⟨1, m + 1⟩ : Q) (⟨1, 1⟩ : Q) := by
        show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((m + 1 : Nat) : Int)
        push_cast; omega
      refine ⟨?_, Qle_trans (by decide) hq1 (canonB_one C), Qle_trans (by decide) hq1 C.hS1⟩
      exact Qinv_antitone (canonB_num C) (Int.ofNat_pos.mpr (Nat.succ_pos m)) hmB

/-- **★ Every active prime evaluation is the rational-scale restriction of the one field**:
    `U_{q_{m,side}}(f,t) = q^{-1/2}·u_{m,side}(f)(t)`. -/
theorem Uc_placeData (C : NormCtx) (m side : Nat) (hm : m < C.X) (f : L2Test) (t : Real) :
    Req (Uc C (ofQ (placeData C m side).q (placeData C m side).hqd) f t)
        (Rmul (normWeight (placeData C m side).q) (uEv C (placeData C m side) f t)) :=
  Uc_ofQ_eq_normWeight_uEv C (placeData C m side) (placeData_in_band C m hm side).1
    (placeData_in_band C m hm side).2.1 (placeData_in_band C m hm side).2.2 f t

/-- The Λ-weight of a place/side without the `q^{-1/2}`: `Λ(m+1)`, resp. `Λ(m+1)·(m+1)^{-1}`. -/
def lamW (m : Nat) : Nat → Real
  | 0 => vonMangoldt (m + 1)
  | (_ + 1) => Rmul (vonMangoldt (m + 1)) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))

theorem placeKappa_eq_lamW (C : NormCtx) (m : Nat) : ∀ side,
    placeKappa C m side = Rmul (lamW m side) (normWeight (placeData C m side).q)
  | 0 => rfl
  | (_ + 1) => rfl

/-- **The prime term in the coherent scale field**: `κ·(u_f v_g + v_f u_g) = Λ·(U_q(f)V(g) + V(f)U_q(g))`. -/
theorem prime_coherent (C : NormCtx) (m side : Nat) (hm : m < C.X) (f g : L2Test) (t : Real) :
    Req (Rmul (placeKappa C m side)
          (Radd (Rmul (uEv C (placeData C m side) f t) (vEv C g t)) (Rmul (vEv C f t) (uEv C (placeData C m side) g t))))
        (Rmul (lamW m side)
          (Radd (Rmul (Uc C (ofQ (placeData C m side).q (placeData C m side).hqd) f t) (Vc C g t))
                (Rmul (Vc C f t) (Uc C (ofQ (placeData C m side).q (placeData C m side).hqd) g t)))) := by
  rw [placeKappa_eq_lamW]
  refine Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) ?_)
  refine Req_trans (Rmul_distrib _ _ _) (Radd_congr ?_ ?_)
  · refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Req_symm (Uc_placeData C m side hm f t)) (Req_refl _))
  · refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_)
    exact Rmul_congr (Req_refl _) (Req_symm (Uc_placeData C m side hm g t))

end UOR.Bridge.F1Square.Square
