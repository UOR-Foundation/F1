/-
F1 square — **the raw single-test archimedean coordinates and THE ENDPOINT-DEFECT IDENTITY**
(`AtlasArchCoords.lean`).

The archimedean numerator of the coupled Weil form is `N⁺(x) = F⁺_{f,g}(x) + F⁺_{g,f}(x) − 2F⁺_{f,g}(1)/x`
(`archNumC`), a TWO-TEST output.  Following the directive, it is re-expressed through RAW SINGLE-TEST
coordinates of the window variable `t`, exactly as the code realizes `F⁺` (`FCanon = FTwo`, the
two-sided `x^{-1/2}` clamp `invSqrtTwoF`, the `[0,S]` band clamp of the real scale, the Haar window):

    `U_x(f,t) = x^{-1/2} · f(x / max(t,a))`      (`Uc`),
    `V(f,t)   = f(1 / max(t,a))`                  (`Vc`),
    `D_x(f,t) = U_x(f,t) − (1/max(x,1)) · V(f,t)`   (`Dc`),

and THE RAW ENDPOINT-DEFECT IDENTITY — pointwise in `t` for every real `x`:

    `U_x(f)V(g) + V(f)U_x(g) − 2·(1/x)·V(f)V(g) = D_x(f)V(g) + V(f)D_x(g)`   (`endpoint_defect_pt`),

lifted to the numerator through the certified Haar integrals (`archNumC_endpoint_defect`):

    `N⁺(x) = w·∫₀¹ [D_x(f)V(g) + V(f)D_x(g)]·(1/max(t,a)) dt(x)`   for every real `x`.

The `x = 1` cancellation lives INSIDE `D_x` (`D_1(f,t) = 0` up to the clamps: `U_1 = V`), so the
subtraction tail is a defect of the single-test coordinate, not a separate two-test term.  Nothing
here builds a fiber, a measure, or a form; the pole side (`+PoleForm`, measure `2·poleDens`) and the
tail side (`−ArchTail`, kernel `1/(x−1) + 1/(x+1)`) are consumed by fibers in the next file.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasPrimeDirect
import F1Square.Square.WeilArchNumC

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
-- (3) The readbacks of `F⁺(x)` and `F⁺(1)` through the raw coordinates.
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

/-- **`F⁺_{f,g}(x) = x^{-1/2} · w · ∫₀¹ crossInt`** (definitional: `FCanon → FTwo → productTest →
    HcrossTest → mulConvRTest → mulConvR → haarIntegral → innerIonI → riemannIntegralI`). -/
theorem FCanon_f_eq (C : NormCtx) (x : Real) (f g : L2Test) :
    (FCanon C f g).f x
      = Rmul (invSq C x) (Rmul (ofQ C.w C.hw)
          (riemannIntegral (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g) (crossInt_fc C x f g))) := by
  show Rmul (invSq C x) ((HcrossTest f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn).f x) = _
  rw [HcrossTest_f]
  show Rmul (invSq C x) (haarIntegral (productTest (dilRef C x f) (reflectTest C.a C.han C.had g))
    C.a C.han C.had C.a C.w C.had C.hw C.hwn) = _
  unfold haarIntegral innerIonI riemannIntegralI
  rfl

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

/-- **`F⁺_{f,g}(1) = w · ∫₀¹ V(f)V(g)·(1/max(t,a))`** — via the two-sided rational readback at `q = 1`
    (`FTwo_ofQ`), `1^{-1/2} = 1`, and `f(1·y) = f(y)`. -/
theorem FCanon_one_eq (C : NormCtx) (f g : L2Test) :
    Req ((FCanon C f g).f one)
        (Rmul (ofQ C.w C.hw) (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g))) := by
  have h := FTwo_ofQ (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C) (canonB_one C)
    (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C) f g C.S C.hSd C.hSn
    C.a C.han C.had C.w C.hw C.hwn (⟨1, 1⟩ : Q) Nat.one_pos (canonC_le_one C) (canonB_one C) C.hS1
  refine Req_trans h ?_
  show Req (Rmul (normWeight (⟨1, 1⟩ : Q)) (HForm f g pdOne.q pdOne.hqn pdOne.hqd C.a C.han C.had C.w C.hw C.hwn)) _
  rw [HForm_unfold C pdOne f g]
  have hnw : Req (normWeight (⟨1, 1⟩ : Q)) one :=
    Req_trans (normWeight_pos_eq (show (0 : Int) < 1 by decide)) Rsqrt_one
  refine Req_trans (Rmul_congr hnw (Req_refl _)) (Req_trans (Rone_mul _) (Rmul_congr (Req_refl _) ?_))
  have hlipV : ∀ y z, Rle (Rabs (Rsub (vvInt C f g y) (vvInt C f g z)))
      (Rmul (ofQ (hIntL C pdOne f g) (hIntL_den C pdOne f g)) (Rabs (Rsub y z))) :=
    lip_of_congr_pd _ (fun y => Req_symm (hInt_one_eq_vv C f g y)) (hInt_lip C pdOne f g)
  refine Req_trans (riemannIntegral_congr (hIntL_den C pdOne f g) (hIntL_num C pdOne f g) (hInt_lip C pdOne f g)
    (hInt_fc C pdOne f g) hlipV (vvInt_fc C f g) (hInt_one_eq_vv C f g)) ?_
  exact riemannIntegral_certif_irrel _ _ hlipV _ (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)

-- ===========================================================================
-- (4) ★ THE ENDPOINT-DEFECT IDENTITY FOR THE NUMERATOR `N⁺(x)`.
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

/-- **★ THE RAW ENDPOINT-DEFECT IDENTITY FOR THE NUMERATOR**: for every real `x`,
    `N⁺(x) = F⁺_{f,g}(x) + F⁺_{g,f}(x) − 2F⁺_{f,g}(1)/max(x,1) = w · ∫₀¹ [D_x(f)V(g) + V(f)D_x(g)]·(1/max(t,a))`. -/
theorem archNumC_endpoint_defect (C : NormCtx) (f g : L2Test) (x : Real) :
    Req ((archNumC C f g).f x) (Rmul (ofQ C.w C.hw) (defectIntegral C x f g)) := by
  rw [archNumC_f, FCanon_f_eq, FCanon_f_eq]
  have hone := FCanon_one_eq C f g
  refine Req_trans (Radd_congr (Radd_congr (swap_w_ac _ _ _) (swap_w_ac _ _ _))
    (Rneg_congr (Req_trans (Rmul_congr (Rmul_congr (Req_refl _) hone) (Req_refl _)) (two_w_ac _ _ _)))) ?_
  refine Req_trans (Radd_congr (Req_symm (Rmul_distrib _ _ _)) (Req_symm (Rmul_neg_right _ _))) ?_
  refine Req_trans (Req_symm (Rmul_distrib _ _ _)) (Rmul_congr (Req_refl _) ?_)
  refine Req_trans (Req_symm (integral_asm C x f g)) ?_
  unfold defectIntegral
  exact riemannIntegral_congr (asmL_den C x f g) (asmL_num C x f g) (asmInt_lip C x f g) (asmInt_fc C x f g)
    (defInt_lip C x f g) (defInt_fc C x f g) (asmInt_eq_defInt C x f g)

end UOR.Bridge.F1Square.Square
