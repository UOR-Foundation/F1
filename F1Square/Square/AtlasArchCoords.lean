/-
F1 square — **the readbacks of `F⁺(x)`, `F⁺(1)` and `N⁺(x)` through the raw scale field**
(`AtlasArchCoords.lean`).  With the target-free coordinates of `AtlasScaleField`:

    `F⁺_{f,g}(x) = x^{-1/2}·w·∫₀¹ crossInt`                     (`FCanon_f_eq`, definitional),
    `F⁺_{f,g}(1) = w·∫₀¹ V(f)V(g)/max(t,a)`                      (`FCanon_one_eq`),
    `N⁺(x) = w·∫₀¹ [D_x(f)V(g) + V(f)D_x(g)]/max(t,a)`  ∀ real `x`   (`archNumC_endpoint_defect`).

The `x = 1` cancellation lives INSIDE `D_x` (`D_1 = 0`), so the subtraction tail is a defect of the
single-test coordinate, not a separate two-test term.  This is the readback (target-side) module.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasScaleField
import F1Square.Square.WeilArchNumC
import F1Square.Square.WeilCrossFTwo

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

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
