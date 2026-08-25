/-
F1 square — **the archimedean numerator from the two-sided correlation** (`WeilArchNumC.lean`):

    `N⁺(x) = F⁺_{f,g}(x) + F⁺_{g,f}(x) − 2·F⁺_{f,g}(1)·(1/max(x,1))`   (`archNumC`)

built from `FCanon` (the canonical two-sided `x^{-1/2}`-normalized correlation), and its agreement
with the one-sided numerator `archNum C.geom f g` at EVERY real `x ≥ 1` (`archNumC_eq_archNum`):
on `x ≥ 1` both weights are the same clamped-band root (`twoRad_eq_isqRad_ge_one` — no upper bound
needed: the band cap is common), so `F⁺ = F` there (`FCanon_eq_FTestG_ge_one`).  The vanishing
`N⁺(1) = 0`, the vanishing RATE `|N⁺(x)| ≤ L·|x−1|`, and the retained-tail bound past the support
transfer accordingly.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchKern

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The two weights agree on all of `x ≥ 1`.
-- ===========================================================================

/-- `a ≤ band_{[a,b]}(x)` at the real level (`a ≤ b`). -/
theorem Rle_ofQ_qBandQ (a b : Q) (had : 0 < a.den) (hbd : 0 < b.den) (hab : Qle a b) (x : Real) :
    Rle (ofQ a had) (qBandQ a b had hbd x) := fun n =>
  Qle_trans ((qBandQ a b had hbd x).den_pos n) (qBandQ_ge a b had hbd hab x n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- On `x ≥ 1` the two-sided and one-sided radicands agree (the low clamps are inert, the band cap
    is common, and the value is `≥ 1` so both reciprocal clamps are inert). -/
theorem twoRad_eq_isqRad_ge_one (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hc1 : Qle c (⟨1, 1⟩ : Q)) (hB1 : Qle (⟨1, 1⟩ : Q) B) (x : Real) (hx1 : Rle one x) :
    Req (twoRad c B hcn hcd hBd x) (isqRad B hBd x) := by
  have hcx : Rle (ofQ c hcd) x := Rle_trans (Rle_ofQ_ofQ hcd (by decide) hc1) hx1
  have hb : Req (twoBand c B hcd hBd x) (isqBand B hBd x) := by
    show Req (qCapQ B hBd (qClampQ c hcd x)) (qCapQ B hBd (qClampQ (⟨1, 1⟩ : Q) (by decide) x))
    exact Req_trans (qCapQ_congr B hBd (qClampQ_eq_of_ge hcx))
      (Req_symm (qCapQ_congr B hBd (qClampQ_eq_of_ge hx1)))
  have hy1 : Rle one (isqBand B hBd x) := Rle_ofQ_qBandQ (⟨1, 1⟩ : Q) B (by decide) hBd hB1 x
  have hyc : Rle (ofQ c hcd) (isqBand B hBd x) := Rle_trans (Rle_ofQ_ofQ hcd (by decide) hc1) hy1
  obtain ⟨ky, hky⟩ := Pos_of_Rle_ofQ hcn hcd hyc
  refine Req_trans (clampedInv_congr c hcn hcd hb) ?_
  refine Req_trans (clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hky hyc) ?_
  exact Req_symm (clampedInv_eq_of_ge (a := (⟨1, 1⟩ : Q)) (han := by decide) (had := by decide) hky hy1)

/-- On `x ≥ 1` the two weights agree: `invSqrtTwoF x ≈ invSqrtF x`. -/
theorem invSqrtTwoF_eq_ge_one (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) (hx1 : Rle one x) :
    Req (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) (invSqrtF B hBd hB1 N hN hBN x) :=
  RsqrtRealPos_unique (isqRad B hBd x) N hN (isqRad_scale B hBd hB1 N hN hBN x)
    (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x)
    (Req_trans (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x)
      (twoRad_eq_isqRad_ge_one c B hcn hcd hBd hc1 hB1 x hx1))

/-- **`F⁺ = F` on all of `x ≥ 1`** (canonical band). -/
theorem FCanon_eq_FTestG_ge_one (C : NormCtx) (f g : L2Test) (x : Real) (hx1 : Rle one x) :
    Req ((FCanon C f g).f x) ((FTestG C.geom f g).f x) := by
  rw [FTestG_geom_f, FTest_f]
  show Req (Rmul (invSqrtTwoF (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
      (canonB_one C) (canonC_le_B C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C) x)
      ((HcrossTest f g C.S C.hSd C.hSn C.a C.han C.had C.w C.hw C.hwn).f x)) _
  exact Rmul_congr (invSqrtTwoF_eq_ge_one (canonC C) (canonB C) (canonC_num C) (canonC_den C)
    (canonB_den C) (canonB_one C) (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X)
    (canonB_le_N C) x hx1) (Req_refl _)

-- ===========================================================================
-- (2) The numerator `N⁺` from `F⁺`.
-- ===========================================================================

theorem twoFoneC_bound (C : NormCtx) (f g : L2Test) :
    Rle (Rabs (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FCanon C f g).f one)))
        (ofQ (mul (⟨2, 1⟩ : Q) (FCanon C f g).M)
          (Qmul_den_pos (by decide) (FCanon C f g).hMd)) := by
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Rabs_ofQ (by decide)) (Req_refl _))) ?_
  refine Rle_trans (Rmul_le_Rmul_left
    (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 2; decide)) ((FCanon C f g).hbd one)) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (FCanon C f g).hMd)

/-- **THE NUMERATOR FROM `F⁺`** `N⁺(x) = F⁺_{f,g}(x) + F⁺_{g,f}(x) − 2·F⁺_{f,g}(1)·(1/max(x,1))`. -/
def archNumC (C : NormCtx) (f g : L2Test) : L2Test :=
  L2Test.sub (L2Test.add (FCanon C f g) (FCanon C g f))
    (L2Test.mul
      (constTest (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FCanon C f g).f one))
        (mul (⟨2, 1⟩ : Q) (FCanon C f g).M)
        (Qmul_den_pos (by decide) (FCanon C f g).hMd)
        (Int.mul_nonneg (by show (0 : Int) ≤ 2; decide) (FCanon C f g).hMn)
        (twoFoneC_bound C f g))
      (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)))

theorem archNumC_f (C : NormCtx) (f g : L2Test) (x : Real) :
    (archNumC C f g).f x
      = Radd (Radd ((FCanon C f g).f x) ((FCanon C g f).f x))
          (Rneg (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FCanon C f g).f one))
            (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) := rfl

/-- **`N⁺ = N` on all of `x ≥ 1`** (the one-sided numerator of the constructed tail). -/
theorem archNumC_eq_archNum (C : NormCtx) (f g : L2Test) (x : Real) (hx1 : Rle one x) :
    Req ((archNumC C f g).f x) ((archNum C.geom f g).f x) := by
  rw [archNumC_f, archNum_f]
  have h1 := FCanon_eq_FTestG_ge_one C f g x hx1
  have h2 := FCanon_eq_FTestG_ge_one C g f x hx1
  have h3 := FCanon_eq_FTestG_ge_one C f g one (Rle_refl one)
  exact Radd_congr (Radd_congr h1 h2)
    (Rneg_congr (Rmul_congr (Rmul_congr (Req_refl _) h3) (Req_refl _)))

theorem archNumC_one_zero (C : NormCtx) (f g : L2Test) : Req ((archNumC C f g).f one) zero :=
  Req_trans (archNumC_eq_archNum C f g one (Rle_refl one)) (archNum_one_zero C.geom f g)

/-- The vanishing RATE `|N⁺(x)| ≤ L·|x − 1|` (Lipschitz against `N⁺(1) = 0`). -/
theorem archNumC_abs_le_dist_one (C : NormCtx) (f g : L2Test) (x : Real) :
    Rle (Rabs ((archNumC C f g).f x))
        (Rmul (ofQ (archNumC C f g).L (archNumC C f g).hLd) (Rabs (Rsub x one))) := by
  have hshift : Req ((archNumC C f g).f x) (Rsub ((archNumC C f g).f x) ((archNumC C f g).f one)) :=
    Req_symm (Req_trans (Rsub_congr (Req_refl _) (archNumC_one_zero C f g))
      (Rsub_zero ((archNumC C f g).f x)))
  exact Rle_trans (Rle_of_Req (Rabs_congr hshift)) ((archNumC C f g).hlip x one)

/-- The retained-tail bound past the support (`x ≥ c ≥ Bd`): `|N⁺(x)| ≤ K_l·(1/c)`. -/
theorem archNumC_late_bound (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (hg : CoreTest C.geom g) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den)
    (x : Real) (hx : Rle (ofQ c hcd) x) (hpast : Qle C.geom.Bd c) :
    Rle (Rabs ((archNumC C f g).f x))
        (Rmul (ofQ (archKl C.geom f g) (archKl_den C.geom f g))
              (ofQ (Qinv c) (Qinv_den_pos hcn))) := by
  have hx1 : Rle one x :=
    Rle_trans (Rle_ofQ_ofQ (by decide) hcd (Qle_trans C.geom.hBdd C.geom.hBd1 hpast)) hx
  exact Rle_trans (Rle_of_Req (Rabs_congr (archNumC_eq_archNum C f g x hx1)))
    (archNum_late_bound C.geom f g hf hg c hcn hcd x hx hpast)

-- Seal the tower (in-file defeq uses are above).
attribute [irreducible] archNumC

end UOR.Bridge.F1Square.Square
