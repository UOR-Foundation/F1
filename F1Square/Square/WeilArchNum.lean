/-
F1 square — **the archimedean-tail numerator and kernels** (`WeilArchNum.lean`): the certified
integrand pieces of `ArchTailForm(f,g) = ∫₁^∞ (F_{f,g}+F_{g,f}−2F_{f,g}(1)/x)/(x−x⁻¹) dx`.

The kernel is split by partial fractions, `1/(x−x⁻¹) = x/(x²−1) = ½·(1/(x−1) + 1/(x+1))` (an exact
identity on `x > 1`), so the tail decomposes into a REGULAR part (kernel `1/(x+1)`, bounded), a
NEAR-singular part (kernel `1/(x−1)` on `[1+ε, 2]`, treated by the proved lower-end improper limit),
and a FAR part (`∫₂^∞`, realized as `∫₁^∞ N(u+1)/u du`).  This file builds the pieces:

  • `archNum G f g` — THE NUMERATOR `N(x) = F_{f,g}(x) + F_{g,f}(x) − 2·F_{f,g}(1)·(1/max(x,1))`
    as an `L2Test` (on `[1,∞)` the clamp is inert, so this is the CC subtracted numerator, with its
    non-truncatable `−2F(1)/x` tail RETAINED).
  • `archNum_one_zero` — `N(1) ≈ 0`: the endpoint vanishing (from the PROVEN value-at-1 symmetry
    `FTest_one_symm` and `2F(1) = F(1)+F(1)`), the datum that makes `x = 1` a removable singularity.
  • `archNum_abs_le_dist_one` — `|N(x)| ≤ N.L·|x−1|`: the numerator's vanishing RATE at the endpoint
    (Lipschitz against `N(1) ≈ 0`) — the bound the improper `x = 1` limit consumes.  Lipschitz
    regularity is used ONLY to bound the numerator; no value is invented at the singular point.
  • `archNum_past` — past the support bound the numerator IS the retained tail:
    `N(x) ≈ −2F(1)·(1/max(x,1))` for real `x ≥ Bd`.
  • `archKernNear c` — the near kernel `1/max(x−1, c)` (`= 1/(x−1)` on `x ≥ 1+c`), per-`ε` certified.
  • `archKernReg` — the regular kernel `1/max(x+1, 2)` (`= 1/(x+1)` on `x ≥ 1`), globally certified.
  • `archShiftNum` — the shifted numerator `u ↦ N(u+1)` (the far part's integrand factor).
  • `clampedInv_le_ofQ_inv_of_ge` / `Rle_self_qClampQ` — clamp bounds the decay estimates consume.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPoleForm

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) Shift isometries and clamp bounds.
-- ===========================================================================

/-- `(x−1) − (y−1) ≈ x − y` (translation isometry, subtracted form). -/
theorem sub_shift_iso (x y : Real) :
    Req (Rsub (Rsub x one) (Rsub y one)) (Rsub x y) :=
  Req_trans (Rsub_Radd_Radd x (Rneg one) y (Rneg one))
    (Req_trans (Radd_congr (Req_refl (Rsub x y)) (Radd_neg (Rneg one))) (Radd_zero (Rsub x y)))

/-- `(x+1) − (y+1) ≈ x − y` (translation isometry, added form). -/
theorem add_shift_iso (x y : Real) :
    Req (Rsub (Radd x one) (Radd y one)) (Rsub x y) :=
  Req_trans (Rsub_Radd_Radd x one y one)
    (Req_trans (Radd_congr (Req_refl (Rsub x y)) (Radd_neg one)) (Radd_zero (Rsub x y)))

/-- `x ≤ max(x, a)` at the `Real` level. -/
theorem Rle_self_qClampQ (a : Q) (had : 0 < a.den) (x : Real) :
    Rle x (qClampQ a had x) := fun n =>
  Qle_trans (Qmax_den_pos (x.den_pos n) had) (Qmax_ge_left (x.seq n) a)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **The clamp-reciprocal cap over a real threshold**: `x ≥ c > 0` gives
    `1/max(x, c') ≤ 1/c` (any positive clamp floor `c'`). -/
theorem clampedInv_le_ofQ_inv_of_ge {c' : Q} (hc'n : 0 < c'.num) (hc'd : 0 < c'.den)
    {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) {x : Real} (hx : Rle (ofQ c hcd) x) :
    Rle (clampedInv c' hc'n hc'd x) (ofQ (Qinv c) (Qinv_den_pos hcn)) :=
  Rinv_le_ofQ_inv hcn hcd (qClampQ_witness c' hc'n hc'd x)
    (Rle_trans hx (Rle_self_qClampQ c' hc'd x))

-- ===========================================================================
-- (1) The numerator `N(x) = F_{f,g}(x) + F_{g,f}(x) − 2F_{f,g}(1)·(1/max(x,1))`.
-- ===========================================================================

/-- The constant `2·F_{f,g}(1)` is bounded by `2·M` — the `constTest` certificate. -/
theorem twoFone_bound (G : ClosedGeom) (f g : L2Test) :
    Rle (Rabs (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one)))
        (ofQ (mul (⟨2, 1⟩ : Q) (FTestG G f g).M)
          (Qmul_den_pos (by decide) (FTestG G f g).hMd)) := by
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Rabs_ofQ (by decide)) (Req_refl _))) ?_
  refine Rle_trans (Rmul_le_Rmul_left
    (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 2; decide)) ((FTestG G f g).hbd one)) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ (by decide) (FTestG G f g).hMd)

/-- **THE ARCHIMEDEAN NUMERATOR** `N(x) = F_{f,g}(x) + F_{g,f}(x) − 2·F_{f,g}(1)·(1/max(x,1))` as
    an `L2Test` — on `[1,∞)` the clamp is inert, so this is the CC subtracted numerator with the
    `−2F(1)/x` tail RETAINED past the support boundary. -/
def archNum (G : ClosedGeom) (f g : L2Test) : L2Test :=
  L2Test.sub (L2Test.add (FTestG G f g) (FTestG G g f))
    (L2Test.mul
      (constTest (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one))
        (mul (⟨2, 1⟩ : Q) (FTestG G f g).M)
        (Qmul_den_pos (by decide) (FTestG G f g).hMd)
        (Int.mul_nonneg (by show (0 : Int) ≤ 2; decide) (FTestG G f g).hMn)
        (twoFone_bound G f g))
      (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)))

/-- The numerator's value unfolds (readback shape). -/
theorem archNum_f (G : ClosedGeom) (f g : L2Test) (x : Real) :
    (archNum G f g).f x
      = Radd (Radd ((FTestG G f g).f x) ((FTestG G g f).f x))
          (Rneg (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one))
            (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) := rfl

/-- **`N(1) ≈ 0`** — the endpoint vanishing: `1/max(1,1) = 1`, `2F(1) = F(1)+F(1)`, and
    `F_{g,f}(1) ≈ F_{f,g}(1)` (the PROVEN value-at-1 symmetry). -/
theorem archNum_one_zero (G : ClosedGeom) (f g : L2Test) :
    Req ((archNum G f g).f one) zero := by
  rw [archNum_f]
  -- the subtracted term at 1: 2F(1)·(1/max(1,1)) ≈ 2F(1) ≈ F(1)+F(1)
  have hclamp : Req (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) one) one :=
    clampedInv_ofQ (by decide) (by decide) (by decide) (by decide) (Qle_refl _)
  have hsub : Req (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one))
        (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) one))
      (Radd ((FTestG G f g).f one) ((FTestG G f g).f one)) :=
    Req_trans (Rmul_congr (Req_refl _) hclamp)
      (Req_trans (Rmul_one _) (Rmul_two_eq_add ((FTestG G f g).f one)))
  -- the added term at 1: F(1) + F♯(1) ≈ F(1) + F(1)
  have hadd : Req (Radd ((FTestG G f g).f one) ((FTestG G g f).f one))
      (Radd ((FTestG G f g).f one) ((FTestG G f g).f one)) :=
    Radd_congr (Req_refl _) (Req_symm (FTestG_one_symm G f g))
  refine Req_trans (Radd_congr hadd (Rneg_congr hsub)) ?_
  exact Radd_neg (Radd ((FTestG G f g).f one) ((FTestG G f g).f one))

/-- **The endpoint vanishing RATE**: `|N(x)| ≤ N.L·|x−1|` — the numerator's Lipschitz modulus
    against `N(1) ≈ 0`.  (Lipschitz only BOUNDS the numerator; no value at the singular point is
    invented — the `x = 1` treatment is the improper limit.) -/
theorem archNum_abs_le_dist_one (G : ClosedGeom) (f g : L2Test) (x : Real) :
    Rle (Rabs ((archNum G f g).f x))
        (Rmul (ofQ (archNum G f g).L (archNum G f g).hLd) (Rabs (Rsub x one))) := by
  have hshift : Req ((archNum G f g).f x) (Rsub ((archNum G f g).f x) ((archNum G f g).f one)) :=
    Req_symm (Req_trans (Rsub_congr (Req_refl _) (archNum_one_zero G f g))
      (Rsub_zero ((archNum G f g).f x)))
  exact Rle_trans (Rle_of_Req (Rabs_congr hshift)) ((archNum G f g).hlip x one)

/-- **Past the support bound the numerator IS the retained tail**:
    `N(x) ≈ −2F_{f,g}(1)·(1/max(x,1))` for real `x ≥ Bd`. -/
theorem archNum_past (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g)
    (x : Real) (hx : Rle (ofQ G.Bd G.hBdd) x) :
    Req ((archNum G f g).f x)
        (Rneg (Rmul (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one))
          (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) := by
  rw [archNum_f]
  refine Req_trans (Radd_congr
    (Req_trans (Radd_congr (FTestG_high_vanish G f g hf x hx)
      (FTestG_high_vanish G g f hg x hx)) (Radd_zero zero)) (Req_refl _)) ?_
  exact Req_trans (Radd_comm zero _) (Radd_zero _)

-- ===========================================================================
-- (2) The kernels.
-- ===========================================================================

/-- **The near kernel** `1/max(x−1, c)` (`= 1/(x−1)` on `x ≥ 1+c`) — the per-`ε` certified
    singular factor of the `x = 1` improper limit. -/
def archKernNear (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) : L2Test where
  f := fun x => clampedInv c hcn hcd (Rsub x one)
  L := mul (Qinv c) (Qinv c)
  M := Qinv c
  hLd := Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn)
  hLn := Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos hcd)) (Int.le_of_lt (Qinv_num_pos hcd))
  hMd := Qinv_den_pos hcn
  hMn := Int.le_of_lt (Qinv_num_pos hcd)
  hlip := fun x y =>
    Rle_trans (clampedInv_lipschitz c hcn hcd (Rsub x one) (Rsub y one))
      (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_congr (sub_shift_iso x y))))
  hfc := fun x y h => clampedInv_congr c hcn hcd (Rsub_congr h (Req_refl one))
  hbd := fun x =>
    Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_clampedInv c hcn hcd (Rsub x one))))
      (Rinv_le_ofQ_inv hcn hcd (qClampQ_witness c hcn hcd (Rsub x one))
        (Rle_ofQ_qClampQ c hcd (Rsub x one)))

/-- **The regular kernel** `1/max(x+1, 2)` (`= 1/(x+1)` on `x ≥ 1`) — bounded, no singularity. -/
def archKernReg : L2Test where
  f := fun x => clampedInv (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd x one)
  L := mul (Qinv (⟨2, 1⟩ : Q)) (Qinv (⟨2, 1⟩ : Q))
  M := Qinv (⟨2, 1⟩ : Q)
  hLd := Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide))
  hLn := Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos (by decide)))
    (Int.le_of_lt (Qinv_num_pos (by decide)))
  hMd := Qinv_den_pos (by decide)
  hMn := Int.le_of_lt (Qinv_num_pos (by decide))
  hlip := fun x y =>
    Rle_trans (clampedInv_lipschitz (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd x one) (Radd y one))
      (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_congr (add_shift_iso x y))))
  hfc := fun x y h =>
    clampedInv_congr (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd_congr h (Req_refl one))
  hbd := fun x =>
    Rle_trans (Rle_of_Req (Rabs_of_nonneg
      (Rnonneg_clampedInv (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd x one))))
      (Rinv_le_ofQ_inv (by decide) (by decide)
        (qClampQ_witness (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd x one))
        (Rle_ofQ_qClampQ (⟨2, 1⟩ : Q) (by decide) (Radd x one)))

/-- **The shifted numerator** `u ↦ N(u+1)` — the far part's integrand factor
    (`∫₂^∞ N(x)/(x−1) dx = ∫₁^∞ N(u+1)/u du`). -/
def archShiftNum (G : ClosedGeom) (f g : L2Test) : L2Test where
  f := fun u => (archNum G f g).f (Radd u one)
  L := (archNum G f g).L
  M := (archNum G f g).M
  hLd := (archNum G f g).hLd
  hLn := (archNum G f g).hLn
  hMd := (archNum G f g).hMd
  hMn := (archNum G f g).hMn
  hlip := fun x y =>
    Rle_trans ((archNum G f g).hlip (Radd x one) (Radd y one))
      (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_congr (add_shift_iso x y))))
  hfc := fun x y h => (archNum G f g).hfc _ _ (Radd_congr h (Req_refl one))
  hbd := fun u => (archNum G f g).hbd (Radd u one)

-- Seal the deep definitional towers (elaborator whnf economy; in-file defeq uses are above).
attribute [irreducible] archNum

end UOR.Bridge.F1Square.Square
