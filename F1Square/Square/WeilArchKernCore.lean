/-
F1 square — **the unsplit archimedean kernel, target-free** (`WeilArchKernCore.lean`): the inner map
`x ↦ x − 1/max(x,1)` (2-Lipschitz), the full kernel `K_c(x) = 1/max(x − 1/max(x,1), c)` as an `L2Test`,
and `y·(1/max(y,1)) = 1` for `y ≥ 1`.  Split out of `WeilArchKern`/`WeilMellinPole` so that the Atlas
fibers and the source Gram can use the kernel without importing the closed Weil form.  Only the
source layer below `ClosedWeilBilin` is imported.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchNear

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The inner map `x ↦ x − 1/max(x,1)` (2-Lipschitz) and the full kernel.
-- ===========================================================================

/-- `x − 1/max(x,1)`. -/
def innerXm (x : Real) : Real := Rsub x (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)

theorem innerXm_congr {x y : Real} (h : Req x y) : Req (innerXm x) (innerXm y) :=
  Rsub_congr h (clampedInv_congr _ _ _ h)

/-- `|innerXm x − innerXm y| ≤ 2·|x − y|`. -/
theorem innerXm_lip (x y : Real) :
    Rle (Rabs (Rsub (innerXm x) (innerXm y))) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (Rabs (Rsub x y))) := by
  have hone : Req (ofQ (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q)))
        (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide)))) one :=
    Req_of_seq_Qeq (fun _ => by
      show Qeq (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (⟨1, 1⟩ : Q); decide)
  -- (x − u) − (y − v) = (x − y) − (u − v)
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_sub_sub _ _ _ _))) ?_
  refine Rle_trans (Rle_trans (Rabs_Radd _ _) (Radd_le_add (Rle_refl _) (Rle_of_Req (Rabs_Rneg _)))) ?_
  refine Rle_trans (Radd_le_add (Rle_refl _)
    (Rle_trans (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide) x y)
      (Rle_of_Req (Req_trans (Rmul_congr hone (Req_refl _)) (Rone_mul _))))) ?_
  exact Rle_of_Req (Req_symm (Rmul_two_eq_add _))

/-- **THE FULL KERNEL** `1/max(x − 1/max(x,1), c)` — an `L2Test`; `= 1/(x − x⁻¹)` on `x − 1 ≥ c`. -/
def archKernFull (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) : L2Test where
  f := fun x => clampedInv c hcn hcd (innerXm x)
  L := mul (mul (Qinv c) (Qinv c)) (⟨2, 1⟩ : Q)
  M := Qinv c
  hLd := Qmul_den_pos (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn)) Nat.one_pos
  hLn := Int.mul_nonneg (Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos hcd)) (Int.le_of_lt (Qinv_num_pos hcd)))
    (show (0 : Int) ≤ 2 by decide)
  hMd := Qinv_den_pos hcn
  hMn := Int.le_of_lt (Qinv_num_pos hcd)
  hlip := fun x y => by
    refine Rle_trans (clampedInv_lipschitz c hcn hcd (innerXm x) (innerXm y)) ?_
    refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos hcd))
      (Int.le_of_lt (Qinv_num_pos hcd)))) (innerXm_lip x y)) ?_
    refine Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
    exact Rmul_congr (Rmul_ofQ_ofQ _ _) (Req_refl _)
  hfc := fun x y h => clampedInv_congr c hcn hcd (innerXm_congr h)
  hbd := fun x =>
    Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_clampedInv c hcn hcd (innerXm x))))
      (Rinv_le_ofQ_inv hcn hcd (qClampQ_witness c hcn hcd (innerXm x))
        (Rle_ofQ_qClampQ c hcd (innerXm x)))

theorem archKernFull_f (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) :
    (archKernFull c hcn hcd).f x = clampedInv c hcn hcd (innerXm x) := rfl

/-- `y·(1/y) = 1` with the clamped reciprocal, for `y ≥ 1`. -/
theorem Rmul_clampedInv_one (y : Real) (hy1 : Rle one y) :
    Req (Rmul y (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) y)) one := by
  obtain ⟨ky, hky⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hy1
  exact Req_trans (Rmul_congr (Req_refl _) (clampedInv_eq_of_ge hky hy1)) (Rmul_Rinv_self hky)

end UOR.Bridge.F1Square.Square
