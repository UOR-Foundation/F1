/-
F1 square — **the UNSPLIT archimedean kernel** `1/(x − x⁻¹)` (`WeilArchKern.lean`):

  • `archKernFull c` — the bounded Lipschitz representative `1/max(x − 1/max(x,1), c)` (an `L2Test`),
    inert (`= 1/(x − x⁻¹)`) on every real `x` with `x − 1 ≥ c`;
  • **THE PARTIAL-FRACTION IDENTITY on `x > 1`** (`archKernFull_partial`):
        `1/(x − x⁻¹) = ½·(1/(x−1) + 1/(x+1))`
    proved directly at the real level (both sides are the multiplicative inverse of `x − x⁻¹`;
    `(x−1)(x+1) = x·(x − x⁻¹)`), with the clamped near/regular kernels of `WeilArchNum` on the RHS;
  • the caps `(x−1)·K(x) ≤ 1` (the numerator-vanishing rate transfers to the quotient) and
    `K(x) ≤ 1/m` for `x ≥ m+1` (block decay).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilMellinPole

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

-- ===========================================================================
-- (2) Inertness on `x − 1 ≥ c`, and the caps.
-- ===========================================================================

/-- On `x ≥ 1`: `x − 1 ≤ x − 1/x` (`1/x ≤ 1`). -/
theorem sub_one_le_innerXm (x : Real) (hx1 : Rle one x) : Rle (Rsub x one) (innerXm x) := by
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx1
  have hle : Rle (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) one :=
    Rle_trans (Rle_of_Req (clampedInv_eq_of_ge hkx hx1))
      (Rle_trans (Rinv_le_ofQ_inv (a := (⟨1, 1⟩ : Q)) (by decide) (by decide) hkx hx1)
        (Rle_of_Req (Req_of_seq_Qeq (fun _ => by show Qeq (Qinv (⟨1, 1⟩ : Q)) (⟨1, 1⟩ : Q); decide))))
  exact Rsub_le_mono (Rle_refl x) hle

/-- The inner map dominates the clamp floor on `x − 1 ≥ c`. -/
theorem innerXm_ge_c (c : Q) (hcd : 0 < c.den) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ c hcd) (Rsub x one)) : Rle (ofQ c hcd) (innerXm x) :=
  Rle_trans hxc (sub_one_le_innerXm x hx1)

/-- **`(x−1)·K(x) ≤ 1`** on `x − 1 ≥ c > 0`: the quotient absorbs one power of the vanishing. -/
theorem archKernFull_cap (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ c hcd) (Rsub x one)) :
    Rle (Rmul (Rsub x one) ((archKernFull c hcn hcd).f x)) one := by
  rw [archKernFull_f]
  have hge := innerXm_ge_c c hcd x hx1 hxc
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ hcn hcd hge
  have hK : Req (clampedInv c hcn hcd (innerXm x)) (Rinv (innerXm x) ki hki) :=
    clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hki hge
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_clampedInv c hcn hcd _) (sub_one_le_innerXm x hx1)) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) hK) (Rmul_Rinv_self hki))

/-- **Block cap** `K(x) ≤ 1/m` for `x ≥ m+1` (`m ≥ 1`): `x − x⁻¹ ≥ x − 1 ≥ m`. -/
theorem archKernFull_le_inv (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (m : Nat) (hm : 1 ≤ m)
    (x : Real) (hx : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x) :
    Rle ((archKernFull c hcn hcd).f x)
        (ofQ (Qinv (⟨(m : Int), 1⟩ : Q)) (Qinv_den_pos (show (0 : Int) < (m : Int) by omega))) := by
  rw [archKernFull_f]
  have hmn : (0 : Int) < (m : Int) := by omega
  have hx1 : Rle one x := Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hx
  -- x − 1 ≥ m
  have hsub : Rle (ofQ (⟨(m : Int), 1⟩ : Q) Nat.one_pos) (Rsub x one) := by
    have hsplit : Req (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (ofQ (⟨(m : Int), 1⟩ : Q) Nat.one_pos) one) := by
      refine Req_symm (Req_trans (Radd_ofQ_ofQ Nat.one_pos (by decide)) (ofQ_congr _ _ ?_))
      simp only [Qeq, add]; push_cast; ring_uor
    have h1 : Rle (Rsub (Radd (ofQ (⟨(m : Int), 1⟩ : Q) Nat.one_pos) one) one) (Rsub x one) :=
      Rsub_le_mono (Rle_trans (Rle_of_Req (Req_symm hsplit)) hx) (Rle_refl one)
    exact Rle_trans (Rle_of_Req (Req_symm (Radd_sub_cancel_right _ _))) h1
  exact clampedInv_le_ofQ_inv_of_ge hcn hcd hmn Nat.one_pos
    (Rle_trans hsub (sub_one_le_innerXm x hx1))

-- ===========================================================================
-- (3) THE PARTIAL-FRACTION IDENTITY on `x − 1 ≥ c`:
--     `1/(x − x⁻¹) = ½·(1/(x−1) + 1/(x+1))`.
-- ===========================================================================

/-- `x·(x − x⁻¹) = (x−1)(x+1)` for real `x ≥ 1`. -/
theorem innerXm_mul (x : Real) (hx1 : Rle one x) :
    Req (Rmul x (innerXm x)) (Rmul (Rsub x one) (Radd x one)) := by
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx1
  have hc : Req (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) (Rinv x kx hkx) :=
    clampedInv_eq_of_ge hkx hx1
  -- x·(x − u) = x·x − x·u = x·x − 1;  (x−1)(x+1) = x·x + x − x − 1 = x·x − 1
  have hL : Req (Rmul x (innerXm x)) (Rsub (Rmul x x) one) := by
    show Req (Rmul x (Rsub x (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))) _
    refine Req_trans (Rmul_sub_distrib _ _ _) ?_
    exact Rsub_congr (Req_refl _) (Req_trans (Rmul_congr (Req_refl _) hc) (Rmul_Rinv_self hkx))
  have hR : Req (Rmul (Rsub x one) (Radd x one)) (Rsub (Rmul x x) one) :=
    Req_trans (Rmul_sub_add_self x one) (Rsub_congr (Req_refl _) (Rone_mul one))
  exact Req_trans hL (Req_symm hR)

/-- Abstract algebra: if `(x−1)·a = 1`, `(x+1)·b = 1`, `x·I = (x−1)(x+1)` and `x·xi = 1`, then
    `(a + b)·I = 2`. -/
theorem inv_sum_mul_two (x a b I xi : Real)
    (ha : Req (Rmul (Rsub x one) a) one) (hb : Req (Rmul (Radd x one) b) one)
    (hxI : Req (Rmul x I) (Rmul (Rsub x one) (Radd x one))) (hxi : Req (Rmul x xi) one) :
    Req (Rmul (Radd a b) I) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) := by
  -- a·((x−1)(x+1)) = x+1
  have ha' : Req (Rmul a (Rmul (Rsub x one) (Radd x one))) (Radd x one) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) ha) (Req_refl _)) (Rone_mul _))
  -- b·((x−1)(x+1)) = x−1
  have hb' : Req (Rmul b (Rmul (Rsub x one) (Radd x one))) (Rsub x one) := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) ?_
    exact Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Req_trans (Rmul_congr (Req_trans (Rmul_comm _ _) hb) (Req_refl _)) (Rone_mul _))
  -- (x+1) + (x−1) = 2x
  have hsum : Req (Radd (Radd x one) (Rsub x one)) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) x) := by
    refine Req_trans (Radd_add_add_comm _ _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Radd_neg one)) ?_
    exact Req_trans (Radd_zero _) (Req_symm (Rmul_two_eq_add x))
  -- ((a+b)·I)·x = 2x
  have h1 : Req (Rmul (Rmul (Radd a b) I) x) (Rmul (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) x) := by
    refine Req_trans (Rmul_assoc _ _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) hxI)) ?_
    refine Req_trans (Rmul_distrib_right _ _ _) ?_
    exact Req_trans (Radd_congr ha' hb') hsum
  -- cancel x
  refine Req_trans (Req_symm (Rmul_one _)) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Req_symm hxi)) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr h1 (Req_refl _)) ?_
  exact Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) hxi) (Rmul_one _))

/-- Abstract algebra: if `s·I = 2` and `I·q = 1` then `q = ½·s`. -/
theorem inv_eq_half_of (s I q : Real) (hs : Req (Rmul s I) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos))
    (hq : Req (Rmul I q) one) :
    Req q (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) s) := by
  have hhalf : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ofQ (⟨2, 1⟩ : Q) Nat.one_pos)) one :=
    Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ (by decide) (by decide))
  -- q = 1·q = (½·(s·I))·q = (½·s)·(I·q) = ½·s
  refine Req_trans (Req_symm (Rone_mul q)) ?_
  refine Req_trans (Rmul_congr (Req_symm hhalf) (Req_refl q)) ?_
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Req_symm hs)) (Req_refl q)) ?_
  refine Req_trans (Rmul_congr (Req_symm (Rmul_assoc _ _ _)) (Req_refl q)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  exact Req_trans (Rmul_congr (Req_refl _) hq) (Rmul_one _)

/-- **THE PARTIAL-FRACTION IDENTITY** at every real `x` with `x − 1 ≥ c > 0`:
    `1/(x − x⁻¹) = ½·(1/(x−1) + 1/(x+1))`, with the three clamped kernels of the construction
    (all inert there). -/
theorem archKernFull_partial (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ c hcd) (Rsub x one)) :
    Req ((archKernFull c hcn hcd).f x)
        (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
          (Radd ((archKernNear c hcn hcd).f x) (archKernReg.f x))) := by
  rw [archKernFull_f]
  have hge := innerXm_ge_c c hcd x hx1 hxc
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ hcn hcd hge
  obtain ⟨ka, hka⟩ := Pos_of_Rle_ofQ hcn hcd hxc
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx1
  have hx2 : Rle (ofQ (⟨2, 1⟩ : Q) Nat.one_pos) (Radd x one) := by
    refine Rle_trans (Rle_of_Req (Req_symm (Req_trans (Radd_ofQ_ofQ (by decide) (by decide))
      (ofQ_congr _ _ (by decide : Qeq (add (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q)) (⟨2, 1⟩ : Q)))))) ?_
    exact Radd_le_add hx1 (Rle_refl one)
  obtain ⟨kb, hkb⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx2
  have hK : Req (clampedInv c hcn hcd (innerXm x)) (Rinv (innerXm x) ki hki) :=
    clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hki hge
  have hA : Req ((archKernNear c hcn hcd).f x) (Rinv (Rsub x one) ka hka) :=
    clampedInv_eq_of_ge (a := c) (han := hcn) (had := hcd) hka hxc
  have hB : Req (archKernReg.f x) (Rinv (Radd x one) kb hkb) :=
    clampedInv_eq_of_ge (a := (⟨2, 1⟩ : Q)) (han := by decide) (had := by decide) hkb hx2
  have h2 := inv_sum_mul_two x (Rinv (Rsub x one) ka hka) (Rinv (Radd x one) kb hkb) (innerXm x)
    (Rinv x kx hkx) (Rmul_Rinv_self hka) (Rmul_Rinv_self hkb) (innerXm_mul x hx1) (Rmul_Rinv_self hkx)
  have hq := inv_eq_half_of _ (innerXm x) (Rinv (innerXm x) ki hki) h2 (Rmul_Rinv_self hki)
  refine Req_trans hK (Req_trans hq ?_)
  exact Rmul_congr (Req_refl _) (Radd_congr (Req_symm hA) (Req_symm hB))

end UOR.Bridge.F1Square.Square
