/-
F1 square — **the regular-kernel family and the split of `∫₁^∞ N⁺/(x+1)` at `2`**
(`WeilArchRegSplit.lean`): `regInt = N⁺(x)·(1/max(x+1,2))`, its shifted family with the UNIFORM
block decay at the same constant `archKC` as the full-kernel family, its far-window rate, and the
improper split `∫_{1}^{∞} N⁺/(x+1) = ∫_{[1,2]} N⁺/(x+1) + ∫_{2}^{∞} N⁺/(x+1)` (shift `0` then `1`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchLimit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `N⁺(x)·(1/max(x+1, 2))`. -/
def regInt (C : NormCtx) (f g : L2Test) : L2Test := productTest (archNumC C f g) archKernReg

theorem regInt_f (C : NormCtx) (f g : L2Test) (x : Real) :
    (regInt C f g).f x = Rmul ((archNumC C f g).f x) (archKernReg.f x) := rfl

/-- The regular kernel is capped by `1/(m+2) ≤ 1/m` at `x ≥ m+1` and by `1` everywhere. -/
theorem archKernReg_le_inv (m : Nat) (hm : 1 ≤ m) (x : Real)
    (hx : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x) :
    Rle (archKernReg.f x) (ofQ (Qinv (⟨(m : Int), 1⟩ : Q)) (Qinv_den_pos (show (0 : Int) < (m : Int) by omega))) := by
  have hm2 : (0 : Int) < (m : Int) + 2 := by omega
  have hmn : (0 : Int) < (m : Int) := by omega
  have h1 : Rle (archKernReg.f x) (ofQ (Qinv (⟨(m : Int) + 2, 1⟩ : Q)) (Qinv_den_pos hm2)) :=
    clampedInv_le_ofQ_inv_of_ge (by decide) (by decide) hm2 Nat.one_pos (blockPoint_succ_ge m x hx)
  refine Rle_trans h1 (Rle_ofQ_ofQ _ _ ?_)
  exact Qinv_antitone hm2 hmn (by
    show (m : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 2) * ((1 : Nat) : Int); push_cast; omega)

theorem archKernReg_le_one (x : Real) : Rle (archKernReg.f x) one := by
  refine Rle_trans (Rle_trans (Rle_Rabs_self _) (archKernReg.hbd x)) ?_
  exact Rle_ofQ_ofQ _ (by decide) (by show Qle (Qinv (⟨2, 1⟩ : Q)) (⟨1, 1⟩ : Q); decide)

theorem archKernReg_nonneg (x : Real) : Rnonneg (archKernReg.f x) :=
  Rnonneg_clampedInv (⟨2, 1⟩ : Q) (by decide) (by decide) (Radd x one)

/-- **The uniform block decay** of the shifted regular family at `archKC`. -/
theorem regDecay (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (δ : Q) (hδd : 0 < δ.den) (hδn : 0 ≤ δ.num) :
    DecayAt (shiftTest δ hδd (regInt C f g)) (archKC C f g) (archKC_den C f g) := by
  intro m hm
  have hm1n : (0 : Int) < (m : Int) + 1 := by omega
  have hm0n : (0 : Int) < (m : Int) := by omega
  have hpt : ∀ t : Real, Rle zero t →
      Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) t) (ofQ δ hδd)) :=
    fun t ht0 => Rle_trans (blockPoint_ge m t ht0) (Rle_self_Radd_right (Rnonneg_ofQ hδd hδn))
  have habs : Rle (Rabs (integralTerm (shiftTest δ hδd (regInt C f g)).hLd (shiftTest δ hδd (regInt C f g)).hLn
        (shiftTest δ hδd (regInt C f g)).hlip (shiftTest δ hδd (regInt C f g)).hfc m))
      (ofQ (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))) := by
    rcases Qle_or_Qlt C.geom.Bd (⟨(m : Int) + 1, 1⟩ : Q) with hpast | hearly
    · have hBLd : 0 < (mul (mul (archKl C.geom f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q)))
          (Qinv (⟨(m : Int), 1⟩ : Q))).den :=
        Qmul_den_pos (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
      refine Rle_trans (riemannIntegralI_abs_le_window (shiftTest δ hδd (regInt C f g)).hLd
        (shiftTest δ hδd (regInt C f g)).hLn (shiftTest δ hδd (regInt C f g)).hlip
        (shiftTest δ hδd (regInt C f g)).hfc (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
        (mul (mul (archKl C.geom f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q))) (Qinv (⟨(m : Int), 1⟩ : Q)))
        Nat.one_pos (by decide) (by decide) hBLd ?_) ?_
      · intro t ht0 _
        have hx := hpt t ht0
        rw [shiftTest_f, regInt_f]
        have hNb := archNumC_late_bound C f g hf hg (⟨(m : Int) + 1, 1⟩ : Q) hm1n Nat.one_pos _ hx hpast
        have hkb := archKernReg_le_inv m hm _ hx
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
          (Rnonneg_ofQ (Qinv_den_pos hm0n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
          hNb (Rle_trans (Rle_of_Req (Rabs_of_nonneg (archKernReg_nonneg _))) hkb)) ?_
        refine Rle_of_Req (Req_trans (Rmul_congr
          (Rmul_ofQ_ofQ (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Req_refl _)) ?_)
        exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
      · refine Rle_ofQ_ofQ (Qmul_den_pos (by decide) hBLd)
          (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm)) ?_
        refine Qle_trans hBLd (Qeq_le (Qone_mul _)) ?_
        refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (digamma_succ_mul_pos hm))
          (Qeq_le (late_product_eq (archKl C.geom f g) m hm)) ?_
        exact archKC_late C f g m
    · refine Rle_trans (riemannIntegralI_abs_le_window (shiftTest δ hδd (regInt C f g)).hLd
        (shiftTest δ hδd (regInt C f g)).hLn (shiftTest δ hδd (regInt C f g)).hlip
        (shiftTest δ hδd (regInt C f g)).hfc (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (archNumC C f g).M
        Nat.one_pos (by decide) (by decide) (archNumC C f g).hMd ?_) ?_
      · intro t _ _
        rw [shiftTest_f, regInt_f]
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (by decide) (by decide))
          ((archNumC C f g).hbd _) (Rle_trans (Rle_of_Req (Rabs_of_nonneg (archKernReg_nonneg _)))
            (archKernReg_le_one _))) ?_
        exact Rle_of_Req (Rmul_one _)
      · exact Rle_ofQ_ofQ (Qmul_den_pos (by decide) (archNumC C f g).hMd)
          (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))
          (archKC_early C f g m hm hearly)
  exact ⟨Rneg_le_of_Rabs_le habs, Rle_of_Rabs_le habs⟩

/-- **The far-window rate** of the shifted regular family. -/
theorem regFar (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (δ : Q) (hδd : 0 < δ.den) (hδn : 0 ≤ δ.num) (Δ : Q) (hΔd : 0 < Δ.den) (hΔn : 0 < Δ.num)
    (hΔ1 : Qle Δ (⟨1, 1⟩ : Q)) (j : Nat) :
    Rle (Rabs (riemannIntegralI (shiftTest δ hδd (regInt C f g)).hLd (shiftTest δ hδd (regInt C f g)).hLn
        (shiftTest δ hδd (regInt C f g)).hlip (shiftTest δ hδd (regInt C f g)).hfc
        (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd (Int.le_of_lt hΔn)))
      (ofQ (⟨((archCF C f g : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  have hMj : j + 1 ≤ digammaMidx (archKC C f g) j := digammaMidx_ge _ j
  have hM1 : 1 ≤ digammaMidx (archKC C f g) j := digammaMidx_ge_one _ j
  have hm1n : (0 : Int) < ((digammaMidx (archKC C f g) j : Nat) : Int) + 1 := by omega
  have hm0n : (0 : Int) < ((digammaMidx (archKC C f g) j : Nat) : Int) := by omega
  have hpt : ∀ t : Real, Rle zero t →
      Rle (ofQ (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Δ Nat.one_pos hΔd t)
          (ofQ δ hδd)) :=
    fun t ht0 => Rle_trans (affine_ge_lo _ _ Nat.one_pos hΔd (Int.le_of_lt hΔn) t ht0)
      (Rle_self_Radd_right (Rnonneg_ofQ hδd hδn))
  rcases Qle_or_Qlt C.geom.Bd (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) with hpast | hearly
  · have hBLd : 0 < (mul (mul (archKl C.geom f g)
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q)))
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))).den :=
      Qmul_den_pos (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
    have hBLn : 0 ≤ (mul (mul (archKl C.geom f g)
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q)))
        (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))).num :=
      Int.mul_nonneg (Int.mul_nonneg (archKl_num C.geom f g) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
        (Int.le_of_lt (Qinv_num_pos Nat.one_pos))
    refine Rle_trans (riemannIntegralI_abs_le_window (shiftTest δ hδd (regInt C f g)).hLd
      (shiftTest δ hδd (regInt C f g)).hLn (shiftTest δ hδd (regInt C f g)).hlip
      (shiftTest δ hδd (regInt C f g)).hfc _ Δ _ Nat.one_pos hΔd (Int.le_of_lt hΔn) hBLd ?_) ?_
    · intro t ht0 _
      have hx := hpt t ht0
      rw [shiftTest_f, regInt_f]
      have hNb := archNumC_late_bound C f g hf hg _ hm1n Nat.one_pos _ hx hpast
      have hkb := archKernReg_le_inv _ hM1 _ hx
      refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
      refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
        (Rnonneg_ofQ (Qinv_den_pos hm0n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
        hNb (Rle_trans (Rle_of_Req (Rabs_of_nonneg (archKernReg_nonneg _))) hkb)) ?_
      refine Rle_of_Req (Req_trans (Rmul_congr
        (Rmul_ofQ_ofQ (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Req_refl _)) ?_)
      exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
    · refine Rle_ofQ_ofQ (Qmul_den_pos hΔd hBLd) (Nat.succ_pos j) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos hBLd) (Qmul_le_mul_right hBLn hΔ1) ?_
      refine Qle_trans hBLd (Qeq_le (Qone_mul _)) ?_
      refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (digamma_succ_mul_pos hM1))
        (Qeq_le (late_product_eq (archKl C.geom f g) _ hM1)) ?_
      refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (Nat.succ_pos j))
        (Qmul_le_mul_left (archKl_num C.geom f g) (qinv_block_le _ j hMj)) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos j))
        (Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) (archCF_ge_Kl C f g)) ?_
      exact Qeq_le (qCF_mul_inv _ j)
  · refine Rle_trans (riemannIntegralI_abs_le_window (shiftTest δ hδd (regInt C f g)).hLd
      (shiftTest δ hδd (regInt C f g)).hLn (shiftTest δ hδd (regInt C f g)).hlip
      (shiftTest δ hδd (regInt C f g)).hfc _ Δ (archNumC C f g).M Nat.one_pos hΔd (Int.le_of_lt hΔn)
      (archNumC C f g).hMd ?_) ?_
    · intro t _ _
      rw [shiftTest_f, regInt_f]
      refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
      refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (by decide) (by decide))
        ((archNumC C f g).hbd _) (Rle_trans (Rle_of_Req (Rabs_of_nonneg (archKernReg_nonneg _)))
          (archKernReg_le_one _))) ?_
      exact Rle_of_Req (Rmul_one _)
    · refine Rle_ofQ_ofQ (Qmul_den_pos hΔd (archNumC C f g).hMd) (Nat.succ_pos j) ?_
      refine Qle_trans (Qmul_den_pos Nat.one_pos (archNumC C f g).hMd)
        (Qmul_le_mul_right (archNumC C f g).hMn hΔ1) ?_
      refine Qle_trans (archNumC C f g).hMd (Qeq_le (Qone_mul _)) ?_
      have hjB : ((j : Nat) : Int) + 1 ≤ C.geom.Bd.num := by
        have h1 := le_Bd_num_of_lt C.geom (digammaMidx (archKC C f g) j) hearly
        have h2 : ((j : Nat) : Int) + 1 ≤ ((digammaMidx (archKC C f g) j : Nat) : Int) + 1 := by
          have := Int.ofNat_le.mpr hMj; push_cast at this; omega
        omega
      have hMB := archCF_ge_MB C f g
      simp only [Qle, mul] at hMB
      push_cast at hMB
      show (archNumC C f g).M.num * ((j + 1 : Nat) : Int)
        ≤ ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den : Int)
      push_cast
      have h3 : (archNumC C f g).M.num * ((j : Int) + 1) ≤ (archNumC C f g).M.num * C.geom.Bd.num :=
        Int.mul_le_mul_of_nonneg_left hjB (archNumC C f g).hMn
      have e1 : (archNumC C f g).M.num * C.geom.Bd.num * 1 = (archNumC C f g).M.num * C.geom.Bd.num := by
        ring_uor
      have e2 : ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den * 1 : Int)
          = ((archCF C f g : Nat) : Int) * ((archNumC C f g).M.den : Int) := by ring_uor
      omega

/-- **THE REGULAR SPLIT AT `2`**: `∫_{1}^{∞} N⁺/(x+1) = ∫_{[1,2]} N⁺/(x+1) + ∫_{2}^{∞} N⁺/(x+1)`
    (shift `0` on the left, shift `1` on the right, both at `archKC`). -/
theorem reg_split_two (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    Req (improperIntegral1 (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLd
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLn
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hlip
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hfc (archKC_den C f g) (archKC_num C f g)
          (regDecay C f g hf hg (⟨0, 1⟩ : Q) Nat.one_pos (by decide)))
        (Radd (riemannIntegralI (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLd
            (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLn
            (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hlip
            (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hfc (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q)
            Nat.one_pos Nat.one_pos (by decide))
          (improperIntegral1 (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos)
              (regInt C f g)).hLd
            (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hLn
            (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hlip
            (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hfc
            (archKC_den C f g) (archKC_num C f g)
            (regDecay C f g hf hg (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos)
              (by decide)))) :=
  improper_split_shift (regInt C f g) (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos (by decide)
    (archKC_den C f g) (archKC_num C f g)
    (regDecay C f g hf hg (⟨0, 1⟩ : Q) Nat.one_pos (by decide))
    (regDecay C f g hf hg (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (by decide))
    (archCF C f g)
    (regFar C f g hf hg (⟨0, 1⟩ : Q) Nat.one_pos (by decide) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) (Qle_refl _))

-- Seal the regular-family tower (in-file defeq uses are above; `regInt_f` is the readback).
attribute [irreducible] regInt

end UOR.Bridge.F1Square.Square
