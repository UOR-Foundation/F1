/-
F1 square — **THE FAR COEFFICIENT IS INDEPENDENT OF THE LEVEL** (`AtlasFarCoefStable.lean`, target side).

`farCoef C k = ∫_B^∞ K_k(x)/x dx` with the floored kernel `K_k = 1/max(x − 1/x, 2^{-k})`.  Beyond `B ≥ 2` the floor
is inert for every `k ≥ 1` (`x − 1 ≥ 1 ≥ 2^{-k}`), so `farCoef C k = farCoef C k'` for all `k, k' ≥ 1`
(`farCoef_eq_of_pos`): the far mass of the anchor kernel on the range is a single constant `fc_∞`, and the limiting
kernel `anchorKernelLimit C fc_∞ h` of `AtlasAnchorAutocorr` is the level-free object.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasTailSplit
import F1Square.Square.AtlasAnchorAutocorr

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `farShift C k = B − 1` as rationals (for every `k`). -/
theorem farShift_eq_Bm1 (C : NormCtx) (k : Nat) : Qeq (farShift C k) (Qsub (canonB C) (⟨1, 1⟩ : Q)) := by
  unfold farShift tailGap Qsub canonB dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  ring_uor

theorem farShift_congr (C : NormCtx) (k k' : Nat) : Qeq (farShift C k) (farShift C k') :=
  Qeq_trans (Qsub_den_pos (canonB_den C) Nat.one_pos) (farShift_eq_Bm1 C k) (Qeq_symm (farShift_eq_Bm1 C k'))

/-- `2^{-k} ≤ 1`. -/
theorem dyQ_le_one_fs (k : Nat) : Qle (dyQ k) (⟨1, 1⟩ : Q) := by
  show (1 : Int) * ((1 : Nat) : Int) ≤ 1 * ((2 ^ k : Nat) : Int)
  have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h' := Int.ofNat_le.mpr h
  push_cast at h' ⊢
  omega

/-- On the `m`-th unit window (`u ≥ m + 1 ≥ 1`) the two far kernels agree: `y = u + (B − 1) ≥ 2`, both floors inert. -/
theorem farKer_agree (C : NormCtx) (k k' : Nat) (m : Nat) (y : Real) (hy0 : Rle zero y) (_hy1 : Rle y one) :
    Req ((farKer C k).f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y))
        ((farKer C k').f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y)) := by
  rw [farKer_f, farKer_f]
  have hs : Req (ofQ (farShift C k) (farShift_den C k)) (ofQ (farShift C k') (farShift_den C k')) :=
    ofQ_congr _ _ (farShift_congr C k k')
  have hu : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y) :=
    affineMap_ge_a _ _ _ _ (by decide) y hy0
  have hu1 : Rle one (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y) :=
    Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hu
  have hsh : Rle one (ofQ (farShift C k) (farShift_den C k)) := Rle_ofQ_ofQ (by decide) _ (one_le_farShift C k)
  -- y − 1 ≥ 1 ≥ 2^{-j} for both floors
  have hdist : Rle one (Rsub (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y)
      (ofQ (farShift C k) (farShift_den C k))) one) := by
    refine Rle_trans (Rle_of_Req (Req_symm (sub_one_of_one_add_ac _))) (Radd_le_add ?_ (Rle_refl _))
    exact Radd_le_add hu1 hsh
  have hxc : ∀ j, Rle (ofQ (dyQ j) (dyQ_den j)) (Rsub (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y)
      (ofQ (farShift C k) (farShift_den C k))) one) :=
    fun j => Rle_trans (Rle_ofQ_ofQ (dyQ_den j) Nat.one_pos (dyQ_le_one_fs j)) hdist
  have hy1' : Rle one (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y) (ofQ (farShift C k) (farShift_den C k))) :=
    Rle_trans hu1 (Rle_self_Radd_right (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) hsh)))
  have hK : Req (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y)
      (ofQ (farShift C k) (farShift_den C k))))
      (Kfl (dyQ k') (dyQ_num k') (dyQ_den k') (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) y)
      (ofQ (farShift C k) (farShift_den C k)))) :=
    archKernFull_inert_pair (dyQ k) (dyQ k') (dyQ_num k) (dyQ_den k) (dyQ_num k') (dyQ_den k') _ hy1' (hxc k) (hxc k')
  refine Req_trans (Rmul_congr (Req_refl _) hK) ?_
  exact Rmul_congr (clampedInv_congr _ _ _ (Radd_congr (Req_refl _) hs))
    ((archKernFull (dyQ k') (dyQ_num k') (dyQ_den k')).hfc _ _ (Radd_congr (Req_refl _) hs))

/-- **★ `farCoef C k = farCoef C k'`** for every `k, k'` (the floor is inert beyond `B ≥ 2`). -/
theorem farCoef_eq_of_pos (C : NormCtx) (k k' : Nat) : Req (farCoef C k) (farCoef C k') := by
  unfold farCoef
  refine improperIntegral1_congr_terms _ _ _ _ _ _ _ _ Nat.one_pos (by decide) (farKer_decay C k) (farKer_decay C k') (fun m => ?_)
  unfold integralTerm
  exact intI_congr_unit_free _ _ _ _ _ _ _ _ _ _ Nat.one_pos (by decide) (by decide) (fun y hy0 hy1 => farKer_agree C k k' m y hy0 hy1)

end UOR.Bridge.F1Square.Square
