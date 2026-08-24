/-
F1 square — **the `x = 1` lower-end improper limit of the archimedean tail** (`WeilArchNear.lean`):

  `ArchNearPart(f,g) = lim_{k→∞} ∫_{1+2⁻ᵏ}^{2} N(x)·(1/(x−1)) dx`

— the PROVED lower-end improper limit at the removable singularity.  The truncated integrals
`J k = ∫_{1+2⁻ᵏ}^{2} N(x)·(1/max(x−1, 2⁻ᵏ)) dx` (the clamp inert on the window) form a Bishop-regular
sequence: consecutive truncations differ by the strip `[1+2⁻ᵏ⁻¹, 1+2⁻ᵏ]`, and on the strip the
integrand is bounded by the numerator's Lipschitz modulus alone — `|N(x)·(1/(x−1))| ≤ N.L`, since
`|N(x)| ≤ N.L·|x−1|` (`archNum_abs_le_dist_one`, the endpoint vanishing `N(1) ≈ 0` at rate `L`) and
`(x−1)·(1/(x−1)) = 1`.  So `|J(k+1) − J k| ≤ N.L·2⁻ᵏ⁻¹` — geometric — and the telescoped bound
`|J(k+d) − J k| ≤ CN·(2ᵈ−1)/2ᵏ⁺ᵈ ≤ CN/2ᵏ` (`CN` an integer cap of `N.L`) gives regularity after the
reindex `k ↦ k + CN` (`CN < 2^CN`).  `Rlim` of the reindexed sequence IS the improper limit.

Lipschitz regularity is used ONLY to bound the quotient near `x = 1`; NO value at the singular point
is invented — the definition is the limit of honest truncations.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchTailFar

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) The truncation geometry: windows `[1+2⁻ᵏ, 2]` and the dyadic clamp floors.
-- ===========================================================================

/-- The dyadic floor `2⁻ᵏ` as a rational. -/
def dyQ (k : Nat) : Q := ⟨1, 2 ^ k⟩

theorem dyQ_den (k : Nat) : 0 < (dyQ k).den := Nat.two_pow_pos k

theorem dyQ_num (k : Nat) : 0 < (dyQ k).num := by show (0 : Int) < 1; decide

/-- The truncated window's low edge `1 + 2⁻ᵏ`. -/
def nearLo (k : Nat) : Q := add (⟨1, 1⟩ : Q) (dyQ k)

theorem nearLo_den (k : Nat) : 0 < (nearLo k).den := add_den_pos (by decide) (dyQ_den k)

/-- The truncated window's width `(2ᵏ−1)/2ᵏ` (so the window is `[1+2⁻ᵏ, 2]`). -/
def nearW (k : Nat) : Q := ⟨((2 ^ k : Nat) : Int) - 1, 2 ^ k⟩

theorem nearW_den (k : Nat) : 0 < (nearW k).den := Nat.two_pow_pos k

theorem nearW_num (k : Nat) : 0 ≤ (nearW k).num := by
  show (0 : Int) ≤ ((2 ^ k : Nat) : Int) - 1
  have h : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := by
    exact_mod_cast Nat.one_le_two_pow (n := k)
  omega

/-- The truncated near integrand `N(x)·(1/max(x−1, 2⁻ᵏ))`. -/
def nearIntegrand (G : ClosedGeom) (f g : L2Test) (k : Nat) : L2Test :=
  productTest (archNum G f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))

/-- **The truncated integral** `J k = ∫_{1+2⁻ᵏ}^{2} N(x)·(1/max(x−1,2⁻ᵏ)) dx`. -/
def nearJ (G : ClosedGeom) (f g : L2Test) (k : Nat) : Real :=
  riemannIntegralI (nearIntegrand G f g k).hLd (nearIntegrand G f g k).hLn
    (nearIntegrand G f g k).hlip (nearIntegrand G f g k).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k)

-- ===========================================================================
-- (1) The strip bound `|N(x)·(1/max(x−1,c))| ≤ N.L` for `x ≥ 1+c` — the quotient cap.
-- ===========================================================================

/-- On `x ≥ 1+c` (any dyadic floor `c`), the near integrand is capped by the numerator's Lipschitz
    modulus: `|N(x)·(1/max(x−1,c))| ≤ N.L` — `|N(x)| ≤ N.L·(x−1)` and `(x−1)·(1/(x−1)) = 1`. -/
theorem nearIntegrand_cap (G : ClosedGeom) (f g : L2Test) (c : Q) (hcn : 0 < c.num)
    (hcd : 0 < c.den) (x : Real)
    (hx : Rle (ofQ (add (⟨1, 1⟩ : Q) c) (add_den_pos (by decide) hcd)) x) :
    Rle (Rabs (Rmul ((archNum G f g).f x) (clampedInv c hcn hcd (Rsub x one))))
        (ofQ (archNum G f g).L (archNum G f g).hLd) := by
  -- x−1 ≥ c
  have hsplit : Req (ofQ (add (⟨1, 1⟩ : Q) c) (add_den_pos (by decide) hcd))
      (Radd one (ofQ c hcd)) := Req_symm (Radd_ofQ_ofQ (by decide) hcd)
  have hxc : Rle (ofQ c hcd) (Rsub x one) := by
    have h1 : Rle (Rsub (Radd one (ofQ c hcd)) one) (Rsub x one) :=
      Rsub_le_mono (Rle_trans (Rle_of_Req (Req_symm hsplit)) hx) (Rle_refl one)
    refine Rle_trans (Rle_of_Req ?_) h1
    -- c ≈ (1+c) − 1
    refine Req_symm (Req_trans (Rsub_congr (Radd_comm one (ofQ c hcd)) (Req_refl one)) ?_)
    refine Req_trans (Radd_assoc (ofQ c hcd) one (Rneg one)) ?_
    exact Req_trans (Radd_congr (Req_refl _) (Radd_neg one)) (Radd_zero _)
  -- witness for the positivity of x−1, and the clamp is inert
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ hcn hcd hxc
  have hclamp : Req (clampedInv c hcn hcd (Rsub x one)) (Rinv (Rsub x one) kx hkx) :=
    clampedInv_eq_of_ge hkx hxc
  -- (x−1) ≥ 0 and (x−1)·(1/(x−1)) ≈ 1
  have hx1nn : Rnonneg (Rsub x one) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg
      (Rnonneg_ofQ hcd (Int.le_of_lt hcn))) hxc)
  have hkernn : Rnonneg (clampedInv c hcn hcd (Rsub x one)) :=
    Rnonneg_clampedInv c hcn hcd (Rsub x one)
  -- |N·kern| = |N|·kern ≤ (L·|x−1|)·kern = L·(|x−1|·kern) = L·((x−1)·kern) = L·1 = L
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_of_nonneg hkernn))) ?_
  refine Rle_trans (Rmul_le_Rmul_right hkernn (archNum_abs_le_dist_one G f g x)) ?_
  refine Rle_trans (Rle_of_Req (Rmul_assoc _ _ _)) ?_
  have hprod1 : Req (Rmul (Rabs (Rsub x one)) (clampedInv c hcn hcd (Rsub x one))) one := by
    refine Req_trans (Rmul_congr (Rabs_of_nonneg hx1nn) hclamp) ?_
    exact Rmul_Rinv_self hkx
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) hprod1)) ?_
  exact Rle_of_Req (Rmul_one _)

-- ===========================================================================
-- (2) `x ≥ 1+c ⟹ x−1 ≥ c` (standalone helper) and the window-point bound.
-- ===========================================================================

/-- `x ≥ 1+c` gives `x−1 ≥ c`. -/
theorem sub_one_ge_of_ge_add {c : Q} (hcd : 0 < c.den) {x : Real}
    (hx : Rle (ofQ (add (⟨1, 1⟩ : Q) c) (add_den_pos (by decide) hcd)) x) :
    Rle (ofQ c hcd) (Rsub x one) := by
  have hsplit : Req (ofQ (add (⟨1, 1⟩ : Q) c) (add_den_pos (by decide) hcd))
      (Radd one (ofQ c hcd)) := Req_symm (Radd_ofQ_ofQ (by decide) hcd)
  have h1 : Rle (Rsub (Radd one (ofQ c hcd)) one) (Rsub x one) :=
    Rsub_le_mono (Rle_trans (Rle_of_Req (Req_symm hsplit)) hx) (Rle_refl one)
  refine Rle_trans (Rle_of_Req ?_) h1
  refine Req_symm (Req_trans (Rsub_congr (Radd_comm one (ofQ c hcd)) (Req_refl one)) ?_)
  refine Req_trans (Radd_assoc (ofQ c hcd) one (Rneg one)) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg one)) (Radd_zero _)

/-- Window points of the `[lo, lo+w]`-window dominate `lo`. -/
theorem affine_ge_lo (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (t : Real) (ht0 : Rle zero t) :
    Rle (ofQ lo hlo) (affineMap lo w hlo hw t) :=
  Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_of_Rle_zero ht0))

-- ===========================================================================
-- (3) The consecutive-strip identity and the geometric strip bound.
-- ===========================================================================

/-- The dyadic floors decrease: `2⁻ᵏ⁻¹ ≤ 2⁻ᵏ`. -/
theorem dyQ_succ_le (k : Nat) : Qle (dyQ (k + 1)) (dyQ k) := by
  show (1 : Int) * ((2 ^ k : Nat) : Int) ≤ 1 * ((2 ^ (k + 1) : Nat) : Int)
  have h : ((2 ^ k : Nat) : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide) (show k ≤ k + 1 by omega)
  omega

/-- The strip integral `∫_{1+2⁻ᵏ⁻¹}^{1+2⁻ᵏ} N·(1/max(x−1,2⁻ᵏ⁻¹))`. -/
def nearStrip (G : ClosedGeom) (f g : L2Test) (k : Nat) : Real :=
  riemannIntegralI (nearIntegrand G f g (k + 1)).hLd (nearIntegrand G f g (k + 1)).hLn
    (nearIntegrand G f g (k + 1)).hlip (nearIntegrand G f g (k + 1)).hfc
    (nearLo (k + 1)) (dyQ (k + 1)) (nearLo_den (k + 1)) (dyQ_den (k + 1))
    (Int.le_of_lt (dyQ_num (k + 1)))

theorem dyQ_le_nearW (k : Nat) : Qle (dyQ (k + 1)) (nearW (k + 1)) := by
  show (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)
    ≤ (((2 ^ (k + 1) : Nat) : Int) - 1) * ((2 ^ (k + 1) : Nat) : Int)
  have h2k2 : (2 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) :=
    Int.ofNat_le.mpr (Nat.one_lt_two_pow (n := k + 1) (by omega))
  have hfac : (1 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) - 1 := by omega
  have h0 : (0 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) := by omega
  calc (1 : Int) * ((2 ^ (k + 1) : Nat) : Int)
      = ((2 ^ (k + 1) : Nat) : Int) * 1 := by ring_uor
    _ ≤ ((2 ^ (k + 1) : Nat) : Int) * (((2 ^ (k + 1) : Nat) : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left hfac h0
    _ = (((2 ^ (k + 1) : Nat) : Int) - 1) * ((2 ^ (k + 1) : Nat) : Int) := by ring_uor

theorem nearW_sub_num (k : Nat) : 0 ≤ (Qsub (nearW (k + 1)) (dyQ (k + 1))).num := by
  show (0 : Int) ≤ (((2 ^ (k + 1) : Nat) : Int) - 1) * ((2 ^ (k + 1) : Nat) : Int)
    + (-1) * ((2 ^ (k + 1) : Nat) : Int)
  have h2k2 : (2 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) :=
    Int.ofNat_le.mpr (Nat.one_lt_two_pow (n := k + 1) (by omega))
  have hf1 : (0 : Int) ≤ (((2 ^ (k + 1) : Nat) : Int) - 2) := by omega
  have hf2 : (0 : Int) ≤ ((2 ^ (k + 1) : Nat) : Int) := by omega
  have he : (((2 ^ (k + 1) : Nat) : Int) - 1) * ((2 ^ (k + 1) : Nat) : Int)
      + (-1) * ((2 ^ (k + 1) : Nat) : Int)
      = (((2 ^ (k + 1) : Nat) : Int) - 2) * ((2 ^ (k + 1) : Nat) : Int) := by
    generalize ((2 ^ (k + 1) : Nat) : Int) = P
    ring_uor
  rw [he]
  exact Int.mul_nonneg hf1 hf2

theorem nearLo_step_eq (k : Nat) : Qeq (add (nearLo (k + 1)) (dyQ (k + 1))) (nearLo k) := by
  simp only [Qeq, nearLo, dyQ, add]
  push_cast [Nat.pow_succ]
  ring_uor

theorem nearW_step_eq (k : Nat) : Qeq (Qsub (nearW (k + 1)) (dyQ (k + 1))) (nearW k) := by
  simp only [Qeq, nearW, dyQ, Qsub, add, neg]
  push_cast [Nat.pow_succ]
  ring_uor

/-- The truncated integrands agree pointwise on the `k`-window (both dyadic clamps inert). -/
theorem nearIntegrand_step_agree (G : ClosedGeom) (f g : L2Test) (k : Nat)
    (t : Real) (ht0 : Rle zero t) :
    Req ((nearIntegrand G f g (k + 1)).f
          (affineMap (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) t))
        ((nearIntegrand G f g k).f
          (affineMap (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) t)) := by
  have hxlo := affine_ge_lo (nearLo k) (nearW k) (nearLo_den k) (nearW_den k)
    (nearW_num k) t ht0
  have hxc : Rle (ofQ (dyQ k) (dyQ_den k))
      (Rsub (affineMap (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) t) one) :=
    sub_one_ge_of_ge_add (dyQ_den k) hxlo
  have hxc1 : Rle (ofQ (dyQ (k + 1)) (dyQ_den (k + 1)))
      (Rsub (affineMap (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) t) one) :=
    Rle_trans (Rle_ofQ_ofQ (dyQ_den (k + 1)) (dyQ_den k) (dyQ_succ_le k)) hxc
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (dyQ_num k) (dyQ_den k) hxc
  refine Rmul_congr (Req_refl _) ?_
  exact Req_trans
    (clampedInv_eq_of_ge (a := dyQ (k + 1)) (han := dyQ_num (k + 1))
      (had := dyQ_den (k + 1)) hkx hxc1)
    (Req_symm (clampedInv_eq_of_ge (a := dyQ k) (han := dyQ_num k)
      (had := dyQ_den k) hkx hxc))

/-- The remainder piece of the split is `J k` (window `Qeq` + kernel swap). -/
theorem nearRest_eq (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Req (riemannIntegralI (nearIntegrand G f g (k + 1)).hLd
        (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
        (nearIntegrand G f g (k + 1)).hfc
        (add (nearLo (k + 1)) (dyQ (k + 1))) (Qsub (nearW (k + 1)) (dyQ (k + 1)))
        (add_den_pos (nearLo_den (k + 1)) (dyQ_den (k + 1)))
        (Qsub_den_pos (nearW_den (k + 1)) (dyQ_den (k + 1))) (nearW_sub_num k))
      (nearJ G f g k) := by
  refine Req_trans (riemannIntegralI_congr_Q (nearIntegrand G f g (k + 1)).hLd
    (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
    (nearIntegrand G f g (k + 1)).hfc
    (add (nearLo (k + 1)) (dyQ (k + 1))) (Qsub (nearW (k + 1)) (dyQ (k + 1)))
    (nearLo k) (nearW k)
    (add_den_pos (nearLo_den (k + 1)) (dyQ_den (k + 1)))
    (Qsub_den_pos (nearW_den (k + 1)) (dyQ_den (k + 1))) (nearW_sub_num k)
    (nearLo_den k) (nearW_den k) (nearW_num k) (nearLo_step_eq k) (nearW_step_eq k)) ?_
  refine riemannIntegralI_congr_unit_mod (nearIntegrand G f g (k + 1)).hLd
    (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
    (nearIntegrand G f g (k + 1)).hfc (nearIntegrand G f g k).hLd
    (nearIntegrand G f g k).hLn (nearIntegrand G f g k).hlip (nearIntegrand G f g k).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) ?_
  intro t ht0 _
  exact nearIntegrand_step_agree G f g k t ht0

/-- `(s + J) − J ≈ s` (generic cancellation). -/
theorem Radd_sub_cancel_right (s J : Real) : Req (Rsub (Radd s J) J) s :=
  Req_trans (Radd_assoc s J (Rneg J))
    (Req_trans (Radd_congr (Req_refl s) (Radd_neg J)) (Radd_zero s))

set_option maxHeartbeats 1600000 in
/-- The truncation splits: `J(k+1) ≈ strip + J k`. -/
theorem nearJ_split (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Req (nearJ G f g (k + 1)) (Radd (nearStrip G f g k) (nearJ G f g k)) := by
  refine Req_trans (riemannIntegralI_split_at (nearIntegrand G f g (k + 1)).hLd
    (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
    (nearIntegrand G f g (k + 1)).hfc (nearLo (k + 1)) (nearW (k + 1)) (dyQ (k + 1))
    (nearLo_den (k + 1)) (nearW_den (k + 1)) (nearW_num (k + 1))
    (dyQ_den (k + 1)) (dyQ_num (k + 1)) (dyQ_le_nearW k) (nearW_sub_num k)) ?_
  exact Radd_congr (Req_refl _) (nearRest_eq G f g k)

/-- **The consecutive truncations differ by the strip**. -/
theorem nearJ_succ_diff (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Req (Rsub (nearJ G f g (k + 1)) (nearJ G f g k)) (nearStrip G f g k) :=
  Req_trans (Rsub_congr (nearJ_split G f g k) (Req_refl _))
    (Radd_sub_cancel_right (nearStrip G f g k) (nearJ G f g k))

-- ===========================================================================
-- (4) The integer cap of the numerator's modulus and the geometric strip bound.
-- ===========================================================================

/-- The integer cap `CN = ⌈N.L⌉+1` of the numerator's Lipschitz modulus. -/
def nearCN (G : ClosedGeom) (f g : L2Test) : Nat := (archNum G f g).L.num.toNat + 1

theorem nearCN_ge (G : ClosedGeom) (f g : L2Test) :
    Qle (archNum G f g).L (⟨(nearCN G f g : Int), 1⟩ : Q) := by
  have hLn := (archNum G f g).hLn
  have hLd := (archNum G f g).hLd
  show (archNum G f g).L.num * ((1 : Nat) : Int)
    ≤ ((nearCN G f g : Nat) : Int) * ((archNum G f g).L.den : Int)
  have hcast : ((nearCN G f g : Nat) : Int) = (archNum G f g).L.num + 1 := by
    show (((archNum G f g).L.num.toNat + 1 : Nat) : Int) = (archNum G f g).L.num + 1
    push_cast [Int.toNat_of_nonneg hLn]
    ring_uor
  rw [hcast]
  have h1 : (archNum G f g).L.num * 1 ≤ ((archNum G f g).L.num + 1) * 1 := by omega
  have h2 : ((archNum G f g).L.num + 1) * 1
      ≤ ((archNum G f g).L.num + 1) * ((archNum G f g).L.den : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  calc (archNum G f g).L.num * ((1 : Nat) : Int)
      = (archNum G f g).L.num * 1 := by push_cast; ring_uor
    _ ≤ ((archNum G f g).L.num + 1) * ((archNum G f g).L.den : Int) := Int.le_trans h1 h2

/-- **The geometric strip bound**: `|J(k+1) − J k| ≤ CN·2⁻ᵏ⁻¹`. -/
theorem nearJ_succ_bound (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Rle (Rabs (Rsub (nearJ G f g (k + 1)) (nearJ G f g k)))
        (ofQ (⟨(nearCN G f g : Int), 2 ^ (k + 1)⟩ : Q) (Nat.two_pow_pos (k + 1))) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (nearJ_succ_diff G f g k))) ?_
  show Rle (Rabs (riemannIntegralI (nearIntegrand G f g (k + 1)).hLd
      (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
      (nearIntegrand G f g (k + 1)).hfc (nearLo (k + 1)) (dyQ (k + 1))
      (nearLo_den (k + 1)) (dyQ_den (k + 1)) (Int.le_of_lt (dyQ_num (k + 1))))) _
  refine Rle_trans (riemannIntegralI_abs_le_window (nearIntegrand G f g (k + 1)).hLd
    (nearIntegrand G f g (k + 1)).hLn (nearIntegrand G f g (k + 1)).hlip
    (nearIntegrand G f g (k + 1)).hfc (nearLo (k + 1)) (dyQ (k + 1))
    (⟨(nearCN G f g : Int), 1⟩ : Q) (nearLo_den (k + 1)) (dyQ_den (k + 1))
    (Int.le_of_lt (dyQ_num (k + 1))) Nat.one_pos ?_) ?_
  · -- pointwise cap on the strip window
    intro t ht0 _
    have hxlo := affine_ge_lo (nearLo (k + 1)) (dyQ (k + 1)) (nearLo_den (k + 1))
      (dyQ_den (k + 1)) (Int.le_of_lt (dyQ_num (k + 1))) t ht0
    refine Rle_trans (nearIntegrand_cap G f g (dyQ (k + 1)) (dyQ_num (k + 1))
      (dyQ_den (k + 1)) _ hxlo) ?_
    exact Rle_ofQ_ofQ (archNum G f g).hLd Nat.one_pos (nearCN_ge G f g)
  · -- (1/2^{k+1})·CN ≈ CN/2^{k+1}
    refine Rle_of_Req (ofQ_congr (Qmul_den_pos (dyQ_den (k + 1)) Nat.one_pos)
      (Nat.two_pow_pos (k + 1)) ?_)
    simp only [Qeq, mul, dyQ]
    push_cast
    ring_uor

-- ===========================================================================
-- (5) The geometric telescope and the Bishop regularity of the truncations.
-- ===========================================================================

/-- Real triangle for differences: `|A−C| ≤ |A−B| + |B−C|`. -/
theorem Rabs_sub_le_tri (A B C : Real) :
    Rle (Rabs (Rsub A C)) (Radd (Rabs (Rsub A B)) (Rabs (Rsub B C))) :=
  Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rsub_telescope A B C)))) (Rabs_Radd _ _)

/-- The dyadic halving identity `CN/2ᵐ ≈ CN/2ᵐ⁺¹ + CN/2ᵐ⁺¹` (for any integer numerator). -/
theorem dy_halve (c : Nat) (m : Nat) :
    Req (ofQ (⟨(c : Int), 2 ^ m⟩ : Q) (Nat.two_pow_pos m))
        (Radd (ofQ (⟨(c : Int), 2 ^ (m + 1)⟩ : Q) (Nat.two_pow_pos (m + 1)))
              (ofQ (⟨(c : Int), 2 ^ (m + 1)⟩ : Q) (Nat.two_pow_pos (m + 1)))) := by
  refine Req_symm (Req_trans (Radd_ofQ_ofQ (Nat.two_pow_pos (m + 1)) (Nat.two_pow_pos (m + 1)))
    (ofQ_congr (add_den_pos (Nat.two_pow_pos (m + 1)) (Nat.two_pow_pos (m + 1)))
      (Nat.two_pow_pos m) ?_))
  simp only [Qeq, add, Nat.pow_succ]
  push_cast
  generalize ((2 : Int) ^ m) = A
  ring_uor

/-- **The geometric telescope** (real-valued bound): `|J(k+d) − J k| ≤ CN/2ᵏ − CN/2ᵏ⁺ᵈ`. -/
theorem nearJ_tel (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    ∀ d : Nat, Rle (Rabs (Rsub (nearJ G f g (k + d)) (nearJ G f g k)))
      (Rsub (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k))
            (ofQ (⟨(nearCN G f g : Int), 2 ^ (k + d)⟩ : Q) (Nat.two_pow_pos (k + d))))
  | 0 => by
      refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Radd_neg _)) Rabs_zero)) ?_
      -- 0 ≤ a − a
      refine Rle_of_Req (Req_symm ?_)
      exact Radd_neg (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k))
  | (d + 1) => by
      have hstep := nearJ_succ_bound G f g (k + d)
      have hprev := nearJ_tel G f g k d
      have htri := Rabs_sub_le_tri (nearJ G f g (k + d + 1)) (nearJ G f g (k + d))
        (nearJ G f g k)
      have hkd1 : k + (d + 1) = k + d + 1 := by omega
      rw [hkd1]
      refine Rle_trans htri ?_
      refine Rle_trans (Radd_le_add hstep hprev) ?_
      -- CN/2^{k+d+1} + (CN/2^k − CN/2^{k+d}) ≈ CN/2^k − CN/2^{k+d+1}
      refine Rle_of_Req ?_
      have hhalve := dy_halve (nearCN G f g) (k + d)
      -- abbreviations: s := CN/2^{k+d+1}, big := CN/2^k
      -- LHS = s + (big − (s+s)) ≈ big − s
      refine Req_trans (Radd_congr (Req_refl _)
        (Rsub_congr (Req_refl _) hhalve)) ?_
      -- s + (big − (s+s)) ≈ big − s : pure additive shuffling
      refine Req_trans (Radd_comm _ _) ?_
      -- (big − (s+s)) + s ≈ big − s
      refine Req_trans (Radd_congr (Rsub_congr (Req_refl _)
        (Req_refl _)) (Req_refl _)) ?_
      -- big + (−(s+s)) + s ≈ big + (−s) : associate and cancel
      refine Req_trans (Radd_assoc _ _ _) ?_
      refine Radd_congr (Req_refl _) ?_
      -- (−(s+s)) + s ≈ −s
      refine Req_trans (Radd_congr (Rneg_Radd _ _) (Req_refl _)) ?_
      -- (−s + −s) + s ≈ −s
      refine Req_trans (Radd_assoc _ _ _) ?_
      refine Req_trans (Radd_congr (Req_refl _)
        (Req_trans (Radd_comm _ _) (Radd_neg _))) ?_
      exact Radd_zero _

/-- **The uniform diff bound**: `|J(k+d) − J k| ≤ CN/2ᵏ` (drop the subtracted tail). -/
theorem nearJ_diff_le (G : ClosedGeom) (f g : L2Test) (k d : Nat) :
    Rle (Rabs (Rsub (nearJ G f g (k + d)) (nearJ G f g k)))
      (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
  refine Rle_trans (nearJ_tel G f g k d) ?_
  refine Rle_trans (Rsub_le_mono (Rle_refl _)
    (Rle_zero_of_Rnonneg (Rnonneg_ofQ (Nat.two_pow_pos (k + d))
      (by show (0 : Int) ≤ (nearCN G f g : Int); omega)))) ?_
  exact Rle_of_Req (Rsub_zero _)

-- ===========================================================================
-- (6) Regularity of the reindexed truncations and the limit.
-- ===========================================================================

/-- The pairwise regularity bound of the reindexed sequence. -/
def nearC (G : ClosedGeom) (f g : L2Test) (j k : Nat) : Q :=
  add (⟨(nearCN G f g : Int), 2 ^ (j + nearCN G f g)⟩ : Q)
      (⟨(nearCN G f g : Int), 2 ^ (k + nearCN G f g)⟩ : Q)

theorem nearC_den (G : ClosedGeom) (f g : L2Test) (j k : Nat) : 0 < (nearC G f g j k).den :=
  add_den_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)

/-- Each addend fits under its modulus: `CN/2^{j+CN} ≤ 1/(j+1)` (since `CN ≤ 2^CN`, `j+1 ≤ 2^j`). -/
theorem nearC_addend_le (G : ClosedGeom) (f g : L2Test) (j : Nat) :
    Qle (⟨(nearCN G f g : Int), 2 ^ (j + nearCN G f g)⟩ : Q) (⟨1, j + 1⟩ : Q) := by
  show ((nearCN G f g : Nat) : Int) * ((j + 1 : Nat) : Int)
    ≤ 1 * ((2 ^ (j + nearCN G f g) : Nat) : Int)
  have hNat : nearCN G f g * (j + 1) ≤ 2 ^ (j + nearCN G f g) := by
    have h1 : nearCN G f g ≤ 2 ^ nearCN G f g := Nat.le_of_lt (Nat.lt_two_pow_self)
    have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    calc nearCN G f g * (j + 1) ≤ 2 ^ nearCN G f g * 2 ^ j := Nat.mul_le_mul h1 h2
      _ = 2 ^ (j + nearCN G f g) := by rw [← Nat.pow_add, Nat.add_comm]
  calc ((nearCN G f g : Nat) : Int) * ((j + 1 : Nat) : Int)
      = ((nearCN G f g * (j + 1) : Nat) : Int) := by push_cast; ring_uor
    _ ≤ ((2 ^ (j + nearCN G f g) : Nat) : Int) := Int.ofNat_le.mpr hNat
    _ = 1 * ((2 ^ (j + nearCN G f g) : Nat) : Int) := by ring_uor

theorem nearC_le (G : ClosedGeom) (f g : L2Test) (j k : Nat) :
    Qle (nearC G f g j k) (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) :=
  Qadd_le_add (nearC_addend_le G f g j) (nearC_addend_le G f g k)

/-- The one-sided pairwise bound of the reindexed truncations. -/
theorem nearX_bound (G : ClosedGeom) (f g : L2Test) (j k : Nat) :
    Rle (Rsub (nearJ G f g (j + nearCN G f g)) (nearJ G f g (k + nearCN G f g)))
        (ofQ (nearC G f g j k) (nearC_den G f g j k)) := by
  rcases Nat.le_total k j with hkj | hjk
  · -- k ≤ j : bound by the k-addend
    have he : j + nearCN G f g = (k + nearCN G f g) + (j - k) := by omega
    have hd := nearJ_diff_le G f g (k + nearCN G f g) (j - k)
    rw [← he] at hd
    refine Rle_trans (Rle_of_Rabs_le hd) ?_
    refine Rle_ofQ_ofQ (Nat.two_pow_pos _) (nearC_den G f g j k) ?_
    exact Qle_self_add_l (by show (0 : Int) ≤ (nearCN G f g : Int); omega)
  · -- j ≤ k : bound by the j-addend, after flipping the difference
    have he : k + nearCN G f g = (j + nearCN G f g) + (k - j) := by omega
    have hd := nearJ_diff_le G f g (j + nearCN G f g) (k - j)
    rw [← he] at hd
    have hflip : Req (Rabs (Rsub (nearJ G f g (k + nearCN G f g))
          (nearJ G f g (j + nearCN G f g))))
        (Rabs (Rsub (nearJ G f g (j + nearCN G f g)) (nearJ G f g (k + nearCN G f g)))) :=
      Req_trans (Req_symm (Rabs_Rneg _)) (Rabs_congr (Rneg_Rsub _ _))
    have hd' : Rle (Rabs (Rsub (nearJ G f g (j + nearCN G f g))
          (nearJ G f g (k + nearCN G f g))))
        (ofQ (⟨(nearCN G f g : Int), 2 ^ (j + nearCN G f g)⟩ : Q) (Nat.two_pow_pos _)) :=
      Rle_trans (Rle_of_Req (Req_symm hflip)) hd
    refine Rle_trans (Rle_of_Rabs_le hd') ?_
    refine Rle_ofQ_ofQ (Nat.two_pow_pos _) (nearC_den G f g j k) ?_
    exact Qle_self_add (by show (0 : Int) ≤ (nearCN G f g : Int); omega)

/-- **The reindexed truncations are Bishop-regular.** -/
theorem nearX_RReg (G : ClosedGeom) (f g : L2Test) :
    RReg (fun j => nearJ G f g (j + nearCN G f g)) :=
  RReg_of_real_bound _ (nearC G f g) (nearC_den G f g) (nearC_le G f g) (nearX_bound G f g)

/-- **★ THE `x = 1` LOWER-END IMPROPER LIMIT**:
    `ArchNearPart(f,g) = lim_k ∫_{1+2⁻ᵏ}^{2} N(x)·(1/(x−1)) dx` — the Bishop limit of the honest
    truncations, with the PROVED geometric regularity.  No value at the singular point is invented. -/
def ArchNearPart (G : ClosedGeom) (f g : L2Test) : Real :=
  Rlim (fun j => nearJ G f g (j + nearCN G f g)) (nearX_RReg G f g)

-- Seal the truncation tower (in-file defeq uses are above).
attribute [irreducible] nearIntegrand nearJ nearStrip ArchNearPart

end UOR.Bridge.F1Square.Square
