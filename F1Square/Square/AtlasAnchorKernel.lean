/-
F1 square — **THE ANCHOR KERNEL: the cross form in the anchor alone** (`AtlasAnchorKernel.lean`, target-free).

On a fully source-coherent element `z` the shift law `U_x(t) = x^{-1/2}·V̂(t/x)` (on `t ≥ a·x`) and the two zero
laws (`U_x(t) = 0` for `t ≤ a·x`, `V̂(s) = 0` for `s ≤ a`) eliminate every recovered field from the cross form:
with `h = V̂` (the far anchor, constant in the scale),

    `crossForm5 z = anchorKernel5 h`,

where `anchorKernel5 h` transparently contains the five terms in `h` alone — pole `−¼∫∫ 8(1+1/x)wr·x^{-1/2}h(t/x)·h(t)`,
prime `¼Σ_n∫ 8Λ(n)wr·n^{-1/2}h(t/n)·h(t)` (the nonlocal mate `t/n`), constant `¼∫ 4(log4π+γ)wr·h(t)²`
(`constDens5 = 4(log4π+γ)wr`, so the constant coefficient is `(log4π+γ)·N_h`),
compact tail `¼∫∫ 8wr·Z_h·W_h` with `Z_h = x̄K(x̄)(x^{-1/2}h(t/x) − h(t)/x̄)`, `W_h = h(t)/x̄`, far `−¼∫ 8·fc·wr·h(t)²`.
The identity uses the ε-argument at the threshold `t = a·x` (exact above it by the shift law, both sides `0`
below it by the zero laws, Lipschitz in between).  No sign, no bound.
`anchorKernel5` accepts any certified field; its one-variable reading (`h(x,t) = H(t)`) is the ANCHOR-PROFILE case
`AnchorProfile C h` (scale-constant, vanishing below `a`; AtlasAnchorAutocorr), inhabited by `anchorOf z` for every
fully coherent `z`, where it is the autocorrelation form `anchorKernel5_autocorr`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasCoherentBridge

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (1) The shifted anchor fields `x^{-1/2}·h(t̄/x̄)` and `n^{-1/2}·h(t̄/n)`.
-- ===========================================================================

/-- `(x,t) ↦ t̄·(1/max(x̄,1))` — the argument `t/x` of the shift, clamped on both coordinates. -/
def shiftArgF (C : NormCtx) : CField := mulF (tBandF C) (rOneClF C)
theorem shiftArgF_F (C : NormCtx) (x t : Real) : (shiftArgF C).F x t = Rmul (tBand C t) (rOne (xcl C x)) := rfl

/-- `(x,t) ↦ x̄^{-1/2}·h(1, t̄/x̄)`. -/
def shiftUF (C : NormCtx) (h : CField) : CField :=
  mulF (invSqClF C) (comp2F h oneConstF (shiftArgF C))
theorem shiftUF_F (C : NormCtx) (h : CField) (x t : Real) :
    (shiftUF C h).F x t = Rmul (invSq C (xcl C x)) (h.F one (Rmul (tBand C t) (rOne (xcl C x)))) := rfl

/-- `t ↦ t̄·(1/n)`. -/
def nArgF (C : NormCtx) (m : Nat) : CField := mulF (tBandF C) (invNF m)
/-- `t ↦ n^{-1/2}·h(1, t̄/n)`. -/
def shiftUnF (C : NormCtx) (m : Nat) (h : CField) : CField :=
  mulF (invSqNF C m) (comp2F h oneConstF (nArgF C m))
theorem shiftUnF_F (C : NormCtx) (m : Nat) (h : CField) (x t : Real) :
    (shiftUnF C m h).F x t = Rmul (invSq C (upR m)) (h.F one (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m)))) := rfl

/-- `Z_h = x̄K(x̄)·(x^{-1/2}h(t/x) − h/x̄)` and `W_h = h/x̄`. -/
def ZhF (C : NormCtx) (k : Nat) (h : CField) : CField :=
  mulF (mulF (xclF C) (KxF C k)) (subF (shiftUF C h) (mulF (rOneClF C) h))
def WhF (C : NormCtx) (h : CField) : CField := mulF (rOneClF C) h

/-- **★ THE ANCHOR KERNEL**: the five cross terms in the anchor `h` alone. -/
def anchorKernel5 (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (h : CField) : Real :=
  Radd (Radd (Radd (Radd
    (intX C (mulF (poleDens5 C) (crossF (shiftUF C h) (negF h))) (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C))
    (RsumN (fun m => intT C (mulF (primeDens5 C m) (crossF (shiftUnF C m h) h)) one) C.X))
    (intT C (mulF (constDens5 C) (crossF h h)) one))
    (intX C (mulF (tailDens5 C) (crossF (ZhF C k h) (WhF C h))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k)
      (tailGap_num_nonneg C k hk)))
    (intT C (mulF (farDens5 C fc) (crossF h (negF h))) one)

/-- The anchor of a carrier element: its far port `2·A_far`. -/
def anchorOf (z : Carrier5) : CField := recVFarF z

-- ===========================================================================
-- (2) `U^{rec}_x(t) = x^{-1/2}·V̂(t/x)` at every real scale of the band (shift law + zero laws + ε-argument).
-- ===========================================================================

theorem rOne_eq_Rinv_of_ge_one {x : Real} (hx1 : Rle one x) {kx : Nat} (hkx : Qlt (Qbound kx) (x.seq kx)) :
    Req (rOne x) (Rinv x kx hkx) := clampedInv_eq_of_ge hkx hx1

/-- The exact case `t ≥ a·x`. -/
theorem recU_shift_exact (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) {x t : Real}
    (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) (hax : Rle (Rmul (ofQ C.a C.had) x) t) :
    Req ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))) := by
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hx1
  refine Req_trans (hz.shift x t hx1 hxB kx hkx hax) ?_
  exact Rmul_congr (Req_refl _) ((recVFarF z).hfct one (Rmul_congr (Req_refl t) (Req_symm (rOne_eq_Rinv_of_ge_one hx1 hkx))))

/-- Below the threshold both sides vanish: `t ≤ a·x` ⟹ `U = 0` and `V̂(t/x) = 0`. -/
theorem recU_shift_zero (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) {x t : Real}
    (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) (hta : Rle t (Rmul (ofQ C.a C.had) x)) :
    Req ((recUF C k z).F x t) zero ∧ Req ((recVFarF z).F one (Rmul t (rOne x))) zero := by
  refine ⟨hz.zero_real x t hx1 hxB hta, hz.anchor_zero one _ ?_⟩
  -- t·(1/x) ≤ (a·x)·(1/x) = a
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_clampedInv _ _ _ _) hta) (Rle_of_Req ?_)
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_clampedInv_one x hx1)) (Rmul_one _))

/-- The uniform bound of the difference `|U − x^{-1/2}·V̂(t/x)|` in terms of the field bounds. -/
def shiftDiffBound (C : NormCtx) (k : Nat) (z : Carrier5) : Q :=
  add (recUF C k z).M (mul (Qinv (canonC C)) (recVFarF z).M)
theorem shiftDiffBound_den (C : NormCtx) (k : Nat) (z : Carrier5) : 0 < (shiftDiffBound C k z).den :=
  add_den_pos (recUF C k z).hMd (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (recVFarF z).hMd)

/-- The Lipschitz constant of `t ↦ U(x,t) − x^{-1/2}·V̂(t/x)`: `Lt_U + (1/c)·Lt_h` (`1/x ≤ 1`). -/
def shiftLipQ (C : NormCtx) (k : Nat) (z : Carrier5) : Q :=
  add (recUF C k z).Lt (mul (Qinv (canonC C)) (recVFarF z).Lt)
theorem shiftLipQ_den (C : NormCtx) (k : Nat) (z : Carrier5) : 0 < (shiftLipQ C k z).den :=
  add_den_pos (recUF C k z).hLtd (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (recVFarF z).hLtd)
theorem shiftLipQ_num (C : NormCtx) (k : Nat) (z : Carrier5) : 0 ≤ (shiftLipQ C k z).num :=
  Qadd_num_nonneg_loc (recUF C k z).hLtn (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) (recVFarF z).hLtn)

/-- `|x^{-1/2}·(h(t·r) − h(t'·r))| ≤ (1/c)·Lt_h·|t − t'|` for `1 ≤ x`. -/
theorem shift_lip_t (C : NormCtx) (z : Carrier5) {x : Real} (hx1 : Rle one x) (t t' : Real) :
    Rle (Rabs (Rsub (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t' (rOne x))))))
        (Rmul (ofQ (mul (Qinv (canonC C)) (recVFarF z).Lt) (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (recVFarF z).hLtd)) (Rabs (Rsub t t'))) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib _ _ _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  have hr1 : Rle (Rabs (rOne x)) one :=
    Rle_trans (rOne_bd x) (Rle_of_Req (ofQ_congr (Qinv_den_pos (by decide)) (by decide) (by decide)))
  have hh : Rle (Rabs (Rsub ((recVFarF z).F one (Rmul t (rOne x))) ((recVFarF z).F one (Rmul t' (rOne x)))))
      (Rmul (ofQ (recVFarF z).Lt (recVFarF z).hLtd) (Rabs (Rsub t t'))) := by
    refine Rle_trans ((recVFarF z).hlipt one _ _) (Rmul_le_Rmul_left (Rnonneg_ofQ _ (recVFarF z).hLtn) ?_)
    -- |t·r − t'·r| = |t − t'|·|r| ≤ |t − t'|
    refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Req_symm (Rsub_mul_ac _ _ _))) (Rabs_Rmul _ _))) ?_
    exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_Rabs _) hr1) (Rle_of_Req (Rmul_one _))
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ _ (recVFarF z).hLtn) (Rnonneg_Rabs _)) (invSq_bd C x) hh) ?_
  exact Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ _ _) (Req_refl _)))

/-- The difference is Lipschitz in `t` with constant `shiftLipQ`. -/
theorem shift_diff_lip (C : NormCtx) (k : Nat) (z : Carrier5) {x : Real} (hx1 : Rle one x) (t t' : Real) :
    Rle (Rabs (Rsub (Rsub ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))))
                    (Rsub ((recUF C k z).F x t') (Rmul (invSq C x) ((recVFarF z).F one (Rmul t' (rOne x)))))))
        (Rmul (ofQ (shiftLipQ C k z) (shiftLipQ_den C k z)) (Rabs (Rsub t t'))) :=
  lip_add_fl (f := fun t => (recUF C k z).F x t) (g := fun t => Rneg (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))))
    (recUF C k z).hLtd (Qmul_den_pos (Qinv_den_pos (canonC_num C)) (recVFarF z).hLtd) ((recUF C k z).hlipt x)
    (lip_neg_pi _ (shift_lip_t C z hx1)) t t'

/-- The integer ceiling of the Lipschitz constant. -/
def shiftN (C : NormCtx) (k : Nat) (z : Carrier5) : Nat := xBound (ofQ (shiftLipQ C k z) (shiftLipQ_den C k z))

/-- **The ε-estimate at the threshold `t = a·x`**: `|U(x,t) − x^{-1/2}V̂(t/x)| ≤ N/(j+1)` for every `j`. -/
theorem recU_shift_le_eps (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) {x t : Real}
    (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) (j : Nat) :
    Rle (Rabs (Rsub ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x))))))
        (ofQ (⟨((shiftN C k z : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  rcases Rle_or_Rle (x := Rsub t (Rmul (ofQ C.a C.had) x)) (q1 := (⟨0, 1⟩ : Q)) (q2 := (⟨1, j + 1⟩ : Q))
      (by decide) (Nat.succ_pos j) (Qlt_zero_inv_succ j) with hB | hA
  · -- t − ε ≤ a·x: both sides vanish at t − ε, and the difference is Lipschitz
    have hle : Rle (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))) (Rmul (ofQ C.a C.had) x) := by
      -- t − ε ≤ ax  ⟸  t − ax ≤ ε
      refine Rle_of_Rnonneg_Rsub ?_
      have e : Req (Rsub (Rmul (ofQ C.a C.had) x) (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))))
          (Rsub (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j)) (Rsub t (Rmul (ofQ C.a C.had) x))) := by
        -- ax − (t − ε) = ε − (t − ax)
        refine Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_refl _) (Rneg_neg _)))) ?_
        refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_comm _ _) ?_)
        refine Radd_congr (Req_refl _) ?_
        refine Req_trans (Radd_comm _ _) ?_
        exact Req_symm (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_refl _) (Rneg_neg _)))
      exact Rnonneg_congr (Req_symm e) (Rnonneg_Rsub_of_Rle hB)
    have h0 := recU_shift_zero C k hz hx1 hxB hle
    have hzero : Req (Rsub ((recUF C k z).F x (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))))
        (Rmul (invSq C x) ((recVFarF z).F one (Rmul (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))) (rOne x))))) zero :=
      Req_trans (Rsub_congr h0.1 (Req_trans (Rmul_congr (Req_refl _) h0.2) (Rmul_zero _))) (Radd_zero _)
    -- |D(t)| = |D(t) − D(t − ε)| ≤ L·ε ≤ N·ε
    have hstep := shift_diff_lip C k z hx1 t (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j)))
    have hD : Req (Rsub ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))))
        (Rsub (Rsub ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))))
              (Rsub ((recUF C k z).F x (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))))
                    (Rmul (invSq C x) ((recVFarF z).F one (Rmul (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))) (rOne x)))))) :=
      Req_symm (Req_trans (Rsub_congr (Req_refl _) hzero) (Rsub_zero _))
    have hε : Req (Rabs (Rsub t (Rsub t (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j))))) (ofQ (⟨1, j + 1⟩ : Q) (Nat.succ_pos j)) := by
      refine Req_trans (Rabs_congr ?_) (Rabs_ofQ_nonneg (Nat.succ_pos j) (show (0 : Int) ≤ 1 by decide))
      -- t − (t − ε) = ε
      refine Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_refl _) (Rneg_neg _)))) ?_
      refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_congr (Radd_neg _) (Req_refl _)) ?_)
      exact Req_trans (Radd_comm _ _) (Radd_zero _)
    refine Rle_trans (Rle_of_Req (Rabs_congr hD)) (Rle_trans hstep ?_)
    refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) hε)) ?_
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ (Nat.succ_pos j) (show (0 : Int) ≤ 1 by decide))
      (Rle_of_Rabs_le (Rabs_le_ofQ_xBound (ofQ (shiftLipQ C k z) (shiftLipQ_den C k z))))) ?_
    refine Rle_of_Req (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (Nat.succ_pos j)) (ofQ_congr _ _ ?_))
    show Qeq (mul (⟨((shiftN C k z : Nat) : Int), 1⟩ : Q) (⟨1, j + 1⟩ : Q)) (⟨((shiftN C k z : Nat) : Int), j + 1⟩ : Q)
    simp only [Qeq, mul]; push_cast; ring_uor
  · -- t ≥ a·x: exact
    have hax : Rle (Rmul (ofQ C.a C.had) x) t := Rle_of_Rnonneg_Rsub (Rnonneg_of_Rle_zero hA)
    have h := recU_shift_exact C k hz hx1 hxB hax
    refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Req_trans (Rsub_congr h (Req_refl _)) (Radd_neg _))) Rabs_zero)) ?_
    exact Rle_zero_of_Rnonneg (Rnonneg_ofQ (Nat.succ_pos j) (Int.ofNat_nonneg _))

/-- **★ THE SHIFT LAW AT EVERY REAL SCALE OF THE BAND**: `U^{rec}_x(t) = x^{-1/2}·V̂(t/x)` for every `t`. -/
theorem recU_shift_of_fullCoherent (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) {x : Real} (t : Real)
    (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Req ((recUF C k z).F x t) (Rmul (invSq C x) ((recVFarF z).F one (Rmul t (rOne x)))) := by
  refine Rle_antisymm ?_ ?_
  · exact Rle_of_Rsub_le_eps (C := shiftN C k z) (fun j => Rle_trans (Rle_Rabs_self _) (recU_shift_le_eps C k hz hx1 hxB j))
  · exact Rle_of_Rsub_le_eps (C := shiftN C k z) (fun j => Rle_trans (Rle_Rabs_self _)
      (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (recU_shift_le_eps C k hz hx1 hxB j)))

-- ===========================================================================
-- (3) ★ THE CROSS FORM IS THE ANCHOR KERNEL on the fully coherent carrier.
-- ===========================================================================

/-- `1/max(n,1) = 1/n` for the place `n = m + 1`. -/
theorem rOne_upR (m : Nat) : Req (rOne (upR m)) (ofQ (invNQ m) (Nat.succ_pos m)) := by
  refine Req_trans (clampedInv_ofQ (a := (⟨1, 1⟩ : Q)) (q := (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (by decide) (by decide) Nat.one_pos
    (by show (0 : Int) < ((m + 1 : Nat) : Int); omega) (one_le_upQ m)) ?_
  refine ofQ_congr _ (Nat.succ_pos m) ?_
  show (1 : Int) * ((m + 1 : Nat) : Int) = 1 * (((((m + 1 : Nat) : Int)).toNat : Nat) : Int)
  simp only [Int.toNat_ofNat]

theorem invSq_congr_ak (C : NormCtx) {x y : Real} (h : Req x y) : Req (invSq C x) (invSq C y) := by
  unfold invSq; exact invSqrtTwoF_congr _ _ _ _ _ _ _ _ _ _ h

theorem negF_F_ak (u : CField) (x t : Real) : (negF u).F x t = Rneg (u.F x t) := rfl
theorem mulF_crossF_F (d u v : CField) (x t : Real) :
    (mulF d (crossF u v)).F x t = Rmul (d.F x t) (Rmul cQ (Rmul (u.F x t) (v.F x t))) := rfl
theorem ZhF_F (C : NormCtx) (k : Nat) (h : CField) (x t : Real) :
    (ZhF C k h).F x t = Rmul (Rmul (xcl C x) (Kx C k x)) (Rsub ((shiftUF C h).F x t) (Rmul (rOne (xcl C x)) (h.F x t))) := rfl
theorem WhF_F (C : NormCtx) (h : CField) (x t : Real) : (WhF C h).F x t = Rmul (rOne (xcl C x)) (h.F x t) := rfl

/-- On the pole support, `recUF z = shiftUF (anchorOf z)` pointwise. -/
theorem recU_eq_shiftU (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) {x t : Real}
    (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) (ht : InWin C t) :
    Req ((recUF C k z).F x t) ((shiftUF C (anchorOf z)).F x t) := by
  rw [shiftUF_F]
  refine Req_trans (recU_shift_of_fullCoherent C k hz t hx1 hxB) ?_
  have hxcl : Req (xcl C x) x := xcl_eq_of_band C hx1 hxB
  have htb : Req (tBand C t) t := tBand_eq_of_win C ht.1 ht.2
  exact Rmul_congr (invSq_congr_ak C (Req_symm hxcl)) ((recVFarF z).hfct one (Rmul_congr (Req_symm htb) (clampedInv_congr _ _ _ (Req_symm hxcl))))

/-- On the Haar window, `anchorDual z = anchorOf z` at every scale. -/
theorem anchorDual_eq_anchorOf (C : NormCtx) (k : Nat) (hk : 1 ≤ k) {z : Carrier5} (hz : FullSourceCoherent5 C k z) (x t : Real)
    (ht : InWin C t) : Req ((anchorDual C k hk z).F x t) ((anchorOf z).F x t) :=
  anchorDual_eq_far_of_fullCoherent C k hk hz x t ht

/-- At the active places, `primeUJ z m = shiftUnF m (anchorOf z)` on the Haar window (`m < X`). -/
theorem primeUJ_eq_shiftUn (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) {z : Carrier5} (hz : FullSourceCoherent5 C k z)
    (m : Nat) (hm : m < C.X) (x t : Real) (ht : InWin C t) :
    Req ((primeUJ C k hw0 hk z m).F x t) ((shiftUnF C m (anchorOf z)).F x t) := by
  rw [shiftUnF_F]
  have htb : Req (tBand C t) t := tBand_eq_of_win C ht.1 ht.2
  have hshift : Req ((recUF C k z).F (upR m) t) (Rmul (invSq C (upR m)) ((anchorOf z).F one (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))))) := by
    refine Req_trans (recU_shift_of_fullCoherent C k hz t (one_le_upR_R m) (upR_le_B_R C m hm)) ?_
    exact Rmul_congr (Req_refl _) ((recVFarF z).hfct one (Rmul_congr (Req_symm htb) (rOne_upR m)))
  by_cases hm1 : 1 ≤ m
  · have e : primeUJ C k hw0 hk z m = readFiber C k m hw0 hk z := by unfold primeUJ; rw [dif_pos hm1]
    rw [e]
    exact Req_trans (readFiber_eq_recU_of_fullCoherent C k m hw0 hk hm hm1 hz x t ht) hshift
  · have e : primeUJ C k hw0 hk z m = anchorDual C k hk z := by unfold primeUJ; rw [dif_neg hm1]
    have hm0 : m = 0 := by omega
    rw [e]
    subst hm0
    refine Req_trans (anchorDual_eq_anchorOf C k hk hz x t ht) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (hz.far_const x one t)) ?_
    refine Req_trans (Req_symm (recU_one_eq_far_of_fullCoherent C k hz t ht.1)) ?_
    refine Req_trans (Req_symm ((recUF C k z).hfcx t upR_zero_eq_one)) ?_
    exact hshift

/-- **★ `crossForm5 z = anchorKernel5 (anchorOf z)`** for every fully source-coherent `z` (`w > 0`, `k ≥ 1`). -/
theorem crossForm5_eq_anchorKernel (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) {z : Carrier5}
    (hz : FullSourceCoherent5 C k z) :
    Req (crossForm5 C k hw0 hk fc z) (anchorKernel5 C k hk fc (anchorOf z)) := by
  unfold crossForm5 anchorKernel5
  refine Radd_congr (Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_) ?_
  · -- pole
    refine intX_congr_win C _ _ (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C) ?_
    intro s hs0 hs1 y hy0 hy1
    have hx1 := affine_pole_ge_one C s hs0
    have hxB := affine_pole_le_B C s hs1
    have ht := inWin_of_affine C y hy0 hy1
    rw [mulF_crossF_F, mulF_crossF_F, negF_F_ak, negF_F_ak]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (recU_eq_shiftU C k hz hx1 hxB ht)
      (Rneg_congr (anchorDual_eq_anchorOf C k hk hz _ _ ht))))
  · -- prime
    refine RsumN_congr C.X (fun m hm => ?_)
    refine intT_congr_win C _ _ one ?_
    intro y hy0 hy1
    have ht := inWin_of_affine C y hy0 hy1
    rw [mulF_crossF_F, mulF_crossF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (primeUJ_eq_shiftUn C k hw0 hk hz m hm one _ ht)
      (anchorDual_eq_anchorOf C k hk hz one _ ht)))
  · -- constant
    refine intT_congr_win C _ _ one ?_
    intro y hy0 hy1
    have ht := inWin_of_affine C y hy0 hy1
    rw [mulF_crossF_F, mulF_crossF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (anchorDual_eq_anchorOf C k hk hz one _ ht)
      (anchorDual_eq_anchorOf C k hk hz one _ ht)))
  · -- compact tail
    refine intX_congr_win C _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) ?_
    intro s hs0 hs1 y hy0 hy1
    have hx1 : Rle one _ := Rle_trans (Rle_ofQ_ofQ (by decide) (tailLo_den k) (one_le_tailLo k)) (affine_tail_ge_lo C k hk s hs0)
    have hxB := affine_tail_le_B C k hk s hs1
    have ht := inWin_of_affine C y hy0 hy1
    have hU := recU_eq_shiftU C k hz hx1 hxB ht
    have hV := anchorDual_eq_anchorOf C k hk hz (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) (affineMap C.a C.w C.had C.hw y) ht
    rw [mulF_crossF_F, mulF_crossF_F, ZrecJ_F, WrecJ_F, ZhF_F, WhF_F]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr
      (Rmul_congr (Req_refl _) (Rsub_congr hU (Rmul_congr (Req_refl _) hV))) (Rmul_congr (Req_refl _) hV)))
  · -- far
    refine intT_congr_win C _ _ one ?_
    intro y hy0 hy1
    have ht := inWin_of_affine C y hy0 hy1
    rw [mulF_crossF_F, mulF_crossF_F, negF_F_ak, negF_F_ak]
    exact Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (anchorDual_eq_anchorOf C k hk hz one _ ht)
      (Rneg_congr (anchorDual_eq_anchorOf C k hk hz one _ ht))))

end UOR.Bridge.F1Square.Square
