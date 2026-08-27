/-
F1 square — **THE BOUNDED ANCHOR EXTRACTOR BY GENUINE SCALE INTEGRATION** (`AtlasAnchorExtract.lean`, target-free).

The anchor `V(t)` is read from the pole and compact-tail CUT ports of a five-channel carrier element `z` by ONE
scale integral over the compact tail window `[1 + 2^{-k}, B]`, with the EXACT-RECOVERY WEIGHT `P_k(x̄)/4`
(the reciprocal of the algebraic coefficient `4/P_k` of the pointwise recovery `V = 4·(q_k·A_pole − A_tail)/P_k`, i.e.
`q_k·A_pole − A_tail = (P_k/4)·V`).  It is NOT the source-metric dual density: against the pole/tail metric with densities
`8(1+r)wr` and `8wr`, the dual constant of the recovery functional is `a_V(x) = (2/P_k²)·(q_k²/(1+r) + 1)`, so the
energy-optimal weight would be `∝ a_V(x)^{-1} = P_k²/(2(q_k²/(1+r) + 1))`; the weight used here is the algebraic one.
The certified constant `c_k` below grows like `4^k` at fixed context: it supplies no uniform control and is not to be fed
into the scheduled limit:

    `anchorAx z (t) = ( ∫_{[1+2^{-k},B]} (q_k(x̄)·A_pole(x̄,t) − A_tail(x̄,t)) dx ) / ( ∫_{[1+2^{-k},B]} P_k(x̄)/4 dx )`.

No pointwise division: the denominator is a test-INDEPENDENT positive constant `≥ (B − 1 − 2^{-k})/(4B)`
(`anchorDen_ge`), inverted once at an EXPLICIT witness index (`denInvAx`, no choice).  On the cut analysis
of every test the numerator integrand is `(P_k(x̄)/4)·V(t)` at every scale (the anchor identity
`anchor_from_pole_tail_ge_one`), so the extractor is EXACT: `anchorAx (A_k f) = V(f)` (`anchorAx_source`),
for every Haar coordinate `t`, with no support or window hypothesis.

THE SOURCE-METRIC BOUND (`anchorAx_bound`), for EVERY carrier element `z` (not only analyses), with the
compact-tail density `8·w·r(t)` as the anchor weight:

    `∫₀¹ 8wr·anchor² ≤ c_k · ( poleCutEnergy(z) + tailCutEnergy(z) )`,   `c_k = (4B/gap_k)²·gap_k·2(B·M_K + 1)²`,

`gap_k = B − 1 − 2^{-k}`, `M_K` the bound of the floored kernel: Cauchy–Schwarz on the scale integral
(`unit_cs_ax`, `anchorXInt_sq_le`), the pointwise estimate `(q·A_p − A_t)² ≤ 2(BM_K+1)²(A_p² + A_t²)`
(`num_sq_le_ax`), the Fubini swap of the two certified integrals (`fubini_ax`, from
`bern2D_general_swap_window`), and the monotonicity of the pole window `[1,B] ⊇ [1+2^{-k},B]`
(`intX_tail_le_pole_ax`).  This is a bound on the ANCHOR by two cut energies — an honest estimate, not a
field, not a hypothesis, and not a bound on any colligation; nothing here is a sign claim about the crux.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasCarrier5
import F1Square.Square.AtlasCutRecovery
import F1Square.Square.Bern2DWindowSwap
import F1Square.Square.IntegralCSFull
import F1Square.Square.TestAlgebra

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (0) The scale integral of a field at a fixed Haar coordinate, as a certified function of that coordinate.
-- ===========================================================================

/-- `t ↦ ∫_{[lo, lo+w]} H(x, t) dx`. -/
def anchorXInt (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) : Real :=
  riemannIntegralI (f := fun x => H.F x t) H.hLxd H.hLxn (H.hlipx t) (fun _ _ h => H.hfcx t h) lo w hlo hw hwn

/-- The unit-parametrized core `∫₀¹ H(lo + w·u, t) du`. -/
def anchorXCore (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) : Real :=
  riemannIntegral (f := fun u => H.F (affineMap lo w hlo hw u) t) (L := mul H.Lx w)
    (Qmul_den_pos H.hLxd hw) (Int.mul_nonneg H.hLxn hwn)
    (affine_lip H.hLxd H.hLxn (H.hlipx t) lo w hlo hw hwn)
    (fun _ _ h => H.hfcx t (affineMap_congr lo w hlo hw h))

theorem anchorXInt_eq_core (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    anchorXInt H lo w hlo hw hwn t = Rmul (ofQ w hw) (anchorXCore H lo w hlo hw hwn t) := rfl

theorem anchorXCore_lip (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t',
    Rle (Rabs (Rsub (anchorXCore H lo w hlo hw hwn t) (anchorXCore H lo w hlo hw hwn t'))) (Rmul (ofQ H.Lt H.hLtd) (Rabs (Rsub t t'))) :=
  fun t t' => param_integral_lip (F := fun t u => H.F (affineMap lo w hlo hw u) t) (L := fun _ => mul H.Lx w)
    (fun _ => Qmul_den_pos H.hLxd hw) (fun _ => Int.mul_nonneg H.hLxn hwn)
    (fun t => affine_lip H.hLxd H.hLxn (H.hlipx t) lo w hlo hw hwn)
    (fun t _ _ h => H.hfcx t (affineMap_congr lo w hlo hw h))
    H.hLtd (fun u _ _ t t' => H.hlipt (affineMap lo w hlo hw u) t t') t t'

theorem anchorXCore_fc (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t', Req t t' →
    Req (anchorXCore H lo w hlo hw hwn t) (anchorXCore H lo w hlo hw hwn t') :=
  fun t t' h => param_integral_congr (F := fun t u => H.F (affineMap lo w hlo hw u) t) (L := fun _ => mul H.Lx w)
    (fun _ => Qmul_den_pos H.hLxd hw) (fun _ => Int.mul_nonneg H.hLxn hwn)
    (fun t => affine_lip H.hLxd H.hLxn (H.hlipx t) lo w hlo hw hwn)
    (fun t _ _ h => H.hfcx t (affineMap_congr lo w hlo hw h))
    t t' (fun _ => H.hfct _ h)

theorem anchorXCore_bd (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    Rle (Rabs (anchorXCore H lo w hlo hw hwn t)) (ofQ H.M H.hMd) :=
  riemannIntegral_abs_le_unit_real _ _ _ _ _ (fun u _ _ => H.hbd (affineMap lo w hlo hw u) t)

theorem anchorXInt_lip (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t',
    Rle (Rabs (Rsub (anchorXInt H lo w hlo hw hwn t) (anchorXInt H lo w hlo hw hwn t')))
        (Rmul (ofQ (mul w H.Lt) (Qmul_den_pos hw H.hLtd)) (Rabs (Rsub t t'))) :=
  lip_const_mul_left (F := anchorXCore H lo w hlo hw hwn) H.hLtd H.hLtn (anchorXCore_lip H lo w hlo hw hwn) (ofQ w hw) hw (abs_ofQ_le hw hwn)

theorem anchorXInt_bd (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    Rle (Rabs (anchorXInt H lo w hlo hw hwn t)) (ofQ (mul w H.M) (Qmul_den_pos hw H.hMd)) :=
  abs_mul_bd hw H.hMd H.hMn (abs_ofQ_le hw hwn) (anchorXCore_bd H lo w hlo hw hwn t)

theorem anchorXInt_fc (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t', Req t t' →
    Req (anchorXInt H lo w hlo hw hwn t) (anchorXInt H lo w hlo hw hwn t') :=
  fun t t' h => Rmul_congr (Req_refl _) (anchorXCore_fc H lo w hlo hw hwn t t' h)

/-- **The scale integral as a certified field of the Haar coordinate** (constant in the scale). -/
def anchorXIntF (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : CField :=
  ofT (anchorXInt H lo w hlo hw hwn) (L := mul w H.Lt) (M := mul w H.M)
    (Qmul_den_pos hw H.hLtd) (Qmul_num_nonneg hwn H.hLtn) (Qmul_den_pos hw H.hMd) (Qmul_num_nonneg hwn H.hMn)
    (anchorXInt_lip H lo w hlo hw hwn) (anchorXInt_bd H lo w hlo hw hwn) (anchorXInt_fc H lo w hlo hw hwn)

theorem anchorXIntF_F (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x t : Real) :
    (anchorXIntF H lo w hlo hw hwn).F x t = anchorXInt H lo w hlo hw hwn t := rfl

-- ===========================================================================
-- (1) Window plumbing with independent certificates: real scalar, monotonicity.
-- ===========================================================================

section Plumbing
variable {f g h : Real → Real} {Lf Lg Lh : Q}

/-- `h ≈ c·f` pointwise (real `c`) ⟹ `∫_{[lo,lo+w]} h ≈ c·∫_{[lo,lo+w]} f`. -/
theorem intI_smul_ax (c : Real) (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) (Rmul c (f y)))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI hhd hhn hhlip hhfc lo w hlo hw hwn) (Rmul c (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn)) := by
  unfold riemannIntegralI
  refine Req_trans (Rmul_congr (Req_refl (ofQ w hw)) (intU_smul_free c (Qmul_den_pos hfd hw) (Int.mul_nonneg hfn hwn)
    (affine_lip hfd hfn hflip lo w hlo hw hwn) (fun _ _ e => hffc _ _ (affineMap_congr lo w hlo hw e))
    (Qmul_den_pos hhd hw) (Int.mul_nonneg hhn hwn) (affine_lip hhd hhn hhlip lo w hlo hw hwn)
    (fun _ _ e => hhfc _ _ (affineMap_congr lo w hlo hw e)) (fun u => hh (affineMap lo w hlo hw u)))) ?_
  exact swap_w_ac _ _ _

/-- `f ≤ g` pointwise ⟹ `∫_{[lo,lo+w]} f ≤ ∫_{[lo,lo+w]} g` (independent certificates). -/
theorem intI_le_ax (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y)) (hfg : ∀ y, Rle (f y) (g y))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Rle (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn) (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn) := by
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hg' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hglip
  refine Rle_trans (Rle_of_Req (riemannIntegralI_certif_irrel _ _ hflip hffc hSd hSn hf' hffc lo w hlo hw hwn)) ?_
  refine Rle_trans (riemannIntegralI_le hSd hSn hf' hffc hg' hgfc hfg lo w hlo hw hwn) ?_
  exact Rle_of_Req (riemannIntegralI_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc lo w hlo hw hwn)

/-- Window-local monotonicity (`f ≤ g` on `[lo, lo+w]` only), independent certificates. -/
theorem intI_le_unit_ax (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (hfg : ∀ u, Rle zero u → Rle u one → Rle (f (affineMap lo w hlo hw u)) (g (affineMap lo w hlo hw u))) :
    Rle (riemannIntegralI hfd hfn hflip hffc lo w hlo hw hwn) (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn) := by
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hg' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hglip
  refine Rle_trans (Rle_of_Req (riemannIntegralI_certif_irrel _ _ hflip hffc hSd hSn hf' hffc lo w hlo hw hwn)) ?_
  refine Rle_trans (riemannIntegralI_le_unit hSd hSn hf' hffc hg' hgfc lo w hlo hw hwn hfg) ?_
  exact Rle_of_Req (riemannIntegralI_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc lo w hlo hw hwn)

/-- `f ≤ g` pointwise ⟹ `∫₀¹ f ≤ ∫₀¹ g` (independent certificates). -/
theorem intU_le_ax (hfd : 0 < Lf.den) (hfn : 0 ≤ Lf.num)
    (hflip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hffc : ∀ x y, Req x y → Req (f x) (f y))
    (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y)) (hfg : ∀ y, Rle (f y) (g y)) :
    Rle (riemannIntegral hfd hfn hflip hffc) (riemannIntegral hgd hgn hglip hgfc) := by
  have hSd : 0 < (add Lf Lg).den := add_den_pos hfd hgd
  have hSn : 0 ≤ (add Lf Lg).num := Qadd_num_nonneg_loc hfn hgn
  have hf' := lip_weaken_fl hfd hSd (Qle_add_right_nonneg hgn) hflip
  have hg' := lip_weaken_fl hgd hSd (Qle_add_left_nonneg hfn) hglip
  refine Rle_trans (Rle_of_Req (riemannIntegral_certif_irrel _ _ hflip hffc hSd hSn hf' hffc)) ?_
  refine Rle_trans (riemannIntegral_le hSd hSn hf' hffc hg' hgfc hfg) ?_
  exact Rle_of_Req (riemannIntegral_certif_irrel _ _ hg' hgfc hgd hgn hglip hgfc)

end Plumbing

-- ===========================================================================
-- (2) The exact-recovery weight `P_k(x̄)/4`, the clamped ports, the numerator field.
-- ===========================================================================

/-- The constant field `1`. -/
def anchorOneF : CField :=
  constF one Nat.one_pos (by decide) (abs_ofQ_le (q := (⟨1, 1⟩ : Q)) Nat.one_pos (by decide) : Rle (Rabs one) (ofQ (⟨1, 1⟩ : Q) Nat.one_pos))

/-- `x ↦ 1/max(x̄, 1)`. -/
def rOneClAx (C : NormCtx) : CField := compX rOneF (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)

/-- `x ↦ P_k(x̄) = K_k(x̄)·(x̄ + 1) + 1/max(x̄,1)`. -/
def PkAx (C : NormCtx) (k : Nat) : CField := addF (mulF (KxF C k) (addF (xclF C) anchorOneF)) (rOneClAx C)
theorem PkAx_F (C : NormCtx) (k : Nat) (x t : Real) : (PkAx C k).F x t = Pk k (xcl C x) := rfl

/-- **The exact-recovery weight** `P_k(x̄)/4` (`q_k·A_pole − A_tail = (P_k/4)·V`; not the metric-dual density). -/
def densAx (C : NormCtx) (k : Nat) : CField := smulQF (⟨1, 4⟩ : Q) (by decide) (by decide) (PkAx C k)
theorem densAx_F (C : NormCtx) (k : Nat) (x t : Real) : (densAx C k).F x t = Rmul cQ (Pk k (xcl C x)) := rfl

/-- `x ↦ q_k(x̄) = x̄·K_k(x̄)`. -/
def qkAx (C : NormCtx) (k : Nat) : CField := mulF (xclF C) (KxF C k)
theorem qkAx_F (C : NormCtx) (k : Nat) (x t : Real) : (qkAx C k).F x t = qk k (xcl C x) := rfl

/-- The pole port at the clamped scale. -/
def poleAx (C : NormCtx) (z : Carrier5) : CField := compX z.pole (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)
/-- The tail port at the clamped scale. -/
def tailAx (C : NormCtx) (z : Carrier5) : CField := compX z.tail (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)
theorem poleAx_F (C : NormCtx) (z : Carrier5) (x t : Real) : (poleAx C z).F x t = z.pole.F (xcl C x) t := rfl
theorem tailAx_F (C : NormCtx) (z : Carrier5) (x t : Real) : (tailAx C z).F x t = z.tail.F (xcl C x) t := rfl

/-- **The numerator field** `q_k(x̄)·A_pole(x̄,t) − A_tail(x̄,t)`. -/
def numAx (C : NormCtx) (k : Nat) (z : Carrier5) : CField := subF (mulF (qkAx C k) (poleAx C z)) (tailAx C z)
theorem numAx_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (numAx C k z).F x t = Rsub (Rmul (qk k (xcl C x)) (z.pole.F (xcl C x) t)) (z.tail.F (xcl C x) t) := rfl

-- ===========================================================================
-- (3) The denominator, its explicit positive lower bound, and the reciprocal at an explicit witness.
-- ===========================================================================

/-- **The denominator** `∫_{[1+2^{-k},B]} P_k(x̄)/4 dx` (the density is constant in the Haar coordinate). -/
def anchorDen (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real :=
  anchorXInt (densAx C k) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) one

/-- The lower bound `gap_k · (1/4)·(1/B)`. -/
def denLo (C : NormCtx) (k : Nat) : Q := mul (tailGap C k) (mul (⟨1, 4⟩ : Q) (Qinv (canonB C)))
theorem denLo_den (C : NormCtx) (k : Nat) : 0 < (denLo C k).den :=
  Qmul_den_pos (tailGap_den C k) (Qmul_den_pos (by decide) (Qinv_den_pos (canonB_num C)))
theorem denLo_num_pos (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : 0 < (denLo C k).num :=
  Int.mul_pos (tailGap_num_pos C k hk) (Int.mul_pos (by decide) (Qinv_num_pos (canonB_den C)))

theorem xcl_zero_le_ax (C : NormCtx) (x : Real) : Rle zero (xcl C x) :=
  Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) (xcl_ge_one C x)

/-- **`anchorDen ≥ gap_k/(4B)`**: `P_k(x̄) ≥ 1/B` at every clamped scale. -/
theorem anchorDen_ge (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Rle (ofQ (denLo C k) (denLo_den C k)) (anchorDen C k hk) := by
  unfold anchorDen anchorXInt
  have hpt : ∀ x, Rle zero x → Rle x one →
      Rle (ofQ (mul (⟨1, 4⟩ : Q) (Qinv (canonB C))) (Qmul_den_pos (by decide) (Qinv_den_pos (canonB_num C))))
          ((densAx C k).F (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) x) one) := by
    intro x _ _
    rw [densAx_F]
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (by decide) (Qinv_den_pos (canonB_num C))))) ?_
    exact Rmul_le_Rmul_left (Rnonneg_ofQ (by decide) (by decide)) (Pk_ge_invB C k (xcl_zero_le_ax C _) (xcl_le_B C _))
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ (tailGap_den C k) (Qmul_den_pos (by decide) (Qinv_den_pos (canonB_num C)))))) ?_
  exact riemannIntegralI_ge_const _ _ _ _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) hpt

/-- The reciprocal of the denominator at the explicit witness index `3·(denLo).den`. -/
def denInvAx (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real :=
  Rinv (anchorDen C k hk) (3 * (denLo C k).den)
    (Rlt_Qbound_of_Rle_ofQ (denLo_num_pos C k hk) (denLo_den C k) (anchorDen_ge C k hk))

theorem anchorDen_mul_inv (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Req (Rmul (anchorDen C k hk) (denInvAx C k hk)) one :=
  Rmul_Rinv_self _

theorem denInvAx_nonneg (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Rnonneg (denInvAx C k hk) := Rnonneg_Rinv _ _ _

/-- `1/anchorDen ≤ 1/denLo`. -/
theorem denInvAx_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) :
    Rle (denInvAx C k hk) (ofQ (Qinv (denLo C k)) (Qinv_den_pos (denLo_num_pos C k hk))) :=
  Rinv_le_ofQ_inv (denLo_num_pos C k hk) (denLo_den C k) _ (anchorDen_ge C k hk)

-- ===========================================================================
-- (4) THE ANCHOR EXTRACTOR and its exactness on the analyses.
-- ===========================================================================

/-- **★ THE ANCHOR EXTRACTOR**: `anchorAx z (t) = (1/anchorDen)·∫_{[1+2^{-k},B]} (q_k·A_pole − A_tail)(x̄,t) dx`. -/
def anchorAx (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  smulR (denInvAx C k hk) (anchorXIntF (numAx C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))

theorem anchorAx_F (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (anchorAx C k hk z).F x t
      = Rmul (denInvAx C k hk) (anchorXInt (numAx C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t) := rfl

theorem aCoefGa_congr_ax {u u' v v' : Real} (hu : Req u u') (hv : Req v v') : Req (aCoefGa one u v) (aCoefGa one u' v') :=
  Rmul_congr (Req_refl _) (Rsub_congr (Rmul_congr (Req_refl _) hu) hv)
theorem Zc_congr_x_ax (C : NormCtx) (k : Nat) {x y : Real} (h : Req x y) (f : L2Test) (t : Real) :
    Req (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) y f t) :=
  Rmul_congr (Rmul_congr h ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hfc _ _ h)) (Dc_congr_x C h f t)
theorem Wc_congr_x_ax (C : NormCtx) {x y : Real} (h : Req x y) (f : L2Test) (t : Real) : Req (Wc C x f t) (Wc C y f t) :=
  Rmul_congr (clampedInv_congr _ _ _ h) (Req_refl _)
theorem xcl_idem_ax (C : NormCtx) (x : Real) : Req (xcl C (xcl C x)) (xcl C x) :=
  xcl_eq_of_band C (xcl_ge_one C x) (xcl_le_B C x)

/-- The tail port of the cut analysis at the clamped scale is the tail cut coordinate at `x̄` (`x̄̄ = x̄`). -/
theorem cutAnalysis5_tail_ax (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((cutAnalysis5 C k f).tail.F (xcl C x) t)
        (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t) (Wc C (xcl C x) f t)) := by
  rw [cutAnalysis5_tail]
  exact aCoefGa_congr_ax (Zc_congr_x_ax C k (xcl_idem_ax C x) f t) (Wc_congr_x_ax C (xcl_idem_ax C x) f t)

theorem half_half_eq_quarter_ax : Req (Rmul cH cH) cQ :=
  Req_trans (Rmul_ofQ_ofQ (by decide) (by decide))
    (ofQ_congr (a := mul (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)) (b := (⟨1, 4⟩ : Q)) (Qmul_den_pos (by decide) (by decide)) (by decide) (by decide))

theorem half_two_eq_one_ax : Req (Rmul cH cTwo) one :=
  Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos)
    (ofQ_congr (a := mul (⟨1, 2⟩ : Q) (⟨2, 1⟩ : Q)) (b := (⟨1, 1⟩ : Q)) (Qmul_den_pos (by decide) Nat.one_pos) Nat.one_pos (by decide))

/-- **★ THE NUMERATOR OF A CUT ANALYSIS IS THE DUAL DENSITY TIMES `V`**, at every scale:
    `q_k(x̄)·A_pole(x̄,t) − A_tail(x̄,t) = (P_k(x̄)/4)·V(f,t)`. -/
theorem numAx_source (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((numAx C k (cutAnalysis5 C k f)).F x t) (Rmul ((densAx C k).F x t) (Vc C f t)) := by
  rw [numAx_F, densAx_F, cutAnalysis5_pole]
  have hanc := anchor_from_pole_tail_ge_one C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) (xcl_ge_one C x) f t
  -- hanc : P·(½V) ≈ 2·(q·Ap − At)
  refine Req_trans (Rsub_congr (Req_refl _) (cutAnalysis5_tail_ax C k f x t)) ?_
  -- q·Ap − At ≈ ½·(2·(q·Ap − At)) ≈ ½·(P·(½V)) ≈ (¼·P)·V
  refine Req_trans (Req_symm (Rone_mul _)) ?_
  refine Req_trans (Rmul_congr (Req_symm half_two_eq_one_ax) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl cH) (Req_symm hanc)) ?_
  -- ½·(P·(½V)) ≈ (¼·P)·V
  refine Req_trans (Rmul_congr (Req_refl cH) (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_comm _ _) (Req_refl _)))) ?_
  refine Req_trans (Req_symm (Rmul_assoc cH _ _)) ?_
  refine Req_trans (Rmul_congr (Req_symm (Rmul_assoc cH cH _)) (Req_refl _)) ?_
  exact Rmul_congr (Rmul_congr half_half_eq_quarter_ax (Req_refl _)) (Req_refl _)

/-- The density field is constant in the Haar coordinate. -/
theorem densAx_const_t (C : NormCtx) (k : Nat) (x t : Real) : (densAx C k).F x t = (densAx C k).F x one := rfl

/-- The scale integral of the numerator of a cut analysis is `V(t)·anchorDen`. -/
theorem anchorXInt_numAx_source (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) (t : Real) :
    Req (anchorXInt (numAx C k (cutAnalysis5 C k f)) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)
        (Rmul (Vc C f t) (anchorDen C k hk)) := by
  unfold anchorDen anchorXInt
  refine intI_smul_ax (Vc C f t) _ _ _ _ _ _ _ _ ?_ _ _ _ _ _
  intro x
  refine Req_trans (numAx_source C k f x t) ?_
  rw [densAx_const_t C k x t]
  exact Rmul_comm _ _

/-- **★ THE ANCHOR EXTRACTOR IS EXACT ON EVERY CUT ANALYSIS**: `anchorAx (A_k f) (t) = V(f,t)` for every test `f`
    and every Haar coordinate `t` — no support or window hypothesis. -/
theorem anchorAx_source (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f : L2Test) (x t : Real) :
    Req ((anchorAx C k hk (cutAnalysis5 C k f)).F x t) (Vc C f t) := by
  rw [anchorAx_F]
  refine Req_trans (Rmul_congr (Req_refl _) (anchorXInt_numAx_source C k hk f t)) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) (anchorDen_mul_inv C k hk))) ?_
  exact Rmul_one _


-- ===========================================================================
-- (5) THE SOURCE-METRIC BOUND OF THE EXTRACTOR.
-- ===========================================================================

-- --- (5a) Cauchy–Schwarz on the unit interval: `(∫₀¹ φ)² ≤ ∫₀¹ φ²`. ---

theorem innerI_one_right (φ : L2Test) : Req (innerI φ oneTest) (riemannIntegral φ.hLd φ.hLn φ.hlip φ.hfc) :=
  intU_congr_free _ _ _ _ _ _ _ _ (fun u => Rmul_one (φ.f u))

theorem innerI_one_one : Req (innerI oneTest oneTest) one :=
  Req_trans (intU_congr_free (g := fun _ => one) _ _ _ _ (by decide) (by decide) (const_lip0 one) (fun _ _ _ => Req_refl one)
    (fun _ => Rmul_one one)) (riemannIntegral_const_gen one _ _ _ _)

/-- **`(∫₀¹ φ)² ≤ ∫₀¹ φ²`** (Cauchy–Schwarz against the constant test `1`). -/
theorem unit_cs_ax (φ : L2Test) :
    Rle (Rmul (riemannIntegral φ.hLd φ.hLn φ.hlip φ.hfc) (riemannIntegral φ.hLd φ.hLn φ.hlip φ.hfc)) (innerI φ φ) := by
  have h := innerI_cauchy_schwarz φ oneTest
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_symm (innerI_one_right φ)) (Req_symm (innerI_one_right φ)))) ?_
  refine Rle_trans h (Rle_of_Req ?_)
  exact Req_trans (Rmul_congr (Req_refl _) innerI_one_one) (Rmul_one _)

/-- The unit pullback of a field at a fixed Haar coordinate, as a test. -/
def pullTest (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) : L2Test where
  f := fun u => H.F (affineMap lo w hlo hw u) t
  L := mul H.Lx w
  M := H.M
  hLd := Qmul_den_pos H.hLxd hw
  hLn := Int.mul_nonneg H.hLxn hwn
  hMd := H.hMd
  hMn := H.hMn
  hlip := affine_lip H.hLxd H.hLxn (H.hlipx t) lo w hlo hw hwn
  hfc := fun _ _ h => H.hfcx t (affineMap_congr lo w hlo hw h)
  hbd := fun u => H.hbd (affineMap lo w hlo hw u) t

theorem pullTest_int (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    riemannIntegral (pullTest H lo w hlo hw hwn t).hLd (pullTest H lo w hlo hw hwn t).hLn
      (pullTest H lo w hlo hw hwn t).hlip (pullTest H lo w hlo hw hwn t).hfc = anchorXCore H lo w hlo hw hwn t := rfl

theorem pullTest_inner (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    Req (innerI (pullTest H lo w hlo hw hwn t) (pullTest H lo w hlo hw hwn t)) (anchorXCore (mulF H H) lo w hlo hw hwn t) :=
  intU_congr_free _ _ _ _ _ _ _ _ (fun _ => Req_refl _)

/-- **★ CS FOR THE SCALE INTEGRAL**: `(∫_{[lo,lo+w]} H(·,t))² ≤ w·∫_{[lo,lo+w]} H(·,t)²`. -/
theorem anchorXInt_sq_le (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    Rle (Rmul (anchorXInt H lo w hlo hw hwn t) (anchorXInt H lo w hlo hw hwn t))
        (Rmul (ofQ w hw) (anchorXInt (mulF H H) lo w hlo hw hwn t)) := by
  rw [anchorXInt_eq_core, anchorXInt_eq_core]
  have hcs : Rle (Rmul (anchorXCore H lo w hlo hw hwn t) (anchorXCore H lo w hlo hw hwn t)) (anchorXCore (mulF H H) lo w hlo hw hwn t) := by
    have h := unit_cs_ax (pullTest H lo w hlo hw hwn t)
    rw [pullTest_int] at h
    exact Rle_trans h (Rle_of_Req (pullTest_inner H lo w hlo hw hwn t))
  -- (w·c)·(w·c) ≈ (w·w)·(c·c) ≤ (w·w)·c₂ ≈ w·(w·c₂)
  refine Rle_trans (Rle_of_Req (mul4_swap_ch _ _ _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_ofQ hw hwn)) hcs) ?_
  exact Rle_of_Req (Rmul_assoc _ _ _)

-- --- (5b) The pointwise square estimate `(q·p − τ)² ≤ 2(Q+1)²·(p² + τ²)` for `|q| ≤ Q`. ---

/-- `(u − v)² ≤ 2u² + 2v²`. -/
theorem sq_sub_le_ax (u v : Real) :
    Rle (Rmul (Rsub u v) (Rsub u v)) (Radd (Rmul cTwo (Rmul u u)) (Rmul cTwo (Rmul v v))) := by
  -- 2u² + 2v² − (u − v)² = (u + v)² ≥ 0
  have hid : Req (Rsub (Radd (Rmul cTwo (Rmul u u)) (Rmul cTwo (Rmul v v))) (Rmul (Rsub u v) (Rsub u v)))
      (Rmul (Radd u v) (Radd u v)) := by
    have e1 : Req (Rmul (Rsub u v) (Rsub u v)) (Radd (Radd (Rmul u u) (Rneg (Rmul u v))) (Radd (Rneg (Rmul v u)) (Rmul v v))) :=
      Req_trans (Rmul_distrib_right u (Rneg v) (Rsub u v))
        (Radd_congr (Req_trans (Rmul_distrib u u (Rneg v)) (Radd_congr (Req_refl _) (Rmul_neg_right u v)))
          (Req_trans (Rmul_distrib (Rneg v) u (Rneg v))
            (Radd_congr (Rmul_neg_left v u) (Req_trans (Rmul_neg_left v (Rneg v)) (Req_trans (Rneg_congr (Rmul_neg_right v v)) (Rneg_neg _))))))
    have e2 : Req (Rmul (Radd u v) (Radd u v)) (Radd (Radd (Rmul u u) (Rmul u v)) (Radd (Rmul v u) (Rmul v v))) :=
      Req_trans (Rmul_distrib_right u v (Radd u v)) (Radd_congr (Rmul_distrib u u v) (Rmul_distrib v u v))
    have e3 : Req (Rmul cTwo (Rmul u u)) (Radd (Rmul u u) (Rmul u u)) := cTwo_mul _
    have e4 : Req (Rmul cTwo (Rmul v v)) (Radd (Rmul v v) (Rmul v v)) := cTwo_mul _
    refine Req_trans (Rsub_congr (Radd_congr e3 e4) e1) ?_
    refine Req_trans ?_ (Req_symm e2)
    -- ((uu + uu) + (vv + vv)) − ((uu − uv) + (−vu + vv)) ≈ (uu + uv) + (vu + vv)
    refine Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd _ _) (Radd_congr (Rneg_Radd _ _) (Rneg_Radd _ _)))) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Radd_congr (Req_refl _) (Rneg_neg _)) (Radd_congr (Rneg_neg _) (Req_refl _)))) ?_
    -- ((A + A) + (D + D)) + ((−A + B) + (Cc + −D)) ≈ (A + B) + (Cc + D)   [A = uu, B = uv, Cc = vu, D = vv]
    refine Req_trans (Radd_swap _ _ _ _) ?_
    refine Radd_congr ?_ ?_
    · -- (A + A) + (−A + B) ≈ A + B
      refine Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl _) ?_)
      refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_congr (Radd_neg _) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _)))
    · -- (D + D) + (Cc + −D) ≈ Cc + D
      refine Req_trans (Radd_comm _ _) (Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl _) ?_))
      refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_congr (Req_trans (Radd_comm _ _) (Radd_neg _)) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _)))
  exact Rle_of_Rnonneg_Rsub (Rnonneg_congr (Req_symm hid) (Rnonneg_Rmul_self _))

/-- `q² ≤ Q²` from `|q| ≤ Q`. -/
theorem sq_le_of_abs_le_ax {q Qb : Real} (hQ : Rnonneg Qb) (h : Rle (Rabs q) Qb) : Rle (Rmul q q) (Rmul Qb Qb) := by
  refine Rle_trans (Rle_of_Req (Req_symm (Rabs_of_nonneg (Rnonneg_Rmul_self q)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul q q)) ?_
  exact Rmul_le_Rmul_both (Rnonneg_Rabs _) hQ h h

/-- **The pointwise estimate**: `(q·p − τ)² ≤ (2·(Q+1)²)·(p² + τ²)` when `|q| ≤ Q ≥ 0`. -/
theorem num_sq_le_ax {q p τ Qb : Real} (hQ : Rnonneg Qb) (hq : Rle (Rabs q) Qb) :
    Rle (Rmul (Rsub (Rmul q p) τ) (Rsub (Rmul q p) τ))
        (Rmul (Rmul cTwo (Rmul (Radd Qb one) (Radd Qb one))) (Radd (Rmul p p) (Rmul τ τ))) := by
  have hQ1 : Rnonneg (Radd Qb one) := Rnonneg_Radd hQ Rnonneg_one
  have hQle : Rle Qb (Radd Qb one) := Rle_self_Radd_right Rnonneg_one
  have h1le : Rle one (Radd Qb one) := Rle_self_Radd_left hQ
  have hQQ : Rle (Rmul Qb Qb) (Rmul (Radd Qb one) (Radd Qb one)) := Rmul_le_Rmul_both hQ hQ1 hQle hQle
  have h11 : Rle one (Rmul (Radd Qb one) (Radd Qb one)) :=
    Rle_trans (Rle_of_Req (Req_symm (Rmul_one one))) (Rmul_le_Rmul_both Rnonneg_one hQ1 h1le h1le)
  have hqq : Rle (Rmul q q) (Rmul (Radd Qb one) (Radd Qb one)) := Rle_trans (sq_le_of_abs_le_ax hQ hq) hQQ
  -- (qp)² = (qq)(pp) ≤ Q1²·pp ; τ² = 1·ττ ≤ Q1²·ττ
  have hA : Rle (Rmul (Rmul q p) (Rmul q p)) (Rmul (Rmul (Radd Qb one) (Radd Qb one)) (Rmul p p)) :=
    Rle_trans (Rle_of_Req (mul4_swap_ch q p q p)) (Rmul_le_Rmul_right (Rnonneg_Rmul_self p) hqq)
  have hB : Rle (Rmul τ τ) (Rmul (Rmul (Radd Qb one) (Radd Qb one)) (Rmul τ τ)) :=
    Rle_trans (Rle_of_Req (Req_symm (Rone_mul _))) (Rmul_le_Rmul_right (Rnonneg_Rmul_self τ) h11)
  refine Rle_trans (sq_sub_le_ax (Rmul q p) τ) ?_
  refine Rle_trans (Radd_le_add (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide)) hA)
    (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide)) hB)) ?_
  refine Rle_of_Req ?_
  refine Req_trans (Req_symm (Rmul_distrib cTwo _ _)) ?_
  refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_symm (Rmul_distrib _ _ _))) ?_
  exact Req_symm (Rmul_assoc _ _ _)

-- --- (5c) The Fubini swap for a field: `∫₀¹ (∫_{[lo,lo+w]} G(x, a+w·y) dx) dy = ∫_{[lo,lo+w]} (∫₀¹ G(x, a+w·y) dy) dx`. ---

theorem affineMap_zero_one_ax (u : Real) : Req (affineMap (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q) (by decide) (by decide) u) u := by
  unfold affineMap
  refine Req_trans (Radd_congr (Req_refl _) (Rone_mul u)) ?_
  exact Req_trans (Radd_comm _ _) (Radd_zero u)

/-- The joint Lipschitz estimate of `(x,y) ↦ G(x, a + w·y)`. -/
theorem joint_lip_ax (C : NormCtx) (G : CField) (a a' b b' : Real) :
    Rle (Rabs (Rsub (G.F a (affineMap C.a C.w C.had C.hw b)) (G.F a' (affineMap C.a C.w C.had C.hw b'))))
        (Radd (Rmul (ofQ G.Lx G.hLxd) (Rabs (Rsub a a')))
              (Rmul (ofQ (mul G.Lt C.w) (Qmul_den_pos G.hLtd C.hw)) (Rabs (Rsub b b')))) :=
  Rle_trans (abs_sub_tri _ (G.F a' (affineMap C.a C.w C.had C.hw b)) _)
    (Radd_le_add (G.hlipx _ a a') (affine_lip G.hLtd G.hLtn (G.hlipt a') C.a C.w C.had C.hw C.hwn b b'))

/-- **★ FUBINI FOR A CERTIFIED FIELD** (`bern2D_general_swap_window` on the unit Haar window). -/
theorem fubini_ax (C : NormCtx) (G : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (intT C (anchorXIntF G lo w hlo hw hwn) one) (intX C G lo w hlo hw hwn) := by
  have hswap := bern2D_general_swap_window (fun x y => G.F x (affineMap C.a C.w C.had C.hw y)) G.Lx (mul G.Lt C.w) G.M
    G.hLxd G.hLxn (Qmul_den_pos G.hLtd C.hw) (Qmul_num_nonneg G.hLtn C.hwn) G.hMd G.hMn
    (fun x y y' => affine_lip G.hLtd G.hLtn (G.hlipt x) C.a C.w C.had C.hw C.hwn y y')
    (fun x _ _ h => G.hfct x (affineMap_congr C.a C.w C.had C.hw h))
    (fun x x' y => G.hlipx (affineMap C.a C.w C.had C.hw y) x x')
    (fun _ _ y h => G.hfcx (affineMap C.a C.w C.had C.hw y) h)
    (joint_lip_ax C G) (fun a b => G.hbd a (affineMap C.a C.w C.had C.hw b))
    lo w (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q) hlo hw hwn (by decide) (by decide) (by decide)
  refine Req_symm (Req_trans ?_ (Req_trans hswap ?_))
  · -- intX C G ≈ the swap's left side: pointwise in x, the `[0,1]`-window integral is `intT C G x`.
    unfold intX
    refine intI_congr_free _ _ _ _ _ _ _ _ ?_ lo w hlo hw hwn
    intro x
    show Req (intT C G x) (Rmul (ofQ (⟨1, 1⟩ : Q) (by decide)) (riemannIntegral _ _ _ _))
    refine Req_trans ?_ (Req_symm (Rone_mul _))
    unfold intT
    exact intU_congr_free _ _ _ _ _ _ _ _ (fun u => G.hfct x (affineMap_congr C.a C.w C.had C.hw (Req_symm (affineMap_zero_one_ax u))))
  · -- the swap's right side ≈ intT C (anchorXIntF G) one.
    show Req (Rmul (ofQ (⟨1, 1⟩ : Q) (by decide)) (riemannIntegral _ _ _ _)) (intT C (anchorXIntF G lo w hlo hw hwn) one)
    refine Req_trans (Rone_mul _) ?_
    unfold intT
    refine intU_congr_free _ _ _ _ _ _ _ _ ?_
    intro u
    dsimp only [paramIntegralTest, anchorXIntF, CField.ofT, anchorXInt]
    refine intI_congr_free ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ lo w hlo hw hwn
    exact fun x => G.hfct x (affineMap_congr C.a C.w C.had C.hw (affineMap_zero_one_ax u))

-- --- (5d) Window plumbing: `Qeq`-widths, nonnegativity, monotonicity of the pole window. ---

theorem intI_congr_w_ax {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y))
    (a w w' : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (hw' : 0 < w'.den) (hw'n : 0 ≤ w'.num) (h : Qeq w w') :
    Req (riemannIntegralI hLd hLn hlip hfc a w ha hw hwn) (riemannIntegralI hLd hLn hlip hfc a w' ha hw' hw'n) := by
  unfold riemannIntegralI
  refine Rmul_congr (ofQ_congr hw hw' h) ?_
  exact intU_congr_free _ _ _ _ _ _ _ _
    (fun u => hfc _ _ (Radd_congr (Req_refl _) (Rmul_congr (ofQ_congr hw hw' h) (Req_refl u))))

theorem intT_nonneg_ax (C : NormCtx) (H : CField) (x : Real) (h : ∀ t, Rnonneg (H.F x t)) : Rnonneg (intT C H x) :=
  riemannIntegral_nonneg _ _ _ _ (fun y => h _)

theorem intX_nonneg_ax (C : NormCtx) (H : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num)
    (h : ∀ x t, Rnonneg (H.F x t)) : Rnonneg (intX C H lo w hlo hw hwn) :=
  riemannIntegralI_nonneg _ _ _ _ (fun x => intT_nonneg_ax C H x (h x)) lo w hlo hw hwn

/-- `(B − 1) − 2^{-k} = B − (1 + 2^{-k})` as rationals. -/
theorem poleW_sub_dyQ (C : NormCtx) (k : Nat) : Qeq (Qsub (poleW C) (dyQ k)) (tailGap C k) := by
  simp only [Qeq, poleW, tailGap, Qsub, add, neg, dyQ, canonB]
  push_cast
  generalize hP : (2 : Int) ^ k = p
  generalize hX : ((C.X : Nat) : Int) = X
  ring_uor

/-- `2^{-k} ≤ 1`. -/
theorem dyQ_le_one_ax (k : Nat) : Qle (dyQ k) (⟨1, 1⟩ : Q) := by
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp' : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := by exact_mod_cast hp
  simp only [Qle, dyQ]
  push_cast at hp' ⊢
  generalize hP : (2 : Int) ^ k = p at hp' ⊢
  omega

/-- `1 ≤ B − 1` (`X ≥ 1`). -/
theorem one_le_poleW_ax (C : NormCtx) : Qle (⟨1, 1⟩ : Q) (poleW C) := by
  have hX := C.hX
  simp only [Qle, poleW, Qsub, add, neg, canonB]
  push_cast
  omega

/-- `2^{-k} ≤ B − 1` (`X ≥ 1`). -/
theorem dyQ_le_poleW (C : NormCtx) (k : Nat) : Qle (dyQ k) (poleW C) :=
  Qle_trans Nat.one_pos (dyQ_le_one_ax k) (one_le_poleW_ax C)

/-- **The pole window dominates the tail window** for a field nonnegative on `[1,B]`:
    `∫_{[1+2^{-k},B]} intT H ≤ ∫_{[1,B]} intT H`. -/
theorem intX_tail_le_pole_ax (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (H : CField) (hH : ∀ x t, Rnonneg (H.F x t)) :
    Rle (intX C H (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
        (intX C H (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C)) := by
  unfold intX
  have hsplit := riemannIntegralI_split_at (f := fun x => intT C H x) H.hLxd H.hLxn (intT_lip C H) (intT_fc C H)
    (⟨1, 1⟩ : Q) (poleW C) (dyQ k) Nat.one_pos (poleW_den C) (poleW_num C) (dyQ_den k) (dyQ_num k) (dyQ_le_poleW C k)
    (Qsub_num_nonneg (dyQ_le_poleW C k))
  refine Rle_trans ?_ (Rle_of_Req (Req_symm hsplit))
  refine Rle_trans ?_ (Rle_self_Radd_left (riemannIntegralI_nonneg _ _ _ _ (fun x => intT_nonneg_ax C H x (hH x)) _ _ _ _ _))
  exact Rle_of_Req (Req_symm (intI_congr_w_ax _ _ _ _ _ _ _ _ _ _ _ _ (poleW_sub_dyQ C k)))

-- --- (5e) The energies and the assembly. ---

/-- The square field `A_pole(x̄,t)² + A_tail(x̄,t)²` of the clamped ports. -/
def sqAx (C : NormCtx) (z : Carrier5) : CField := addF (mulF (poleAx C z) (poleAx C z)) (mulF (tailAx C z) (tailAx C z))
/-- The weighted square field `8wr(t)·(A_pole(x̄,t)² + A_tail(x̄,t)²)`. -/
def wsqAx (C : NormCtx) (z : Carrier5) : CField := mulF (tailDens5 C) (sqAx C z)

/-- **The anchor energy** `∫₀¹ 8wr·anchor²` (the compact-tail density as the anchor weight). -/
def anchorEnergyAx (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : Real :=
  gramT C (tailDens5 C) (anchorAx C k hk z) (anchorAx C k hk z)

/-- The bound on `q_k(x̄) = x̄·K_k(x̄)`: `B·M_K`. -/
def qBound (C : NormCtx) (k : Nat) : Q := mul (canonB C) (kerM k)
theorem qBound_den (C : NormCtx) (k : Nat) : 0 < (qBound C k).den := Qmul_den_pos (canonB_den C) (kerM_den k)
theorem qBound_num (C : NormCtx) (k : Nat) : 0 ≤ (qBound C k).num := Qmul_num_nonneg (Int.le_of_lt (canonB_num C)) (kerM_num k)
theorem qk_abs_le (C : NormCtx) (k : Nat) (x : Real) : Rle (Rabs (qk k (xcl C x))) (ofQ (qBound C k) (qBound_den C k)) :=
  abs_mul_bd (canonB_den C) (kerM_den k) (kerM_num k) (xcl_abs_bd C x) (Kx_bd C k x)

/-- `2·(B·M_K + 1)²`. -/
def cOneAx (C : NormCtx) (k : Nat) : Real :=
  Rmul cTwo (Rmul (Radd (ofQ (qBound C k) (qBound_den C k)) one) (Radd (ofQ (qBound C k) (qBound_den C k)) one))
theorem cOneAx_nonneg (C : NormCtx) (k : Nat) : Rnonneg (cOneAx C k) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul (Rnonneg_Radd (Rnonneg_ofQ _ (qBound_num C k)) Rnonneg_one)
    (Rnonneg_Radd (Rnonneg_ofQ _ (qBound_num C k)) Rnonneg_one))

/-- **The explicit constant** `c_k = (1/denLo)²·gap_k·2(B·M_K + 1)²`. -/
def anchorCAx (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real :=
  Rmul (Rmul (ofQ (Qinv (denLo C k)) (Qinv_den_pos (denLo_num_pos C k hk))) (ofQ (Qinv (denLo C k)) (Qinv_den_pos (denLo_num_pos C k hk))))
    (Rmul (ofQ (tailGap C k) (tailGap_den C k)) (cOneAx C k))

theorem numAx_sq_le (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    Rle ((mulF (numAx C k z) (numAx C k z)).F x t) (Rmul (cOneAx C k) ((sqAx C z).F x t)) :=
  num_sq_le_ax (Rnonneg_ofQ _ (qBound_num C k)) (qk_abs_le C k x)

/-- The scale integral of the squared numerator is dominated by `c₁·∫ (A_pole² + A_tail²)`. -/
theorem anchorXInt_numsq_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) :
    Rle (anchorXInt (mulF (numAx C k z) (numAx C k z)) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)
        (Rmul (cOneAx C k) (anchorXInt (sqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)) := by
  unfold anchorXInt
  refine Rle_trans (intI_le_ax _ _ _ _ (smulR (cOneAx C k) (sqAx C z)).hLxd (smulR (cOneAx C k) (sqAx C z)).hLxn
    ((smulR (cOneAx C k) (sqAx C z)).hlipx t) (fun _ _ h => (smulR (cOneAx C k) (sqAx C z)).hfcx t h)
    (fun x => numAx_sq_le C k z x t) _ _ _ _ _) ?_
  exact Rle_of_Req (intI_smul_ax (cOneAx C k) _ _ _ _ _ _ _ _ (fun _ => Req_refl _) _ _ _ _ _)

theorem sqAx_nonneg (C : NormCtx) (z : Carrier5) (x t : Real) : Rnonneg ((sqAx C z).F x t) :=
  Rnonneg_Radd (Rnonneg_Rmul_self _) (Rnonneg_Rmul_self _)

theorem tailDens5_nonneg (C : NormCtx) (x t : Real) : Rnonneg ((tailDens5 C).F x t) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
    (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t)))

theorem tailDens5_const_x (C : NormCtx) (x t : Real) : (tailDens5 C).F x t = (tailDens5 C).F one t := rfl

/-- Abbreviations (definitions, so that every unfolding is explicit). -/
def anchorNum (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) : Real :=
  anchorXInt (numAx C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t
def sqInt (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) : Real :=
  anchorXInt (sqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t
def wsqInt (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) : Real :=
  anchorXInt (wsqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t
def denLoInv (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Real := ofQ (Qinv (denLo C k)) (Qinv_den_pos (denLo_num_pos C k hk))
def gapR (C : NormCtx) (k : Nat) : Real := ofQ (tailGap C k) (tailGap_den C k)

theorem anchorAx_F_num (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (x t : Real) :
    (anchorAx C k hk z).F x t = Rmul (denInvAx C k hk) (anchorNum C k hk z t) := rfl

theorem denLoInv_nonneg (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Rnonneg (denLoInv C k hk) :=
  Rnonneg_ofQ _ (Int.le_of_lt (Qinv_num_pos (denLo_den C k)))
theorem gapR_nonneg (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : Rnonneg (gapR C k) := Rnonneg_ofQ _ (tailGap_num_nonneg C k hk)

/-- The weighted square integral is `d(t)·sqInt` (the density is constant in the scale). -/
theorem wsqInt_eq (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) :
    Req (wsqInt C k hk z t) (Rmul ((tailDens5 C).F one t) (sqInt C k hk z t)) := by
  unfold wsqInt sqInt anchorXInt
  refine intI_smul_ax ((tailDens5 C).F one t) (sqAx C z).hLxd (sqAx C z).hLxn ((sqAx C z).hlipx t) (fun _ _ h => (sqAx C z).hfcx t h)
    (wsqAx C z).hLxd (wsqAx C z).hLxn ((wsqAx C z).hlipx t) (fun _ _ h => (wsqAx C z).hfcx t h) ?_ _ _ _ _ _
  intro x
  show Req (Rmul ((tailDens5 C).F x t) ((sqAx C z).F x t)) (Rmul ((tailDens5 C).F one t) ((sqAx C z).F x t))
  rw [tailDens5_const_x C x t]
  exact Req_refl _

/-- `anchor(t)² ≤ (1/denLo)²·anchorNum(t)²`. -/
theorem anchor_sq_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) :
    Rle (Rmul ((anchorAx C k hk z).F one t) ((anchorAx C k hk z).F one t))
        (Rmul (Rmul (denLoInv C k hk) (denLoInv C k hk)) (Rmul (anchorNum C k hk z t) (anchorNum C k hk z t))) := by
  rw [anchorAx_F_num]
  refine Rle_trans (Rle_of_Req (mul4_swap_ch (denInvAx C k hk) (anchorNum C k hk z t) (denInvAx C k hk) (anchorNum C k hk z t))) ?_
  exact Rmul_le_Rmul_right (Rnonneg_Rmul_self (anchorNum C k hk z t))
    (Rmul_le_Rmul_both (denInvAx_nonneg C k hk) (denLoInv_nonneg C k hk) (denInvAx_le C k hk) (denInvAx_le C k hk))

/-- `anchorNum(t)² ≤ gap·(c₁·sqInt(t))`. -/
theorem anchorNum_sq_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) :
    Rle (Rmul (anchorNum C k hk z t) (anchorNum C k hk z t)) (Rmul (gapR C k) (Rmul (cOneAx C k) (sqInt C k hk z t))) :=
  Rle_trans (anchorXInt_sq_le (numAx C k z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)
    (Rmul_le_Rmul_left (gapR_nonneg C k hk) (anchorXInt_numsq_le C k hk z t))

/-- `d·((Dl·Dl)·(gap·(c₁·S))) ≈ ((Dl·Dl)·(gap·c₁))·(d·S)`. -/
theorem pt_alg_ax (d Dl gap c S : Real) :
    Req (Rmul d (Rmul (Rmul Dl Dl) (Rmul gap (Rmul c S)))) (Rmul (Rmul (Rmul Dl Dl) (Rmul gap c)) (Rmul d S)) := by
  have e1 : Req (Rmul d (Rmul (Rmul Dl Dl) (Rmul gap (Rmul c S)))) (Rmul (Rmul Dl Dl) (Rmul d (Rmul gap (Rmul c S)))) :=
    Req_trans (Req_symm (Rmul_assoc d (Rmul Dl Dl) (Rmul gap (Rmul c S))))
      (Req_trans (Rmul_congr (Rmul_comm d (Rmul Dl Dl)) (Req_refl (Rmul gap (Rmul c S)))) (Rmul_assoc (Rmul Dl Dl) d (Rmul gap (Rmul c S))))
  have e2 : Req (Rmul d (Rmul gap (Rmul c S))) (Rmul gap (Rmul d (Rmul c S))) :=
    Req_trans (Req_symm (Rmul_assoc d gap (Rmul c S)))
      (Req_trans (Rmul_congr (Rmul_comm d gap) (Req_refl (Rmul c S))) (Rmul_assoc gap d (Rmul c S)))
  have e3 : Req (Rmul d (Rmul c S)) (Rmul c (Rmul d S)) :=
    Req_trans (Req_symm (Rmul_assoc d c S)) (Req_trans (Rmul_congr (Rmul_comm d c) (Req_refl S)) (Rmul_assoc c d S))
  have e4 : Req (Rmul gap (Rmul c (Rmul d S))) (Rmul (Rmul gap c) (Rmul d S)) := Req_symm (Rmul_assoc gap c (Rmul d S))
  refine Req_trans e1 ?_
  refine Req_trans (Rmul_congr (Req_refl (Rmul Dl Dl)) e2) ?_
  refine Req_trans (Rmul_congr (Req_refl (Rmul Dl Dl)) (Rmul_congr (Req_refl gap) e3)) ?_
  refine Req_trans (Rmul_congr (Req_refl (Rmul Dl Dl)) e4) ?_
  exact Req_symm (Rmul_assoc (Rmul Dl Dl) (Rmul gap c) (Rmul d S))

/-- **★ THE POINTWISE ENERGY ESTIMATE**: `8wr(t)·anchor(t)² ≤ c_k·∫_{[1+2^{-k},B]} 8wr(t)·(A_pole² + A_tail²)(x̄,t) dx`. -/
theorem anchor_pt_le (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) (t : Real) :
    Rle ((mulF (mulF (tailDens5 C) (anchorAx C k hk z)) (anchorAx C k hk z)).F one t)
        (Rmul (anchorCAx C k hk) (anchorXInt (wsqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) t)) := by
  have hd0 : Rnonneg ((tailDens5 C).F one t) := tailDens5_nonneg C one t
  show Rle (Rmul (Rmul ((tailDens5 C).F one t) ((anchorAx C k hk z).F one t)) ((anchorAx C k hk z).F one t))
           (Rmul (anchorCAx C k hk) (wsqInt C k hk z t))
  refine Rle_trans (Rle_of_Req (Rmul_assoc _ _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left hd0 (Rle_trans (anchor_sq_le C k hk z t)
    (Rmul_le_Rmul_left (Rnonneg_Rmul (denLoInv_nonneg C k hk) (denLoInv_nonneg C k hk)) (anchorNum_sq_le C k hk z t)))) ?_
  refine Rle_trans (Rle_of_Req (pt_alg_ax _ _ _ _ _)) ?_
  exact Rle_of_Req (Rmul_congr (Req_refl _) (Req_symm (wsqInt_eq C k hk z t)))

/-- The weighted-square scale integral as a field of the Haar coordinate. -/
def wsqIntF (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) : CField :=
  anchorXIntF (wsqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)

/-- The integrated form: `anchorEnergy ≤ c_k · ∫₀¹ ∫_{[1+2^{-k},B]} 8wr·(A_pole² + A_tail²)`. -/
theorem anchorEnergy_le_iter (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) :
    Rle (anchorEnergyAx C k hk z) (Rmul (anchorCAx C k hk) (intT C (wsqIntF C k hk z) one)) := by
  unfold anchorEnergyAx gramT
  have hle : Rle (intT C (mulF (mulF (tailDens5 C) (anchorAx C k hk z)) (anchorAx C k hk z)) one)
      (intT C (smulR (anchorCAx C k hk) (wsqIntF C k hk z)) one) := by
    unfold intT
    exact intU_le_ax _ _ _ _ _ _ _ _ (fun y => anchor_pt_le C k hk z _)
  refine Rle_trans hle (Rle_of_Req ?_)
  unfold intT
  exact intU_smul_free (anchorCAx C k hk) _ _ _ _ _ _ _ _ (fun _ => Req_refl _)

/-- `intX` of a sum. -/
theorem intX_add_ax (C : NormCtx) (u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (intX C (addF u v) lo w hlo hw hwn) (Radd (intX C u lo w hlo hw hwn) (intX C v lo w hlo hw hwn)) := by
  have h := intX_sub_pt C u (negF v) (addF u v) lo w hlo hw hwn
    (fun x t => Radd_congr (Req_refl (u.F x t)) (Req_symm (Rneg_neg (v.F x t))))
  refine Req_trans h (Radd_congr (Req_refl _) ?_)
  -- −intX(negF v) ≈ intX v : intX (negF v) ≈ intX zero − intX v ≈ −intX v
  have hz : Req (intX C (negF v) lo w hlo hw hwn) (Rneg (intX C v lo w hlo hw hwn)) := by
    have h0 := intX_sub_pt C (constF zero (Mc := (⟨0, 1⟩ : Q)) Nat.one_pos (by decide) (Rle_of_Req Rabs_zero)) v (negF v) lo w hlo hw hwn
      (fun x t => Req_symm (Req_trans (Radd_comm zero (Rneg (v.F x t))) (Radd_zero (Rneg (v.F x t)))))
    refine Req_trans h0 ?_
    have hz0 : Req (intX C (constF zero (Mc := (⟨0, 1⟩ : Q)) Nat.one_pos (by decide) (Rle_of_Req Rabs_zero)) lo w hlo hw hwn) zero := by
      unfold intX
      refine Req_trans (intI_congr_free (g := fun _ => zero) _ _ _ _ (by decide) (by decide) (const_lip0 zero) (fun _ _ _ => Req_refl zero)
        (fun x => intT_zero_pt C (constF zero (Mc := (⟨0, 1⟩ : Q)) Nat.one_pos (by decide) (Rle_of_Req Rabs_zero)) x (fun _ => Req_refl zero)) lo w hlo hw hwn) ?_
      exact Req_trans (riemannIntegralI_const zero lo w hlo hw hwn) (Rmul_zero _)
    exact Req_trans (Radd_congr hz0 (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))
  exact Req_trans (Rneg_congr hz) (Rneg_neg _)

theorem tailLo_add_gap (C : NormCtx) (k : Nat) : Qeq (add (tailLo k) (tailGap C k)) (canonB C) := by
  simp only [Qeq, tailLo, tailGap, Qsub, add, neg, dyQ, canonB]
  push_cast
  generalize hP : (2 : Int) ^ k = p
  generalize hX : ((C.X : Nat) : Int) = X
  ring_uor

theorem affineMap_ge_lo_ax (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) {s : Real} (hs : Rle zero s) :
    Rle (ofQ lo hlo) (affineMap lo w hlo hw s) :=
  Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_of_Rle_zero hs))

/-- On the tail window the clamp is inert: `x̄ = x` for `x ∈ [1 + 2^{-k}, B]`. -/
theorem xcl_eq_on_tail (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (s : Real) (h0 : Rle zero s) (h1 : Rle s one) :
    Req (xcl C (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s))
        (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) := by
  refine xcl_eq_of_band C ?_ ?_
  · refine Rle_trans ?_ (affineMap_ge_lo_ax (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) h0)
    exact Rle_ofQ_ofQ _ _ (Qle_add_right_nonneg (Int.le_of_lt (dyQ_num k)))
  · refine Rle_trans (Radd_le_add (Rle_refl _) (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (tailGap_num_nonneg C k hk)) h1)
      (Rle_of_Req (Rmul_one _)))) ?_
    exact Rle_of_Req (Req_trans (Radd_ofQ_ofQ (tailLo_den k) (tailGap_den C k)) (ofQ_congr _ _ (tailLo_add_gap C k)))

/-- The tail cut energy of `z` is the tail-window integral of the weighted clamped square. -/
theorem tailG_eq_wsq (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) :
    Req (intX C (mulF (tailDens5 C) (mulF (tailAx C z) (tailAx C z))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
        (tailG C k hk z.tail z.tail) := by
  unfold tailG gramX
  refine intX_congr_win C _ _ _ _ _ _ _ ?_
  intro s h0 h1 y _ _
  show Req (Rmul ((tailDens5 C).F _ _) (Rmul (z.tail.F (xcl C _) _) (z.tail.F (xcl C _) _)))
           (Rmul (Rmul ((tailDens5 C).F _ _) (z.tail.F _ _)) (z.tail.F _ _))
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  exact Rmul_congr (Rmul_congr (Req_refl _) (z.tail.hfcx _ (xcl_eq_on_tail C k hk s h0 h1))) (z.tail.hfcx _ (xcl_eq_on_tail C k hk s h0 h1))

/-- `8wr ≤ 8(1 + 1/x)wr` pointwise. -/
theorem tailDens5_le_poleDens5 (C : NormCtx) (x t : Real) : Rle ((tailDens5 C).F x t) ((poleDens5 C).F x t) := by
  show Rle (Rmul (ofQ q4 Nat.one_pos) (Rmul (ofQ q2 Nat.one_pos) (Rmul (ofQ C.w C.hw) (rEv C t))))
           (Rmul (ofQ q4 Nat.one_pos) (Rmul (ofQ q2 Nat.one_pos) (Rmul (Radd one (rOne x)) (Rmul (ofQ C.w C.hw) (rEv C t)))))
  refine Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide)) (Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (by decide)) ?_)
  refine Rle_trans (Rle_of_Req (Req_symm (Rone_mul _))) ?_
  exact Rmul_le_Rmul_right (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t))
    (Rle_self_Radd_right (Rnonneg_clampedInv _ _ _ x))

theorem poleDens5_nonneg (C : NormCtx) (x t : Real) : Rnonneg ((poleDens5 C).F x t) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
    (Rnonneg_Rmul (Rnonneg_Radd Rnonneg_one (Rnonneg_clampedInv _ _ _ x)) (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t))))

/-- The pole part of the weighted square is dominated by the pole cut energy of `z`. -/
theorem wsq_pole_le_poleG (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) :
    Rle (intX C (mulF (tailDens5 C) (mulF (poleAx C z) (poleAx C z))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
        (poleG C z.pole z.pole) := by
  unfold poleG gramX
  refine Rle_trans ?_ (intX_tail_le_pole_ax C k hk (mulF (mulF (poleDens5 C) z.pole) z.pole)
    (fun x t => Rnonneg_congr (Req_symm (Rmul_assoc _ _ _)) (Rnonneg_Rmul (poleDens5_nonneg C x t) (Rnonneg_Rmul_self _))))
  unfold intX
  refine intI_le_unit_ax _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  intro s h0 h1
  unfold intT
  refine intU_le_ax _ _ _ _ _ _ _ _ ?_
  intro y
  show Rle (Rmul ((tailDens5 C).F _ _) (Rmul (z.pole.F (xcl C _) _) (z.pole.F (xcl C _) _)))
           (Rmul (Rmul ((poleDens5 C).F _ _) (z.pole.F _ _)) (z.pole.F _ _))
  refine Rle_trans ?_ (Rle_of_Req (Req_symm (Rmul_assoc _ _ _)))
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_refl _) (Rmul_congr (z.pole.hfcx _ (xcl_eq_on_tail C k hk s h0 h1)) (z.pole.hfcx _ (xcl_eq_on_tail C k hk s h0 h1))))) ?_
  exact Rmul_le_Rmul_right (Rnonneg_Rmul_self _) (tailDens5_le_poleDens5 C _ _)

/-- **★ THE SOURCE-METRIC BOUND OF THE ANCHOR EXTRACTOR**, for EVERY carrier element `z`:
    `∫₀¹ 8wr·anchor² ≤ c_k·(poleCutEnergy(z) + tailCutEnergy(z))`, `c_k = (4B/gap_k)²·gap_k·2(B·M_K+1)²` explicit. -/
theorem anchorAx_bound (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z : Carrier5) :
    Rle (anchorEnergyAx C k hk z) (Rmul (anchorCAx C k hk) (Radd (poleG C z.pole z.pole) (tailG C k hk z.tail z.tail))) := by
  refine Rle_trans (anchorEnergy_le_iter C k hk z) ?_
  have hc0 : Rnonneg (anchorCAx C k hk) :=
    Rnonneg_Rmul (Rnonneg_Rmul_self _) (Rnonneg_Rmul (Rnonneg_ofQ _ (tailGap_num_nonneg C k hk)) (cOneAx_nonneg C k))
  refine Rmul_le_Rmul_left hc0 ?_
  refine Rle_trans (Rle_of_Req (fubini_ax C (wsqAx C z) _ _ _ _ _)) ?_
  -- wsq = d·(p² + τ²) ≈ d·p² + d·τ² pointwise; integrate
  have hsplit : Req (intX C (wsqAx C z) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
      (Radd (intX C (mulF (tailDens5 C) (mulF (poleAx C z) (poleAx C z))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))
            (intX C (mulF (tailDens5 C) (mulF (tailAx C z) (tailAx C z))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk))) := by
    refine Req_trans (intX_congr_pt C _ (addF (mulF (tailDens5 C) (mulF (poleAx C z) (poleAx C z))) (mulF (tailDens5 C) (mulF (tailAx C z) (tailAx C z))))
      _ _ _ _ _ (fun x t => Rmul_distrib _ _ _)) ?_
    exact intX_add_ax C _ _ _ _ _ _ _
  refine Rle_trans (Rle_of_Req hsplit) ?_
  exact Radd_le_add (wsq_pole_le_poleG C k hk z) (Rle_of_Req (tailG_eq_wsq C k hk z))

end UOR.Bridge.F1Square.Square
