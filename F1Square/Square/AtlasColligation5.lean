/-
F1 square — **THE SIGNED FIVE-CHANNEL ATLAS COLLIGATION** (`AtlasColligation5.lean`, target-free).

`atlasMatrix C k : Carrier5 → Carrier5` maps a CUT carrier element `z` (five certified fields) to a CYCLE
carrier element, using only cut data:

 * the LOCAL recovery `U_x = 4((K + r)A_pole + A_tail)/P_k`, `V = 4(q_kA_pole − A_tail)/P_k` (`AtlasCutRecovery`),
   here as certified fields with the Lipschitz reciprocal `1/P_k = clampedInv_{1/B}(P_k(x̄))` (inert since `P_k ≥ 1/B`);
 * the far anchor `V = 2·A_far`;
 * THE NONLOCAL ORBIT READING of the prime channel: for the place `n = m+1 ≤ X` the value `U_n(t)` is the
   NORMALIZED HAAR AVERAGE over the scale window `x ∈ [n, B]` (inside `J_{k,n,t}`: `x ≥ 1+2^{-k}`, `x ≤ B`,
   `x·t/n ≥ a`) of the cut-only reading `invSq(n)·invSq(x)·x·U_x^{rec}(x, x·t/n)` against `dx/max(x,1)`:

       `readHaar_m(z)(t) = (∫_{[n,B]} r(x)·invSq(n)·invSq(x)·x·U^{rec}_x(z)(x, x·t/n) dx) / ∫_{[n,B]} r(x) dx`,

   a genuine certified integral in the scale (`xInt`), no point sampling, no refinement parameter;
 * the two-port action: cycle coordinates `B = (u + v)/4` of every channel fiber from the recovered `(u, v)`.

THE LOAD-BEARING FACTS PROVED HERE:
 * `readHaar_source` — on every analysis `A_k f` the orbit reading IS `U_n(f,t)` for `t ∈ [a, a+w]` (the real-scale
   orbit law `Uc_orbit` and the weight law `invSq_sq_mul_self`, integrated: the integrand is `r(x̄)·U_n(t)` at
   every scale of the window, so the normalized average is exactly `U_n(t)`);
 * `atlasMatrix_reproduces` — `atlasMatrix C k (A_k f)` agrees with the cycle analysis `B_k f` on the measured
   supports of all five channels, EXACTLY (error identically zero; no `N`, no `ε`);
 * `energy5_matrix_eq` — hence its energy is the cycle energy of `f`;
 * `atlasMatrix_range_bound_iff` — on the range, `‖atlasMatrix z‖² ≤ ‖z‖²` ⟺ `cutEnergy − cycleEnergy ≥ 0`;
 * `colligation_range_bound_imp` — for EVERY map `T : Carrier5 → Carrier5` reproducing the cycle analysis on the
   supports, the range bound `‖T(A_k f)‖² ≤ ‖A_k f‖²` implies `cutEnergy − cycleEnergy ≥ 0`.

SCOPE OF THE READING WINDOW.  The window `[n, B]` is contained in `J_{k,n,t} ∩ {s ≥ a}` for every `t ∈ [a, a+w]`
(`n ≥ 2 > 1 + 2^{-k}`, `x ≥ n ⟹ s = x·t/n ≥ t ≥ a`), which is all the ORBIT LAW needs, so the reading is exact on
every analysis.  It is NOT contained in the full `J_{k,n,t}`: for `x > n(a+w)/t` the mate `s` lies above `a + w`,
where the pole/tail cut fields of an ARBITRARY carrier element carry no `inner5`-energy.  Hence `readHaar` is an
exact reproduction kernel, not an energy-bounded one on the whole carrier — no such bound is stated here.

NOT PROVED, NOT CLAIMED: any bound `‖atlasMatrix z‖ ≤ (1+ε)‖z‖`.  By `atlasMatrix_range_bound_iff` together with
`atlasDefectGram_split`/`source5_split_fixed` the bound on the range IS the sign of the defect Gram at level `k`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasCarrier5
import F1Square.Square.AtlasCutRecovery

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (0) Window helpers and one more plumbing lemma.
-- ===========================================================================

theorem affineMap_ge_lo_c5 (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (s : Real) (hs : Rle zero s) :
    Rle (ofQ lo hlo) (affineMap lo w hlo hw s) :=
  Rle_trans (Rle_self_Radd_left (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_of_Rle_zero hs))) (Rle_of_Req (Radd_comm _ _))

theorem affineMap_le_hi_c5 (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (s : Real) (hs : Rle s one) :
    Rle (affineMap lo w hlo hw s) (ofQ (add lo w) (add_den_pos hlo hw)) :=
  Rle_trans (Radd_le_add (Rle_refl _) (Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hw hwn) hs) (Rle_of_Req (Rmul_one _))))
    (Rle_of_Req (Radd_ofQ_ofQ hlo hw))

/-- Window version: `h ≈ c·g` pointwise ⟹ `∫_I h ≈ c·∫_I g`. -/
theorem intI_smul_free {g h : Real → Real} {Lg Lh : Q} (c : Real) (hgd : 0 < Lg.den) (hgn : 0 ≤ Lg.num)
    (hglip : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y))))
    (hgfc : ∀ x y, Req x y → Req (g x) (g y))
    (hhd : 0 < Lh.den) (hhn : 0 ≤ Lh.num)
    (hhlip : ∀ x y, Rle (Rabs (Rsub (h x) (h y))) (Rmul (ofQ Lh hhd) (Rabs (Rsub x y))))
    (hhfc : ∀ x y, Req x y → Req (h x) (h y)) (hh : ∀ y, Req (h y) (Rmul c (g y)))
    (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) :
    Req (riemannIntegralI hhd hhn hhlip hhfc lo w hlo hw hwn) (Rmul c (riemannIntegralI hgd hgn hglip hgfc lo w hlo hw hwn)) := by
  unfold riemannIntegralI
  refine Req_trans (Rmul_congr (Req_refl _) (intU_smul_free c (Qmul_den_pos hgd hw) (Int.mul_nonneg hgn hwn)
    (affine_lip hgd hgn hglip lo w hlo hw hwn) (fun _ _ e => hgfc _ _ (affineMap_congr lo w hlo hw e)) _ _ _ _ (fun _ => hh _))) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

-- ===========================================================================
-- (1) The Lipschitz reciprocal of `P_k` and the recovery fields.
-- ===========================================================================

/-- `one` as a certified constant field. -/
def oneConstF : CField :=
  constF one Nat.one_pos (by decide) (abs_ofQ_le (q := (⟨1, 1⟩ : Q)) Nat.one_pos (by decide) : Rle (Rabs one) (ofQ (⟨1, 1⟩ : Q) Nat.one_pos))

/-- `x ↦ 1/max(x̄, 1)`. -/
def rOneClF (C : NormCtx) : CField := compX rOneF (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)

/-- `(x,t) ↦ P_k(x̄) = K_k(x̄)·(x̄ + 1) + 1/max(x̄,1)`. -/
def PkClF (C : NormCtx) (k : Nat) : CField := addF (mulF (KxF C k) (addF (xclF C) oneConstF)) (rOneClF C)
theorem PkClF_F (C : NormCtx) (k : Nat) (x t : Real) : (PkClF C k).F x t = Pk k (xcl C x) := rfl

/-- The certified reciprocal floor `1/B`. -/
def invBQ (C : NormCtx) : Q := Qinv (canonB C)
theorem invBQ_num (C : NormCtx) : 0 < (invBQ C).num := Qinv_num_pos (canonB_den C)
theorem invBQ_den (C : NormCtx) : 0 < (invBQ C).den := Qinv_den_pos (canonB_num C)

/-- `x ↦ clampedInv_{1/B}(P_k(x̄))` — the Lipschitz reciprocal of `P_k` on the band. -/
def PkInvF (C : NormCtx) (k : Nat) : CField :=
  compX (ofX (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).f
      (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hLd (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hLn
      (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hMd (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hMn
      (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hlip (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hbd
      (recipTest (invBQ C) (invBQ_num C) (invBQ_den C)).hfc)
    (fun x => Pk k (xcl C x)) (PkClF C k).hLxd (PkClF C k).hLxn ((PkClF C k).hlipx one) (fun _ _ h => (PkClF C k).hfcx one h)

theorem xcl_zero_le (C : NormCtx) (x : Real) : Rle zero (xcl C x) :=
  Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) (xcl_ge_one C x)

/-- On the band the Lipschitz reciprocal IS the certified reciprocal `PkInv`. -/
theorem PkInvF_F (C : NormCtx) (k : Nat) (x t : Real) :
    Req ((PkInvF C k).F x t) (PkInv C k (xcl C x) (xcl_zero_le C x) (xcl_le_B C x)) :=
  clampedInv_eq_of_ge (han := invBQ_num C) (had := invBQ_den C) (kx := 3 * (Qinv (canonB C)).den)
    (Rlt_Qbound_of_Rle_ofQ (Qinv_num_pos (canonB_den C)) (Qinv_den_pos (canonB_num C)) (Pk_ge_invB C k (xcl_zero_le C x) (xcl_le_B C x)))
    (Pk_ge_invB C k (xcl_zero_le C x) (xcl_le_B C x))

/-- `(x,t) ↦ q_k(x̄) = x̄·K_k(x̄)`. -/
def qkClF (C : NormCtx) (k : Nat) : CField := mulF (xclF C) (KxF C k)

/-- A carrier field read at the clamped scale `x̄`. -/
def atCl (C : NormCtx) (u : CField) : CField := compX u (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)
theorem atCl_F (C : NormCtx) (u : CField) (x t : Real) : (atCl C u).F x t = u.F (xcl C x) t := rfl

/-- **`U^{rec}`: the recovered `U_x` field** `4·((K_k(x̄) + r(x̄))·A_pole(x̄,t) + A_tail(x̄,t))·(1/P_k(x̄))`. -/
def recUF (C : NormCtx) (k : Nat) (z : Carrier5) : CField :=
  mulF (smulQF q4 Nat.one_pos (by decide) (addF (mulF (addF (KxF C k) (rOneClF C)) (atCl C z.pole)) (atCl C z.tail))) (PkInvF C k)

/-- **`V^{rec}`: the recovered `V` field** `4·(q_k(x̄)·A_pole(x̄,t) − A_tail(x̄,t))·(1/P_k(x̄))`. -/
def recVF (C : NormCtx) (k : Nat) (z : Carrier5) : CField :=
  mulF (smulQF q4 Nat.one_pos (by decide) (subF (mulF (qkClF C k) (atCl C z.pole)) (atCl C z.tail))) (PkInvF C k)

/-- **The far anchor** `V = 2·A_far`. -/
def recVFarF (z : Carrier5) : CField := smulQF q2 Nat.one_pos (by decide) z.far

theorem recUF_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    Req ((recUF C k z).F x t)
        (recoverUFromCut C k (xcl C x) (xcl_zero_le C x) (xcl_le_B C x) (z.pole.F (xcl C x) t) (z.tail.F (xcl C x) t)) :=
  Rmul_congr (Req_refl _) (PkInvF_F C k x t)

theorem recVF_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    Req ((recVF C k z).F x t)
        (recoverVFromCut C k (xcl C x) (xcl_zero_le C x) (xcl_le_B C x) (z.pole.F (xcl C x) t) (z.tail.F (xcl C x) t)) :=
  Rmul_congr (Req_refl _) (PkInvF_F C k x t)

theorem recVFarF_F (z : Carrier5) (x t : Real) : (recVFarF z).F x t = recoverVFromFar (z.far.F x t) := rfl

-- --- source identities on the analyses ---

theorem xcl_idem (C : NormCtx) (x : Real) : Req (xcl C (xcl C x)) (xcl C x) :=
  xcl_eq_of_band C (xcl_ge_one C x) (xcl_le_B C x)

theorem Wc_congr_x (C : NormCtx) {x x' : Real} (h : Req x x') (f : L2Test) (t : Real) : Req (Wc C x f t) (Wc C x' f t) :=
  Rmul_congr (clampedInv_congr _ _ _ h) (Req_refl _)

theorem Zc_congr_x (C : NormCtx) (k : Nat) {x x' : Real} (h : Req x x') (f : L2Test) (t : Real) :
    Req (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x' f t) :=
  Rmul_congr (Rmul_congr h ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hfc _ _ h)) (Dc_congr_x C h f t)

theorem aCoefGa_congr {u u' v v' : Real} (hu : Req u u') (hv : Req v v') : Req (aCoefGa one u v) (aCoefGa one u' v') :=
  Rmul_congr (Req_refl _) (Rsub_congr (Rmul_congr (Req_refl _) hu) hv)
theorem bCoefGa_congr {u u' v v' : Real} (hu : Req u u') (hv : Req v v') : Req (bCoefGa one u v) (bCoefGa one u' v') :=
  Rmul_congr (Req_refl _) (Radd_congr (Rmul_congr (Req_refl _) hu) hv)

/-- The tail cut coordinate of the analysis, read at `x̄`, is the tail cut coordinate at `x̄` (clamp idempotent). -/
theorem cut_tail_at_cl (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((cutAnalysis5 C k f).tail.F (xcl C x) t)
        (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t) (Wc C (xcl C x) f t)) := by
  rw [cutAnalysis5_tail]
  exact aCoefGa_congr (Zc_congr_x C k (xcl_idem C x) f t) (Wc_congr_x C (xcl_idem C x) f t)

/-- **★ `U^{rec}(A_k f) = U_{x̄}(f)`** at every `(x,t)`. -/
theorem recUF_source (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((recUF C k (cutAnalysis5 C k f)).F x t) (Uc C (xcl C x) f t) := by
  refine Req_trans (recUF_F C k _ x t) ?_
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Radd_congr (Req_refl _) (cut_tail_at_cl C k f x t))) (Req_refl _)) ?_
  exact recoverUFromCut_source C k (xcl C x) (xcl_ge_one C x) (xcl_le_B C x) f t

/-- **★ `V^{rec}(A_k f) = V(f)`** at every `(x,t)`. -/
theorem recVF_source (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((recVF C k (cutAnalysis5 C k f)).F x t) (Vc C f t) := by
  refine Req_trans (recVF_F C k _ x t) ?_
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Rsub_congr (Req_refl _) (cut_tail_at_cl C k f x t))) (Req_refl _)) ?_
  exact recoverVFromCut_source C k (xcl C x) (xcl_ge_one C x) (xcl_le_B C x) f t

/-- **`2·A_far(A_k f) = V(f)`**. -/
theorem recVFarF_source (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    Req ((recVFarF (cutAnalysis5 C k f)).F x t) (Vc C f t) :=
  recoverVFromFar_source C f t

-- ===========================================================================
-- (2) The scale integral of a field at fixed Haar coordinate, with its Haar certificates.
-- ===========================================================================

/-- `xInt z lo w t = ∫_{[lo,lo+w]} z(x,t) dx`. -/
def xInt (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) : Real :=
  riemannIntegralI (f := fun x => z.F x t) z.hLxd z.hLxn (z.hlipx t) (fun _ _ h => z.hfcx t h) lo w hlo hw hwn

theorem xInt_lip (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t',
    Rle (Rabs (Rsub (xInt z lo w hlo hw hwn t) (xInt z lo w hlo hw hwn t')))
        (Rmul (ofQ (mul w z.Lt) (Qmul_den_pos hw z.hLtd)) (Rabs (Rsub t t'))) := by
  intro t t'
  unfold xInt riemannIntegralI
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib _ _ _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ z.hLtd z.hLtn) (Rnonneg_Rabs _))
    (Rle_of_Req (Rabs_ofQ_nonneg hw hwn))
    (param_integral_lip (F := fun t y => z.F (affineMap lo w hlo hw y) t) (L := fun _ => mul z.Lx w)
      (fun _ => Qmul_den_pos z.hLxd hw) (fun _ => Int.mul_nonneg z.hLxn hwn)
      (fun t => affine_lip z.hLxd z.hLxn (z.hlipx t) lo w hlo hw hwn)
      (fun t _ _ h => z.hfcx t (affineMap_congr lo w hlo hw h))
      z.hLtd (fun y _ _ t t' => z.hlipt (affineMap lo w hlo hw y) t t') t t')) ?_
  exact Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ hw z.hLtd) (Req_refl _)))

theorem xInt_bd (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (t : Real) :
    Rle (Rabs (xInt z lo w hlo hw hwn t)) (ofQ (mul w z.M) (Qmul_den_pos hw z.hMd)) := by
  unfold xInt riemannIntegralI
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ z.hMd z.hMn) (Rle_of_Req (Rabs_ofQ_nonneg hw hwn))
    (riemannIntegral_abs_le_unit_real _ _ _ _ _ (fun y _ _ => z.hbd _ t))) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ hw z.hMd)

theorem xInt_fc (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : ∀ t t', Req t t' →
    Req (xInt z lo w hlo hw hwn t) (xInt z lo w hlo hw hwn t') :=
  fun t t' h => riemannIntegralI_congr _ _ _ _ _ _ lo w hlo hw hwn (fun x => z.hfct x h)

/-- `t ↦ xInt z lo w t` as a certified field (constant in the scale). -/
def xIntF (z : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : CField :=
  ofT (xInt z lo w hlo hw hwn) (Qmul_den_pos hw z.hLtd) (Qmul_num_nonneg hwn z.hLtn) (Qmul_den_pos hw z.hMd) (Qmul_num_nonneg hwn z.hMn)
    (xInt_lip z lo w hlo hw hwn) (xInt_bd z lo w hlo hw hwn) (xInt_fc z lo w hlo hw hwn)

/-- If `u(x,t) ≈ c·v(x,t')` on the window, then `xInt u t ≈ c·xInt v t'`. -/
theorem xInt_congr_smul (u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (c t t' : Real)
    (h : ∀ s, Rle zero s → Rle s one → Req (u.F (affineMap lo w hlo hw s) t) (Rmul c (v.F (affineMap lo w hlo hw s) t'))) :
    Req (xInt u lo w hlo hw hwn t) (Rmul c (xInt v lo w hlo hw hwn t')) := by
  unfold xInt
  refine Req_trans (intI_congr_unit_free u.hLxd u.hLxn (u.hlipx t) (fun _ _ e => u.hfcx t e)
    (Qmul_den_pos Nat.one_pos v.hLxd) (Qmul_num_nonneg (xBQ_num_nonneg c) v.hLxn)
    (lip_smul_fl c v.hLxd v.hLxn (v.hlipx t')) (fc_smul_fl c (fun _ _ e => v.hfcx t' e)) lo w hlo hw hwn h) ?_
  exact intI_smul_free c v.hLxd v.hLxn (v.hlipx t') (fun _ _ e => v.hfcx t' e) _ _ _ _ (fun _ => Req_refl _) lo w hlo hw hwn

-- ===========================================================================
-- (3) The Haar window `[n, B]` of the place `n = m+1`, its mass, and the orbit reading.
-- ===========================================================================

/-- The place as a rational `n = m + 1`. -/
def upQ (m : Nat) : Q := (⟨((m + 1 : Nat) : Int), 1⟩ : Q)
/-- The window width `X − m` (so `n + (X − m) = B` for `m ≤ X`). -/
def wnQ (C : NormCtx) (m : Nat) : Q := (⟨((C.X - m : Nat) : Int), 1⟩ : Q)
theorem wnQ_num (C : NormCtx) (m : Nat) : 0 ≤ (wnQ C m).num := Int.ofNat_nonneg _
theorem wnQ_num_pos (C : NormCtx) (m : Nat) (hm : m < C.X) : 0 < (wnQ C m).num := by
  show (0 : Int) < ((C.X - m : Nat) : Int)
  have : 0 < C.X - m := Nat.sub_pos_of_lt hm
  omega

/-- `n + (X − m) ≤ B` for `m ≤ X` (equality). -/
theorem upQ_add_wnQ_le_B (C : NormCtx) (m : Nat) (hm : m ≤ C.X) : Qle (add (upQ m) (wnQ C m)) (canonB C) := by
  show ((((m + 1 : Nat) : Int)) * ((1 : Nat) : Int) + (((C.X - m : Nat) : Int)) * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
      ≤ ((C.X + 1 : Nat) : Int) * (((1 : Nat) * (1 : Nat) : Nat) : Int)
  have h1 : ((C.X - m : Nat) : Int) = (C.X : Int) - (m : Int) := by omega
  push_cast
  rw [h1]; omega

/-- The Haar mass `∫_{[n, n + (X−m)]} 1/max(x̄,1) dx`. -/
def hMass (C : NormCtx) (m : Nat) : Real :=
  xInt (rOneClF C) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m) one

/-- `1/max(x̄,1) ≥ 1/B` everywhere (`x̄ ≤ B`). -/
theorem rOneCl_ge_invB (C : NormCtx) (x : Real) : Rle (ofQ (invBQ C) (invBQ_den C)) (rOne (xcl C x)) :=
  ofQ_inv_le_clampedInv (by decide) (by decide) (canonB_den C) (canonB_num C) (xcl_le_B C x) (canonB_one C)

/-- The mass floor `(X−m)/B`. -/
def massFloor (C : NormCtx) (m : Nat) : Q := mul (wnQ C m) (invBQ C)
theorem massFloor_den (C : NormCtx) (m : Nat) : 0 < (massFloor C m).den := Qmul_den_pos Nat.one_pos (invBQ_den C)
theorem massFloor_num_pos (C : NormCtx) (m : Nat) (hm : m < C.X) : 0 < (massFloor C m).num :=
  Int.mul_pos (wnQ_num_pos C m hm) (invBQ_num C)

/-- **The Haar mass is at least `(X−m)/B`**. -/
theorem hMass_ge (C : NormCtx) (m : Nat) : Rle (ofQ (massFloor C m) (massFloor_den C m)) (hMass C m) := by
  unfold hMass xInt
  have hlipc := lip_weaken_fl (f := fun _ : Real => ofQ (invBQ C) (invBQ_den C)) (by decide) (rOneClF C).hLxd
    (Qle_add_left_nonneg (rOneClF C).hLxn) (const_lip0 _)
  have hle : Rle (riemannIntegralI (rOneClF C).hLxd (rOneClF C).hLxn hlipc (fun _ _ _ => Req_refl _)
      (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m))
      (riemannIntegralI (rOneClF C).hLxd (rOneClF C).hLxn ((rOneClF C).hlipx one) (fun _ _ h => (rOneClF C).hfcx one h)
      (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m)) :=
    riemannIntegralI_le _ _ _ _ _ _ (fun x => rOneCl_ge_invB C x) _ _ _ _ _
  refine Rle_trans ?_ hle
  refine Rle_of_Req (Req_symm ?_)
  refine Req_trans (riemannIntegralI_certif_irrel _ _ hlipc (fun _ _ _ => Req_refl _) (by decide) (by decide) (const_lip0 _)
    (fun _ _ _ => Req_refl _) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m)) ?_
  refine Req_trans (riemannIntegralI_const _ (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m)) ?_
  exact Rmul_ofQ_ofQ Nat.one_pos (invBQ_den C)

/-- **The normalized Haar mass** `1/∫_{[n,B]} r` at the explicit witness `3·(massFloor).den` (`m < X`). -/
def hMassInv (C : NormCtx) (m : Nat) (hm : m < C.X) : Real :=
  Rinv (hMass C m) (3 * (massFloor C m).den)
    (Rlt_Qbound_of_Rle_ofQ (massFloor_num_pos C m hm) (massFloor_den C m) (hMass_ge C m))

theorem hMassInv_mul (C : NormCtx) (m : Nat) (hm : m < C.X) : Req (Rmul (hMass C m) (hMassInv C m hm)) one := Rmul_Rinv_self _

/-- The Haar band `t̄ = band_{[a, a+w]}(t)` (inert on the window). -/
def tBand (C : NormCtx) (t : Real) : Real := qBandQ C.a (add C.a C.w) C.had (add_den_pos C.had C.hw) t
theorem tBand_ge_a (C : NormCtx) (t : Real) : Rle (ofQ C.a C.had) (tBand C t) := fun n =>
  Qle_trans ((tBand C t).den_pos n) (qBandQ_ge C.a (add C.a C.w) C.had (add_den_pos C.had C.hw) (Qle_add_right_nonneg C.hwn) t n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))
theorem tBand_le (C : NormCtx) (t : Real) : Rle (tBand C t) (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) := fun n =>
  Qle_trans (add_den_pos C.had C.hw) (qBandQ_le C.a (add C.a C.w) C.had (add_den_pos C.had C.hw) t n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))
theorem tBand_eq_of_win (C : NormCtx) {t : Real} (h1 : Rle (ofQ C.a C.had) t) (h2 : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req (tBand C t) t := qBandQ_eq_of_band h1 h2
theorem tBand_abs_bd (C : NormCtx) (t : Real) : Rle (Rabs (tBand C t)) (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) :=
  Rabs_le_of_nonneg_le (add_den_pos C.had C.hw) (Qadd_num_nonneg_loc (Int.le_of_lt C.han) C.hwn)
    (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ C.had (Int.le_of_lt C.han))) (tBand_ge_a C t))) (tBand_le C t)

/-- `t ↦ t̄`. -/
def tBandF (C : NormCtx) : CField :=
  ofT (tBand C) (L := (⟨1, 1⟩ : Q)) (M := add C.a C.w) Nat.one_pos (by decide) (add_den_pos C.had C.hw)
    (Qadd_num_nonneg_loc (Int.le_of_lt C.han) C.hwn)
    (fun t t' => Rle_trans (qBandQ_lipschitz _ _ _ _ t t') (Rle_of_Req (Req_symm (Rone_mul _))))
    (tBand_abs_bd C) (fun _ _ h => qBandQ_congr _ _ _ _ h)

/-- `1/n` as a rational constant. -/
def invNQ (m : Nat) : Q := (⟨1, m + 1⟩ : Q)
theorem invNQ_num (m : Nat) : 0 ≤ (invNQ m).num := by show (0 : Int) ≤ 1; decide
def invNF (m : Nat) : CField :=
  constF (ofQ (invNQ m) (Nat.succ_pos m)) (Nat.succ_pos m) (invNQ_num m) (abs_ofQ_le (Nat.succ_pos m) (invNQ_num m))

/-- **The Archimedean mate** `(x,t) ↦ x̄·(t̄/n)`. -/
def mateF (C : NormCtx) (m : Nat) : CField := mulF (xclF C) (mulF (tBandF C) (invNF m))
theorem mateF_F (C : NormCtx) (m : Nat) (x t : Real) :
    (mateF C m).F x t = Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))) := rfl

/-- Composition of a field with two fields. -/
def comp2F (u α β : CField) : CField :=
  comp2 u α.F β.F α.hLxd α.hLxn α.hLtd α.hLtn β.hLxd β.hLxn β.hLtd β.hLtn α.hlipx α.hlipt β.hlipx β.hlipt
    (fun hx ht => cfield_fc α hx ht) (fun hx ht => cfield_fc β hx ht)
theorem comp2F_F (u α β : CField) (x t : Real) : (comp2F u α β).F x t = u.F (α.F x t) (β.F x t) := rfl

/-- `x ↦ x̄^{-1/2}`. -/
def invSqClF (C : NormCtx) : CField :=
  compX (ofX (invSq C) (invSqL_den C) (invSqL_num C) (Qinv_den_pos (canonC_num C)) (Int.le_of_lt (Qinv_num_pos (canonC_den C)))
      (invSq_lip C) (invSq_bd C) (fun _ _ h => (invSqrtTwoTest (canonC C) (canonB C) (canonC_num C) (canonC_den C) (canonB_den C)
        (canonB_one C) (canonC_le_B C) (canonC_le_one C) (C.X + 1) (Nat.succ_pos C.X) (canonB_le_N C)).hfc _ _ h))
    (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)

/-- `n^{-1/2}` as a constant field. -/
def invSqNF (C : NormCtx) (m : Nat) : CField :=
  constF (invSq C (upR m)) (Qinv_den_pos (canonC_num C)) (Int.le_of_lt (Qinv_num_pos (canonC_den C))) (invSq_bd C (upR m))

/-- **THE CUT-ONLY READING INTEGRAND** `(x,t) ↦ r(x̄)·invSq(n)·invSq(x̄)·x̄·U^{rec}(z)(x̄, x̄·t̄/n)`. -/
def readF (C : NormCtx) (k m : Nat) (z : Carrier5) : CField :=
  mulF (mulF (mulF (rOneClF C) (invSqNF C m)) (mulF (invSqClF C) (xclF C))) (comp2F (recUF C k z) (xclF C) (mateF C m))

theorem readF_F (C : NormCtx) (k m : Nat) (z : Carrier5) (x t : Real) :
    (readF C k m z).F x t =
      Rmul (Rmul (Rmul (rOne (xcl C x)) (invSq C (upR m))) (Rmul (invSq C (xcl C x)) (xcl C x)))
           ((recUF C k z).F (xcl C x) (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))))) := rfl

/-- **★ THE ORBIT READING** `readHaar_m(z)(t) = (∫_{[n,B]} readF(x,t) dx) / ∫_{[n,B]} r(x̄) dx` (`m < X`). -/
def readHaar (C : NormCtx) (k m : Nat) (hm : m < C.X) (z : Carrier5) : CField :=
  smulR (hMassInv C m hm) (xIntF (readF C k m z) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m))

theorem readHaar_F (C : NormCtx) (k m : Nat) (hm : m < C.X) (z : Carrier5) (x t : Real) :
    (readHaar C k m hm z).F x t = Rmul (hMassInv C m hm) (xInt (readF C k m z) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m) t) := rfl

-- ===========================================================================
-- (4) THE REAL-SCALE READING IDENTITY and the source theorem of the orbit reading.
-- ===========================================================================

/-- The pure algebra of the reading: from the orbit law `iN·uS = iX·uN` and the weight law `(iX·iX)·xb = 1`,
    `((r·iN)·(iX·xb))·uS = r·uN`. -/
theorem read_alg (r iN iX xb uS uN : Real) (hOrb : Req (Rmul iN uS) (Rmul iX uN)) (hW : Req (Rmul (Rmul iX iX) xb) one) :
    Req (Rmul (Rmul (Rmul r iN) (Rmul iX xb)) uS) (Rmul r uN) := by
  -- ((r·iN)·(iX·xb))·uS ≈ r·((iX·xb)·(iN·uS))
  have h1 : Req (Rmul (Rmul (Rmul r iN) (Rmul iX xb)) uS) (Rmul r (Rmul (Rmul iX xb) (Rmul iN uS))) := by
    refine Req_trans (Rmul_assoc _ _ _) ?_
    -- (r·iN)·((iX·xb)·uS) ≈ r·(iN·((iX·xb)·uS)) ≈ r·((iX·xb)·(iN·uS))
    refine Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl r) ?_)
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))
  refine Req_trans h1 (Rmul_congr (Req_refl r) ?_)
  -- (iX·xb)·(iN·uS) ≈ (iX·xb)·(iX·uN) ≈ ((iX·iX)·xb)·uN ≈ uN
  refine Req_trans (Rmul_congr (Req_refl _) hOrb) ?_
  -- (iX·xb)·(iX·uN) ≈ iX·(xb·(iX·uN)) ≈ iX·((xb·iX)·uN) ≈ iX·((iX·xb)·uN) ≈ iX·(iX·(xb·uN)) ≈ (iX·iX)·(xb·uN) ≈ ((iX·iX)·xb)·uN
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl iX) (Req_symm (Rmul_assoc _ _ _))) ?_)
  refine Req_trans (Rmul_congr (Req_refl iX) (Rmul_congr (Rmul_comm _ _) (Req_refl _))) ?_
  refine Req_trans (Rmul_congr (Req_refl iX) (Rmul_assoc _ _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr hW (Req_refl _)) (Rone_mul _))

/-- `n·(x̄·(t/n)) ≈ x̄·t`. -/
theorem orbit_mate_alg (m : Nat) (xb t : Real) :
    Req (Rmul (upR m) (Rmul xb (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))) (Rmul xb t) := by
  refine Req_trans (Rmul_congr (Req_refl _) (Req_symm (Rmul_assoc _ _ _))) ?_
  refine Req_trans (Rmul_comm _ _) (Req_trans (Rmul_assoc _ _ _) ?_)
  exact Req_trans (Rmul_congr (Req_refl _) (ofQ_recip_one m)) (Rmul_one _)

theorem upR_nonneg (m : Nat) : Rle zero (upR m) :=
  Rle_zero_of_Rnonneg (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg _))

theorem upQ_le_B (C : NormCtx) (m : Nat) (hm : m < C.X) : Qle (upQ m) (canonB C) := by
  show (((m + 1 : Nat) : Int)) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
  push_cast; omega

theorem upR_le_S (C : NormCtx) (m : Nat) (hm : m < C.X) : Rle (upR m) (ofQ C.S C.hSd) :=
  Rle_ofQ_ofQ Nat.one_pos C.hSd (Qle_trans (canonB_den C) (upQ_le_B C m hm) (canonB_le_S C))

theorem xcl_le_S (C : NormCtx) (x : Real) : Rle (xcl C x) (ofQ C.S C.hSd) :=
  Rle_trans (xcl_le_B C x) (Rle_ofQ_ofQ (canonB_den C) C.hSd (canonB_le_S C))

/-- `x̄·(t/n) ≥ a` when `x̄ ≥ n` and `t ≥ a`. -/
theorem mate_ge_a (C : NormCtx) (m : Nat) {xb t : Real} (hxn : Rle (upR m) xb) (hta : Rle (ofQ C.a C.had) t) :
    Rle (ofQ C.a C.had) (Rmul xb (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) := by
  have hn : Rnonneg (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))) :=
    Rnonneg_Rmul (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ C.had (Int.le_of_lt C.han))) hta))
      (Rnonneg_ofQ (Nat.succ_pos m) (invNQ_num m))
  -- t ≈ n·(t/n)
  have ht : Req t (Rmul (upR m) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) := by
    refine Req_symm (Req_trans (Rmul_comm _ _) (Req_trans (Rmul_assoc _ _ _) ?_))
    exact Req_trans (Rmul_congr (Req_refl t) (ofQ_recip_one m)) (Rmul_one t)
  refine Rle_trans hta (Rle_trans (Rle_of_Req ht) ?_)
  exact Rmul_le_Rmul_right hn hxn

theorem c_le_xcl (C : NormCtx) (x : Real) : Rle (ofQ (canonC C) (canonC_den C)) (xcl C x) :=
  Rle_trans (Rle_ofQ_ofQ (canonC_den C) (by decide) (canonC_le_one C)) (xcl_ge_one C x)

/-- **★ THE REAL-SCALE READING IDENTITY**: for `x̄ ≥ n` and `t ∈ [a, a+w]`, the reading integrand at `(x,t)` on the
    analysis `A_k f` is `r(x̄)·U_n(f,t)`. -/
theorem readF_source (C : NormCtx) (k m : Nat) (hm : m < C.X) (f : L2Test) (x t : Real)
    (hxn : Rle (upR m) (xcl C x)) (hta : Rle (ofQ C.a C.had) t) (htw : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req ((readF C k m (cutAnalysis5 C k f)).F x t) (Rmul (rOne (xcl C x)) (Uc C (upR m) f t)) := by
  rw [readF_F]
  have htb : Req (tBand C t) t := tBand_eq_of_win C hta htw
  have hs : Req (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m))))
      (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m)))) :=
    Rmul_congr (Req_refl _) (Rmul_congr htb (Req_refl _))
  have hrec : Req ((recUF C k (cutAnalysis5 C k f)).F (xcl C x) (Rmul (xcl C x) (Rmul (tBand C t) (ofQ (invNQ m) (Nat.succ_pos m)))))
      (Uc C (xcl C x) f (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))) := by
    refine Req_trans ((recUF C k (cutAnalysis5 C k f)).hfct _ hs) ?_
    exact Req_trans (recUF_source C k f (xcl C x) _) (Uc_congr_x C (xcl_idem C x) f _)
  refine Req_trans (Rmul_congr (Req_refl _) hrec) ?_
  have hOrb : Req (Rmul (invSq C (upR m)) (Uc C (xcl C x) f (Rmul (xcl C x) (Rmul t (ofQ (invNQ m) (Nat.succ_pos m))))))
      (Rmul (invSq C (xcl C x)) (Uc C (upR m) f t)) :=
    Uc_orbit C f (xcl_zero_le C x) (xcl_le_S C x) (upR_nonneg m) (upR_le_S C m hm) (mate_ge_a C m hxn hta) hta
      (orbit_mate_alg m (xcl C x) t)
  obtain ⟨kx, hkx⟩ := Pos_of_Rle_ofQ (canonC_num C) (canonC_den C) (c_le_xcl C x)
  have hW := invSq_sq_mul_self C (c_le_xcl C x) (xcl_le_B C x) hkx
  exact read_alg _ _ _ _ _ _ hOrb hW

/-- `[n, n + (X − m)] ⊆ [n, B]`: the window scale satisfies `x̄ = x ≥ n`. -/
theorem win_xcl_ge_n (C : NormCtx) (m : Nat) (hm : m < C.X) (s : Real) (hs0 : Rle zero s) (hs1 : Rle s one) :
    Rle (upR m) (xcl C (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s)) := by
  have hlo : Rle (ofQ (upQ m) Nat.one_pos) (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) :=
    affineMap_ge_lo_c5 _ _ _ _ (wnQ_num C m) s hs0
  have hhi : Rle (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) (ofQ (canonB C) (canonB_den C)) :=
    Rle_trans (affineMap_le_hi_c5 _ _ _ _ (wnQ_num C m) s hs1) (Rle_ofQ_ofQ _ _ (upQ_add_wnQ_le_B C m (Nat.le_of_lt hm)))
  have h1 : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) :=
    Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
      show (1 : Int) * ((1 : Nat) : Int) ≤ ((m + 1 : Nat) : Int) * ((1 : Nat) : Int)
      push_cast; omega)) hlo
  exact Rle_trans hlo (Rle_of_Req (Req_symm (xcl_eq_of_band C h1 hhi)))

/-- **★ THE ORBIT READING IS `U_n(f,t)`** on every analysis, for `t ∈ [a, a+w]` and every `m < X`. -/
theorem readHaar_source (C : NormCtx) (k m : Nat) (hm : m < C.X) (f : L2Test) (x t : Real)
    (hta : Rle (ofQ C.a C.had) t) (htw : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req ((readHaar C k m hm (cutAnalysis5 C k f)).F x t) (Uc C (upR m) f t) := by
  rw [readHaar_F]
  have hpt : ∀ s, Rle zero s → Rle s one →
      Req ((readF C k m (cutAnalysis5 C k f)).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) t)
          (Rmul (Uc C (upR m) f t) ((rOneClF C).F (affineMap (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos s) one)) :=
    fun s hs0 hs1 => Req_trans (readF_source C k m hm f _ t (win_xcl_ge_n C m hm s hs0 hs1) hta htw) (Rmul_comm _ _)
  have hI := xInt_congr_smul (readF C k m (cutAnalysis5 C k f)) (rOneClF C) (upQ m) (wnQ C m) Nat.one_pos Nat.one_pos (wnQ_num C m)
    (Uc C (upR m) f t) t one hpt
  unfold hMass at *
  refine Req_trans (Rmul_congr (Req_refl _) hI) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_))
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_comm _ _) (hMassInv_mul C m hm))) (Rmul_one _)

-- ===========================================================================
-- (5) THE SIGNED FIVE-CHANNEL MATRIX.
-- ===========================================================================

/-- The zero field. -/
def zeroF : CField := constF zero Nat.one_pos (by decide) (Rle_of_Req (Req_trans Rabs_zero (Req_symm (Req_of_seq_Qeq (fun _ => Qeq_refl _)))))

/-- `Z^{rec} = x̄·K_k(x̄)·(U^{rec} − r(x̄)·V^{rec})`. -/
def ZrecF (C : NormCtx) (k : Nat) (z : Carrier5) : CField :=
  mulF (mulF (xclF C) (KxF C k)) (subF (recUF C k z) (mulF (rOneClF C) (recVF C k z)))
/-- `W^{rec} = r(x̄)·V^{rec}`. -/
def WrecF (C : NormCtx) (k : Nat) (z : Carrier5) : CField := mulF (rOneClF C) (recVF C k z)

/-- **★ THE ATLAS MATRIX** `CutCarrier → CycleCarrier`: every cycle coordinate `B = (u + v)/4` from cut data only. -/
def atlasMatrix (C : NormCtx) (k : Nat) (z : Carrier5) : Carrier5 where
  pole := bCoefF (recUF C k z) (negF (recVF C k z))
  prime := fun m => if hm : m < C.X then bCoefF (readHaar C k m hm z) (recVFarF z) else zeroF
  const := bCoefF (recVFarF z) (recVFarF z)
  tail := bCoefF (ZrecF C k z) (WrecF C k z)
  far := bCoefF (recVFarF z) (negF (recVFarF z))

theorem atlasMatrix_pole_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (atlasMatrix C k z).pole.F x t = bCoefGa one ((recUF C k z).F x t) (Rneg ((recVF C k z).F x t)) := rfl
theorem atlasMatrix_prime_F (C : NormCtx) (k m : Nat) (hm : m < C.X) (z : Carrier5) (x t : Real) :
    ((atlasMatrix C k z).prime m).F x t = bCoefGa one ((readHaar C k m hm z).F x t) ((recVFarF z).F x t) := by
  show ((if hm : m < C.X then bCoefF (readHaar C k m hm z) (recVFarF z) else zeroF)).F x t = _
  rw [dif_pos hm]
  rfl
theorem atlasMatrix_const_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (atlasMatrix C k z).const.F x t = bCoefGa one ((recVFarF z).F x t) ((recVFarF z).F x t) := rfl
theorem ZrecF_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (ZrecF C k z).F x t = Rmul (Rmul (xcl C x) (Kx C k x)) (Rsub ((recUF C k z).F x t) (Rmul (rOne (xcl C x)) ((recVF C k z).F x t))) := rfl
theorem WrecF_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (WrecF C k z).F x t = Rmul (rOne (xcl C x)) ((recVF C k z).F x t) := rfl
theorem atlasMatrix_tail_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (atlasMatrix C k z).tail.F x t = bCoefGa one ((ZrecF C k z).F x t) ((WrecF C k z).F x t) := rfl
theorem atlasMatrix_far_F (C : NormCtx) (k : Nat) (z : Carrier5) (x t : Real) :
    (atlasMatrix C k z).far.F x t = bCoefGa one ((recVFarF z).F x t) (Rneg ((recVFarF z).F x t)) := rfl

-- ===========================================================================
-- (6) Agreement on the measured supports, and EXACT reproduction.
-- ===========================================================================

/-- The Haar window `t ∈ [a, a+w]`. -/
def InWin (C : NormCtx) (t : Real) : Prop := Rle (ofQ C.a C.had) t ∧ Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))

/-- **Agreement of two carrier elements on the measured supports of the five channels.** -/
structure EqOnSupport5 (C : NormCtx) (k : Nat) (z z' : Carrier5) : Prop where
  pole : ∀ x t, Rle one x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t → Req (z.pole.F x t) (z'.pole.F x t)
  prime : ∀ m, m < C.X → ∀ x t, InWin C t → Req ((z.prime m).F x t) ((z'.prime m).F x t)
  const : ∀ x t, InWin C t → Req (z.const.F x t) (z'.const.F x t)
  tail : ∀ x t, Rle (ofQ (tailLo k) (tailLo_den k)) x → Rle x (ofQ (canonB C) (canonB_den C)) → InWin C t →
    Req (z.tail.F x t) (z'.tail.F x t)
  far : ∀ x t, InWin C t → Req (z.far.F x t) (z'.far.F x t)

theorem inWin_of_affine (C : NormCtx) (y : Real) (h0 : Rle zero y) (h1 : Rle y one) : InWin C (affineMap C.a C.w C.had C.hw y) :=
  ⟨affineMap_ge_lo_c5 _ _ _ _ C.hwn y h0, affineMap_le_hi_c5 _ _ _ _ C.hwn y h1⟩

/-- **★ EXACT REPRODUCTION**: `atlasMatrix C k (A_k f)` agrees with the cycle analysis `B_k f` on every measured support. -/
theorem atlasMatrix_reproduces (C : NormCtx) (k : Nat) (f : L2Test) :
    EqOnSupport5 C k (cycleAnalysis5 C k f) (atlasMatrix C k (cutAnalysis5 C k f)) where
  pole := fun x t hx1 hxB _ => by
    rw [cycleAnalysis5_pole, atlasMatrix_pole_F]
    refine Req_symm (bCoefGa_congr ?_ (Rneg_congr (recVF_source C k f x t)))
    exact Req_trans (recUF_source C k f x t) (Uc_congr_x C (xcl_eq_of_band C hx1 hxB) f t)
  prime := fun m hm x t ht => by
    rw [cycleAnalysis5_prime, atlasMatrix_prime_F C k m hm]
    exact Req_symm (bCoefGa_congr (readHaar_source C k m hm f x t ht.1 ht.2) (recVFarF_source C k f x t))
  const := fun x t _ => by
    rw [cycleAnalysis5_const, atlasMatrix_const_F]
    exact Req_symm (bCoefGa_congr (recVFarF_source C k f x t) (recVFarF_source C k f x t))
  tail := fun x t _ _ _ => by
    rw [cycleAnalysis5_tail, atlasMatrix_tail_F, ZrecF_F, WrecF_F]
    refine Req_symm (bCoefGa_congr ?_ (Rmul_congr (Req_refl _) (recVF_source C k f x t)))
    exact Rmul_congr (Req_refl _) (Rsub_congr (recUF_source C k f x t) (Rmul_congr (Req_refl _) (recVF_source C k f x t)))
  far := fun x t _ => by
    rw [cycleAnalysis5_far, atlasMatrix_far_F]
    exact Req_symm (bCoefGa_congr (recVFarF_source C k f x t) (Rneg_congr (recVFarF_source C k f x t)))

-- ===========================================================================
-- (7) The quadratic form only sees the supports; the range bound is the sign of `cut − cycle`.
-- ===========================================================================

theorem affine_pole_ge_one (C : NormCtx) (s : Real) (hs : Rle zero s) :
    Rle one (affineMap (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) s) :=
  affineMap_ge_lo_c5 _ _ _ _ (poleW_num C) s hs
theorem affine_pole_le_B (C : NormCtx) (s : Real) (hs : Rle s one) :
    Rle (affineMap (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) s) (ofQ (canonB C) (canonB_den C)) :=
  Rle_trans (affineMap_le_hi_c5 _ _ _ _ (poleW_num C) s hs) (Rle_of_Req (ofQ_congr _ _ (Qadd_sub_cancel_left (⟨1, 1⟩ : Q) (canonB C))))
theorem affine_tail_ge_lo (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (s : Real) (hs : Rle zero s) :
    Rle (ofQ (tailLo k) (tailLo_den k)) (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) :=
  affineMap_ge_lo_c5 _ _ _ _ (tailGap_num_nonneg C k hk) s hs
theorem affine_tail_le_B (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (s : Real) (hs : Rle s one) :
    Rle (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s) (ofQ (canonB C) (canonB_den C)) :=
  Rle_trans (affineMap_le_hi_c5 _ _ _ _ (tailGap_num_nonneg C k hk) s hs)
    (Rle_of_Req (ofQ_congr _ _ (Qadd_sub_cancel_left (tailLo k) (canonB C))))

/-- **The five-channel form only sees the supports**: support-agreement of both arguments gives equal values. -/
theorem inner5_congr_support (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) {z₁ z₁' z₂ z₂' : Carrier5}
    (h₁ : EqOnSupport5 C k z₁ z₁') (h₂ : EqOnSupport5 C k z₂ z₂') :
    Req (inner5 C k hk fc z₁ z₂) (inner5 C k hk fc z₁' z₂') := by
  unfold inner5 inner4 poleG primeG constG tailG farG gramX gramT
  refine Radd_congr (Radd_congr (Radd_congr (Radd_congr ?_ ?_) ?_) ?_) ?_
  · refine intX_congr_win C _ _ _ _ _ _ _ (fun s hs0 hs1 y hy0 hy1 => ?_)
    rw [mulF_F, mulF_F, mulF_F, mulF_F]
    exact Rmul_congr (Rmul_congr (Req_refl _) (h₁.pole _ _ (affine_pole_ge_one C s hs0) (affine_pole_le_B C s hs1) (inWin_of_affine C y hy0 hy1)))
      (h₂.pole _ _ (affine_pole_ge_one C s hs0) (affine_pole_le_B C s hs1) (inWin_of_affine C y hy0 hy1))
  · refine RsumN_congr C.X (fun m hm => ?_)
    refine intT_congr_win C _ _ _ (fun y hy0 hy1 => ?_)
    rw [mulF_F, mulF_F, mulF_F, mulF_F]
    exact Rmul_congr (Rmul_congr (Req_refl _) (h₁.prime m hm _ _ (inWin_of_affine C y hy0 hy1))) (h₂.prime m hm _ _ (inWin_of_affine C y hy0 hy1))
  · refine intT_congr_win C _ _ _ (fun y hy0 hy1 => ?_)
    rw [mulF_F, mulF_F, mulF_F, mulF_F]
    exact Rmul_congr (Rmul_congr (Req_refl _) (h₁.const _ _ (inWin_of_affine C y hy0 hy1))) (h₂.const _ _ (inWin_of_affine C y hy0 hy1))
  · refine intX_congr_win C _ _ _ _ _ _ _ (fun s hs0 hs1 y hy0 hy1 => ?_)
    rw [mulF_F, mulF_F, mulF_F, mulF_F]
    exact Rmul_congr (Rmul_congr (Req_refl _) (h₁.tail _ _ (affine_tail_ge_lo C k hk s hs0) (affine_tail_le_B C k hk s hs1) (inWin_of_affine C y hy0 hy1)))
      (h₂.tail _ _ (affine_tail_ge_lo C k hk s hs0) (affine_tail_le_B C k hk s hs1) (inWin_of_affine C y hy0 hy1))
  · refine intT_congr_win C _ _ _ (fun y hy0 hy1 => ?_)
    rw [mulF_F, mulF_F, mulF_F, mulF_F]
    exact Rmul_congr (Rmul_congr (Req_refl _) (h₁.far _ _ (inWin_of_affine C y hy0 hy1))) (h₂.far _ _ (inWin_of_affine C y hy0 hy1))

/-- **The energy of the matrix image of `A_k f` is the cycle energy of `f`.** -/
theorem energy5_matrix_eq (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (f : L2Test) :
    Req (energy5 C k hk fc (atlasMatrix C k (cutAnalysis5 C k f))) (energy5 C k hk fc (cycleAnalysis5 C k f)) :=
  Req_symm (inner5_congr_support C k hk fc (atlasMatrix_reproduces C k f) (atlasMatrix_reproduces C k f))

/-- **★ THE RANGE BOUND IS THE SIGN**: `‖atlasMatrix(A_k f)‖² ≤ ‖A_k f‖²` ⟺ `cutEnergy(f) − cycleEnergy(f) ≥ 0`. -/
theorem atlasMatrix_range_bound_iff (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (f : L2Test) :
    Rle (energy5 C k hk fc (atlasMatrix C k (cutAnalysis5 C k f))) (energy5 C k hk fc (cutAnalysis5 C k f)) ↔
      Rnonneg (Rsub (energy5 C k hk fc (cutAnalysis5 C k f)) (energy5 C k hk fc (cycleAnalysis5 C k f))) :=
  ⟨fun h => Rnonneg_Rsub_of_Rle (Rle_trans (Rle_of_Req (Req_symm (energy5_matrix_eq C k hk fc f))) h),
   fun h => Rle_trans (Rle_of_Req (energy5_matrix_eq C k hk fc f)) (Rle_of_Rnonneg_Rsub h)⟩

/-- **★ THE UNIVERSAL OBSTRUCTION (target-free form)**: for EVERY map `T : Carrier5 → Carrier5` that reproduces the
    cycle analysis of `f` on the supports, the range bound `‖T(A_k f)‖² ≤ ‖A_k f‖²` forces `cutEnergy − cycleEnergy ≥ 0`.
    No structure of `T` (locality, routing, asymptotics) enters. -/
theorem colligation_range_bound_imp (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (T : Carrier5 → Carrier5) (f : L2Test)
    (hrep : EqOnSupport5 C k (cycleAnalysis5 C k f) (T (cutAnalysis5 C k f)))
    (hbd : Rle (energy5 C k hk fc (T (cutAnalysis5 C k f))) (energy5 C k hk fc (cutAnalysis5 C k f))) :
    Rnonneg (Rsub (energy5 C k hk fc (cutAnalysis5 C k f)) (energy5 C k hk fc (cycleAnalysis5 C k f))) :=
  Rnonneg_Rsub_of_Rle (Rle_trans (Rle_of_Req (inner5_congr_support C k hk fc hrep hrep)) hbd)

end UOR.Bridge.F1Square.Square
