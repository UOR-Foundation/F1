/-
F1 square — **THE ANCHOR KERNEL IN AUTOCORRELATION FORM** (`AtlasAnchorAutocorr.lean`, target-free).

For an ANCHOR PROFILE `h` (a certified field constant in the scale and vanishing below the window floor — two of
the ten laws of `FullSourceCoherent5`, `anchorProfile_of_fullCoherent`), with `H(t) = h(1,t)`,

    `N_H = ∫ H(t)² w·dt/t`,     `R_H(x) = ∫ x̄^{-1/2}·H(t/x̄)·H(t) w·dt/t`   (Haar integrals over the window),

the executable five-channel kernel `anchorKernel5` equals (`anchorKernel5_autocorr`)

    `AK_k(H) = −2∫_1^B (1 + 1/x)·R_H(x) dx + 2Σ_{n ≤ X} Λ(n)·R_H(n) + (log 4π + γ)·N_H`
             `+ 2∫_{1+2^{-k}}^B K_k(x̄)·(R_H(x) − N_H/x̄) dx − 2·fc·N_H`,

with `K_k(x̄) = 1/max(x̄ − 1/x̄, 2^{-k})` the floored archimedean kernel and `fc` the far mass parameter (on the
range `fc = farCoef C k = ∫_B^∞ K_k(x)/x dx`).  `R_H(x) = 0` for `x ≥ B` (`RH_zero_beyond_B`: the mate
`t/x ≤ (a+w)/B ≤ a` lies below the floor), so the far term is the continuation of the last integral to `[B, ∞)`
with `R_H ≡ 0` there.  This is the signed nonlocal Mellin/Toeplitz form of the cross form; no sign is asserted.

Also the precise support statement of the fiber mask: `maskF = 0` for `x̄ ≤ λ(t)` and for `x̄ ≥ μ(t)`
(`maskF_zero_of_le_lam`, `maskF_zero_of_ge_mu`), so the mask is supported in `λ(t) ≤ x̄ ≤ μ(t)`, the region
where `mate_ge_a_of_lam` and `mate_le_aw_of_mu` apply.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasAnchorKernel
import F1Square.Analysis.WindowBoundReal
import F1Square.Analysis.ComplexLimitCore

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis
open CField

-- ===========================================================================
-- (0) Anchor profiles.
-- ===========================================================================

/-- **An anchor profile**: a certified field constant in the scale and vanishing below the window floor. -/
structure AnchorProfile (C : NormCtx) (h : CField) : Prop where
  scale_const : ∀ x x' t, Req (h.F x t) (h.F x' t)
  zero_low : ∀ x s, Rle s (ofQ C.a C.had) → Req (h.F x s) zero

/-- The anchor of a fully coherent element is an anchor profile (laws (4) and (10)). -/
theorem anchorProfile_of_fullCoherent (C : NormCtx) (k : Nat) {z : Carrier5} (hz : FullSourceCoherent5 C k z) :
    AnchorProfile C (anchorOf z) :=
  ⟨fun x x' t => Rmul_congr (Req_refl _) (hz.far_const x x' t), hz.anchor_zero⟩

-- ===========================================================================
-- (1) Plumbing.
-- ===========================================================================

theorem smulQF_F_ac (q : Q) (hqd : 0 < q.den) (hqn : 0 ≤ q.num) (u : CField) (x t : Real) :
    (smulQF q hqd hqn u).F x t = Rmul (ofQ q hqd) (u.F x t) := rfl
theorem subF_F_ac (u v : CField) (x t : Real) : (subF u v).F x t = Rsub (u.F x t) (v.F x t) := rfl

/-- `u(x,·) ≈ c·v(x,·)` ⟹ `∫ u(x,·) ≈ c·∫ v(x,·)`. -/
theorem intT_smul_pt (C : NormCtx) (u v : CField) (x c : Real) (h : ∀ t, Req (u.F x t) (Rmul c (v.F x t))) :
    Req (intT C u x) (Rmul c (intT C v x)) :=
  intU_smul_free c _ _ _ _ _ _ _ _ (fun _ => h _)

/-- Agreement across two scales: `u(x,·) ≈ v(x',·)` ⟹ `∫ u(x,·) ≈ ∫ v(x',·)`. -/
theorem intT_congr_scale (C : NormCtx) (u v : CField) (x x' : Real) (h : ∀ t, Req (u.F x t) (v.F x' t)) :
    Req (intT C u x) (intT C v x') :=
  intU_congr_free _ _ _ _ _ _ _ _ (fun _ => h _)

/-- `|∫ z(x,·)| ≤ M_z`. -/
theorem intT_abs_le_M (C : NormCtx) (z : CField) (x : Real) : Rle (Rabs (intT C z x)) (ofQ z.M z.hMd) :=
  riemannIntegral_abs_le_unit_real _ _ _ _ _ (fun y _ _ => z.hbd x (affineMap C.a C.w C.had C.hw y))

theorem four_smul_quarter_ac (X : Real) : Req (Rmul (Rmul (ofQ q4 Nat.one_pos) X) cQ) X :=
  Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _))
    (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr four_quarter_j (Req_refl _)) (Rone_mul _))))

/-- The density/cross normalization `(4·(A·W))·(¼·H) = A·(W·H)`. -/
theorem dens_cross_ac (A W H : Real) :
    Req (Rmul (Rmul (ofQ q4 Nat.one_pos) (Rmul A W)) (Rmul cQ H)) (Rmul A (Rmul W H)) :=
  Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (four_smul_quarter_ac _) (Req_refl _)) (Rmul_assoc _ _ _))

-- ===========================================================================
-- (2) The autocorrelation data `N_H`, `R_H`.
-- ===========================================================================

/-- `(x,t) ↦ w·r(t)·h(x,t)²`. -/
def NHF (C : NormCtx) (h : CField) : CField := mulF (wrF C) (mulF h h)
theorem NHF_F (C : NormCtx) (h : CField) (x t : Real) :
    (NHF C h).F x t = Rmul (Rmul (ofQ C.w C.hw) (rEv C t)) (Rmul (h.F x t) (h.F x t)) := rfl
/-- **`N_H = ∫ H(t)² w·dt/t`** (the Haar integral at scale `1`). -/
def NH (C : NormCtx) (h : CField) : Real := intT C (NHF C h) one

/-- `(x,t) ↦ w·r(t)·x̄^{-1/2}·h(1, t̄/x̄)·h(x,t)`. -/
def RHF (C : NormCtx) (h : CField) : CField := mulF (wrF C) (mulF (shiftUF C h) h)
theorem RHF_F (C : NormCtx) (h : CField) (x t : Real) :
    (RHF C h).F x t = Rmul (Rmul (ofQ C.w C.hw) (rEv C t)) (Rmul ((shiftUF C h).F x t) (h.F x t)) := rfl
/-- **`R_H(x) = ∫ x̄^{-1/2}·H(t/x̄)·H(t) w·dt/t`** — the autocorrelation of the anchor at scale `x`. -/
def RH (C : NormCtx) (h : CField) (x : Real) : Real := intT C (RHF C h) x

/-- `x ↦ R_H(x)` as a certified field (constant in `t`; modulus `Lx` of `RHF`, bound `M` of `RHF`). -/
def RHXF (C : NormCtx) (h : CField) : CField :=
  ofX (RH C h) (L := (RHF C h).Lx) (M := (RHF C h).M) (RHF C h).hLxd (RHF C h).hLxn (RHF C h).hMd (RHF C h).hMn
    (intT_lip C (RHF C h)) (fun x => intT_abs_le_M C (RHF C h) x) (intT_fc C (RHF C h))
theorem RHXF_F (C : NormCtx) (h : CField) (x t : Real) : (RHXF C h).F x t = RH C h x := rfl

/-- `N_H` as a constant field. -/
def NHconstF (C : NormCtx) (h : CField) : CField :=
  constF (NH C h) (NHF C h).hMd (NHF C h).hMn (intT_abs_le_M C (NHF C h) one)
theorem NHconstF_F (C : NormCtx) (h : CField) (x t : Real) : (NHconstF C h).F x t = NH C h := rfl

-- ===========================================================================
-- (3) The five channels in autocorrelation form.
-- ===========================================================================

/-- Constant channel: `∫ constDens5·¼·h² = (log 4π + γ)·N_H`. -/
theorem constTerm_ac (C : NormCtx) (h : CField) :
    Req (intT C (mulF (constDens5 C) (crossF h h)) one) (Rmul archConst (NH C h)) :=
  intT_smul_pt C _ (NHF C h) one archConst (fun _ => dens_cross_ac archConst _ _)

/-- Far channel: `∫ farDens5·¼·h·(−h) = −2·fc·N_H`. -/
theorem farTerm_ac (C : NormCtx) (fc : Real) (h : CField) :
    Req (intT C (mulF (farDens5 C fc) (crossF h (negF h))) one) (Rneg (Rmul (Rmul cTwo fc) (NH C h))) := by
  refine Req_trans (intT_smul_pt C _ (NHF C h) one (Rneg (Rmul cTwo fc)) (fun t => ?_)) (Rmul_neg_left _ _)
  refine Req_trans (dens_cross_ac (Rmul cTwo fc) _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_neg_right _ _))) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_neg_right _ _)) ?_
  exact Req_trans (Rmul_neg_right _ _) (Req_symm (Rmul_neg_left _ _))

/-- `x ↦ −2(1 + 1/x)·R_H(x)`. -/
def poleACF (C : NormCtx) (h : CField) : CField :=
  mulF (negF (smulQF q2 Nat.one_pos (by decide) oneRF)) (RHXF C h)
theorem poleACF_F (C : NormCtx) (h : CField) (x t : Real) :
    (poleACF C h).F x t = Rmul (Rneg (Rmul (ofQ q2 Nat.one_pos) (Radd one (rOne x)))) (RH C h x) := rfl
/-- **The pole term** `−2∫_1^B (1 + 1/x)·R_H(x) dx`. -/
def poleAC (C : NormCtx) (h : CField) : Real :=
  xInt (poleACF C h) (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C) one

theorem poleTerm_pt (C : NormCtx) (h : CField) (x : Real) :
    Req (intT C (mulF (poleDens5 C) (crossF (shiftUF C h) (negF h))) x) ((poleACF C h).F x one) := by
  rw [poleACF_F]
  refine intT_smul_pt C _ (RHF C h) x _ (fun t => ?_)
  refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Req_symm (Rmul_assoc _ _ _))) (Req_refl _)) ?_
  refine Req_trans (dens_cross_ac (Rmul (ofQ q2 Nat.one_pos) (Radd one (rOne x))) _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_neg_right _ _))) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_neg_right _ _)) ?_
  exact Req_trans (Rmul_neg_right _ _) (Req_symm (Rmul_neg_left _ _))

/-- Pole channel: `∫_1^B ∫ poleDens5·¼·(x^{-1/2}h(t/x))·(−h) = poleAC`. -/
theorem poleTerm_ac (C : NormCtx) (h : CField) :
    Req (intX C (mulF (poleDens5 C) (crossF (shiftUF C h) (negF h))) (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C))
        (poleAC C h) := by
  unfold intX poleAC xInt
  exact intI_congr_free _ _ _ _ _ _ _ _ (fun x => poleTerm_pt C h x) _ _ _ _ _

/-- **The prime term** `2Σ_{n ≤ X} Λ(n)·R_H(n)` (`n = m + 1`, `Λ(1) = 0`). -/
def primeAC (C : NormCtx) (h : CField) : Real :=
  RsumN (fun m => Rmul (Rmul (ofQ q2 Nat.one_pos) (vonMangoldt (m + 1))) (RH C h (upR m))) C.X

/-- At an active place `n = m + 1 ≤ B`, the shifted field at scale `1` is the scale-`n` shift. -/
theorem shiftUn_eq_shiftU_ac (C : NormCtx) (h : CField) (m : Nat) (hm : m < C.X) (t : Real) :
    Req ((shiftUnF C m h).F one t) ((shiftUF C h).F (upR m) t) := by
  rw [shiftUnF_F, shiftUF_F]
  have hx : Req (xcl C (upR m)) (upR m) := xcl_eq_of_band C (one_le_upR_R m) (upR_le_B_R C m hm)
  refine Rmul_congr (invSq_congr_ak C (Req_symm hx)) (h.hfct one (Rmul_congr (Req_refl _) ?_))
  exact Req_trans (Req_symm (rOne_upR m)) (clampedInv_congr _ _ _ (Req_symm hx))

theorem primeTerm_m_ac (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (m : Nat) (hm : m < C.X) :
    Req (intT C (mulF (primeDens5 C m) (crossF (shiftUnF C m h) h)) one)
        (Rmul (Rmul (ofQ q2 Nat.one_pos) (vonMangoldt (m + 1))) (RH C h (upR m))) := by
  refine Req_trans (intT_smul_pt C _ (mulF (wrF C) (mulF (shiftUnF C m h) h)) one
    (Rmul (ofQ q2 Nat.one_pos) (vonMangoldt (m + 1))) (fun t => ?_)) ?_
  · refine Req_trans (Rmul_congr (Rmul_congr (Req_refl _) (Req_symm (Rmul_assoc _ _ _))) (Req_refl _)) ?_
    exact dens_cross_ac _ _ _
  · refine Rmul_congr (Req_refl _) (intT_congr_scale C _ (RHF C h) one (upR m) (fun t => ?_))
    exact Rmul_congr (Req_refl _) (Rmul_congr (shiftUn_eq_shiftU_ac C h m hm t) (hp.scale_const one (upR m) t))

/-- Prime channel: `Σ_m ∫ primeDens5_m·¼·(n^{-1/2}h(t/n))·h = primeAC`. -/
theorem primeTerm_ac (C : NormCtx) (h : CField) (hp : AnchorProfile C h) :
    Req (RsumN (fun m => intT C (mulF (primeDens5 C m) (crossF (shiftUnF C m h) h)) one) C.X) (primeAC C h) :=
  RsumN_congr C.X (fun m hm => primeTerm_m_ac C h hp m hm)

/-- The tail integrand algebra: `W·(((x̄K)(S − r h))(r h)) = K·(W(S h) − r·(W(h h)))` from `x̄·r = 1`. -/
theorem tail_inner_ac (xb K r S h W : Real) (hxr : Req (Rmul xb r) one) :
    Req (Rmul W (Rmul (Rmul (Rmul xb K) (Rsub S (Rmul r h))) (Rmul r h)))
        (Rmul K (Rsub (Rmul W (Rmul S h)) (Rmul r (Rmul W (Rmul h h))))) := by
  have hA : Req (Rmul (Rmul (Rmul xb K) (Rsub S (Rmul r h))) (Rmul r h)) (Rmul K (Rmul (Rsub S (Rmul r h)) h)) := by
    refine Req_trans (Rmul_assoc _ _ _) ?_
    refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
    refine Req_trans (Rmul_assoc _ _ _) ?_
    refine Rmul_congr (Req_refl K) ?_
    refine Req_trans (Rmul_congr (Req_refl xb) (Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))) ?_
    exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr hxr (Req_refl _)) (Rone_mul _))
  have hB : Req (Rmul (Rsub S (Rmul r h)) h) (Rsub (Rmul S h) (Rmul r (Rmul h h))) :=
    Req_trans (Rmul_sub_distrib_right _ _ _) (Rsub_congr (Req_refl _) (Rmul_assoc _ _ _))
  refine Req_trans (Rmul_congr (Req_refl W) (Req_trans hA (Rmul_congr (Req_refl K) hB))) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_))
  refine Rmul_congr (Req_refl K) ?_
  refine Req_trans (Rmul_sub_distrib W _ _) (Rsub_congr (Req_refl _) ?_)
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- `x̄·(1/x̄) = 1`. -/
theorem xcl_mul_rOne_ac (C : NormCtx) (x : Real) : Req (Rmul (xcl C x) (rOne (xcl C x))) one :=
  Rmul_clampedInv_one (xcl C x) (xcl_ge_one C x)

/-- `x ↦ 2K_k(x̄)·(R_H(x) − N_H/x̄)`. -/
def tailACF (C : NormCtx) (k : Nat) (h : CField) : CField :=
  mulF (smulQF q2 Nat.one_pos (by decide) (KxF C k)) (subF (RHXF C h) (mulF (rOneClF C) (NHconstF C h)))
theorem tailACF_F (C : NormCtx) (k : Nat) (h : CField) (x t : Real) :
    (tailACF C k h).F x t = Rmul (Rmul (ofQ q2 Nat.one_pos) (Kx C k x)) (Rsub (RH C h x) (Rmul (rOne (xcl C x)) (NH C h))) := rfl
/-- **The compact tail term** `2∫_{1+2^{-k}}^B K_k(x̄)·(R_H(x) − N_H/x̄) dx`. -/
def tailAC (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (h : CField) : Real :=
  xInt (tailACF C k h) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk) one

theorem tailTerm_pt (C : NormCtx) (k : Nat) (h : CField) (hp : AnchorProfile C h) (x : Real) :
    Req (intT C (mulF (tailDens5 C) (crossF (ZhF C k h) (WhF C h))) x) ((tailACF C k h).F x one) := by
  rw [tailACF_F]
  refine Req_trans (intT_smul_pt C _ (subF (RHF C h) (mulF (rOneClF C) (NHF C h))) x
    (Rmul (ofQ q2 Nat.one_pos) (Kx C k x)) (fun t => ?_)) ?_
  · rw [mulF_crossF_F, ZhF_F, WhF_F]
    refine Req_trans (dens_cross_ac (ofQ q2 Nat.one_pos) _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (tail_inner_ac _ _ _ _ _ _ (xcl_mul_rOne_ac C x))) ?_
    exact Req_symm (Rmul_assoc _ _ _)
  · refine Rmul_congr (Req_refl _) ?_
    refine Req_trans (intT_sub_pt C (RHF C h) (mulF (rOneClF C) (NHF C h)) _ x (fun t => Req_refl _)) ?_
    refine Rsub_congr (Req_refl _) ?_
    refine Req_trans (intT_smul_pt C _ (NHF C h) x (rOne (xcl C x)) (fun t => Req_refl _)) ?_
    exact Rmul_congr (Req_refl _) (intT_congr_scale C _ _ x one (fun t =>
      Rmul_congr (Req_refl _) (Rmul_congr (hp.scale_const x one t) (hp.scale_const x one t))))

/-- Compact tail channel: `∫_{[1+2^{-k},B]} ∫ tailDens5·¼·Z_h·W_h = tailAC`. -/
theorem tailTerm_ac (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (h : CField) (hp : AnchorProfile C h) :
    Req (intX C (mulF (tailDens5 C) (crossF (ZhF C k h) (WhF C h))) (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k)
          (tailGap_num_nonneg C k hk))
        (tailAC C k hk h) := by
  unfold intX tailAC xInt
  exact intI_congr_free _ _ _ _ _ _ _ _ (fun x => tailTerm_pt C k h hp x) _ _ _ _ _

/-- **★ THE ANCHOR KERNEL IN AUTOCORRELATION FORM** (for every anchor profile, every `k ≥ 1`, every far mass `fc`). -/
theorem anchorKernel5_autocorr (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (h : CField) (hp : AnchorProfile C h) :
    Req (anchorKernel5 C k hk fc h)
      (Radd (Radd (Radd (Radd (poleAC C h) (primeAC C h)) (Rmul archConst (NH C h))) (tailAC C k hk h))
        (Rneg (Rmul (Rmul cTwo fc) (NH C h)))) := by
  unfold anchorKernel5
  exact Radd_congr (Radd_congr (Radd_congr (Radd_congr (poleTerm_ac C h) (primeTerm_ac C h hp)) (constTerm_ac C h))
    (tailTerm_ac C k hk h hp)) (farTerm_ac C fc h)

-- ===========================================================================
-- (4) `R_H` vanishes beyond the band edge.
-- ===========================================================================

/-- `1/max(y,1) ≤ 1/B` for `y ≥ B`. -/
theorem rOne_le_invB_ac (C : NormCtx) {y : Real} (hy : Rle (ofQ (canonB C) (canonB_den C)) y) :
    Rle (rOne y) (ofQ (canonC C) (canonC_den C)) :=
  Rinv_le_ofQ_inv (canonB_num C) (canonB_den C) (qClampQ_witness (⟨1, 1⟩ : Q) (by decide) (by decide) y)
    (Rle_trans hy (Rle_self_qClampQ (⟨1, 1⟩ : Q) (by decide) y))

/-- `(a + w)·(1/B) ≤ a` (from `a + w ≤ B·a`, `hband_hi`). -/
theorem aw_invB_le_a (C : NormCtx) : Qle (mul (add C.a C.w) (canonC C)) C.a := by
  have h := C.hband_hi
  simp only [Qle, mul, add, canonC, canonB, Qinv] at h ⊢
  push_cast at h ⊢
  rw [Int.toNat_of_nonneg (show (0 : Int) ≤ ((C.X : Nat) : Int) + 1 by omega)]
  have e1 : (C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int)) * 1 * (C.a.den : Int)
      = (C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int)) * (1 * (C.a.den : Int)) := by ring_uor
  have e2 : (((C.X : Nat) : Int) + 1) * C.a.num * ((C.a.den : Int) * (C.w.den : Int))
      = C.a.num * ((C.a.den : Int) * (C.w.den : Int) * (((C.X : Nat) : Int) + 1)) := by ring_uor
  rw [e1, ← e2]; exact h

/-- **`R_H(x) = 0` for `x ≥ B`**: the mate `t̄/x̄ ≤ (a+w)/B ≤ a` lies below the window floor. -/
theorem RH_zero_beyond_B (C : NormCtx) (h : CField) (hp : AnchorProfile C h) {x : Real}
    (hx : Rle (ofQ (canonB C) (canonB_den C)) x) : Req (RH C h x) zero := by
  unfold RH
  refine intT_zero_pt C _ x (fun t => ?_)
  rw [RHF_F, shiftUF_F]
  have hxB : Rle (ofQ (canonB C) (canonB_den C)) (xcl C x) :=
    band_ge_of_ge (⟨1, 1⟩ : Q) (canonB C) (by decide) (canonB_den C) (canonB_den C) hx (Qle_refl _)
  have hr : Rle (rOne (xcl C x)) (ofQ (canonC C) (canonC_den C)) := rOne_le_invB_ac C hxB
  have hta : Rnonneg (tBand C t) :=
    Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ C.had (Int.le_of_lt C.han))) (tBand_ge_a C t))
  have hmate : Rle (Rmul (tBand C t) (rOne (xcl C x))) (ofQ C.a C.had) := by
    refine Rle_trans (Rmul_le_Rmul_both hta (Rnonneg_ofQ (canonC_den C) (Int.le_of_lt (canonC_num C))) (tBand_le C t) hr) ?_
    exact Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ _ _)) (Rle_ofQ_ofQ _ _ (aw_invB_le_a C))
  have h0 : Req (h.F one (Rmul (tBand C t) (rOne (xcl C x)))) zero := hp.zero_low one _ hmate
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Rmul_congr (Req_refl _) h0) (Req_refl _))) ?_
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Rzero_mul_ch _))) (Rmul_zero _)

-- ===========================================================================
-- (5) The support of the fiber mask (precision repair of the AC-29 prose).
-- ===========================================================================

/-- `x̄ ≤ λ(t)` ⟹ `maskF = 0` (the lower ramp vanishes). -/
theorem maskF_zero_of_le_lam (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real)
    (hx : Rle (xcl C x) ((lamF C k m).F x t)) : Req ((maskF C k m hw0).F x t) zero := by
  rw [maskF_F]
  refine Req_trans (Rmul_congr (ramp_eq_zero_of_le ?_) (Req_refl _)) (Rzero_mul_ch _)
  have hs : Rle (Rsub (xcl C x) ((lamF C k m).F x t)) zero :=
    Rle_trans (Radd_le_add hx (Rle_refl _)) (Rle_of_Req (Radd_neg _))
  exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) hs) (Rle_of_Req (Rmul_zero _))

/-- `μ(t) ≤ x̄` ⟹ `maskF = 0` (the upper ramp vanishes). -/
theorem maskF_zero_of_ge_mu (C : NormCtx) (k m : Nat) (hw0 : 0 < C.w.num) (x t : Real)
    (hx : Rle ((muF C k m).F x t) (xcl C x)) : Req ((maskF C k m hw0).F x t) zero := by
  rw [maskF_F]
  refine Req_trans (Rmul_congr (Req_refl _) (ramp_eq_zero_of_le ?_)) (Rmul_zero _)
  have hs : Rle (Rsub ((muF C k m).F x t) (xcl C x)) zero :=
    Rle_trans (Radd_le_add hx (Rle_refl _)) (Rle_of_Req (Radd_neg _))
  exact Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ _ (invEtaQ_num C)) hs) (Rle_of_Req (Rmul_zero _))


-- ===========================================================================
-- (6) The regularity energy: the pointwise bound `|R_H(x) − N_H/x̄| ≤ Reg·(x̄ − 1)`.
-- ===========================================================================

theorem rOne_le_one_ac (x : Real) : Rle (rOne x) one :=
  Rle_trans (Rle_of_Rabs_le (rOne_bd x)) (Rle_of_Req (ofQ_congr (Qinv_den_pos (by decide)) (by decide) (by decide)))

theorem dist_one_le_innerXm_ac (x : Real) : Rle (Rsub x one) (innerXm x) :=
  Radd_le_add (Rle_refl x) (Rle_Rneg (rOne_le_one_ac x))

/-- `K(x)·(x − 1) ≤ 1` for every floor `c` and every `x` (`x − 1 ≤ x − 1/max(x,1) ≤ max(·, c)`). -/
theorem Kfl_mul_dist_le_one_ac (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) :
    Rle (Rmul (Kfl c hcn hcd x) (Rsub x one)) one := by
  have hK : Rnonneg (Kfl c hcn hcd x) := Rnonneg_clampedInv c hcn hcd _
  have hle : Rle (Rsub x one) (qClampQ c hcd (innerXm x)) :=
    Rle_trans (dist_one_le_innerXm_ac x) (Rle_self_qClampQ c hcd _)
  refine Rle_trans (Rmul_le_Rmul_left hK hle) (Rle_of_Req ?_)
  show Req (Rmul (clampedInv c hcn hcd (innerXm x)) (qClampQ c hcd (innerXm x))) one
  exact Req_trans (Rmul_comm _ _) (qClampQ_mul_clampedInv c hcn hcd (innerXm x))

theorem add_mul_ac (a b d : Real) : Req (Rmul (Radd a b) d) (Radd (Rmul a d) (Rmul b d)) :=
  Req_trans (Rmul_comm _ _) (Req_trans (Rmul_distrib _ _ _) (Radd_congr (Rmul_comm _ _) (Rmul_comm _ _)))

/-- `(p − q) + (q − u) = p − u`. -/
theorem sub_add_sub_ac (p q u : Real) : Req (Radd (Rsub p q) (Rsub q u)) (Rsub p u) := by
  refine Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl p) ?_)
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  refine Req_trans (Radd_congr (Req_trans (Radd_comm _ _) (Radd_neg q)) (Req_refl _)) ?_
  exact Req_trans (Radd_comm _ _) (Radd_zero _)

/-- The modulus `L_√ + 1` of `y ↦ y^{-1/2} − 1/max(y,1)` at `y = 1`. -/
def sqOneL (C : NormCtx) : Q := add (invSqL C) (⟨1, 1⟩ : Q)
theorem sqOneL_den (C : NormCtx) : 0 < (sqOneL C).den := add_den_pos (invSqL_den C) Nat.one_pos
theorem sqOneL_num (C : NormCtx) : 0 ≤ (sqOneL C).num := Qadd_num_nonneg_loc (invSqL_num C) (by decide)

/-- `|1/max(y,1) − 1| ≤ |y − 1|`. -/
theorem rOne_sub_one_le (y : Real) : Rle (Rabs (Rsub (rOne y) one)) (Rabs (Rsub y one)) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_refl _) (Req_symm rOne_one)))) ?_
  refine Rle_trans (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide) y one) ?_
  exact Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs _) (Rle_of_Req (ofQ_congr _ Nat.one_pos (by decide)))) (Rle_of_Req (Rone_mul _))

/-- `|y^{-1/2} − 1/max(y,1)| ≤ (L_√ + 1)·|y − 1|`. -/
theorem invSq_sub_rOne_le (C : NormCtx) (y : Real) :
    Rle (Rabs (Rsub (invSq C y) (rOne y))) (Rmul (ofQ (sqOneL C) (sqOneL_den C)) (Rabs (Rsub y one))) := by
  have h1 : Rle (Rabs (Rsub (invSq C y) one)) (Rmul (ofQ (invSqL C) (invSqL_den C)) (Rabs (Rsub y one))) :=
    Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_refl _) (Req_symm (invSq_one C))))) (invSq_lip C y one)
  have h2 : Rle (Rabs (Rsub one (rOne y))) (Rabs (Rsub y one)) :=
    Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (rOne_sub_one_le y)
  refine Rle_trans (abs_sub_tri _ one _) (Rle_trans (Radd_le_add h1 h2) (Rle_of_Req ?_))
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Rone_mul _))) ?_
  refine Req_trans (Req_symm (add_mul_ac _ _ _)) (Rmul_congr ?_ (Req_refl _))
  exact Radd_ofQ_ofQ _ _

/-- On the Haar window, `|t̄·(1/max(y,1)) − t| ≤ (a + w)·|y − 1|`. -/
theorem shift_arg_dist_ac (C : NormCtx) {t : Real} (ht : InWin C t) (y : Real) :
    Rle (Rabs (Rsub (Rmul (tBand C t) (rOne y)) t)) (Rmul (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) (Rabs (Rsub y one))) := by
  have htb : Req (tBand C t) t := tBand_eq_of_win C ht.1 ht.2
  have e : Req (Rsub (Rmul (tBand C t) (rOne y)) t) (Rmul t (Rsub (rOne y) one)) :=
    Req_trans (Rsub_congr (Rmul_congr htb (Req_refl _)) (Req_symm (Rmul_one t))) (Req_symm (Rmul_sub_distrib _ _ _))
  refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr e) (Rabs_Rmul _ _))) ?_
  have hta : Rle (Rabs t) (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) :=
    Rabs_le_of_nonneg_le (add_den_pos C.had C.hw) (Qadd_num_nonneg_loc (Int.le_of_lt C.han) C.hwn)
      (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg (Rnonneg_ofQ C.had (Int.le_of_lt C.han))) ht.1)) ht.2
  exact Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rabs _) hta (rOne_sub_one_le y)

/-- The regularity modulus of the anchor `K₁ = (L_√ + 1)·M_h + (a + w)·L_h`. -/
def kOneQ (C : NormCtx) (h : CField) : Q := add (mul (sqOneL C) h.M) (mul (add C.a C.w) h.Lt)
theorem kOneQ_den (C : NormCtx) (h : CField) : 0 < (kOneQ C h).den :=
  add_den_pos (Qmul_den_pos (sqOneL_den C) h.hMd) (Qmul_den_pos (add_den_pos C.had C.hw) h.hLtd)
theorem kOneQ_num (C : NormCtx) (h : CField) : 0 ≤ (kOneQ C h).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (sqOneL_num C) h.hMn)
    (Qmul_num_nonneg (Qadd_num_nonneg_loc (Int.le_of_lt C.han) C.hwn) h.hLtn)

/-- `s·A − r·B = (s − r)·A + r·(A − B)`. -/
theorem shift_diff_split_ac (s r A B : Real) :
    Req (Rsub (Rmul s A) (Rmul r B)) (Radd (Rmul (Rsub s r) A) (Rmul r (Rsub A B))) :=
  Req_symm (Req_trans (Radd_congr (Rmul_sub_distrib_right _ _ _) (Rmul_sub_distrib _ _ _)) (sub_add_sub_ac _ _ _))

/-- **The shift defect of an anchor profile**: `|x̄^{-1/2}·H(t̄/x̄) − H(t)/x̄| ≤ K₁·|x̄ − 1|` on the Haar window. -/
theorem anchor_shift_diff_le (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (x : Real) {t : Real} (ht : InWin C t) :
    Rle (Rabs (Rsub ((shiftUF C h).F x t) (Rmul (rOne (xcl C x)) (h.F x t))))
        (Rmul (ofQ (kOneQ C h) (kOneQ_den C h)) (Rabs (Rsub (xcl C x) one))) := by
  rw [shiftUF_F]
  refine Rle_trans (Rle_of_Req (Rabs_congr (shift_diff_split_ac _ _ _ _))) ?_
  refine Rle_trans (Rabs_Radd _ _) ?_
  have hA : Rle (Rabs (h.F one (Rmul (tBand C t) (rOne (xcl C x))))) (ofQ h.M h.hMd) := h.hbd _ _
  have h1 : Rle (Rabs (Rmul (Rsub (invSq C (xcl C x)) (rOne (xcl C x))) (h.F one (Rmul (tBand C t) (rOne (xcl C x))))))
      (Rmul (Rmul (ofQ (sqOneL C) (sqOneL_den C)) (Rabs (Rsub (xcl C x) one))) (ofQ h.M h.hMd)) :=
    Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ h.hMn) (invSq_sub_rOne_le C _) hA)
  have hAB : Rle (Rabs (Rsub (h.F one (Rmul (tBand C t) (rOne (xcl C x)))) (h.F x t)))
      (Rmul (ofQ h.Lt h.hLtd) (Rmul (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) (Rabs (Rsub (xcl C x) one)))) := by
    refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_refl _) (hp.scale_const x one t)))) ?_
    refine Rle_trans (h.hlipt one _ _) (Rmul_le_Rmul_left (Rnonneg_ofQ _ h.hLtn) ?_)
    exact shift_arg_dist_ac C ht _
  have h2 : Rle (Rabs (Rmul (rOne (xcl C x)) (Rsub (h.F one (Rmul (tBand C t) (rOne (xcl C x)))) (h.F x t))))
      (Rmul one (Rmul (ofQ h.Lt h.hLtd) (Rmul (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) (Rabs (Rsub (xcl C x) one))))) :=
    Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) (Rmul_le_Rmul_both (Rnonneg_Rabs _)
      (Rnonneg_Rmul (Rnonneg_ofQ _ h.hLtn) (Rnonneg_Rmul (Rnonneg_ofQ _ (Qadd_num_nonneg_loc (Int.le_of_lt C.han) C.hwn)) (Rnonneg_Rabs _)))
      (Rle_trans (Rle_of_Rabs_le (rOne_bd _)) (Rle_of_Req (ofQ_congr _ Nat.one_pos (by decide)))) hAB)
  refine Rle_trans (Radd_le_add h1 h2) (Rle_of_Req ?_)
  -- (L₁·d)·M + 1·(Lt·((a+w)·d)) = ((L₁·M) + ((a+w)·Lt))·d
  have e1 : Req (Rmul (Rmul (ofQ (sqOneL C) (sqOneL_den C)) (Rabs (Rsub (xcl C x) one))) (ofQ h.M h.hMd))
      (Rmul (ofQ (mul (sqOneL C) h.M) (Qmul_den_pos (sqOneL_den C) h.hMd)) (Rabs (Rsub (xcl C x) one))) :=
    Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _))
      (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ _ _) (Req_refl _))))
  have e2 : Req (Rmul one (Rmul (ofQ h.Lt h.hLtd) (Rmul (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) (Rabs (Rsub (xcl C x) one)))))
      (Rmul (ofQ (mul (add C.a C.w) h.Lt) (Qmul_den_pos (add_den_pos C.had C.hw) h.hLtd)) (Rabs (Rsub (xcl C x) one))) :=
    Req_trans (Rone_mul _) (Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Rmul_congr (Req_trans (Rmul_comm _ _) (Rmul_ofQ_ofQ _ _)) (Req_refl _)))
  refine Req_trans (Radd_congr e1 e2) ?_
  exact Req_trans (Req_symm (add_mul_ac _ _ _)) (Rmul_congr (Radd_ofQ_ofQ _ _) (Req_refl _))

/-- The integrand of `R_H(x) − N_H/x̄`. -/
def edgeIntF (C : NormCtx) (h : CField) : CField := subF (RHF C h) (mulF (rOneClF C) (NHF C h))

/-- `∫ edgeIntF(x,·) = R_H(x) − N_H/x̄` for an anchor profile. -/
theorem edgeInt_eq (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (x : Real) :
    Req (intT C (edgeIntF C h) x) (Rsub (RH C h x) (Rmul (rOne (xcl C x)) (NH C h))) := by
  refine Req_trans (intT_sub_pt C (RHF C h) (mulF (rOneClF C) (NHF C h)) _ x (fun t => Req_refl _)) ?_
  refine Rsub_congr (Req_refl _) ?_
  refine Req_trans (intT_smul_pt C _ (NHF C h) x (rOne (xcl C x)) (fun t => Req_refl _)) ?_
  exact Rmul_congr (Req_refl _) (intT_congr_scale C _ _ x one (fun t =>
    Rmul_congr (Req_refl _) (Rmul_congr (hp.scale_const x one t) (hp.scale_const x one t))))

/-- `W·(S·B) − r·(W·(B·B)) = W·(B·(S − r·B))`. -/
theorem edge_pt_alg (W S B r : Real) :
    Req (Rsub (Rmul W (Rmul S B)) (Rmul r (Rmul W (Rmul B B)))) (Rmul W (Rmul B (Rsub S (Rmul r B)))) := by
  refine Req_symm ?_
  refine Req_trans (Rmul_congr (Req_refl W) (Rmul_sub_distrib _ _ _)) (Req_trans (Rmul_sub_distrib _ _ _) (Rsub_congr ?_ ?_))
  · exact Rmul_congr (Req_refl _) (Rmul_comm _ _)
  · -- W·(B·(r·B)) = r·(W·(B·B))
    refine Req_trans (Rmul_congr (Req_refl W) (Req_trans (Req_symm (Rmul_assoc _ _ _))
      (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))) ?_
    exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- **The regularity energy** `Reg_H = (w/a)·M_h·K₁` — from the source bound and Lipschitz constant of the anchor. -/
def regQ (C : NormCtx) (h : CField) : Q := mul (mul (mul C.w (Qinv C.a)) h.M) (kOneQ C h)
theorem regQ_den (C : NormCtx) (h : CField) : 0 < (regQ C h).den :=
  Qmul_den_pos (Qmul_den_pos (Qmul_den_pos C.hw (Qinv_den_pos C.han)) h.hMd) (kOneQ_den C h)
theorem regQ_num (C : NormCtx) (h : CField) : 0 ≤ (regQ C h).num :=
  Qmul_num_nonneg (Qmul_num_nonneg (Qmul_num_nonneg C.hwn (Int.le_of_lt (Qinv_num_pos C.had))) h.hMn) (kOneQ_num C h)

/-- `|w·r(t)| ≤ w/a`. -/
theorem wr_abs_le_ac (C : NormCtx) (t : Real) :
    Rle (Rabs (Rmul (ofQ C.w C.hw) (rEv C t))) (ofQ (mul C.w (Qinv C.a)) (Qmul_den_pos C.hw (Qinv_den_pos C.han))) := by
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ (Int.le_of_lt (Qinv_num_pos C.had)))
    (Rle_of_Req (Rabs_ofQ_nonneg C.hw C.hwn)) (Rle_trans (Rle_of_Req (Rabs_of_nonneg (rEv_nonneg C t))) (rEv_le_inv_a C t))) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ _ _)

/-- **The pointwise regularity bound** `|edgeIntF(x, t)| ≤ Reg_H·|x̄ − 1|` on the Haar window. -/
theorem edgeInt_abs_le (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (x : Real) {t : Real} (ht : InWin C t) :
    Rle (Rabs ((edgeIntF C h).F x t)) (Rmul (ofQ (regQ C h) (regQ_den C h)) (Rabs (Rsub (xcl C x) one))) := by
  show Rle (Rabs (Rsub (Rmul (Rmul (ofQ C.w C.hw) (rEv C t)) (Rmul ((shiftUF C h).F x t) (h.F x t)))
    (Rmul (rOne (xcl C x)) (Rmul (Rmul (ofQ C.w C.hw) (rEv C t)) (Rmul (h.F x t) (h.F x t)))))) _
  refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (edge_pt_alg _ _ _ _)) (Req_trans (Rabs_Rmul _ _)
    (Rmul_congr (Req_refl _) (Rabs_Rmul _ _))))) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ _ h.hMn)
      (Rnonneg_Rmul (Rnonneg_ofQ _ (kOneQ_num C h)) (Rnonneg_Rabs _))) (wr_abs_le_ac C t)
    (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ _ (kOneQ_num C h)) (Rnonneg_Rabs _)) (h.hbd x t)
      (anchor_shift_diff_le C h hp x ht))) (Rle_of_Req ?_)
  -- (w/a)·(M·(K₁·d)) = ((w/a·M)·K₁)·d
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _)))
  exact Req_trans (Rmul_congr (Rmul_ofQ_ofQ _ _) (Req_refl _)) (Rmul_ofQ_ofQ _ _)

/-- **`|R_H(x) − N_H/x̄| ≤ Reg_H·(x̄ − 1)`** for every anchor profile and every scale `x`. -/
theorem RH_sub_NH_abs_le (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (x : Real) :
    Rle (Rabs (Rsub (RH C h x) (Rmul (rOne (xcl C x)) (NH C h)))) (Rmul (ofQ (regQ C h) (regQ_den C h)) (Rsub (xcl C x) one)) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (edgeInt_eq C h hp x)))) ?_
  refine Rle_trans (riemannIntegral_abs_le_unit_real _ _ _ _ _ (fun y hy0 hy1 => edgeInt_abs_le C h hp x (inWin_of_affine C y hy0 hy1))) ?_
  exact Rle_of_Req (Rmul_congr (Req_refl _) (Rabs_of_nonneg (Rnonneg_Rsub_of_Rle (xcl_ge_one C x))))

/-- **The uniform bound of the tail integrand** `|2K_k(x̄)·(R_H(x) − N_H/x̄)| ≤ 2·Reg_H` at every scale and every floor. -/
theorem tailACF_abs_le (C : NormCtx) (k : Nat) (h : CField) (hp : AnchorProfile C h) (x : Real) :
    Rle (Rabs ((tailACF C k h).F x one)) (Rmul cTwo (ofQ (regQ C h) (regQ_den C h))) := by
  rw [tailACF_F]
  have hK : Rnonneg (Kx C k x) := Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ _ (regQ_num C h)) (Rnonneg_Rsub_of_Rle (xcl_ge_one C x)))
    (Rle_of_Req (Req_trans (Rabs_Rmul _ _) (Rmul_congr (Rabs_ofQ_nonneg Nat.one_pos (by decide)) (Rabs_of_nonneg hK))))
    (RH_sub_NH_abs_le C h hp x)) ?_
  -- (2·K)·(Reg·(x̄−1)) = (2·Reg)·(K·(x̄−1)) ≤ (2·Reg)·1
  refine Rle_trans (Rle_of_Req (mul4_swap_ch _ _ _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_Rmul (Rnonneg_ofQ _ (by decide)) (Rnonneg_ofQ _ (regQ_num C h)))
    (Kfl_mul_dist_le_one_ac (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x))) (Rle_of_Req (Rmul_one _))


-- ===========================================================================
-- (7) The edge estimate `|AK_{k'} − AK_k| ≤ 2^{1−k}·Reg_H` (`1 ≤ k ≤ k'`, same far mass).
-- ===========================================================================

theorem dyQ_add_le_ac (k d : Nat) : Qle (dyQ (k + d)) (dyQ k) := by
  show (1 : Int) * ((2 ^ k : Nat) : Int) ≤ 1 * ((2 ^ (k + d) : Nat) : Int)
  have h : 2 ^ k ≤ 2 ^ (k + d) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right k d)
  have h' := Int.ofNat_le.mpr h
  omega

theorem dyQ_sub_num_pos_ac (k d : Nat) (hd : 1 ≤ d) : 0 < (Qsub (dyQ k) (dyQ (k + d))).num := by
  show (0 : Int) < 1 * ((2 ^ (k + d) : Nat) : Int) + (-1) * ((2 ^ k : Nat) : Int)
  have h : 2 ^ k < 2 ^ (k + d) :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_succ (by decide)) (Nat.pow_le_pow_right (by decide) (by omega : k + 1 ≤ k + d))
  have h' := Int.ofNat_lt.mpr h
  omega

theorem dyQ_sub_le_ac (k d : Nat) : Qle (Qsub (dyQ k) (dyQ (k + d))) (dyQ k) := by
  show (1 * ((2 ^ (k + d) : Nat) : Int) + (-1) * ((2 ^ k : Nat) : Int)) * ((2 ^ k : Nat) : Int)
    ≤ 1 * ((2 ^ k * 2 ^ (k + d) : Nat) : Int)
  push_cast
  have hP : (0 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast Nat.zero_le _
  generalize hPe : ((2 : Int) ^ k) = P at hP ⊢
  generalize ((2 : Int) ^ (k + d)) = Q
  have e : (1 * Q + (-1) * P) * P = P * Q - P * P := by ring_uor
  have e2 : (1 : Int) * (P * Q) = P * Q := by ring_uor
  rw [e, e2]
  exact Int.sub_le_self _ (Int.mul_nonneg hP hP)

/-- The floors `2^{-(k+d)} ≤ 2^{-k}` are both inert at `x̄` once `x̄ − 1 ≥ 2^{-k}`. -/
theorem Kx_inert_ac (C : NormCtx) (k d : Nat) (x : Real) (hx : Rle (ofQ (dyQ k) (dyQ_den k)) (Rsub (xcl C x) one)) :
    Req (Kx C (k + d) x) (Kx C k x) := by
  have hge : Rle (ofQ (dyQ k) (dyQ_den k)) (innerXm (xcl C x)) := Rle_trans hx (dist_one_le_innerXm_ac _)
  have hge' : Rle (ofQ (dyQ (k + d)) (dyQ_den (k + d))) (innerXm (xcl C x)) :=
    Rle_trans (Rle_ofQ_ofQ (dyQ_den (k + d)) (dyQ_den k) (dyQ_add_le_ac k d)) hge
  obtain ⟨ki, hki⟩ := Pos_of_Rle_ofQ (dyQ_num k) (dyQ_den k) hge
  show Req (clampedInv (dyQ (k + d)) (dyQ_num (k + d)) (dyQ_den (k + d)) (innerXm (xcl C x)))
    (clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (innerXm (xcl C x)))
  exact Req_trans (clampedInv_eq_of_ge (a := dyQ (k + d)) (han := dyQ_num (k + d)) (had := dyQ_den (k + d)) hki hge')
    (Req_symm (clampedInv_eq_of_ge (a := dyQ k) (han := dyQ_num k) (had := dyQ_den k) hki hge))

theorem sub_one_of_one_add_ac (d : Real) : Req (Rsub (Radd one d) one) d :=
  Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _))
    (Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _)))

/-- On the tail window `[1 + 2^{-k}, B]`: `x̄ − 1 ≥ 2^{-k}`. -/
theorem tail_window_dist (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (s : Real) (hs0 : Rle zero s) (hs1 : Rle s one) :
    Rle (ofQ (dyQ k) (dyQ_den k))
        (Rsub (xcl C (affineMap (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) s)) one) := by
  have hx1 : Rle one _ := Rle_trans (Rle_ofQ_ofQ (by decide) (tailLo_den k) (one_le_tailLo k)) (affine_tail_ge_lo C k hk s hs0)
  have hxB := affine_tail_le_B C k hk s hs1
  have hxcl := xcl_eq_of_band C hx1 hxB
  have hlo : Rle (Radd one (ofQ (dyQ k) (dyQ_den k))) (xcl C _) :=
    Rle_trans (Rle_of_Req (Radd_ofQ_ofQ Nat.one_pos (dyQ_den k))) (Rle_trans (affine_tail_ge_lo C k hk s hs0) (Rle_of_Req (Req_symm hxcl)))
  exact Rle_trans (Rle_of_Req (Req_symm (sub_one_of_one_add_ac _))) (Radd_le_add hlo (Rle_refl _))

/-- The split width `2^{-k} − 2^{-(k+d)}`. -/
def edgeW (k d : Nat) : Q := Qsub (dyQ k) (dyQ (k + d))
theorem edgeW_den (k d : Nat) : 0 < (edgeW k d).den := Qsub_den_pos (dyQ_den k) (dyQ_den (k + d))

/-- `edgeW + tailGap_k = tailGap_{k+d}` (rationally). -/
theorem edgeW_add_tailGap (C : NormCtx) (k d : Nat) : Qeq (add (edgeW k d) (tailGap C k)) (tailGap C (k + d)) := by
  unfold edgeW tailGap Qsub canonB dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  generalize (2 : Int) ^ (k + d) = q
  ring_uor

/-- `tailLo_{k+d} + edgeW = tailLo_k` (rationally). -/
theorem tailLo_add_edgeW (k d : Nat) : Qeq (add (tailLo (k + d)) (edgeW k d)) (tailLo k) := by
  unfold edgeW tailLo Qsub dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  generalize (2 : Int) ^ (k + d) = q
  ring_uor

/-- `tailGap_{k+d} − edgeW = tailGap_k` (rationally). -/
theorem tailGap_sub_edgeW (C : NormCtx) (k d : Nat) : Qeq (Qsub (tailGap C (k + d)) (edgeW k d)) (tailGap C k) := by
  unfold edgeW tailGap Qsub canonB dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  generalize (2 : Int) ^ (k + d) = q
  ring_uor

theorem num_nonneg_of_Qeq {a b : Q} (hbd : 0 < b.den) (h : Qeq a b) (hn : 0 ≤ b.num) : 0 ≤ a.num := by
  unfold Qeq at h
  have h1 : 0 ≤ a.num * (b.den : Int) := by rw [h]; exact Int.mul_nonneg hn (Int.ofNat_nonneg _)
  have h2 : (0 : Int) * (b.den : Int) ≤ a.num * (b.den : Int) := by rw [Int.zero_mul]; exact h1
  exact Int.le_of_mul_le_mul_right h2 (by exact_mod_cast hbd)

theorem edgeW_le_tailGap (C : NormCtx) (k d : Nat) (hk : 1 ≤ k) : Qle (edgeW k d) (tailGap C (k + d)) :=
  Qle_congr_right (add_den_pos (edgeW_den k d) (tailGap_den C k)) (edgeW_add_tailGap C k d)
    (Qle_add_right_nonneg (tailGap_num_nonneg C k hk))

theorem tailGap_sub_edgeW_num (C : NormCtx) (k d : Nat) (hk : 1 ≤ k) : 0 ≤ (Qsub (tailGap C (k + d)) (edgeW k d)).num :=
  num_nonneg_of_Qeq (tailGap_den C k) (tailGap_sub_edgeW C k d) (tailGap_num_nonneg C k hk)

/-- **The edge piece** `2∫_{1+2^{-(k+d)}}^{1+2^{-k}} K_{k+d}(x̄)·(R_H(x) − N_H/x̄) dx`. -/
def edgePiece (C : NormCtx) (k d : Nat) (hd : 1 ≤ d) (h : CField) : Real :=
  xInt (tailACF C (k + d) h) (tailLo (k + d)) (edgeW k d) (tailLo_den (k + d)) (edgeW_den k d)
    (Int.le_of_lt (dyQ_sub_num_pos_ac k d hd)) one

/-- **The tail split** `tailAC_{k+d} = edgePiece + tailAC_k` (`k ≥ 1`, `d ≥ 1`). -/
theorem tailAC_split (C : NormCtx) (k d : Nat) (hk : 1 ≤ k) (hd : 1 ≤ d) (h : CField) :
    Req (tailAC C (k + d) (Nat.le_trans hk (Nat.le_add_right k d)) h) (Radd (edgePiece C k d hd h) (tailAC C k hk h)) := by
  unfold tailAC edgePiece xInt
  refine Req_trans (riemannIntegralI_split_at _ _ _ _ (tailLo (k + d)) (tailGap C (k + d)) (edgeW k d) (tailLo_den (k + d))
    (tailGap_den C (k + d)) (tailGap_num_nonneg C (k + d) (Nat.le_trans hk (Nat.le_add_right k d))) (edgeW_den k d)
    (dyQ_sub_num_pos_ac k d hd) (edgeW_le_tailGap C k d hk) (tailGap_sub_edgeW_num C k d hk)) ?_
  refine Radd_congr (Req_refl _) ?_
  refine Req_trans (riemannIntegralI_congr_Q _ _ _ _ _ _ (tailLo k) (tailGap C k) _ _ _ (tailLo_den k) (tailGap_den C k)
    (tailGap_num_nonneg C k hk) (tailLo_add_edgeW k d) (tailGap_sub_edgeW C k d)) ?_
  refine intI_congr_unit_free _ _ _ _ _ _ _ _ (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
    (fun s hs0 hs1 => ?_)
  rw [tailACF_F, tailACF_F]
  exact Rmul_congr (Rmul_congr (Req_refl _) (Kx_inert_ac C k d _ (tail_window_dist C k hk s hs0 hs1))) (Req_refl _)

/-- **The edge bound** `2^{1−k}·Reg_H = 2^{-k}·(2·Reg_H)` — test-independent coefficient `2^{1−k}`. -/
def edgeBound (C : NormCtx) (k : Nat) (h : CField) : Q := mul (dyQ k) (mul (⟨2, 1⟩ : Q) (regQ C h))
theorem edgeBound_den (C : NormCtx) (k : Nat) (h : CField) : 0 < (edgeBound C k h).den :=
  Qmul_den_pos (dyQ_den k) (Qmul_den_pos Nat.one_pos (regQ_den C h))
theorem edgeBound_num (C : NormCtx) (k : Nat) (h : CField) : 0 ≤ (edgeBound C k h).num :=
  Qmul_num_nonneg (Int.le_of_lt (dyQ_num k)) (Qmul_num_nonneg (by decide) (regQ_num C h))

/-- `|edgePiece| ≤ 2^{-k}·(2·Reg_H)`. -/
theorem edgePiece_abs_le (C : NormCtx) (k d : Nat) (hd : 1 ≤ d) (h : CField) (hp : AnchorProfile C h) :
    Rle (Rabs (edgePiece C k d hd h)) (ofQ (edgeBound C k h) (edgeBound_den C k h)) := by
  unfold edgePiece xInt
  refine Rle_trans (riemannIntegralI_abs_le_window_real _ _ _ _ (tailLo (k + d)) (edgeW k d) (Rmul cTwo (ofQ (regQ C h) (regQ_den C h)))
    (tailLo_den (k + d)) (edgeW_den k d) (Int.le_of_lt (dyQ_sub_num_pos_ac k d hd)) (fun s _ _ => tailACF_abs_le C (k + d) h hp _)) ?_
  refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rmul (Rnonneg_ofQ _ (by decide)) (Rnonneg_ofQ _ (regQ_num C h)))
    (Rle_ofQ_ofQ (edgeW_den k d) (dyQ_den k) (dyQ_sub_le_ac k d))) ?_
  exact Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _))

/-- `((P + T') + F) − ((P + T) + F) = T' − T`. -/
theorem add_cancel_ac (P T T' F : Real) : Req (Rsub (Radd (Radd P T') F) (Radd (Radd P T) F)) (Rsub T' T) := by
  refine Req_trans (Req_symm (add_sub_add_c5 _ _ _ _)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_neg F)) (Req_trans (Radd_zero _) ?_)
  refine Req_trans (Req_symm (add_sub_add_c5 _ _ _ _)) ?_
  exact Req_trans (Radd_congr (Radd_neg P) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

/-- **The level difference is the edge piece**: `AK_{k+d} − AK_k = edgePiece` (same `fc`). -/
theorem anchorKernel5_diff_edge (C : NormCtx) (k d : Nat) (hk : 1 ≤ k) (hd : 1 ≤ d) (fc : Real) (h : CField) (hp : AnchorProfile C h) :
    Req (Rsub (anchorKernel5 C (k + d) (Nat.le_trans hk (Nat.le_add_right k d)) fc h) (anchorKernel5 C k hk fc h))
        (edgePiece C k d hd h) := by
  refine Req_trans (Rsub_congr (anchorKernel5_autocorr C (k + d) _ fc h hp) (anchorKernel5_autocorr C k hk fc h hp)) ?_
  refine Req_trans (add_cancel_ac _ _ _ _) ?_
  refine Req_trans (Rsub_congr (tailAC_split C k d hk hd h) (Req_refl _)) ?_
  -- (E + T) − T = E
  refine Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _))

/-- **★ THE EDGE ESTIMATE** `|AK_{k'} − AK_k| ≤ 2^{1−k}·Reg_H` for `1 ≤ k ≤ k'` (same far mass `fc`). -/
theorem anchorKernel5_edge_abs (C : NormCtx) {k k' : Nat} (hk : 1 ≤ k) (hk' : 1 ≤ k') (hkk : k ≤ k') (fc : Real) (h : CField)
    (hp : AnchorProfile C h) :
    Rle (Rabs (Rsub (anchorKernel5 C k' hk' fc h) (anchorKernel5 C k hk fc h))) (ofQ (edgeBound C k h) (edgeBound_den C k h)) := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  cases d with
  | zero =>
    exact Rle_trans (Rle_of_Req (Req_trans (Rabs_congr (Radd_neg _)) Rabs_zero))
      (Rle_zero_of_Rnonneg (Rnonneg_ofQ _ (edgeBound_num C k h)))
  | succ d' =>
    refine Rle_trans (Rle_of_Req (Rabs_congr (anchorKernel5_diff_edge C k (d' + 1) hk (Nat.succ_pos d') fc h hp))) ?_
    exact edgePiece_abs_le C k (d' + 1) (Nat.succ_pos d') h hp

-- ===========================================================================
-- (8) The regularized limit `AK_∞` and the estimate to the limit.
-- ===========================================================================

/-- The integer ceiling of the regularity energy. -/
def regN (C : NormCtx) (h : CField) : Nat := (regQ C h).num.toNat

/-- The schedule `N(j) = j + ⌈Reg⌉ + 1`, so that `2^{1−N(j)}·Reg ≤ 1/(j+1)`. -/
def sched (C : NormCtx) (h : CField) (j : Nat) : Nat := j + regN C h + 1

theorem two_mul_le_two_pow_ac : ∀ r : Nat, 2 * r ≤ 2 ^ r
  | 0 => by decide
  | 1 => by decide
  | (r + 2) => by
    have ih := two_mul_le_two_pow_ac (r + 1)
    have h2 : 2 ≤ 2 ^ (r + 1) := Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.pow_succ]
    omega

/-- `2^{1−N(j)}·Reg ≤ 1/(j+1)`. -/
theorem edgeBound_sched_le (C : NormCtx) (h : CField) (j : Nat) :
    Qle (edgeBound C (sched C h j) h) (⟨1, j + 1⟩ : Q) := by
  have hnum : (regQ C h).num = ((regN C h : Nat) : Int) := (Int.toNat_of_nonneg (regQ_num C h)).symm
  have hden : 1 ≤ (regQ C h).den := regQ_den C h
  unfold edgeBound sched dyQ
  simp only [Qle, mul]
  rw [hnum]
  push_cast
  -- 1·(2·r)·(j+1) ≤ 1·(2^{j+r+1}·(1·den))
  have hN : 2 * regN C h * (j + 1) ≤ 2 ^ (j + regN C h + 1) * (regQ C h).den := by
    have h1 : 2 * regN C h ≤ 2 ^ regN C h := two_mul_le_two_pow_ac _
    have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
    have h3 : 2 * regN C h * (j + 1) ≤ 2 ^ regN C h * 2 ^ j := Nat.mul_le_mul h1 h2
    have h4 : 2 ^ regN C h * 2 ^ j ≤ 2 ^ (j + regN C h + 1) := by
      rw [Nat.pow_succ, Nat.pow_add, Nat.mul_comm (2 ^ j)]
      exact Nat.le_mul_of_pos_right _ (by decide)
    exact Nat.le_trans (Nat.le_trans h3 h4) (Nat.le_mul_of_pos_right _ hden)
  have hN' : ((2 * regN C h * (j + 1) : Nat) : Int) ≤ ((2 ^ (j + regN C h + 1) * (regQ C h).den : Nat) : Int) := Int.ofNat_le.mpr hN
  push_cast at hN'
  simp only [Int.one_mul, Int.mul_one]
  exact hN'

/-- The scheduled kernel sequence `j ↦ AK_{N(j)}`. -/
def akSeq (C : NormCtx) (fc : Real) (h : CField) (j : Nat) : Real :=
  anchorKernel5 C (sched C h j) (Nat.succ_pos _) fc h

theorem akSeq_close (C : NormCtx) (fc : Real) (h : CField) (hp : AnchorProfile C h) (j i : Nat) :
    Rle (Rsub (akSeq C fc h j) (akSeq C fc h i))
        (ofQ (add (⟨1, j + 1⟩ : Q) (⟨1, i + 1⟩ : Q)) (add_den_pos (Nat.succ_pos j) (Nat.succ_pos i))) := by
  rcases Nat.le_total j i with hji | hij
  · -- N(j) ≤ N(i): |X_i − X_j| ≤ edgeBound (N j) ≤ 1/(j+1)
    have hb := anchorKernel5_edge_abs C (k := sched C h j) (k' := sched C h i) (Nat.succ_pos _) (Nat.succ_pos _)
      (by unfold sched; omega) fc h hp
    refine Rle_trans (Rle_Rabs_self _) (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (Rle_trans hb ?_))
    exact Rle_ofQ_ofQ _ _ (Qle_trans (b := (⟨1, j + 1⟩ : Q)) (Nat.succ_pos j) (edgeBound_sched_le C h j)
      (Qle_add_right_nonneg (show (0 : Int) ≤ 1 by decide)))
  · have hb := anchorKernel5_edge_abs C (k := sched C h i) (k' := sched C h j) (Nat.succ_pos _) (Nat.succ_pos _)
      (by unfold sched; omega) fc h hp
    refine Rle_trans (Rle_Rabs_self _) (Rle_trans hb ?_)
    refine Rle_ofQ_ofQ _ _ (Qle_trans (b := (⟨1, i + 1⟩ : Q)) (Nat.succ_pos i) (edgeBound_sched_le C h i) ?_)
    exact Qle_congr_right (add_den_pos (Nat.succ_pos i) (Nat.succ_pos j)) (Qadd_comm (⟨1, i + 1⟩ : Q) (⟨1, j + 1⟩ : Q))
      (Qle_add_right_nonneg (show (0 : Int) ≤ 1 by decide))

/-- The scheduled sequence is regular. -/
theorem akSeq_reg (C : NormCtx) (fc : Real) (h : CField) (hp : AnchorProfile C h) : RReg (akSeq C fc h) :=
  RReg_of_real_bound (akSeq C fc h) (fun j i => add (⟨1, j + 1⟩ : Q) (⟨1, i + 1⟩ : Q))
    (fun j i => add_den_pos (Nat.succ_pos j) (Nat.succ_pos i)) (fun _ _ => Qle_refl _) (akSeq_close C fc h hp)

/-- **★ THE REGULARIZED LIMITING KERNEL** `AK_∞(fc, H) = lim_j AK_{N(j)}(fc, H)` (the lower edge moved to `1`). -/
def anchorKernelLimit (C : NormCtx) (fc : Real) (h : CField) (hp : AnchorProfile C h) : Real :=
  Rlim (akSeq C fc h) (akSeq_reg C fc h hp)

theorem Rle_self_add_ofQ_ac (y : Real) (t : Nat) : Rle y (Radd y (ofQ (⟨1, t + 1⟩ : Q) (Nat.succ_pos t))) :=
  Rle_self_Radd_right (Rnonneg_ofQ (Nat.succ_pos t) (show (0 : Int) ≤ 1 by decide))

/-- For `n ≥ k`: `N(n) ≥ k`. -/
theorem sched_ge (C : NormCtx) (h : CField) {k n : Nat} (hn : k ≤ n) : k ≤ sched C h n := by unfold sched; omega

/-- **★ THE EDGE ESTIMATE TO THE LIMIT** `|AK_k − AK_∞| ≤ 2^{1−k}·Reg_H` for every `k ≥ 1`. -/
theorem anchorKernel5_limit_abs (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (h : CField) (hp : AnchorProfile C h) :
    Rle (Rabs (Rsub (anchorKernel5 C k hk fc h) (anchorKernelLimit C fc h hp))) (ofQ (edgeBound C k h) (edgeBound_den C k h)) := by
  have hX := akSeq_reg C fc h hp
  have hNX : RReg (fun j => Rneg (akSeq C fc h j)) := RReg_neg_core hX
  have hY : RReg (fun j => Radd (anchorKernel5 C k hk fc h) (Rneg (akSeq C fc h j))) := RReg_add_const _ _ hNX
  have hZ : RReg (fun j => Radd (Rneg (anchorKernel5 C k hk fc h)) (akSeq C fc h j)) := RReg_add_const _ _ hX
  have eY : Req (Rlim _ hY) (Rsub (anchorKernel5 C k hk fc h) (anchorKernelLimit C fc h hp)) :=
    Req_trans (Rlim_add_const _ _ hNX hY) (Radd_congr (Req_refl _) (Rlim_neg _ hX hNX))
  have eZ : Req (Rlim _ hZ) (Rneg (Rsub (anchorKernel5 C k hk fc h) (anchorKernelLimit C fc h hp))) := by
    refine Req_trans (Rlim_add_const _ _ hX hZ) ?_
    exact Req_symm (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_refl _) (Rneg_neg _)))
  have hev : ∀ n, k ≤ n → Rle (Rabs (Rsub (akSeq C fc h n) (anchorKernel5 C k hk fc h))) (ofQ (edgeBound C k h) (edgeBound_den C k h)) :=
    fun n hn => anchorKernel5_edge_abs C hk (Nat.succ_pos _) (sched_ge C h hn) fc h hp
  refine Rabs_le_of_both ?_ ?_
  · refine Rle_trans (Rle_of_Req (Req_symm eY)) (Rle_Rlim_ofQ_eventual_core hY _ _ (fun t => ⟨k, fun n hn => ?_⟩))
    refine Rle_trans ?_ (Rle_self_add_ofQ_ac _ t)
    exact Rle_trans (Rle_Rabs_self _) (Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) (hev n hn))
  · refine Rle_trans (Rle_of_Req (Req_symm eZ)) (Rle_Rlim_ofQ_eventual_core hZ _ _ (fun t => ⟨k, fun n hn => ?_⟩))
    refine Rle_trans ?_ (Rle_self_add_ofQ_ac _ t)
    exact Rle_trans (Rle_of_Req (Radd_comm _ _)) (Rle_trans (Rle_Rabs_self _) (hev n hn))

/-- **The edge estimate on the fully coherent carrier**: `|crossForm5 z − AK_∞(fc, V̂)| ≤ 2^{1−k}·Reg_{V̂}`. -/
theorem crossForm5_limit_abs (C : NormCtx) (k : Nat) (hw0 : 0 < C.w.num) (hk : 1 ≤ k) (fc : Real) {z : Carrier5}
    (hz : FullSourceCoherent5 C k z) :
    Rle (Rabs (Rsub (crossForm5 C k hw0 hk fc z) (anchorKernelLimit C fc (anchorOf z) (anchorProfile_of_fullCoherent C k hz))))
        (ofQ (edgeBound C k (anchorOf z)) (edgeBound_den C k (anchorOf z))) :=
  Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (crossForm5_eq_anchorKernel C k hw0 hk fc hz) (Req_refl _))))
    (anchorKernel5_limit_abs C k hk fc (anchorOf z) (anchorProfile_of_fullCoherent C k hz))


-- ===========================================================================
-- (9) Narrow windows: the prime term of `AK` vanishes identically when `w < a`.
-- ===========================================================================

/-- `R_H(x) = 0` whenever `a·x̄ ≥ a + w` (the mate `t̄/x̄ ≤ (a+w)/x̄ ≤ a` is below the floor). -/
theorem RH_zero_of_scale_ge (C : NormCtx) (h : CField) (hp : AnchorProfile C h) {x : Real}
    (hx : Rle (ofQ (add C.a C.w) (add_den_pos C.had C.hw)) (Rmul (ofQ C.a C.had) (xcl C x))) : Req (RH C h x) zero := by
  unfold RH
  refine intT_zero_pt C _ x (fun t => ?_)
  rw [RHF_F, shiftUF_F]
  have hr : Rnonneg (rOne (xcl C x)) := Rnonneg_clampedInv _ _ _ _
  have hmate : Rle (Rmul (tBand C t) (rOne (xcl C x))) (ofQ C.a C.had) := by
    refine Rle_trans (Rmul_le_Rmul_right hr (tBand_le C t)) ?_
    refine Rle_trans (Rmul_le_Rmul_right hr hx) (Rle_of_Req ?_)
    exact Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (xcl_mul_rOne_ac C x)) (Rmul_one _))
  have h0 : Req (h.F one (Rmul (tBand C t) (rOne (xcl C x)))) zero := hp.zero_low one _ hmate
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Rmul_congr (Req_refl _) h0) (Req_refl _))) ?_
  exact Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Rzero_mul_ch _))) (Rmul_zero _)

theorem RsumN_zero_ac (F : Nat → Real) : ∀ N, (∀ i, i < N → Req (F i) zero) → Req (RsumN F N) zero
  | 0, _ => Req_refl _
  | (n + 1), h =>
    Req_trans (Radd_congr (RsumN_zero_ac F n (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))) (Radd_zero _)

/-- `w < a` ⟹ `a + w ≤ a·n` for every place `n ≥ 2`. -/
theorem aw_le_a_mul_n_of_narrow (C : NormCtx) (hw : Qlt C.w C.a) (m : Nat) :
    Qle (add C.a C.w) (mul C.a (upQ (m + 1))) := by
  have hw' := hw
  simp only [Qlt] at hw'
  simp only [Qle, add, mul, upQ]
  push_cast at hw' ⊢
  have hA : (0 : Int) ≤ C.a.num * (C.w.den : Int) := Int.mul_nonneg (Int.le_of_lt C.han) (Int.ofNat_nonneg _)
  have had : (0 : Int) ≤ (C.a.den : Int) := Int.ofNat_nonneg _
  have hm2 : (2 : Int) ≤ ((m : Nat) : Int) + 1 + 1 := by omega
  have e1 : (C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int)) * ((C.a.den : Int) * 1)
      = (C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int)) * (C.a.den : Int) := by ring_uor
  have e2 : C.a.num * (((m : Nat) : Int) + 1 + 1) * ((C.a.den : Int) * (C.w.den : Int))
      = ((((m : Nat) : Int) + 1 + 1) * (C.a.num * (C.w.den : Int))) * (C.a.den : Int) := by ring_uor
  rw [e1, e2]
  refine Int.mul_le_mul_of_nonneg_right ?_ had
  have h2 : C.a.num * (C.w.den : Int) + C.w.num * (C.a.den : Int) ≤ 2 * (C.a.num * (C.w.den : Int)) := by omega
  exact Int.le_trans h2 (Int.mul_le_mul_of_nonneg_right hm2 hA)

/-- **Narrow window**: `w < a` ⟹ `R_H(n) = 0` for every place `n ≥ 2` (`Λ(1) = 0` at `n = 1`), so the prime term
    of the anchor kernel vanishes identically — the kernel is then purely archimedean. -/
theorem primeAC_zero_of_narrow (C : NormCtx) (h : CField) (hp : AnchorProfile C h) (hw : Qlt C.w C.a) :
    Req (primeAC C h) zero := by
  unfold primeAC
  refine RsumN_zero_ac _ C.X (fun m hm => ?_)
  cases m with
  | zero =>
    exact Req_trans (Rmul_congr (Rmul_congr (Req_refl _) vonMangoldt_one) (Req_refl _))
      (Req_trans (Rmul_congr (Rmul_zero _) (Req_refl _)) (Rzero_mul_ch _))
  | succ m' =>
    refine Req_trans (Rmul_congr (Req_refl _) (RH_zero_of_scale_ge C h hp ?_)) (Rmul_zero _)
    have hx : Req (xcl C (upR (m' + 1))) (upR (m' + 1)) := xcl_eq_of_band C (one_le_upR_R _) (upR_le_B_R C _ hm)
    refine Rle_trans ?_ (Rle_of_Req (Rmul_congr (Req_refl _) (Req_symm hx)))
    refine Rle_trans (Rle_ofQ_ofQ _ (Qmul_den_pos C.had Nat.one_pos) (aw_le_a_mul_n_of_narrow C hw m')) ?_
    exact Rle_of_Req (Req_symm (Rmul_ofQ_ofQ _ _))

end UOR.Bridge.F1Square.Square
