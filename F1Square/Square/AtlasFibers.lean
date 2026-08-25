/-
F1 square — **the pole, constant and tail fibers with their external positive densities**
(`AtlasFibers.lean`).

With the raw coordinates `U_x, V, D_x` (`AtlasArchCoords`) and the weight-free atoms `posFiber`/`negFiber`
(`AtlasPrimeDirect`), the remaining terms of the coupled form are realized POINTWISE by fibers of the
Atlas `3 × 8` space paired against EXTERNAL NONNEGATIVE densities (all weights outside Γ):

 * POLE      `poleFiber_x(f,t)  = posFiber (U_x(f,t)) (V(f,t))`,      density `2·(1 + 1/max(x,1))·w·r(t)`:
             reads `(1 + 1/x)·w·r·(U_x(f)V(g) + V(f)U_x(g))` — the pole integrand of `+PoleForm`.
 * CONSTANT  `constFiber(f,t)   = negFiber (V(f,t)) (V(f,t))`,        density `(log 4π + γ)·w·r(t)`:
             reads `−(log 4π + γ)·w·r·V(f)V(g)` — the integrand of `−ArchConstForm`.
 * TAIL      `tailFiber_x(f,t)  = negFiber (Z_x(f,t)) (W_x(f,t))`,     density `2·w·r(t)`,
             `Z_x = x·K(x)·D_x`, `W_x = (1/max(x,1))·V`, `K(x) = 1/max(x − 1/max(x,1), c)` (floor `c`):
             reads `−w·r·K(x)·(D_x(f)V(g) + V(f)D_x(g))` for `x ≥ 1` — the integrand of `−ArchTail`
             with the mandatory factor `2` (`2·(−½) = −1`).  No quotient value at `x = 1` is invented:
             the kernel keeps its floor, and the truncations `x ≥ 1 + 2^{-k}` of the tail stay external.

Each readback is `density·⟨Φ_f, MΦ_g⟩ = (the scalar integrand)` POINTWISE; the fibers' cut/cycle
masses `4A²`, `4B²` are the sites of the finite carriers (`AtlasCarrier`).  Nothing here is a limit,
a form value, or a sign claim.  Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasArchCoords
import F1Square.Square.WeilMellinPole
import F1Square.Analysis.LogFourPiLower
import F1Square.Analysis.LambdaThreePos

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

/-- The archimedean address gauge (any valid address; the readbacks are address-independent). -/
def archAddr : Nat × Nat := (0, 0)
theorem archAddr_valid : archAddr.1 < 3 ∧ archAddr.2 < 8 := by decide

-- ===========================================================================
-- (1) The pole fiber.
-- ===========================================================================

/-- **The pole fiber** `posFiber (U_x(f,t)) (V(f,t))`. -/
def poleFiber (C : NormCtx) (x : Real) (f : L2Test) (t : Real) : Nat → Nat → Real :=
  posFiber archAddr.1 archAddr.2 (Uc C x f t) (Vc C f t)

/-- The pole density `2·(1 + 1/max(x,1))·w·r(t)`. -/
def poleDensity (C : NormCtx) (x t : Real) : Real :=
  Rmul (Rmul cTwo (Radd one (rOne x))) (Rmul (ofQ C.w C.hw) (rEv C t))

theorem poleDensity_nonneg (C : NormCtx) (x t : Real) : Rnonneg (poleDensity C x t) :=
  Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
      (Rnonneg_Radd (Rnonneg_ofQ (by decide) (by decide)) (Rnonneg_clampedInv _ _ _ x)))
    (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t))

/-- `2·p·(½·S) ≈ p·S`. -/
theorem two_half_pd (p S : Real) : Req (Rmul (Rmul cTwo p) (Rmul cH S)) (Rmul p S) := by
  refine Req_trans (mul4_swap_ch cTwo p cH S) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr _ (by decide) (by decide : Qeq (mul (⟨2, 1⟩ : Q) (⟨1, 2⟩ : Q)) (⟨1, 1⟩ : Q)))) (Req_refl _)) ?_
  exact Rone_mul _

/-- **★ POLE READBACK**: `density·⟨poleFiber_f, M poleFiber_g⟩ = (1 + 1/x)·w·r·(U_x(f)V(g) + V(f)U_x(g))`. -/
theorem poleFiber_readback (C : NormCtx) (x : Real) (f g : L2Test) (t : Real) :
    Req (Rmul (poleDensity C x t) (pairF (poleFiber C x f t) (atlasOp (poleFiber C x g t))))
        (Rmul (Rmul (Radd one (rOne x)) (Rmul (ofQ C.w C.hw) (rEv C t)))
              (Radd (Rmul (Uc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C x g t)))) := by
  unfold poleFiber poleDensity
  refine Req_trans (Rmul_congr (Req_refl _) (posFiber_readback _ _ archAddr_valid.1 archAddr_valid.2 _ _ _ _)) ?_
  -- (2·p)·(W r)·(½ S) ≈ (p·(W r))·S
  refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (two_half_pd _ _)) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_comm _ _) (Req_refl _))

-- ===========================================================================
-- (2) The constant fiber.
-- ===========================================================================

/-- **The constant fiber** `negFiber (V(f,t)) (V(f,t))`. -/
def constFiber (C : NormCtx) (f : L2Test) (t : Real) : Nat → Nat → Real :=
  negFiber archAddr.1 archAddr.2 (Vc C f t) (Vc C f t)

/-- The CC archimedean constant `log 4π + γ`. -/
def archConst : Real := Radd Rlog4pic Rgamma_h

theorem archConst_nonneg : Rnonneg archConst :=
  Rnonneg_Radd (Rnonneg_of_Rle_zero (Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) Rlog4pic_ge))
    Rgamma_h_nonneg

/-- The constant density `(log 4π + γ)·w·r(t)`. -/
def constDensity (C : NormCtx) (t : Real) : Real := Rmul archConst (Rmul (ofQ C.w C.hw) (rEv C t))

theorem constDensity_nonneg (C : NormCtx) (t : Real) : Rnonneg (constDensity C t) :=
  Rnonneg_Rmul archConst_nonneg (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t))

/-- **★ CONSTANT READBACK**: `density·⟨constFiber_f, M constFiber_g⟩ = −(log 4π + γ)·w·r·V(f)V(g)`. -/
theorem constFiber_readback (C : NormCtx) (f g : L2Test) (t : Real) :
    Req (Rmul (constDensity C t) (pairF (constFiber C f t) (atlasOp (constFiber C g t))))
        (Rneg (Rmul (Rmul archConst (Rmul (ofQ C.w C.hw) (rEv C t))) (Rmul (Vc C f t) (Vc C g t)))) := by
  unfold constFiber constDensity
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_readback _ _ archAddr_valid.1 archAddr_valid.2 _ _ _ _)) ?_
  refine Req_trans (Rmul_neg_right _ _) (Rneg_congr ?_)
  -- d·(½(VV' + VV')) ≈ d·(VV')
  refine Rmul_congr (Req_refl _) ?_
  exact half_double_pd _

-- ===========================================================================
-- (3) The tail fiber.
-- ===========================================================================

/-- The floored archimedean kernel `K_c(x) = 1/max(x − 1/max(x,1), c)` (`= 1/(x − x⁻¹)` where `x − x⁻¹ ≥ c`). -/
def Kfl (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) : Real := (archKernFull c hcn hcd).f x

/-- **`Z_x(f,t) = x·K_c(x)·D_x(f,t)`** — the kernel-absorbed defect coordinate. -/
def Zc (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (f : L2Test) (t : Real) : Real :=
  Rmul (Rmul x (Kfl c hcn hcd x)) (Dc C x f t)

/-- **`W_x(f,t) = (1/max(x,1))·V(f,t)`**. -/
def Wc (C : NormCtx) (x : Real) (f : L2Test) (t : Real) : Real := Rmul (rOne x) (Vc C f t)

/-- **The tail fiber** `negFiber (Z_x(f,t)) (W_x(f,t))`. -/
def tailFiber (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (f : L2Test) (t : Real) :
    Nat → Nat → Real :=
  negFiber archAddr.1 archAddr.2 (Zc C c hcn hcd x f t) (Wc C x f t)

/-- The tail density `2·w·r(t)` (the mandatory factor `2`; the kernel sits inside `Z`). -/
def tailDensity (C : NormCtx) (t : Real) : Real := Rmul cTwo (Rmul (ofQ C.w C.hw) (rEv C t))

theorem tailDensity_nonneg (C : NormCtx) (t : Real) : Rnonneg (tailDensity C t) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t))

/-- `Z_f·W_g = K·(D_f·V_g)` for `x ≥ 1` (`x·(1/max(x,1)) = 1`). -/
theorem Zc_mul_Wc (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx : Rle one x)
    (f g : L2Test) (t : Real) :
    Req (Rmul (Zc C c hcn hcd x f t) (Wc C x g t)) (Rmul (Kfl c hcn hcd x) (Rmul (Dc C x f t) (Vc C g t))) := by
  unfold Zc Wc
  -- ((xK)D)·(rV) ≈ (K·(x·r))·(D·V)
  refine Req_trans (mul4_swap_ch _ _ _ _) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_assoc x _ _) (Req_trans (Rmul_congr (Req_refl x) (Rmul_comm _ _))
    (Req_trans (Req_symm (Rmul_assoc x _ _)) (Rmul_congr (Rmul_clampedInv_one x hx) (Req_refl _))))) (Req_refl _)) ?_
  exact Rmul_congr (Rone_mul _) (Req_refl _)

/-- `W_f·Z_g = K·(V_f·D_g)` for `x ≥ 1`. -/
theorem Wc_mul_Zc (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx : Rle one x)
    (f g : L2Test) (t : Real) :
    Req (Rmul (Wc C x f t) (Zc C c hcn hcd x g t)) (Rmul (Kfl c hcn hcd x) (Rmul (Vc C f t) (Dc C x g t))) := by
  refine Req_trans (Rmul_comm _ _) (Req_trans (Zc_mul_Wc C c hcn hcd x hx g f t) ?_)
  exact Rmul_congr (Req_refl _) (Rmul_comm _ _)

/-- **★ TAIL READBACK** (`x ≥ 1`): `density·⟨tailFiber_f, M tailFiber_g⟩ = −w·r·K(x)·(D_x(f)V(g) + V(f)D_x(g))`. -/
theorem tailFiber_readback (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx : Rle one x)
    (f g : L2Test) (t : Real) :
    Req (Rmul (tailDensity C t) (pairF (tailFiber C c hcn hcd x f t) (atlasOp (tailFiber C c hcn hcd x g t))))
        (Rneg (Rmul (Rmul (ofQ C.w C.hw) (rEv C t))
          (Rmul (Kfl c hcn hcd x) (Radd (Rmul (Dc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C x g t)))))) := by
  unfold tailFiber tailDensity
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_readback _ _ archAddr_valid.1 archAddr_valid.2 _ _ _ _)) ?_
  refine Req_trans (Rmul_neg_right _ _) (Rneg_congr ?_)
  -- (2·(W r))·(½·S) ≈ (W r)·S, then S = K(DV') + K(VD') = K·(…)
  refine Req_trans (two_half_pd _ _) (Rmul_congr (Req_refl _) ?_)
  refine Req_trans (Radd_congr (Zc_mul_Wc C c hcn hcd x hx f g t) (Wc_mul_Zc C c hcn hcd x hx f g t)) ?_
  exact Req_symm (Rmul_distrib _ _ _)

-- ===========================================================================
-- (4) Two sourced identities preserved for the replacement.
-- ===========================================================================

/-- `(P + Q) − ((P − R) − S) ≈ (Q + R) + S`. -/
theorem sub_regroup_af (P Q R S : Real) :
    Req (Rsub (Radd P Q) (Rsub (Rsub P R) S)) (Radd (Radd Q R) S) := by
  show Req (Radd (Radd P Q) (Rneg (Radd (Radd P (Rneg R)) (Rneg S)))) (Radd (Radd Q R) S)
  refine Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_trans (Rneg_Radd _ _)
    (Radd_congr (Req_refl _) (Rneg_neg R))) (Rneg_neg S)))) ?_
  -- (P + Q) + ((−P + R) + S) ≈ (Q + R) + S
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Radd_congr ?_ (Req_refl S))
  refine Req_trans (Radd_swap P Q (Rneg P) R) ?_
  exact Req_trans (Radd_congr (Radd_neg P) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

/-- **★ THE ANCHOR FROM POLE AND TAIL CUT COORDINATES (raw form, every real `x`)**:
    `(K·(x + x·(1/max(x,1))) + 1/max(x,1))·(V/2) = 2·(xK·A_pole − A_tail)`,
    `A_pole = (U_x + V)/4`, `A_tail = (Z_x − W_x)/4`.  For `x ≥ 1` the prefactor is `K(x+1) + x⁻¹`
    (`anchor_from_pole_tail_ge_one`); no `x = 1` site is needed. -/
theorem anchor_from_pole_tail (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (f : L2Test) (t : Real) :
    Req (Rmul (Radd (Rmul (Kfl c hcn hcd x) (Radd x (Rmul x (rOne x)))) (rOne x)) (Rmul cH (Vc C f t)))
        (Rmul cTwo (Rsub (Rmul (Rmul x (Kfl c hcn hcd x)) (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))))
                         (aCoefGa one (Zc C c hcn hcd x f t) (Wc C x f t)))) := by
  unfold aCoefGa Zc Wc Dc
  -- abbreviations as reals
  generalize hK : Kfl c hcn hcd x = K
  generalize hr : rOne x = r
  generalize hU : Uc C x f t = U
  generalize hV : Vc C f t = V
  refine Req_symm ?_
  -- A_pole = ¼(U + V), A_tail = ¼((xK)(U − rV) − rV)
  have hA : Req (Rmul cQ (Rsub (Rmul one U) (Rneg V))) (Rmul cQ (Radd U V)) :=
    Rmul_congr (Req_refl cQ) (Radd_congr (Rone_mul U) (Rneg_neg V))
  have hB : Req (Rmul cQ (Rsub (Rmul one (Rmul (Rmul x K) (Rsub U (Rmul r V)))) (Rmul r V)))
      (Rmul cQ (Rsub (Rmul (Rmul x K) (Rsub U (Rmul r V))) (Rmul r V))) :=
    Rmul_congr (Req_refl cQ) (Rsub_congr (Rone_mul _) (Req_refl _))
  refine Req_trans (Rmul_congr (Req_refl cTwo) (Rsub_congr (Rmul_congr (Req_refl _) hA) hB)) ?_
  -- (xK)(¼Y) ≈ ¼((xK)Y)
  have hpull : Req (Rmul (Rmul x K) (Rmul cQ (Radd U V))) (Rmul cQ (Rmul (Rmul x K) (Radd U V))) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))
  refine Req_trans (Rmul_congr (Req_refl cTwo) (Rsub_congr hpull (Req_refl _))) ?_
  refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_symm (Rmul_sub_distrib cQ _ _))) ?_
  -- 2·(¼Z) ≈ ½Z
  refine Req_trans (Req_symm (Rmul_assoc cTwo cQ _)) ?_
  have h2q : Req (Rmul cTwo cQ) cH :=
    Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide)) (ofQ_congr _ (by decide) (by decide))
  refine Req_trans (Rmul_congr h2q (Req_refl _)) ?_
  -- Z = (xK)(U+V) − ((xK)(U − rV) − rV) ≈ ((xK)V + (xK)(rV)) + rV
  have hZ : Req (Rsub (Rmul (Rmul x K) (Radd U V)) (Rsub (Rmul (Rmul x K) (Rsub U (Rmul r V))) (Rmul r V)))
      (Radd (Radd (Rmul (Rmul x K) V) (Rmul (Rmul x K) (Rmul r V))) (Rmul r V)) := by
    refine Req_trans (Rsub_congr (Rmul_distrib _ _ _) (Rsub_congr (Rmul_sub_distrib _ _ _) (Req_refl _))) ?_
    exact sub_regroup_af _ _ _ _
  refine Req_trans (Rmul_congr (Req_refl cH) hZ) ?_
  -- ½·(((xK)V + (xK)(rV)) + rV) ≈ (K(x + xr) + r)·(½V)
  have hS : Req (Radd (Radd (Rmul (Rmul x K) V) (Rmul (Rmul x K) (Rmul r V))) (Rmul r V))
      (Rmul (Radd (Rmul K (Radd x (Rmul x r))) r) V) := by
    refine Req_symm ?_
    refine Req_trans (Rmul_distrib_right _ _ _) (Radd_congr ?_ (Req_refl _))
    refine Req_trans (Rmul_congr (Rmul_distrib K x (Rmul x r)) (Req_refl V)) ?_
    refine Req_trans (Rmul_distrib_right _ _ _) (Radd_congr (Rmul_congr (Rmul_comm K x) (Req_refl V)) ?_)
    -- (K(xr))V ≈ (xK)(rV)
    refine Req_trans (Rmul_assoc K _ _) ?_
    refine Req_trans (Rmul_congr (Req_refl K) (Rmul_assoc x r V)) ?_
    refine Req_trans (Req_symm (Rmul_assoc K x _)) (Rmul_congr (Rmul_comm K x) (Req_refl _))
  refine Req_trans (Rmul_congr (Req_refl cH) hS) ?_
  -- ½(S·V) ≈ S·(½V)
  refine Req_trans (Req_symm (Rmul_assoc cH _ V)) (Req_trans (Rmul_congr (Rmul_comm cH _) (Req_refl V)) (Rmul_assoc _ cH V))

/-- The `x ≥ 1` form: `(K(x+1) + x⁻¹)·(V/2) = 2·(xK·A_pole − A_tail)`. -/
theorem anchor_from_pole_tail_ge_one (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (x : Real) (hx : Rle one x)
    (f : L2Test) (t : Real) :
    Req (Rmul (Radd (Rmul (Kfl c hcn hcd x) (Radd x one)) (rOne x)) (Rmul cH (Vc C f t)))
        (Rmul cTwo (Rsub (Rmul (Rmul x (Kfl c hcn hcd x)) (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))))
                         (aCoefGa one (Zc C c hcn hcd x f t) (Wc C x f t)))) := by
  refine Req_trans ?_ (anchor_from_pole_tail C c hcn hcd x f t)
  exact Rmul_congr (Radd_congr (Rmul_congr (Req_refl _) (Radd_congr (Req_refl x) (Req_symm (Rmul_clampedInv_one x hx)))) (Req_refl _)) (Req_refl _)

/-- `posFiber V V` is PURE CUT: its cycle coordinate vanishes and its cut coordinate is `V/2`. -/
theorem posFiber_VV_cycle_zero (V : Real) : Req (bCoefGa one V (Rneg V)) zero := by
  unfold bCoefGa
  exact Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Radd_congr (Rone_mul V) (Req_refl _)) (Radd_neg V))) (Rmul_zero cQ)
theorem posFiber_VV_cut (V : Real) : Req (aCoefGa one V (Rneg V)) (Rmul cH V) := by
  unfold aCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Rsub_congr (Rone_mul V) (Req_refl _))
    (Req_trans (Radd_congr (Req_refl V) (Rneg_neg V)) (Req_symm (cTwo_mul V))))) ?_
  refine Req_trans (Req_symm (Rmul_assoc cQ cTwo V)) (Rmul_congr ?_ (Req_refl V))
  exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))
theorem posFiber_VV_readback (uf ug : Real) :
    Req (pairF (posFiber archAddr.1 archAddr.2 uf uf) (atlasOp (posFiber archAddr.1 archAddr.2 ug ug))) (Rmul uf ug) :=
  Req_trans (posFiber_readback _ _ archAddr_valid.1 archAddr_valid.2 uf uf ug ug) (half_double_pd _)

/-- `WR·(K·(2·(r₁·P))) ≈ ((2·WR)·(K·r₁))·P`. -/
theorem tail_high_alg (WR K r₁ P : Real) :
    Req (Rmul WR (Rmul K (Rmul cTwo (Rmul r₁ P)))) (Rmul (Rmul (Rmul cTwo WR) (Rmul K r₁)) P) := by
  refine Req_trans (Rmul_congr (Req_refl WR) (Rmul_congr (Req_refl K) (Req_symm (Rmul_assoc cTwo r₁ P)))) ?_
  refine Req_trans (Rmul_congr (Req_refl WR) (Req_symm (Rmul_assoc K _ P))) ?_
  refine Req_trans (Req_symm (Rmul_assoc WR _ P)) (Rmul_congr ?_ (Req_refl P))
  -- WR·(K·(2r₁)) ≈ (2WR)·(K r₁)
  refine Req_trans (Rmul_congr (Req_refl WR) (Req_trans (Req_symm (Rmul_assoc K cTwo r₁))
    (Req_trans (Rmul_congr (Rmul_comm K cTwo) (Req_refl r₁)) (Rmul_assoc cTwo K r₁)))) ?_
  refine Req_trans (Req_symm (Rmul_assoc WR cTwo _)) (Rmul_congr (Rmul_comm WR cTwo) (Req_refl _))

/-- **★ THE OMITTED `x ≥ B` TAIL IS A POSITIVE PURE-CUT CHANNEL** (core tests, `t ≤ a + w`): there
    `D_x = −(1/x)V`, so the tail integrand is `+(2·w·r·K(x)·(1/x))·V(f)V(g)` — the readback of the pure-cut
    fiber `posFiber V V` against the nonnegative density `2·w·r·K(x)/x`.  (Classically
    `∫_B^∞ 2·dx/(x²−1) = log((B+1)/(B−1))` is its integrated coefficient; that closed form is NOT claimed here.) -/
theorem tailFiber_high_pure_cut (C : NormCtx) (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (f g : L2Test)
    (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (x t : Real)
    (hx : Rle (ofQ (canonB C) (canonB_den C)) x) (ht : Rle t (ofQ (add C.a C.w) (add_den_pos C.had C.hw))) :
    Req (Rmul (tailDensity C t) (pairF (tailFiber C c hcn hcd x f t) (atlasOp (tailFiber C c hcn hcd x g t))))
        (Rmul (Rmul (tailDensity C t) (Rmul (Kfl c hcn hcd x) (rOne x)))
              (pairF (posFiber archAddr.1 archAddr.2 (Vc C f t) (Vc C f t))
                     (atlasOp (posFiber archAddr.1 archAddr.2 (Vc C g t) (Vc C g t))))) := by
  have hx1 : Rle one x := Rle_trans (Rle_ofQ_ofQ (by decide) (canonB_den C) (canonB_one C)) hx
  have hin : Req (Radd (Rmul (Rneg (Rmul (rOne x) (Vc C f t))) (Vc C g t)) (Rmul (Vc C f t) (Rneg (Rmul (rOne x) (Vc C g t)))))
      (Rneg (Rmul cTwo (Rmul (rOne x) (Rmul (Vc C f t) (Vc C g t))))) := by
    refine Req_trans (Radd_congr (Rmul_neg_left _ _) (Rmul_neg_right _ _)) ?_
    refine Req_trans (Req_symm (Rneg_Radd _ _)) (Rneg_congr ?_)
    have h1 : Req (Rmul (Rmul (rOne x) (Vc C f t)) (Vc C g t)) (Rmul (rOne x) (Rmul (Vc C f t) (Vc C g t))) := Rmul_assoc _ _ _
    have h2 : Req (Rmul (Vc C f t) (Rmul (rOne x) (Vc C g t))) (Rmul (rOne x) (Rmul (Vc C f t) (Vc C g t))) :=
      Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))
    exact Req_trans (Radd_congr h1 h2) (Req_symm (cTwo_mul _))
  refine Req_trans (tailFiber_readback C c hcn hcd x hx1 f g t) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _)
    (Radd_congr (Rmul_congr (Dc_high_eq_neg_rOne_Vc C f hf x t hx ht) (Req_refl _))
                (Rmul_congr (Req_refl _) (Dc_high_eq_neg_rOne_Vc C g hg x t hx ht)))))) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) hin))) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl _) (Rmul_neg_right _ _))) ?_
  refine Req_trans (Rneg_congr (Rmul_neg_right _ _)) ?_
  refine Req_trans (Rneg_neg _) ?_
  refine Req_trans (tail_high_alg _ _ _ _) ?_
  unfold tailDensity
  exact Rmul_congr (Req_refl _) (Req_symm (posFiber_VV_readback _ _))

end UOR.Bridge.F1Square.Square
