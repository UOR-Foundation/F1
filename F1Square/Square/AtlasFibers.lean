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

end UOR.Bridge.F1Square.Square
