/-
F1 square — **the folded prime channel on the upper scale** (`AtlasPrimeFold.lean`, AC-22 item 2).

Each reciprocal prime pair is folded onto its upper scale `n = m+1` (all-scale adjoint law):

    `P_m(f,g) = Λ(n)·(B_n(f,g) + B_n(g,f))`                              (`PForm_fold`, core tests),
    `B_n(f,g) = w·∫₀¹ U_n(f)·V(g)·r`   with `U_n = n^{-1/2}·u_n`             (`BForm_eq_w_foldInt`),

and consumed immediately by ONE `negFiber` field `Φ_f(t) = negFiber (U_n(f,t)) (V(f,t))` against the
external nonnegative density `2·Λ(n)·w·r(t)` (the factor `2` is forced: `negFiber` reads back `−½` of the
symmetric product):

    `density·⟨Φ_f, MΦ_g⟩ = −Λ(n)·w·r·(U_n(f)V(g) + V(f)U_n(g))`             (`primeFoldFiber_readback`),
    `primeFoldDirect_m(f,g) = ∫₀¹ density·⟨Φ_f, MΦ_g⟩ = −Λ(n)(B_n(f,g) + B_n(g,f))`,
    `primeFoldGram(f,g) = Σ_{m<X} primeFoldDirect_m = −PrimeForm_X(f,g)`   on `ClosedCore`.

Co-location of the scale labels with the pole/tail field is NOT a cancellation: the prime mass is atomic
(one scale per place), the tail is continuous.  Target-free: imports no closed form.  No positivity.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasFibers
import F1Square.Square.AtlasParamIntegral

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) THE FOLD `P_m(f,g) = Λ(n)(B_n(f,g) + B_n(g,f))` on core tests.
-- ===========================================================================

/-- **★ THE FOLD**: the lower-scale term `(m+1)^{-1}·B_{1/(m+1)}(f,g)` IS `B_{m+1}(g,f)`
    (`BForm_adjoint_swap_all`), so `P_m(f,g) = Λ(m+1)·(B_{m+1}(f,g) + B_{m+1}(g,f))`.  `m = 0` by `Λ(1) = 0`. -/
theorem PForm_fold (C : NormCtx) (m : Nat) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    Req (PForm m f g C.a C.han C.had C.w C.hw C.hwn)
        (Rmul (vonMangoldt (m + 1))
          (Radd (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                   C.a C.han C.had C.w C.hw C.hwn)
                (BForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                   C.a C.han C.had C.w C.hw C.hwn))) := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have L : Req (PForm 0 f g C.a C.han C.had C.w C.hw C.hwn) zero :=
      Req_trans (Rmul_congr vonMangoldt_one (Req_refl _))
        (Req_trans (Rmul_comm zero _) (Rmul_zero _))
    refine Req_trans L (Req_symm ?_)
    exact Req_trans (Rmul_congr vonMangoldt_one (Req_refl _)) (Req_trans (Rmul_comm zero _) (Rmul_zero _))
  · refine Rmul_congr (Req_refl _) (Radd_congr (Req_refl _) ?_)
    refine Req_trans (Rmul_congr (Req_refl _)
      (BForm_adjoint_swap_all f g C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos m hpos hg.hgh hf.hgl C.hfit)) ?_
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))
      (ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos) _)) ?_
    exact Req_trans (Rmul_congr (ofQ_recip_one m) (Req_refl _)) (Rone_mul _)

-- ===========================================================================
-- (2) The folded fiber, its density, and the pointwise readback.
-- ===========================================================================

/-- The upper scale `n = m+1` as a real. -/
def upR (m : Nat) : Real := ofQ (⟨((m + 1 : Nat) : Int), 1⟩ : Q) Nat.one_pos

/-- **The folded prime fiber** `negFiber (U_n(f,t)) (V(f,t))` at the archimedean address gauge. -/
def primeFoldFiber (C : NormCtx) (m : Nat) (f : L2Test) (t : Real) : Nat → Nat → Real :=
  negFiber archAddr.1 archAddr.2 (Uc C (upR m) f t) (Vc C f t)

/-- The folded prime density `2·Λ(n)·w·r(t)` (the mandatory factor `2`). -/
def primeFoldDensity (C : NormCtx) (m : Nat) (t : Real) : Real :=
  Rmul cTwo (Rmul (vonMangoldt (m + 1)) (Rmul (ofQ C.w C.hw) (rEv C t)))

theorem primeFoldDensity_nonneg (C : NormCtx) (m : Nat) (t : Real) : Rnonneg (primeFoldDensity C m t) :=
  Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
    (Rnonneg_Rmul (vonMangoldt_nonneg _) (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t)))

/-- **★ FOLD READBACK**: `density·⟨Φ_f, MΦ_g⟩ = −Λ(n)·w·r·(U_n(f)V(g) + V(f)U_n(g))`. -/
theorem primeFoldFiber_readback (C : NormCtx) (m : Nat) (f g : L2Test) (t : Real) :
    Req (Rmul (primeFoldDensity C m t) (pairF (primeFoldFiber C m f t) (atlasOp (primeFoldFiber C m g t))))
        (Rneg (Rmul (Rmul (vonMangoldt (m + 1)) (Rmul (ofQ C.w C.hw) (rEv C t)))
          (Radd (Rmul (Uc C (upR m) f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C (upR m) g t))))) := by
  unfold primeFoldFiber primeFoldDensity
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_readback _ _ archAddr_valid.1 archAddr_valid.2 _ _ _ _)) ?_
  refine Req_trans (Rmul_neg_right _ _) (Rneg_congr ?_)
  exact two_half_pd _ _

-- ===========================================================================
-- (3) The raw integrand `U_n(f)V(g)r = n^{-1/2}·crossInt` and its identification with `B_n`.
-- ===========================================================================

/-- The pulled-back raw integrand `U_n(f)·V(g)·r`, realized as `n^{-1/2}·crossInt_n`. -/
def foldInt (C : NormCtx) (m : Nat) (f g : L2Test) (y : Real) : Real :=
  Rmul (invSq C (upR m)) (crossInt C (upR m) f g y)
def foldL (C : NormCtx) (m : Nat) (f g : L2Test) : Q := mul (xBQ (invSq C (upR m))) (crossL C (upR m) f g)
theorem foldL_den (C : NormCtx) (m : Nat) (f g : L2Test) : 0 < (foldL C m f g).den :=
  Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)
theorem foldL_num (C : NormCtx) (m : Nat) (f g : L2Test) : 0 ≤ (foldL C m f g).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)
theorem foldInt_lip (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (foldInt C m f g y) (foldInt C m f g z))) (Rmul (ofQ (foldL C m f g) (foldL_den C m f g)) (Rabs (Rsub y z))) :=
  p1_lip C (upR m) f g
theorem foldInt_fc (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z, Req y z → Req (foldInt C m f g y) (foldInt C m f g z) :=
  fc_smul_fl _ (crossInt_fc C (upR m) f g)

/-- `s·((d·v)·r) ≈ ((s·d)·v)·r`. -/
theorem pull_af (s d v r : Real) : Req (Rmul s (Rmul (Rmul d v) r)) (Rmul (Rmul (Rmul s d) v) r) :=
  Req_trans (Req_symm (Rmul_assoc s (Rmul d v) r)) (Rmul_congr (Req_symm (Rmul_assoc s d v)) (Req_refl r))

/-- `foldInt = (U_n(f)·V(g))·r` pointwise. -/
theorem foldInt_eq_UV (C : NormCtx) (m : Nat) (f g : L2Test) (y : Real) :
    Req (foldInt C m f g y) (Rmul (Rmul (Uc C (upR m) f (affC C y)) (Vc C g (affC C y))) (rEv C (affC C y))) := by
  unfold foldInt crossInt prodInt Uc Vc vEv
  exact pull_af _ _ _ _

/-- `foldInt = n^{-1/2}·hInt` pointwise (`m < X`: the common-scale bridge `Uc_placeData`). -/
theorem foldInt_eq_hInt (C : NormCtx) (m : Nat) (hm : m < C.X) (f g : L2Test) (y : Real) :
    Req (foldInt C m f g y)
        (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (hInt C (placeData C m 0) f g y)) := by
  refine Req_trans (foldInt_eq_UV C m f g y) ?_
  have hU : Req (Uc C (upR m) f (affC C y))
      (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (uEv C (placeData C m 0) f (affC C y))) :=
    Uc_placeData C m 0 hm f (affC C y)
  unfold hInt affC
  show Req (Rmul (Rmul (Uc C (upR m) f (affC C y)) (Vc C g (affC C y))) (rEv C (affC C y)))
    (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
      (Rmul (Rmul (uEv C (placeData C m 0) f (affC C y)) (vEv C g (affC C y))) (rEv C (affC C y))))
  refine Req_trans (Rmul_congr (Rmul_congr hU (Req_refl _)) (Req_refl _)) ?_
  exact Req_symm (pull_af _ _ _ _)

/-- `∫₀¹ foldInt = n^{-1/2}·∫₀¹ hInt` (`m < X`). -/
theorem integral_foldInt (C : NormCtx) (m : Nat) (hm : m < C.X) (f g : L2Test) :
    Req (riemannIntegral (foldL_den C m f g) (foldL_num C m f g) (foldInt_lip C m f g) (foldInt_fc C m f g))
        (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
          (riemannIntegral (hIntL_den C (placeData C m 0) f g) (hIntL_num C (placeData C m 0) f g)
            (hInt_lip C (placeData C m 0) f g) (hInt_fc C (placeData C m 0) f g))) := by
  have hlipN : ∀ y z, Rle (Rabs (Rsub (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (hInt C (placeData C m 0) f g y))
                                     (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (hInt C (placeData C m 0) f g z))))
      (Rmul (ofQ (foldL C m f g) (foldL_den C m f g)) (Rabs (Rsub y z))) :=
    lip_of_congr_pd _ (fun y => Req_symm (foldInt_eq_hInt C m hm f g y)) (foldInt_lip C m f g)
  have hfcN := fc_smul_fl (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (hInt_fc C (placeData C m 0) f g)
  refine Req_trans (riemannIntegral_congr (foldL_den C m f g) (foldL_num C m f g) (foldInt_lip C m f g) (foldInt_fc C m f g)
    hlipN hfcN (foldInt_eq_hInt C m hm f g)) ?_
  refine Req_trans (riemannIntegral_certif_irrel _ _ hlipN hfcN (Qmul_den_pos Nat.one_pos (hIntL_den C (placeData C m 0) f g))
    (Qmul_num_nonneg (xBQ_num_nonneg _) (hIntL_num C (placeData C m 0) f g))
    (lip_smul_fl _ (hIntL_den C (placeData C m 0) f g) (hIntL_num C (placeData C m 0) f g) (hInt_lip C (placeData C m 0) f g)) hfcN) ?_
  exact riemannIntegral_smul_real_fl _ (hIntL_den C (placeData C m 0) f g) (hIntL_num C (placeData C m 0) f g)
    (hInt_lip C (placeData C m 0) f g) (hInt_fc C (placeData C m 0) f g)

/-- **★ `B_n(f,g) = w·∫₀¹ U_n(f)V(g)r`** (`m < X`): the normalized Haar form at the upper scale is the
    window integral of the raw coherent coordinates. -/
theorem BForm_eq_w_foldInt (C : NormCtx) (m : Nat) (hm : m < C.X) (f g : L2Test) :
    Req (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
          C.a C.han C.had C.w C.hw C.hwn)
        (Rmul (ofQ C.w C.hw)
          (riemannIntegral (foldL_den C m f g) (foldL_num C m f g) (foldInt_lip C m f g) (foldInt_fc C m f g))) := by
  show Req (Rmul (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
              (HForm f g (placeData C m 0).q (placeData C m 0).hqn (placeData C m 0).hqd C.a C.han C.had C.w C.hw C.hwn)) _
  rw [HForm_unfold C (placeData C m 0) f g]
  refine Req_trans (swap_w_ac _ _ _) (Rmul_congr (Req_refl _) ?_)
  exact Req_symm (integral_foldInt C m hm f g)

-- ===========================================================================
-- (4) The pairing integrand, its explicit form, certificates, and the direct integral.
-- ===========================================================================

/-- The pulled-back pairing integrand `density(t)·⟨Φ_f(t), MΦ_g(t)⟩`, `t = a + w·y`. -/
def primeFoldInt (C : NormCtx) (m : Nat) (f g : L2Test) (y : Real) : Real :=
  Rmul (primeFoldDensity C m (affC C y))
       (pairF (primeFoldFiber C m f (affC C y)) (atlasOp (primeFoldFiber C m g (affC C y))))

/-- The explicit form `−(Λ·w)·(foldInt(f,g) + foldInt(g,f))`. -/
def foldExp (C : NormCtx) (m : Nat) (f g : L2Test) (y : Real) : Real :=
  Rneg (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw)) (Radd (foldInt C m f g y) (foldInt C m g f y)))

/-- `(Λ·(w·r))·(A + B) ≈ (Λ·w)·((A·r) + (B·r))`. -/
theorem fold_pt_alg (Λ w r A B : Real) :
    Req (Rmul (Rmul Λ (Rmul w r)) (Radd A B)) (Rmul (Rmul Λ w) (Radd (Rmul A r) (Rmul B r))) := by
  refine Req_trans (Rmul_congr (Req_symm (Rmul_assoc Λ w r)) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc (Rmul Λ w) r (Radd A B)) (Rmul_congr (Req_refl _) ?_)
  exact Req_trans (Rmul_distrib r A B) (Radd_congr (Rmul_comm r A) (Rmul_comm r B))

/-- The pairing integrand IS the explicit form pointwise. -/
theorem primeFoldInt_eq_exp (C : NormCtx) (m : Nat) (f g : L2Test) (y : Real) :
    Req (primeFoldInt C m f g y) (foldExp C m f g y) := by
  unfold primeFoldInt foldExp
  refine Req_trans (primeFoldFiber_readback C m f g (affC C y)) (Rneg_congr ?_)
  refine Req_trans (fold_pt_alg _ _ _ _ _) (Rmul_congr (Req_refl _) (Radd_congr (Req_symm (foldInt_eq_UV C m f g y)) ?_))
  exact Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_symm (foldInt_eq_UV C m g f y))

def foldPairL (C : NormCtx) (m : Nat) (f g : L2Test) : Q := add (foldL C m f g) (foldL C m g f)
theorem foldPairL_den (C : NormCtx) (m : Nat) (f g : L2Test) : 0 < (foldPairL C m f g).den :=
  add_den_pos (foldL_den C m f g) (foldL_den C m g f)
theorem foldPairL_num (C : NormCtx) (m : Nat) (f g : L2Test) : 0 ≤ (foldPairL C m f g).num :=
  Qadd_num_nonneg_loc (foldL_num C m f g) (foldL_num C m g f)
theorem foldPair_lip (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Radd (foldInt C m f g y) (foldInt C m g f y)) (Radd (foldInt C m f g z) (foldInt C m g f z))))
        (Rmul (ofQ (foldPairL C m f g) (foldPairL_den C m f g)) (Rabs (Rsub y z))) :=
  lip_add_fl (foldL_den C m f g) (foldL_den C m g f) (foldInt_lip C m f g) (foldInt_lip C m g f)
theorem foldPair_fc (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z, Req y z →
    Req (Radd (foldInt C m f g y) (foldInt C m g f y)) (Radd (foldInt C m f g z) (foldInt C m g f z)) :=
  fun y z h => Radd_congr (foldInt_fc C m f g y z h) (foldInt_fc C m g f y z h)

def foldExpL (C : NormCtx) (m : Nat) (f g : L2Test) : Q :=
  mul (xBQ (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw))) (foldPairL C m f g)
theorem foldExpL_den (C : NormCtx) (m : Nat) (f g : L2Test) : 0 < (foldExpL C m f g).den :=
  Qmul_den_pos Nat.one_pos (foldPairL_den C m f g)
theorem foldExpL_num (C : NormCtx) (m : Nat) (f g : L2Test) : 0 ≤ (foldExpL C m f g).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (foldPairL_num C m f g)
theorem foldExpPos_lip (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw)) (Radd (foldInt C m f g y) (foldInt C m g f y)))
                    (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw)) (Radd (foldInt C m f g z) (foldInt C m g f z)))))
        (Rmul (ofQ (foldExpL C m f g) (foldExpL_den C m f g)) (Rabs (Rsub y z))) :=
  lip_smul_fl _ (foldPairL_den C m f g) (foldPairL_num C m f g) (foldPair_lip C m f g)
theorem foldExpPos_fc (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z, Req y z →
    Req (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw)) (Radd (foldInt C m f g y) (foldInt C m g f y)))
        (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw)) (Radd (foldInt C m f g z) (foldInt C m g f z))) :=
  fc_smul_fl _ (foldPair_fc C m f g)
theorem foldExp_lip (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (foldExp C m f g y) (foldExp C m f g z))) (Rmul (ofQ (foldExpL C m f g) (foldExpL_den C m f g)) (Rabs (Rsub y z))) :=
  lip_neg_pi (foldExpL_den C m f g) (foldExpPos_lip C m f g)
theorem foldExp_fc (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z, Req y z → Req (foldExp C m f g y) (foldExp C m f g z) :=
  fun y z h => Rneg_congr (foldExpPos_fc C m f g y z h)

theorem primeFoldInt_lip (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (primeFoldInt C m f g y) (primeFoldInt C m f g z)))
        (Rmul (ofQ (foldExpL C m f g) (foldExpL_den C m f g)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (primeFoldInt_eq_exp C m f g) (foldExp_lip C m f g)
theorem primeFoldInt_fc (C : NormCtx) (m : Nat) (f g : L2Test) : ∀ y z, Req y z →
    Req (primeFoldInt C m f g y) (primeFoldInt C m f g z) :=
  fc_of_congr_pd (primeFoldInt_eq_exp C m f g) (foldExp_fc C m f g)

/-- **The folded direct integral** `∫₀¹ density·⟨Φ_f, MΦ_g⟩` at place `m`. -/
def primeFoldDirect (C : NormCtx) (m : Nat) (f g : L2Test) : Real :=
  riemannIntegral (foldExpL_den C m f g) (foldExpL_num C m f g) (primeFoldInt_lip C m f g) (primeFoldInt_fc C m f g)

/-- `primeFoldDirect = −(Λ·w)·(∫foldInt(f,g) + ∫foldInt(g,f))` (finite linearity, moduli reconciled). -/
theorem primeFoldDirect_eq (C : NormCtx) (m : Nat) (f g : L2Test) :
    Req (primeFoldDirect C m f g)
        (Rneg (Rmul (Rmul (vonMangoldt (m + 1)) (ofQ C.w C.hw))
          (Radd (riemannIntegral (foldL_den C m f g) (foldL_num C m f g) (foldInt_lip C m f g) (foldInt_fc C m f g))
                (riemannIntegral (foldL_den C m g f) (foldL_num C m g f) (foldInt_lip C m g f) (foldInt_fc C m g f))))) := by
  unfold primeFoldDirect
  refine Req_trans (riemannIntegral_congr (foldExpL_den C m f g) (foldExpL_num C m f g) (primeFoldInt_lip C m f g)
    (primeFoldInt_fc C m f g) (foldExp_lip C m f g) (foldExp_fc C m f g) (primeFoldInt_eq_exp C m f g)) ?_
  refine Req_trans (riemannIntegral_neg (foldExpL_den C m f g) (foldExpL_num C m f g) (foldExpPos_lip C m f g)
    (foldExpPos_fc C m f g) (foldExp_lip C m f g) (foldExp_fc C m f g)) (Rneg_congr ?_)
  refine Req_trans (riemannIntegral_smul_real_fl _ (foldPairL_den C m f g) (foldPairL_num C m f g)
    (foldPair_lip C m f g) (foldPair_fc C m f g)) (Rmul_congr (Req_refl _) ?_)
  have h1 := lip_weaken_fl (foldL_den C m f g) (foldPairL_den C m f g) (Qle_add_right_nonneg (foldL_num C m g f)) (foldInt_lip C m f g)
  have h2 := lip_weaken_fl (foldL_den C m g f) (foldPairL_den C m f g) (Qle_add_left_nonneg (foldL_num C m f g)) (foldInt_lip C m g f)
  refine Req_trans (riemannIntegral_add (foldPairL_den C m f g) (foldPairL_num C m f g) h1 (foldInt_fc C m f g) h2 (foldInt_fc C m g f)
    (foldPair_lip C m f g) (foldPair_fc C m f g)) ?_
  exact Radd_congr (riemannIntegral_certif_irrel _ _ h1 _ (foldL_den C m f g) (foldL_num C m f g) (foldInt_lip C m f g) (foldInt_fc C m f g))
    (riemannIntegral_certif_irrel _ _ h2 _ (foldL_den C m g f) (foldL_num C m g f) (foldInt_lip C m g f) (foldInt_fc C m g f))

/-- **★ `primeFoldDirect_m(f,g) = −Λ(n)·(B_n(f,g) + B_n(g,f))`** (`m < X`). -/
theorem primeFoldDirect_eq_BForm (C : NormCtx) (m : Nat) (hm : m < C.X) (f g : L2Test) :
    Req (primeFoldDirect C m f g)
        (Rneg (Rmul (vonMangoldt (m + 1))
          (Radd (BForm f g (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                   C.a C.han C.had C.w C.hw C.hwn)
                (BForm g f (⟨((m + 1 : Nat) : Int), 1⟩ : Q) (Int.ofNat_pos.mpr (Nat.succ_pos m)) Nat.one_pos
                   C.a C.han C.had C.w C.hw C.hwn)))) := by
  refine Req_trans (primeFoldDirect_eq C m f g) (Rneg_congr ?_)
  refine Req_trans (Rmul_assoc _ _ _) (Rmul_congr (Req_refl _) ?_)
  refine Req_trans (Rmul_distrib _ _ _) ?_
  exact Radd_congr (Req_symm (BForm_eq_w_foldInt C m hm f g)) (Req_symm (BForm_eq_w_foldInt C m hm g f))

-- ===========================================================================
-- (5) The folded prime Gram and its identification with `−PrimeForm` on the core.
-- ===========================================================================

/-- **The folded prime Gram** `Σ_{m<X} ∫₀¹ 2Λ(m+1)·w·r·⟨Φ_f, MΦ_g⟩`. -/
def primeFoldGram (C : NormCtx) (f g : L2Test) : Real :=
  RsumN (fun m => primeFoldDirect C m f g) C.X

/-- **★ `primeFoldGram(f,g) = −PrimeForm_X(f,g)` on the core** (fold + readback at every place). -/
theorem primeFoldGram_eq_neg_PrimeForm (C : NormCtx) (f g : ClosedCore C) :
    Req (primeFoldGram C f.1 g.1) (Rneg (PrimeForm C.X f.1 g.1 C.a C.han C.had C.w C.hw C.hwn)) := by
  unfold primeFoldGram
  refine Req_trans (RsumN_congr C.X (fun m hm =>
    Req_trans (primeFoldDirect_eq_BForm C m hm f.1 g.1) (Rneg_congr (Req_symm (PForm_fold C m f.1 g.1 f.2 g.2))))) ?_
  exact RsumN_Rneg _ C.X

end UOR.Bridge.F1Square.Square
