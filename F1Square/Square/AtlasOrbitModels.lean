/-
F1 square — **pointwise recovery presentations of the cycle coordinates** (`AtlasOrbitModels.lean`, target-free).

Coordinate lemmas only.  The cycle coordinates of each channel are expressed pointwise through cut coordinates:

PRESENTATION 1 (same site): prime cycle (n,t) = pole cut (n,t) (`model1_prime`, the swap); const cycle (s) =
far cut (·,s) (`model1_const`); pole cycle (x,s) = pole cut (x,s) − far cut (·,s) (`model1_pole`);
tail cycle (x,s) = tail cut (x,s) + (1/x)·far cut (·,s) (`model1_tail`).
PRESENTATION 2 (one weighted identity at one coupling address `n·s = x·t`, band/window hypotheses):
`invSq(x)·prime cycle (n,t) = invSq(n)·(pole cut (x,s) − ½·far cut (·,s)) + invSq(x)·½·far cut (·,t)`
(`model2_prime`, from `decode_orbit_equivariance`).  `model2_mix` is a generic affine-combination lemma
(`θ₁ + θ₂ = 1`, no sign condition); it is NOT instantiated with coupling addresses and contains no density,
integral, measure, or operator.

HONEST SCOPE.  These are pointwise identities, not operators: no complete five-channel map `A_k → C_k` is
constructed here, nothing shows the two presentations differ on source-coherent inputs (orbit equivariance
indicates they are different readings of the same source-restricted functional), and no statement about
transport densities, boundary error, boundedness, or uniqueness is made or proved.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasOrbitDecode
import F1Square.Square.AtlasDefectGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- The pole cut coordinate at a site: `A(posFiber U V) = (U + V)/4`. -/
def poleCutTp (U V : Real) : Real := aCoefGa one U (Rneg V)
/-- The far cut coordinate at a Haar coordinate: `A(posFiber V V) = V/2`. -/
def farCutTp (V : Real) : Real := aCoefGa one V (Rneg V)
/-- The tail cut coordinate `A(negFiber Z W) = (Z − W)/4`. -/
def tailCutTp (Z W : Real) : Real := aCoefGa one Z W
/-- The prime cycle coordinate `B(negFiber U V) = (U + V)/4`. -/
def primeCycTp (U V : Real) : Real := bCoefGa one U V
def poleCycTp (U V : Real) : Real := bCoefGa one U (Rneg V)
def constCycTp (V : Real) : Real := bCoefGa one V V
def tailCycTp (Z W : Real) : Real := bCoefGa one Z W

-- ===========================================================================
-- (1) PRESENTATION 1: the same-site recovery identities.
-- ===========================================================================

theorem model1_prime (U V : Real) : Req (primeCycTp U V) (poleCutTp U V) := Req_symm (pole_cut_eq_prime_cycle U V)

theorem model1_const (V : Real) : Req (constCycTp V) (farCutTp V) :=
  Req_trans (negFiber_VV_cycle V) (Req_symm (posFiber_VV_cut V))

theorem aCoefGa_one (u v : Real) : Req (aCoefGa one u v) (Rmul cQ (Rsub u v)) :=
  Rmul_congr (Req_refl cQ) (Rsub_congr (Rone_mul u) (Req_refl v))
theorem bCoefGa_one (u v : Real) : Req (bCoefGa one u v) (Rmul cQ (Radd u v)) :=
  Rmul_congr (Req_refl cQ) (Radd_congr (Rone_mul u) (Req_refl v))

/-- `(U − V)/4 = (U + V)/4 − V/2`. -/
theorem model1_pole (U V : Real) : Req (poleCycTp U V) (Rsub (poleCutTp U V) (farCutTp V)) := by
  unfold poleCycTp poleCutTp farCutTp
  refine Req_trans (bCoefGa_one _ _) (Req_symm ?_)
  refine Req_trans (Rsub_congr (aCoefGa_one _ _) (aCoefGa_one _ _)) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib cQ _ _)) (Rmul_congr (Req_refl cQ) ?_)
  -- (U − (−V)) − (V − (−V)) ≈ U + (−V)
  refine Req_trans (Rsub_congr (Radd_congr (Req_refl U) (Rneg_neg V)) (Radd_congr (Req_refl V) (Rneg_neg V))) ?_
  refine Req_trans (Rsub_Radd_Radd U V V V) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg V)) (Radd_zero _)

/-- `(Z + W)/4 = (Z − W)/4 + r·(V/2)` for `W = r·V`. -/
theorem model1_tail (Z r V : Real) :
    Req (tailCycTp Z (Rmul r V)) (Radd (tailCutTp Z (Rmul r V)) (Rmul r (farCutTp V))) := by
  unfold tailCycTp tailCutTp farCutTp
  refine Req_trans (bCoefGa_one _ _) (Req_symm ?_)
  refine Req_trans (Radd_congr (aCoefGa_one _ _) (Rmul_congr (Req_refl r) (aCoefGa_one _ _))) ?_
  -- r·(¼(V − (−V))) ≈ ¼(rV + rV)
  have h : Req (Rmul r (Rmul cQ (Rsub V (Rneg V)))) (Rmul cQ (Radd (Rmul r V) (Rmul r V))) := by
    refine Req_trans (Rmul_congr (Req_refl r) (Rmul_congr (Req_refl cQ) (Radd_congr (Req_refl V) (Rneg_neg V)))) ?_
    refine Req_trans (Req_symm (Rmul_assoc r cQ _)) (Req_trans (Rmul_congr (Rmul_comm r cQ) (Req_refl _)) (Req_trans (Rmul_assoc cQ r _) ?_))
    exact Rmul_congr (Req_refl cQ) (Rmul_distrib r V V)
  refine Req_trans (Radd_congr (Req_refl _) h) ?_
  refine Req_trans (Req_symm (Rmul_distrib cQ _ _)) (Rmul_congr (Req_refl cQ) ?_)
  -- (Z − W) + (W + W) ≈ Z + W
  refine Req_trans (Radd_assoc _ _ _) (Radd_congr (Req_refl Z) ?_)
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) ?_
  exact Req_trans (Radd_congr (Req_trans (Radd_comm _ _) (Radd_neg _)) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _))

-- ===========================================================================
-- (2) PRESENTATION 2: the orbit-shifted recovery identity on a coupling address.
-- ===========================================================================

/-- **Presentation 2**: on a coupling address `n·s = x·t` (band/window hypotheses as in `decode_orbit_equivariance`),
    `invSq(x)·primeCycTp(n,t) = invSq(n)·(poleCutTp(x,s) − ½·farCutTp(s)) + invSq(x)·(½·farCutTp(t))`. -/
theorem model2_prime (C : NormCtx) (f : L2Test) (c : CouplingAddr)
    (hnS : Rle c.fin.n.r (ofQ C.S C.hSd)) (hxS : Rle c.arch.xr (ofQ C.S C.hSd))
    (ht : Rle (ofQ C.a C.had) c.fin.tr) (hs : Rle (ofQ C.a C.had) c.arch.sr) :
    Req (Rmul (invSq C c.arch.xr) (primeCycTp (Uc C c.fin.n.r f c.fin.tr) (Vc C f c.fin.tr)))
        (Radd (Rmul (invSq C c.fin.n.r)
                (Rsub (poleCutTp (Uc C c.arch.xr f c.arch.sr) (Vc C f c.arch.sr)) (Rmul cH (farCutTp (Vc C f c.arch.sr)))))
              (Rmul (invSq C c.arch.xr) (Rmul cH (farCutTp (Vc C f c.fin.tr))))) := by
  have heq := decode_orbit_equivariance C f c hnS hxS ht hs
  -- abbreviations
  unfold primeCycTp poleCutTp farCutTp
  -- LHS = invSq x · ¼(U_n + V_t) = ¼(invSq x·U_n) + ¼(invSq x·V_t)
  refine Req_trans (Rmul_congr (Req_refl _) (bCoefGa_one _ _)) ?_
  -- RHS pieces: poleCutTp − ½ farCutTp = ¼(U_x + V_s) − ½·½(V_s + V_s)·… = ¼U_x
  have hpc : Req (Rsub (aCoefGa one (Uc C c.arch.xr f c.arch.sr) (Rneg (Vc C f c.arch.sr)))
                       (Rmul cH (aCoefGa one (Vc C f c.arch.sr) (Rneg (Vc C f c.arch.sr)))))
                 (Rmul cQ (Uc C c.arch.xr f c.arch.sr)) := by
    refine Req_trans (Rsub_congr (Req_trans (aCoefGa_one _ _) (Rmul_congr (Req_refl cQ) (Radd_congr (Req_refl _) (Rneg_neg _))))
      (Rmul_congr (Req_refl cH) (posFiber_VV_cut _))) ?_
    -- ¼(U + V) − ½(½V) ≈ ¼U
    have h2 : Req (Rmul cH (Rmul cH (Vc C f c.arch.sr))) (Rmul cQ (Vc C f c.arch.sr)) :=
      Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (by decide) (by decide))
        (ofQ_congr (a := mul (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)) (b := (⟨1, 4⟩ : Q)) (Qmul_den_pos (by decide) (by decide)) (by decide) (by decide))) (Req_refl _))
    refine Req_trans (Rsub_congr (Rmul_distrib cQ _ _) h2) ?_
    exact Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _))
  have hft : Req (Rmul cH (aCoefGa one (Vc C f c.fin.tr) (Rneg (Vc C f c.fin.tr)))) (Rmul cQ (Vc C f c.fin.tr)) :=
    Req_trans (Rmul_congr (Req_refl cH) (posFiber_VV_cut _))
      (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (by decide) (by decide))
        (ofQ_congr (a := mul (⟨1, 2⟩ : Q) (⟨1, 2⟩ : Q)) (b := (⟨1, 4⟩ : Q)) (Qmul_den_pos (by decide) (by decide)) (by decide) (by decide))) (Req_refl _)))
  refine Req_symm (Req_trans (Radd_congr (Rmul_congr (Req_refl _) hpc) (Rmul_congr (Req_refl _) hft)) ?_)
  -- invSq n·(¼U_x) + invSq x·(¼V_t) ≈ invSq x·(¼(U_n + V_t))
  refine Req_trans (Radd_congr (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))
                               (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _)))) ?_
  refine Req_trans (Req_symm (Rmul_distrib cQ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_refl cQ) (Radd_congr (Req_symm heq) (Req_refl _))) ?_
  refine Req_trans (Rmul_congr (Req_refl cQ) (Req_symm (Rmul_distrib _ _ _))) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

-- ===========================================================================
-- (3) An affine-combination lemma (generic; not an operator statement).
-- ===========================================================================

/-- A generic affine-combination lemma: two readings `R₁ = w₁·P`, `R₂ = w₂·P` combined with `θ₁ + θ₂ = 1`
    (no sign condition) satisfy `θ₁·w₂·R₁ + θ₂·w₁·R₂ = w₁·w₂·P`.  Not instantiated with coupling addresses. -/
theorem model2_mix (w₁ w₂ P R₁ R₂ θ₁ θ₂ : Real) (hθ : Req (Radd θ₁ θ₂) one)
    (h₁ : Req (Rmul w₁ P) R₁) (h₂ : Req (Rmul w₂ P) R₂) :
    Req (Radd (Rmul θ₁ (Rmul w₂ R₁)) (Rmul θ₂ (Rmul w₁ R₂))) (Rmul (Rmul w₁ w₂) P) := by
  refine Req_trans (Radd_congr (Rmul_congr (Req_refl θ₁) (Rmul_congr (Req_refl w₂) (Req_symm h₁)))
                               (Rmul_congr (Req_refl θ₂) (Rmul_congr (Req_refl w₁) (Req_symm h₂)))) ?_
  -- θ₁·(w₂·(w₁ P)) + θ₂·(w₁·(w₂ P)) ≈ (θ₁ + θ₂)·((w₁w₂)P)
  have e1 : Req (Rmul w₂ (Rmul w₁ P)) (Rmul (Rmul w₁ w₂) P) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_comm _ _) (Req_refl _))
  have e2 : Req (Rmul w₁ (Rmul w₂ P)) (Rmul (Rmul w₁ w₂) P) := Req_symm (Rmul_assoc _ _ _)
  refine Req_trans (Radd_congr (Rmul_congr (Req_refl _) e1) (Rmul_congr (Req_refl _) e2)) ?_
  refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) ?_
  exact Req_trans (Rmul_congr hθ (Req_refl _)) (Rone_mul _)

end UOR.Bridge.F1Square.Square
