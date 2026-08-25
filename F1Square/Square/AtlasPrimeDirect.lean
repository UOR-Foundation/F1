/-
F1 square — **THE POSITIVE-MEASURE DIRECT-INTEGRAL REALIZATION OF THE PRIME FORM**
(`AtlasPrimeDirect.lean`).

ONE FIXED, WEIGHT-FREE FIELD.  The fiber field of a raw test `f` at the point `t` of the Haar window is

    `Φ_f(t) = negFiber (d,ℓ) (u(f)(t)) (v(f)(t))`,   `negFiber d ℓ u v = gammaAtom d ℓ 1 u v`,

i.e. `p((u − v)/4) + q((u + v)/4)` with the RAW single-test Haar evaluations
`u(f)(t) = f(q/max(t,a))`, `v(f)(t) = f(1/max(t,a))` — no quadrature weight, no κ, no density inside Γ.
The weight and the Haar density stay OUTSIDE, as the NONNEGATIVE measure on the window

    `dμ_{m,side}(t) = κ_{m,side} · (1/max(t,a)) dt`,   `κ_{m,0} = Λ(m+1)·(m+1)^{-1/2}`,  `κ_{m,1} = Λ(m+1)·(m+1)^{-1}·(m+1)^{1/2}`

(`placeKappa_nonneg`, `primeMeasure_nonneg`).  The place/side direct integral is

    `primeDirect(f,g) = ∫_window ⟨Φ_f(t), M Φ_g(t)⟩ dμ(t)`   (certified; `= w·∫₀¹` of the pulled-back integrand),

and its dyadic stages are the Riemann sums of THIS ONE field sampled at the dyadic points — nothing signed
is appended (`primeCutDyadic_RReg`, `primeCycleDyadic_RReg` are the regularity of those stages).

THE SPLIT AND THE SIGNS.  `⟨Φ_f, MΦ_g⟩ = ⟨BΦ_f, BΦ_g⟩ − ⟨Φ_f, Φ_g⟩ = 4A_fA_g − 4B_fB_g` pointwise, so

    `atlasPrimeDirect = atlasPrimeCut − atlasPrimeCycle`   (`atlasPrimeDirect_split`),

with `atlasPrimeCut(f,f) ≥ 0` and `atlasPrimeCycle(f,f) ≥ 0` (`atlasPrimeCut_nonneg`, `atlasPrimeCycle_nonneg`):
BOTH masses are genuine positive semidefinite direct integrals; the prime form is their DIFFERENCE:

    `atlasPrimeDirect(f,g) = −½·(PrimeForm_X(f,g) + PrimeForm_X(g,f))`   (all tests, `atlasPrimeDirect_eq`),
    `atlasPrimeDirect(f,g) = −PrimeForm_X(f,g)`   on `ClosedCore C`   (`atlasPrimeDirect_eq_neg_PrimeForm`).

HONEST SCOPE: a realization of `−PrimeForm` as (cut Gram) − (cycle Gram) of one field against a
positive measure.  No range law, no contraction, no bound on `CoupledForm`; `CurrentArchDominatesPrime`
is untouched.  Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasPrimeDyadicReadback
import F1Square.Analysis.CosSinBound

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) The weight-free fibers.
-- ===========================================================================

/-- `negFiber d ℓ u v = p((u−v)/4) + q((u+v)/4)` — reads back `−½(u_f v_g + v_f u_g)`. -/
def negFiber (d ℓ : Nat) (u v : Real) : Nat → Nat → Real := gammaAtom d ℓ one u v

/-- `posFiber d ℓ u v = negFiber d ℓ u (−v)` — reads back `+½(u_f v_g + v_f u_g)`. -/
def posFiber (d ℓ : Nat) (u v : Real) : Nat → Nat → Real := gammaAtom d ℓ one u (Rneg v)

theorem negFiber_readback (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (uf vf ug vg : Real) :
    Req (pairF (negFiber d ℓ uf vf) (atlasOp (negFiber d ℓ ug vg)))
        (Rneg (Rmul cH (Radd (Rmul uf vg) (Rmul vf ug)))) :=
  Req_trans (gammaAtom_readback d ℓ hd hℓ one uf vf ug vg)
    (Rneg_congr (Rmul_congr (Rmul_one cH) (Req_refl _)))

theorem posFiber_readback (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (uf vf ug vg : Real) :
    Req (pairF (posFiber d ℓ uf vf) (atlasOp (posFiber d ℓ ug vg)))
        (Rmul cH (Radd (Rmul uf vg) (Rmul vf ug))) := by
  refine Req_trans (gammaAtom_readback d ℓ hd hℓ one uf (Rneg vf) ug (Rneg vg)) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Rmul_one cH)
    (Radd_congr (Rmul_neg_right uf vg) (Rmul_neg_left vf ug)))) ?_
  refine Req_trans (Rneg_congr (Rmul_congr (Req_refl cH) (Req_symm (Rneg_Radd _ _)))) ?_
  refine Req_trans (Rneg_congr (Rmul_neg_right cH _)) ?_
  exact Rneg_neg _

/-- The pointwise split `⟨Φ_f, MΦ_g⟩ = 4A_fA_g − 4B_fB_g` (`A = (u−v)/4`, `B = (u+v)/4`). -/
theorem negFiber_split (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (uf vf ug vg : Real) :
    Req (pairF (negFiber d ℓ uf vf) (atlasOp (negFiber d ℓ ug vg)))
        (Rsub (Rmul c4 (Rmul (aCoefGa one uf vf) (aCoefGa one ug vg)))
              (Rmul c4 (Rmul (bCoefGa one uf vf) (bCoefGa one ug vg)))) :=
  gamma_bilinear d ℓ hd hℓ _ _ _ _

-- ===========================================================================
-- (2) The nonnegative measure.
-- ===========================================================================

/-- The sourced place/side weight WITHOUT the window width: `Λ(m+1)·q^{-1/2}` (side `0`),
    `Λ(m+1)·(m+1)^{-1}·q^{-1/2}` (side `1`). -/
def placeKappa (C : NormCtx) (m : Nat) : Nat → Real
  | 0 => Rmul (vonMangoldt (m + 1)) (normWeight (⟨((m + 1 : Nat) : Int), 1⟩ : Q))
  | _ => Rmul (Rmul (vonMangoldt (m + 1)) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m))) (normWeight (⟨1, m + 1⟩ : Q))

/-- The AC-17 weight is `placeKappa · w`. -/
theorem placeData_kappa (C : NormCtx) (m : Nat) : ∀ side,
    (placeData C m side).κ = Rmul (placeKappa C m side) (ofQ C.w C.hw)
  | 0 => rfl
  | (_ + 1) => rfl

theorem normWeight_nonneg_pd (q : Q) : Rnonneg (normWeight q) := by
  unfold normWeight
  by_cases h : 0 < q.num
  · rw [dif_pos h]; exact Rsqrt_nonneg _ _ _
  · rw [dif_neg h]; exact Rnonneg_ofQ (by decide) (by decide)

/-- **`κ ≥ 0`**: `Λ ≥ 0`, `q^{-1/2} ≥ 0`, `(m+1)^{-1} ≥ 0`. -/
theorem placeKappa_nonneg (C : NormCtx) (m : Nat) : ∀ side, Rnonneg (placeKappa C m side)
  | 0 => Rnonneg_Rmul (vonMangoldt_nonneg _) (normWeight_nonneg_pd _)
  | (_ + 1) => Rnonneg_Rmul (Rnonneg_Rmul (vonMangoldt_nonneg _)
      (Rnonneg_ofQ (Nat.succ_pos m) (show (0 : Int) ≤ 1 by decide))) (normWeight_nonneg_pd _)

/-- **The measure density on the window**: `μ(t) = κ · (1/max(t,a))`. -/
def primeMeasure (C : NormCtx) (m side : Nat) (t : Real) : Real := Rmul (placeKappa C m side) (rEv C t)

/-- **`μ ≥ 0`**. -/
theorem primeMeasure_nonneg (C : NormCtx) (m side : Nat) (t : Real) : Rnonneg (primeMeasure C m side t) :=
  Rnonneg_Rmul (placeKappa_nonneg C m side) (Rnonneg_clampedInv C.a C.han C.had t)

-- ===========================================================================
-- (3) The field, the pulled-back integrands, and their certificates.
-- ===========================================================================

/-- **THE FIELD** `Φ_f(t) = negFiber (u(f)(t)) (v(f)(t))` at the address gauge of the place. -/
def primeField (C : NormCtx) (m side : Nat) (f : L2Test) (t : Real) : Nat → Nat → Real :=
  negFiber (primeAddr m).1 (primeAddr m).2 (uEv C (placeData C m side) f t) (vEv C f t)

/-- The window point of `x ∈ [0,1]`. -/
def affC (C : NormCtx) (x : Real) : Real := affineMap C.a C.w C.had C.hw x

/-- The pulled-back integrand of the direct integral: `w · μ(t(x)) · ⟨Φ_f(t(x)), MΦ_g(t(x))⟩`. -/
def primePairInt (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) : Real :=
  Rmul (Rmul (ofQ C.w C.hw) (primeMeasure C m side (affC C x)))
       (pairF (primeField C m side f (affC C x)) (atlasOp (primeField C m side g (affC C x))))

/-- The cut integrand `w·μ·4A_fA_g`. -/
def cutInt (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) : Real :=
  Rmul (Rmul (ofQ C.w C.hw) (primeMeasure C m side (affC C x)))
       (Rmul c4 (Rmul (aCoefGa one (uEv C (placeData C m side) f (affC C x)) (vEv C f (affC C x)))
                      (aCoefGa one (uEv C (placeData C m side) g (affC C x)) (vEv C g (affC C x)))))

/-- The cycle integrand `w·μ·4B_fB_g`. -/
def cycInt (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) : Real :=
  Rmul (Rmul (ofQ C.w C.hw) (primeMeasure C m side (affC C x)))
       (Rmul c4 (Rmul (bCoefGa one (uEv C (placeData C m side) f (affC C x)) (vEv C f (affC C x)))
                      (bCoefGa one (uEv C (placeData C m side) g (affC C x)) (vEv C g (affC C x)))))

/-- Pointwise split. -/
theorem primePairInt_split (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) :
    Req (primePairInt C m side f g x) (Rsub (cutInt C m side f g x) (cycInt C m side f g x)) := by
  obtain ⟨hd, hℓ⟩ := primeAddr_valid m
  unfold primePairInt cutInt cycInt
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_split _ _ hd hℓ _ _ _ _)) ?_
  exact Rmul_sub_distrib _ _ _

/-- `(W(κ'r))·(−(½S)) ≈ (−(½(κ'W)))·((A r) + (A' r))`, `S = A + B'`, `B' = vf·ug`, `A' = ug·vf`. -/
theorem pair_pt_alg_pd (W κ' r uf vf ug vg : Real) :
    Req (Rmul (Rmul W (Rmul κ' r)) (Rneg (Rmul cH (Radd (Rmul uf vg) (Rmul vf ug)))))
        (Rmul (Rneg (Rmul cH (Rmul κ' W))) (Radd (Rmul (Rmul uf vg) r) (Rmul (Rmul ug vf) r))) := by
  have h1 : Req (Rmul W (Rmul κ' r)) (Rmul (Rmul κ' W) r) :=
    Req_trans (Req_symm (Rmul_assoc W κ' r)) (Rmul_congr (Rmul_comm W κ') (Req_refl r))
  have h2 : Req (Rmul (Rmul W (Rmul κ' r)) (Rmul cH (Radd (Rmul uf vg) (Rmul vf ug))))
      (Rmul (Rmul cH (Rmul κ' W)) (Rmul (Radd (Rmul uf vg) (Rmul vf ug)) r)) :=
    Req_trans (Rmul_congr h1 (Req_refl _))
      (Req_trans (mul4_swap_ch (Rmul κ' W) r cH (Radd (Rmul uf vg) (Rmul vf ug)))
        (Rmul_congr (Rmul_comm _ _) (Rmul_comm _ _)))
  refine Req_trans (Rmul_neg_right _ _) ?_
  refine Req_trans (Rneg_congr h2) ?_
  refine Req_trans (Req_symm (Rmul_neg_left _ _)) (Rmul_congr (Req_refl _) ?_)
  refine Req_trans (Rmul_distrib_right _ _ _) (Radd_congr (Req_refl _) ?_)
  exact Rmul_congr (Rmul_comm vf ug) (Req_refl r)

/-- The pulled-back pairing integrand IS the AC-17 term `gTerm` pointwise. -/
theorem primePairInt_eq_gTerm (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) :
    Req (primePairInt C m side f g x) (gTerm C f g m side x) := by
  obtain ⟨hd, hℓ⟩ := primeAddr_valid m
  unfold primePairInt gTerm omegaW hInt primeMeasure primeField affC
  rw [placeData_kappa]
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_readback _ _ hd hℓ _ _ _ _)) ?_
  exact pair_pt_alg_pd _ _ _ _ _ _ _

/-- Transport of a Lipschitz certificate along pointwise `≈`. -/
theorem lip_of_congr_pd {F G : Real → Real} {L : Q} (hLd : 0 < L.den) (h : ∀ x, Req (F x) (G x))
    (hG : ∀ x y, Rle (Rabs (Rsub (G x) (G y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) :=
  fun x y => Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (h x) (h y)))) (hG x y)

theorem fc_of_congr_pd {F G : Real → Real} (h : ∀ x, Req (F x) (G x))
    (hG : ∀ x y, Req x y → Req (G x) (G y)) : ∀ x y, Req x y → Req (F x) (F y) :=
  fun x y hxy => Req_trans (h x) (Req_trans (hG x y hxy) (Req_symm (h y)))

/-- Certificates of the pairing integrand (via `gTerm`). -/
theorem primePairInt_lip (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (primePairInt C m side f g x) (primePairInt C m side f g y)))
        (Rmul (ofQ (termL C f g m side) (termL_den C f g m side)) (Rabs (Rsub x y))) :=
  lip_of_congr_pd _ (primePairInt_eq_gTerm C m side f g) (term_lip C f g m side)
theorem primePairInt_fc (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y, Req x y →
    Req (primePairInt C m side f g x) (primePairInt C m side f g y) :=
  fc_of_congr_pd (primePairInt_eq_gTerm C m side f g) (term_fc C f g m side)

/-- The difference test `reflect_a(dilate_q f) − reflect_a f` (`.f t = u(f)(t) − v(f)(t)`). -/
def Dtest (C : NormCtx) (pd : PlaceDatum) (f : L2Test) : L2Test :=
  L2Test.sub (reflectTest C.a C.han C.had (dilateTest pd.q pd.hqn pd.hqd f)) (reflectTest C.a C.han C.had f)
/-- The sum test `reflect_a(dilate_q f) + reflect_a f` (`.f t = u(f)(t) + v(f)(t)`). -/
def Stest (C : NormCtx) (pd : PlaceDatum) (f : L2Test) : L2Test :=
  L2Test.add (reflectTest C.a C.han C.had (dilateTest pd.q pd.hqn pd.hqd f)) (reflectTest C.a C.han C.had f)

/-- The pulled-back Haar integrand of a product of two tests against the density. -/
def prodInt (C : NormCtx) (φ ψ : L2Test) (x : Real) : Real :=
  Rmul (Rmul (φ.f (affC C x)) (ψ.f (affC C x))) (rEv C (affC C x))
def prodIntL (C : NormCtx) (φ ψ : L2Test) : Q := mul (l2L (productTest φ ψ) (recipTest C.a C.han C.had)) C.w
theorem prodIntL_den (C : NormCtx) (φ ψ : L2Test) : 0 < (prodIntL C φ ψ).den := Qmul_den_pos (l2L_den _ _) C.hw
theorem prodIntL_num (C : NormCtx) (φ ψ : L2Test) : 0 ≤ (prodIntL C φ ψ).num := Int.mul_nonneg (l2L_num _ _) C.hwn
theorem prodInt_lip (C : NormCtx) (φ ψ : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (prodInt C φ ψ x) (prodInt C φ ψ y))) (Rmul (ofQ (prodIntL C φ ψ) (prodIntL_den C φ ψ)) (Rabs (Rsub x y))) :=
  affine_lip (l2L_den (productTest φ ψ) (recipTest C.a C.han C.had)) (l2L_num (productTest φ ψ) (recipTest C.a C.han C.had))
    (l2lip (productTest φ ψ) (recipTest C.a C.han C.had)) C.a C.w C.had C.hw C.hwn
theorem prodInt_fc (C : NormCtx) (φ ψ : L2Test) : ∀ x y, Req x y → Req (prodInt C φ ψ x) (prodInt C φ ψ y) :=
  fun x y h => l2fc (productTest φ ψ) (recipTest C.a C.han C.had) _ _ (affineMap_congr C.a C.w C.had C.hw h)

/-- `(W(κ'r))·(4·((¼(1u−v))(¼(1u'−v')))) ≈ ((κ'W)·¼)·((D D') r)` — the scalar pull for the cut integrand. -/
theorem cut_pt_alg_pd (W κ' r u v u' v' : Real) :
    Req (Rmul (Rmul W (Rmul κ' r)) (Rmul c4 (Rmul (Rmul cQ (Rsub (Rmul one u) v)) (Rmul cQ (Rsub (Rmul one u') v')))))
        (Rmul (Rmul (Rmul κ' W) cQ) (Rmul (Rmul (Rsub u v) (Rsub u' v')) r)) := by
  have h1 : Req (Rmul W (Rmul κ' r)) (Rmul (Rmul κ' W) r) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_comm _ _) (Req_refl _))
  have h2 : Req (Rmul c4 (Rmul (Rmul cQ (Rsub (Rmul one u) v)) (Rmul cQ (Rsub (Rmul one u') v'))))
      (Rmul cQ (Rmul (Rsub u v) (Rsub u' v'))) :=
    Req_trans (quarter_collapse_ga _ _) (Rmul_congr (Req_refl cQ)
      (Rmul_congr (Rsub_congr (Rone_mul u) (Req_refl v)) (Rsub_congr (Rone_mul u') (Req_refl v'))))
  refine Req_trans (Rmul_congr h1 h2) ?_
  refine Req_trans (mul4_swap_ch _ _ _ _) (Rmul_congr (Req_refl _) (Rmul_comm _ _))

/-- The same for the cycle integrand (`+`). -/
theorem cyc_pt_alg_pd (W κ' r u v u' v' : Real) :
    Req (Rmul (Rmul W (Rmul κ' r)) (Rmul c4 (Rmul (Rmul cQ (Radd (Rmul one u) v)) (Rmul cQ (Radd (Rmul one u') v')))))
        (Rmul (Rmul (Rmul κ' W) cQ) (Rmul (Rmul (Radd u v) (Radd u' v')) r)) := by
  have h1 : Req (Rmul W (Rmul κ' r)) (Rmul (Rmul κ' W) r) :=
    Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_comm _ _) (Req_refl _))
  have h2 : Req (Rmul c4 (Rmul (Rmul cQ (Radd (Rmul one u) v)) (Rmul cQ (Radd (Rmul one u') v'))))
      (Rmul cQ (Rmul (Radd u v) (Radd u' v'))) :=
    Req_trans (quarter_collapse_ga _ _) (Rmul_congr (Req_refl cQ)
      (Rmul_congr (Radd_congr (Rone_mul u) (Req_refl v)) (Radd_congr (Rone_mul u') (Req_refl v'))))
  refine Req_trans (Rmul_congr h1 h2) ?_
  refine Req_trans (mul4_swap_ch _ _ _ _) (Rmul_congr (Req_refl _) (Rmul_comm _ _))

/-- The cut scalar `(κ'w)/4`. -/
def cutScal (C : NormCtx) (m side : Nat) : Real := Rmul (Rmul (placeKappa C m side) (ofQ C.w C.hw)) cQ

theorem cutInt_eq (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) :
    Req (cutInt C m side f g x)
        (Rmul (cutScal C m side) (prodInt C (Dtest C (placeData C m side) f) (Dtest C (placeData C m side) g) x)) := by
  unfold cutInt primeMeasure aCoefGa cutScal prodInt Dtest
  exact cut_pt_alg_pd _ _ _ _ _ _ _

theorem cycInt_eq (C : NormCtx) (m side : Nat) (f g : L2Test) (x : Real) :
    Req (cycInt C m side f g x)
        (Rmul (cutScal C m side) (prodInt C (Stest C (placeData C m side) f) (Stest C (placeData C m side) g) x)) := by
  unfold cycInt primeMeasure bCoefGa cutScal prodInt Stest
  exact cyc_pt_alg_pd _ _ _ _ _ _ _

/-- The cut modulus `xBound(κ'w/4) · L(D_f D_g)`. -/
def cutL (C : NormCtx) (m side : Nat) (f g : L2Test) : Q :=
  mul (xBQ (cutScal C m side)) (prodIntL C (Dtest C (placeData C m side) f) (Dtest C (placeData C m side) g))
theorem cutL_den (C : NormCtx) (m side : Nat) (f g : L2Test) : 0 < (cutL C m side f g).den :=
  Qmul_den_pos Nat.one_pos (prodIntL_den _ _ _)
theorem cutL_num (C : NormCtx) (m side : Nat) (f g : L2Test) : 0 ≤ (cutL C m side f g).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (prodIntL_num _ _ _)
theorem cutInt_lip (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (cutInt C m side f g x) (cutInt C m side f g y)))
        (Rmul (ofQ (cutL C m side f g) (cutL_den C m side f g)) (Rabs (Rsub x y))) :=
  lip_of_congr_pd _ (cutInt_eq C m side f g)
    (lip_smul_fl (cutScal C m side) (prodIntL_den _ _ _) (prodIntL_num _ _ _) (prodInt_lip _ _ _))
theorem cutInt_fc (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y, Req x y →
    Req (cutInt C m side f g x) (cutInt C m side f g y) :=
  fc_of_congr_pd (cutInt_eq C m side f g) (fc_smul_fl _ (prodInt_fc _ _ _))

def cycL (C : NormCtx) (m side : Nat) (f g : L2Test) : Q :=
  mul (xBQ (cutScal C m side)) (prodIntL C (Stest C (placeData C m side) f) (Stest C (placeData C m side) g))
theorem cycL_den (C : NormCtx) (m side : Nat) (f g : L2Test) : 0 < (cycL C m side f g).den :=
  Qmul_den_pos Nat.one_pos (prodIntL_den _ _ _)
theorem cycL_num (C : NormCtx) (m side : Nat) (f g : L2Test) : 0 ≤ (cycL C m side f g).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (prodIntL_num _ _ _)
theorem cycInt_lip (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y,
    Rle (Rabs (Rsub (cycInt C m side f g x) (cycInt C m side f g y)))
        (Rmul (ofQ (cycL C m side f g) (cycL_den C m side f g)) (Rabs (Rsub x y))) :=
  lip_of_congr_pd _ (cycInt_eq C m side f g)
    (lip_smul_fl (cutScal C m side) (prodIntL_den _ _ _) (prodIntL_num _ _ _) (prodInt_lip _ _ _))
theorem cycInt_fc (C : NormCtx) (m side : Nat) (f g : L2Test) : ∀ x y, Req x y →
    Req (cycInt C m side f g x) (cycInt C m side f g y) :=
  fc_of_congr_pd (cycInt_eq C m side f g) (fc_smul_fl _ (prodInt_fc _ _ _))

-- ===========================================================================
-- (4) The direct integrals, their dyadic stages, and the split.
-- ===========================================================================

/-- **The place/side direct integral** `∫_window ⟨Φ_f, MΦ_g⟩ dμ` (as `∫₀¹` of the pulled-back integrand). -/
def primeDirect (C : NormCtx) (m side : Nat) (f g : L2Test) : Real :=
  riemannIntegral (termL_den C f g m side) (termL_num C f g m side) (primePairInt_lip C m side f g) (primePairInt_fc C m side f g)
/-- The cut direct integral `∫ 4A_fA_g dμ`. -/
def primeCut (C : NormCtx) (m side : Nat) (f g : L2Test) : Real :=
  riemannIntegral (cutL_den C m side f g) (cutL_num C m side f g) (cutInt_lip C m side f g) (cutInt_fc C m side f g)
/-- The cycle direct integral `∫ 4B_fB_g dμ`. -/
def primeCycle (C : NormCtx) (m side : Nat) (f g : L2Test) : Real :=
  riemannIntegral (cycL_den C m side f g) (cycL_num C m side f g) (cycInt_lip C m side f g) (cycInt_fc C m side f g)

/-- **The dyadic stages of the cut integral are the Riemann sums of the ONE field** (definitional):
    `D_k = 2^{-k} Σ_i w·μ(t_i)·4A_f(t_i)A_g(t_i)`. -/
theorem primeCutDyadic_field (C : NormCtx) (m side : Nat) (f g : L2Test) (k : Nat) :
    dyadicR (cutInt C m side f g) k
      = Rmul (ofQ (⟨1, 2 ^ k - 1 + 1⟩ : Q) (Nat.succ_pos _))
          (RsumN (fun i => cutInt C m side f g (ofQ (⟨(i : Int), 2 ^ k - 1 + 1⟩ : Q) (Nat.succ_pos _))) (2 ^ k - 1 + 1)) := rfl

/-- **The cut stages are a regular sequence** (Bishop-convergent to `primeCut`). -/
theorem primeCutDyadic_RReg (C : NormCtx) (m side : Nat) (f g : L2Test) :
    RReg (fun j => genSum (dyadicTerm (cutInt C m side f g)) (digammaMidx (cutL C m side f g) j)) :=
  dyadicSum_RReg (cutL_den C m side f g) (cutL_num C m side f g) (cutInt_lip C m side f g) (cutInt_fc C m side f g)

/-- **The cycle stages are a regular sequence**. -/
theorem primeCycleDyadic_RReg (C : NormCtx) (m side : Nat) (f g : L2Test) :
    RReg (fun j => genSum (dyadicTerm (cycInt C m side f g)) (digammaMidx (cycL C m side f g) j)) :=
  dyadicSum_RReg (cycL_den C m side f g) (cycL_num C m side f g) (cycInt_lip C m side f g) (cycInt_fc C m side f g)

/-- `primeCut = D_0 + lim` of its stages (definitional). -/
theorem primeCut_limit (C : NormCtx) (m side : Nat) (f g : L2Test) :
    primeCut C m side f g
      = Radd (dyadicR (cutInt C m side f g) 0)
          (Rlim (fun j => genSum (dyadicTerm (cutInt C m side f g)) (digammaMidx (cutL C m side f g) j))
            (primeCutDyadic_RReg C m side f g)) := rfl

/-- The totals over all places and sides. -/
def atlasPrimeDirect (C : NormCtx) (f g : L2Test) : Real :=
  RsumN (fun m => RsumN (fun side => primeDirect C m side f g) 2) C.X
def atlasPrimeCut (C : NormCtx) (f g : L2Test) : Real :=
  RsumN (fun m => RsumN (fun side => primeCut C m side f g) 2) C.X
def atlasPrimeCycle (C : NormCtx) (f g : L2Test) : Real :=
  RsumN (fun m => RsumN (fun side => primeCycle C m side f g) 2) C.X

/-- Negation transports a Lipschitz certificate. -/
theorem lip_neg_pd {F : Real → Real} {L : Q} (hLd : 0 < L.den)
    (hF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Rneg (F x)) (Rneg (F y)))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) := by
  intro x y
  have h : Req (Rabs (Rsub (Rneg (F x)) (Rneg (F y)))) (Rabs (Rsub (F x) (F y))) := by
    refine Req_trans (Rabs_congr (Req_trans (Radd_congr (Req_refl _) (Rneg_neg (F y))) (Radd_comm _ _))) ?_
    exact Req_trans (Rabs_congr (Req_symm (Rneg_Rsub_flip (F x) (F y)))) (Rabs_Rneg _)
  exact Rle_trans (Rle_of_Req h) (hF x y)

/-- Per place/side: `primeDirect = primeCut − primeCycle`. -/
theorem primeDirect_split (C : NormCtx) (m side : Nat) (f g : L2Test) :
    Req (primeDirect C m side f g) (Rsub (primeCut C m side f g) (primeCycle C m side f g)) := by
  -- common modulus `cutL + cycL`
  have hSd : 0 < (add (cutL C m side f g) (cycL C m side f g)).den := add_den_pos (cutL_den _ _ _ _ _) (cycL_den _ _ _ _ _)
  have hSn : 0 ≤ (add (cutL C m side f g) (cycL C m side f g)).num := Qadd_num_nonneg_loc (cutL_num _ _ _ _ _) (cycL_num _ _ _ _ _)
  have hcutS := lip_weaken_fl (cutL_den C m side f g) hSd (Qle_add_right_nonneg (cycL_num _ _ _ _ _)) (cutInt_lip C m side f g)
  have hcycS := lip_weaken_fl (cycL_den C m side f g) hSd (Qle_add_left_nonneg (cutL_num _ _ _ _ _)) (cycInt_lip C m side f g)
  have hncycS := lip_neg_pd hSd hcycS
  have hncyc_fc : ∀ x y, Req x y → Req (Rneg (cycInt C m side f g x)) (Rneg (cycInt C m side f g y)) :=
    fun x y h => Rneg_congr (cycInt_fc C m side f g x y h)
  have hsum_lip : ∀ x y, Rle (Rabs (Rsub (Radd (cutInt C m side f g x) (Rneg (cycInt C m side f g x)))
        (Radd (cutInt C m side f g y) (Rneg (cycInt C m side f g y)))))
      (Rmul (ofQ (add (cutL C m side f g) (cycL C m side f g)) hSd) (Rabs (Rsub x y))) :=
    lip_add_fl (cutL_den _ _ _ _ _) (cycL_den _ _ _ _ _) (cutInt_lip C m side f g) (lip_neg_pd (cycL_den _ _ _ _ _) (cycInt_lip C m side f g))
  have hsum_fc : ∀ x y, Req x y → Req (Radd (cutInt C m side f g x) (Rneg (cycInt C m side f g x)))
      (Radd (cutInt C m side f g y) (Rneg (cycInt C m side f g y))) :=
    fun x y h => Radd_congr (cutInt_fc C m side f g x y h) (hncyc_fc x y h)
  have hpp_lipS : ∀ x y, Rle (Rabs (Rsub (primePairInt C m side f g x) (primePairInt C m side f g y)))
      (Rmul (ofQ (add (cutL C m side f g) (cycL C m side f g)) hSd) (Rabs (Rsub x y))) :=
    lip_of_congr_pd _ (primePairInt_split C m side f g) hsum_lip
  unfold primeDirect
  refine Req_trans (riemannIntegral_certif_irrel _ _ (primePairInt_lip C m side f g) (primePairInt_fc C m side f g)
    hSd hSn hpp_lipS (primePairInt_fc C m side f g)) ?_
  refine Req_trans (riemannIntegral_congr hSd hSn hpp_lipS (primePairInt_fc C m side f g) hsum_lip hsum_fc
    (primePairInt_split C m side f g)) ?_
  refine Req_trans (riemannIntegral_add hSd hSn hcutS (cutInt_fc C m side f g) hncycS hncyc_fc hsum_lip hsum_fc) ?_
  refine Radd_congr ?_ ?_
  · exact riemannIntegral_certif_irrel hSd hSn hcutS _ (cutL_den _ _ _ _ _) (cutL_num _ _ _ _ _)
      (cutInt_lip C m side f g) (cutInt_fc C m side f g)
  · refine Req_trans (riemannIntegral_certif_irrel hSd hSn hncycS hncyc_fc (cycL_den _ _ _ _ _) (cycL_num _ _ _ _ _)
      (lip_neg_pd (cycL_den _ _ _ _ _) (cycInt_lip C m side f g)) hncyc_fc) ?_
    exact riemannIntegral_neg (cycL_den _ _ _ _ _) (cycL_num _ _ _ _ _) (cycInt_lip C m side f g) (cycInt_fc C m side f g)
      (lip_neg_pd (cycL_den _ _ _ _ _) (cycInt_lip C m side f g)) hncyc_fc

/-- **★ THE SPLIT** `atlasPrimeDirect = atlasPrimeCut − atlasPrimeCycle`. -/
theorem atlasPrimeDirect_split (C : NormCtx) (f g : L2Test) :
    Req (atlasPrimeDirect C f g) (Rsub (atlasPrimeCut C f g) (atlasPrimeCycle C f g)) := by
  unfold atlasPrimeDirect atlasPrimeCut atlasPrimeCycle
  refine Req_trans (RsumN_congr C.X (fun m _ => RsumN_congr 2 (fun side _ => primeDirect_split C m side f g))) ?_
  refine Req_trans (RsumN_congr C.X (fun m _ => RsumN_Rsub _ _ 2)) ?_
  exact RsumN_Rsub _ _ C.X

/-- **★ THE CUT MASS IS NONNEGATIVE**: `atlasPrimeCut(f,f) ≥ 0` (integrand `w·μ·4A_f² ≥ 0`, `μ ≥ 0`). -/
theorem atlasPrimeCut_nonneg (C : NormCtx) (f : L2Test) : Rnonneg (atlasPrimeCut C f f) := by
  unfold atlasPrimeCut
  refine Rnonneg_RsumN C.X (fun m _ => Rnonneg_RsumN 2 (fun side _ => ?_))
  unfold primeCut
  refine riemannIntegral_nonneg _ _ _ _ (fun x => ?_)
  unfold cutInt
  refine Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (primeMeasure_nonneg C m side _)) ?_
  exact Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _)

/-- **★ THE CYCLE MASS IS NONNEGATIVE**: `atlasPrimeCycle(f,f) ≥ 0`. -/
theorem atlasPrimeCycle_nonneg (C : NormCtx) (f : L2Test) : Rnonneg (atlasPrimeCycle C f f) := by
  unfold atlasPrimeCycle
  refine Rnonneg_RsumN C.X (fun m _ => Rnonneg_RsumN 2 (fun side _ => ?_))
  unfold primeCycle
  refine riemannIntegral_nonneg _ _ _ _ (fun x => ?_)
  unfold cycInt
  refine Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (primeMeasure_nonneg C m side _)) ?_
  exact Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_Rmul_self _)

-- ===========================================================================
-- (5) ★ THE IDENTIFICATION WITH THE PRIME FORM.
-- ===========================================================================

/-- Per place/side: the direct integral is the AC-17 weighted Haar integral. -/
theorem primeDirect_eq (C : NormCtx) (m side : Nat) (f g : L2Test) :
    Req (primeDirect C m side f g)
        (Rmul (omegaW C m side)
          (Radd (riemannIntegral (hIntL_den C (placeData C m side) f g) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _))
                (riemannIntegral (hIntL_den C (placeData C m side) g f) (hIntL_num _ _ _ _) (hInt_lip _ _ _ _) (hInt_fc _ _ _ _)))) := by
  unfold primeDirect
  refine Req_trans (riemannIntegral_congr (termL_den C f g m side) (termL_num C f g m side)
    (primePairInt_lip C m side f g) (primePairInt_fc C m side f g) (term_lip C f g m side) (term_fc C f g m side)
    (primePairInt_eq_gTerm C m side f g)) ?_
  refine Req_trans (riemannIntegral_smul_real_fl (omegaW C m side) (pairL_den C f g m side) (pairL_num C f g m side)
    (pair_lip C f g m side) (pair_fc C f g m side)) ?_
  exact Rmul_congr (Req_refl _) (integral_pair C f g m side)

/-- **★ THE DIRECT INTEGRAL IS `−½(PrimeForm(f,g) + PrimeForm(g,f))`** for ALL tests. -/
theorem atlasPrimeDirect_eq (C : NormCtx) (f g : L2Test) :
    Req (atlasPrimeDirect C f g)
        (Rneg (Rmul cH (Radd (PrimeForm C.X f g C.a C.han C.had C.w C.hw C.hwn)
                             (PrimeForm C.X g f C.a C.han C.had C.w C.hw C.hwn)))) := by
  unfold atlasPrimeDirect
  refine Req_trans (RsumN_congr C.X (fun m _ => RsumN_congr 2 (fun side _ => primeDirect_eq C m side f g))) ?_
  refine Req_trans (RsumN_congr C.X (fun m _ => place_readback C f g m)) ?_
  refine Req_trans (RsumN_Rneg _ C.X) (Rneg_congr ?_)
  refine Req_trans (RsumN_smul_ai cH _ C.X) (Rmul_congr (Req_refl cH) ?_)
  exact RsumN_Radd _ _ C.X

/-- **★ ON THE CORE: `atlasPrimeDirect(f,g) = −PrimeForm_X(f,g)`** — the prime form is realized as
    `(cut Gram) − (cycle Gram)` of the one field against the nonnegative measure. -/
theorem atlasPrimeDirect_eq_neg_PrimeForm (C : NormCtx) (f g : ClosedCore C) :
    Req (atlasPrimeDirect C f.1 g.1) (Rneg (PrimeForm C.X f.1 g.1 C.a C.han C.had C.w C.hw C.hwn)) := by
  refine Req_trans (atlasPrimeDirect_eq C f.1 g.1) (Rneg_congr ?_)
  have hsym : Req (PrimeForm C.X g.1 f.1 C.a C.han C.had C.w C.hw C.hwn)
      (PrimeForm C.X f.1 g.1 C.a C.han C.had C.w C.hw C.hwn) :=
    PrimeForm_symm C.X g.1 f.1 C.a C.han C.had C.w C.hw C.hwn C.b C.hbd C.hbnpos
      g.2.hgh g.2.hgl f.2.hgh f.2.hgl C.hfit
  refine Req_trans (Rmul_congr (Req_refl cH) (Radd_congr (Req_refl _) hsym)) ?_
  exact half_double_pd _

/-- The diagonal for every raw test: `atlasPrimeCut(f,f) − atlasPrimeCycle(f,f) = −PrimeForm(f,f)`. -/
theorem atlasPrime_diag (C : NormCtx) (f : L2Test) :
    Req (Rsub (atlasPrimeCut C f f) (atlasPrimeCycle C f f))
        (Rneg (PrimeForm C.X f f C.a C.han C.had C.w C.hw C.hwn)) :=
  Req_trans (Req_symm (atlasPrimeDirect_split C f f))
    (Req_trans (atlasPrimeDirect_eq C f f) (Rneg_congr (half_double_pd _)))

end UOR.Bridge.F1Square.Square
