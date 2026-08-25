/-
F1 square — **the Atlas atom of a single weighted product** (`AtlasGammaAtom.lean`).

For a sourced real coefficient `c` and two raw single-test evaluations `u, v` (reals), the
ATOM is the mixed cut/cycle fiber vector at address `(d, ℓ)`

    `A = (c·u − v)/4`,   `B = (c·u + v)/4`,   `Γ_{c}(u, v) = p_ℓ(A) + q_{d,ℓ}(B)`,

and THE LOAD-BEARING ATOMIC IDENTITY (`gammaAtom_readback`, uniformly in the address):

    `[Γ_c(u_f, v_f), Γ_c(u_g, v_g)]_M = −(c/2)·(u_f·v_g + v_f·u_g)`.

The cut channel enters with the sign `+` (`[p,p] = 4AA'`) and the cycle channel with the sign `−`
of the `−I` term (`[q,q] = −4BB'`); the negative product arises from `4AA' − 4BB'` by polarization,
inside the ONE mixed expression — not as a separate stage.  Only rational scalings and the given
weight `c` are used; no square root, no target scalar, no basis, no sign hypothesis, no form.
The atom is additive in the evaluations (`gammaAtom_add`, `gammaAtom_neg`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasChannels

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (0) Real-algebra helpers.
-- ===========================================================================

/-- `1/4`. -/
def cQ : Real := ofQ (⟨1, 4⟩ : Q) (by decide)
/-- `1/2`. -/
def cH : Real := ofQ (⟨1, 2⟩ : Q) (by decide)
/-- `2`. -/
def cTwo : Real := ofQ (⟨2, 1⟩ : Q) Nat.one_pos

/-- `2·z ≈ z + z`. -/
theorem cTwo_mul (z : Real) : Req (Rmul cTwo z) (Radd z z) := by
  have h2 : Req cTwo (Radd one one) := Req_symm (Radd_ofQ_ofQ (by decide) (by decide))
  refine Req_trans (Rmul_congr h2 (Req_refl z)) ?_
  exact Req_trans (Rmul_distrib_right one one z) (Radd_congr (Rone_mul z) (Rone_mul z))

/-- `(P − v)(P' − v') ≈ (PP' + (−Pv')) + ((−vP') + vv')`. -/
theorem sub_mul_sub_ga (P v P' v' : Real) :
    Req (Rmul (Rsub P v) (Rsub P' v'))
        (Radd (Radd (Rmul P P') (Rneg (Rmul P v'))) (Radd (Rneg (Rmul v P')) (Rmul v v'))) := by
  show Req (Rmul (Radd P (Rneg v)) (Radd P' (Rneg v')))
           (Radd (Radd (Rmul P P') (Rneg (Rmul P v'))) (Radd (Rneg (Rmul v P')) (Rmul v v')))
  refine Req_trans (Rmul_distrib_right P (Rneg v) (Radd P' (Rneg v'))) ?_
  refine Radd_congr ?_ ?_
  · exact Req_trans (Rmul_distrib P P' (Rneg v')) (Radd_congr (Req_refl _) (Rmul_neg_right P v'))
  · refine Req_trans (Rmul_distrib (Rneg v) P' (Rneg v')) (Radd_congr (Rmul_neg_left v P') ?_)
    exact Req_trans (Rmul_neg_left v (Rneg v')) (Req_trans (Rneg_congr (Rmul_neg_right v v')) (Rneg_neg _))

/-- `(P + v)(P' + v') ≈ (PP' + Pv') + (vP' + vv')`. -/
theorem add_mul_add_ga (P v P' v' : Real) :
    Req (Rmul (Radd P v) (Radd P' v'))
        (Radd (Radd (Rmul P P') (Rmul P v')) (Radd (Rmul v P') (Rmul v v'))) :=
  Req_trans (Rmul_distrib_right P v (Radd P' v'))
    (Radd_congr (Rmul_distrib P P' v') (Rmul_distrib v P' v'))

/-- `(−x) − x ≈ −(x + x)`. -/
theorem neg_sub_self_ga (x : Real) : Req (Rsub (Rneg x) x) (Rneg (Radd x x)) :=
  Req_symm (Rneg_Radd x x)

/-- **Polarization core**: `(P−v)(P'−v') − (P+v)(P'+v') ≈ −(2·(Pv' + vP'))`. -/
theorem polar_core_ga (P v P' v' : Real) :
    Req (Rsub (Rmul (Rsub P v) (Rsub P' v')) (Rmul (Radd P v) (Radd P' v')))
        (Rneg (Rmul cTwo (Radd (Rmul P v') (Rmul v P')))) := by
  refine Req_trans (Rsub_congr (sub_mul_sub_ga P v P' v') (add_mul_add_ga P v P' v')) ?_
  refine Req_trans (Rsub_Radd_Radd _ _ _ _) ?_
  refine Req_trans (Radd_congr (Rsub_Radd_Radd _ _ _ _) (Rsub_Radd_Radd _ _ _ _)) ?_
  -- ((PP' − PP') + (−Pv' − Pv')) + ((−vP' − vP') + (vv' − vv'))
  refine Req_trans (Radd_congr
    (Radd_congr (Radd_neg (Rmul P P')) (neg_sub_self_ga (Rmul P v')))
    (Radd_congr (neg_sub_self_ga (Rmul v P')) (Radd_neg (Rmul v v')))) ?_
  refine Req_trans (Radd_congr (Req_trans (Radd_comm _ _) (Radd_zero _)) (Radd_zero _)) ?_
  -- −(a + a) + −(b + b) ≈ −(2(a + b))
  refine Req_trans (Req_symm (Rneg_Radd _ _)) (Rneg_congr ?_)
  refine Req_trans (Radd_swap _ _ _ _) ?_
  exact Req_symm (cTwo_mul _)

/-- `4·((¼X)(¼X')) ≈ ¼·(XX')`. -/
theorem quarter_collapse_ga (X X' : Real) :
    Req (Rmul c4 (Rmul (Rmul cQ X) (Rmul cQ X'))) (Rmul cQ (Rmul X X')) := by
  refine Req_trans (Rmul_congr (Req_refl c4) (mul4_swap_ch cQ X cQ X')) ?_
  refine Req_trans (Req_symm (Rmul_assoc c4 (Rmul cQ cQ) (Rmul X X'))) ?_
  refine Rmul_congr ?_ (Req_refl _)
  refine Req_trans (Rmul_congr (Req_refl c4) (Rmul_ofQ_ofQ (by decide) (by decide))) ?_
  refine Req_trans (Rmul_ofQ_ofQ Nat.one_pos _) ?_
  exact ofQ_congr _ (by decide) (by decide)

/-- `¼·(−(2z)) ≈ −(½·z)`. -/
theorem quarter_neg_two_ga (z : Real) :
    Req (Rmul cQ (Rneg (Rmul cTwo z))) (Rneg (Rmul cH z)) := by
  refine Req_trans (Rmul_neg_right _ _) (Rneg_congr ?_)
  refine Req_trans (Req_symm (Rmul_assoc cQ cTwo z)) (Rmul_congr ?_ (Req_refl z))
  exact Req_trans (Rmul_ofQ_ofQ (by decide) Nat.one_pos) (ofQ_congr _ (by decide) (by decide))

-- ===========================================================================
-- (1) The atom.
-- ===========================================================================

/-- `A = (c·u − v)/4`. -/
def aCoefGa (c u v : Real) : Real := Rmul cQ (Rsub (Rmul c u) v)
/-- `B = (c·u + v)/4`. -/
def bCoefGa (c u v : Real) : Real := Rmul cQ (Radd (Rmul c u) v)

/-- **THE ATOM** `Γ_c(u,v) = p_ℓ(A) + q_{d,ℓ}(B)` at address `(d, ℓ)`. -/
def gammaAtom (d ℓ : Nat) (c u v : Real) : Nat → Nat → Real :=
  fun i j => Radd (pCh ℓ (aCoefGa c u v) i j) (qCh d ℓ (bCoefGa c u v) i j)

/-- Left additivity of the pairing. -/
theorem pairF_add_left (v v' w : Nat → Nat → Real) :
    Req (pairF (fun i j => Radd (v i j) (v' i j)) w) (Radd (pairF v w) (pairF v' w)) :=
  Req_trans (pairF_comm _ _)
    (Req_trans (pairF_add_right w v v') (Radd_congr (pairF_comm w v) (pairF_comm w v')))

/-- The bilinear expansion of `[p(A) + q(B), M(p(A') + q(B'))]`. -/
theorem gamma_bilinear (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (A B A' B' : Real) :
    Req (pairF (fun i j => Radd (pCh ℓ A i j) (qCh d ℓ B i j))
               (atlasOp (fun i j => Radd (pCh ℓ A' i j) (qCh d ℓ B' i j))))
        (Rsub (Rmul c4 (Rmul A A')) (Rmul c4 (Rmul B B'))) := by
  refine Req_trans (pairF_congr (fun _ _ _ _ => Req_refl _)
    (fun i j _ _ => atlasOp_add (pCh ℓ A') (qCh d ℓ B') i j)) ?_
  refine Req_trans (pairF_add_right _ (atlasOp (pCh ℓ A')) (atlasOp (qCh d ℓ B'))) ?_
  refine Req_trans (Radd_congr (pairF_add_left (pCh ℓ A) (qCh d ℓ B) _)
    (pairF_add_left (pCh ℓ A) (qCh d ℓ B) _)) ?_
  refine Req_trans (Radd_congr (Radd_congr (pCh_pCh ℓ hℓ A A') (qCh_pCh d ℓ hd hℓ B A'))
    (Radd_congr (pCh_qCh d ℓ hd hℓ A B') (qCh_qCh d ℓ hd hℓ B B'))) ?_
  refine Req_trans (Radd_congr (Radd_zero _) (Req_trans (Radd_comm _ _) (Radd_zero _))) ?_
  exact Req_refl _

/-- **★ THE ATOMIC IDENTITY** `[Γ_c(u_f,v_f), Γ_c(u_g,v_g)]_M = −(c/2)·(u_f v_g + v_f u_g)`, at every
    valid address (address-independent readback). -/
theorem gammaAtom_readback (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (c uf vf ug vg : Real) :
    Req (pairF (gammaAtom d ℓ c uf vf) (atlasOp (gammaAtom d ℓ c ug vg)))
        (Rneg (Rmul (Rmul cH c) (Radd (Rmul uf vg) (Rmul vf ug)))) := by
  refine Req_trans (gamma_bilinear d ℓ hd hℓ _ _ _ _) ?_
  unfold aCoefGa bCoefGa
  refine Req_trans (Rsub_congr (quarter_collapse_ga _ _) (quarter_collapse_ga _ _)) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib cQ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_refl cQ) (polar_core_ga (Rmul c uf) vf (Rmul c ug) vg)) ?_
  refine Req_trans (quarter_neg_two_ga _) (Rneg_congr ?_)
  -- ½·((cu)v' + v(cu')) ≈ (½c)·(uv' + vu')
  refine Req_trans (Rmul_congr (Req_refl cH)
    (Radd_congr (Rmul_assoc c uf vg) (Req_trans (Rmul_comm vf (Rmul c ug))
      (Req_trans (Rmul_assoc c ug vf) (Rmul_congr (Req_refl c) (Rmul_comm ug vf)))))) ?_
  refine Req_trans (Rmul_congr (Req_refl cH) (Req_symm (Rmul_distrib c _ _))) ?_
  exact Req_symm (Rmul_assoc cH c _)

-- ===========================================================================
-- (2) Additivity in the evaluations (single-test linearity of the atom).
-- ===========================================================================

theorem aCoef_add (c u v u' v' : Real) :
    Req (aCoefGa c (Radd u u') (Radd v v')) (Radd (aCoefGa c u v) (aCoefGa c u' v')) := by
  unfold aCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) ?_) (Rmul_distrib cQ _ _)
  show Req (Radd (Rmul c (Radd u u')) (Rneg (Radd v v')))
           (Radd (Radd (Rmul c u) (Rneg v)) (Radd (Rmul c u') (Rneg v')))
  refine Req_trans (Radd_congr (Rmul_distrib c u u') (Rneg_Radd v v')) ?_
  exact Radd_swap _ _ _ _

theorem bCoef_add (c u v u' v' : Real) :
    Req (bCoefGa c (Radd u u') (Radd v v')) (Radd (bCoefGa c u v) (bCoefGa c u' v')) := by
  unfold bCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) ?_) (Rmul_distrib cQ _ _)
  refine Req_trans (Radd_congr (Rmul_distrib c u u') (Req_refl _)) ?_
  exact Radd_swap _ _ _ _

/-- **Additivity of the atom in the evaluations**. -/
theorem gammaAtom_add (d ℓ : Nat) (c u v u' v' : Real) (i j : Nat) :
    Req (gammaAtom d ℓ c (Radd u u') (Radd v v') i j)
        (Radd (gammaAtom d ℓ c u v i j) (gammaAtom d ℓ c u' v' i j)) := by
  unfold gammaAtom
  refine Req_trans (Radd_congr
    (Req_trans (pCh_congr_ga ℓ (aCoef_add c u v u' v') i j) (pCh_add ℓ _ _ i j))
    (Req_trans (qCh_congr_ga d ℓ (bCoef_add c u v u' v') i j) (qCh_add d ℓ _ _ i j))) ?_
  exact Radd_swap _ _ _ _
where
  pCh_congr_ga (ℓ : Nat) {x x' : Real} (h : Req x x') (i j : Nat) : Req (pCh ℓ x i j) (pCh ℓ x' i j) :=
    Rmul_congr h (Req_refl _)
  qCh_congr_ga (d ℓ : Nat) {x x' : Real} (h : Req x x') (i j : Nat) : Req (qCh d ℓ x i j) (qCh d ℓ x' i j) :=
    Rmul_congr (Rmul_congr h (Req_refl _)) (Req_refl _)

theorem aCoef_neg (c u v : Real) : Req (aCoefGa c (Rneg u) (Rneg v)) (Rneg (aCoefGa c u v)) := by
  unfold aCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) ?_) (Rmul_neg_right cQ _)
  show Req (Radd (Rmul c (Rneg u)) (Rneg (Rneg v))) (Rneg (Radd (Rmul c u) (Rneg v)))
  refine Req_trans (Radd_congr (Rmul_neg_right c u) (Req_refl _)) ?_
  exact Req_symm (Rneg_Radd _ _)

theorem bCoef_neg (c u v : Real) : Req (bCoefGa c (Rneg u) (Rneg v)) (Rneg (bCoefGa c u v)) := by
  unfold bCoefGa
  refine Req_trans (Rmul_congr (Req_refl cQ) ?_) (Rmul_neg_right cQ _)
  refine Req_trans (Radd_congr (Rmul_neg_right c u) (Req_refl _)) ?_
  exact Req_symm (Rneg_Radd _ _)

/-- **Negation of the atom in the evaluations**. -/
theorem gammaAtom_neg (d ℓ : Nat) (c u v : Real) (i j : Nat) :
    Req (gammaAtom d ℓ c (Rneg u) (Rneg v) i j) (Rneg (gammaAtom d ℓ c u v i j)) := by
  unfold gammaAtom
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_congr (aCoef_neg c u v) (Req_refl _)) (Rmul_neg_left _ _))
    (Req_trans (Rmul_congr (Rmul_congr (bCoef_neg c u v) (Req_refl _)) (Req_refl _))
      (Req_trans (Rmul_congr (Rmul_neg_left _ _) (Req_refl _)) (Rmul_neg_left _ _)))) ?_
  exact Req_symm (Rneg_Radd _ _)

/-- The atom vanishes at zero evaluations. -/
theorem gammaAtom_zero (d ℓ : Nat) (c : Real) (i j : Nat) :
    Req (gammaAtom d ℓ c zero zero i j) zero := by
  unfold gammaAtom
  have hA : Req (aCoefGa c zero zero) zero := by
    unfold aCoefGa
    refine Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Rsub_congr (Rmul_zero c) (Req_refl _)) (Radd_neg zero))) ?_
    exact Rmul_zero cQ
  have hB : Req (bCoefGa c zero zero) zero := by
    unfold bCoefGa
    refine Req_trans (Rmul_congr (Req_refl cQ) (Req_trans (Radd_congr (Rmul_zero c) (Req_refl _)) (Radd_zero zero))) ?_
    exact Rmul_zero cQ
  refine Req_trans (Radd_congr
    (Req_trans (Rmul_congr hA (Req_refl _)) (Rzero_mul_ch _))
    (Req_trans (Rmul_congr (Req_trans (Rmul_congr hB (Req_refl _)) (Rzero_mul_ch _)) (Req_refl _)) (Rzero_mul_ch _))) ?_
  exact Radd_zero zero

end UOR.Bridge.F1Square.Square
