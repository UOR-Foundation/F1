/-
F1 square — **THE CANONICAL ATLAS REYNOLDS COMPRESSION AND ITS FAILED READBACK** (`AtlasReynolds.lean`,
target-free).

The repository formalizes the class transforms `σ, τ, μ` only as rotation-order facts (`AtlasClasses` §3);
no complete `σ/τ/μ` representation on the 96-class carrier exists, and the scope coordinate `h₂` is absent
from `gammaAtom`.  `reyT` is the explicit row-average map on the `3 × 8` fiber,

    `(P_τ v)(i,j) = (1/8)·Σ_j v(i,j)`      (`reyT`),

the projection onto `ℓ`-constant fibers — the value a Reynolds average of a τ-rotation action would have,
but it is NOT proved here to be the average of an implemented action.  PROVED here from the fiber algebra alone:
 * `reyT_idem`, `reyT_selfadj` — `P_τ` is an idempotent, `pairF`-self-adjoint projection (external proofs,
   not structure fields);
 * `reyT_psd` — its compression of the Atlas pairing is PSD: `⟨P_τ v, M P_τ v⟩ = 8·(S² + 7·Σᵢuᵢ²) ≥ 0`;
 * `reyT_gamma` — on every source fiber `Γ_{d,ℓ}(A,B) = p_ℓ(A) + q_{d,ℓ}(B)` it kills the cycle channel and
   keeps `A/12` (address-independent: the same value at every `(d,ℓ)`, so averaging over `σ`/`μ` as well
   changes nothing);
 * `reyT_gamma_pairing` — THE COMPRESSED READBACK IS `(5/3)·A_f·A_g`: exactly `5/12` of the cut Gram, NO
   cycle Gram at all;
 * `reynolds_gamma_gap` — the readback error is `(7/3)·A_fA_g − 4·B_fB_g` pointwise on every fiber;
 * `reynolds_const_readback_gap` — on the constant channel (pure cycle) the compressed Gram is `0` and the
   error is the WHOLE channel: `constGram − reyConstGram = −ArchConstForm(f,g)`, independent of the
   truncation `k` and of any refinement stage;
 * `fiberwise_psd_const_gap` — for ANY fiberwise compression `P` with PSD compressed pairing, the
   constant-channel integrand is `≤ 0 ≤` its compression at every `t`: no fiberwise PSD compression
   reads the constant channel back.

THE FAILED READBACK OF THE FIBERWISE ROW-AVERAGE.  `reyT` is the cut projection up to the scalar `5/12`; its
constant-channel readback error is the whole channel.  This falsifies the fiberwise row-average candidate.
It does NOT show that errors from all channels cannot cancel in a total trace, and `fiberwise_psd_const_gap`
quantifies only over `Fiber → Fiber` maps — it says nothing about operators on a channel/place/scale/Haar
address.  The correct conclusion is only: the current F1 encoding acts on the internal `3 × 8` fiber and
therefore cannot express a nonlocal coupling; that coupling needs an action on the site index.
Nothing here is a positivity or dominance claim.  Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasDefectGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

def c18ry : Real := ofQ (⟨1, 8⟩ : Q) (by decide)
def c12ry : Real := ofQ (⟨1, 12⟩ : Q) (by decide)
def c53ry : Real := ofQ (⟨5, 3⟩ : Q) (by decide)
def c73ry : Real := ofQ (⟨7, 3⟩ : Q) (by decide)

theorem RofNat8_eq : Req (RofNat 8) c8 := ofQ_congr Nat.one_pos Nat.one_pos (by decide)
theorem RofNat3_eq : Req (RofNat 3) c3 := ofQ_congr Nat.one_pos Nat.one_pos (by decide)

-- ===========================================================================
-- (1) The τ-Reynolds projection: idempotent, self-adjoint, PSD compression.
-- ===========================================================================

/-- **The τ-Reynolds projection** `(P_τ v)(i,j) = (1/8)·rowSum v i`. -/
def reyT (v : Nat → Nat → Real) (i _j : Nat) : Real := Rmul c18ry (rowSum v i)

theorem rowSum_reyT (v : Nat → Nat → Real) (i : Nat) : Req (rowSum (reyT v) i) (rowSum v i) := by
  show Req (RsumN (fun _ => Rmul c18ry (rowSum v i)) 8) (rowSum v i)
  refine Req_trans (RsumN_const _ 8) ?_
  refine Req_trans (Rmul_congr RofNat8_eq (Req_refl _)) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (a := (⟨8, 1⟩ : Q)) (b := (⟨1, 8⟩ : Q)) Nat.one_pos (by decide))
    (ofQ_congr (a := mul (⟨8, 1⟩ : Q) (⟨1, 8⟩ : Q)) (b := (⟨1, 1⟩ : Q)) (Qmul_den_pos Nat.one_pos (by decide)) Nat.one_pos (by decide))) (Req_refl _)) ?_
  exact Rone_mul _

/-- `P_τ` is idempotent. -/
theorem reyT_idem (v : Nat → Nat → Real) (i j : Nat) : Req (reyT (reyT v) i j) (reyT v i j) :=
  Rmul_congr (Req_refl _) (rowSum_reyT v i)

theorem pairF_reyT_left (v w : Nat → Nat → Real) :
    Req (pairF (reyT v) w) (RsumN (fun i => Rmul (Rmul c18ry (rowSum v i)) (rowSum w i)) 3) :=
  RsumN_congr 3 (fun i _ => RsumN_smul_ai (Rmul c18ry (rowSum v i)) (fun j => w i j) 8)

/-- `P_τ` is self-adjoint for the fiber pairing. -/
theorem reyT_selfadj (v w : Nat → Nat → Real) : Req (pairF (reyT v) w) (pairF v (reyT w)) := by
  refine Req_trans (pairF_reyT_left v w) ?_
  refine Req_symm (Req_trans (RsumN_congr 3 (fun i _ => RsumN_smul_right_ai (Rmul c18ry (rowSum w i)) (fun j => v i j) 8)) ?_)
  refine RsumN_congr 3 (fun i _ => ?_)
  -- r_i·(c·s_i) ≈ (c·r_i)·s_i
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_refl _))

/-- `(X + a) − a ≈ X`. -/
theorem add_sub_cancel_ry (X a : Real) : Req (Rsub (Radd X a) a) X :=
  Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg a)) (Radd_zero _))

/-- `7u + u ≈ 8u`. -/
theorem seven_add_one_ry (u : Real) : Req (Radd (Rmul c7 u) u) (Rmul c8 u) := by
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Rone_mul u))) ?_
  refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) (Rmul_congr ?_ (Req_refl u))
  exact Req_trans (Radd_ofQ_ofQ (a := (⟨7, 1⟩ : Q)) (b := (⟨1, 1⟩ : Q)) Nat.one_pos Nat.one_pos)
    (ofQ_congr (a := add (⟨7, 1⟩ : Q) (⟨1, 1⟩ : Q)) (b := (⟨8, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos (by decide))

/-- `M` on a τ-projected fiber: `(M P_τ w)(i,j) = S' + 7·u'ᵢ` with `u'ᵢ = (1/8)rowSum w i`, `S' = Σᵢ u'ᵢ`. -/
theorem atlasOp_reyT (w : Nat → Nat → Real) (i j : Nat) :
    Req (atlasOp (reyT w) i j)
        (Radd (RsumN (fun i => Rmul c18ry (rowSum w i)) 3) (Rmul c7 (Rmul c18ry (rowSum w i)))) := by
  unfold atlasOp
  have hr : Req (rowSum (reyT w) i) (Rmul c8 (Rmul c18ry (rowSum w i))) :=
    Req_trans (RsumN_const _ 8) (Rmul_congr RofNat8_eq (Req_refl _))
  have hc : Req (colSum (reyT w) j) (RsumN (fun i => Rmul c18ry (rowSum w i)) 3) := Req_refl _
  refine Req_trans (Rsub_congr (Radd_congr hc hr) (Req_refl (reyT w i j))) ?_
  refine Req_trans (Rsub_congr (Radd_congr (Req_refl _) (Req_symm (seven_add_one_ry _))) (Req_refl _)) ?_
  refine Req_trans (Rsub_congr (Req_symm (Radd_assoc _ _ _)) (Req_refl _)) ?_
  exact add_sub_cancel_ry _ _

/-- **★ THE COMPRESSED PAIRING**: `⟨P_τ v, M P_τ w⟩ = 8·(S·S' + 7·Σᵢ uᵢu'ᵢ)`. -/
theorem pairF_reyT_M (v w : Nat → Nat → Real) :
    Req (pairF (reyT v) (atlasOp (reyT w)))
        (Rmul c8 (Radd (Rmul (RsumN (fun i => Rmul c18ry (rowSum v i)) 3) (RsumN (fun i => Rmul c18ry (rowSum w i)) 3))
                       (Rmul c7 (RsumN (fun i => Rmul (Rmul c18ry (rowSum v i)) (Rmul c18ry (rowSum w i))) 3)))) := by
  unfold pairF
  refine Req_trans (RsumN_congr 3 (fun i _ => RsumN_congr 8 (fun j _ =>
    Rmul_congr (Req_refl (reyT v i j)) (atlasOp_reyT w i j)))) ?_
  refine Req_trans (RsumN_congr 3 (fun i _ => Req_trans (RsumN_const _ 8) (Rmul_congr RofNat8_eq (Req_refl _)))) ?_
  refine Req_trans (RsumN_smul_ai c8 _ 3) (Rmul_congr (Req_refl c8) ?_)
  refine Req_trans (RsumN_congr 3 (fun i _ => Req_trans (Rmul_distrib _ _ _)
    (Radd_congr (Req_refl _) (swap_w_ac _ _ _)))) ?_
  refine Req_trans (RsumN_Radd _ _ 3) (Radd_congr ?_ (RsumN_smul_ai c7 _ 3))
  exact RsumN_smul_right_ai _ _ 3

/-- **★ THE COMPRESSION IS PSD**: `⟨P_τ v, M P_τ v⟩ ≥ 0` for every fiber. -/
theorem reyT_psd (v : Nat → Nat → Real) : Rnonneg (pairF (reyT v) (atlasOp (reyT v))) :=
  Rnonneg_congr (Req_symm (pairF_reyT_M v v))
    (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide))
      (Rnonneg_Radd (Rnonneg_Rmul_self _)
        (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (Rnonneg_RsumN 3 (fun _ _ => Rnonneg_Rmul_self _)))))

-- ===========================================================================
-- (2) The projection on the source fibers `Γ_{d,ℓ}(A,B)`: the cycle channel is killed, `A/12` remains.
-- ===========================================================================

theorem rowSum_pCh (ℓ : Nat) (hℓ : ℓ < 8) (A : Real) (i : Nat) : Req (rowSum (pCh ℓ A) i) (Rmul A c23) := by
  unfold pCh
  refine Req_trans (rowSum_tens _ _ i) (Rmul_congr (Req_refl A) ?_)
  exact Req_trans (RsumN_smul_ai c23 (indicCh ℓ) 8) (Req_trans (Rmul_congr (Req_refl _) (RsumN_indic ℓ 8 hℓ)) (Rmul_one _))

theorem RsumN_sgCh (ℓ : Nat) (hℓ : ℓ < 8) : Req (RsumN (sgCh ℓ ((ℓ + 1) % 8)) 8) zero := by
  show Req (RsumN (fun j => Rsub (indicCh ℓ j) (indicCh ((ℓ + 1) % 8) j)) 8) zero
  refine Req_trans (RsumN_Rsub _ _ 8) ?_
  refine Req_trans (Rsub_congr (RsumN_indic ℓ 8 hℓ) (RsumN_indic _ 8 (succ_mod8 ℓ hℓ).1)) ?_
  exact Radd_neg one

theorem rowSum_qCh (d ℓ : Nat) (hℓ : ℓ < 8) (B : Real) (i : Nat) : Req (rowSum (qCh d ℓ B) i) zero := by
  unfold qCh
  refine Req_trans (rowSum_tens _ _ i) ?_
  exact Req_trans (Rmul_congr (Req_refl _) (RsumN_sgCh ℓ hℓ)) (Rmul_zero _)

/-- The row sum of a source fiber is `(2/3)·A`: the cycle channel has zero row sums. -/
theorem rowSum_gamma (d ℓ : Nat) (hℓ : ℓ < 8) (c u v : Real) (i : Nat) :
    Req (rowSum (gammaAtom d ℓ c u v) i) (Rmul (aCoefGa c u v) c23) := by
  show Req (RsumN (fun j => Radd (pCh ℓ (aCoefGa c u v) i j) (qCh d ℓ (bCoefGa c u v) i j)) 8) _
  refine Req_trans (RsumN_Radd _ _ 8) ?_
  exact Req_trans (Radd_congr (rowSum_pCh ℓ hℓ _ i) (rowSum_qCh d ℓ hℓ _ i)) (Radd_zero _)

/-- **★ `P_τ Γ_{d,ℓ}(A,B) = A/12`** at every entry — the cycle coordinate `B` is gone. -/
theorem reyT_gamma (d ℓ : Nat) (hℓ : ℓ < 8) (c u v : Real) (i j : Nat) :
    Req (reyT (gammaAtom d ℓ c u v) i j) (Rmul c12ry (aCoefGa c u v)) := by
  unfold reyT
  refine Req_trans (Rmul_congr (Req_refl _) (rowSum_gamma d ℓ hℓ c u v i)) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _)))
  exact Req_trans (Rmul_ofQ_ofQ (a := (⟨1, 8⟩ : Q)) (b := (⟨2, 3⟩ : Q)) (by decide) (by decide))
    (ofQ_congr (a := mul (⟨1, 8⟩ : Q) (⟨2, 3⟩ : Q)) (b := (⟨1, 12⟩ : Q)) (Qmul_den_pos (by decide) (by decide)) (by decide) (by decide))

/-- The rational bookkeeping `8·((3α)(3α') + 7·(3·(αα'))) = 240·αα'` with `α = A/12, α' = A'/12`: `= (5/3)·AA'`. -/
theorem ry_const_alg (A A' : Real) :
    Req (Rmul c8 (Radd (Rmul (Rmul c3 (Rmul c12ry A)) (Rmul c3 (Rmul c12ry A')))
                       (Rmul c7 (Rmul c3 (Rmul (Rmul c12ry A) (Rmul c12ry A'))))))
        (Rmul c53ry (Rmul A A')) := by
  have h1 : Req (Rmul (Rmul c3 (Rmul c12ry A)) (Rmul c3 (Rmul c12ry A')))
      (Rmul (Rmul (Rmul c3 c12ry) (Rmul c3 c12ry)) (Rmul A A')) :=
    Req_trans (Rmul_congr (Req_symm (Rmul_assoc _ _ _)) (Req_symm (Rmul_assoc _ _ _))) (mul4_swap_ch _ _ _ _)
  have h2 : Req (Rmul c7 (Rmul c3 (Rmul (Rmul c12ry A) (Rmul c12ry A'))))
      (Rmul (Rmul c7 (Rmul c3 (Rmul c12ry c12ry))) (Rmul A A')) := by
    refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (mul4_swap_ch _ _ _ _))) ?_
    refine Req_trans (Rmul_congr (Req_refl _) (Req_symm (Rmul_assoc _ _ _))) ?_
    exact Req_symm (Rmul_assoc _ _ _)
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Radd_congr h1 h2) (Req_symm (Rmul_distrib_right _ _ _)))) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr ?_ (Req_refl _))
  -- the rational constant: 8·((1/4)(1/4) + 7·(3·(1/144))) = 5/3
  have k1 : Req (Rmul c3 c12ry) (ofQ (⟨1, 4⟩ : Q) (by decide)) :=
    Req_trans (Rmul_ofQ_ofQ (a := (⟨3, 1⟩ : Q)) (b := (⟨1, 12⟩ : Q)) Nat.one_pos (by decide))
      (ofQ_congr (a := mul (⟨3, 1⟩ : Q) (⟨1, 12⟩ : Q)) (b := (⟨1, 4⟩ : Q)) (Qmul_den_pos Nat.one_pos (by decide)) (by decide) (by decide))
  have k2 : Req (Rmul c12ry c12ry) (ofQ (⟨1, 144⟩ : Q) (by decide)) :=
    Req_trans (Rmul_ofQ_ofQ (a := (⟨1, 12⟩ : Q)) (b := (⟨1, 12⟩ : Q)) (by decide) (by decide))
      (ofQ_congr (a := mul (⟨1, 12⟩ : Q) (⟨1, 12⟩ : Q)) (b := (⟨1, 144⟩ : Q)) (Qmul_den_pos (by decide) (by decide)) (by decide) (by decide))
  refine Req_trans (Rmul_congr (Req_refl _) (Radd_congr (Rmul_congr k1 k1) (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) k2)))) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Radd_congr (Rmul_ofQ_ofQ (a := (⟨1, 4⟩ : Q)) (b := (⟨1, 4⟩ : Q)) (by decide) (by decide))
    (Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ (a := (⟨3, 1⟩ : Q)) (b := (⟨1, 144⟩ : Q)) Nat.one_pos (by decide)))
      (Rmul_ofQ_ofQ (a := (⟨7, 1⟩ : Q)) Nat.one_pos (Qmul_den_pos Nat.one_pos (by decide)))))) ?_
  refine Req_trans (Rmul_congr (Req_refl _) (Radd_ofQ_ofQ (Qmul_den_pos (by decide) (by decide))
    (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (by decide))))) ?_
  exact Req_trans (Rmul_ofQ_ofQ (a := (⟨8, 1⟩ : Q)) Nat.one_pos (add_den_pos (Qmul_den_pos (by decide) (by decide))
    (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (by decide)))))
    (ofQ_congr (a := mul (⟨8, 1⟩ : Q) (add (mul (⟨1, 4⟩ : Q) (⟨1, 4⟩ : Q)) (mul (⟨7, 1⟩ : Q) (mul (⟨3, 1⟩ : Q) (⟨1, 144⟩ : Q))))) (b := (⟨5, 3⟩ : Q))
      (Qmul_den_pos Nat.one_pos (add_den_pos (Qmul_den_pos (by decide) (by decide))
      (Qmul_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (by decide))))) (by decide) (by decide))

/-- **★★ THE COMPRESSED READBACK OF THE SOURCE FIBERS IS `(5/3)·A_f·A_g`** — `5/12` of the cut Gram and
    NO cycle Gram, at every pair of addresses. -/
theorem reyT_gamma_pairing (d ℓ d' ℓ' : Nat) (hℓ : ℓ < 8) (hℓ' : ℓ' < 8) (c uf vf ug vg : Real) :
    Req (pairF (reyT (gammaAtom d ℓ c uf vf)) (atlasOp (reyT (gammaAtom d' ℓ' c ug vg))))
        (Rmul c53ry (Rmul (aCoefGa c uf vf) (aCoefGa c ug vg))) := by
  refine Req_trans (pairF_reyT_M _ _) ?_
  have hu : ∀ i, i < 3 → Req (Rmul c18ry (rowSum (gammaAtom d ℓ c uf vf) i)) (Rmul c12ry (aCoefGa c uf vf)) :=
    fun i _ => reyT_gamma d ℓ hℓ c uf vf i 0
  have hu' : ∀ i, i < 3 → Req (Rmul c18ry (rowSum (gammaAtom d' ℓ' c ug vg) i)) (Rmul c12ry (aCoefGa c ug vg)) :=
    fun i _ => reyT_gamma d' ℓ' hℓ' c ug vg i 0
  have hS : Req (RsumN (fun i => Rmul c18ry (rowSum (gammaAtom d ℓ c uf vf) i)) 3) (Rmul c3 (Rmul c12ry (aCoefGa c uf vf))) :=
    Req_trans (RsumN_congr 3 hu) (Req_trans (RsumN_const _ 3) (Rmul_congr RofNat3_eq (Req_refl _)))
  have hS' : Req (RsumN (fun i => Rmul c18ry (rowSum (gammaAtom d' ℓ' c ug vg) i)) 3) (Rmul c3 (Rmul c12ry (aCoefGa c ug vg))) :=
    Req_trans (RsumN_congr 3 hu') (Req_trans (RsumN_const _ 3) (Rmul_congr RofNat3_eq (Req_refl _)))
  have hP : Req (RsumN (fun i => Rmul (Rmul c18ry (rowSum (gammaAtom d ℓ c uf vf) i)) (Rmul c18ry (rowSum (gammaAtom d' ℓ' c ug vg) i))) 3)
      (Rmul c3 (Rmul (Rmul c12ry (aCoefGa c uf vf)) (Rmul c12ry (aCoefGa c ug vg)))) :=
    Req_trans (RsumN_congr 3 (fun i hi => Rmul_congr (hu i hi) (hu' i hi)))
      (Req_trans (RsumN_const _ 3) (Rmul_congr RofNat3_eq (Req_refl _)))
  refine Req_trans (Rmul_congr (Req_refl _) (Radd_congr (Rmul_congr hS hS') (Rmul_congr (Req_refl _) hP))) ?_
  exact ry_const_alg _ _

/-- **★ THE POINTWISE READBACK ERROR** of the Reynolds compression on every source fiber:
    `⟨Γ_f, MΓ_g⟩ − ⟨P_τΓ_f, M P_τΓ_g⟩ = (7/3)·A_fA_g − 4·B_fB_g`. -/
theorem reynolds_gamma_gap (d ℓ : Nat) (hd : d < 3) (hℓ : ℓ < 8) (c uf vf ug vg : Real) :
    Req (Rsub (pairF (gammaAtom d ℓ c uf vf) (atlasOp (gammaAtom d ℓ c ug vg)))
              (pairF (reyT (gammaAtom d ℓ c uf vf)) (atlasOp (reyT (gammaAtom d ℓ c ug vg)))))
        (Rsub (Rmul c73ry (Rmul (aCoefGa c uf vf) (aCoefGa c ug vg)))
              (Rmul c4 (Rmul (bCoefGa c uf vf) (bCoefGa c ug vg)))) := by
  refine Req_trans (Rsub_congr (gamma_bilinear d ℓ hd hℓ _ _ _ _) (reyT_gamma_pairing d ℓ d ℓ hℓ hℓ c uf vf ug vg)) ?_
  -- (4AA' − 4BB') − (5/3)AA' ≈ (7/3)AA' − 4BB'
  refine Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_comm _ _) (Radd_congr ?_ (Req_refl _)))
  -- 4·X + (−(5/3)·X) ≈ (7/3)·X
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Rmul_neg_left _ _))) ?_
  refine Req_trans (Req_symm (Rmul_distrib_right _ _ _)) (Rmul_congr ?_ (Req_refl _))
  refine Req_trans (Radd_congr (Req_refl _) (Rneg_ofQ (⟨5, 3⟩ : Q) (by decide))) ?_
  exact Req_trans (Radd_ofQ_ofQ (a := (⟨4, 1⟩ : Q)) (b := neg (⟨5, 3⟩ : Q)) Nat.one_pos (by decide))
    (ofQ_congr (a := add (⟨4, 1⟩ : Q) (neg (⟨5, 3⟩ : Q))) (b := (⟨7, 3⟩ : Q)) (add_den_pos Nat.one_pos (by decide)) (by decide) (by decide))

-- ===========================================================================
-- (3) The constant channel: the compressed Gram is `0`, the readback error is the WHOLE channel.
-- ===========================================================================

/-- `P_τ` kills the constant fiber (pure cycle: `A = 0`). -/
theorem reyT_constFiber_zero (C : NormCtx) (f : L2Test) (t : Real) (i j : Nat) : Req (reyT (constFiber C f t) i j) zero := by
  unfold constFiber negFiber
  refine Req_trans (reyT_gamma archAddr.1 archAddr.2 archAddr_valid.2 one (Vc C f t) (Vc C f t) i j) ?_
  exact Req_trans (Rmul_congr (Req_refl _) (negFiber_VV_cut_zero (Vc C f t))) (Rmul_zero _)

theorem pairF_zero_left (v w : Nat → Nat → Real) (hv : ∀ i j, i < 3 → j < 8 → Req (v i j) zero) : Req (pairF v w) zero := by
  unfold pairF
  refine Req_trans (RsumN_congr 3 (fun i hi => Req_trans (RsumN_congr 8 (fun j hj =>
    Req_trans (Rmul_congr (hv i j hi hj) (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))))
    (Req_trans (RsumN_const zero 8) (Rmul_zero _)))) ?_
  exact Req_trans (RsumN_const zero 3) (Rmul_zero _)

/-- The compressed constant-channel integrand. -/
def reyConstInt (C : NormCtx) (f g : L2Test) (y : Real) : Real :=
  Rmul (constDensity C (affC C y)) (pairF (reyT (constFiber C f (affC C y))) (atlasOp (reyT (constFiber C g (affC C y)))))

theorem reyConstInt_zero (C : NormCtx) (f g : L2Test) (y : Real) : Req (reyConstInt C f g y) zero :=
  Req_trans (Rmul_congr (Req_refl _) (pairF_zero_left _ _ (fun i j _ _ => reyT_constFiber_zero C f _ i j))) (Rmul_zero _)
theorem reyConstInt_lip (C : NormCtx) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (reyConstInt C f g y) (reyConstInt C f g z))) (Rmul (ofQ (⟨0, 1⟩ : Q) (by decide)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (reyConstInt_zero C f g) (const_lip0 zero)
theorem reyConstInt_fc (C : NormCtx) (f g : L2Test) : ∀ y z, Req y z → Req (reyConstInt C f g y) (reyConstInt C f g z) :=
  fun y z _ => Req_trans (reyConstInt_zero C f g y) (Req_symm (reyConstInt_zero C f g z))

/-- The compressed constant Gram `∫₀¹ constDensity·⟨P_τ constFiber_f, M P_τ constFiber_g⟩`. -/
def reyConstGram (C : NormCtx) (f g : L2Test) : Real :=
  riemannIntegral (by decide) (by decide) (reyConstInt_lip C f g) (reyConstInt_fc C f g)

theorem reyConstGram_zero (C : NormCtx) (f g : L2Test) : Req (reyConstGram C f g) zero :=
  Req_trans (riemannIntegral_congr _ _ (reyConstInt_lip C f g) (reyConstInt_fc C f g) (const_lip0 zero)
    (fun _ _ _ => Req_refl _) (reyConstInt_zero C f g)) (riemannIntegral_const_gen zero _ _ _ _)

/-- **★ THE CONSTANT-CHANNEL READBACK ERROR IS THE WHOLE CHANNEL**: `constGram − reyConstGram = −ArchConstForm(f,g)`,
    independent of the truncation `k` and of any refinement stage — it cannot vanish along a schedule. -/
theorem reynolds_const_readback_gap (C : NormCtx) (f g : L2Test) :
    Req (Rsub (constGram C f g) (reyConstGram C f g)) (Rneg (ArchConstForm f g C.a C.han C.had C.w C.hw C.hwn)) :=
  Req_trans (Rsub_congr (Req_refl _) (reyConstGram_zero C f g))
    (Req_trans (Rsub_zero _) (Req_trans (constGram_eq C f g) (Rneg_congr (Req_symm (ArchConstForm_eq_vv C f g)))))

-- ===========================================================================
-- (4) No fiberwise PSD compression reads back the constant channel.
-- ===========================================================================

/-- **★ THE GENERAL FIBERWISE OBSTRUCTION**: for ANY compression `P` of fibers whose compressed pairing is PSD,
    the source constant-channel integrand is `≤ 0 ≤` its compression at every `t`; the two agree only where
    `V(f,t) = 0`.  Every address-level Atlas operation is such a `P`. -/
theorem fiberwise_psd_const_gap (P : (Nat → Nat → Real) → (Nat → Nat → Real))
    (hP : ∀ v, Rnonneg (pairF (P v) (atlasOp (P v)))) (C : NormCtx) (f : L2Test) (t : Real) :
    Rle (Rmul (constDensity C t) (pairF (constFiber C f t) (atlasOp (constFiber C f t))))
        (Rmul (constDensity C t) (pairF (P (constFiber C f t)) (atlasOp (P (constFiber C f t))))) := by
  have hX : Rnonneg (Rmul (Rmul archConst (Rmul (ofQ C.w C.hw) (rEv C t))) (Rmul (Vc C f t) (Vc C f t))) :=
    Rnonneg_Rmul (Rnonneg_Rmul archConst_nonneg (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (Rnonneg_clampedInv C.a C.han C.had t)))
      (Rnonneg_Rmul_self _)
  have hneg : Rle (Rmul (constDensity C t) (pairF (constFiber C f t) (atlasOp (constFiber C f t)))) zero :=
    Rle_trans (Rle_of_Req (constFiber_readback C f f t))
      (Rle_trans (Rle_Rneg (Rle_zero_of_Rnonneg hX)) (Rle_of_Req Rneg_zero))
  exact Rle_trans hneg (Rle_zero_of_Rnonneg (Rnonneg_Rmul (constDensity_nonneg C t) (hP _)))

end UOR.Bridge.F1Square.Square
