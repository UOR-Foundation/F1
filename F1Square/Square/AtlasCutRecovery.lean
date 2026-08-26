/-
F1 square — **SOURCE RECOVERY FROM CUT COORDINATES** (`AtlasCutRecovery.lean`, target-free).

At fixed raw truncation `k`, with `K = K_k(x)`, `r = 1/max(x,1)`, `q_k = x·K`, `P_k = K·(x+1) + r`, the pole and
compact-tail CUT coordinates `A_pole = (U_x + V)/4`, `A_tail = (Z_{k,x} − r·V)/4` determine the source
field EXACTLY (`x ≥ 1`):

    `V   = 4·(q_k·A_pole − A_tail) / P_k`          (`recoverVFromCut`, `recoverVFromCut_source`),
    `U_x = 4·((K + r)·A_pole + A_tail) / P_k`      (`recoverUFromCut`, `recoverUFromCut_source`),
    `V   = 2·A_far`                                (`recoverVFromFar`, `recoverVFromFar_source`).

`P_k ≥ 1/B` on `x ≤ B` (`Pk_ge_invB`), so `1/P_k` is the certified reciprocal at an EXPLICIT witness index
(`PkInv`; no choice).  These are maps of the cut coordinates alone — they never read `U` or `V` directly.

THE CUT-ONLY ORBIT READING.  `readCut` reads the prime-scale value `U_n(t)` on a coupling address from the
pole/tail cut coordinates at the Archimedean mate `(x, s)` through `recoverUFromCut`, weighted division-free by
`invSq(n)·invSq(x)·x`; on decoded core tests it IS `U_n(t)` (`readCut_source`).  `couplingOfAdmissible`
connects the admissible interval `J_{k,n,t}` to `CouplingAddr` with its band/window certificates.

No integration over `x`, no density, no norm, no operator bound, no sign.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasSourceCoherent
import F1Square.Square.AtlasOrbitModels

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- `P_k(x) = K_k(x)·(x+1) + 1/max(x,1)`. -/
def Pk (k : Nat) (x : Real) : Real := Radd (Rmul (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x) (Radd x one)) (rOne x)
/-- `q_k(x) = x·K_k(x)`. -/
def qk (k : Nat) (x : Real) : Real := Rmul x (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x)

/-- `P_k(x) ≥ 1/B` for `0 ≤ x ≤ B`. -/
theorem Pk_ge_invB (C : NormCtx) (k : Nat) {x : Real} (hx0 : Rle zero x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Rle (ofQ (Qinv (canonB C)) (Qinv_den_pos (canonB_num C))) (Pk k x) := by
  have h1 : Rle (ofQ (Qinv (canonB C)) (Qinv_den_pos (canonB_num C))) (rOne x) :=
    ofQ_inv_le_clampedInv (by decide) (by decide) (canonB_den C) (canonB_num C) hxB (canonB_one C)
  refine Rle_trans h1 ?_
  unfold Pk Kfl
  exact Rle_self_Radd_left (Rnonneg_Rmul (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _)
    (Rnonneg_Radd (Rnonneg_of_Rle_zero hx0) (Rnonneg_ofQ (by decide) (by decide))))

/-- The certified reciprocal `1/P_k(x)` at the explicit witness index `3·(1/B).den`. -/
def PkInv (C : NormCtx) (k : Nat) (x : Real) (hx0 : Rle zero x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) : Real :=
  Rinv (Pk k x) (3 * (Qinv (canonB C)).den)
    (Rlt_Qbound_of_Rle_ofQ (Qinv_num_pos (canonB_den C)) (Qinv_den_pos (canonB_num C)) (Pk_ge_invB C k hx0 hxB))

theorem Pk_mul_PkInv (C : NormCtx) (k : Nat) (x : Real) (hx0 : Rle zero x) (hxB : Rle x (ofQ (canonB C) (canonB_den C))) :
    Req (Rmul (Pk k x) (PkInv C k x hx0 hxB)) one := Rmul_Rinv_self _

/-- **`V` from the pole and tail cut coordinates**: `4·(q_k·A_pole − A_tail)/P_k`. -/
def recoverVFromCut (C : NormCtx) (k : Nat) (x : Real) (hx0 : Rle zero x) (hxB : Rle x (ofQ (canonB C) (canonB_den C)))
    (Ap At : Real) : Real :=
  Rmul (Rmul c4 (Rsub (Rmul (qk k x) Ap) At)) (PkInv C k x hx0 hxB)

/-- **`U_x` from the pole and tail cut coordinates**: `4·((K + r)·A_pole + A_tail)/P_k`. -/
def recoverUFromCut (C : NormCtx) (k : Nat) (x : Real) (hx0 : Rle zero x) (hxB : Rle x (ofQ (canonB C) (canonB_den C)))
    (Ap At : Real) : Real :=
  Rmul (Rmul c4 (Radd (Rmul (Radd (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x) (rOne x)) Ap) At)) (PkInv C k x hx0 hxB)

/-- **`V` from the far cut coordinate**: `2·A_far`. -/
def recoverVFromFar (Af : Real) : Real := Rmul cTwo Af

theorem zero_le_of_one_le {x : Real} (hx1 : Rle one x) : Rle zero x :=
  Rle_trans (Rle_ofQ_ofQ (by decide) (by decide) (by decide)) hx1

theorem c4_eq_two_two : Req c4 (Rmul cTwo cTwo) :=
  Req_symm (Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos)
    (ofQ_congr (a := mul (⟨2, 1⟩ : Q) (⟨2, 1⟩ : Q)) (b := (⟨4, 1⟩ : Q)) (Qmul_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos (by decide)))

theorem two_half_eq_one : Req (Rmul cTwo cH) one :=
  Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
    (ofQ_congr (a := mul (⟨2, 1⟩ : Q) (⟨1, 2⟩ : Q)) (b := (⟨1, 1⟩ : Q)) (Qmul_den_pos Nat.one_pos (by decide)) Nat.one_pos (by decide))

/-- **★ EXACT RECOVERY OF `V`** from the decoded pole/tail cut coordinates (`1 ≤ x ≤ B`). -/
theorem recoverVFromCut_source (C : NormCtx) (k : Nat) (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C)))
    (f : L2Test) (t : Real) :
    Req (recoverVFromCut C k x (zero_le_of_one_le hx1) hxB
          (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))) (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t)))
        (Vc C f t) := by
  have hanc := anchor_from_pole_tail_ge_one C (dyQ k) (dyQ_num k) (dyQ_den k) x hx1 f t
  -- hanc : P·(½V) ≈ 2·(q·Ap − At)
  unfold recoverVFromCut
  -- 4·X ≈ 2·(2·X) ≈ 2·(P·½V) ≈ P·V
  have h4 : Req (Rmul c4 (Rsub (Rmul (qk k x) (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))))
                                (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t))))
      (Rmul (Pk k x) (Vc C f t)) := by
    refine Req_trans (Rmul_congr c4_eq_two_two (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_)
    refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_symm hanc)) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_))
    refine Rmul_congr (Req_refl _) ?_
    exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr two_half_eq_one (Req_refl _)) (Rone_mul _))
  refine Req_trans (Rmul_congr h4 (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_))
  exact Req_trans (Rmul_congr (Pk_mul_PkInv C k x _ hxB) (Req_refl _)) (Rone_mul _)

/-- `P_k − q_k ≈ K + r`. -/
theorem Pk_sub_qk (k : Nat) (x : Real) :
    Req (Rsub (Pk k x) (qk k x)) (Radd (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x) (rOne x)) := by
  unfold Pk qk
  generalize hK : Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x = K
  generalize hr : rOne x = r
  -- (K(x+1) + r) − xK ≈ ((Kx + K) + r) − Kx
  refine Req_trans (Rsub_congr (Radd_congr (Rmul_distrib K x one) (Req_refl r)) (Rmul_comm x K)) ?_
  refine Req_trans (Rsub_congr (Radd_congr (Radd_congr (Req_refl (Rmul K x)) (Rmul_one K)) (Req_refl r)) (Req_refl _)) ?_
  -- ((Kx + K) + r) − Kx ≈ (K + r) + (Kx − Kx) ≈ K + r
  refine Req_trans (Radd_congr (Req_trans (Radd_assoc (Rmul K x) K r) (Radd_comm (Rmul K x) (Radd K r))) (Req_refl _)) ?_
  refine Req_trans (Radd_assoc (Radd K r) (Rmul K x) (Rneg (Rmul K x))) ?_
  exact Req_trans (Radd_congr (Req_refl _) (Radd_neg (Rmul K x))) (Radd_zero _)

/-- **★ THE `U`-RECOVERY IDENTITY** (`x ≥ 1`): `P_k·(½U) = 2·((K + r)·A_pole + A_tail)`, from the anchor identity
    and `2·A_pole = ½U + ½V`. -/
theorem u_from_pole_tail_ge_one (C : NormCtx) (k : Nat) (x : Real) (hx1 : Rle one x) (f : L2Test) (t : Real) :
    Req (Rmul (Pk k x) (Rmul cH (Uc C x f t)))
        (Rmul cTwo (Radd (Rmul (Radd (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x) (rOne x))
                               (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))))
                         (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t)))) := by
  have hanc := anchor_from_pole_tail_ge_one C (dyQ k) (dyQ_num k) (dyQ_den k) x hx1 f t
  -- 2·Ap ≈ ½U + ½V
  have h2A : Req (Rmul cTwo (aCoefGa one (Uc C x f t) (Rneg (Vc C f t)))) (Radd (Rmul cH (Uc C x f t)) (Rmul cH (Vc C f t))) := by
    refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_trans (aCoefGa_one _ _) (Rmul_congr (Req_refl cQ) (Radd_congr (Req_refl _) (Rneg_neg _))))) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    have h2q : Req (Rmul cTwo cQ) cH :=
      Req_trans (Rmul_ofQ_ofQ Nat.one_pos (by decide))
        (ofQ_congr (a := mul (⟨2, 1⟩ : Q) (⟨1, 4⟩ : Q)) (b := (⟨1, 2⟩ : Q)) (Qmul_den_pos Nat.one_pos (by decide)) (by decide) (by decide))
    exact Req_trans (Rmul_congr h2q (Req_refl _)) (Rmul_distrib _ _ _)
  -- ½U ≈ 2Ap − ½V
  have hU : Req (Rmul cH (Uc C x f t)) (Rsub (Rmul cTwo (aCoefGa one (Uc C x f t) (Rneg (Vc C f t)))) (Rmul cH (Vc C f t))) :=
    Req_symm (Req_trans (Rsub_congr h2A (Req_refl _)) (Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) (Radd_neg _)) (Radd_zero _))))
  refine Req_trans (Rmul_congr (Req_refl _) hU) ?_
  refine Req_trans (Rmul_sub_distrib _ _ _) ?_
  refine Req_trans (Rsub_congr (Req_refl _) hanc) ?_
  -- P(2Ap) − 2(qAp − At) ≈ 2((P − q)Ap + At) ≈ 2((K + r)Ap + At)
  refine Req_trans (Rsub_congr (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))) (Req_refl _)) ?_
  refine Req_trans (Req_symm (Rmul_sub_distrib cTwo _ _)) (Rmul_congr (Req_refl cTwo) ?_)
  -- P·Ap − (q·Ap − At) ≈ (P − q)·Ap + At
  refine Req_trans (Radd_congr (Req_refl _) (Req_trans (Rneg_Radd _ _) (Radd_congr (Req_refl _) (Rneg_neg _)))) ?_
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Radd_congr ?_ (Req_refl _))
  refine Req_trans (Radd_congr (Req_refl _) (Req_symm (Rmul_neg_left _ _))) ?_
  exact Req_trans (Req_symm (Rmul_distrib_right _ _ _)) (Rmul_congr (Pk_sub_qk k x) (Req_refl _))

/-- **★ EXACT RECOVERY OF `U_x`** from the decoded pole/tail cut coordinates (`1 ≤ x ≤ B`). -/
theorem recoverUFromCut_source (C : NormCtx) (k : Nat) (x : Real) (hx1 : Rle one x) (hxB : Rle x (ofQ (canonB C) (canonB_den C)))
    (f : L2Test) (t : Real) :
    Req (recoverUFromCut C k x (zero_le_of_one_le hx1) hxB
          (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))) (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t)))
        (Uc C x f t) := by
  have hid := u_from_pole_tail_ge_one C k x hx1 f t
  unfold recoverUFromCut
  have h4 : Req (Rmul c4 (Radd (Rmul (Radd (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) x) (rOne x)) (aCoefGa one (Uc C x f t) (Rneg (Vc C f t))))
                               (aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t))))
      (Rmul (Pk k x) (Uc C x f t)) := by
    refine Req_trans (Rmul_congr c4_eq_two_two (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_)
    refine Req_trans (Rmul_congr (Req_refl cTwo) (Req_symm hid)) ?_
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Req_trans (Rmul_assoc _ _ _) ?_))
    refine Rmul_congr (Req_refl _) ?_
    exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr two_half_eq_one (Req_refl _)) (Rone_mul _))
  refine Req_trans (Rmul_congr h4 (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_))
  exact Req_trans (Rmul_congr (Pk_mul_PkInv C k x _ hxB) (Req_refl _)) (Rone_mul _)

/-- **Exact recovery of `V` from the far cut coordinate**. -/
theorem recoverVFromFar_source (C : NormCtx) (f : L2Test) (t : Real) :
    Req (recoverVFromFar (aCoefGa one (Vc C f t) (Rneg (Vc C f t)))) (Vc C f t) := by
  unfold recoverVFromFar
  refine Req_trans (Rmul_congr (Req_refl cTwo) (posFiber_VV_cut _)) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr two_half_eq_one (Req_refl _)) (Rone_mul _))

-- ===========================================================================
-- (2) The cut fields of a test and the cut-only orbit reading.
-- ===========================================================================

/-- The cut coordinates of a decoded test: pole `(x,t)`, compact tail `(x,t)`, far `t` (the constant channel has cut `0`). -/
structure CutField where
  pole : Real → Real → Real
  tail : Real → Real → Real
  far : Real → Real

/-- The decoded cut field `A_k f`. -/
def cutOf (C : NormCtx) (k : Nat) (f : L2Test) : CutField where
  pole := fun x t => aCoefGa one (Uc C x f t) (Rneg (Vc C f t))
  tail := fun x t => aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) x f t) (Wc C x f t)
  far := fun t => aCoefGa one (Vc C f t) (Rneg (Vc C f t))

/-- **The cut-only orbit reading** of `U_n(t)` from the Archimedean mate `(x,s)` of a coupling address:
    `invSq(n)·(invSq(x)·(x·recoverUFromCut(x,s)))`. -/
def readCut (C : NormCtx) (k : Nat) (c : CouplingAddr) (hx0 : Rle zero c.arch.xr) (hxB : Rle c.arch.xr (ofQ (canonB C) (canonB_den C)))
    (z : CutField) : Real :=
  Rmul (invSq C c.fin.n.r) (Rmul (invSq C c.arch.xr)
    (Rmul c.arch.xr (recoverUFromCut C k c.arch.xr hx0 hxB (z.pole c.arch.xr c.arch.sr) (z.tail c.arch.xr c.arch.sr))))

/-- **★ THE CUT-ONLY READING IS `U_n(t)`** on every decoded core test, for an admissible coupling address in the band
    with `x ≥ 1`. -/
theorem readCut_source (C : NormCtx) (k : Nat) (c : CouplingAddr) (hx1 : Rle one c.arch.xr)
    (hxB : Rle c.arch.xr (ofQ (canonB C) (canonB_den C))) (f : L2Test) (hf : CoreTest C.geom f)
    (hc : AddrAdmissible C c) (hb : AddrBand C c) :
    Req (readCut C k c (zero_le_of_one_le hx1) hxB (cutOf C k f)) (Uc C c.fin.n.r f c.fin.tr) := by
  have hrec := recoverUFromCut_source C k c.arch.xr hx1 hxB f c.arch.sr
  have hW := readW_eq C (decodeField_coherent C f hf) c hc hb
  unfold readCut
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) (Rmul_congr (Req_refl _) hrec))) ?_
  exact hW

-- ===========================================================================
-- (3) From the admissible interval to coupling addresses with certificates.
-- ===========================================================================

theorem Rle_ofQ_of_Qle {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (h : Qle a b) : Rle (ofQ a ha) (ofQ b hb) := Rle_ofQ_ofQ ha hb h

/-- The coupling address `((n,t), (x, x·t/n))` of an admissible scale. -/
def couplingOfAdmissible (C : NormCtx) (k : Nat) (p : FiniteLocalAddr) (x : Q) (hxd : 0 < x.den) (hxn : 0 < x.num)
    (_h : Admissible C k p x) : CouplingAddr :=
  ⟨(p, ⟨x, hxn, hxd, mateS p x, Qmul_num_pos (Qmul_num_pos hxn p.htn) (Qinv_num_pos (primePowerAddr_q_den p.n)),
      Qmul_den_pos (Qmul_den_pos hxd p.htd) (Qinv_den_pos (primePowerAddr_q_num p.n))⟩),
   (onOrbit_iff_orbit _ _).1 (by
      show Qeq (mul p.n.q (mateS p x)) (mul x p.t)
      exact anchor_exists p x)⟩

/-- **An admissible scale yields an admissible coupling address in the band** (`n ≤ B`, `t ∈ [a, a+w]`, `1 ≤ 2^{-k}+1 ≤ x`). -/
theorem couplingOfAdmissible_adm (C : NormCtx) (k : Nat) (p : FiniteLocalAddr) (x : Q) (hxd : 0 < x.den) (hxn : 0 < x.num)
    (h : Admissible C k p x) (hnB : Qle p.n.q (canonB C)) (hta : Qle C.a p.t) :
    AddrAdmissible C (couplingOfAdmissible C k p x hxd hxn h) ∧ AddrBand C (couplingOfAdmissible C k p x hxd hxn h) := by
  have hxB : Qle x (canonB C) := h.hhi
  have h1f : Qle (⟨1, 1⟩ : Q) (tailFloor k) := by
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hp' : (1 : Int) ≤ (2 : Int) ^ k := by exact_mod_cast hp
    simp only [Qle, tailFloor, add]
    push_cast; omega
  have hx1 : Qle (⟨1, 1⟩ : Q) x := Qle_trans (add_den_pos Nat.one_pos (Nat.two_pow_pos k)) h1f h.hlo
  have hn1 : Qle (⟨1, 1⟩ : Q) p.n.q := by
    show (1 : Int) * ((1 : Nat) : Int) ≤ ((p.n.1 : Nat) : Int) * ((1 : Nat) : Int)
    have := primePowerAddr_two_le p.n; push_cast; omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Rle_ofQ_of_Qle _ _ (Qle_trans (canonB_den C) hnB (canonB_le_S C))
  · exact Rle_ofQ_of_Qle _ _ (Qle_trans (canonB_den C) hxB (canonB_le_S C))
  · exact Rle_ofQ_of_Qle _ _ hta
  · exact Rle_ofQ_of_Qle _ _ h.hwin_lo
  · exact Rle_ofQ_of_Qle _ _ (Qle_trans (by decide) (canonC_le_one C) hn1)
  · exact Rle_ofQ_of_Qle _ _ hnB
  · exact Rle_ofQ_of_Qle _ _ (Qle_trans (by decide) (canonC_le_one C) hx1)
  · exact Rle_ofQ_of_Qle _ _ hxB

end UOR.Bridge.F1Square.Square
