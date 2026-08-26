/-
F1 square — **THE MEASURED FIVE-CHANNEL CARRIER AND ITS ANALYSES** (`AtlasCarrier5.lean`, target-free).

The five channels of the Atlas defect Gram — pole, folded prime, constant, compact tail, far tail — are
realized as ONE carrier type of certified fields (`Carrier5`), with the SAME quadratic form on the cut and on
the cycle side (`inner5`):

    `inner5(z₁,z₂) = ∫_{[1,B]}∫ 4·2(1+1/x)wr·z₁z₂ + Σ_{m<X}∫ 4·2Λ(m+1)wr·z₁z₂ + ∫ 4·(log4π+γ)wr·z₁z₂
                     + ∫_{[1+2^{-k},B]}∫ 4·2wr·z₁z₂ + ∫ 4·2·fc·wr·z₁z₂`,

exactly the sourced densities of the channel Grams (`AtlasFibers`, `AtlasPrimeFold`, `AtlasArchGram`), with
the factor `4` of the pointwise split `⟨Φ_f, MΦ_g⟩ = 4A_fA_g − 4B_fB_g` (`negFiber_split`) absorbed into the
density; the far scalar mass `fc` is a parameter here (identified with `farCoef` in `AtlasFiveSplit`).

The ANALYSES `cutAnalysis5 f` / `cycleAnalysis5 f` are the fields of the fiber coordinates `A = (u − v)/4`
and `B = (u + v)/4` of the five channel fibers, with global certificates from the coherent scale field.
THE FOUR TARGET-FREE CHANNEL SPLITS (`poleGram_split`, `primeFoldGram_split`, `constGram_split`,
`tailGram_split`) and their sum `atlasDefectGram_split` express each channel Gram as
`(cut Gram) − (cycle Gram)`: an exact identity of integrals, NOT a sign.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasField2
import F1Square.Square.AtlasDefectGram

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

namespace CField

/-- A real scalar with the sourced `xBound` certificate. -/
def smulR (c : Real) (u : CField) : CField :=
  smulF c Nat.one_pos (xBQ_num_nonneg c) (Rabs_le_ofQ_xBound c) u

/-- `one·u` (the `c·u` factor of the fiber coordinates at the archimedean gauge `c = 1`). -/
def oneF (u : CField) : CField :=
  smulF one Nat.one_pos (by decide)
    (abs_ofQ_le (q := (⟨1, 1⟩ : Q)) Nat.one_pos (by decide) : Rle (Rabs one) (ofQ (⟨1, 1⟩ : Q) Nat.one_pos)) u

/-- The cut coordinate field `A = (1·u − v)/4` of the fiber `negFiber u v`. -/
def aCoefF (u v : CField) : CField := smulQF (⟨1, 4⟩ : Q) (by decide) (by decide) (subF (oneF u) v)

/-- The cycle coordinate field `B = (1·u + v)/4` of the fiber `negFiber u v`. -/
def bCoefF (u v : CField) : CField := smulQF (⟨1, 4⟩ : Q) (by decide) (by decide) (addF (oneF u) v)

end CField

open CField

theorem mulF_F (u v : CField) (x t : Real) : (mulF u v).F x t = Rmul (u.F x t) (v.F x t) := rfl
theorem aCoefF_F (u v : CField) (x t : Real) : (aCoefF u v).F x t = aCoefGa one (u.F x t) (v.F x t) := rfl
theorem bCoefF_F (u v : CField) (x t : Real) : (bCoefF u v).F x t = bCoefGa one (u.F x t) (v.F x t) := rfl

-- ===========================================================================
-- (1) The base fields: `w·r(t)`, `1 + 1/max(x,1)`, `1/max(x,1)`, the clamp `x̄`, the kernel `K_k(x̄)`.
-- ===========================================================================

/-- `t ↦ r(t) = 1/max(t,a)`. -/
def rF (C : NormCtx) : CField :=
  ofT (fun t => rEv C t) (recipTest C.a C.han C.had).hLd (recipTest C.a C.han C.had).hLn
    (recipTest C.a C.han C.had).hMd (recipTest C.a C.han C.had).hMn
    (recipTest C.a C.han C.had).hlip (recipTest C.a C.han C.had).hbd (recipTest C.a C.han C.had).hfc

/-- `(x,t) ↦ w·r(t)`. -/
def wrF (C : NormCtx) : CField := smulQF C.w C.hw C.hwn (rF C)

theorem wrF_F (C : NormCtx) (x t : Real) : (wrF C).F x t = Rmul (ofQ C.w C.hw) (rEv C t) := rfl

/-- `x ↦ 1 + 1/max(x,1)`. -/
def oneRF : CField :=
  ofX (fun x => Radd one (rOne x))
    (L := mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (M := add (⟨1, 1⟩ : Q) (Qinv (⟨1, 1⟩ : Q)))
    (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide)))
    (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) (Int.le_of_lt (Qinv_num_pos (by decide))))
    (add_den_pos Nat.one_pos (Qinv_den_pos (by decide)))
    (Qadd_num_nonneg_loc (by decide) (Int.le_of_lt (Qinv_num_pos (by decide))))
    one_add_rOne_lip one_add_rOne_bd (fun _ _ h => Radd_congr (Req_refl _) (clampedInv_congr _ _ _ h))

/-- `x ↦ 1/max(x,1)`. -/
def rOneF : CField :=
  ofX rOne (L := mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (M := Qinv (⟨1, 1⟩ : Q))
    (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide)))
    (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) (Int.le_of_lt (Qinv_num_pos (by decide))))
    (Qinv_den_pos (by decide)) (Int.le_of_lt (Qinv_num_pos (by decide)))
    (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide)) rOne_bd (fun _ _ h => clampedInv_congr _ _ _ h)

theorem xcl_lip1 (C : NormCtx) : ∀ x x', Rle (Rabs (Rsub (xcl C x) (xcl C x'))) (Rmul (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (Rabs (Rsub x x'))) :=
  fun x x' => Rle_trans (xcl_lip C x x') (Rle_of_Req (Req_symm (Rone_mul _)))

theorem xcl_abs_bd (C : NormCtx) (x : Real) : Rle (Rabs (xcl C x)) (ofQ (canonB C) (canonB_den C)) :=
  Rabs_le_of_nonneg_le (canonB_den C) (Int.le_of_lt (canonB_num C))
    (Rnonneg_of_Rle_zero (Rle_trans (Rle_zero_of_Rnonneg Rnonneg_one) (xcl_ge_one C x))) (xcl_le_B C x)

/-- `x ↦ x̄ = band_{[1,B]}(x)`. -/
def xclF (C : NormCtx) : CField :=
  ofX (xcl C) (L := (⟨1, 1⟩ : Q)) (M := canonB C) Nat.one_pos (by decide) (canonB_den C) (Int.le_of_lt (canonB_num C))
    (xcl_lip1 C) (xcl_abs_bd C) (fun _ _ h => xcl_congr C h)

/-- `x ↦ K_k(x̄)`. -/
def KxF (C : NormCtx) (k : Nat) : CField :=
  ofX (Kx C k) (kerL_den k) (kerL_num k) (kerM_den k) (kerM_num k) (Kx_lip C k) (Kx_bd C k) (fun _ _ h => Kx_congr C k h)

-- ===========================================================================
-- (2) The five channel densities (the sourced densities times the split factor `4`).
-- ===========================================================================

def q4 : Q := (⟨4, 1⟩ : Q)
def q2 : Q := (⟨2, 1⟩ : Q)

/-- Pole: `4·2(1 + 1/x)·w·r`. -/
def poleDens5 (C : NormCtx) : CField := smulQF q4 Nat.one_pos (by decide) (smulQF q2 Nat.one_pos (by decide) (mulF oneRF (wrF C)))
/-- Folded prime at place `m`: `4·2Λ(m+1)·w·r`. -/
def primeDens5 (C : NormCtx) (m : Nat) : CField :=
  smulQF q4 Nat.one_pos (by decide) (smulQF q2 Nat.one_pos (by decide) (smulR (vonMangoldt (m + 1)) (wrF C)))
/-- Constant: `4·(log 4π + γ)·w·r`. -/
def constDens5 (C : NormCtx) : CField := smulQF q4 Nat.one_pos (by decide) (smulR archConst (wrF C))
/-- Compact tail: `4·2·w·r`. -/
def tailDens5 (C : NormCtx) : CField := smulQF q4 Nat.one_pos (by decide) (smulQF q2 Nat.one_pos (by decide) (wrF C))
/-- Far tail with scalar mass `fc`: `4·(2·fc)·w·r`. -/
def farDens5 (C : NormCtx) (fc : Real) : CField := smulQF q4 Nat.one_pos (by decide) (smulR (Rmul cTwo fc) (wrF C))

theorem poleDens5_F (C : NormCtx) (x t : Real) : Req ((poleDens5 C).F x t) (Rmul c4 (poleDensity C x t)) :=
  Rmul_congr (Req_refl _) (Req_symm (Rmul_assoc _ _ _))
theorem primeDens5_F (C : NormCtx) (m : Nat) (x t : Real) : Req ((primeDens5 C m).F x t) (Rmul c4 (primeFoldDensity C m t)) :=
  Req_refl _
theorem constDens5_F (C : NormCtx) (x t : Real) : Req ((constDens5 C).F x t) (Rmul c4 (constDensity C t)) :=
  Req_refl _
theorem tailDens5_F (C : NormCtx) (x t : Real) : Req ((tailDens5 C).F x t) (Rmul c4 (tailDensity C t)) :=
  Req_refl _
theorem farDens5_F (C : NormCtx) (fc : Real) (x t : Real) :
    Req ((farDens5 C fc).F x t) (Rmul c4 (Rmul (Rmul cTwo fc) (Rmul (ofQ C.w C.hw) (rEv C t)))) :=
  Req_refl _

-- ===========================================================================
-- (3) The carrier, the channel Grams, and the quadratic form.
-- ===========================================================================

/-- **The five-channel carrier**: one certified field per channel (the prime channel indexed by the place). -/
structure Carrier5 where
  pole : CField
  prime : Nat → CField
  const : CField
  tail : CField
  far : CField

/-- The Haar Gram `∫₀¹ d·u·v` of a `t`-channel (evaluated at the inert scale `1`). -/
def gramT (C : NormCtx) (d u v : CField) : Real := intT C (mulF (mulF d u) v) one
/-- The iterated Gram `∫_{[lo,lo+w]}∫₀¹ d·u·v` of an `(x,t)`-channel. -/
def gramX (C : NormCtx) (d u v : CField) (lo w : Q) (hlo : 0 < lo.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) : Real :=
  intX C (mulF (mulF d u) v) lo w hlo hw hwn

def poleW (C : NormCtx) : Q := Qsub (canonB C) (⟨1, 1⟩ : Q)
theorem poleW_den (C : NormCtx) : 0 < (poleW C).den := Qsub_den_pos (canonB_den C) Nat.one_pos
theorem poleW_num (C : NormCtx) : 0 ≤ (poleW C).num := Qsub_num_nonneg (canonB_one C)
def tailLo (k : Nat) : Q := add (⟨1, 1⟩ : Q) (dyQ k)
theorem tailLo_den (k : Nat) : 0 < (tailLo k).den := add_den_pos Nat.one_pos (dyQ_den k)

/-- The pole channel Gram on `[1,B]`. -/
def poleG (C : NormCtx) (u v : CField) : Real := gramX C (poleDens5 C) u v (⟨1, 1⟩ : Q) (poleW C) Nat.one_pos (poleW_den C) (poleW_num C)
/-- The folded prime channel Gram at place `m`. -/
def primeG (C : NormCtx) (m : Nat) (u v : CField) : Real := gramT C (primeDens5 C m) u v
/-- The constant channel Gram. -/
def constG (C : NormCtx) (u v : CField) : Real := gramT C (constDens5 C) u v
/-- The compact tail channel Gram on `[1+2^{-k}, B]`. -/
def tailG (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (u v : CField) : Real :=
  gramX C (tailDens5 C) u v (tailLo k) (tailGap C k) (tailLo_den k) (tailGap_den C k) (tailGap_num_nonneg C k hk)
/-- The far channel Gram with scalar mass `fc`. -/
def farG (C : NormCtx) (fc : Real) (u v : CField) : Real := gramT C (farDens5 C fc) u v

/-- The four compact channels. -/
def inner4 (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (z₁ z₂ : Carrier5) : Real :=
  Radd (Radd (Radd (poleG C z₁.pole z₂.pole) (RsumN (fun m => primeG C m (z₁.prime m) (z₂.prime m)) C.X))
    (constG C z₁.const z₂.const)) (tailG C k hk z₁.tail z₂.tail)

/-- **★ THE FIVE-CHANNEL QUADRATIC FORM** (the same on the cut and on the cycle carrier). -/
def inner5 (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (z₁ z₂ : Carrier5) : Real :=
  Radd (inner4 C k hk z₁ z₂) (farG C fc z₁.far z₂.far)

/-- The energy `⟨z,z⟩`. -/
def energy5 (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (fc : Real) (z : Carrier5) : Real := inner5 C k hk fc z z

-- ===========================================================================
-- (4) The coordinate fields of a test and the two analyses.
-- ===========================================================================

/-- `t ↦ V(f,t)`. -/
def VF (C : NormCtx) (f : L2Test) : CField :=
  ofT (fun t => Vc C f t) (reflectTest C.a C.han C.had f).hLd (reflectTest C.a C.han C.had f).hLn
    (reflectTest C.a C.han C.had f).hMd (reflectTest C.a C.han C.had f).hMn
    (reflectTest C.a C.han C.had f).hlip (reflectTest C.a C.han C.had f).hbd (reflectTest C.a C.han C.had f).hfc

/-- The uniform Haar modulus of `t ↦ f(x/max(t,a))`. -/
def dilTL (C : NormCtx) (f : L2Test) : Q := mul (mul f.L C.S) (mul (Qinv C.a) (Qinv C.a))
theorem dilTL_den (C : NormCtx) (f : L2Test) : 0 < (dilTL C f).den := (dilRef C one f).hLd
theorem dilTL_num (C : NormCtx) (f : L2Test) : 0 ≤ (dilTL C f).num := (dilRef C one f).hLn

/-- `(x,t) ↦ U_x(f,t)`. -/
def UF (C : NormCtx) (f : L2Test) : CField where
  F := fun x t => Uc C x f t
  Lx := UcL C f
  Lt := mul (Qinv (canonC C)) (dilTL C f)
  M := mul (Qinv (canonC C)) f.M
  hLxd := UcL_den C f
  hLxn := UcL_num C f
  hLtd := Qmul_den_pos (Qinv_den_pos (canonC_num C)) (dilTL_den C f)
  hLtn := Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) (dilTL_num C f)
  hMd := Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd
  hMn := Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) f.hMn
  hlipx := fun t x x' => Uc_lip_x C f t x x'
  hlipt := fun x t t' => lip_const_mul_left (F := fun t => (dilRef C x f).f t) (dilRef C x f).hLd (dilRef C x f).hLn
    (dilRef C x f).hlip (invSq C x) (Qinv_den_pos (canonC_num C)) (invSq_bd C x) t t'
  hbd := fun x t => Uc_bd C f x t
  hfcx := @fun _ _ t h => Uc_congr_x C h f t
  hfct := @fun x _ _ h => Rmul_congr (Req_refl _) ((dilRef C x f).hfc _ _ h)

/-- `t ↦ U_x(f,t)` at a fixed scale (constant in the scale variable). -/
def UFix (C : NormCtx) (x : Real) (f : L2Test) : CField :=
  ofT (fun t => Uc C x f t) (UF C f).hLtd (UF C f).hLtn (UF C f).hMd (UF C f).hMn
    ((UF C f).hlipt x) ((UF C f).hbd x) (fun _ _ h => (UF C f).hfct x h)

/-- `(x,t) ↦ D_x(f,t) = U_x − (1/max(x,1))·V`. -/
def DF (C : NormCtx) (f : L2Test) : CField := subF (UF C f) (mulF rOneF (VF C f))
theorem DF_F (C : NormCtx) (f : L2Test) (x t : Real) : (DF C f).F x t = Dc C x f t := rfl

/-- `(x,t) ↦ D_{x̄}(f,t)`. -/
def DFcl (C : NormCtx) (f : L2Test) : CField :=
  compX (DF C f) (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)

/-- `(x,t) ↦ Z_{k,x̄}(f,t) = x̄·K_k(x̄)·D_{x̄}(f,t)`. -/
def ZF (C : NormCtx) (k : Nat) (f : L2Test) : CField := mulF (mulF (xclF C) (KxF C k)) (DFcl C f)
theorem ZF_F (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (ZF C k f).F x t = Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t := rfl

/-- `(x,t) ↦ W_{x̄}(f,t) = (1/max(x̄,1))·V(f,t)`. -/
def WF (C : NormCtx) (f : L2Test) : CField :=
  mulF (compX rOneF (xcl C) Nat.one_pos (by decide) (xcl_lip1 C) (fun _ _ h => xcl_congr C h)) (VF C f)
theorem WF_F (C : NormCtx) (f : L2Test) (x t : Real) : (WF C f).F x t = Wc C (xcl C x) f t := rfl

/-- **★ THE CUT ANALYSIS** `A_k f`: the cut coordinates `(u − v)/4` of the five channel fibers. -/
def cutAnalysis5 (C : NormCtx) (k : Nat) (f : L2Test) : Carrier5 where
  pole := aCoefF (UF C f) (negF (VF C f))
  prime := fun m => aCoefF (UFix C (upR m) f) (VF C f)
  const := aCoefF (VF C f) (VF C f)
  tail := aCoefF (ZF C k f) (WF C f)
  far := aCoefF (VF C f) (negF (VF C f))

/-- **★ THE CYCLE ANALYSIS** `B_k f`: the cycle coordinates `(u + v)/4` of the five channel fibers. -/
def cycleAnalysis5 (C : NormCtx) (k : Nat) (f : L2Test) : Carrier5 where
  pole := bCoefF (UF C f) (negF (VF C f))
  prime := fun m => bCoefF (UFix C (upR m) f) (VF C f)
  const := bCoefF (VF C f) (VF C f)
  tail := bCoefF (ZF C k f) (WF C f)
  far := bCoefF (VF C f) (negF (VF C f))

theorem cutAnalysis5_pole (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cutAnalysis5 C k f).pole.F x t = aCoefGa one (Uc C x f t) (Rneg (Vc C f t)) := rfl
theorem cutAnalysis5_prime (C : NormCtx) (k m : Nat) (f : L2Test) (x t : Real) :
    ((cutAnalysis5 C k f).prime m).F x t = aCoefGa one (Uc C (upR m) f t) (Vc C f t) := rfl
theorem cutAnalysis5_const (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cutAnalysis5 C k f).const.F x t = aCoefGa one (Vc C f t) (Vc C f t) := rfl
theorem cutAnalysis5_tail (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cutAnalysis5 C k f).tail.F x t = aCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t) (Wc C (xcl C x) f t) := rfl
theorem cutAnalysis5_far (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cutAnalysis5 C k f).far.F x t = aCoefGa one (Vc C f t) (Rneg (Vc C f t)) := rfl
theorem cycleAnalysis5_pole (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cycleAnalysis5 C k f).pole.F x t = bCoefGa one (Uc C x f t) (Rneg (Vc C f t)) := rfl
theorem cycleAnalysis5_prime (C : NormCtx) (k m : Nat) (f : L2Test) (x t : Real) :
    ((cycleAnalysis5 C k f).prime m).F x t = bCoefGa one (Uc C (upR m) f t) (Vc C f t) := rfl
theorem cycleAnalysis5_const (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cycleAnalysis5 C k f).const.F x t = bCoefGa one (Vc C f t) (Vc C f t) := rfl
theorem cycleAnalysis5_tail (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cycleAnalysis5 C k f).tail.F x t = bCoefGa one (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f t) (Wc C (xcl C x) f t) := rfl
theorem cycleAnalysis5_far (C : NormCtx) (k : Nat) (f : L2Test) (x t : Real) :
    (cycleAnalysis5 C k f).far.F x t = bCoefGa one (Vc C f t) (Rneg (Vc C f t)) := rfl

-- ===========================================================================
-- (5) The pointwise split under every channel density, and the four target-free channel splits.
-- ===========================================================================

/-- `d·(c·(A·A')) ≈ ((c·d)·A)·A'`. -/
theorem dens_split_alg (d c A A' : Real) : Req (Rmul d (Rmul c (Rmul A A'))) (Rmul (Rmul (Rmul c d) A) A') :=
  Req_trans (Req_symm (Rmul_assoc d c _)) (Req_trans (Rmul_congr (Rmul_comm d c) (Req_refl _)) (Req_symm (Rmul_assoc _ _ _)))

/-- **The pointwise split under a density**: `dens·⟨negFiber u_f v_f, M negFiber u_g v_g⟩ = (D5·A_f)·A_g − (D5·B_f)·B_g`
    for `D5 = 4·dens`. -/
theorem fiber_int_split {dens D5 : Real} (hD : Req D5 (Rmul c4 dens)) (uf vf ug vg : Real) :
    Req (Rmul dens (pairF (negFiber archAddr.1 archAddr.2 uf vf) (atlasOp (negFiber archAddr.1 archAddr.2 ug vg))))
        (Rsub (Rmul (Rmul D5 (aCoefGa one uf vf)) (aCoefGa one ug vg))
              (Rmul (Rmul D5 (bCoefGa one uf vf)) (bCoefGa one ug vg))) := by
  refine Req_trans (Rmul_congr (Req_refl _) (negFiber_split _ _ archAddr_valid.1 archAddr_valid.2 uf vf ug vg)) ?_
  refine Req_trans (Rmul_sub_distrib _ _ _) (Rsub_congr ?_ ?_)
  · exact Req_trans (dens_split_alg _ _ _ _) (Rmul_congr (Rmul_congr (Req_symm hD) (Req_refl _)) (Req_refl _))
  · exact Req_trans (dens_split_alg _ _ _ _) (Rmul_congr (Rmul_congr (Req_symm hD) (Req_refl _)) (Req_refl _))

/-- **★ POLE SPLIT**: `poleGram(f,g) = poleG(A_f, A_g) − poleG(B_f, B_g)`. -/
theorem poleGram_split (C : NormCtx) (k : Nat) (f g : L2Test) :
    Req (poleGram C f g)
        (Rsub (poleG C (cutAnalysis5 C k f).pole (cutAnalysis5 C k g).pole)
              (poleG C (cycleAnalysis5 C k f).pole (cycleAnalysis5 C k g).pole)) := by
  unfold poleGram poleG gramX CField.intX
  refine intI_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_ _ _ _ _ _
  intro x
  unfold poleInner CField.intT
  refine intU_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, mulF_F, mulF_F, cutAnalysis5_pole, cutAnalysis5_pole, cycleAnalysis5_pole, cycleAnalysis5_pole]
  unfold poleInt poleFiber posFiber affC
  exact fiber_int_split (poleDens5_F C x (affineMap C.a C.w C.had C.hw y)) (Uc C x f _) (Rneg (Vc C f _)) (Uc C x g _) (Rneg (Vc C g _))

/-- **★ PRIME SPLIT** at place `m`. -/
theorem primeFoldDirect_split (C : NormCtx) (k m : Nat) (f g : L2Test) :
    Req (primeFoldDirect C m f g)
        (Rsub (primeG C m ((cutAnalysis5 C k f).prime m) ((cutAnalysis5 C k g).prime m))
              (primeG C m ((cycleAnalysis5 C k f).prime m) ((cycleAnalysis5 C k g).prime m))) := by
  unfold primeFoldDirect primeG gramT CField.intT
  refine intU_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, mulF_F, mulF_F, cutAnalysis5_prime, cutAnalysis5_prime, cycleAnalysis5_prime, cycleAnalysis5_prime]
  unfold primeFoldInt primeFoldFiber affC
  exact fiber_int_split (primeDens5_F C m one (affineMap C.a C.w C.had C.hw y)) (Uc C (upR m) f _) (Vc C f _) (Uc C (upR m) g _) (Vc C g _)

/-- **★ PRIME SPLIT** (all places). -/
theorem primeFoldGram_split (C : NormCtx) (k : Nat) (f g : L2Test) :
    Req (primeFoldGram C f g)
        (Rsub (RsumN (fun m => primeG C m ((cutAnalysis5 C k f).prime m) ((cutAnalysis5 C k g).prime m)) C.X)
              (RsumN (fun m => primeG C m ((cycleAnalysis5 C k f).prime m) ((cycleAnalysis5 C k g).prime m)) C.X)) :=
  Req_trans (RsumN_congr C.X (fun m _ => primeFoldDirect_split C k m f g)) (RsumN_sub_f2 _ _ C.X)

/-- **★ CONSTANT SPLIT**. -/
theorem constGram_split (C : NormCtx) (k : Nat) (f g : L2Test) :
    Req (constGram C f g)
        (Rsub (constG C (cutAnalysis5 C k f).const (cutAnalysis5 C k g).const)
              (constG C (cycleAnalysis5 C k f).const (cycleAnalysis5 C k g).const)) := by
  unfold constGram constG gramT CField.intT
  refine intU_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, mulF_F, mulF_F, cutAnalysis5_const, cutAnalysis5_const, cycleAnalysis5_const, cycleAnalysis5_const]
  unfold constInt constFiber affC
  exact fiber_int_split (constDens5_F C one (affineMap C.a C.w C.had C.hw y)) (Vc C f _) (Vc C f _) (Vc C g _) (Vc C g _)

/-- **★ TAIL SPLIT**. -/
theorem tailGram_split (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : L2Test) :
    Req (tailGram C k hk f g)
        (Rsub (tailG C k hk (cutAnalysis5 C k f).tail (cutAnalysis5 C k g).tail)
              (tailG C k hk (cycleAnalysis5 C k f).tail (cycleAnalysis5 C k g).tail)) := by
  unfold tailGram tailG gramX CField.intX
  refine intI_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_ _ _ _ _ _
  intro x
  unfold tailInner CField.intT
  refine intU_sub_free _ _ _ _ _ _ _ _ _ _ _ _ ?_
  intro y
  rw [mulF_F, mulF_F, mulF_F, mulF_F, cutAnalysis5_tail, cutAnalysis5_tail, cycleAnalysis5_tail, cycleAnalysis5_tail]
  unfold tailInt tailFiber affC
  exact fiber_int_split (tailDens5_F C x (affineMap C.a C.w C.had C.hw y))
    (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f _) (Wc C (xcl C x) f _) (Zc C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) g _) (Wc C (xcl C x) g _)

/-- `(a − b) + (c − d) ≈ (a + c) − (b + d)`. -/
theorem add_sub_add_c5 (a b c d : Real) : Req (Radd (Rsub a b) (Rsub c d)) (Rsub (Radd a c) (Radd b d)) := by
  refine Req_trans ?_ (Radd_congr (Req_refl _) (Req_symm (Rneg_Radd b d)))
  -- (a + −b) + (c + −d) ≈ (a + c) + (−b + −d)
  refine Req_trans (Radd_assoc _ _ _) (Req_trans (Radd_congr (Req_refl _) ?_) (Req_symm (Radd_assoc _ _ _)))
  refine Req_trans (Req_symm (Radd_assoc _ _ _)) (Req_trans (Radd_congr (Radd_comm _ _) (Req_refl _)) (Radd_assoc _ _ _))

/-- **★ THE FOUR-CHANNEL SPLIT**: `atlasDefectGram_k(f,g) = inner4(A_k f, A_k g) − inner4(B_k f, B_k g)`. -/
theorem atlasDefectGram_split (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : L2Test) :
    Req (atlasDefectGram C k hk f g)
        (Rsub (inner4 C k hk (cutAnalysis5 C k f) (cutAnalysis5 C k g))
              (inner4 C k hk (cycleAnalysis5 C k f) (cycleAnalysis5 C k g))) := by
  unfold atlasDefectGram inner4
  refine Req_trans (Radd_congr (Radd_congr (Radd_congr (poleGram_split C k f g) (primeFoldGram_split C k f g))
    (constGram_split C k f g)) (tailGram_split C k hk f g)) ?_
  refine Req_trans (Radd_congr (Radd_congr (add_sub_add_c5 _ _ _ _) (Req_refl _)) (Req_refl _)) ?_
  refine Req_trans (Radd_congr (add_sub_add_c5 _ _ _ _) (Req_refl _)) ?_
  exact add_sub_add_c5 _ _ _ _

end UOR.Bridge.F1Square.Square
