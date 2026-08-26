/-
F1 square — **the archimedean channel Grams: constant, pole, and compact tail** (`AtlasArchGram.lean`,
AC-22 item 3, target-free).

Each archimedean term of the coupled form is realized as a certified (iterated) integral of the
pointwise fiber pairing `density·⟨Φ_f, MΦ_g⟩` of `AtlasFibers`, with the coordinates from the coherent
scale field `U_x, V, D_x` (`AtlasScaleField`):

 * CONSTANT  `constGram(f,g)   = ∫₀¹ (log 4π + γ)·w·r·⟨constFiber_f, M constFiber_g⟩`
             `= −(log 4π + γ)·w·∫₀¹ V(f)V(g)r`  (`constGram_eq`);  `ArchConstForm = +(…)` (`ArchConstForm_eq_vv`);
 * POLE      `poleGram(f,g)    = ∫_{x∈[1,B]} ∫₀¹ 2(1+1/x)·w·r·⟨poleFiber_x f, M poleFiber_x g⟩ dt dx`,
             inner value `(1+1/x)·w·(x^{-1/2}∫cross_{fg} + x^{-1/2}∫cross_{gf})`  (`poleInner_eq`);
 * TAIL      `tailGram_k(f,g)  = ∫_{x∈[1+2^{-k},B]} ∫₀¹ 2·w·r·⟨tailFiber_{k,x̄} f, M tailFiber_{k,x̄} g⟩ dt dx`,
             `x̄ = band_{[1,B]}(x)` (inert on the window; it makes the outer integrand a globally certified
             function), inner value `−w·K_k(x̄)·defectIntegral(x̄)`  (`tailInner_eq`).

The outer integrands are the inner Haar integrals, certified in the scale variable through
`param_integral_lip` from the uniform-in-`t` moduli of the coordinates (`Uc_lip_x`, `Dc_lip_x`).
No target form is imported; nothing here is a sign claim.  The identification with `PoleForm`,
`ArchConstForm` and `compactTail` is in `AtlasDefectReadback.lean`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasPrimeFold

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (0) The compact tail domain `[1 + 2^{-k}, B]` (moved from `AtlasTailSplit`).
-- ===========================================================================

/-- The gap `B − (1 + 2^{-k})`. -/
def tailGap (C : NormCtx) (k : Nat) : Q := Qsub (canonB C) (add (⟨1, 1⟩ : Q) (dyQ k))

theorem tailGap_den (C : NormCtx) (k : Nat) : 0 < (tailGap C k).den :=
  Qsub_den_pos (canonB_den C) (add_den_pos Nat.one_pos (dyQ_den k))

/-- `2 ≤ 2^k` for `k ≥ 1`. -/
theorem two_le_two_pow (k : Nat) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
  simpa using this

/-- `B − 1 − 2^{-k} > 0` for `k ≥ 1` (`X ≥ 1`). -/
theorem tailGap_num_pos (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : 0 < (tailGap C k).num := by
  have hp : 2 ≤ 2 ^ k := two_le_two_pow k hk
  have hXp : 2 ^ k ≤ C.X * 2 ^ k := Nat.le_mul_of_pos_left _ C.hX
  show (0 : Int) < ((C.X + 1 : Nat) : Int) * ((1 * 2 ^ k : Nat) : Int)
      + (-((1 * 2 ^ k + 1 * 1 : Nat) : Int)) * ((1 : Nat) : Int)
  have hp' : ((2 : Nat) : Int) ≤ ((2 ^ k : Nat) : Int) := by exact_mod_cast hp
  have hXp' : ((2 ^ k : Nat) : Int) ≤ ((C.X * 2 ^ k : Nat) : Int) := by exact_mod_cast hXp
  push_cast at hp' hXp' ⊢
  generalize hP : (2 : Int) ^ k = p at hp' hXp' ⊢
  have e : ((C.X : Int) + 1) * (1 * p) + -(1 * p + 1) * 1 = ((C.X : Int) * p + p) - p - 1 := by ring_uor
  omega

theorem tailGap_num_nonneg (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : 0 ≤ (tailGap C k).num :=
  Int.le_of_lt (tailGap_num_pos C k hk)

-- ===========================================================================
-- (1) Lipschitz/bound helpers.
-- ===========================================================================

/-- `x ↦ F(x)·c` is `L·M_c`-Lipschitz when `F` is `L`-Lipschitz and `|c| ≤ M_c`. -/
theorem lip_mul_const_right {F : Real → Real} {L : Q} (hLd : 0 < L.den)
    (hF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (c : Real) {Mc : Q} (hMd : 0 < Mc.den) (hMn : 0 ≤ Mc.num) (hc : Rle (Rabs c) (ofQ Mc hMd)) : ∀ x y,
    Rle (Rabs (Rsub (Rmul (F x) c) (Rmul (F y) c))) (Rmul (ofQ (mul L Mc) (Qmul_den_pos hLd hMd)) (Rabs (Rsub x y))) := by
  intro x y
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rsub_mul_ac _ _ _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ hMd hMn) (hF x y) hc) ?_
  exact Rle_of_Req (Req_trans (Rmul_assoc _ _ _) (Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _))
    (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ hLd hMd) (Req_refl _)))))

/-- `x ↦ c·F(x)` is `M_c·L`-Lipschitz. -/
theorem lip_const_mul_left {F : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (c : Real) {Mc : Q} (hMd : 0 < Mc.den) (hc : Rle (Rabs c) (ofQ Mc hMd)) : ∀ x y,
    Rle (Rabs (Rsub (Rmul c (F x)) (Rmul c (F y)))) (Rmul (ofQ (mul Mc L) (Qmul_den_pos hMd hLd)) (Rabs (Rsub x y))) := by
  intro x y
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib _ _ _)))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_Rmul (Rnonneg_ofQ hLd hLn) (Rnonneg_Rabs _)) hc (hF x y)) ?_
  exact Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) (Rmul_congr (Rmul_ofQ_ofQ hMd hLd) (Req_refl _)))

/-- `|a·b| ≤ M_a·M_b`. -/
theorem abs_mul_bd {a b : Real} {Ma Mb : Q} (hMad : 0 < Ma.den) (hMbd : 0 < Mb.den) (hMbn : 0 ≤ Mb.num)
    (ha : Rle (Rabs a) (ofQ Ma hMad)) (hb : Rle (Rabs b) (ofQ Mb hMbd)) :
    Rle (Rabs (Rmul a b)) (ofQ (mul Ma Mb) (Qmul_den_pos hMad hMbd)) :=
  Rle_trans (Rle_of_Req (Rabs_Rmul _ _))
    (Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ hMbd hMbn) ha hb) (Rle_of_Req (Rmul_ofQ_ofQ hMad hMbd)))

/-- `|a + b| ≤ M_a + M_b`. -/
theorem abs_add_bd {a b : Real} {Ma Mb : Q} (hMad : 0 < Ma.den) (hMbd : 0 < Mb.den)
    (ha : Rle (Rabs a) (ofQ Ma hMad)) (hb : Rle (Rabs b) (ofQ Mb hMbd)) :
    Rle (Rabs (Radd a b)) (ofQ (add Ma Mb) (add_den_pos hMad hMbd)) :=
  Rle_trans (Rabs_Radd _ _) (Rle_trans (Radd_le_add ha hb) (Rle_of_Req (Radd_ofQ_ofQ hMad hMbd)))

-- --- bounds and moduli of the raw coordinates ---

theorem Vc_bd (C : NormCtx) (f : L2Test) (t : Real) : Rle (Rabs (Vc C f t)) (ofQ f.M f.hMd) :=
  (reflectTest C.a C.han C.had f).hbd t

/-- `|U_x(f,t)| ≤ (1/c)·M_f`. -/
theorem Uc_bd (C : NormCtx) (f : L2Test) (x t : Real) :
    Rle (Rabs (Uc C x f t)) (ofQ (mul (Qinv (canonC C)) f.M) (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd)) :=
  abs_mul_bd (Qinv_den_pos (canonC_num C)) f.hMd f.hMn (invSq_bd C x) (dil_bd C f t x)

theorem rOne_bd (x : Real) : Rle (Rabs (rOne x)) (ofQ (Qinv (⟨1, 1⟩ : Q)) (Qinv_den_pos (by decide))) :=
  (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)).hbd x

theorem one_add_rOne_bd (x : Real) :
    Rle (Rabs (Radd one (rOne x))) (ofQ (add (⟨1, 1⟩ : Q) (Qinv (⟨1, 1⟩ : Q))) (add_den_pos Nat.one_pos (Qinv_den_pos (by decide)))) :=
  abs_add_bd Nat.one_pos (Qinv_den_pos (by decide)) (Rle_of_Req (Rabs_ofQ_nonneg (by decide) (by decide))) (rOne_bd x)

/-- `x ↦ 1 + 1/max(x,1)` is `1`-Lipschitz (modulus `(1/1)·(1/1)`). -/
theorem one_add_rOne_lip : ∀ x y,
    Rle (Rabs (Rsub (Radd one (rOne x)) (Radd one (rOne y))))
        (Rmul (ofQ (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide))))
          (Rabs (Rsub x y))) := by
  intro x y
  have h : Req (Rsub (Radd one (rOne x)) (Radd one (rOne y))) (Rsub (rOne x) (rOne y)) :=
    Req_trans (Rsub_Radd_Radd one (rOne x) one (rOne y))
      (Req_trans (Radd_congr (Radd_neg one) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _)))
  exact Rle_trans (Rle_of_Req (Rabs_congr h)) (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide) x y)

/-- `|w·r(t)| ≤ w·(1/a)`. -/
theorem wr_bd (C : NormCtx) (t : Real) :
    Rle (Rabs (Rmul (ofQ C.w C.hw) (rEv C t))) (ofQ (mul C.w (Qinv C.a)) (Qmul_den_pos C.hw (Qinv_den_pos C.han))) :=
  abs_mul_bd C.hw (Qinv_den_pos C.han) (Int.le_of_lt (Qinv_num_pos C.had))
    (Rle_of_Req (Rabs_ofQ_nonneg C.hw C.hwn)) ((recipTest C.a C.han C.had).hbd t)

theorem UcL_num (C : NormCtx) (f : L2Test) : 0 ≤ (UcL C f).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) (dilL_num C f))
    (Qmul_num_nonneg f.hMn (invSqL_num C))

-- ===========================================================================
-- (2) THE CONSTANT CHANNEL.
-- ===========================================================================

/-- The pulled-back constant pairing integrand `constDensity(t)·⟨constFiber_f(t), M constFiber_g(t)⟩`. -/
def constInt (C : NormCtx) (f g : L2Test) (y : Real) : Real :=
  Rmul (constDensity C (affC C y)) (pairF (constFiber C f (affC C y)) (atlasOp (constFiber C g (affC C y))))

/-- Its explicit form `−(archConst·w)·vvInt`. -/
def constExp (C : NormCtx) (f g : L2Test) (y : Real) : Real :=
  Rneg (Rmul (Rmul archConst (ofQ C.w C.hw)) (vvInt C f g y))

/-- `(a·(w·r))·P ≈ (a·w)·(P·r)`. -/
theorem const_pt_alg (a w r P : Real) : Req (Rmul (Rmul a (Rmul w r)) P) (Rmul (Rmul a w) (Rmul P r)) := by
  refine Req_trans (Rmul_congr (Req_symm (Rmul_assoc a w r)) (Req_refl P)) ?_
  exact Req_trans (Rmul_assoc (Rmul a w) r P) (Rmul_congr (Req_refl _) (Rmul_comm r P))

theorem constInt_eq_exp (C : NormCtx) (f g : L2Test) (y : Real) : Req (constInt C f g y) (constExp C f g y) := by
  unfold constInt constExp
  refine Req_trans (constFiber_readback C f g (affC C y)) (Rneg_congr ?_)
  refine Req_trans (const_pt_alg _ _ _ _) (Rmul_congr (Req_refl _) ?_)
  unfold vvInt prodInt Vc vEv
  exact Req_refl _

def constExpL (C : NormCtx) (f g : L2Test) : Q := mul (xBQ (Rmul archConst (ofQ C.w C.hw))) (vvL C f g)
theorem constExpL_den (C : NormCtx) (f g : L2Test) : 0 < (constExpL C f g).den := Qmul_den_pos Nat.one_pos (vvL_den C f g)
theorem constExpL_num (C : NormCtx) (f g : L2Test) : 0 ≤ (constExpL C f g).num := Qmul_num_nonneg (xBQ_num_nonneg _) (vvL_num C f g)
theorem constExpPos_lip (C : NormCtx) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Rmul (Rmul archConst (ofQ C.w C.hw)) (vvInt C f g y)) (Rmul (Rmul archConst (ofQ C.w C.hw)) (vvInt C f g z))))
        (Rmul (ofQ (constExpL C f g) (constExpL_den C f g)) (Rabs (Rsub y z))) :=
  lip_smul_fl _ (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g)
theorem constExpPos_fc (C : NormCtx) (f g : L2Test) : ∀ y z, Req y z →
    Req (Rmul (Rmul archConst (ofQ C.w C.hw)) (vvInt C f g y)) (Rmul (Rmul archConst (ofQ C.w C.hw)) (vvInt C f g z)) :=
  fc_smul_fl _ (vvInt_fc C f g)
theorem constExp_lip (C : NormCtx) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (constExp C f g y) (constExp C f g z))) (Rmul (ofQ (constExpL C f g) (constExpL_den C f g)) (Rabs (Rsub y z))) :=
  lip_neg_pi (constExpL_den C f g) (constExpPos_lip C f g)
theorem constExp_fc (C : NormCtx) (f g : L2Test) : ∀ y z, Req y z → Req (constExp C f g y) (constExp C f g z) :=
  fun y z h => Rneg_congr (constExpPos_fc C f g y z h)
theorem constInt_lip (C : NormCtx) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (constInt C f g y) (constInt C f g z))) (Rmul (ofQ (constExpL C f g) (constExpL_den C f g)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (constInt_eq_exp C f g) (constExp_lip C f g)
theorem constInt_fc (C : NormCtx) (f g : L2Test) : ∀ y z, Req y z → Req (constInt C f g y) (constInt C f g z) :=
  fc_of_congr_pd (constInt_eq_exp C f g) (constExp_fc C f g)

/-- **The constant Gram** `∫₀¹ constDensity·⟨constFiber_f, M constFiber_g⟩`. -/
def constGram (C : NormCtx) (f g : L2Test) : Real :=
  riemannIntegral (constExpL_den C f g) (constExpL_num C f g) (constInt_lip C f g) (constInt_fc C f g)

/-- `constGram = −(archConst·w)·∫₀¹ V(f)V(g)r`. -/
theorem constGram_eq (C : NormCtx) (f g : L2Test) :
    Req (constGram C f g)
        (Rneg (Rmul (Rmul archConst (ofQ C.w C.hw))
          (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)))) := by
  unfold constGram
  refine Req_trans (riemannIntegral_congr (constExpL_den C f g) (constExpL_num C f g) (constInt_lip C f g) (constInt_fc C f g)
    (constExp_lip C f g) (constExp_fc C f g) (constInt_eq_exp C f g)) ?_
  refine Req_trans (riemannIntegral_neg (constExpL_den C f g) (constExpL_num C f g) (constExpPos_lip C f g) (constExpPos_fc C f g)
    (constExp_lip C f g) (constExp_fc C f g)) (Rneg_congr ?_)
  exact riemannIntegral_smul_real_fl _ (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)

/-- **`ArchConstForm(f,g) = (log 4π + γ)·w·∫₀¹ V(f)V(g)r`** (`B_1`: `1^{-1/2} = 1`, `f(1·y) = f(y)`). -/
theorem ArchConstForm_eq_vv (C : NormCtx) (f g : L2Test) :
    Req (ArchConstForm f g C.a C.han C.had C.w C.hw C.hwn)
        (Rmul (Rmul archConst (ofQ C.w C.hw))
          (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g))) := by
  show Req (Rmul archConst (Rmul (normWeight (⟨1, 1⟩ : Q))
              (HForm f g pdOne.q pdOne.hqn pdOne.hqd C.a C.han C.had C.w C.hw C.hwn))) _
  rw [HForm_unfold C pdOne f g]
  have hnw : Req (normWeight (⟨1, 1⟩ : Q)) one :=
    Req_trans (normWeight_pos_eq (show (0 : Int) < 1 by decide)) Rsqrt_one
  have hlipV : ∀ y z, Rle (Rabs (Rsub (vvInt C f g y) (vvInt C f g z)))
      (Rmul (ofQ (hIntL C pdOne f g) (hIntL_den C pdOne f g)) (Rabs (Rsub y z))) :=
    lip_of_congr_pd _ (fun y => Req_symm (hInt_one_eq_vv C f g y)) (hInt_lip C pdOne f g)
  have hI : Req (riemannIntegral (hIntL_den C pdOne f g) (hIntL_num C pdOne f g) (hInt_lip C pdOne f g) (hInt_fc C pdOne f g))
      (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)) :=
    Req_trans (riemannIntegral_congr (hIntL_den C pdOne f g) (hIntL_num C pdOne f g) (hInt_lip C pdOne f g)
        (hInt_fc C pdOne f g) hlipV (vvInt_fc C f g) (hInt_one_eq_vv C f g))
      (riemannIntegral_certif_irrel _ _ hlipV _ (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g))
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (Rmul_congr hnw (Rmul_congr (Req_refl _) hI)) (Rone_mul _))) ?_
  exact Req_symm (Rmul_assoc _ _ _)

-- ===========================================================================
-- (3) THE POLE CHANNEL: inner Haar integral, its scale-Lipschitz certificate, outer integral.
-- ===========================================================================

/-- The pulled-back pole pairing integrand at scale `x`. -/
def poleInt (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Rmul (poleDensity C x (affC C y)) (pairF (poleFiber C x f (affC C y)) (atlasOp (poleFiber C x g (affC C y))))

/-- The symmetric raw integrand `x^{-1/2}·(cross_{fg} + cross_{gf})`. -/
def symInt (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Radd (Rmul (invSq C x) (crossInt C x f g y)) (Rmul (invSq C x) (crossInt C x g f y))
def symL (C : NormCtx) (x : Real) (f g : L2Test) : Q :=
  add (mul (xBQ (invSq C x)) (crossL C x f g)) (mul (xBQ (invSq C x)) (crossL C x g f))
theorem symL_den (C : NormCtx) (x : Real) (f g : L2Test) : 0 < (symL C x f g).den :=
  add_den_pos (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _))
theorem symL_num (C : NormCtx) (x : Real) (f g : L2Test) : 0 ≤ (symL C x f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)) (Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _))
theorem symInt_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (symInt C x f g y) (symInt C x f g z))) (Rmul (ofQ (symL C x f g) (symL_den C x f g)) (Rabs (Rsub y z))) :=
  lip_add_fl (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)) (p1_lip C x f g) (p1_lip C x g f)
theorem symInt_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (symInt C x f g y) (symInt C x f g z) :=
  fun y z h => Radd_congr (fc_smul_fl _ (crossInt_fc C x f g) y z h) (fc_smul_fl _ (crossInt_fc C x g f) y z h)

/-- `symInt = (U_x(f)V(g))r + (V(f)U_x(g))r` pointwise. -/
theorem symInt_eq_UV (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) :
    Req (symInt C x f g y)
        (Radd (Rmul (Rmul (Uc C x f (affC C y)) (Vc C g (affC C y))) (rEv C (affC C y)))
              (Rmul (Rmul (Vc C f (affC C y)) (Uc C x g (affC C y))) (rEv C (affC C y)))) := by
  unfold symInt crossInt prodInt Uc Vc vEv
  exact Radd_congr (pull_af _ _ _ _) (Req_trans (pull_af _ _ _ _) (Rmul_congr (Rmul_comm _ _) (Req_refl _)))

/-- The explicit form `((1 + 1/x)·w)·symInt`. -/
def poleExp (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Rmul (Rmul (Radd one (rOne x)) (ofQ C.w C.hw)) (symInt C x f g y)

theorem poleInt_eq_exp (C : NormCtx) (x : Real) (f g : L2Test) (y : Real) : Req (poleInt C x f g y) (poleExp C x f g y) := by
  unfold poleInt poleExp
  refine Req_trans (poleFiber_readback C x f g (affC C y)) ?_
  exact Req_trans (fold_pt_alg _ _ _ _ _) (Rmul_congr (Req_refl _) (Req_symm (symInt_eq_UV C x f g y)))

def poleExpL (C : NormCtx) (x : Real) (f g : L2Test) : Q := mul (xBQ (Rmul (Radd one (rOne x)) (ofQ C.w C.hw))) (symL C x f g)
theorem poleExpL_den (C : NormCtx) (x : Real) (f g : L2Test) : 0 < (poleExpL C x f g).den := Qmul_den_pos Nat.one_pos (symL_den C x f g)
theorem poleExpL_num (C : NormCtx) (x : Real) (f g : L2Test) : 0 ≤ (poleExpL C x f g).num := Qmul_num_nonneg (xBQ_num_nonneg _) (symL_num C x f g)
theorem poleExp_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (poleExp C x f g y) (poleExp C x f g z))) (Rmul (ofQ (poleExpL C x f g) (poleExpL_den C x f g)) (Rabs (Rsub y z))) :=
  lip_smul_fl _ (symL_den C x f g) (symL_num C x f g) (symInt_lip C x f g)
theorem poleExp_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (poleExp C x f g y) (poleExp C x f g z) :=
  fc_smul_fl _ (symInt_fc C x f g)
theorem poleInt_lip (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (poleInt C x f g y) (poleInt C x f g z))) (Rmul (ofQ (poleExpL C x f g) (poleExpL_den C x f g)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (poleInt_eq_exp C x f g) (poleExp_lip C x f g)
theorem poleInt_fc (C : NormCtx) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (poleInt C x f g y) (poleInt C x f g z) :=
  fc_of_congr_pd (poleInt_eq_exp C x f g) (poleExp_fc C x f g)

/-- **The inner pole integral** `∫₀¹ poleDensity·⟨poleFiber_x f, M poleFiber_x g⟩` at scale `x`. -/
def poleInner (C : NormCtx) (x : Real) (f g : L2Test) : Real :=
  riemannIntegral (poleExpL_den C x f g) (poleExpL_num C x f g) (poleInt_lip C x f g) (poleInt_fc C x f g)

/-- `poleInner(x) = ((1 + 1/x)·w)·(x^{-1/2}∫cross_{fg} + x^{-1/2}∫cross_{gf})`. -/
theorem poleInner_eq (C : NormCtx) (x : Real) (f g : L2Test) :
    Req (poleInner C x f g)
        (Rmul (Rmul (Radd one (rOne x)) (ofQ C.w C.hw))
          (Radd (Rmul (invSq C x) (riemannIntegral (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g) (crossInt_fc C x f g)))
                (Rmul (invSq C x) (riemannIntegral (crossL_den C x g f) (crossL_num C x g f) (crossInt_lip C x g f) (crossInt_fc C x g f))))) := by
  unfold poleInner
  refine Req_trans (riemannIntegral_congr (poleExpL_den C x f g) (poleExpL_num C x f g) (poleInt_lip C x f g) (poleInt_fc C x f g)
    (poleExp_lip C x f g) (poleExp_fc C x f g) (poleInt_eq_exp C x f g)) ?_
  refine Req_trans (riemannIntegral_smul_real_fl _ (symL_den C x f g) (symL_num C x f g) (symInt_lip C x f g) (symInt_fc C x f g))
    (Rmul_congr (Req_refl _) ?_)
  have hL1d : 0 < (mul (xBQ (invSq C x)) (crossL C x f g)).den := Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)
  have hL1n : 0 ≤ (mul (xBQ (invSq C x)) (crossL C x f g)).num := Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)
  have hL2d : 0 < (mul (xBQ (invSq C x)) (crossL C x g f)).den := Qmul_den_pos Nat.one_pos (crossL_den _ _ _ _)
  have hL2n : 0 ≤ (mul (xBQ (invSq C x)) (crossL C x g f)).num := Qmul_num_nonneg (xBQ_num_nonneg _) (crossL_num _ _ _ _)
  have h1S := lip_weaken_fl hL1d (symL_den C x f g) (Qle_add_right_nonneg hL2n) (p1_lip C x f g)
  have h2S := lip_weaken_fl hL2d (symL_den C x f g) (Qle_add_left_nonneg hL1n) (p1_lip C x g f)
  refine Req_trans (riemannIntegral_add (symL_den C x f g) (symL_num C x f g) h1S (fc_smul_fl _ (crossInt_fc C x f g)) h2S
    (fc_smul_fl _ (crossInt_fc C x g f)) (symInt_lip C x f g) (symInt_fc C x f g)) ?_
  refine Radd_congr ?_ ?_
  · refine Req_trans (riemannIntegral_certif_irrel _ _ h1S _ hL1d hL1n (p1_lip C x f g) (fc_smul_fl _ (crossInt_fc C x f g))) ?_
    exact riemannIntegral_smul_real_fl (invSq C x) (crossL_den C x f g) (crossL_num C x f g) (crossInt_lip C x f g) (crossInt_fc C x f g)
  · refine Req_trans (riemannIntegral_certif_irrel _ _ h2S _ hL2d hL2n (p1_lip C x g f) (fc_smul_fl _ (crossInt_fc C x g f))) ?_
    exact riemannIntegral_smul_real_fl (invSq C x) (crossL_den C x g f) (crossL_num C x g f) (crossInt_lip C x g f) (crossInt_fc C x g f)

-- --- the scale-Lipschitz certificate of the pole integrand, uniform in `t` ---

/-- The readback form of the pole integrand at `(x,t)` (the RHS of `poleFiber_readback`). -/
def poleRB (C : NormCtx) (x : Real) (f g : L2Test) (t : Real) : Real :=
  Rmul (Rmul (Radd one (rOne x)) (Rmul (ofQ C.w C.hw) (rEv C t)))
       (Radd (Rmul (Uc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C x g t)))

/-- Modulus and bound of the density factor `(1 + 1/x)·w·r`. -/
def poleL1 (C : NormCtx) : Q := mul (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (mul C.w (Qinv C.a))
def poleM1 (C : NormCtx) : Q := mul (add (⟨1, 1⟩ : Q) (Qinv (⟨1, 1⟩ : Q))) (mul C.w (Qinv C.a))
theorem poleL1_den (C : NormCtx) : 0 < (poleL1 C).den :=
  Qmul_den_pos (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide))) (Qmul_den_pos C.hw (Qinv_den_pos C.han))
theorem poleM1_den (C : NormCtx) : 0 < (poleM1 C).den :=
  Qmul_den_pos (add_den_pos Nat.one_pos (Qinv_den_pos (by decide))) (Qmul_den_pos C.hw (Qinv_den_pos C.han))
theorem wa_num (C : NormCtx) : 0 ≤ (mul C.w (Qinv C.a)).num := Int.mul_nonneg C.hwn (Int.le_of_lt (Qinv_num_pos C.had))
theorem poleL1_num (C : NormCtx) : 0 ≤ (poleL1 C).num :=
  Qmul_num_nonneg (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) (Int.le_of_lt (Qinv_num_pos (by decide)))) (wa_num C)
theorem poleM1_num (C : NormCtx) : 0 ≤ (poleM1 C).num :=
  Qmul_num_nonneg (Qadd_num_nonneg_loc (by decide) (Int.le_of_lt (Qinv_num_pos (by decide)))) (wa_num C)
theorem poleF1_lip (C : NormCtx) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Rmul (Radd one (rOne x)) (Rmul (ofQ C.w C.hw) (rEv C t))) (Rmul (Radd one (rOne y)) (Rmul (ofQ C.w C.hw) (rEv C t)))))
        (Rmul (ofQ (poleL1 C) (poleL1_den C)) (Rabs (Rsub x y))) :=
  lip_mul_const_right _ one_add_rOne_lip _ (Qmul_den_pos C.hw (Qinv_den_pos C.han)) (wa_num C) (wr_bd C t)
theorem poleF1_bd (C : NormCtx) (t : Real) : ∀ x,
    Rle (Rabs (Rmul (Radd one (rOne x)) (Rmul (ofQ C.w C.hw) (rEv C t)))) (ofQ (poleM1 C) (poleM1_den C)) :=
  fun x => abs_mul_bd _ _ (wa_num C) (one_add_rOne_bd x) (wr_bd C t)

/-- Modulus and bound of the coordinate factor `U_x(f)V(g) + V(f)U_x(g)`. -/
def poleL2 (C : NormCtx) (f g : L2Test) : Q := add (mul (UcL C f) g.M) (mul f.M (UcL C g))
def poleM2 (C : NormCtx) (f g : L2Test) : Q :=
  add (mul (mul (Qinv (canonC C)) f.M) g.M) (mul f.M (mul (Qinv (canonC C)) g.M))
theorem poleL2_den (C : NormCtx) (f g : L2Test) : 0 < (poleL2 C f g).den :=
  add_den_pos (Qmul_den_pos (UcL_den C f) g.hMd) (Qmul_den_pos f.hMd (UcL_den C g))
theorem poleL2_num (C : NormCtx) (f g : L2Test) : 0 ≤ (poleL2 C f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (UcL_num C f) g.hMn) (Qmul_num_nonneg f.hMn (UcL_num C g))
theorem poleM2_den (C : NormCtx) (f g : L2Test) : 0 < (poleM2 C f g).den :=
  add_den_pos (Qmul_den_pos (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd) g.hMd)
    (Qmul_den_pos f.hMd (Qmul_den_pos (Qinv_den_pos (canonC_num C)) g.hMd))
theorem poleM2_num (C : NormCtx) (f g : L2Test) : 0 ≤ (poleM2 C f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) f.hMn) g.hMn)
    (Qmul_num_nonneg f.hMn (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) g.hMn))
theorem poleF2_lip (C : NormCtx) (f g : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Radd (Rmul (Uc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C x g t)))
                    (Radd (Rmul (Uc C y f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C y g t)))))
        (Rmul (ofQ (poleL2 C f g) (poleL2_den C f g)) (Rabs (Rsub x y))) :=
  lip_add_fl (Qmul_den_pos (UcL_den C f) g.hMd) (Qmul_den_pos f.hMd (UcL_den C g))
    (lip_mul_const_right (UcL_den C f) (Uc_lip_x C f t) (Vc C g t) g.hMd g.hMn (Vc_bd C g t))
    (lip_const_mul_left (UcL_den C g) (UcL_num C g) (Uc_lip_x C g t) (Vc C f t) f.hMd (Vc_bd C f t))
theorem poleF2_bd (C : NormCtx) (f g : L2Test) (t : Real) : ∀ x,
    Rle (Rabs (Radd (Rmul (Uc C x f t) (Vc C g t)) (Rmul (Vc C f t) (Uc C x g t)))) (ofQ (poleM2 C f g) (poleM2_den C f g)) :=
  fun x => abs_add_bd _ _ (abs_mul_bd _ _ g.hMn (Uc_bd C f x t) (Vc_bd C g t))
    (abs_mul_bd _ _ (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) g.hMn) (Vc_bd C f t) (Uc_bd C g x t))

/-- **The scale modulus of the pole integrand**, uniform in `t`. -/
def poleXL (C : NormCtx) (f g : L2Test) : Q := add (mul (poleM1 C) (poleL2 C f g)) (mul (poleM2 C f g) (poleL1 C))
theorem poleXL_den (C : NormCtx) (f g : L2Test) : 0 < (poleXL C f g).den :=
  add_den_pos (Qmul_den_pos (poleM1_den C) (poleL2_den C f g)) (Qmul_den_pos (poleM2_den C f g) (poleL1_den C))
theorem poleXL_num (C : NormCtx) (f g : L2Test) : 0 ≤ (poleXL C f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (poleM1_num C) (poleL2_num C f g)) (Qmul_num_nonneg (poleM2_num C f g) (poleL1_num C))

theorem poleRB_lip_x (C : NormCtx) (f g : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (poleRB C x f g t) (poleRB C y f g t))) (Rmul (ofQ (poleXL C f g) (poleXL_den C f g)) (Rabs (Rsub x y))) := by
  intro x y
  unfold poleRB
  exact Rmul_lipschitz (poleL1_den C) (poleL2_den C f g) (poleM1_den C) (poleM2_den C f g)
    (poleL1_num C) (poleL2_num C f g) (poleM1_num C) (poleM2_num C f g)
    (poleF1_lip C t) (poleF2_lip C f g t) (poleF1_bd C t) (poleF2_bd C f g t) x y

theorem poleRB_congr_x (C : NormCtx) {x y : Real} (h : Req x y) (f g : L2Test) (t : Real) :
    Req (poleRB C x f g t) (poleRB C y f g t) :=
  Rmul_congr (Rmul_congr (Radd_congr (Req_refl _) (clampedInv_congr _ _ _ h)) (Req_refl _))
    (Radd_congr (Rmul_congr (Uc_congr_x C h f t) (Req_refl _)) (Rmul_congr (Req_refl _) (Uc_congr_x C h g t)))

/-- The pole integrand is `poleXL`-Lipschitz in the scale, for every `y`. -/
theorem poleInt_lip_x (C : NormCtx) (f g : L2Test) (y : Real) : ∀ x x',
    Rle (Rabs (Rsub (poleInt C x f g y) (poleInt C x' f g y))) (Rmul (ofQ (poleXL C f g) (poleXL_den C f g)) (Rabs (Rsub x x'))) :=
  lip_of_congr_pd (F := fun x => poleInt C x f g y) (G := fun x => poleRB C x f g (affC C y)) _
    (fun x => poleFiber_readback C x f g (affC C y)) (poleRB_lip_x C f g (affC C y))

theorem poleInt_congr_x (C : NormCtx) {x x' : Real} (h : Req x x') (f g : L2Test) (y : Real) :
    Req (poleInt C x f g y) (poleInt C x' f g y) :=
  Req_trans (poleFiber_readback C x f g (affC C y))
    (Req_trans (poleRB_congr_x C h f g (affC C y)) (Req_symm (poleFiber_readback C x' f g (affC C y))))

/-- **★ The inner pole integral is `poleXL`-Lipschitz in the scale** (`param_integral_lip`). -/
theorem poleInner_lip (C : NormCtx) (f g : L2Test) : ∀ x x',
    Rle (Rabs (Rsub (poleInner C x f g) (poleInner C x' f g))) (Rmul (ofQ (poleXL C f g) (poleXL_den C f g)) (Rabs (Rsub x x'))) :=
  fun x x' => param_integral_lip (F := fun x y => poleInt C x f g y) (L := fun x => poleExpL C x f g)
    (fun x => poleExpL_den C x f g) (fun x => poleExpL_num C x f g) (fun x => poleInt_lip C x f g) (fun x => poleInt_fc C x f g)
    (poleXL_den C f g) (fun y _ _ x x' => poleInt_lip_x C f g y x x') x x'

theorem poleInner_fc (C : NormCtx) (f g : L2Test) : ∀ x x', Req x x' → Req (poleInner C x f g) (poleInner C x' f g) :=
  fun x x' h => param_integral_congr (F := fun x y => poleInt C x f g y) (L := fun x => poleExpL C x f g)
    (fun x => poleExpL_den C x f g) (fun x => poleExpL_num C x f g) (fun x => poleInt_lip C x f g) (fun x => poleInt_fc C x f g)
    x x' (fun y => poleInt_congr_x C h f g y)

/-- **★ THE POLE GRAM** `∫_{x∈[1,B]} poleInner(x) dx` — the certified outer integral of the inner fiber pairing. -/
def poleGram (C : NormCtx) (f g : L2Test) : Real :=
  riemannIntegralI (f := fun x => poleInner C x f g) (poleXL_den C f g) (poleXL_num C f g) (poleInner_lip C f g) (poleInner_fc C f g)
    (⟨1, 1⟩ : Q) (Qsub (canonB C) (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos (canonB_den C) Nat.one_pos) (Qsub_num_nonneg (canonB_one C))

-- ===========================================================================
-- (4) THE COMPACT TAIL CHANNEL: the `[1,B]`-clamped scale, inner integral, scale certificate, outer integral.
-- ===========================================================================

/-- The `[1,B]` band clamp of the scale — inert on the compact tail window, globally `1`-Lipschitz. -/
def xcl (C : NormCtx) (x : Real) : Real := qBandQ (⟨1, 1⟩ : Q) (canonB C) (by decide) (canonB_den C) x

theorem xcl_ge_one (C : NormCtx) (x : Real) : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) (xcl C x) := fun n =>
  Qle_trans ((xcl C x).den_pos n) (qBandQ_ge (⟨1, 1⟩ : Q) (canonB C) (by decide) (canonB_den C) (canonB_one C) x n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))
theorem xcl_le_B (C : NormCtx) (x : Real) : Rle (xcl C x) (ofQ (canonB C) (canonB_den C)) := fun n =>
  Qle_trans (canonB_den C) (qBandQ_le (⟨1, 1⟩ : Q) (canonB C) (by decide) (canonB_den C) x n)
    (Qle_self_add (by show (0 : Int) ≤ 2; decide))
theorem xcl_lip (C : NormCtx) (x y : Real) : Rle (Rabs (Rsub (xcl C x) (xcl C y))) (Rabs (Rsub x y)) :=
  qBandQ_lipschitz _ _ _ _ x y
theorem xcl_congr (C : NormCtx) {x y : Real} (h : Req x y) : Req (xcl C x) (xcl C y) := qBandQ_congr _ _ _ _ h
/-- On `[1, B]` the clamp is inert. -/
theorem xcl_eq_of_band (C : NormCtx) {x : Real} (h1 : Rle (ofQ (⟨1, 1⟩ : Q) (by decide)) x)
    (hB : Rle x (ofQ (canonB C) (canonB_den C))) : Req (xcl C x) x :=
  qBandQ_eq_of_band h1 hB

/-- Composition with the clamp preserves a Lipschitz certificate. -/
theorem lip_comp_xcl (C : NormCtx) {F : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) : ∀ x y,
    Rle (Rabs (Rsub (F (xcl C x)) (F (xcl C y)))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))) :=
  fun x y => Rle_trans (hF _ _) (Rmul_le_Rmul_left (Rnonneg_ofQ hLd hLn) (xcl_lip C x y))

/-- The floored kernel at the clamped scale. -/
def Kx (C : NormCtx) (k : Nat) (x : Real) : Real := Kfl (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x)
def kerL (k : Nat) : Q := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).L
def kerM (k : Nat) : Q := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).M
theorem kerL_den (k : Nat) : 0 < (kerL k).den := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hLd
theorem kerL_num (k : Nat) : 0 ≤ (kerL k).num := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hLn
theorem kerM_den (k : Nat) : 0 < (kerM k).den := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hMd
theorem kerM_num (k : Nat) : 0 ≤ (kerM k).num := (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hMn
theorem Kx_lip (C : NormCtx) (k : Nat) : ∀ x y,
    Rle (Rabs (Rsub (Kx C k x) (Kx C k y))) (Rmul (ofQ (kerL k) (kerL_den k)) (Rabs (Rsub x y))) :=
  lip_comp_xcl C (kerL_den k) (kerL_num k) (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hlip
theorem Kx_bd (C : NormCtx) (k : Nat) : ∀ x, Rle (Rabs (Kx C k x)) (ofQ (kerM k) (kerM_den k)) :=
  fun x => (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hbd (xcl C x)
theorem Kx_congr (C : NormCtx) (k : Nat) {x y : Real} (h : Req x y) : Req (Kx C k x) (Kx C k y) :=
  (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).hfc _ _ (xcl_congr C h)

/-- The pulled-back tail pairing integrand at the clamped scale. -/
def tailInt (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Rmul (tailDensity C (affC C y))
       (pairF (tailFiber C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) f (affC C y))
              (atlasOp (tailFiber C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) g (affC C y))))

/-- The readback form at `(x̄, t)` (the RHS of `tailFiber_readback`, valid since `x̄ ≥ 1`). -/
def tailRB (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (t : Real) : Real :=
  Rneg (Rmul (Rmul (ofQ C.w C.hw) (rEv C t))
    (Rmul (Kx C k x) (Radd (Rmul (Dc C (xcl C x) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C x) g t)))))

theorem tailInt_eq_RB (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (y : Real) :
    Req (tailInt C k x f g y) (tailRB C k x f g (affC C y)) :=
  tailFiber_readback C (dyQ k) (dyQ_num k) (dyQ_den k) (xcl C x) (xcl_ge_one C x) f g (affC C y)

/-- The explicit form `−(w·K(x̄))·defInt_{x̄}`. -/
def tailExp (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (y : Real) : Real :=
  Rneg (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defInt C (xcl C x) f g y))

/-- `(w·r)·(K·S) ≈ (w·K)·(S·r)`. -/
theorem tail_pt_alg (w r K S : Real) : Req (Rmul (Rmul w r) (Rmul K S)) (Rmul (Rmul w K) (Rmul S r)) :=
  Req_trans (mul4_swap_ch w r K S) (Rmul_congr (Req_refl _) (Rmul_comm r S))

theorem tailRB_eq_exp (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (y : Real) :
    Req (tailRB C k x f g (affC C y)) (tailExp C k x f g y) := by
  unfold tailRB tailExp defInt
  exact Rneg_congr (tail_pt_alg _ _ _ _)

theorem tailInt_eq_exp (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) (y : Real) :
    Req (tailInt C k x f g y) (tailExp C k x f g y) :=
  Req_trans (tailInt_eq_RB C k x f g y) (tailRB_eq_exp C k x f g y)

def tailExpL (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : Q :=
  mul (xBQ (Rmul (ofQ C.w C.hw) (Kx C k x))) (asmL C (xcl C x) f g)
theorem tailExpL_den (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : 0 < (tailExpL C k x f g).den :=
  Qmul_den_pos Nat.one_pos (asmL_den C (xcl C x) f g)
theorem tailExpL_num (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : 0 ≤ (tailExpL C k x f g).num :=
  Qmul_num_nonneg (xBQ_num_nonneg _) (asmL_num C (xcl C x) f g)
theorem tailExpPos_lip (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defInt C (xcl C x) f g y))
                    (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defInt C (xcl C x) f g z))))
        (Rmul (ofQ (tailExpL C k x f g) (tailExpL_den C k x f g)) (Rabs (Rsub y z))) :=
  lip_smul_fl _ (asmL_den C (xcl C x) f g) (asmL_num C (xcl C x) f g) (defInt_lip C (xcl C x) f g)
theorem tailExpPos_fc (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z, Req y z →
    Req (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defInt C (xcl C x) f g y))
        (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defInt C (xcl C x) f g z)) :=
  fc_smul_fl _ (defInt_fc C (xcl C x) f g)
theorem tailExp_lip (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (tailExp C k x f g y) (tailExp C k x f g z))) (Rmul (ofQ (tailExpL C k x f g) (tailExpL_den C k x f g)) (Rabs (Rsub y z))) :=
  lip_neg_pi (tailExpL_den C k x f g) (tailExpPos_lip C k x f g)
theorem tailExp_fc (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (tailExp C k x f g y) (tailExp C k x f g z) :=
  fun y z h => Rneg_congr (tailExpPos_fc C k x f g y z h)
theorem tailInt_lip (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z,
    Rle (Rabs (Rsub (tailInt C k x f g y) (tailInt C k x f g z))) (Rmul (ofQ (tailExpL C k x f g) (tailExpL_den C k x f g)) (Rabs (Rsub y z))) :=
  lip_of_congr_pd _ (tailInt_eq_exp C k x f g) (tailExp_lip C k x f g)
theorem tailInt_fc (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : ∀ y z, Req y z → Req (tailInt C k x f g y) (tailInt C k x f g z) :=
  fc_of_congr_pd (tailInt_eq_exp C k x f g) (tailExp_fc C k x f g)

/-- **The inner tail integral** `∫₀¹ tailDensity·⟨tailFiber_{k,x̄} f, M tailFiber_{k,x̄} g⟩`. -/
def tailInner (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) : Real :=
  riemannIntegral (tailExpL_den C k x f g) (tailExpL_num C k x f g) (tailInt_lip C k x f g) (tailInt_fc C k x f g)

/-- `tailInner(x) = −(w·K_k(x̄))·defectIntegral(x̄)`. -/
theorem tailInner_eq (C : NormCtx) (k : Nat) (x : Real) (f g : L2Test) :
    Req (tailInner C k x f g) (Rneg (Rmul (Rmul (ofQ C.w C.hw) (Kx C k x)) (defectIntegral C (xcl C x) f g))) := by
  unfold tailInner
  refine Req_trans (riemannIntegral_congr (tailExpL_den C k x f g) (tailExpL_num C k x f g) (tailInt_lip C k x f g) (tailInt_fc C k x f g)
    (tailExp_lip C k x f g) (tailExp_fc C k x f g) (tailInt_eq_exp C k x f g)) ?_
  refine Req_trans (riemannIntegral_neg (tailExpL_den C k x f g) (tailExpL_num C k x f g) (tailExpPos_lip C k x f g)
    (tailExpPos_fc C k x f g) (tailExp_lip C k x f g) (tailExp_fc C k x f g)) (Rneg_congr ?_)
  exact riemannIntegral_smul_real_fl _ (asmL_den C (xcl C x) f g) (asmL_num C (xcl C x) f g) (defInt_lip C (xcl C x) f g) (defInt_fc C (xcl C x) f g)

-- --- the scale-Lipschitz certificate of the tail integrand, uniform in `t` ---

theorem rVL_num (f : L2Test) : 0 ≤ (rVL f).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) (by decide))
    (Qmul_num_nonneg f.hMn (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) (Int.le_of_lt (Qinv_num_pos (by decide)))))
theorem DcL_num (C : NormCtx) (f : L2Test) : 0 ≤ (DcL C f).num := Qadd_num_nonneg_loc (UcL_num C f) (rVL_num f)

/-- The bound `|D_x(f,t)| ≤ (1/c)·M_f + 1·M_f`. -/
def DcM (C : NormCtx) (f : L2Test) : Q := add (mul (Qinv (canonC C)) f.M) (mul (Qinv (⟨1, 1⟩ : Q)) f.M)
theorem DcM_den (C : NormCtx) (f : L2Test) : 0 < (DcM C f).den :=
  add_den_pos (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd) (Qmul_den_pos (Qinv_den_pos (by decide)) f.hMd)
theorem DcM_num (C : NormCtx) (f : L2Test) : 0 ≤ (DcM C f).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (canonC_den C))) f.hMn)
    (Qmul_num_nonneg (Int.le_of_lt (Qinv_num_pos (by decide))) f.hMn)
theorem Dc_bd (C : NormCtx) (f : L2Test) (x t : Real) : Rle (Rabs (Dc C x f t)) (ofQ (DcM C f) (DcM_den C f)) := by
  have h2 : Rle (Rabs (Rneg (Rmul (rOne x) (Vc C f t))))
      (ofQ (mul (Qinv (⟨1, 1⟩ : Q)) f.M) (Qmul_den_pos (Qinv_den_pos (by decide)) f.hMd)) :=
    Rle_trans (Rle_of_Req (Rabs_Rneg _)) (abs_mul_bd (Qinv_den_pos (by decide)) f.hMd f.hMn (rOne_bd x) (Vc_bd C f t))
  exact abs_add_bd (Qmul_den_pos (Qinv_den_pos (canonC_num C)) f.hMd) (Qmul_den_pos (Qinv_den_pos (by decide)) f.hMd)
    (Uc_bd C f x t) h2

theorem Dc_congr_x (C : NormCtx) {x y : Real} (h : Req x y) (f : L2Test) (t : Real) : Req (Dc C x f t) (Dc C y f t) :=
  Rsub_congr (Uc_congr_x C h f t) (Rmul_congr (clampedInv_congr _ _ _ h) (Req_refl _))

theorem Dcl_lip (C : NormCtx) (f : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Dc C (xcl C x) f t) (Dc C (xcl C y) f t))) (Rmul (ofQ (DcL C f) (DcL_den C f)) (Rabs (Rsub x y))) :=
  fun x y => Rle_trans (Dc_lip_x C f t (xcl C x) (xcl C y))
    (Rmul_le_Rmul_left (Rnonneg_ofQ (DcL_den C f) (DcL_num C f)) (xcl_lip C x y))

def tailL2 (C : NormCtx) (f g : L2Test) : Q := add (mul (DcL C f) g.M) (mul f.M (DcL C g))
def tailM2 (C : NormCtx) (f g : L2Test) : Q := add (mul (DcM C f) g.M) (mul f.M (DcM C g))
theorem tailL2_den (C : NormCtx) (f g : L2Test) : 0 < (tailL2 C f g).den :=
  add_den_pos (Qmul_den_pos (DcL_den C f) g.hMd) (Qmul_den_pos f.hMd (DcL_den C g))
theorem tailL2_num (C : NormCtx) (f g : L2Test) : 0 ≤ (tailL2 C f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (DcL_num C f) g.hMn) (Qmul_num_nonneg f.hMn (DcL_num C g))
theorem tailM2_den (C : NormCtx) (f g : L2Test) : 0 < (tailM2 C f g).den :=
  add_den_pos (Qmul_den_pos (DcM_den C f) g.hMd) (Qmul_den_pos f.hMd (DcM_den C g))
theorem tailM2_num (C : NormCtx) (f g : L2Test) : 0 ≤ (tailM2 C f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (DcM_num C f) g.hMn) (Qmul_num_nonneg f.hMn (DcM_num C g))
theorem tailS_lip (C : NormCtx) (f g : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Radd (Rmul (Dc C (xcl C x) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C x) g t)))
                    (Radd (Rmul (Dc C (xcl C y) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C y) g t)))))
        (Rmul (ofQ (tailL2 C f g) (tailL2_den C f g)) (Rabs (Rsub x y))) :=
  lip_add_fl (Qmul_den_pos (DcL_den C f) g.hMd) (Qmul_den_pos f.hMd (DcL_den C g))
    (lip_mul_const_right (DcL_den C f) (Dcl_lip C f t) (Vc C g t) g.hMd g.hMn (Vc_bd C g t))
    (lip_const_mul_left (DcL_den C g) (DcL_num C g) (Dcl_lip C g t) (Vc C f t) f.hMd (Vc_bd C f t))
theorem tailS_bd (C : NormCtx) (f g : L2Test) (t : Real) : ∀ x,
    Rle (Rabs (Radd (Rmul (Dc C (xcl C x) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C x) g t)))) (ofQ (tailM2 C f g) (tailM2_den C f g)) :=
  fun x => abs_add_bd _ _ (abs_mul_bd _ _ g.hMn (Dc_bd C f (xcl C x) t) (Vc_bd C g t))
    (abs_mul_bd _ _ (DcM_num C g) (Vc_bd C f t) (Dc_bd C g (xcl C x) t))

def tailKS (C : NormCtx) (k : Nat) (f g : L2Test) : Q := add (mul (kerM k) (tailL2 C f g)) (mul (tailM2 C f g) (kerL k))
theorem tailKS_den (C : NormCtx) (k : Nat) (f g : L2Test) : 0 < (tailKS C k f g).den :=
  add_den_pos (Qmul_den_pos (kerM_den k) (tailL2_den C f g)) (Qmul_den_pos (tailM2_den C f g) (kerL_den k))
theorem tailKS_num (C : NormCtx) (k : Nat) (f g : L2Test) : 0 ≤ (tailKS C k f g).num :=
  Qadd_num_nonneg_loc (Qmul_num_nonneg (kerM_num k) (tailL2_num C f g)) (Qmul_num_nonneg (tailM2_num C f g) (kerL_num k))
theorem tailKS_lip (C : NormCtx) (k : Nat) (f g : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (Rmul (Kx C k x) (Radd (Rmul (Dc C (xcl C x) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C x) g t))))
                    (Rmul (Kx C k y) (Radd (Rmul (Dc C (xcl C y) f t) (Vc C g t)) (Rmul (Vc C f t) (Dc C (xcl C y) g t))))))
        (Rmul (ofQ (tailKS C k f g) (tailKS_den C k f g)) (Rabs (Rsub x y))) :=
  Rmul_lipschitz (kerL_den k) (tailL2_den C f g) (kerM_den k) (tailM2_den C f g)
    (kerL_num k) (tailL2_num C f g) (kerM_num k) (tailM2_num C f g)
    (Kx_lip C k) (tailS_lip C f g t) (Kx_bd C k) (tailS_bd C f g t)

/-- **The scale modulus of the tail integrand**, uniform in `t`. -/
def tailXL (C : NormCtx) (k : Nat) (f g : L2Test) : Q := mul (mul C.w (Qinv C.a)) (tailKS C k f g)
theorem tailXL_den (C : NormCtx) (k : Nat) (f g : L2Test) : 0 < (tailXL C k f g).den :=
  Qmul_den_pos (Qmul_den_pos C.hw (Qinv_den_pos C.han)) (tailKS_den C k f g)
theorem tailXL_num (C : NormCtx) (k : Nat) (f g : L2Test) : 0 ≤ (tailXL C k f g).num :=
  Qmul_num_nonneg (wa_num C) (tailKS_num C k f g)

theorem tailRB_lip_x (C : NormCtx) (k : Nat) (f g : L2Test) (t : Real) : ∀ x y,
    Rle (Rabs (Rsub (tailRB C k x f g t) (tailRB C k y f g t))) (Rmul (ofQ (tailXL C k f g) (tailXL_den C k f g)) (Rabs (Rsub x y))) := by
  intro x y
  unfold tailRB
  exact lip_neg_pi (tailXL_den C k f g)
    (lip_const_mul_left (tailKS_den C k f g) (tailKS_num C k f g) (tailKS_lip C k f g t) _ (Qmul_den_pos C.hw (Qinv_den_pos C.han)) (wr_bd C t)) x y

theorem tailRB_congr_x (C : NormCtx) (k : Nat) {x y : Real} (h : Req x y) (f g : L2Test) (t : Real) :
    Req (tailRB C k x f g t) (tailRB C k y f g t) :=
  Rneg_congr (Rmul_congr (Req_refl _) (Rmul_congr (Kx_congr C k h)
    (Radd_congr (Rmul_congr (Dc_congr_x C (xcl_congr C h) f t) (Req_refl _)) (Rmul_congr (Req_refl _) (Dc_congr_x C (xcl_congr C h) g t)))))

theorem tailInt_lip_x (C : NormCtx) (k : Nat) (f g : L2Test) (y : Real) : ∀ x x',
    Rle (Rabs (Rsub (tailInt C k x f g y) (tailInt C k x' f g y))) (Rmul (ofQ (tailXL C k f g) (tailXL_den C k f g)) (Rabs (Rsub x x'))) :=
  lip_of_congr_pd (F := fun x => tailInt C k x f g y) (G := fun x => tailRB C k x f g (affC C y)) _
    (fun x => tailInt_eq_RB C k x f g y) (tailRB_lip_x C k f g (affC C y))
theorem tailInt_congr_x (C : NormCtx) (k : Nat) {x x' : Real} (h : Req x x') (f g : L2Test) (y : Real) :
    Req (tailInt C k x f g y) (tailInt C k x' f g y) :=
  Req_trans (tailInt_eq_RB C k x f g y) (Req_trans (tailRB_congr_x C k h f g (affC C y)) (Req_symm (tailInt_eq_RB C k x' f g y)))

/-- **★ The inner tail integral is `tailXL`-Lipschitz in the scale** (`param_integral_lip`). -/
theorem tailInner_lip (C : NormCtx) (k : Nat) (f g : L2Test) : ∀ x x',
    Rle (Rabs (Rsub (tailInner C k x f g) (tailInner C k x' f g))) (Rmul (ofQ (tailXL C k f g) (tailXL_den C k f g)) (Rabs (Rsub x x'))) :=
  fun x x' => param_integral_lip (F := fun x y => tailInt C k x f g y) (L := fun x => tailExpL C k x f g)
    (fun x => tailExpL_den C k x f g) (fun x => tailExpL_num C k x f g) (fun x => tailInt_lip C k x f g) (fun x => tailInt_fc C k x f g)
    (tailXL_den C k f g) (fun y _ _ x x' => tailInt_lip_x C k f g y x x') x x'
theorem tailInner_fc (C : NormCtx) (k : Nat) (f g : L2Test) : ∀ x x', Req x x' → Req (tailInner C k x f g) (tailInner C k x' f g) :=
  fun x x' h => param_integral_congr (F := fun x y => tailInt C k x f g y) (L := fun x => tailExpL C k x f g)
    (fun x => tailExpL_den C k x f g) (fun x => tailExpL_num C k x f g) (fun x => tailInt_lip C k x f g) (fun x => tailInt_fc C k x f g)
    x x' (fun y => tailInt_congr_x C k h f g y)

/-- **★ THE COMPACT TAIL GRAM** `∫_{x∈[1+2^{-k},B]} tailInner_k(x) dx` (`k ≥ 1`). -/
def tailGram (C : NormCtx) (k : Nat) (hk : 1 ≤ k) (f g : L2Test) : Real :=
  riemannIntegralI (f := fun x => tailInner C k x f g) (tailXL_den C k f g) (tailXL_num C k f g) (tailInner_lip C k f g) (tailInner_fc C k f g)
    (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k) (tailGap_num_nonneg C k hk)

end UOR.Bridge.F1Square.Square
