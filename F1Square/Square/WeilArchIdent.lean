/-
F1 square — **THE IDENTIFICATION `ArchIntegral = ArchTailForm`** (`WeilArchIdent.lean`):

For every truncation level `k ≥ 1`,
    `T_k = ½·J_k + ½·(Reg − E_k) + ½·Far`,      `E_k = ∫_{[1, 1+2⁻ᵏ]} N⁺/(x+1)`,
where `J_k` is the near truncation of `WeilArchNear`, `Reg`/`Far` the constructed regular/far parts:
the strip `[1+2⁻ᵏ, 2]` is partial-fractioned pointwise (`archKernFull_partial`), the far window
`[2, ∞)` block-wise (`improperIntegral1_congr_terms`), `∫₂^∞ N⁺/(x−1) = ∫₁^∞ N(u+1)/u` is the far
translation (`shiftTest`), `∫₁^∞ N⁺/(x+1)` splits at `2` (`reg_split_two`), and every improper
integral is reconciled to one decay constant `K_big` (`decay_mono`, `improperIntegral1_sched`).
Then `k → ∞`: `J_k → Near` at rate `CN/2ᵏ` and `E_k → 0` at rate `M/2ᵏ`, so the lower-end limit of
`T_k` is `½·(Reg + Near + Far) = ArchTailForm` (`Rlim_eval_real_rate`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchReconcile
import F1Square.Square.WeilArchRegSplit

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The reconciled decay constant.
-- ===========================================================================

/-- `K_R`, `K_F`: the constructed parts' decay constants. -/
def archKR (C : NormCtx) (f g : L2Test) : Q := archK C.geom f g (archRegIntegrand C.geom f g).M
def archKF (C : NormCtx) (f g : L2Test) : Q := archK C.geom f g (archFarIntegrand C.geom f g).M

theorem archKR_den (C : NormCtx) (f g : L2Test) : 0 < (archKR C f g).den :=
  archK_den C.geom f g _ (archRegIntegrand C.geom f g).hMd
theorem archKR_num (C : NormCtx) (f g : L2Test) : 0 ≤ (archKR C f g).num :=
  archK_num C.geom f g _ (archRegIntegrand C.geom f g).hMn (archRegIntegrand C.geom f g).hMd
theorem archKF_den (C : NormCtx) (f g : L2Test) : 0 < (archKF C f g).den :=
  archK_den C.geom f g _ (archFarIntegrand C.geom f g).hMd
theorem archKF_num (C : NormCtx) (f g : L2Test) : 0 ≤ (archKF C f g).num :=
  archK_num C.geom f g _ (archFarIntegrand C.geom f g).hMn (archFarIntegrand C.geom f g).hMd

/-- **The reconciled constant** `K_big = archKC + (K_R + K_F)`. -/
def archKB (C : NormCtx) (f g : L2Test) : Q := add (archKC C f g) (add (archKR C f g) (archKF C f g))

theorem archKB_den (C : NormCtx) (f g : L2Test) : 0 < (archKB C f g).den :=
  add_den_pos (archKC_den C f g) (add_den_pos (archKR_den C f g) (archKF_den C f g))
theorem archKB_num (C : NormCtx) (f g : L2Test) : 0 ≤ (archKB C f g).num :=
  Qadd_num_nonneg_loc (archKC_num C f g) (Qadd_num_nonneg_loc (archKR_num C f g) (archKF_num C f g))

theorem archKC_le_KB (C : NormCtx) (f g : L2Test) : Qle (archKC C f g) (archKB C f g) :=
  Qle_self_add (Qadd_num_nonneg_loc (archKR_num C f g) (archKF_num C f g))
theorem archKR_le_KB (C : NormCtx) (f g : L2Test) : Qle (archKR C f g) (archKB C f g) :=
  Qle_trans (add_den_pos (archKR_den C f g) (archKF_den C f g)) (Qle_self_add (archKF_num C f g))
    (Qle_self_add_l (archKC_num C f g))
theorem archKF_le_KB (C : NormCtx) (f g : L2Test) : Qle (archKF C f g) (archKB C f g) :=
  Qle_trans (add_den_pos (archKR_den C f g) (archKF_den C f g)) (Qle_self_add_l (archKR_num C f g))
    (Qle_self_add_l (archKC_num C f g))

-- ===========================================================================
-- (2) Abstract real algebra for the assembly and the limit difference.
-- ===========================================================================

/-- `½(n + P) + ½(F + ((R − E) − P)) = ½(n + (R + F)) − ½E`. -/
theorem arch_assemble (n P F R E : Real) :
    Req (Radd (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd n P))
          (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd F (Rsub (Rsub R E) P))))
        (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd n (Radd R F)))
          (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) E)) := by
  -- pull ½ out
  refine Req_trans (Req_symm (Rmul_distrib _ _ _)) ?_
  refine Req_trans ?_ (Rmul_sub_distrib _ _ _)
  refine Rmul_congr (Req_refl _) ?_
  -- (n + P) + (F + ((R − E) − P)) = (n + (R + F)) − E
  -- F + (X − P) = (F + X) − P with X := R − E
  have h1 : Req (Radd F (Rsub (Rsub R E) P)) (Rsub (Radd F (Rsub R E)) P) :=
    Req_symm (Radd_assoc F (Rsub R E) (Rneg P))
  refine Req_trans (Radd_congr (Req_refl _) h1) ?_
  -- (n + P) + (Y + −P) = (n + Y) + (P + −P) = n + Y
  refine Req_trans (Radd_add_add_comm n P (Radd F (Rsub R E)) (Rneg P)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_neg P)) ?_
  refine Req_trans (Radd_zero _) ?_
  -- n + (F + (R + −E)) = (n + (R + F)) + −E
  refine Req_trans (Radd_congr (Req_refl n) (Req_symm (Radd_assoc F R (Rneg E)))) ?_
  refine Req_trans (Radd_congr (Req_refl n) (Radd_congr (Radd_comm F R) (Req_refl _))) ?_
  exact Req_symm (Radd_assoc n (Radd R F) (Rneg E))

/-- `(½(n + (R + F)) − ½E) − ½(R + (Nr + F)) = ½(n − Nr) − ½E`. -/
theorem arch_limit_diff (n Nr R F E : Real) :
    Req (Rsub (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd n (Radd R F)))
                    (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) E))
              (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd R (Radd Nr F))))
        (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Rsub n Nr))
              (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) E)) := by
  -- (A − hE) − B = (A − B) − hE
  have h1 : Req (Rsub (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd n (Radd R F)))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) E))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd R (Radd Nr F))))
      (Rsub (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd n (Radd R F)))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd R (Radd Nr F))))
      (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) E)) := by
    refine Req_trans (Radd_assoc _ _ _) ?_
    refine Req_trans (Radd_congr (Req_refl _) (Radd_comm _ _)) ?_
    exact Req_symm (Radd_assoc _ _ _)
  refine Req_trans h1 ?_
  refine Rsub_congr ?_ (Req_refl _)
  -- ½X − ½Y = ½(X − Y), and (n + (R+F)) − (R + (Nr + F)) = n − Nr
  refine Req_trans (Req_symm (Rmul_sub_distrib _ _ _)) ?_
  refine Rmul_congr (Req_refl _) ?_
  -- (n + (R + F)) − (R + (Nr + F)) = (n + (R+F)) − ((R + F) + Nr) = n − Nr
  have h2 : Req (Radd R (Radd Nr F)) (Radd Nr (Radd R F)) :=
    Req_trans (Req_symm (Radd_assoc R Nr F))
      (Req_trans (Radd_congr (Radd_comm R Nr) (Req_refl F)) (Radd_assoc Nr R F))
  refine Req_trans (Rsub_congr (Req_refl _) h2) ?_
  -- (n + Z) − (Nr + Z) = n − Nr
  exact add_shift_iso_gen n Nr (Radd R F)

-- ===========================================================================
-- (3) Half-scaling and sums of decaying tests.
-- ===========================================================================

/-- `½·ψ` as an `L2Test` (ψ's own Lipschitz certificate, bound `M`). -/
def halfTest (ψ : L2Test) : L2Test where
  f := fun x => Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f x)
  L := ψ.L
  M := ψ.M
  hLd := ψ.hLd
  hLn := ψ.hLn
  hMd := ψ.hMd
  hMn := ψ.hMn
  hlip := half_lip ψ
  hfc := half_fc ψ
  hbd := fun x => by
    refine Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg (Nat.succ_pos 1) (by decide) _)) ?_
    refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (ψ.hbd x)) ?_
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_ofQ ψ.hMd ψ.hMn)
      (Rle_ofQ_ofQ (Nat.succ_pos 1) (by decide) (by decide : Qle (⟨1, 2⟩ : Q) (⟨1, 1⟩ : Q)))) ?_
    exact Rle_of_Req (Rone_mul _)

theorem halfTest_f (ψ : L2Test) (x : Real) :
    (halfTest ψ).f x = Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (ψ.f x) := rfl

/-- The unit term of `½·ψ` is half the unit term of ψ. -/
theorem integralTerm_half (ψ : L2Test) (m : Nat) :
    Req (integralTerm (halfTest ψ).hLd (halfTest ψ).hLn (halfTest ψ).hlip (halfTest ψ).hfc m)
        (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (integralTerm ψ.hLd ψ.hLn ψ.hlip ψ.hfc m)) :=
  integralTerm_smul (⟨1, 2⟩ : Q) (Nat.succ_pos 1) ψ.hLd ψ.hLn ψ.hlip ψ.hfc (half_lip ψ) (half_fc ψ) m

/-- The unit term of `A + B` is the sum of the unit terms (certificates weakened to the common modulus). -/
theorem integralTerm_addTest (A B : L2Test) (m : Nat) :
    Req (integralTerm (L2Test.add A B).hLd (L2Test.add A B).hLn (L2Test.add A B).hlip (L2Test.add A B).hfc m)
        (Radd (integralTerm A.hLd A.hLn A.hlip A.hfc m) (integralTerm B.hLd B.hLn B.hlip B.hfc m)) :=
  riemannIntegralI_addTest A B _ _ Nat.one_pos (by decide) (by decide)

/-- `K·w + K·w = (K+K)·w`. -/
theorem q_double_mul (K w : Q) : Qeq (add (mul K w) (mul K w)) (mul (add K K) w) := by
  simp only [Qeq, add, mul]
  push_cast
  generalize K.num = kn
  generalize ((K.den : Nat) : Int) = kd
  generalize w.num = wn
  generalize ((w.den : Nat) : Int) = wd
  ring_uor

/-- `½·((K+K)·w) = K·w`. -/
theorem q_half_double (K w : Q) : Qeq (mul (⟨1, 2⟩ : Q) (mul (add K K) w)) (mul K w) := by
  simp only [Qeq, add, mul]
  push_cast
  generalize K.num = kn
  generalize ((K.den : Nat) : Int) = kd
  generalize w.num = wn
  generalize ((w.den : Nat) : Int) = wd
  ring_uor

theorem decay_add (A B : L2Test) {K : Q} (hKd : 0 < K.den)
    (hA : DecayAt A K hKd) (hB : DecayAt B K hKd) :
    DecayAt (L2Test.add A B) (add K K) (add_den_pos hKd hKd) := by
  intro m hm
  have hA' := hA m hm
  have hB' := hB m hm
  have heq := integralTerm_addTest A B m
  have hsum : Req (Radd (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))
      (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
      (ofQ (mul (add K K) (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos (add_den_pos hKd hKd) (digamma_succ_mul_pos hm))) :=
    Req_trans (Radd_ofQ_ofQ _ _) (ofQ_congr _ _ (q_double_mul K _))
  constructor
  · refine Rle_trans (Rle_of_Req (Rneg_congr (Req_symm hsum))) ?_
    refine Rle_trans (Rle_of_Req (Rneg_Radd _ _)) ?_
    exact Rle_trans (Radd_le_add hA'.1 hB'.1) (Rle_of_Req (Req_symm heq))
  · refine Rle_trans (Rle_of_Req heq) ?_
    exact Rle_trans (Radd_le_add hA'.2 hB'.2) (Rle_of_Req hsum)

theorem decay_half (ψ : L2Test) {K : Q} (hKd : 0 < K.den)
    (hψ : DecayAt ψ (add K K) (add_den_pos hKd hKd)) : DecayAt (halfTest ψ) K hKd := by
  intro m hm
  have h := hψ m hm
  have heq := integralTerm_half ψ m
  have hhalf : Req (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
      (ofQ (mul (add K K) (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos (add_den_pos hKd hKd) (digamma_succ_mul_pos hm))))
      (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))) :=
    Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ _ (q_half_double K _))
  have hnn : Rnonneg (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) := Rnonneg_ofQ (Nat.succ_pos 1) (by decide)
  constructor
  · refine Rle_trans (Rle_of_Req (Rneg_congr (Req_symm hhalf))) ?_
    refine Rle_trans (Rle_of_Req (Req_symm (Rmul_neg_right _ _))) ?_
    exact Rle_trans (Rmul_le_Rmul_left hnn h.1) (Rle_of_Req (Req_symm heq))
  · refine Rle_trans (Rle_of_Req heq) ?_
    exact Rle_trans (Rmul_le_Rmul_left hnn h.2) (Rle_of_Req hhalf)

-- ===========================================================================
-- (4) The far and regular translates: block-wise congruences and decay at `K_big`.
-- ===========================================================================

/-- The near-kernel integrand from `N⁺` at floor `2⁻ᵏ`. -/
def nearIntC (C : NormCtx) (f g : L2Test) (k : Nat) : L2Test :=
  productTest (archNumC C f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))

theorem nearIntC_f (C : NormCtx) (f g : L2Test) (k : Nat) (x : Real) :
    (nearIntC C f g k).f x = Rmul ((archNumC C f g).f x) (clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (Rsub x one)) :=
  rfl

/-- The far translate `A_k = (nearIntC k)(u + 1)` agrees with `archFarIntegrand` at every `u ≥ 1`. -/
theorem farTranslate_eq (C : NormCtx) (f g : L2Test) (k : Nat) (u : Real) (hu : Rle one u) :
    Req ((shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)).f u) ((archFarIntegrand C.geom f g).f u) := by
  rw [shiftTest_f, nearIntC_f]
  unfold archFarIntegrand
  show Req (Rmul ((archNumC C f g).f (Radd u one)) (clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (Rsub (Radd u one) one)))
    (Rmul ((archNum C.geom f g).f (Radd u one)) (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) u))
  have hu1 : Rle one (Radd u one) := Rle_trans hu (Rle_self_Radd_right (Rnonneg_ofQ (by decide) (by decide)))
  obtain ⟨ku, hku⟩ := Pos_of_Rle_ofQ (by decide) (by decide) hu
  have hdk : Rle (ofQ (dyQ k) (dyQ_den k)) u := Rle_trans (Rle_ofQ_ofQ _ (by decide) (dyQ_le_one k)) hu
  refine Rmul_congr (archNumC_eq_archNum C f g _ hu1) ?_
  refine Req_trans (clampedInv_congr _ _ _ (Radd_sub_cancel_right u one)) ?_
  exact Req_trans (clampedInv_eq_of_ge (a := dyQ k) (han := dyQ_num k) (had := dyQ_den k) hku hdk)
    (Req_symm (clampedInv_eq_of_ge (a := (⟨1, 1⟩ : Q)) (han := by decide) (had := by decide) hku hu))

theorem farTranslate_terms (C : NormCtx) (f g : L2Test) (k m : Nat) :
    Req (integralTerm (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)).hLd
          (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)).hLn
          (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)).hlip
          (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)).hfc m)
        (integralTerm (archFarIntegrand C.geom f g).hLd (archFarIntegrand C.geom f g).hLn
          (archFarIntegrand C.geom f g).hlip (archFarIntegrand C.geom f g).hfc m) :=
  integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun u hu => farTranslate_eq C f g k u
    (Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
      show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hu))

/-- `shift 0 (regInt)` agrees with `archRegIntegrand` at every `x ≥ 1`. -/
theorem regZero_eq (C : NormCtx) (f g : L2Test) (x : Real) (hx : Rle one x) :
    Req ((shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).f x) ((archRegIntegrand C.geom f g).f x) := by
  rw [shiftTest_f, regInt_f]
  unfold archRegIntegrand
  show Req (Rmul ((archNumC C f g).f (Radd x (ofQ (⟨0, 1⟩ : Q) Nat.one_pos))) (archKernReg.f (Radd x (ofQ (⟨0, 1⟩ : Q) Nat.one_pos))))
    (Rmul ((archNum C.geom f g).f x) (archKernReg.f x))
  have h0 : Req (Radd x (ofQ (⟨0, 1⟩ : Q) Nat.one_pos)) x :=
    Req_trans (Radd_congr (Req_refl x) (Req_of_seq_Qeq (fun _ => Qeq_refl _))) (Radd_zero x)
  exact Rmul_congr (Req_trans ((archNumC C f g).hfc _ _ h0) (archNumC_eq_archNum C f g x hx))
    (archKernReg.hfc _ _ h0)

theorem regZero_terms (C : NormCtx) (f g : L2Test) (m : Nat) :
    Req (integralTerm (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLd
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLn
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hlip
          (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hfc m)
        (integralTerm (archRegIntegrand C.geom f g).hLd (archRegIntegrand C.geom f g).hLn
          (archRegIntegrand C.geom f g).hlip (archRegIntegrand C.geom f g).hfc m) :=
  integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun x hx => regZero_eq C f g x
    (Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
      show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hx))

/-- Decay of the far translate at `K_big` (from the far part's proved decay). -/
theorem decay_farTranslate (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) :
    DecayAt (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)) (archKB C f g) (archKB_den C f g) :=
  decay_of_terms_congr (archFarIntegrand C.geom f g) _ (archKB_den C f g)
    (fun m => Req_symm (farTranslate_terms C f g k m))
    (decay_mono _ (archKF_den C f g) (archKB_den C f g) (archKF_le_KB C f g) (archFarDecay C.geom f g hf hg))

/-- Decay of the far part's integrand at `K_big`. -/
theorem decay_farIntegrand (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (archFarIntegrand C.geom f g) (archKB C f g) (archKB_den C f g) :=
  decay_mono _ (archKF_den C f g) (archKB_den C f g) (archKF_le_KB C f g) (archFarDecay C.geom f g hf hg)

/-- Decay of `B = shift 1 (regInt)` at `K_big`. -/
theorem decay_B (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (regInt C f g)) (archKB C f g) (archKB_den C f g) :=
  decay_mono _ (archKC_den C f g) (archKB_den C f g) (archKC_le_KB C f g)
    (regDecay C f g hf hg (⟨1, 1⟩ : Q) Nat.one_pos (by decide))

/-- Decay of the regular part's integrand at `K_big` and at `archKC`. -/
theorem decay_regIntegrand_KB (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (archRegIntegrand C.geom f g) (archKB C f g) (archKB_den C f g) :=
  decay_mono _ (archKR_den C f g) (archKB_den C f g) (archKR_le_KB C f g) (archRegDecay C.geom f g hf hg)

theorem decay_regIntegrand_KC (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (archRegIntegrand C.geom f g) (archKC C f g) (archKC_den C f g) :=
  decay_of_terms_congr _ _ (archKC_den C f g) (regZero_terms C f g)
    (regDecay C f g hf hg (⟨0, 1⟩ : Q) Nat.one_pos (by decide))


-- ===========================================================================
-- (5) The master constant `K2 = K_big + K_big` and certificates at `K2`.
-- ===========================================================================

def archK2 (C : NormCtx) (f g : L2Test) : Q := add (archKB C f g) (archKB C f g)
theorem archK2_den (C : NormCtx) (f g : L2Test) : 0 < (archK2 C f g).den :=
  add_den_pos (archKB_den C f g) (archKB_den C f g)
theorem archK2_num (C : NormCtx) (f g : L2Test) : 0 ≤ (archK2 C f g).num :=
  Qadd_num_nonneg_loc (archKB_num C f g) (archKB_num C f g)
theorem archKB_le_K2 (C : NormCtx) (f g : L2Test) : Qle (archKB C f g) (archK2 C f g) :=
  Qle_self_add (archKB_num C f g)
theorem archKC_le_K2 (C : NormCtx) (f g : L2Test) : Qle (archKC C f g) (archK2 C f g) :=
  Qle_trans (archKB_den C f g) (archKC_le_KB C f g) (archKB_le_K2 C f g)

/-- A decay certificate transported along a Lipschitz-certificate weakening (`riemannIntegralI_certif_irrel`). -/
theorem decay_weaken_L (ψ : L2Test) {L' : Q} (hL'd : 0 < L'.den) (hL'n : 0 ≤ L'.num)
    (hlip' : ∀ x y, Rle (Rabs (Rsub (ψ.f x) (ψ.f y))) (Rmul (ofQ L' hL'd) (Rabs (Rsub x y))))
    {K : Q} (hKd : 0 < K.den) (hb : DecayAt ψ K hKd) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))))
          (integralTerm hL'd hL'n hlip' ψ.hfc m)
      ∧ Rle (integralTerm hL'd hL'n hlip' ψ.hfc m)
          (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm))) := fun m hm =>
  ⟨Rle_trans (hb m hm).1 (Rle_of_Req (riemannIntegralI_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _ _)),
   Rle_trans (Rle_of_Req (riemannIntegralI_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _ _)) (hb m hm).2⟩

-- ===========================================================================
-- (6) The strip `[1+2⁻ᵏ, 2]`: partial fractions pointwise, readback to `nearJ`.
-- ===========================================================================

/-- `2⁻ᵏ < 1` for `k ≥ 1`: the strip width `1 − 2⁻ᵏ` is positive. -/
theorem strip_width_pos (k : Nat) (hk : 1 ≤ k) : 0 < (Qsub (⟨1, 1⟩ : Q) (dyQ k)).num := by
  refine Qsub_num_pos_of_lt ?_
  show (1 : Int) * ((1 : Nat) : Int) < 1 * ((2 ^ k : Nat) : Int)
  have h : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h' := Int.ofNat_le.mpr h
  push_cast at h' ⊢; omega

theorem strip_width_le_one (k : Nat) : Qle (Qsub (⟨1, 1⟩ : Q) (dyQ k)) (⟨1, 1⟩ : Q) := by
  show ((1 : Int) * ((2 ^ k : Nat) : Int) + -1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
    ≤ 1 * ((1 * 2 ^ k : Nat) : Int)
  push_cast; omega

theorem strip_width_eq_nearW (k : Nat) : Qeq (Qsub (⟨1, 1⟩ : Q) (dyQ k)) (nearW k) := by
  simp only [Qeq, Qsub, add, neg, dyQ, nearW]
  push_cast
  generalize ((2 ^ k : Nat) : Int) = P
  ring_uor

/-- Pointwise on the strip: `F_k(x) = (½·(nearIntC + regInt))(x)` for `x − 1 ≥ 2⁻ᵏ`. -/
theorem fullInt_partial_pt (C : NormCtx) (f g : L2Test) (k : Nat) (x : Real) (hx1 : Rle one x)
    (hxc : Rle (ofQ (dyQ k) (dyQ_den k)) (Rsub x one)) :
    Req ((fullInt C f g k).f x) ((halfTest (L2Test.add (nearIntC C f g k) (regInt C f g))).f x) := by
  rw [fullInt_f, halfTest_f]
  show Req (Rmul ((archNumC C f g).f x) ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f x))
    (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (Radd ((nearIntC C f g k).f x) ((regInt C f g).f x)))
  rw [nearIntC_f, regInt_f]
  refine Req_trans (Rmul_congr (Req_refl _) (archKernFull_partial (dyQ k) (dyQ_num k) (dyQ_den k) x hx1 hxc)) ?_
  -- a·(½·(b + c)) = ½·(a·b + a·c)
  refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
  refine Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) ?_
  refine Req_trans (Rmul_assoc _ _ _) ?_
  exact Rmul_congr (Req_refl _) (Rmul_distrib _ _ _)

/-- **The strip** `∫_{[1+2⁻ᵏ, 2]} F_k = ½·(∫ nearIntC + ∫ regInt)` over the same window. -/
theorem strip_partial (C : NormCtx) (f g : L2Test) (k : Nat) :
    Req (riemannIntegralI (fullInt C f g k).hLd (fullInt C f g k).hLn (fullInt C f g k).hlip
          (fullInt C f g k).hfc (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
          (Radd (riemannIntegralI (nearIntC C f g k).hLd (nearIntC C f g k).hLn (nearIntC C f g k).hlip
              (nearIntC C f g k).hfc (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k))
            (riemannIntegralI (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip
              (regInt C f g).hfc (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k)))) := by
  refine Req_trans (riemannIntegralI_congr_unit_mod (fullInt C f g k).hLd (fullInt C f g k).hLn
    (fullInt C f g k).hlip (fullInt C f g k).hfc
    (halfTest (L2Test.add (nearIntC C f g k) (regInt C f g))).hLd
    (halfTest (L2Test.add (nearIntC C f g k) (regInt C f g))).hLn
    (halfTest (L2Test.add (nearIntC C f g k) (regInt C f g))).hlip
    (halfTest (L2Test.add (nearIntC C f g k) (regInt C f g))).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) (fun t ht0 _ => ?_)) ?_
  · have hx := affine_ge_lo (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) t ht0
    have hx1 : Rle one _ := Rle_trans (Rle_ofQ_ofQ (by decide) (nearLo_den k)
      (Qle_self_add (Int.le_of_lt (dyQ_num k)))) hx
    exact fullInt_partial_pt C f g k _ hx1 (sub_one_ge_of_ge_add (dyQ_den k) hx)
  · refine Req_trans (riemannIntegralI_smul (⟨1, 2⟩ : Q) (Nat.succ_pos 1)
      (L2Test.add (nearIntC C f g k) (regInt C f g)).hLd (L2Test.add (nearIntC C f g k) (regInt C f g)).hLn
      (L2Test.add (nearIntC C f g k) (regInt C f g)).hlip (L2Test.add (nearIntC C f g k) (regInt C f g)).hfc
      (half_lip _) (half_fc _) (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k)) ?_
    exact Rmul_congr (Req_refl _) (riemannIntegralI_addTest _ _ _ _ _ _ _)

/-- **Readback to the near truncation**: `∫_{[1+2⁻ᵏ, 2]} nearIntC = nearJ k`. -/
theorem near_readback (C : NormCtx) (f g : L2Test) (k : Nat) :
    Req (riemannIntegralI (nearIntC C f g k).hLd (nearIntC C f g k).hLn (nearIntC C f g k).hlip
          (nearIntC C f g k).hfc (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k))
        (nearJ C.geom f g k) := by
  unfold nearJ nearIntegrand
  refine riemannIntegralI_congr_unit_mod (nearIntC C f g k).hLd (nearIntC C f g k).hLn (nearIntC C f g k).hlip
    (nearIntC C f g k).hfc
    (productTest (archNum C.geom f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))).hLd
    (productTest (archNum C.geom f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))).hLn
    (productTest (archNum C.geom f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))).hlip
    (productTest (archNum C.geom f g) (archKernNear (dyQ k) (dyQ_num k) (dyQ_den k))).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) (fun t ht0 _ => ?_)
  have hx := affine_ge_lo (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k) t ht0
  have hx1 : Rle one _ := Rle_trans (Rle_ofQ_ofQ (by decide) (nearLo_den k)
    (Qle_self_add (Int.le_of_lt (dyQ_num k)))) hx
  show Req (Rmul ((archNumC C f g).f _) _) (Rmul ((archNum C.geom f g).f _) _)
  exact Rmul_congr (archNumC_eq_archNum C f g _ hx1) (Req_refl _)


-- ===========================================================================
-- (7) P1–P2: the split of `T_k` at `2` and the strip readback.
-- ===========================================================================

/-- **P1**: `T_k = ∫_{[1, 1+(1−2⁻ᵏ)]} g_{k,2⁻ᵏ} + ∫_{2}^{∞} F_k` (shift `1`, both at `archKC`). -/
theorem trunc_split_two (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) (hk : 1 ≤ k) :
    Req (archTrunc C f g hf hg k)
        (Radd (riemannIntegralI (truncInt C f g k (dyQ k) (dyQ_den k)).hLd (truncInt C f g k (dyQ k) (dyQ_den k)).hLn
            (truncInt C f g k (dyQ k) (dyQ_den k)).hlip (truncInt C f g k (dyQ k) (dyQ_den k)).hfc
            (⟨1, 1⟩ : Q) (Qsub (⟨1, 1⟩ : Q) (dyQ k)) Nat.one_pos (Qsub_den_pos Nat.one_pos (dyQ_den k))
            (Int.le_of_lt (strip_width_pos k hk)))
          (improperIntegral1 (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hLd
            (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hLn (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hlip
            (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hfc (archKC_den C f g) (archKC_num C f g)
            (truncDecay C f g hf hg k (⟨1, 1⟩ : Q) Nat.one_pos (by decide)))) := by
  have hΔd : 0 < (Qsub (⟨1, 1⟩ : Q) (dyQ k)).den := Qsub_den_pos Nat.one_pos (dyQ_den k)
  have hΔn := strip_width_pos k hk
  have hsumn : 0 ≤ (add (dyQ k) (Qsub (⟨1, 1⟩ : Q) (dyQ k))).num :=
    Qadd_num_nonneg_loc (Int.le_of_lt (dyQ_num k)) (Int.le_of_lt hΔn)
  refine Req_trans (improper_split_shift (fullInt C f g k) (dyQ k) (Qsub (⟨1, 1⟩ : Q) (dyQ k))
    (dyQ_den k) hΔd hΔn (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg k (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k)))
    (truncDecay C f g hf hg k (add (dyQ k) (Qsub (⟨1, 1⟩ : Q) (dyQ k))) (add_den_pos (dyQ_den k) hΔd) hsumn)
    (archCF C f g)
    (truncFar C f g hf hg k (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k)) _ hΔd hΔn (strip_width_le_one k))) ?_
  refine Radd_congr (Req_refl _) ?_
  exact improperIntegral1_congr _ _ _ _ _ _ (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg k (add (dyQ k) (Qsub (⟨1, 1⟩ : Q) (dyQ k))) (add_den_pos (dyQ_den k) hΔd) hsumn)
    (truncDecay C f g hf hg k (⟨1, 1⟩ : Q) Nat.one_pos (by decide))
    (fun u => shiftTest_congr_shift _ _ _ _ (Qadd_Qsub_cancel (dyQ k) (⟨1, 1⟩ : Q)) (fullInt C f g k) u)

/-- **P2**: the strip integral is `∫_{[1+2⁻ᵏ, 2]} F_k` over the `nearJ` window. -/
theorem strip_readback (C : NormCtx) (f g : L2Test) (k : Nat) (hk : 1 ≤ k) :
    Req (riemannIntegralI (truncInt C f g k (dyQ k) (dyQ_den k)).hLd (truncInt C f g k (dyQ k) (dyQ_den k)).hLn
          (truncInt C f g k (dyQ k) (dyQ_den k)).hlip (truncInt C f g k (dyQ k) (dyQ_den k)).hfc
          (⟨1, 1⟩ : Q) (Qsub (⟨1, 1⟩ : Q) (dyQ k)) Nat.one_pos (Qsub_den_pos Nat.one_pos (dyQ_den k))
          (Int.le_of_lt (strip_width_pos k hk)))
        (riemannIntegralI (fullInt C f g k).hLd (fullInt C f g k).hLn (fullInt C f g k).hlip
          (fullInt C f g k).hfc (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k)) := by
  refine Req_trans (shift_window (dyQ k) (dyQ_den k) (fullInt C f g k) (⟨1, 1⟩ : Q)
    (Qsub (⟨1, 1⟩ : Q) (dyQ k)) Nat.one_pos (Qsub_den_pos Nat.one_pos (dyQ_den k))
    (Int.le_of_lt (strip_width_pos k hk))) ?_
  exact riemannIntegralI_congr_Q (fullInt C f g k).hLd (fullInt C f g k).hLn (fullInt C f g k).hlip
    (fullInt C f g k).hfc (add (⟨1, 1⟩ : Q) (dyQ k)) (Qsub (⟨1, 1⟩ : Q) (dyQ k)) (nearLo k) (nearW k)
    (add_den_pos Nat.one_pos (dyQ_den k)) (Qsub_den_pos Nat.one_pos (dyQ_den k))
    (Int.le_of_lt (strip_width_pos k hk)) (nearLo_den k) (nearW_den k) (nearW_num k)
    (Qeq_refl _) (strip_width_eq_nearW k)

-- ===========================================================================
-- (8) P3: the far window `∫_2^∞ F_k = ½·(Far + ∫_2^∞ N⁺/(x+1))`.
-- ===========================================================================

/-- The far translates `A_k = (nearIntC k)(u+1)`, `B = (regInt)(u+1)` — named, then SEALED (tower economy). -/
def farA (C : NormCtx) (f g : L2Test) (k : Nat) : L2Test :=
  shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (nearIntC C f g k)
def farB (C : NormCtx) (f g : L2Test) : L2Test :=
  shiftTest (⟨1, 1⟩ : Q) Nat.one_pos (regInt C f g)

/-- Block-wise partial fractions on `[2, ∞)`: `(shift 1 F_k)(u) = (½·(A_k + B))(u)` for `u ≥ 1`. -/
theorem far_partial_pt (C : NormCtx) (f g : L2Test) (k : Nat) (u : Real) (hu : Rle one u) :
    Req ((truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).f u)
        ((halfTest (L2Test.add (farA C f g k) (farB C f g))).f u) := by
  have hx1 : Rle one (Radd u (ofQ (⟨1, 1⟩ : Q) Nat.one_pos)) :=
    Rle_trans hu (Rle_self_Radd_right (Rnonneg_ofQ Nat.one_pos (by decide)))
  have hxc : Rle (ofQ (dyQ k) (dyQ_den k)) (Rsub (Radd u (ofQ (⟨1, 1⟩ : Q) Nat.one_pos)) one) :=
    Rle_trans (Rle_trans (Rle_ofQ_ofQ _ (by decide) (dyQ_le_one k)) hu)
      (Rle_of_Req (Req_symm (Radd_sub_cancel_right u one)))
  exact fullInt_partial_pt C f g k (Radd u (ofQ (⟨1, 1⟩ : Q) Nat.one_pos)) hx1 hxc

theorem decay_farA_KB (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    DecayAt (farA C f g k) (archKB C f g) (archKB_den C f g) := decay_farTranslate C f g hf hg k
theorem decay_farB_KB (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (farB C f g) (archKB C f g) (archKB_den C f g) := decay_B C f g hf hg
theorem farA_terms (C : NormCtx) (f g : L2Test) (k m : Nat) :
    Req (integralTerm (farA C f g k).hLd (farA C f g k).hLn (farA C f g k).hlip (farA C f g k).hfc m)
        (integralTerm (archFarIntegrand C.geom f g).hLd (archFarIntegrand C.geom f g).hLn
          (archFarIntegrand C.geom f g).hlip (archFarIntegrand C.geom f g).hfc m) :=
  farTranslate_terms C f g k m

theorem farB_f (C : NormCtx) (f g : L2Test) (u : Real) :
    (farB C f g).f u = (regInt C f g).f (Radd u (ofQ (⟨1, 1⟩ : Q) Nat.one_pos)) := rfl
theorem decay_farB_KC (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (farB C f g) (archKC C f g) (archKC_den C f g) :=
  regDecay C f g hf hg (⟨1, 1⟩ : Q) Nat.one_pos (by decide)

attribute [irreducible] farA farB nearIntC

theorem decay_farA_K2 (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    DecayAt (farA C f g k) (archK2 C f g) (archK2_den C f g) :=
  decay_mono _ (archKB_den C f g) (archK2_den C f g) (archKB_le_K2 C f g) (decay_farA_KB C f g hf hg k)
theorem decay_farB_K2 (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) :
    DecayAt (farB C f g) (archK2 C f g) (archK2_den C f g) :=
  decay_mono _ (archKB_den C f g) (archK2_den C f g) (archKB_le_K2 C f g) (decay_farB_KB C f g hf hg)
theorem decay_farAB_K2 (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    DecayAt (L2Test.add (farA C f g k) (farB C f g)) (archK2 C f g) (archK2_den C f g) :=
  decay_add _ _ (archKB_den C f g) (decay_farA_KB C f g hf hg k) (decay_farB_KB C f g hf hg)
theorem decay_farH_K2 (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    DecayAt (halfTest (L2Test.add (farA C f g k) (farB C f g))) (archK2 C f g) (archK2_den C f g) :=
  decay_mono _ (archKB_den C f g) (archK2_den C f g) (archKB_le_K2 C f g)
    (decay_half _ (archKB_den C f g) (decay_farAB_K2 C f g hf hg k))

/-- `∫_2^∞ ½(A_k + B) = ½·(∫ A_k + ∫ B)` at `K2` (smul + add, certificates reconciled). -/
theorem far_half_sum (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    Req (improperIntegral1 (halfTest (L2Test.add (farA C f g k) (farB C f g))).hLd
          (halfTest (L2Test.add (farA C f g k) (farB C f g))).hLn
          (halfTest (L2Test.add (farA C f g k) (farB C f g))).hlip
          (halfTest (L2Test.add (farA C f g k) (farB C f g))).hfc
          (archK2_den C f g) (archK2_num C f g) (decay_farH_K2 C f g hf hg k))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
          (Radd (improperIntegral1 (farA C f g k).hLd (farA C f g k).hLn (farA C f g k).hlip (farA C f g k).hfc
              (archK2_den C f g) (archK2_num C f g) (decay_farA_K2 C f g hf hg k))
            (improperIntegral1 (farB C f g).hLd (farB C f g).hLn (farB C f g).hlip (farB C f g).hfc
              (archK2_den C f g) (archK2_num C f g) (decay_farB_K2 C f g hf hg)))) := by
  refine Req_trans (improperIntegral1_smul (⟨1, 2⟩ : Q) (Nat.succ_pos 1)
    (L2Test.add (farA C f g k) (farB C f g)).hLd (L2Test.add (farA C f g k) (farB C f g)).hLn
    (L2Test.add (farA C f g k) (farB C f g)).hlip (L2Test.add (farA C f g k) (farB C f g)).hfc
    (half_lip _) (half_fc _) (archK2_den C f g) (archK2_num C f g)
    (decay_farAB_K2 C f g hf hg k) (decay_farH_K2 C f g hf hg k)) ?_
  refine Rmul_congr (Req_refl _) ?_
  refine Req_trans (improperIntegral1_add (L2Test.add (farA C f g k) (farB C f g)).hLd
    (L2Test.add (farA C f g k) (farB C f g)).hLn
    (lip_weaken (farA C f g k).hLd (L2Test.add (farA C f g k) (farB C f g)).hLd
      (Qle_self_add (farB C f g).hLn) (farA C f g k).hlip)
    (farA C f g k).hfc
    (lip_weaken (farB C f g).hLd (L2Test.add (farA C f g k) (farB C f g)).hLd
      (Qle_self_add_l (farA C f g k).hLn) (farB C f g).hlip)
    (farB C f g).hfc
    (L2Test.add (farA C f g k) (farB C f g)).hlip (L2Test.add (farA C f g k) (farB C f g)).hfc
    (archK2_den C f g) (archK2_num C f g)
    (decay_weaken_L (farA C f g k) _ _ _ (archK2_den C f g) (decay_farA_K2 C f g hf hg k))
    (decay_weaken_L (farB C f g) _ _ _ (archK2_den C f g) (decay_farB_K2 C f g hf hg))
    (decay_farAB_K2 C f g hf hg k)) ?_
  exact Radd_congr (improperIntegral1_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _)
    (improperIntegral1_certif_irrel _ _ _ _ _ _ _ _ _ _ _ _)

/-- `∫_1^∞ A_k = ArchFarPart` (far translation, block-wise, reconciled). -/
theorem farA_eq_Far (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    Req (improperIntegral1 (farA C f g k).hLd (farA C f g k).hLn (farA C f g k).hlip (farA C f g k).hfc
          (archK2_den C f g) (archK2_num C f g) (decay_farA_K2 C f g hf hg k))
        (ArchFarPart C.geom f g hf hg) := by
  unfold ArchFarPart
  refine Req_trans (improperIntegral1_congr_terms _ _ _ _ _ _ _ _ (archK2_den C f g) (archK2_num C f g)
    (decay_farA_K2 C f g hf hg k)
    (decay_mono _ (archKB_den C f g) (archK2_den C f g) (archKB_le_K2 C f g) (decay_farIntegrand C f g hf hg))
    (farA_terms C f g k)) ?_
  exact improperIntegral1_sched _ _ _ _ (archK2_den C f g) (archK2_num C f g) _ _ _ (archFarDecay C.geom f g hf hg)

/-- **P3**: `∫_2^∞ F_k = ½·(Far + ∫_1^∞ B)`. -/
theorem far_window (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    Req (improperIntegral1 (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hLd
          (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hLn (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hlip
          (truncInt C f g k (⟨1, 1⟩ : Q) Nat.one_pos).hfc (archKC_den C f g) (archKC_num C f g)
          (truncDecay C f g hf hg k (⟨1, 1⟩ : Q) Nat.one_pos (by decide)))
        (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
          (Radd (ArchFarPart C.geom f g hf hg)
            (improperIntegral1 (farB C f g).hLd (farB C f g).hLn (farB C f g).hlip (farB C f g).hfc
              (archK2_den C f g) (archK2_num C f g) (decay_farB_K2 C f g hf hg)))) := by
  refine Req_trans (improperIntegral1_sched _ _ _ _ (archKC_den C f g) (archKC_num C f g)
    (archK2_den C f g) (archK2_num C f g) _
    (decay_mono _ (archKC_den C f g) (archK2_den C f g) (archKC_le_K2 C f g)
      (truncDecay C f g hf hg k (⟨1, 1⟩ : Q) Nat.one_pos (by decide)))) ?_
  refine Req_trans (improperIntegral1_congr_terms _ _ _ _ _ _ _ _ (archK2_den C f g) (archK2_num C f g) _
    (decay_farH_K2 C f g hf hg k)
    (fun m => integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun u hu => far_partial_pt C f g k u
      (Rle_trans (Rle_ofQ_ofQ (by decide) Nat.one_pos (by
        show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hu)))) ?_
  refine Req_trans (far_half_sum C f g hf hg k) ?_
  exact Rmul_congr (Req_refl _) (Radd_congr (farA_eq_Far C f g hf hg k) (Req_refl _))

-- ===========================================================================
-- (9) P4: the regular chain `Reg = E_k + (P_k + IB)`.
-- ===========================================================================

/-- `E_k = ∫_{[1, 1+2⁻ᵏ]} N⁺/(x+1)`. -/
def archE (C : NormCtx) (f g : L2Test) (k : Nat) : Real :=
  riemannIntegralI (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip (regInt C f g).hfc
    (⟨1, 1⟩ : Q) (dyQ k) Nat.one_pos (dyQ_den k) (Int.le_of_lt (dyQ_num k))

/-- `P_k = ∫_{[1+2⁻ᵏ, 2]} N⁺/(x+1)`. -/
def archP (C : NormCtx) (f g : L2Test) (k : Nat) : Real :=
  riemannIntegralI (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip (regInt C f g).hfc
    (nearLo k) (nearW k) (nearLo_den k) (nearW_den k) (nearW_num k)

/-- `IB = ∫_1^∞ B = ∫_2^∞ N⁺/(x+1)` at `K2`. -/
def archIB (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) : Real :=
  improperIntegral1 (farB C f g).hLd (farB C f g).hLn (farB C f g).hlip (farB C f g).hfc
    (archK2_den C f g) (archK2_num C f g) (decay_farB_K2 C f g hf hg)

/-- `∫_{[1,2]} N⁺/(x+1) = E_k + P_k`. -/
theorem reg_window_split (C : NormCtx) (f g : L2Test) (k : Nat) :
    Req (riemannIntegralI (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip (regInt C f g).hfc
          (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos (by decide))
        (Radd (archE C f g k) (archP C f g k)) := by
  refine Req_trans (riemannIntegralI_split_at (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip
    (regInt C f g).hfc (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q) (dyQ k) Nat.one_pos Nat.one_pos (by decide)
    (dyQ_den k) (dyQ_num k) (dyQ_le_one k) (Qsub_num_nonneg (dyQ_le_one k))) ?_
  refine Radd_congr (Req_refl _) ?_
  exact riemannIntegralI_congr_Q (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip (regInt C f g).hfc
    (add (⟨1, 1⟩ : Q) (dyQ k)) (Qsub (⟨1, 1⟩ : Q) (dyQ k)) (nearLo k) (nearW k)
    (add_den_pos Nat.one_pos (dyQ_den k)) (Qsub_den_pos Nat.one_pos (dyQ_den k))
    (Qsub_num_nonneg (dyQ_le_one k)) (nearLo_den k) (nearW_den k) (nearW_num k)
    (Qeq_refl _) (strip_width_eq_nearW k)

/-- `(shift 0 R)(x) = R(x)`. -/
theorem regZero_pt (C : NormCtx) (f g : L2Test) (x : Real) :
    Req ((shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).f x) ((regInt C f g).f x) := by
  rw [shiftTest_f]
  exact (regInt C f g).hfc _ _
    (Req_trans (Radd_congr (Req_refl x) (Req_of_seq_Qeq (fun _ => Qeq_refl _))) (Radd_zero x))

set_option maxHeartbeats 2000000 in
/-- **P4**: `Reg = E_k + (P_k + IB)`. -/
theorem reg_chain (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) :
    Req (ArchRegPart C.geom f g hf hg) (Radd (archE C f g k) (Radd (archP C f g k) (archIB C f g hf hg))) := by
  unfold ArchRegPart
  -- schedule K_R → archKC, then block-wise to shift 0 R
  refine Req_trans (improperIntegral1_sched (archRegIntegrand C.geom f g).hLd (archRegIntegrand C.geom f g).hLn
    (archRegIntegrand C.geom f g).hlip (archRegIntegrand C.geom f g).hfc
    (archK_den C.geom f g _ (archRegIntegrand C.geom f g).hMd)
    (archK_num C.geom f g _ (archRegIntegrand C.geom f g).hMn (archRegIntegrand C.geom f g).hMd)
    (archKC_den C f g) (archKC_num C f g)
    (archRegDecay C.geom f g hf hg) (decay_regIntegrand_KC C f g hf hg)) ?_
  refine Req_trans (improperIntegral1_congr_terms (archRegIntegrand C.geom f g).hLd (archRegIntegrand C.geom f g).hLn
    (archRegIntegrand C.geom f g).hlip (archRegIntegrand C.geom f g).hfc
    (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLd (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hLn
    (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hlip (shiftTest (⟨0, 1⟩ : Q) Nat.one_pos (regInt C f g)).hfc
    (archKC_den C f g) (archKC_num C f g)
    (decay_regIntegrand_KC C f g hf hg) (regDecay C f g hf hg (⟨0, 1⟩ : Q) Nat.one_pos (by decide))
    (fun m => Req_symm (regZero_terms C f g m))) ?_
  refine Req_trans (reg_split_two C f g hf hg) ?_
  refine Req_trans (Radd_congr ?_ ?_) (Radd_assoc _ _ _)
  · -- ∫_{[1,2]} (shift 0 R) = ∫_{[1,2]} R = E + P
    refine Req_trans (riemannIntegralI_congr_unit_mod _ _ _ _ (regInt C f g).hLd (regInt C f g).hLn
      (regInt C f g).hlip (regInt C f g).hfc (⟨1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos (by decide)
      (fun t _ _ => regZero_pt C f g _)) ?_
    exact reg_window_split C f g k
  · -- ∫_1^∞ (shift (0+1) R) = ∫_1^∞ B (block-wise), then schedule to K2
    refine Req_trans (improperIntegral1_congr_terms
      (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hLd
      (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hLn
      (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hlip
      (shiftTest (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (regInt C f g)).hfc
      (farB C f g).hLd (farB C f g).hLn (farB C f g).hlip (farB C f g).hfc
      (archKC_den C f g) (archKC_num C f g)
      (regDecay C f g hf hg (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (add_den_pos Nat.one_pos Nat.one_pos) (by decide))
      (decay_farB_KC C f g hf hg)
      (fun m => integralTerm_congr_ge _ _ _ _ _ _ _ _ m (fun u _ => by
        rw [farB_f]
        exact shiftTest_congr_shift _ _ _ _
          (by decide : Qeq (add (⟨0, 1⟩ : Q) (⟨1, 1⟩ : Q)) (⟨1, 1⟩ : Q)) (regInt C f g) u))) ?_
    exact improperIntegral1_sched (farB C f g).hLd (farB C f g).hLn (farB C f g).hlip (farB C f g).hfc
      (archKC_den C f g) (archKC_num C f g) (archK2_den C f g) (archK2_num C f g)
      (decay_farB_KC C f g hf hg) (decay_farB_K2 C f g hf hg)

-- ===========================================================================
-- (10) P5: THE PER-`k` IDENTITY `T_k = ½(J_k + (Reg + Far)) − ½E_k`.
-- ===========================================================================

/-- **THE PER-`k` IDENTITY** (`k ≥ 1`). -/
theorem archTrunc_ident (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) (hk : 1 ≤ k) :
    Req (archTrunc C f g hf hg k)
        (Rsub (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1))
                (Radd (nearJ C.geom f g k) (Radd (ArchRegPart C.geom f g hf hg) (ArchFarPart C.geom f g hf hg))))
              (Rmul (ofQ (⟨1, 2⟩ : Q) (Nat.succ_pos 1)) (archE C f g k))) := by
  -- IB = (Reg − E) − P
  have hreg := reg_chain C f g hf hg k
  have h1 : Req (Rsub (ArchRegPart C.geom f g hf hg) (archE C f g k)) (Radd (archP C f g k) (archIB C f g hf hg)) :=
    Req_trans (Rsub_congr hreg (Req_refl _)) (Rsub_add_cancel_left _ _)
  have h2 : Req (Rsub (Rsub (ArchRegPart C.geom f g hf hg) (archE C f g k)) (archP C f g k)) (archIB C f g hf hg) :=
    Req_trans (Rsub_congr h1 (Req_refl _)) (Rsub_add_cancel_left _ _)
  -- T_k = strip + far window
  refine Req_trans (trunc_split_two C f g hf hg k hk) ?_
  refine Req_trans (Radd_congr (Req_trans (strip_readback C f g k hk) (Req_trans (strip_partial C f g k)
    (Rmul_congr (Req_refl _) (Radd_congr (near_readback C f g k) (Req_refl _)))))
    (far_window C f g hf hg k)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Rmul_congr (Req_refl _) (Radd_congr (Req_refl _) (Req_symm h2)))) ?_
  exact arch_assemble _ _ _ _ _


-- ===========================================================================
-- (11) P6: THE LOWER-END LIMIT `ArchIntegral = ArchTailForm`.
-- ===========================================================================

/-- `|E_k| ≤ 2⁻ᵏ·M_R`. -/
theorem archE_bound (C : NormCtx) (f g : L2Test) (k : Nat) :
    Rle (Rabs (archE C f g k))
        (ofQ (mul (dyQ k) (regInt C f g).M) (Qmul_den_pos (dyQ_den k) (regInt C f g).hMd)) :=
  riemannIntegralI_abs_le_window (regInt C f g).hLd (regInt C f g).hLn (regInt C f g).hlip (regInt C f g).hfc
    (⟨1, 1⟩ : Q) (dyQ k) (regInt C f g).M Nat.one_pos (dyQ_den k) (Int.le_of_lt (dyQ_num k))
    (regInt C f g).hMd (fun t _ _ => (regInt C f g).hbd _)

/-- **The near truncations converge at rate `CN/2ᵏ`**: `|J_k − Near| ≤ CN/2ᵏ`. -/
theorem nearJ_limit_rate (G : ClosedGeom) (f g : L2Test) (k : Nat) :
    Rle (Rabs (Rsub (nearJ G f g k) (ArchNearPart G f g)))
        (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
  unfold ArchNearPart
  have hcn : 0 ≤ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q).num := by
    show (0 : Int) ≤ (nearCN G f g : Int); omega
  have hev : ∀ n, k ≤ n →
      Rle (Rabs (Rsub (nearJ G f g (n + nearCN G f g)) (nearJ G f g k)))
        (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
    intro n hn
    have he : n + nearCN G f g = k + (n + nearCN G f g - k) := by omega
    have hd := nearJ_diff_le G f g k (n + nearCN G f g - k)
    rw [← he] at hd
    exact hd
  -- side A: Near − J_k ≤ c
  have hA : Rle (Rsub (Rlim (fun j => nearJ G f g (j + nearCN G f g)) (nearX_RReg G f g)) (nearJ G f g k))
      (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
    have hZ := RReg_add_const (Rneg (nearJ G f g k)) _ (nearX_RReg G f g)
    have hlim := Rlim_add_const (Rneg (nearJ G f g k)) _ (nearX_RReg G f g) hZ
    have hle : Rle (Rlim (fun j => Radd (Rneg (nearJ G f g k)) (nearJ G f g (j + nearCN G f g))) hZ)
        (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
      refine Rle_Rlim_ofQ_eventual_core hZ _ _ (fun t => ⟨k, fun n hn => ?_⟩)
      refine Rle_trans (Rle_of_Req (Radd_comm _ _)) ?_
      refine Rle_trans (Rle_Rabs_self _) ?_
      exact Rle_trans (hev n hn) (Rle_self_Radd_right (Rnonneg_ofQ _ (by show (0 : Int) ≤ 1; decide)))
    refine Rle_trans (Rle_of_Req (Radd_comm _ _)) (Rle_trans (Rle_of_Req (Req_symm hlim)) hle)
  -- side B: J_k − Near ≤ c
  have hB : Rle (Rsub (nearJ G f g k) (Rlim (fun j => nearJ G f g (j + nearCN G f g)) (nearX_RReg G f g)))
      (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
    have hN := RReg_neg _ (nearX_RReg G f g)
    have hZ := RReg_add_const (nearJ G f g k) _ hN
    have hlim : Req (Rlim (fun j => Radd (nearJ G f g k) (Rneg (nearJ G f g (j + nearCN G f g)))) hZ)
        (Radd (nearJ G f g k) (Rneg (Rlim (fun j => nearJ G f g (j + nearCN G f g)) (nearX_RReg G f g)))) :=
      Req_trans (Rlim_add_const (nearJ G f g k) _ hN hZ)
        (Radd_congr (Req_refl _) (Rlim_neg _ (nearX_RReg G f g) hN))
    have hle : Rle (Rlim (fun j => Radd (nearJ G f g k) (Rneg (nearJ G f g (j + nearCN G f g)))) hZ)
        (ofQ (⟨(nearCN G f g : Int), 2 ^ k⟩ : Q) (Nat.two_pow_pos k)) := by
      refine Rle_Rlim_ofQ_eventual_core hZ _ _ (fun t => ⟨k, fun n hn => ?_⟩)
      refine Rle_trans (Rle_Rabs_self _) ?_
      refine Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) ?_
      exact Rle_trans (hev n hn) (Rle_self_Radd_right (Rnonneg_ofQ _ (by show (0 : Int) ≤ 1; decide)))
    exact Rle_trans (Rle_of_Req (Req_symm hlim)) hle
  refine Rabs_le_of_both hB ?_
  exact Rle_trans (Rle_of_Req (Rneg_Rsub _ _)) hA

/-- `½·q ≤ q` for `q ≥ 0`. -/
theorem half_le_self (q : Q) (hq : 0 ≤ q.num) : Qle (mul (⟨1, 2⟩ : Q) q) q := by
  show (1 * q.num) * (q.den : Int) ≤ q.num * ((2 * q.den : Nat) : Int)
  push_cast
  have h1 : 0 ≤ q.num * (q.den : Int) := Int.mul_nonneg hq (Int.ofNat_nonneg _)
  have e1 : (1 * q.num) * (q.den : Int) = q.num * (q.den : Int) := by ring_uor
  have e2 : q.num * (2 * (q.den : Int)) = 2 * (q.num * (q.den : Int)) := by ring_uor
  omega

/-- `2⁻ᵏ·M ≤ ⟨⌈M⌉+1, 2ᵏ⟩`. -/
theorem dy_mul_le_cap (k : Nat) (M : Q) (hMd : 0 < M.den) (hMn : 0 ≤ M.num) :
    Qle (mul (dyQ k) M) (⟨((M.num.toNat + 1 : Nat) : Int), 2 ^ k⟩ : Q) := by
  refine Qle_trans (Qmul_den_pos (dyQ_den k) Nat.one_pos)
    (Qmul_le_mul_left (Int.le_of_lt (dyQ_num k)) (Qle_num_cap M hMd hMn)) ?_
  refine Qeq_le ?_
  simp only [Qeq, mul, dyQ]
  push_cast
  generalize ((2 ^ k : Nat) : Int) = P
  generalize ((M.num.toNat + 1 : Nat) : Int) = Mc
  ring_uor

/-- `⟨a, 2ᵏ⟩ + ⟨b, 2ᵏ⟩ = ⟨a + b, 2ᵏ⟩`. -/
theorem q_add_same_den (a b : Nat) (k : Nat) :
    Qeq (add (⟨(a : Int), 2 ^ k⟩ : Q) (⟨(b : Int), 2 ^ k⟩ : Q)) (⟨((a + b : Nat) : Int), 2 ^ k⟩ : Q) := by
  simp only [Qeq, add]
  push_cast
  generalize ((2 ^ k : Nat) : Int) = P
  ring_uor

/-- `⟨D, 2ᵏ⟩ ≤ ⟨D, j+1⟩` once `j + 1 ≤ 2ᵏ`. -/
theorem q_den_mono (D k j : Nat) (h : j + 1 ≤ 2 ^ k) :
    Qle (⟨(D : Int), 2 ^ k⟩ : Q) (⟨(D : Int), j + 1⟩ : Q) := by
  show (D : Int) * ((j + 1 : Nat) : Int) ≤ (D : Int) * ((2 ^ k : Nat) : Int)
  exact Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h) (Int.ofNat_nonneg _)

theorem succ_le_two_pow_of_le (j k : Nat) (hjk : j ≤ k) : j + 1 ≤ 2 ^ k :=
  Nat.le_trans (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by decide) hjk)

/-- **★★ THE IDENTIFICATION** `ArchIntegral = ArchTailForm` — the lower-end limit of the unsplit
    truncations is the constructed split tail `½·(Reg + Near + Far)`. -/
theorem ArchIntegral_eq_ArchTailForm (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f)
    (hg : CoreTest C.geom g) :
    Req (ArchIntegral C f g hf hg) (ArchTailForm C.geom f g hf hg) := by
  unfold ArchIntegral ArchTailForm
  refine Rlim_eval_real_rate _ _
    (C := nearCN C.geom f g + ((regInt C f g).M.num.toNat + 1)) (fun j => ?_)
  have hk : 1 ≤ j + archCNC C f g := by unfold archCNC; omega
  have hid := archTrunc_ident C f g hf hg (j + archCNC C f g) hk
  -- the difference is ½(J_k − Near) − ½E_k
  refine Rle_trans (Rle_of_Req (Rabs_congr (Req_trans (Rsub_congr hid (Req_refl _))
    (arch_limit_diff _ _ _ _ _)))) ?_
  refine Rle_trans (Rle_trans (Rabs_Radd _ _) (Radd_le_add (Rle_refl _) (Rle_of_Req (Rabs_Rneg _)))) ?_
  refine Rle_trans (Radd_le_add
    (Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg (Nat.succ_pos 1) (by decide) _))
      (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (nearJ_limit_rate C.geom f g _)))
    (Rle_trans (Rle_of_Req (Rabs_Rmul_ofQ_nonneg (Nat.succ_pos 1) (by decide) _))
      (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (by decide)) (archE_bound C f g _)))) ?_
  -- rational tail: ½·CN/2^k + ½·(2⁻ᵏ·M) ≤ (CN + M')/(j+1)
  refine Rle_trans (Rle_of_Req (Radd_congr (Rmul_ofQ_ofQ _ _) (Rmul_ofQ_ofQ _ _))) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_ofQ _ _)) ?_
  refine Rle_ofQ_ofQ _ (Nat.succ_pos j) ?_
  have hcn : 0 ≤ (⟨(nearCN C.geom f g : Int), 2 ^ (j + archCNC C f g)⟩ : Q).num := by
    show (0 : Int) ≤ (nearCN C.geom f g : Int); omega
  have hMn : 0 ≤ (mul (dyQ (j + archCNC C f g)) (regInt C f g).M).num :=
    Int.mul_nonneg (Int.le_of_lt (dyQ_num _)) (regInt C f g).hMn
  have h1 := half_le_self _ hcn
  have h2 := Qle_trans (Qmul_den_pos (dyQ_den _) (regInt C f g).hMd) (half_le_self _ hMn)
    (dy_mul_le_cap (j + archCNC C f g) (regInt C f g).M (regInt C f g).hMd (regInt C f g).hMn)
  refine Qle_trans (add_den_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) (Qadd_le_add h1 h2) ?_
  refine Qle_trans (Nat.two_pow_pos _) (Qeq_le (q_add_same_den _ _ _)) ?_
  exact q_den_mono _ _ j (succ_le_two_pow_of_le j _ (Nat.le_add_right j _))


end UOR.Bridge.F1Square.Square
