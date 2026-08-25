/-
F1 square — **the exact split of the truncated archimedean tail** (`AtlasTailSplit.lean`).

`archTrunc k = ∫_{1+2^{-k}}^{∞} N⁺(x)·K_k(x) dx` (the source's truncation, kernel floor `dyQ k = 2^{-k}`).
It is split EXACTLY into

 * the COMPACT tail domain `[1 + 2^{-k}, B]` (`compactTail`, a certified window integral), and
 * the FAR part `[B, ∞)`, where `F⁺_{f,g}` and `F⁺_{g,f}` vanish and only the retained subtraction
   tail `−2F⁺_{f,g}(1)/x` survives: `∫_B^∞ N⁺K = −2F⁺_{f,g}(1)·∫_B^∞ K_k(x)/x dx`.

The far coefficient `farCoef k = ∫_B^∞ K_k(x)/x dx` is a certified improper integral with decay
`1/((m+1)m)` and is NONNEGATIVE; `farTailGram = 2·farCoef·w·∫V(f)V(g)/max(t,a)` is the positive
pure-cut channel of `tailFiber_high_pure_cut` (its diagonal is nonnegative), and
`farTailGram = 2·farCoef·F⁺_{f,g}(1)`.  THE SPLIT (`archTrunc_split`):

    `archTrunc k = compactTail k − farTailGram k`   (`k ≥ 1`, core tests).

Nothing here is a sign claim about the coupled form.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.AtlasFibers
import F1Square.Square.WeilArchLimit
import F1Square.Square.WeilArchReconcile

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) The compact tail domain `[1 + 2^{-k}, B]`.
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

/-- **The compact tail** `∫_{1+2^{-k}}^{B} N⁺(x)·K_k(x) dx`. -/
def compactTail (C : NormCtx) (f g : L2Test) (k : Nat) (hk : 1 ≤ k) : Real :=
  riemannIntegralI (fullInt C f g k).hLd (fullInt C f g k).hLn (fullInt C f g k).hlip (fullInt C f g k).hfc
    (add (⟨1, 1⟩ : Q) (dyQ k)) (tailGap C k) (add_den_pos Nat.one_pos (dyQ_den k)) (tailGap_den C k)
    (tailGap_num_nonneg C k hk)

-- ===========================================================================
-- (2) The far kernel `K_k(x)/x` on `[B, ∞)` and its decay.
-- ===========================================================================

/-- The kernel product `x ↦ (1/max(x,1))·K_k(x)` as an `L2Test`. -/
def kerRec (k : Nat) : L2Test :=
  productTest (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)) (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k))

theorem kerRec_f (k : Nat) (y : Real) :
    (kerRec k).f y = Rmul (rOne y) (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) y) := rfl

/-- The far shift `2^{-k} + (B − 1 − 2^{-k})` (`= B − 1`). -/
def farShift (C : NormCtx) (k : Nat) : Q := add (dyQ k) (tailGap C k)
theorem farShift_den (C : NormCtx) (k : Nat) : 0 < (farShift C k).den := add_den_pos (dyQ_den k) (tailGap_den C k)
theorem farShift_num_nonneg (C : NormCtx) (k : Nat) (hk : 1 ≤ k) : 0 ≤ (farShift C k).num :=
  Qadd_num_nonneg_loc (Int.le_of_lt (dyQ_num k)) (tailGap_num_nonneg C k hk)

/-- `1 + farShift = B` (exactly, as rationals). -/
theorem one_add_farShift (C : NormCtx) (k : Nat) : Qeq (add (⟨1, 1⟩ : Q) (farShift C k)) (canonB C) := by
  unfold farShift tailGap Qsub canonB dyQ
  simp only [Qeq, add, neg, mul]
  push_cast
  generalize (2 : Int) ^ k = p
  ring_uor

/-- `1 ≤ farShift` (`B ≥ 2`). -/
theorem one_le_farShift (C : NormCtx) (k : Nat) : Qle (⟨1, 1⟩ : Q) (farShift C k) := by
  have h2B : Qle (⟨2, 1⟩ : Q) (canonB C) := by
    show (2 : Int) * ((1 : Nat) : Int) ≤ ((C.X + 1 : Nat) : Int) * ((1 : Nat) : Int)
    push_cast; have := C.hX; omega
  have h := Qle_congr_right (canonB_den C) (Qeq_symm (one_add_farShift C k)) h2B
  -- 2 ≤ 1 + s  ⟹  1 ≤ s
  simp only [Qle, add] at h ⊢
  push_cast at h ⊢
  omega

/-- **The far kernel** `u ↦ (K_k/x)(u + farShift)` — the kernel product on `[B, ∞)` in unit coordinates. -/
def farKer (C : NormCtx) (k : Nat) : L2Test := shiftTest (farShift C k) (farShift_den C k) (kerRec k)

theorem farKer_f (C : NormCtx) (k : Nat) (u : Real) :
    (farKer C k).f u = Rmul (rOne (Radd u (ofQ (farShift C k) (farShift_den C k))))
      (Kfl (dyQ k) (dyQ_num k) (dyQ_den k) (Radd u (ofQ (farShift C k) (farShift_den C k)))) := rfl

theorem farKer_nonneg (C : NormCtx) (k : Nat) (u : Real) : Rnonneg ((farKer C k).f u) :=
  Rnonneg_Rmul (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _)
    (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _)

/-- `1/max(y,1) ≤ 1/q` for `y ≥ q > 0`. -/
theorem rOne_le_inv (q : Q) (hqn : 0 < q.num) (hqd : 0 < q.den) (y : Real) (hy : Rle (ofQ q hqd) y) :
    Rle (rOne y) (ofQ (Qinv q) (Qinv_den_pos hqn)) :=
  Rinv_le_ofQ_inv hqn hqd (qClampQ_witness (⟨1, 1⟩ : Q) (by decide) (by decide) y)
    (Rle_trans hy (Rle_self_qClampQ (⟨1, 1⟩ : Q) (by decide) y))

/-- `affineMap a w x ≥ a` for `x ≥ 0`, `w ≥ 0`. -/
theorem affineMap_ge_a (a w : Q) (ha : 0 < a.den) (hw : 0 < w.den) (hwn : 0 ≤ w.num) (x : Real) (hx0 : Rle zero x) :
    Rle (ofQ a ha) (affineMap a w ha hw x) :=
  Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ hw hwn) (Rnonneg_of_Rle_zero hx0))

/-- `1/m · 1/(m+1) = 1/((m+1)m)` as rationals. -/
theorem inv_m_inv_succ (m : Nat) (hm : 1 ≤ m) :
    Qeq (mul (Qinv (⟨(m : Int), 1⟩ : Q)) (Qinv (⟨((m + 1 : Nat) : Int), 1⟩ : Q)))
        (mul (⟨1, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q)) := by
  simp only [Qeq, mul, Qinv]
  push_cast
  rw [Int.toNat_of_nonneg (show (0 : Int) ≤ (m : Int) by omega),
    Int.toNat_of_nonneg (show (0 : Int) ≤ (m : Int) + 1 by omega)]
  ring_uor

/-- **The far kernel decays like `1/((m+1)m)`** (`x ≥ B + m ≥ m + 2` on the `m`-th unit window). -/
theorem farKer_decay (C : NormCtx) (k : Nat) : DecayAt (farKer C k) (⟨1, 1⟩ : Q) Nat.one_pos := by
  intro m hm
  have hmn : (0 : Int) < (m : Int) := by omega
  have hm1n : (0 : Int) < ((m + 1 : Nat) : Int) := by omega
  -- pointwise bound on the window
  have hbd : ∀ x, Rle zero x → Rle x one →
      Rle (Rabs ((farKer C k).f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x)))
          (Rmul (ofQ (Qinv (⟨(m : Int), 1⟩ : Q)) (Qinv_den_pos hmn)) (ofQ (Qinv (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (Qinv_den_pos hm1n))) := by
    intro x hx0 _
    rw [farKer_f]
    have hu : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) :=
      affineMap_ge_a _ _ _ _ (by decide) x hx0
    have hs : Rle (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) (ofQ (farShift C k) (farShift_den C k)) :=
      Rle_ofQ_ofQ _ _ (one_le_farShift C k)
    have hy : Rle (ofQ (⟨((m + 1 : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) (ofQ (farShift C k) (farShift_den C k))) := by
      have hq : Qle (⟨((m + 1 : Nat) : Int) + 1, 1⟩ : Q) (add (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)) := by
        show (((m + 1 : Nat) : Int) + 1) * ((1 * 1 : Nat) : Int) ≤ (((m : Int) + 1) * ((1 : Nat) : Int) + 1 * ((1 : Nat) : Int)) * ((1 : Nat) : Int)
        push_cast; omega
      exact Rle_trans (Rle_ofQ_ofQ _ _ hq) (Rle_trans (Rle_of_Req (Req_symm (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos))) (Radd_le_add hu hs))
    have hym : Rle (ofQ (⟨(m : Int), 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) x) (ofQ (farShift C k) (farShift_den C k))) :=
      Rle_trans (Rle_ofQ_ofQ _ _ (by show (m : Int) * ((1 : Nat) : Int) ≤ (((m + 1 : Nat) : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hy
    refine Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_Rmul (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _)
      (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _)))) ?_
    exact Rmul_le_Rmul_both (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _) (Rnonneg_ofQ _ (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
      (rOne_le_inv _ hmn Nat.one_pos _ hym)
      (archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) (m + 1) (by omega) _ hy)
  have habs := riemannIntegralI_abs_le_window_real (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc
    (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) _ Nat.one_pos (by decide) (by decide) hbd
  have hK : Req (Rmul (ofQ (⟨1, 1⟩ : Q) (by decide))
      (Rmul (ofQ (Qinv (⟨(m : Int), 1⟩ : Q)) (Qinv_den_pos hmn)) (ofQ (Qinv (⟨((m + 1 : Nat) : Int), 1⟩ : Q)) (Qinv_den_pos hm1n))))
      (ofQ (mul (⟨1, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos Nat.one_pos (digamma_succ_mul_pos hm))) := by
    refine Req_trans (Rone_mul _) (Req_trans (Rmul_ofQ_ofQ _ _) (ofQ_congr _ _ (inv_m_inv_succ m hm)))
  have habs' : Rle (Rabs (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc m))
      (ofQ (mul (⟨1, 1⟩ : Q) (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos Nat.one_pos (digamma_succ_mul_pos hm))) :=
    Rle_trans habs (Rle_of_Req hK)
  exact ⟨Rneg_le_of_Rabs_le habs', Rle_of_Rabs_le habs'⟩

/-- **The far coefficient** `∫_B^∞ K_k(x)/x dx` — a certified improper integral. -/
def farCoef (C : NormCtx) (k : Nat) : Real :=
  improperIntegral1 (K := (⟨1, 1⟩ : Q)) (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc Nat.one_pos (by decide)
    (farKer_decay C k)

theorem farCoef_nonneg (C : NormCtx) (k : Nat) : Rnonneg (farCoef C k) :=
  improperIntegral1_nonneg (K := (⟨1, 1⟩ : Q)) (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc
    Nat.one_pos (by decide) (farKer_decay C k) (farKer_nonneg C k)

/-- **The far tail Gram** `2·farCoef·w·∫₀¹ V(f)V(g)/max(t,a)` — the positive pure-cut channel. -/
def farTailGram (C : NormCtx) (f g : L2Test) (k : Nat) : Real :=
  Rmul (Rmul cTwo (farCoef C k))
    (Rmul (ofQ C.w C.hw) (riemannIntegral (vvL_den C f g) (vvL_num C f g) (vvInt_lip C f g) (vvInt_fc C f g)))

/-- Its diagonal is nonnegative. -/
theorem farTailGram_diag_nonneg (C : NormCtx) (f : L2Test) (k : Nat) : Rnonneg (farTailGram C f f k) :=
  Rnonneg_Rmul (Rnonneg_Rmul (Rnonneg_ofQ Nat.one_pos (by decide)) (farCoef_nonneg C k))
    (Rnonneg_Rmul (Rnonneg_ofQ C.hw C.hwn) (riemannIntegral_nonneg _ _ _ _ (fun y =>
      Rnonneg_Rmul (Rnonneg_Rmul_self _) (Rnonneg_clampedInv C.a C.han C.had _))))

/-- `farTailGram = 2·farCoef·F⁺_{f,g}(1)`. -/
theorem farTailGram_eq_F1 (C : NormCtx) (f g : L2Test) (k : Nat) :
    Req (farTailGram C f g k) (Rmul (Rmul cTwo (farCoef C k)) ((FCanon C f g).f one)) :=
  Rmul_congr (Req_refl _) (Req_symm (FCanon_one_eq C f g))

-- ===========================================================================
-- (3) A real scalar through an improper integral (termwise).
-- ===========================================================================

/-- Termwise bounds transport to a larger decay constant. -/
theorem decay_weaken (T : Nat → Real) {K K' : Q} (hKd : 0 < K.den) (hK'd : 0 < K'.den) (hKK : Qle K K')
    (hb : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) (T m)
      ∧ Rle (T m) (ofQ (mul K (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKd (digamma_succ_mul_pos hm)))) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)))) (T m)
      ∧ Rle (T m) (ofQ (mul K' (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm))) := by
  intro m hm
  have hq : Qle (mul K (⟨1, (m + 1) * m⟩ : Q)) (mul K' (⟨1, (m + 1) * m⟩ : Q)) :=
    Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide) hKK
  have hR := Rle_ofQ_ofQ (Qmul_den_pos hKd (digamma_succ_mul_pos hm)) (Qmul_den_pos hK'd (digamma_succ_mul_pos hm)) hq
  exact ⟨Rle_trans (Rle_Rneg hR) (hb m hm).1, Rle_trans (hb m hm).2 hR⟩

/-- **`∫₁^∞ φ = c·∫₁^∞ ψ` when the unit terms satisfy `∫_m^{m+1} φ = c·∫_m^{m+1} ψ`** (real scalar `c`;
    the two decay schedules are reconciled through their sum). -/
theorem improper_Rsmul_terms {f g : Real → Real} {Lf Lg Kf Kg : Q} (hLfd : 0 < Lf.den) (hLfn : 0 ≤ Lf.num)
    (hlipf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hLfd) (Rabs (Rsub x y))))
    (hfcf : ∀ x y, Req x y → Req (f x) (f y))
    (hLgd : 0 < Lg.den) (hLgn : 0 ≤ Lg.num)
    (hlipg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hLgd) (Rabs (Rsub x y))))
    (hfcg : ∀ x y, Req x y → Req (g x) (g y))
    (hKfd : 0 < Kf.den) (hKf0 : 0 ≤ Kf.num) (hKgd : 0 < Kg.den) (hKg0 : 0 ≤ Kg.num)
    (hbf : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kf (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKfd (digamma_succ_mul_pos hm))))
          (integralTerm hLfd hLfn hlipf hfcf m)
      ∧ Rle (integralTerm hLfd hLfn hlipf hfcf m)
          (ofQ (mul Kf (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKfd (digamma_succ_mul_pos hm))))
    (hbg : ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul Kg (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKgd (digamma_succ_mul_pos hm))))
          (integralTerm hLgd hLgn hlipg hfcg m)
      ∧ Rle (integralTerm hLgd hLgn hlipg hfcg m)
          (ofQ (mul Kg (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hKgd (digamma_succ_mul_pos hm))))
    (c : Real) (hterm : ∀ m, Req (integralTerm hLfd hLfn hlipf hfcf m) (Rmul c (integralTerm hLgd hLgn hlipg hfcg m))) :
    Req (improperIntegral1 hLfd hLfn hlipf hfcf hKfd hKf0 hbf)
        (Rmul c (improperIntegral1 hLgd hLgn hlipg hfcg hKgd hKg0 hbg)) := by
  have hKd : 0 < (add Kf Kg).den := add_den_pos hKfd hKgd
  have hK0 : 0 ≤ (add Kf Kg).num := Qadd_num_nonneg_loc hKf0 hKg0
  have hbfK := decay_weaken _ hKfd hKd (Qle_add_right_nonneg hKg0) hbf
  have hbgK := decay_weaken _ hKgd hKd (Qle_add_left_nonneg hKf0) hbg
  show Req (Rlim (fun j => genSum (integralTerm hLfd hLfn hlipf hfcf) (digammaMidx Kf j)) _)
           (Rmul c (Rlim (fun j => genSum (integralTerm hLgd hLgn hlipg hfcg) (digammaMidx Kg j)) _))
  refine Req_trans (Rlim_sched_indep _ hKfd hKf0 hKd hK0 hbf hbfK) ?_
  refine Req_trans (Rmul_Rlim_of_approx c _ _ (genSum_RReg _ hKd hK0 hbgK) (genSum_RReg _ hKd hK0 hbfK)
    (fun j => genSum_Rmul_of_termwise hterm _)) ?_
  exact Rmul_congr (Req_refl c) (Rlim_sched_indep _ hKd hK0 hKgd hKg0 hbgK hbg)

-- ===========================================================================
-- (4) ★ THE SPLIT `archTrunc = compactTail − farTailGram`.
-- ===========================================================================

/-- A real scalar through a unit term: `∫_{m+1}^{m+2} c·φ = c·∫_{m+1}^{m+2} φ` (modulus `xBound c · L_φ`). -/
theorem integralTerm_smul_real (φ : L2Test) (c : Real) (m : Nat) :
    Req (integralTerm (Qmul_den_pos Nat.one_pos φ.hLd) (Qmul_num_nonneg (xBQ_num_nonneg c) φ.hLn)
          (lip_smul_fl c φ.hLd φ.hLn φ.hlip) (fc_smul_fl c φ.hfc) m)
        (Rmul c (integralTerm φ.hLd φ.hLn φ.hlip φ.hfc m)) := by
  unfold integralTerm riemannIntegralI
  have hLd' : 0 < (mul φ.L (⟨1, 1⟩ : Q)).den := Qmul_den_pos φ.hLd Nat.one_pos
  have hLn' : 0 ≤ (mul φ.L (⟨1, 1⟩ : Q)).num := Int.mul_nonneg φ.hLn (by decide)
  have hlipP := affine_lip φ.hLd φ.hLn φ.hlip (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos (by decide)
  have hfcP : ∀ x y, Req x y → Req (φ.f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos x))
      (φ.f (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos Nat.one_pos y)) :=
    fun x y h => φ.hfc _ _ (affineMap_congr _ _ _ _ h)
  have hlipS := lip_smul_fl c hLd' hLn' hlipP
  refine Req_trans (Rmul_congr (Req_refl _) (Req_trans (riemannIntegral_certif_irrel _ _ _ _
    (Qmul_den_pos Nat.one_pos hLd') (Qmul_num_nonneg (xBQ_num_nonneg c) hLn') hlipS (fc_smul_fl c hfcP))
    (riemannIntegral_smul_real_fl c hLd' hLn' hlipP hfcP))) ?_
  exact Req_trans (Req_symm (Rmul_assoc _ _ _)) (Req_trans (Rmul_congr (Rmul_comm _ _) (Req_refl _)) (Rmul_assoc _ _ _))

/-- Beyond `B` the truncated integrand is `−2F⁺_{f,g}(1)·(K_k(x)/x)`: the termwise identification of
    the far part (unit windows `[m+1, m+2]`, `m ≥ 0`, in the far-shifted coordinate). -/
theorem far_term_eq (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) (m : Nat) :
    Req (integralTerm (truncInt C f g k (farShift C k) (farShift_den C k)).hLd (truncInt C f g k (farShift C k) (farShift_den C k)).hLn
          (truncInt C f g k (farShift C k) (farShift_den C k)).hlip (truncInt C f g k (farShift C k) (farShift_den C k)).hfc m)
        (Rmul (Rneg (Rmul cTwo ((FCanon C f g).f one)))
          (integralTerm (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip (farKer C k).hfc m)) := by
  -- the scaled far kernel as an integrand with its certificate
  have hlipS := lip_smul_fl (Rneg (Rmul cTwo ((FCanon C f g).f one))) (farKer C k).hLd (farKer C k).hLn (farKer C k).hlip
  have hfcS := fc_smul_fl (Rneg (Rmul cTwo ((FCanon C f g).f one))) (farKer C k).hfc
  refine Req_trans (integralTerm_congr_ge (truncInt C f g k (farShift C k) (farShift_den C k)).hLd
    (truncInt C f g k (farShift C k) (farShift_den C k)).hLn (truncInt C f g k (farShift C k) (farShift_den C k)).hlip
    (truncInt C f g k (farShift C k) (farShift_den C k)).hfc (Qmul_den_pos Nat.one_pos (farKer C k).hLd)
    (Qmul_num_nonneg (xBQ_num_nonneg _) (farKer C k).hLn) hlipS hfcS m (fun x hx => ?_)) ?_
  · -- pointwise beyond `B`
    have hx1 : Rle (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) x :=
      Rle_trans (Rle_ofQ_ofQ _ _ (by show (1 : Int) * ((1 : Nat) : Int) ≤ ((m : Int) + 1) * ((1 : Nat) : Int); push_cast; omega)) hx
    have hy : Rle (ofQ (canonB C) (canonB_den C)) (Radd x (ofQ (farShift C k) (farShift_den C k))) := by
      refine Rle_trans (Rle_of_Req (ofQ_congr (canonB_den C) (add_den_pos Nat.one_pos (farShift_den C k)) (Qeq_symm (one_add_farShift C k)))) ?_
      refine Rle_trans (Rle_of_Req (Req_symm (Radd_ofQ_ofQ Nat.one_pos (farShift_den C k)))) ?_
      exact Radd_le_add hx1 (Rle_refl _)
    show Req (Rmul ((archNumC C f g).f (Radd x (ofQ (farShift C k) (farShift_den C k))))
                   ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f (Radd x (ofQ (farShift C k) (farShift_den C k)))))
             (Rmul (Rneg (Rmul cTwo ((FCanon C f g).f one))) ((farKer C k).f x))
    rw [archNumC_f, farKer_f]
    refine Req_trans (Rmul_congr (Radd_congr (Radd_congr (FCanon_high_vanish C f g hf _ hy) (FCanon_high_vanish C g f hg _ hy))
      (Req_refl _)) (Req_refl _)) ?_
    refine Req_trans (Rmul_congr (Req_trans (Radd_congr (Radd_zero zero) (Req_refl _)) (Req_trans (Radd_comm _ _) (Radd_zero _)))
      (Req_refl _)) ?_
    -- (−((2F1)·r))·K ≈ (−(2F1))·(r·K)
    refine Req_trans (Rmul_neg_left _ _) (Req_trans (Rneg_congr (Rmul_assoc _ _ _)) (Req_symm (Rmul_neg_left _ _)))
  · exact integralTerm_smul_real (farKer C k) _ m

/-- The far windows of the truncated integrand are bounded by `CF/(j+1)` (`|N⁺| ≤ M_{N⁺}`, `K ≤ 1/M_j`). -/
theorem far_window_bound (C : NormCtx) (f g : L2Test) (k : Nat) (hk : 1 ≤ k) (j : Nat) :
    Rle (Rabs (riemannIntegralI (truncInt C f g k (dyQ k) (dyQ_den k)).hLd (truncInt C f g k (dyQ k) (dyQ_den k)).hLn
        (truncInt C f g k (dyQ k) (dyQ_den k)).hlip (truncInt C f g k (dyQ k) (dyQ_den k)).hfc
        (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) (tailGap C k) Nat.one_pos (tailGap_den C k) (tailGap_num_nonneg C k hk)))
      (ofQ (⟨(((mul (tailGap C k) (archNumC C f g).M).num.toNat + 1 : Nat) : Int), j + 1⟩ : Q) (Nat.succ_pos j)) := by
  have hMj1 : 1 ≤ digammaMidx (archKC C f g) j := digammaMidx_ge_one _ j
  have hMjn : (0 : Int) < ((digammaMidx (archKC C f g) j : Nat) : Int) := by omega
  have hMN := (archNumC C f g).hMn
  -- pointwise bound on the window
  have hbd : ∀ x, Rle zero x → Rle x one →
      Rle (Rabs ((truncInt C f g k (dyQ k) (dyQ_den k)).f
            (affineMap (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) (tailGap C k) Nat.one_pos (tailGap_den C k) x)))
          (Rmul (ofQ (archNumC C f g).M (archNumC C f g).hMd)
            (ofQ (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q)) (Qinv_den_pos hMjn))) := by
    intro x hx0 _
    have hu : Rle (ofQ (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (affineMap (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) (tailGap C k) Nat.one_pos (tailGap_den C k) x) :=
      affineMap_ge_a _ _ _ _ (tailGap_num_nonneg C k hk) x hx0
    have hy : Rle (ofQ (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) (tailGap C k) Nat.one_pos (tailGap_den C k) x)
          (ofQ (dyQ k) (dyQ_den k))) :=
      Rle_trans hu (Rle_self_Radd_right (Rnonneg_ofQ _ (Int.le_of_lt (dyQ_num k))))
    show Rle (Rabs (Rmul ((archNumC C f g).f _) ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f _))) _
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ _ (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
      ((archNumC C f g).hbd _) ?_
    refine Rle_trans (Rle_of_Req (Rabs_of_nonneg (Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) _))) ?_
    exact archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) _ hMj1 _ hy
  have habs := riemannIntegralI_abs_le_window_real (truncInt C f g k (dyQ k) (dyQ_den k)).hLd (truncInt C f g k (dyQ k) (dyQ_den k)).hLn
    (truncInt C f g k (dyQ k) (dyQ_den k)).hlip (truncInt C f g k (dyQ k) (dyQ_den k)).hfc
    (⟨((digammaMidx (archKC C f g) j : Nat) : Int) + 1, 1⟩ : Q) (tailGap C k) _ Nat.one_pos (tailGap_den C k) (tailGap_num_nonneg C k hk) hbd
  refine Rle_trans habs ?_
  -- Δ·(M_N·(1/Mj)) ≤ CF/(j+1)
  refine Rle_trans (Rle_of_Req (Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _))) ?_
  refine Rle_ofQ_ofQ _ _ ?_
  have hcap : Qle (mul (tailGap C k) (archNumC C f g).M)
      (⟨(((mul (tailGap C k) (archNumC C f g).M).num.toNat + 1 : Nat) : Int), 1⟩ : Q) :=
    Qle_num_cap _ (Qmul_den_pos (tailGap_den C k) (archNumC C f g).hMd) (Qmul_num_nonneg (tailGap_num_nonneg C k hk) hMN)
  have hinv : Qle (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q)) (⟨1, j + 1⟩ : Q) := by
    have h1 : Qle (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q)) (Qinv (⟨((j + 1 : Nat) : Int), 1⟩ : Q)) :=
      Qinv_antitone hMjn (by show (0 : Int) < ((j + 1 : Nat) : Int); omega) (by
        show ((j + 1 : Nat) : Int) * ((1 : Nat) : Int) ≤ ((digammaMidx (archKC C f g) j : Nat) : Int) * ((1 : Nat) : Int)
        push_cast; have := digammaMidx_ge (archKC C f g) j; omega)
    refine Qle_trans (Qinv_den_pos (by show (0 : Int) < ((j + 1 : Nat) : Int); omega)) h1 (Qeq_le ?_)
    simp only [Qeq, Qinv]
    push_cast
    rw [Int.toNat_of_nonneg (show (0 : Int) ≤ (j : Int) + 1 by omega)]
    try ring_uor
  have hre : Qeq (mul (tailGap C k) (mul (archNumC C f g).M (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))))
      (mul (mul (tailGap C k) (archNumC C f g).M) (Qinv (⟨((digammaMidx (archKC C f g) j : Nat) : Int), 1⟩ : Q))) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (tailGap_den C k) (archNumC C f g).hMd) (Qinv_den_pos hMjn)) (Qeq_le hre) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos j))
    (Qmul_le_mul (Qmul_den_pos (tailGap_den C k) (archNumC C f g).hMd) Nat.one_pos (Qinv_den_pos hMjn)
      (Qmul_num_nonneg (tailGap_num_nonneg C k hk) hMN) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)) hcap hinv) ?_
  exact Qeq_le (by simp only [Qeq, mul]; push_cast; ring_uor)

/-- **★ THE EXACT SPLIT** (`k ≥ 1`, core tests): `archTrunc k = compactTail k − farTailGram k`. -/
theorem archTrunc_split (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g) (k : Nat) (hk : 1 ≤ k) :
    Req (archTrunc C f g hf hg k) (Rsub (compactTail C f g k hk) (farTailGram C f g k)) := by
  have hb1 := truncDecay C f g hf hg k (farShift C k) (farShift_den C k) (farShift_num_nonneg C k hk)
  have hsplit := improper_split_shift (fullInt C f g k) (dyQ k) (tailGap C k) (dyQ_den k) (tailGap_den C k)
    (tailGap_num_pos C k hk) (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg k (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k))) hb1
    ((mul (tailGap C k) (archNumC C f g).M).num.toNat + 1) (far_window_bound C f g k hk)
  refine Req_trans hsplit (Radd_congr ?_ ?_)
  · exact shift_window (dyQ k) (dyQ_den k) (fullInt C f g k) (⟨1, 1⟩ : Q) (tailGap C k) Nat.one_pos (tailGap_den C k)
      (tailGap_num_nonneg C k hk)
  · -- the far part is `−2F⁺(1)·farCoef`
    refine Req_trans (improper_Rsmul_terms _ _ _ _ _ _ _ _ (archKC_den C f g) (archKC_num C f g) Nat.one_pos (by decide)
      hb1 (farKer_decay C k) (Rneg (Rmul cTwo ((FCanon C f g).f one))) (far_term_eq C f g hf hg k)) ?_
    -- (−(2F1))·fc ≈ −((2fc)·F1) = −farTailGram
    refine Req_trans (Rmul_neg_left _ _) (Rneg_congr ?_)
    refine Req_trans (Rmul_assoc cTwo _ _) (Req_trans (Rmul_congr (Req_refl cTwo) (Rmul_comm _ _)) (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_))
    exact Req_symm (farTailGram_eq_F1 C f g k)

end UOR.Bridge.F1Square.Square
