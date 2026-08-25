/-
F1 square — **finite linearity of the certified unit integral** (`IntegralFiniteLin.lean`).

Generic toolkit consumed by the dyadic Atlas readback: rational modulus sums `QsumN`, closure of
the Lipschitz certificate under finite sums (`lip_RsumN_fl`) and real scalars (`lip_smul_fl`, with
the canonical bound `|c| ≤ xBound c`), finite linearity of the dyadic Riemann sums
(`riemannSum_RsumN_fl`) and of the certified integral (`riemannIntegral_RsumN_fl`,
`riemannIntegral_smul_real_fl`), and `RReg` transport along `≈` (`RReg_congr_fl`).
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.IntegralRsmul
import F1Square.Analysis.RiemannSum
import F1Square.Analysis.RabsLemmas
import F1Square.Analysis.ThetaValueDecay
import F1Square.Analysis.ExpLog

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

theorem RsumN_zero_fl (F : Nat → Real) : RsumN F 0 = zero := rfl
theorem RsumN_succ_fl (F : Nat → Real) (n : Nat) : RsumN F (n + 1) = Radd (RsumN F n) (F n) := rfl

attribute [local irreducible] RsumN

-- ===========================================================================
-- (1) Rational modulus sums.
-- ===========================================================================

/-- `Σ_{m<n} L m` over `ℚ`. -/
def QsumN (L : Nat → Q) : Nat → Q
  | 0 => (⟨0, 1⟩ : Q)
  | (n + 1) => add (QsumN L n) (L n)

theorem QsumN_den_pos (L : Nat → Q) (hd : ∀ m, 0 < (L m).den) : ∀ n, 0 < (QsumN L n).den
  | 0 => Nat.one_pos
  | (n + 1) => add_den_pos (QsumN_den_pos L hd n) (hd n)

theorem QsumN_num_nonneg (L : Nat → Q) (hn : ∀ m, 0 ≤ (L m).num) : ∀ n, 0 ≤ (QsumN L n).num
  | 0 => by show (0 : Int) ≤ 0; decide
  | (n + 1) => Qadd_num_nonneg_loc (QsumN_num_nonneg L hn n) (hn n)

/-- `Σ_{m<n} L m ≤ Σ_{m<n+1} L m` (non-negative terms). -/
theorem QsumN_le_succ (L : Nat → Q) (hn : ∀ m, 0 ≤ (L m).num) (n : Nat) :
    Qle (QsumN L n) (QsumN L (n + 1)) :=
  Qle_add_right_nonneg (hn n)

theorem QsumN_mono (L : Nat → Q) (hd : ∀ m, 0 < (L m).den) (hn : ∀ m, 0 ≤ (L m).num) (n : Nat) :
    ∀ k, Qle (QsumN L n) (QsumN L (n + k))
  | 0 => Qle_refl _
  | (k + 1) => Qle_trans (QsumN_den_pos L hd (n + k)) (QsumN_mono L hd hn n k) (QsumN_le_succ L hn (n + k))

/-- Each term is dominated by the full sum: `L m ≤ Σ_{m'<n} L m'` for `m < n`. -/
theorem Qle_term_QsumN (L : Nat → Q) (hd : ∀ m, 0 < (L m).den) (hn : ∀ m, 0 ≤ (L m).num)
    (m n : Nat) (hmn : m < n) : Qle (L m) (QsumN L n) := by
  have h1 : Qle (L m) (QsumN L (m + 1)) := Qle_add_left_nonneg (QsumN_num_nonneg L hn m)
  have h2 : Qle (QsumN L (m + 1)) (QsumN L (m + 1 + (n - (m + 1)))) := QsumN_mono L hd hn (m + 1) _
  have he : m + 1 + (n - (m + 1)) = n := by omega
  rw [he] at h2
  exact Qle_trans (QsumN_den_pos L hd (m + 1)) h1 h2

-- ===========================================================================
-- (2) Lipschitz closure.
-- ===========================================================================

/-- Weakening the modulus. -/
theorem lip_weaken_fl {f : Real → Real} {L L' : Q} (hLd : 0 < L.den) (hL'd : 0 < L'.den) (hLL : Qle L L')
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L' hL'd) (Rabs (Rsub x y))) :=
  fun x y => Rle_trans (hlip x y) (Rmul_le_Rmul_right (Rnonneg_Rabs _) (Rle_ofQ_ofQ hLd hL'd hLL))

/-- Sums of Lipschitz functions. -/
theorem lip_add_fl {f g : Real → Real} {Lf Lg : Q} (hfd : 0 < Lf.den) (hgd : 0 < Lg.den)
    (hf : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ Lf hfd) (Rabs (Rsub x y))))
    (hg : ∀ x y, Rle (Rabs (Rsub (g x) (g y))) (Rmul (ofQ Lg hgd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Radd (f x) (g x)) (Radd (f y) (g y))))
      (Rmul (ofQ (add Lf Lg) (add_den_pos hfd hgd)) (Rabs (Rsub x y))) :=
  fun x y => Rle_trans (Radd_lipschitz_real hf hg x y)
    (Rmul_le_Rmul_right (Rnonneg_Rabs _) (Rle_of_Req (Radd_ofQ_ofQ hfd hgd)))

theorem lip_zero_fl : ∀ x y : Real,
    Rle (Rabs (Rsub zero zero)) (Rmul (ofQ (⟨0, 1⟩ : Q) Nat.one_pos) (Rabs (Rsub x y))) :=
  const_lip0 zero

/-- Finite sums of Lipschitz functions, modulus `QsumN`. -/
theorem lip_RsumN_fl (H : Nat → Real → Real) (Lh : Nat → Q) (hd : ∀ m, 0 < (Lh m).den)
    (hlip : ∀ m x y, Rle (Rabs (Rsub (H m x) (H m y))) (Rmul (ofQ (Lh m) (hd m)) (Rabs (Rsub x y)))) :
    ∀ n x y, Rle (Rabs (Rsub (RsumN (fun m => H m x) n) (RsumN (fun m => H m y) n)))
      (Rmul (ofQ (QsumN Lh n) (QsumN_den_pos Lh hd n)) (Rabs (Rsub x y)))
  | 0, x, y => by rw [RsumN_zero_fl, RsumN_zero_fl]; exact lip_zero_fl x y
  | (n + 1), x, y => by
      rw [RsumN_succ_fl, RsumN_succ_fl]
      exact lip_add_fl (QsumN_den_pos Lh hd n) (hd n) (lip_RsumN_fl H Lh hd hlip n) (hlip n) x y

theorem fc_RsumN_fl (H : Nat → Real → Real) (hfc : ∀ m x y, Req x y → Req (H m x) (H m y)) :
    ∀ n x y, Req x y → Req (RsumN (fun m => H m x) n) (RsumN (fun m => H m y) n)
  | 0, _, _, _ => by rw [RsumN_zero_fl, RsumN_zero_fl]; exact Req_refl _
  | (n + 1), x, y, h => by
      rw [RsumN_succ_fl, RsumN_succ_fl]
      exact Radd_congr (fc_RsumN_fl H hfc n x y h) (hfc n x y h)

/-- `xBound c` as a rational. -/
def xBQ (c : Real) : Q := (⟨(xBound c : Int), 1⟩ : Q)

theorem xBQ_num_nonneg (c : Real) : 0 ≤ (xBQ c).num := Int.ofNat_nonneg _

/-- Real-scalar multiples: modulus `xBound c · L`. -/
theorem lip_smul_fl (c : Real) {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y)))) :
    ∀ x y, Rle (Rabs (Rsub (Rmul c (f x)) (Rmul c (f y))))
      (Rmul (ofQ (mul (xBQ c) L) (Qmul_den_pos Nat.one_pos hLd)) (Rabs (Rsub x y))) := by
  intro x y
  have h1 : Req (Rabs (Rsub (Rmul c (f x)) (Rmul c (f y)))) (Rmul (Rabs c) (Rabs (Rsub (f x) (f y)))) :=
    Req_trans (Rabs_congr (Req_symm (Rmul_sub_distrib c (f x) (f y)))) (Rabs_Rmul c _)
  refine Rle_trans (Rle_of_Req h1) ?_
  refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs c)
    (Rnonneg_Rmul (Rnonneg_ofQ hLd hLn) (Rnonneg_Rabs _)) (Rabs_le_ofQ_xBound c) (hlip x y)) ?_
  exact Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _))
    (Rmul_congr (Rmul_ofQ_ofQ Nat.one_pos hLd) (Req_refl _)))

theorem fc_smul_fl (c : Real) {f : Real → Real} (hfc : ∀ x y, Req x y → Req (f x) (f y)) :
    ∀ x y, Req x y → Req (Rmul c (f x)) (Rmul c (f y)) :=
  fun x y h => Rmul_congr (Req_refl c) (hfc x y h)

-- ===========================================================================
-- (3) Finite linearity of the dyadic Riemann sums.
-- ===========================================================================

theorem riemannSum_zero_fn_fl (N : Nat) : Req (riemannSum (fun _ => zero) N) zero := riemannSum_const zero N

/-- `riemannSum (Σ_m H m) N ≈ Σ_m riemannSum (H m) N`. -/
theorem riemannSum_RsumN_fl (H : Nat → Real → Real) (N : Nat) :
    ∀ n, Req (riemannSum (fun x => RsumN (fun m => H m x) n) N) (RsumN (fun m => riemannSum (H m) N) n)
  | 0 => by
      rw [RsumN_zero_fl]
      refine Req_trans (riemannSum_congr N (fun i _ => ?_)) (riemannSum_zero_fn_fl N)
      rw [RsumN_zero_fl]; exact Req_refl _
  | (n + 1) => by
      rw [RsumN_succ_fl]
      refine Req_trans (riemannSum_congr (g := fun x => Radd (RsumN (fun m => H m x) n) (H n x)) N
        (fun i _ => by rw [RsumN_succ_fl]; exact Req_refl _)) ?_
      refine Req_trans (riemannSum_add _ _ N) ?_
      exact Radd_congr (riemannSum_RsumN_fl H N n) (Req_refl _)

-- ===========================================================================
-- (4) Finite linearity of the certified integral.
-- ===========================================================================

/-- **`∫₀¹ Σ_m H m ≈ Σ_m ∫₀¹ H m`** with the `QsumN` modulus on the left and each term's own
    modulus on the right. -/
theorem riemannIntegral_RsumN_fl (H : Nat → Real → Real) (Lh : Nat → Q)
    (hd : ∀ m, 0 < (Lh m).den) (hn : ∀ m, 0 ≤ (Lh m).num)
    (hlip : ∀ m x y, Rle (Rabs (Rsub (H m x) (H m y))) (Rmul (ofQ (Lh m) (hd m)) (Rabs (Rsub x y))))
    (hfc : ∀ m x y, Req x y → Req (H m x) (H m y)) :
    ∀ n, Req (riemannIntegral (f := fun x => RsumN (fun m => H m x) n)
                (QsumN_den_pos Lh hd n) (QsumN_num_nonneg Lh hn n)
                (lip_RsumN_fl H Lh hd hlip n) (fc_RsumN_fl H hfc n))
             (RsumN (fun m => riemannIntegral (hd m) (hn m) (hlip m) (hfc m)) n)
  | 0 => by
      have hlip0 : ∀ x y : Real, Rle (Rabs (Rsub zero zero))
          (Rmul (ofQ (QsumN Lh 0) (QsumN_den_pos Lh hd 0)) (Rabs (Rsub x y))) := const_lip0 zero
      have hfc0 : ∀ x y : Real, Req x y → Req zero zero := fun _ _ _ => Req_refl zero
      refine Req_trans (riemannIntegral_congr (f := fun x => RsumN (fun m => H m x) 0) (g := fun _ => zero)
        (QsumN_den_pos Lh hd 0) (QsumN_num_nonneg Lh hn 0) (lip_RsumN_fl H Lh hd hlip 0) (fc_RsumN_fl H hfc 0)
        hlip0 hfc0 (fun x => by
          show Req (RsumN (fun m => H m x) 0) zero
          rw [RsumN_zero_fl]; exact Req_refl _)) ?_
      refine Req_trans (riemannIntegral_const_gen zero (QsumN_den_pos Lh hd 0) (QsumN_num_nonneg Lh hn 0)
        hlip0 hfc0) ?_
      rw [RsumN_zero_fl]; exact Req_refl _
  | (n + 1) => by
      rw [RsumN_succ_fl]
      -- moduli
      have hSn : Qle (QsumN Lh n) (QsumN Lh (n + 1)) := QsumN_le_succ Lh hn n
      have hTn : Qle (Lh n) (QsumN Lh (n + 1)) := Qle_term_QsumN Lh hd hn n (n + 1) (Nat.lt_succ_self n)
      have hlipS := lip_weaken_fl (QsumN_den_pos Lh hd n) (QsumN_den_pos Lh hd (n + 1)) hSn (lip_RsumN_fl H Lh hd hlip n)
      have hlipT := lip_weaken_fl (hd n) (QsumN_den_pos Lh hd (n + 1)) hTn (hlip n)
      -- certificates of the `Radd`-form integrand at the modulus `QsumN Lh (n+1) = QsumN Lh n + Lh n`
      have hlipA : ∀ x y, Rle (Rabs (Rsub (Radd (RsumN (fun m => H m x) n) (H n x))
            (Radd (RsumN (fun m => H m y) n) (H n y))))
          (Rmul (ofQ (QsumN Lh (n + 1)) (QsumN_den_pos Lh hd (n + 1))) (Rabs (Rsub x y))) :=
        lip_add_fl (QsumN_den_pos Lh hd n) (hd n) (lip_RsumN_fl H Lh hd hlip n) (hlip n)
      have hfcA : ∀ x y, Req x y → Req (Radd (RsumN (fun m => H m x) n) (H n x))
          (Radd (RsumN (fun m => H m y) n) (H n y)) :=
        fun x y h => Radd_congr (fc_RsumN_fl H hfc n x y h) (hfc n x y h)
      refine Req_trans (riemannIntegral_congr (f := fun x => RsumN (fun m => H m x) (n + 1))
        (g := fun x => Radd (RsumN (fun m => H m x) n) (H n x))
        (QsumN_den_pos Lh hd (n + 1)) (QsumN_num_nonneg Lh hn (n + 1))
        (lip_RsumN_fl H Lh hd hlip (n + 1)) (fc_RsumN_fl H hfc (n + 1)) hlipA hfcA
        (fun x => by
          show Req (RsumN (fun m => H m x) (n + 1)) (Radd (RsumN (fun m => H m x) n) (H n x))
          rw [RsumN_succ_fl]; exact Req_refl _)) ?_
      refine Req_trans (riemannIntegral_add (QsumN_den_pos Lh hd (n + 1)) (QsumN_num_nonneg Lh hn (n + 1))
        hlipS (fc_RsumN_fl H hfc n) hlipT (hfc n) hlipA hfcA) ?_
      refine Radd_congr ?_ ?_
      · refine Req_trans (riemannIntegral_certif_irrel (QsumN_den_pos Lh hd (n + 1)) (QsumN_num_nonneg Lh hn (n + 1))
          hlipS (fc_RsumN_fl H hfc n) (QsumN_den_pos Lh hd n) (QsumN_num_nonneg Lh hn n)
          (lip_RsumN_fl H Lh hd hlip n) (fc_RsumN_fl H hfc n)) ?_
        exact riemannIntegral_RsumN_fl H Lh hd hn hlip hfc n
      · exact riemannIntegral_certif_irrel (QsumN_den_pos Lh hd (n + 1)) (QsumN_num_nonneg Lh hn (n + 1))
          hlipT (hfc n) (hd n) (hn n) (hlip n) (hfc n)

/-- `(xBound c + 1)` as a rational. -/
def xBQ1 (c : Real) : Q := (⟨((xBound c + 1 : Nat) : Int), 1⟩ : Q)

theorem xBQ1_num_nonneg (c : Real) : 0 ≤ (xBQ1 c).num := Int.ofNat_nonneg _

/-- `L ≤ (xBound c + 1)·L` for `L ≥ 0`. -/
theorem Qle_L_xBQ1_mul (c : Real) {L : Q} (hLn : 0 ≤ L.num) : Qle L (mul (xBQ1 c) L) := by
  show L.num * ((1 * L.den : Nat) : Int) ≤ (((xBound c + 1 : Nat) : Int) * L.num) * (L.den : Int)
  have hprod : 0 ≤ ((xBound c : Nat) : Int) * L.num := Int.mul_nonneg (Int.ofNat_nonneg _) hLn
  have hden : (0 : Int) ≤ (L.den : Int) := Int.ofNat_nonneg _
  have hnum : L.num ≤ (((xBound c : Nat) : Int) + 1) * L.num := by
    rw [Int.add_mul, Int.one_mul]
    generalize ((xBound c : Nat) : Int) * L.num = p at hprod ⊢
    omega
  push_cast
  rw [Int.one_mul]
  exact Int.mul_le_mul_of_nonneg_right hnum hden

/-- `xBound c · L ≤ (xBound c + 1)·L` for `L ≥ 0`. -/
theorem Qle_xBQ_xBQ1_mul (c : Real) {L : Q} (hLn : 0 ≤ L.num) : Qle (mul (xBQ c) L) (mul (xBQ1 c) L) := by
  refine Qmul_le_mul_right hLn ?_
  show ((xBound c : Nat) : Int) * ((1 : Nat) : Int) ≤ ((xBound c + 1 : Nat) : Int) * ((1 : Nat) : Int)
  push_cast; omega

/-- **`∫₀¹ c·f ≈ c·∫₀¹ f`** for a REAL scalar `c`, with the sourced modulus `xBound c · L` on the left. -/
theorem riemannIntegral_smul_real_fl (c : Real) {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) :
    Req (riemannIntegral (f := fun x => Rmul c (f x)) (Qmul_den_pos Nat.one_pos hLd)
          (Qmul_num_nonneg (xBQ_num_nonneg c) hLn) (lip_smul_fl c hLd hLn hlip) (fc_smul_fl c hfc))
        (Rmul c (riemannIntegral hLd hLn hlip hfc)) := by
  have hL1d : 0 < (mul (xBQ1 c) L).den := Qmul_den_pos Nat.one_pos hLd
  have hL1n : 0 ≤ (mul (xBQ1 c) L).num := Qmul_num_nonneg (xBQ1_num_nonneg c) hLn
  have hlipf' := lip_weaken_fl hLd hL1d (Qle_L_xBQ1_mul c hLn) hlip
  have hlipcf' := lip_weaken_fl (Qmul_den_pos Nat.one_pos hLd) hL1d (Qle_xBQ_xBQ1_mul c hLn) (lip_smul_fl c hLd hLn hlip)
  refine Req_trans (riemannIntegral_certif_irrel _ _ (lip_smul_fl c hLd hLn hlip) (fc_smul_fl c hfc)
    hL1d hL1n hlipcf' (fc_smul_fl c hfc)) ?_
  refine Req_trans (riemannIntegral_Rsmul c hL1d hL1n hlipf' hfc hlipcf' (fc_smul_fl c hfc)) ?_
  exact Rmul_congr (Req_refl c) (riemannIntegral_certif_irrel _ _ hlipf' hfc hLd hLn hlip hfc)

-- ===========================================================================
-- (5) `RReg` transport along `≈`.
-- ===========================================================================

theorem RReg_congr_fl {Y Z : Nat → Real} (h : ∀ j, Req (Y j) (Z j)) (hZ : RReg Z) : RReg Y := by
  refine RReg_of_real_bound Y (fun j k => add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
    (fun j k => add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
    (fun j k => Qle_refl _) ?_
  intro j k
  refine Rle_trans (Rle_of_Req (Rsub_congr (h j) (h k))) ?_
  intro n
  show Qle (add ((Z j).seq (2 * n + 1)) (neg ((Z k).seq (2 * n + 1))))
        (add (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨2, n + 1⟩ : Q))
  have hr := hZ j k (2 * n + 1)
  have h1 : Qle (add ((Z j).seq (2 * n + 1)) (neg ((Z k).seq (2 * n + 1))))
      (Qabs (Qsub ((Z j).seq (2 * n + 1)) ((Z k).seq (2 * n + 1)))) := Qle_self_Qabs _
  have h2 : Qle (add (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨2, (2 * n + 1) + 1⟩ : Q))
      (add (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨2, n + 1⟩ : Q)) := by
    refine Qadd_le_add (Qle_refl _) ?_
    show (2 : Int) * ((n + 1 : Nat) : Int) ≤ 2 * (((2 * n + 1) + 1 : Nat) : Int)
    push_cast; omega
  exact Qle_trans (Qabs_den_pos (Qsub_den_pos ((Z j).den_pos _) ((Z k).den_pos _)))
    h1 (Qle_trans (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)) hr h2)

end UOR.Bridge.F1Square.Square
