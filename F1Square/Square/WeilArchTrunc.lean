/-
F1 square — **the honest truncations of the UNSPLIT archimedean integral** (`WeilArchTrunc.lean`):
the shifted integrand family

    `g_{k,δ}(u) = N⁺(u+δ) · 1/max((u+δ) − (u+δ)⁻¹, 2⁻ᵏ)`      (`truncInt C f g k δ`),

so that `∫_1^M g_{k,δ} = ∫_{1+δ}^{M+δ} N⁺(x)/(x − x⁻¹) dx` for `δ ≥ 2⁻ᵏ` (kernel inert), and its
UNIFORM block decay `|∫_{[m+1,m+2]} g_{k,δ}| ≤ K/((m+1)m)` (the constant `archKC` depends on neither
`k` nor `δ`): late blocks by the retained-tail bound `|N⁺| ≤ K_l/(m+1)` times the kernel cap
`1/m`, early blocks by width·sup.  Hence the upper-end truncations converge — the improper integral
`archTrunc k = ∫_{1+2⁻ᵏ}^{∞} N⁺(x)/(x − x⁻¹) dx` exists as a Bishop limit of integer truncations.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchNumC
import F1Square.Square.WeilShiftTest

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The shifted integrand family.
-- ===========================================================================

/-- The unshifted full integrand `N⁺(x)·(1/max(x − x⁻¹, 2⁻ᵏ))`. -/
def fullInt (C : NormCtx) (f g : L2Test) (k : Nat) : L2Test :=
  productTest (archNumC C f g) (archKernFull (dyQ k) (dyQ_num k) (dyQ_den k))

theorem fullInt_f (C : NormCtx) (f g : L2Test) (k : Nat) (x : Real) :
    (fullInt C f g k).f x = Rmul ((archNumC C f g).f x) ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f x) :=
  rfl

/-- **The shifted integrand** `g_{k,δ}(u) = (fullInt k)(u + δ)`. -/
def truncInt (C : NormCtx) (f g : L2Test) (k : Nat) (δ : Q) (hδd : 0 < δ.den) : L2Test :=
  shiftTest δ hδd (fullInt C f g k)

theorem truncInt_f (C : NormCtx) (f g : L2Test) (k : Nat) (δ : Q) (hδd : 0 < δ.den) (u : Real) :
    (truncInt C f g k δ hδd).f u
      = Rmul ((archNumC C f g).f (Radd u (ofQ δ hδd)))
          ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f (Radd u (ofQ δ hδd))) := rfl

-- ===========================================================================
-- (2) The uniform decay constant and its two envelopes.
-- ===========================================================================

/-- `K = M_{N⁺}·Bd² + K_l` — independent of `k` and `δ`. -/
def archKC (C : NormCtx) (f g : L2Test) : Q :=
  add (mul (archNumC C f g).M (⟨C.geom.Bd.num * C.geom.Bd.num, 1⟩ : Q)) (archKl C.geom f g)

theorem archKC_den (C : NormCtx) (f g : L2Test) : 0 < (archKC C f g).den :=
  add_den_pos (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos) (archKl_den C.geom f g)

theorem archKC_num (C : NormCtx) (f g : L2Test) : 0 ≤ (archKC C f g).num := by
  have hBdn : 0 < C.geom.Bd.num := qnum_pos_of_one_le C.geom.hBdd C.geom.hBd1
  have h1 : 0 ≤ (mul (archNumC C f g).M (⟨C.geom.Bd.num * C.geom.Bd.num, 1⟩ : Q)).num :=
    Int.mul_nonneg (archNumC C f g).hMn (Int.mul_nonneg (Int.le_of_lt hBdn) (Int.le_of_lt hBdn))
  have h2 := archKl_num C.geom f g
  show 0 ≤ (mul (archNumC C f g).M (⟨C.geom.Bd.num * C.geom.Bd.num, 1⟩ : Q)).num
      * ((archKl C.geom f g).den : Int)
      + (archKl C.geom f g).num * ((mul (archNumC C f g).M (⟨C.geom.Bd.num * C.geom.Bd.num, 1⟩ : Q)).den : Int)
  exact Int.add_nonneg (Int.mul_nonneg h1 (Int.ofNat_nonneg _)) (Int.mul_nonneg h2 (Int.ofNat_nonneg _))

/-- Early envelope: `M ≤ K/((m+1)m)` for `m+1 < Bd`. -/
theorem archKC_early (C : NormCtx) (f g : L2Test) (m : Nat) (hm : 1 ≤ m)
    (hlt : Qlt (⟨(m : Int) + 1, 1⟩ : Q) C.geom.Bd) :
    Qle (mul (⟨1, 1⟩ : Q) (archNumC C f g).M) (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q)) := by
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos (archNumC C f g).hMd Nat.one_pos)
    (digamma_succ_mul_pos hm)) (K_early_general C.geom (archNumC C f g).M (archNumC C f g).hMn m hm hlt) ?_
  exact Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) (Qle_self_add (archKl_num C.geom f g))

/-- Late envelope: `K_l/((m+1)m) ≤ K/((m+1)m)`. -/
theorem archKC_late (C : NormCtx) (f g : L2Test) (m : Nat) :
    Qle (mul (archKl C.geom f g) (⟨1, (m + 1) * m⟩ : Q)) (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q)) := by
  have hBdn : 0 < C.geom.Bd.num := qnum_pos_of_one_le C.geom.hBdd C.geom.hBd1
  refine Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) ?_
  exact Qle_self_add_l (Int.mul_nonneg (archNumC C f g).hMn
    (Int.mul_nonneg (Int.le_of_lt hBdn) (Int.le_of_lt hBdn)))

-- ===========================================================================
-- (3) THE UNIFORM BLOCK DECAY of the shifted family.
-- ===========================================================================

/-- `1/m ≤ 1` for `m ≥ 1`. -/
theorem qinv_nat_le_one (m : Nat) (hm : 1 ≤ m) :
    Qle (Qinv (⟨(m : Int), 1⟩ : Q)) (⟨1, 1⟩ : Q) :=
  qinv_le_one Nat.one_pos (by
    show (1 : Int) * ((1 : Nat) : Int) ≤ (m : Int) * ((1 : Nat) : Int); push_cast; omega)

/-- `K_l·(1/(m+1))·(1/m) = K_l/((m+1)m)`. -/
theorem late_product_eq (Kl : Q) (m : Nat) (hm : 1 ≤ m) :
    Qeq (mul (mul Kl (Qinv (⟨(m : Int) + 1, 1⟩ : Q))) (Qinv (⟨(m : Int), 1⟩ : Q)))
        (mul Kl (⟨1, (m + 1) * m⟩ : Q)) := by
  have hm1 : (0 : Int) < (m : Int) + 1 := by omega
  have hm0 : (0 : Int) < (m : Int) := by omega
  simp only [Qeq, mul, Qinv]
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hm1), Int.toNat_of_nonneg (Int.le_of_lt hm0)]
  simp only [Int.mul_one, Int.mul_assoc]

/-- **THE UNIFORM BLOCK DECAY** of `g_{k,δ}` (`δ ≥ 0`): `|∫_{[m+1,m+2]} g_{k,δ}| ≤ K/((m+1)m)`, with
    `K = archKC` independent of `k` and `δ`. -/
theorem truncDecay (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) (δ : Q) (hδd : 0 < δ.den) (hδn : 0 ≤ δ.num) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))))
          (integralTerm (truncInt C f g k δ hδd).hLd (truncInt C f g k δ hδd).hLn
            (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc m)
      ∧ Rle (integralTerm (truncInt C f g k δ hδd).hLd (truncInt C f g k δ hδd).hLn
            (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc m)
          (ofQ (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))) := by
  intro m hm
  have hm1n : (0 : Int) < (m : Int) + 1 := by omega
  have hm0n : (0 : Int) < (m : Int) := by omega
  -- every window point, after the shift, is ≥ m+1
  have hpt : ∀ t : Real, Rle zero t →
      Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (Radd (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) t) (ofQ δ hδd)) :=
    fun t ht0 => Rle_trans (blockPoint_ge m t ht0) (Rle_self_Radd_right (Rnonneg_ofQ hδd hδn))
  have hKnn : ∀ x, Rnonneg ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f x) := fun x => by
    rw [archKernFull_f]; exact Rnonneg_clampedInv (dyQ k) (dyQ_num k) (dyQ_den k) (innerXm x)
  have habs : Rle (Rabs (integralTerm (truncInt C f g k δ hδd).hLd (truncInt C f g k δ hδd).hLn
        (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc m))
      (ofQ (mul (archKC C f g) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))) := by
    rcases Qle_or_Qlt C.geom.Bd (⟨(m : Int) + 1, 1⟩ : Q) with hpast | hearly
    · -- LATE: |N⁺| ≤ K_l/(m+1), K ≤ 1/m
      have hBLd : 0 < (mul (mul (archKl C.geom f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q)))
          (Qinv (⟨(m : Int), 1⟩ : Q))).den :=
        Qmul_den_pos (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
      refine Rle_trans (riemannIntegralI_abs_le_window (truncInt C f g k δ hδd).hLd
        (truncInt C f g k δ hδd).hLn (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
        (mul (mul (archKl C.geom f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q))) (Qinv (⟨(m : Int), 1⟩ : Q)))
        Nat.one_pos (by decide) (by decide) hBLd ?_) ?_
      · intro t ht0 _
        have hx := hpt t ht0
        rw [truncInt_f]
        have hNb := archNumC_late_bound C f g hf hg (⟨(m : Int) + 1, 1⟩ : Q) hm1n Nat.one_pos _ hx hpast
        have hkb := archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) m hm _ hx
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
          (Rnonneg_ofQ (Qinv_den_pos hm0n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
          hNb (Rle_trans (Rle_of_Req (Rabs_of_nonneg (hKnn _))) hkb)) ?_
        refine Rle_of_Req (Req_trans (Rmul_congr
          (Rmul_ofQ_ofQ (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Req_refl _)) ?_)
        exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den C.geom f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm0n)
      · refine Rle_ofQ_ofQ (Qmul_den_pos (by decide) hBLd)
          (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm)) ?_
        refine Qle_trans hBLd (Qeq_le (Qone_mul _)) ?_
        refine Qle_trans (Qmul_den_pos (archKl_den C.geom f g) (digamma_succ_mul_pos hm))
          (Qeq_le (late_product_eq (archKl C.geom f g) m hm)) ?_
        exact archKC_late C f g m
    · -- EARLY: |N⁺| ≤ M, K ≤ 1/m ≤ 1
      refine Rle_trans (riemannIntegralI_abs_le_window (truncInt C f g k δ hδd).hLd
        (truncInt C f g k δ hδd).hLn (truncInt C f g k δ hδd).hlip (truncInt C f g k δ hδd).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (archNumC C f g).M
        Nat.one_pos (by decide) (by decide) (archNumC C f g).hMd ?_) ?_
      · intro t ht0 _
        have hx := hpt t ht0
        rw [truncInt_f]
        have hkb := archKernFull_le_inv (dyQ k) (dyQ_num k) (dyQ_den k) m hm _ hx
        have hk1 : Rle ((archKernFull (dyQ k) (dyQ_num k) (dyQ_den k)).f _) one :=
          Rle_trans hkb (Rle_ofQ_ofQ _ (by decide) (qinv_nat_le_one m hm))
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ (by decide) (by decide))
          ((archNumC C f g).hbd _) (Rle_trans (Rle_of_Req (Rabs_of_nonneg (hKnn _))) hk1)) ?_
        exact Rle_of_Req (Rmul_one _)
      · exact Rle_ofQ_ofQ (Qmul_den_pos (by decide) (archNumC C f g).hMd)
          (Qmul_den_pos (archKC_den C f g) (digamma_succ_mul_pos hm))
          (archKC_early C f g m hm hearly)
  exact ⟨Rneg_le_of_Rabs_le habs, Rle_of_Rabs_le habs⟩

-- ===========================================================================
-- (4) THE HONEST TRUNCATION `∫_{1+2⁻ᵏ}^{∞} N⁺(x)/(x − x⁻¹) dx`.
-- ===========================================================================

/-- **The `k`-th truncation** — the improper integral (Bishop limit of the integer truncations
    `∫_{1+2⁻ᵏ}^{M+2⁻ᵏ}`) of the unsplit integrand with the lower end at `1 + 2⁻ᵏ`. -/
def archTrunc (C : NormCtx) (f g : L2Test) (hf : CoreTest C.geom f) (hg : CoreTest C.geom g)
    (k : Nat) : Real :=
  improperIntegral1 (truncInt C f g k (dyQ k) (dyQ_den k)).hLd (truncInt C f g k (dyQ k) (dyQ_den k)).hLn
    (truncInt C f g k (dyQ k) (dyQ_den k)).hlip (truncInt C f g k (dyQ k) (dyQ_den k)).hfc
    (archKC_den C f g) (archKC_num C f g)
    (truncDecay C f g hf hg k (dyQ k) (dyQ_den k) (Int.le_of_lt (dyQ_num k)))


end UOR.Bridge.F1Square.Square
