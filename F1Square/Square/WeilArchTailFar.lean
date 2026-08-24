/-
F1 square — **the regular and far improper parts of the archimedean tail** (`WeilArchTailFar.lean`):

  `ArchRegPart(f,g) = ∫₁^∞ N(x)·(1/max(x+1,2)) dx`      (the `1/(x+1)` half of the split kernel)
  `ArchFarPart(f,g) = ∫₁^∞ N(u+1)·(1/max(u,1)) du`      (`= ∫₂^∞ N(x)/(x−1) dx`, the far half)

both CONSTRUCTED as `improperIntegral1`s with the decay hypotheses PROVED — the maintainer's
"retain and evaluate the nonzero tail": past the support bound the numerator is exactly the retained
`−2F(1)·(1/max(x,1))` (`archNum_past`), so the blocks decay like `2M_F/((m+1)(m+2))`, and the
finitely many earlier blocks are width·sup bounded.  The decay constant is the computed rational
`K = M_int·Bd.num² + 2·M_F` (early + late envelopes summed).  NO truncation of the subtraction tail:
the improper integrals genuinely sum every block of `−2F(1)/x·kernel` to infinity.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilArchNum

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) Generalized early-block envelope (the `poleK_early` calc, parameterized by the bound `M`).
-- ===========================================================================

/-- Width·sup fits under `(M·Bd²)/((m+1)m)` for early blocks `m+1 < Bd`. -/
theorem K_early_general (G : ClosedGeom) (M : Q) (hMn : 0 ≤ M.num) (m : Nat) (hm : 1 ≤ m)
    (hlt : Qlt (⟨(m : Int) + 1, 1⟩ : Q) G.Bd) :
    Qle (mul (⟨1, 1⟩ : Q) M)
        (mul (mul M (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q)) := by
  -- m+1 ≤ Bd.num
  have hmBd : (m : Int) + 1 ≤ G.Bd.num := by
    have h := hlt
    simp only [Qlt] at h
    push_cast at h
    have hden1 : (1 : Int) ≤ (G.Bd.den : Int) := by
      have := G.hBdd
      omega
    have h1 : ((m : Int) + 1) * 1 ≤ ((m : Int) + 1) * (G.Bd.den : Int) :=
      Int.mul_le_mul_of_nonneg_left hden1 (by omega)
    omega
  have hkey : ((m : Int) + 1) * (m : Int) ≤ G.Bd.num * G.Bd.num := by
    have hm1 : (m : Int) ≤ (m : Int) + 1 := by omega
    have hm0 : (0 : Int) ≤ (m : Int) := Int.ofNat_nonneg m
    have hBd0 : (0 : Int) ≤ G.Bd.num :=
      Int.le_of_lt (qnum_pos_of_one_le G.hBdd G.hBd1)
    exact Int.mul_le_mul hmBd (Int.le_trans hm1 hmBd) hm0 hBd0
  show (mul (⟨1, 1⟩ : Q) M).num *
      ((mul (mul M (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q)).den : Int)
    ≤ (mul (mul M (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)) (⟨1, (m + 1) * m⟩ : Q)).num *
      ((mul (⟨1, 1⟩ : Q) M).den : Int)
  show (1 * M.num) * (((M.den * 1) * ((m + 1) * m) : Nat) : Int)
    ≤ ((M.num * (G.Bd.num * G.Bd.num)) * 1) * (((1 * M.den : Nat)) : Int)
  calc (1 * M.num) * (((M.den * 1) * ((m + 1) * m) : Nat) : Int)
      = (M.num * (M.den : Int)) * (((m : Int) + 1) * (m : Int)) := by push_cast; ring_uor
    _ ≤ (M.num * (M.den : Int)) * (G.Bd.num * G.Bd.num) :=
      Int.mul_le_mul_of_nonneg_left hkey (Int.mul_nonneg hMn (Int.ofNat_nonneg _))
    _ = ((M.num * (G.Bd.num * G.Bd.num)) * 1) * (((1 * M.den : Nat)) : Int) := by
        push_cast; ring_uor

-- ===========================================================================
-- (1) The two integrands, their decay constants, and the late-block product bounds.
-- ===========================================================================

/-- The regular-part integrand `N(x)·(1/max(x+1,2))`. -/
def archRegIntegrand (G : ClosedGeom) (f g : L2Test) : L2Test :=
  productTest (archNum G f g) archKernReg

/-- The far-part integrand `N(u+1)·(1/max(u,1))`. -/
def archFarIntegrand (G : ClosedGeom) (f g : L2Test) : L2Test :=
  productTest (archShiftNum G f g) (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide))

/-- The late-block bound `K_l = 2·M_F` (the retained tail's coefficient). -/
def archKl (G : ClosedGeom) (f g : L2Test) : Q := mul (⟨2, 1⟩ : Q) (FTestG G f g).M

theorem archKl_den (G : ClosedGeom) (f g : L2Test) : 0 < (archKl G f g).den :=
  Qmul_den_pos (by decide) (FTestG G f g).hMd

theorem archKl_num (G : ClosedGeom) (f g : L2Test) : 0 ≤ (archKl G f g).num :=
  Int.mul_nonneg (by show (0 : Int) ≤ 2; decide) (FTestG G f g).hMn

/-- The decay constant of an arch integrand: `K = M_int·Bd.num² + K_l` (early + late envelopes). -/
def archK (G : ClosedGeom) (f g : L2Test) (Mint : Q) : Q :=
  add (mul Mint (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)) (archKl G f g)

theorem archK_den (G : ClosedGeom) (f g : L2Test) (Mint : Q) (hMd : 0 < Mint.den) :
    0 < (archK G f g Mint).den :=
  add_den_pos (Qmul_den_pos hMd Nat.one_pos) (archKl_den G f g)

theorem archK_num (G : ClosedGeom) (f g : L2Test) (Mint : Q) (hMn : 0 ≤ Mint.num)
    (hMd : 0 < Mint.den) : 0 ≤ (archK G f g Mint).num := by
  have hBdn : 0 < G.Bd.num := qnum_pos_of_one_le G.hBdd G.hBd1
  have h1 : 0 ≤ (mul Mint (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)).num :=
    Int.mul_nonneg hMn (Int.mul_nonneg (Int.le_of_lt hBdn) (Int.le_of_lt hBdn))
  have h2 := archKl_num G f g
  show 0 ≤ (mul Mint (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)).num * ((archKl G f g).den : Int)
      + (archKl G f g).num * ((mul Mint (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)).den : Int)
  exact Int.add_nonneg (Int.mul_nonneg h1 (Int.ofNat_nonneg _))
    (Int.mul_nonneg h2 (Int.ofNat_nonneg _))

/-- The early-block envelope for `archK` (monotone extension of `K_early_general`). -/
theorem archK_early (G : ClosedGeom) (f g : L2Test) (Mint : Q) (hMn : 0 ≤ Mint.num)
    (hMd : 0 < Mint.den) (m : Nat) (hm : 1 ≤ m)
    (hlt : Qlt (⟨(m : Int) + 1, 1⟩ : Q) G.Bd) :
    Qle (mul (⟨1, 1⟩ : Q) Mint) (mul (archK G f g Mint) (⟨1, (m + 1) * m⟩ : Q)) := by
  refine Qle_trans (Qmul_den_pos (Qmul_den_pos hMd Nat.one_pos)
    (digamma_succ_mul_pos hm)) (K_early_general G Mint hMn m hm hlt) ?_
  exact Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide)
    (Qle_self_add (archKl_num G f g))

/-- The late-block envelope: `K_l/((m+1)(m+2)) ≤ archK/((m+1)m)`. -/
theorem archK_late (G : ClosedGeom) (f g : L2Test) (Mint : Q) (hMn : 0 ≤ Mint.num)
    (hMd : 0 < Mint.den) (m : Nat) (hm : 1 ≤ m) :
    Qle (mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q))
        (mul (archK G f g Mint) (⟨1, (m + 1) * m⟩ : Q)) := by
  have hKln := archKl_num G f g
  -- step 1: K_l/((m+1)(m+2)) ≤ K_l/((m+1)m)
  have hstep1 : Qle (mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q))
      (mul (archKl G f g) (⟨1, (m + 1) * m⟩ : Q)) := by
    show (mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q)).num *
        ((mul (archKl G f g) (⟨1, (m + 1) * m⟩ : Q)).den : Int)
      ≤ (mul (archKl G f g) (⟨1, (m + 1) * m⟩ : Q)).num *
        ((mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q)).den : Int)
    show ((archKl G f g).num * 1) * (((archKl G f g).den * ((m + 1) * m) : Nat) : Int)
      ≤ ((archKl G f g).num * 1) * (((archKl G f g).den * ((m + 1) * (m + 2)) : Nat) : Int)
    have hinner : ((m : Int) + 1) * (m : Int) ≤ ((m : Int) + 1) * ((m : Int) + 2) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    calc ((archKl G f g).num * 1) * (((archKl G f g).den * ((m + 1) * m) : Nat) : Int)
        = ((archKl G f g).num * ((archKl G f g).den : Int)) * (((m : Int) + 1) * (m : Int)) := by
          push_cast; ring_uor
      _ ≤ ((archKl G f g).num * ((archKl G f g).den : Int)) * (((m : Int) + 1) * ((m : Int) + 2)) :=
          Int.mul_le_mul_of_nonneg_left hinner
            (Int.mul_nonneg hKln (Int.ofNat_nonneg _))
      _ = ((archKl G f g).num * 1) * (((archKl G f g).den * ((m + 1) * (m + 2)) : Nat) : Int) := by
          push_cast; ring_uor
  -- step 2: K_l/((m+1)m) ≤ (K_e + K_l)/((m+1)m)
  refine Qle_trans (Qmul_den_pos (archKl_den G f g) (digamma_succ_mul_pos hm)) hstep1 ?_
  refine Qmul_le_mul_right (by show (0 : Int) ≤ 1; decide) ?_
  have hBdn : 0 < G.Bd.num := qnum_pos_of_one_le G.hBdd G.hBd1
  exact Qle_self_add_l (Int.mul_nonneg hMn
    (Int.mul_nonneg (Int.le_of_lt hBdn) (Int.le_of_lt hBdn)))

-- ===========================================================================
-- (2) The window-point machinery: every block sample sits above its left endpoint.
-- ===========================================================================

/-- The window points of block `m` dominate `m+1`. -/
theorem blockPoint_ge (m : Nat) (t : Real) (ht0 : Rle zero t) :
    Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos)
        (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) t) :=
  Rle_self_Radd_right (Rnonneg_Rmul (Rnonneg_ofQ (by decide) (by show (0 : Int) ≤ 1; decide))
    (Rnonneg_of_Rle_zero ht0))

/-- `ofQ ⟨m+2,1⟩ ≤ x + 1` for window points `x ≥ m+1`. -/
theorem blockPoint_succ_ge (m : Nat) (x : Real)
    (hx : Rle (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) x) :
    Rle (ofQ (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos) (Radd x one) := by
  have hsplit : Req (ofQ (⟨(m : Int) + 2, 1⟩ : Q) Nat.one_pos)
      (Radd (ofQ (⟨(m : Int) + 1, 1⟩ : Q) Nat.one_pos) one) := by
    refine Req_symm (Req_trans (Radd_ofQ_ofQ Nat.one_pos (by decide))
      (ofQ_congr (add_den_pos Nat.one_pos (by decide)) Nat.one_pos ?_))
    simp only [Qeq, add]; push_cast; ring_uor
  exact Rle_trans (Rle_of_Req hsplit) (Radd_le_add hx (Rle_refl one))

-- ===========================================================================
-- (3) The late-block pointwise bounds (past the support bound, the retained tail decays).
-- ===========================================================================

/-- The retained-tail numerator bound at real `x ≥ c ≥ Bd` (arbitrary rational threshold `c`):
    `|N(x)| ≤ K_l·(1/c)`. -/
theorem archNum_late_bound (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g)
    (c : Q) (hcn : 0 < c.num) (hcd : 0 < c.den)
    (x : Real) (hx : Rle (ofQ c hcd) x) (hpast : Qle G.Bd c) :
    Rle (Rabs ((archNum G f g).f x))
        (Rmul (ofQ (archKl G f g) (archKl_den G f g))
              (ofQ (Qinv c) (Qinv_den_pos hcn))) := by
  have hxBd : Rle (ofQ G.Bd G.hBdd) x :=
    Rle_trans (Rle_ofQ_ofQ G.hBdd hcd hpast) hx
  -- N(x) ≈ −(2F1·recip x)
  have hN := archNum_past G f g hf hg x hxBd
  have hrecip_nn : Rnonneg (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x) :=
    Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x
  have habs : Req (Rabs ((archNum G f g).f x))
      (Rmul (Rabs (Rmul (ofQ (⟨2, 1⟩ : Q) (by decide)) ((FTestG G f g).f one)))
            (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)) := by
    refine Req_trans (Rabs_congr hN) ?_
    refine Req_trans (Rabs_Rneg _) ?_
    refine Req_trans (Rabs_Rmul _ _) ?_
    exact Rmul_congr (Req_refl _) (Rabs_of_nonneg hrecip_nn)
  refine Rle_trans (Rle_of_Req habs) ?_
  exact Rmul_le_Rmul_both (Rnonneg_Rabs _)
    (Rnonneg_ofQ (Qinv_den_pos hcn) (Int.le_of_lt (Qinv_num_pos hcd)))
    (twoFone_bound G f g)
    (clampedInv_le_ofQ_inv_of_ge (by decide) (by decide) hcn hcd hx)

-- ===========================================================================
-- (4) The proved block decay of the two integrands.
-- ===========================================================================

/-- **THE REGULAR PART'S BLOCK DECAY**: every unit block of `N(x)·(1/max(x+1,2))` obeys the two-sided
    `archK/((m+1)m)` envelope — width·sup before the support bound, the retained-tail product bound
    `K_l/((m+1)(m+2))` past it.  NO vanishing is claimed past the bound: the tail is RETAINED. -/
theorem archRegDecay (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul (archK G f g (archRegIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archK_den G f g _ (archRegIntegrand G f g).hMd)
              (digamma_succ_mul_pos hm))))
          (integralTerm (archRegIntegrand G f g).hLd (archRegIntegrand G f g).hLn
            (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc m)
      ∧ Rle (integralTerm (archRegIntegrand G f g).hLd (archRegIntegrand G f g).hLn
            (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc m)
          (ofQ (mul (archK G f g (archRegIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archK_den G f g _ (archRegIntegrand G f g).hMd)
              (digamma_succ_mul_pos hm))) := by
  intro m hm
  have hm1n : (0 : Int) < (m : Int) + 1 := by omega
  have hm2n : (0 : Int) < (m : Int) + 2 := by omega
  have habs : Rle (Rabs (integralTerm (archRegIntegrand G f g).hLd (archRegIntegrand G f g).hLn
        (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc m))
      (ofQ (mul (archK G f g (archRegIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (archK_den G f g _ (archRegIntegrand G f g).hMd)
          (digamma_succ_mul_pos hm))) := by
    rcases Qle_or_Qlt G.Bd (⟨(m : Int) + 1, 1⟩ : Q) with hpast | hearly
    · -- LATE: the retained-tail product bound
      have hBLd : 0 < (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q)))
          (Qinv (⟨(m : Int) + 2, 1⟩ : Q))).den :=
        Qmul_den_pos (Qmul_den_pos (archKl_den G f g) (Qinv_den_pos hm1n)) (Qinv_den_pos hm2n)
      refine Rle_trans (riemannIntegralI_abs_le_window (archRegIntegrand G f g).hLd
        (archRegIntegrand G f g).hLn (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
        (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q))) (Qinv (⟨(m : Int) + 2, 1⟩ : Q)))
        Nat.one_pos (by decide) (by decide) hBLd ?_) ?_
      · -- the pointwise late bound at every window point
        intro t ht0 _
        have hxlo := blockPoint_ge m t ht0
        have hNb := archNum_late_bound G f g hf hg (⟨(m : Int) + 1, 1⟩ : Q) hm1n Nat.one_pos
          _ hxlo hpast
        have hkb : Rle (Rabs (archKernReg.f
              (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) t)))
            (ofQ (Qinv (⟨(m : Int) + 2, 1⟩ : Q)) (Qinv_den_pos hm2n)) := by
          refine Rle_trans (Rle_of_Req (Rabs_of_nonneg
            (Rnonneg_clampedInv (⟨2, 1⟩ : Q) (by decide) (by decide) _))) ?_
          exact clampedInv_le_ofQ_inv_of_ge (by decide) (by decide) hm2n Nat.one_pos
            (blockPoint_succ_ge m _ hxlo)
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
          (Rnonneg_ofQ (Qinv_den_pos hm2n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
          hNb hkb) ?_
        refine Rle_of_Req (Req_trans (Rmul_congr
          (Rmul_ofQ_ofQ (archKl_den G f g) (Qinv_den_pos hm1n)) (Req_refl _)) ?_)
        exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den G f g) (Qinv_den_pos hm1n))
          (Qinv_den_pos hm2n)
      · -- the rational envelope comparison
        refine Rle_ofQ_ofQ (Qmul_den_pos (by decide) hBLd)
          (Qmul_den_pos (archK_den G f g _ (archRegIntegrand G f g).hMd)
            (digamma_succ_mul_pos hm)) ?_
        have heq : Qeq (mul (⟨1, 1⟩ : Q)
              (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 1, 1⟩ : Q)))
                (Qinv (⟨(m : Int) + 2, 1⟩ : Q))))
            (mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q)) := by
          simp only [Qeq, mul, Qinv]
          push_cast [Int.toNat_of_nonneg (Int.le_of_lt hm1n),
            Int.toNat_of_nonneg (Int.le_of_lt hm2n)]
          ring_uor
        exact Qle_trans (Qmul_den_pos (archKl_den G f g)
            (Nat.mul_pos (Nat.succ_pos m) (show 0 < m + 2 by omega)))
          (Qeq_le heq)
          (archK_late G f g (archRegIntegrand G f g).M
            (archRegIntegrand G f g).hMn (archRegIntegrand G f g).hMd m hm)
    · -- EARLY: width·sup under the computed K
      refine Rle_trans (riemannIntegralI_abs_le_window (archRegIntegrand G f g).hLd
        (archRegIntegrand G f g).hLn (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (archRegIntegrand G f g).M
        Nat.one_pos (by decide) (by decide) (archRegIntegrand G f g).hMd
        (fun t _ _ => (archRegIntegrand G f g).hbd _)) ?_
      exact Rle_ofQ_ofQ (Qmul_den_pos (by decide) (archRegIntegrand G f g).hMd)
        (Qmul_den_pos (archK_den G f g _ (archRegIntegrand G f g).hMd)
          (digamma_succ_mul_pos hm))
        (archK_early G f g (archRegIntegrand G f g).M (archRegIntegrand G f g).hMn
          (archRegIntegrand G f g).hMd m hm hearly)
  refine ⟨Rneg_le_of_Rabs_le habs, Rle_of_Rabs_le habs⟩

/-- **THE FAR PART'S BLOCK DECAY** (same envelope; the shifted numerator is bounded at threshold
    `m+2`, the reciprocal factor at `m+1`). -/
theorem archFarDecay (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul (archK G f g (archFarIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archK_den G f g _ (archFarIntegrand G f g).hMd)
              (digamma_succ_mul_pos hm))))
          (integralTerm (archFarIntegrand G f g).hLd (archFarIntegrand G f g).hLn
            (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc m)
      ∧ Rle (integralTerm (archFarIntegrand G f g).hLd (archFarIntegrand G f g).hLn
            (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc m)
          (ofQ (mul (archK G f g (archFarIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (archK_den G f g _ (archFarIntegrand G f g).hMd)
              (digamma_succ_mul_pos hm))) := by
  intro m hm
  have hm1n : (0 : Int) < (m : Int) + 1 := by omega
  have hm2n : (0 : Int) < (m : Int) + 2 := by omega
  have habs : Rle (Rabs (integralTerm (archFarIntegrand G f g).hLd (archFarIntegrand G f g).hLn
        (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc m))
      (ofQ (mul (archK G f g (archFarIntegrand G f g).M) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (archK_den G f g _ (archFarIntegrand G f g).hMd)
          (digamma_succ_mul_pos hm))) := by
    rcases Qle_or_Qlt G.Bd (⟨(m : Int) + 1, 1⟩ : Q) with hpast | hearly
    · -- LATE
      have hpast2 : Qle G.Bd (⟨(m : Int) + 2, 1⟩ : Q) := by
        refine Qle_trans Nat.one_pos hpast ?_
        show ((m : Int) + 1) * ((1 : Nat) : Int) ≤ ((m : Int) + 2) * ((1 : Nat) : Int)
        push_cast; omega
      have hBLd : 0 < (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 2, 1⟩ : Q)))
          (Qinv (⟨(m : Int) + 1, 1⟩ : Q))).den :=
        Qmul_den_pos (Qmul_den_pos (archKl_den G f g) (Qinv_den_pos hm2n)) (Qinv_den_pos hm1n)
      refine Rle_trans (riemannIntegralI_abs_le_window (archFarIntegrand G f g).hLd
        (archFarIntegrand G f g).hLn (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q)
        (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 2, 1⟩ : Q))) (Qinv (⟨(m : Int) + 1, 1⟩ : Q)))
        Nat.one_pos (by decide) (by decide) hBLd ?_) ?_
      · intro t ht0 _
        have hxlo := blockPoint_ge m t ht0
        have hNb := archNum_late_bound G f g hf hg (⟨(m : Int) + 2, 1⟩ : Q) hm2n Nat.one_pos
          _ (blockPoint_succ_ge m _ hxlo) hpast2
        have hkb : Rle (Rabs ((recipTest (⟨1, 1⟩ : Q) (by decide) (by decide)).f
              (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) t)))
            (ofQ (Qinv (⟨(m : Int) + 1, 1⟩ : Q)) (Qinv_den_pos hm1n)) := by
          refine Rle_trans (Rle_of_Req (Rabs_of_nonneg
            (Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) _))) ?_
          exact clampedInv_le_ofQ_inv_of_ge (by decide) (by decide) hm1n Nat.one_pos hxlo
        refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
        refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _)
          (Rnonneg_ofQ (Qinv_den_pos hm1n) (Int.le_of_lt (Qinv_num_pos Nat.one_pos)))
          hNb hkb) ?_
        refine Rle_of_Req (Req_trans (Rmul_congr
          (Rmul_ofQ_ofQ (archKl_den G f g) (Qinv_den_pos hm2n)) (Req_refl _)) ?_)
        exact Rmul_ofQ_ofQ (Qmul_den_pos (archKl_den G f g) (Qinv_den_pos hm2n))
          (Qinv_den_pos hm1n)
      · refine Rle_ofQ_ofQ (Qmul_den_pos (by decide) hBLd)
          (Qmul_den_pos (archK_den G f g _ (archFarIntegrand G f g).hMd)
            (digamma_succ_mul_pos hm)) ?_
        have heq : Qeq (mul (⟨1, 1⟩ : Q)
              (mul (mul (archKl G f g) (Qinv (⟨(m : Int) + 2, 1⟩ : Q)))
                (Qinv (⟨(m : Int) + 1, 1⟩ : Q))))
            (mul (archKl G f g) (⟨1, (m + 1) * (m + 2)⟩ : Q)) := by
          simp only [Qeq, mul, Qinv]
          push_cast [Int.toNat_of_nonneg (Int.le_of_lt hm1n),
            Int.toNat_of_nonneg (Int.le_of_lt hm2n)]
          ring_uor
        exact Qle_trans (Qmul_den_pos (archKl_den G f g)
            (Nat.mul_pos (Nat.succ_pos m) (show 0 < m + 2 by omega)))
          (Qeq_le heq)
          (archK_late G f g (archFarIntegrand G f g).M
            (archFarIntegrand G f g).hMn (archFarIntegrand G f g).hMd m hm)
    · -- EARLY
      refine Rle_trans (riemannIntegralI_abs_le_window (archFarIntegrand G f g).hLd
        (archFarIntegrand G f g).hLn (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (archFarIntegrand G f g).M
        Nat.one_pos (by decide) (by decide) (archFarIntegrand G f g).hMd
        (fun t _ _ => (archFarIntegrand G f g).hbd _)) ?_
      exact Rle_ofQ_ofQ (Qmul_den_pos (by decide) (archFarIntegrand G f g).hMd)
        (Qmul_den_pos (archK_den G f g _ (archFarIntegrand G f g).hMd)
          (digamma_succ_mul_pos hm))
        (archK_early G f g (archFarIntegrand G f g).M (archFarIntegrand G f g).hMn
          (archFarIntegrand G f g).hMd m hm hearly)
  refine ⟨Rneg_le_of_Rabs_le habs, Rle_of_Rabs_le habs⟩

-- ===========================================================================
-- (5) The constructed improper parts.
-- ===========================================================================

/-- **The regular part** `∫₁^∞ N(x)·(1/max(x+1,2)) dx` — CONSTRUCTED, decay proved. -/
def ArchRegPart (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  improperIntegral1 (archRegIntegrand G f g).hLd (archRegIntegrand G f g).hLn
    (archRegIntegrand G f g).hlip (archRegIntegrand G f g).hfc
    (archK_den G f g _ (archRegIntegrand G f g).hMd)
    (archK_num G f g _ (archRegIntegrand G f g).hMn (archRegIntegrand G f g).hMd)
    (archRegDecay G f g hf hg)

/-- **The far part** `∫₁^∞ N(u+1)·(1/max(u,1)) du = ∫₂^∞ N(x)/(x−1) dx` — CONSTRUCTED, decay
    proved, the `−2F(1)/x`-tail RETAINED in every block. -/
def ArchFarPart (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  improperIntegral1 (archFarIntegrand G f g).hLd (archFarIntegrand G f g).hLn
    (archFarIntegrand G f g).hlip (archFarIntegrand G f g).hfc
    (archK_den G f g _ (archFarIntegrand G f g).hMd)
    (archK_num G f g _ (archFarIntegrand G f g).hMn (archFarIntegrand G f g).hMd)
    (archFarDecay G f g hf hg)

-- Seal the deep definitional towers (elaborator whnf economy; in-file defeq uses are above).
attribute [irreducible] archRegIntegrand archFarIntegrand archK archKl ArchRegPart ArchFarPart

end UOR.Bridge.F1Square.Square
