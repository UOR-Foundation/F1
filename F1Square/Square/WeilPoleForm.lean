/-
F1 square — **the genuine two-input pole form** `PoleForm(f,g) = ∫₁^∞ (F_{f,g}+F_{g,f})(1+x⁻¹) dx`
(`WeilPoleForm.lean`) — a CONSTRUCTED improper integral (`improperIntegral1`), not a parameter.

`f̃(1)+f̃(0) = ∫₀^∞ F(x)dx + ∫₀^∞ F(x)dx/x` folds to `[1,∞)` through the reciprocal self-duality
`F(1/x) = x·F^t(x)`: substituting `x ↦ 1/x` on `(0,1]` turns each Mellin pole integral into its
mirrored piece, and the sum of all four pieces is `∫₁^∞ (F_{f,g}(x)+F_{g,f}(x))·(1+1/x) dx` — the
two-input pole form.  Here it is BUILT as a certified `improperIntegral1` of the bundled integrand
`(FTest f g + FTest g f)·(1 + 1/max(x,1))` (all clamps inert on `[1,∞)`), with the decay hypothesis
DISCHARGED from the compact support of the cross-correlation: blocks past the support bound `Bd`
vanish identically (`FTest_high_vanish` at the rational block samples), and the finitely many earlier
blocks are bounded by width·sup (`riemannIntegralI_abs_le_window`) under a computed rational `K`.

THE TYPED DOMAIN (the maintainer's "typed-domain bridge", folded in here):
  • `ClosedGeom` — ONE fixed nondegenerate geometry: window `[a, a+w]`, scale band `[0,S]`, weight
    band `[1,B]` with scale witness `N`, support bound `Bd` with the closure `a+w ≤ Bd·a` and the
    adequacy `Bd ≤ S`, `Bd ≤ B` — chosen INDEPENDENTLY of any tested vector.
  • `CoreTest G f` — `f` compactly supported in `[G.b, 1/G.a]` RELATIVE to the fixed geometry.
  • `FTestG G f g` — the normalized cross-correlation over `G`.

`PoleForm_symm` (two-input symmetry) and `PoleForm_add_left/right` (biadditivity) are proved by
termwise integrand congruence/addition lifted through `genSum` and the Bishop limit.

NO free `Real` parameters, NO assumed convergence (the decay is proved), NO PSD, NO RH input.
Pure Lean 4 core, no Mathlib, choice-free.
-/

import F1Square.Square.WeilCrossF
import F1Square.Analysis.ImproperIntegral

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) The fixed closed geometry and the supported-test predicate.
-- ===========================================================================

/-- **The fixed closed geometry** — every band, bound, and witness of the closed Weil form, chosen
    once and independently of any tested vector. -/
structure ClosedGeom where
  /-- the scale band cap `S` of the real-scale convolution -/
  S : Q
  hSd : 0 < S.den
  hSn : 0 ≤ S.num
  hS1 : Qle (⟨1, 1⟩ : Q) S
  /-- the Haar window floor `a > 0` (window `[a, a+w]`) -/
  a : Q
  han : 0 < a.num
  had : 0 < a.den
  /-- the Haar window width `w ≥ 0` -/
  w : Q
  hw : 0 < w.den
  hwn : 0 ≤ w.num
  /-- the low support edge `b > 0` -/
  b : Q
  hbd : 0 < b.den
  hbn : 0 < b.num
  /-- support fit: `1/b ≤ a+w` -/
  hfit : Qle (Qinv b) (add a w)
  /-- the weight band cap `B ≥ 1` -/
  B : Q
  hBd : 0 < B.den
  hB1 : Qle (⟨1, 1⟩ : Q) B
  /-- the weight scale witness `N ≥ B` -/
  N : Nat
  hN : 0 < N
  hBN : Qle B (⟨(N : Int), 1⟩ : Q)
  /-- the support bound `Bd ≥ 1` -/
  Bd : Q
  hBdd : 0 < Bd.den
  hBd1 : Qle (⟨1, 1⟩ : Q) Bd
  /-- support closure: the window sits below the support bound, `a+w ≤ Bd·a` -/
  hband : Qle (add a w) (mul Bd a)
  /-- cutoff adequacy: the support bound is inside the scale band -/
  hBdS : Qle Bd S
  /-- cutoff adequacy: the support bound is inside the weight band -/
  hBdB : Qle Bd B

/-- **A core test for the fixed geometry**: compactly supported inside `[G.b, 1/G.a]` — the
    admissibility of a tested vector RELATIVE to `G` (never the reverse). -/
structure CoreTest (G : ClosedGeom) (f : L2Test) : Prop where
  hgh : ∀ y, Rle (ofQ (Qinv G.a) (Qinv_den_pos G.han)) y → Req (f.f y) zero
  hgl : ∀ y, Rle y (ofQ G.b G.hbd) → Req (f.f y) zero

/-- Core tests are closed under `L2Test.add`. -/
theorem coreTest_add {G : ClosedGeom} {f₁ f₂ : L2Test}
    (h₁ : CoreTest G f₁) (h₂ : CoreTest G f₂) : CoreTest G (L2Test.add f₁ f₂) where
  hgh := fun y hy => Req_trans (Radd_congr (h₁.hgh y hy) (h₂.hgh y hy)) (Radd_zero zero)
  hgl := fun y hy => Req_trans (Radd_congr (h₁.hgl y hy) (h₂.hgl y hy)) (Radd_zero zero)

/-- `Bd ≥ 0` (from `Bd ≥ 1`). -/
theorem closedGeom_Bd0 (G : ClosedGeom) : Qle (⟨0, 1⟩ : Q) G.Bd := by
  have h := G.hBd1
  simp only [Qle] at *
  push_cast at *
  omega

/-- The normalized cross-correlation over the fixed geometry. -/
def FTestG (G : ClosedGeom) (f g : L2Test) : L2Test :=
  FTest G.B G.hBd G.hB1 G.N G.hN G.hBN f g G.S G.hSd G.hSn G.a G.han G.had G.w G.hw G.hwn

/-- `F_{f,g}` over `G` vanishes at every real `x ≥ Bd` (needs only `f`'s high support). -/
theorem FTestG_high_vanish (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f)
    (x : Real) (hx : Rle (ofQ G.Bd G.hBdd) x) :
    Req ((FTestG G f g).f x) zero :=
  FTest_high_vanish G.B G.hBd G.hB1 G.N G.hN G.hBN f g G.S G.hSd G.hSn G.a G.han G.had
    G.w G.hw G.hwn G.Bd G.hBdd (closedGeom_Bd0 G) G.hBdS G.hband hf.hgh x hx

-- ===========================================================================
-- (1) The pole integrand `(F_{f,g}+F_{g,f})·(1+1/x)`, bundled.
-- ===========================================================================

/-- The pole density `1 + 1/max(x,1)` (`= 1 + 1/x` on `[1,∞)`), as an `L2Test`. -/
def poleDens : L2Test :=
  L2Test.add oneTest (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide))

/-- **The pole integrand** `(F_{f,g}(x)+F_{g,f}(x))·(1+1/max(x,1))`, an `L2Test`. -/
def poleIntegrand (G : ClosedGeom) (f g : L2Test) : L2Test :=
  productTest (L2Test.add (FTestG G f g) (FTestG G g f)) poleDens

/-- The pole integrand vanishes at every real `x ≥ Bd` (both cross-correlations vanish). -/
theorem poleIntegrand_high_vanish (G : ClosedGeom) (f g : L2Test)
    (hf : CoreTest G f) (hg : CoreTest G g)
    (x : Real) (hx : Rle (ofQ G.Bd G.hBdd) x) :
    Req ((poleIntegrand G f g).f x) zero := by
  show Req (Rmul (Radd ((FTestG G f g).f x) ((FTestG G g f).f x)) (poleDens.f x)) zero
  refine Req_trans (Rmul_congr
    (Req_trans (Radd_congr (FTestG_high_vanish G f g hf x hx)
      (FTestG_high_vanish G g f hg x hx)) (Radd_zero zero)) (Req_refl _)) ?_
  exact Req_trans (Rmul_comm zero _) (Rmul_zero _)

-- ===========================================================================
-- (2) The block-decay bound for the improper integral.
-- ===========================================================================

/-- The decay constant `K = M·Bd.num²` of the pole integrand (`M` its global bound). -/
def poleK (G : ClosedGeom) (f g : L2Test) : Q :=
  mul (poleIntegrand G f g).M (⟨G.Bd.num * G.Bd.num, 1⟩ : Q)

theorem poleK_den (G : ClosedGeom) (f g : L2Test) : 0 < (poleK G f g).den :=
  Qmul_den_pos (poleIntegrand G f g).hMd Nat.one_pos

theorem poleK_num (G : ClosedGeom) (f g : L2Test) : 0 ≤ (poleK G f g).num := by
  have hBdn : 0 < G.Bd.num := qnum_pos_of_one_le G.hBdd G.hBd1
  exact Int.mul_nonneg (poleIntegrand G f g).hMn
    (Int.mul_nonneg (Int.le_of_lt hBdn) (Int.le_of_lt hBdn))

/-- `Qle (mul ⟨1,1⟩ M) (mul K ⟨1,(m+1)*m⟩)` for the early blocks `m+1 < Bd` — the width·sup bound
    fits under the decay envelope because `(m+1)·m ≤ Bd.num²`. -/
theorem poleK_early (G : ClosedGeom) (f g : L2Test) (m : Nat) (hm : 1 ≤ m)
    (hlt : Qlt (⟨((m + 1 : Nat) : Int), 1⟩ : Q) G.Bd) :
    Qle (mul (⟨1, 1⟩ : Q) (poleIntegrand G f g).M)
        (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q)) := by
  have hMn := (poleIntegrand G f g).hMn
  -- m+1 ≤ Bd.num
  have hmBd : (m : Int) + 1 ≤ G.Bd.num := by
    have h := hlt
    simp only [Qlt] at h
    push_cast at h
    -- h : (↑m + 1) * ↑Bd.den < Bd.num * 1
    have hden1 : (1 : Int) ≤ (G.Bd.den : Int) := by
      have := G.hBdd
      omega
    have h1 : ((m : Int) + 1) * 1 ≤ ((m : Int) + 1) * (G.Bd.den : Int) :=
      Int.mul_le_mul_of_nonneg_left hden1 (by omega)
    omega
  -- (m+1)·m ≤ Bd.num²
  have hkey : ((m : Int) + 1) * (m : Int) ≤ G.Bd.num * G.Bd.num := by
    have hm1 : (m : Int) ≤ (m : Int) + 1 := by omega
    have hm0 : (0 : Int) ≤ (m : Int) := Int.ofNat_nonneg m
    have hBd0 : (0 : Int) ≤ G.Bd.num :=
      Int.le_of_lt (qnum_pos_of_one_le G.hBdd G.hBd1)
    exact Int.mul_le_mul hmBd (Int.le_trans hm1 hmBd) hm0 hBd0
  -- cross-multiplied comparison, ring-normalized through a calc
  show (mul (⟨1, 1⟩ : Q) (poleIntegrand G f g).M).num *
      ((mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q)).den : Int)
    ≤ (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q)).num *
      ((mul (⟨1, 1⟩ : Q) (poleIntegrand G f g).M).den : Int)
  show (1 * (poleIntegrand G f g).M.num) *
      ((((poleIntegrand G f g).M.den * 1) * ((m + 1) * m) : Nat) : Int)
    ≤ (((poleIntegrand G f g).M.num * (G.Bd.num * G.Bd.num)) * 1) *
      (((1 * (poleIntegrand G f g).M.den : Nat)) : Int)
  calc (1 * (poleIntegrand G f g).M.num) *
      ((((poleIntegrand G f g).M.den * 1) * ((m + 1) * m) : Nat) : Int)
      = ((poleIntegrand G f g).M.num * ((poleIntegrand G f g).M.den : Int)) *
        (((m : Int) + 1) * (m : Int)) := by push_cast; ring_uor
    _ ≤ ((poleIntegrand G f g).M.num * ((poleIntegrand G f g).M.den : Int)) *
        (G.Bd.num * G.Bd.num) :=
      Int.mul_le_mul_of_nonneg_left hkey (Int.mul_nonneg hMn (Int.ofNat_nonneg _))
    _ = (((poleIntegrand G f g).M.num * (G.Bd.num * G.Bd.num)) * 1) *
        (((1 * (poleIntegrand G f g).M.den : Nat)) : Int) := by push_cast; ring_uor

/-- **THE BLOCK-DECAY BOUND**: every unit block `T m = ∫_{m+1}^{m+2}` of the pole integrand obeys the
    two-sided `K/((m+1)m)` envelope — vanishing past the support bound, width·sup before it. -/
theorem poleDecay (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) :
    ∀ m, ∀ hm : 1 ≤ m,
      Rle (Rneg (ofQ (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (poleK_den G f g) (digamma_succ_mul_pos hm))))
          (integralTerm (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
            (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc m)
      ∧ Rle (integralTerm (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
            (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc m)
          (ofQ (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q))
            (Qmul_den_pos (poleK_den G f g) (digamma_succ_mul_pos hm))) := by
  intro m hm
  have hKterm_nn : Rnonneg (ofQ (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q))
      (Qmul_den_pos (poleK_den G f g) (digamma_succ_mul_pos hm))) :=
    Rnonneg_ofQ _ (Int.mul_nonneg (poleK_num G f g) (by show (0 : Int) ≤ 1; decide))
  -- the uniform |T m| ≤ K/((m+1)m) bound, split by the support boundary
  have habs : Rle (Rabs (integralTerm (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
        (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc m))
      (ofQ (mul (poleK G f g) (⟨1, (m + 1) * m⟩ : Q))
        (Qmul_den_pos (poleK_den G f g) (digamma_succ_mul_pos hm))) := by
    rcases Qle_or_Qlt G.Bd (⟨((m + 1 : Nat) : Int), 1⟩ : Q) with hpast | hearly
    · -- past the support: the block vanishes identically
      have hzero : Req (integralTerm (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
          (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc m) zero := by
        refine riemannIntegralI_pts_zero (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
          (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc
          (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide) (by decide) ?_
        intro M i hi
        -- the sample is a rational ≥ m+1 ≥ Bd
        have hqid : (0 : Nat) < M + 1 := Nat.succ_pos M
        have hmul_nn : (0 : Int) ≤ (mul (⟨1, 1⟩ : Q) (⟨(i : Int), M + 1⟩ : Q)).num := by
          show (0 : Int) ≤ 1 * (i : Int)
          exact Int.mul_nonneg (by decide) (Int.ofNat_nonneg i)
        have hqpd : 0 < (add (⟨(m : Int) + 1, 1⟩ : Q) (mul (⟨1, 1⟩ : Q) (⟨(i : Int), M + 1⟩ : Q))).den :=
          add_den_pos Nat.one_pos (Qmul_den_pos (by decide) hqid)
        have step1 : Req (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide)
              (ofQ (⟨(i : Int), M + 1⟩ : Q) hqid))
            (ofQ (add (⟨(m : Int) + 1, 1⟩ : Q) (mul (⟨1, 1⟩ : Q) (⟨(i : Int), M + 1⟩ : Q))) hqpd) :=
          Req_trans (Radd_congr (Req_refl _) (Rmul_ofQ_ofQ (by decide) hqid))
            (Radd_ofQ_ofQ Nat.one_pos (Qmul_den_pos (by decide) hqid))
        have hBdq : Qle G.Bd (add (⟨(m : Int) + 1, 1⟩ : Q) (mul (⟨1, 1⟩ : Q) (⟨(i : Int), M + 1⟩ : Q))) :=
          Qle_trans Nat.one_pos hpast (Qle_self_add hmul_nn)
        have hxge : Rle (ofQ G.Bd G.hBdd)
            (affineMap (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) Nat.one_pos (by decide)
              (ofQ (⟨(i : Int), M + 1⟩ : Q) hqid)) :=
          Rle_trans (Rle_ofQ_ofQ G.hBdd hqpd hBdq) (Rle_of_Req (Req_symm step1))
        exact poleIntegrand_high_vanish G f g hf hg _ hxge
      refine Rle_trans (Rle_of_Req (Req_trans (Rabs_congr hzero) Rabs_zero)) ?_
      exact Rle_zero_of_Rnonneg hKterm_nn
    · -- before the support bound: width·sup, then the early-K comparison
      refine Rle_trans (riemannIntegralI_abs_le_window (poleIntegrand G f g).hLd
        (poleIntegrand G f g).hLn (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc
        (⟨(m : Int) + 1, 1⟩ : Q) (⟨1, 1⟩ : Q) (poleIntegrand G f g).M Nat.one_pos (by decide)
        (by decide) (poleIntegrand G f g).hMd
        (fun x _ _ => (poleIntegrand G f g).hbd _)) ?_
      exact Rle_ofQ_ofQ (Qmul_den_pos (by decide) (poleIntegrand G f g).hMd)
        (Qmul_den_pos (poleK_den G f g) (digamma_succ_mul_pos hm))
        (poleK_early G f g m hm hearly)
  exact ⟨Rneg_le_of_Rabs_le habs, Rle_of_Rabs_le habs⟩

-- ===========================================================================
-- (3) The pole form, its symmetry, and its biadditivity.
-- ===========================================================================

/-- **★ THE GENUINE TWO-INPUT POLE FORM** `PoleForm(f,g) = ∫₁^∞ (F_{f,g}+F_{g,f})(1+1/x) dx` — a
    CONSTRUCTED `improperIntegral1` with the decay DISCHARGED from compact support.  No free `Real`. -/
def PoleForm (G : ClosedGeom) (f g : L2Test) (hf : CoreTest G f) (hg : CoreTest G g) : Real :=
  improperIntegral1 (poleIntegrand G f g).hLd (poleIntegrand G f g).hLn
    (poleIntegrand G f g).hlip (poleIntegrand G f g).hfc
    (poleK_den G f g) (poleK_num G f g) (poleDecay G f g hf hg)

end UOR.Bridge.F1Square.Square
