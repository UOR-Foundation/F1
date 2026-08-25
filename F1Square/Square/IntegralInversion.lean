/-
F1 square — **INVERSION UNDER THE CERTIFIED INTEGRAL** (`IntegralInversion.lean`):

    `∫_{1/B}^{1} φ(x) dx = ∫_{1}^{B} φ(1/y)·y⁻² dy`     (`riemannIntegralI_inversion`)

for every `L2Test` φ and rational `B > 1` — the nonlinear change of variables `x = 1/y` that the
certified (uniform-refinement) integral does not know natively.  PROVED, not assumed: both sides
are compared with the SAME rational sum along the partition `y_i = 1 + i·h` of `[1,B]` and its
inverse image `x_i = 1/y_i` of `[1/B, 1]` (`IntegralInversionGeom`), cell by cell:
  • `cell_est_left` on each `y`-cell (uniform width `h`) and each `x`-cell (width `v_i ≤ h`),
  • the readback `ψ(y_i) = φ(x_i)·x_i²` (the reciprocal is `clampedInv 1`, inert on `y ≥ 1`),
  • the KEY identity `x_i − x_{i+1} = h·x_i·x_{i+1}`, so `h·x_i² − v_i = h·x_i·v_i ∈ [0, h²]`,
  • Lipschitz swap `φ(x_i) → φ(x_{i+1})`,
giving `|ψ-cell − φ-cell| ≤ h²·E`, summed over `N+1` cells: `≤ (B−1)²E/(N+1) → 0`.
Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.IntegralInversionGeom

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) The pulled-back test `ψ(y) = φ(1/y)·(1/y)²`.
-- ===========================================================================

/-- `φ ∘ (1/·)` (reciprocal `clampedInv 1`, inert on `y ≥ 1`), an `L2Test` with φ's own certificates. -/
def recipCompTest (φ : L2Test) : L2Test where
  f := fun x => φ.f (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
  L := φ.L
  M := φ.M
  hLd := φ.hLd
  hLn := φ.hLn
  hMd := φ.hMd
  hMn := φ.hMn
  hlip := Hcross_recip_lip φ
  hfc := fun _ _ h => φ.hfc _ _ (clampedInv_congr _ _ _ h)
  hbd := fun _ => φ.hbd _

/-- `(1/y)²`. -/
def invSqTest : L2Test :=
  productTest (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide))
    (recipTest (⟨1, 1⟩ : Q) (by decide) (by decide))

/-- **The pulled-back test** `ψ = φ(1/y)·(1/y)²`. -/
def invPullTest (φ : L2Test) : L2Test := productTest (recipCompTest φ) invSqTest

theorem invPullTest_f (φ : L2Test) (x : Real) :
    (invPullTest φ).f x
      = Rmul (φ.f (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x))
          (Rmul (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)
                (clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) x)) := rfl

/-- Rational readback `ψ(q) = φ(1/q)·(1/q)²` for `q ≥ 1`. -/
theorem invPullTest_ofQ (φ : L2Test) (q : Q) (hqd : 0 < q.den) (hqn : 0 < q.num)
    (hq1 : Qle (⟨1, 1⟩ : Q) q) :
    Req ((invPullTest φ).f (ofQ q hqd))
        (Rmul (φ.f (ofQ (Qinv q) (Qinv_den_pos hqn)))
          (Rmul (ofQ (Qinv q) (Qinv_den_pos hqn)) (ofQ (Qinv q) (Qinv_den_pos hqn)))) := by
  rw [invPullTest_f]
  have hc := clampedInv_ofQ (a := (⟨1, 1⟩ : Q)) (by decide) (by decide) hqd hqn hq1
  exact Rmul_congr (φ.hfc _ _ hc) (Rmul_congr hc hc)

-- ===========================================================================
-- (2) The rational cell coefficient `c_i = h·x_i² − v_i = h·x_i·v_i ∈ [0, h²]`.
-- ===========================================================================

/-- `v_i = x_i − x_{i+1}`. -/
def invV (B : Q) (N i : Nat) : Q := Qsub (invX B N i) (invX B N (i + 1))

/-- `c_i = h·x_i² − v_i`. -/
def invC (B : Q) (N i : Nat) : Q :=
  Qsub (mul (invH B N) (mul (invX B N i) (invX B N i))) (invV B N i)

/-- Pure ring identity `h·x·x − h·x·x' = h·x·(x − x')`. -/
theorem hxx_sub_id (h x x' : Q) :
    Qeq (Qsub (mul h (mul x x)) (mul h (mul x x'))) (mul h (mul x (Qsub x x'))) := by
  simp only [Qeq, Qsub, add, neg, mul]
  push_cast
  generalize h.num = hn
  generalize ((h.den : Nat) : Int) = hd
  generalize x.num = xn
  generalize ((x.den : Nat) : Int) = xd
  generalize x'.num = yn
  generalize ((x'.den : Nat) : Int) = yd
  ring_uor

/-- **`c_i = h·x_i·v_i`** (from the key identity `v_i = h·x_i·x_{i+1}`). -/
theorem invC_eq (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Qeq (invC B N i) (mul (invH B N) (mul (invX B N i) (invV B N i))) := by
  have hhd := invH_den B hBd N
  have hxd := invX_den B hBd hB1 N i
  have hxd' := invX_den B hBd hB1 N (i + 1)
  refine Qeq_trans (Qsub_den_pos (Qmul_den_pos hhd (Qmul_den_pos hxd hxd))
      (Qmul_den_pos hhd (Qmul_den_pos hxd hxd')))
    (Qsub_congr (Qeq_refl _) (invX_sub_eq B hBd hB1 N i)) ?_
  exact hxx_sub_id (invH B N) (invX B N i) (invX B N (i + 1))

theorem invV_den (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    0 < (invV B N i).den :=
  Qsub_den_pos (invX_den B hBd hB1 N i) (invX_den B hBd hB1 N (i + 1))

theorem invV_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    0 ≤ (invV B N i).num := invX_sub_nonneg B hBd hB1 N i

theorem invV_le_h (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Qle (invV B N i) (invH B N) := invX_sub_le_h B hBd hB1 N i

theorem invC_den (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    0 < (invC B N i).den :=
  Qsub_den_pos (Qmul_den_pos (invH_den B hBd N)
    (Qmul_den_pos (invX_den B hBd hB1 N i) (invX_den B hBd hB1 N i))) (invV_den B hBd hB1 N i)

/-- `0 ≤ h·x_i·v_i`. -/
theorem invC_rep_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    0 ≤ (mul (invH B N) (mul (invX B N i) (invV B N i))).num :=
  Int.mul_nonneg (Int.le_of_lt (invH_num B hB1 N))
    (Int.mul_nonneg (Int.le_of_lt (invX_num B hBd N i)) (invV_nonneg B hBd hB1 N i))

/-- `h·x_i·v_i ≤ h·h`. -/
theorem invC_rep_le (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Qle (mul (invH B N) (mul (invX B N i) (invV B N i))) (mul (invH B N) (invH B N)) := by
  have hhd := invH_den B hBd N
  have hvd := invV_den B hBd hB1 N i
  refine Qmul_le_mul_left (Int.le_of_lt (invH_num B hB1 N)) ?_
  -- x·v ≤ 1·v = v ≤ h
  refine Qle_trans (Qmul_den_pos Nat.one_pos hvd)
    (Qmul_le_mul_right (invV_nonneg B hBd hB1 N i) (invX_le_one B hBd hB1 N i)) ?_
  exact Qle_trans hvd (Qeq_le (Qone_mul _)) (invV_le_h B hBd hB1 N i)

-- ===========================================================================
-- (3) Real abbreviations for the partition data.
-- ===========================================================================

def hR (B : Q) (hBd : 0 < B.den) (N : Nat) : Real := ofQ (invH B N) (invH_den B hBd N)
def yR (B : Q) (hBd : 0 < B.den) (N i : Nat) : Real := ofQ (invY B N i) (invY_den B hBd N i)
def xR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) : Real :=
  ofQ (invX B N i) (invX_den B hBd hB1 N i)
def vR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) : Real :=
  ofQ (invV B N i) (invV_den B hBd hB1 N i)

/-- The `ψ`-cell `∫_{[y_i, y_{i+1}]} ψ`. -/
def psiCell (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) : Real :=
  riemannIntegralI (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
    (invY B N i) (Qsub (invY B N (i + 1)) (invY B N i)) (invY_den B hBd N i)
    (Qsub_den_pos (invY_den B hBd N (i + 1)) (invY_den B hBd N i))
    (Qsub_num_nonneg (Qle_of_Qlt_loc (invY_step_lt B hBd hB1 N i)))

/-- The `φ`-cell `∫_{[x_{i+1}, x_i]} φ`. -/
def phiCell (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) : Real :=
  riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc (invX B N (i + 1)) (invV B N i)
    (invX_den B hBd hB1 N (i + 1)) (invV_den B hBd hB1 N i) (invV_nonneg B hBd hB1 N i)

theorem hR_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Rnonneg (hR B hBd N) := Rnonneg_ofQ _ (Int.le_of_lt (invH_num B hB1 N))

theorem xR_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rnonneg (xR B hBd hB1 N i) := Rnonneg_ofQ _ (Int.le_of_lt (invX_num B hBd N i))

theorem xR_le_one (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (xR B hBd hB1 N i) one := Rle_ofQ_ofQ _ (by decide) (invX_le_one B hBd hB1 N i)

theorem vR_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rnonneg (vR B hBd hB1 N i) := Rnonneg_ofQ _ (invV_nonneg B hBd hB1 N i)

theorem vR_le_hR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (vR B hBd hB1 N i) (hR B hBd N) := Rle_ofQ_ofQ _ _ (invV_le_h B hBd hB1 N i)

/-- `x_i − x_{i+1} = v_i` as reals. -/
theorem xR_sub (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Req (Rsub (xR B hBd hB1 N i) (xR B hBd hB1 N (i + 1))) (vR B hBd hB1 N i) :=
  Rsub_ofQ_ofQ _ _

-- ===========================================================================
-- (4) The three per-cell bounds.
-- ===========================================================================

/-- **T1**: `|ψ-cell − h·ψ(y_i)| ≤ h·(L_ψ·h)`. -/
theorem cell_T1 (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (Rabs (Rsub (psiCell φ B hBd hB1 N i)
                    (Rmul (hR B hBd N) ((invPullTest φ).f (yR B hBd N i)))))
        (Rmul (hR B hBd N) (Rmul (ofQ (invPullTest φ).L (invPullTest φ).hLd) (hR B hBd N))) := by
  have hw : Req (ofQ (Qsub (invY B N (i + 1)) (invY B N i))
      (Qsub_den_pos (invY_den B hBd N (i + 1)) (invY_den B hBd N i))) (hR B hBd N) :=
    ofQ_congr _ _ (invY_step_sub B N i)
  have hce := cell_est_left (invPullTest φ) (invY B N i) (Qsub (invY B N (i + 1)) (invY B N i))
    (invY_den B hBd N i) (Qsub_den_pos (invY_den B hBd N (i + 1)) (invY_den B hBd N i))
    (Qsub_num_nonneg (Qle_of_Qlt_loc (invY_step_lt B hBd hB1 N i)))
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_refl _)
    (Rmul_congr (Req_symm hw) (Req_refl _))))) ?_
  refine Rle_trans hce ?_
  exact Rle_of_Req (Rmul_congr hw (Rmul_congr (Req_refl _) hw))

/-- **T3**: `|v_i·φ(x_{i+1}) − φ-cell| ≤ h·(L_φ·h)`. -/
theorem cell_T3 (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (Rabs (Rsub (Rmul (vR B hBd hB1 N i) (φ.f (xR B hBd hB1 N (i + 1))))
                    (phiCell φ B hBd hB1 N i)))
        (Rmul (hR B hBd N) (Rmul (ofQ φ.L φ.hLd) (hR B hBd N))) := by
  refine Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) ?_
  refine Rle_trans (cell_est_left φ (invX B N (i + 1)) (invV B N i)
    (invX_den B hBd hB1 N (i + 1)) (invV_den B hBd hB1 N i) (invV_nonneg B hBd hB1 N i)) ?_
  exact Rmul_le_Rmul_both (vR_nonneg B hBd hB1 N i)
    (Rnonneg_Rmul (Rnonneg_ofQ φ.hLd φ.hLn) (hR_nonneg B hBd hB1 N))
    (vR_le_hR B hBd hB1 N i)
    (Rmul_le_Rmul_left (Rnonneg_ofQ φ.hLd φ.hLn) (vR_le_hR B hBd hB1 N i))

/-- The real prefactor `P_i = h·x_i²`. -/
def pR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) : Real :=
  Rmul (hR B hBd N) (Rmul (xR B hBd hB1 N i) (xR B hBd hB1 N i))

theorem pR_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rnonneg (pR B hBd hB1 N i) :=
  Rnonneg_Rmul (hR_nonneg B hBd hB1 N) (Rnonneg_Rmul (xR_nonneg B hBd hB1 N i) (xR_nonneg B hBd hB1 N i))

theorem pR_le_hR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (pR B hBd hB1 N i) (hR B hBd N) := by
  have hxx : Rle (Rmul (xR B hBd hB1 N i) (xR B hBd hB1 N i)) one :=
    Rle_trans (Rmul_le_Rmul_both (xR_nonneg B hBd hB1 N i) (Rnonneg_ofQ (by decide) (by decide))
      (xR_le_one B hBd hB1 N i) (xR_le_one B hBd hB1 N i)) (Rle_of_Req (Rone_mul one))
  exact Rle_trans (Rmul_le_Rmul_left (hR_nonneg B hBd hB1 N) hxx) (Rle_of_Req (Rmul_one _))

/-- `h·ψ(y_i) = P_i·φ(x_i)`. -/
theorem hpsi_eq (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Req (Rmul (hR B hBd N) ((invPullTest φ).f (yR B hBd N i)))
        (Rmul (pR B hBd hB1 N i) (φ.f (xR B hBd hB1 N i))) := by
  have hrb := invPullTest_ofQ φ (invY B N i) (invY_den B hBd N i) (invY_num B hBd hB1 N i)
    (invY_ge_one B hBd hB1 N i)
  refine Req_trans (Rmul_congr (Req_refl _) hrb) ?_
  -- h·(F·XX) = (h·XX)·F
  refine Req_trans (Rmul_congr (Req_refl _) (Rmul_comm _ _)) ?_
  exact Req_symm (Rmul_assoc _ _ _)

/-- `P_i − v_i = ofQ c_i`. -/
theorem pR_sub_vR (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Req (Rsub (pR B hBd hB1 N i) (vR B hBd hB1 N i)) (ofQ (invC B N i) (invC_den B hBd hB1 N i)) := by
  have hp : Req (pR B hBd hB1 N i)
      (ofQ (mul (invH B N) (mul (invX B N i) (invX B N i)))
        (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos (invX_den B hBd hB1 N i) (invX_den B hBd hB1 N i)))) :=
    Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _)
  refine Req_trans (Rsub_congr hp (Req_refl _)) ?_
  exact Rsub_ofQ_ofQ _ _

/-- `|P_i − v_i| ≤ h·h`. -/
theorem pR_sub_vR_abs_le (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (Rabs (Rsub (pR B hBd hB1 N i) (vR B hBd hB1 N i))) (Rmul (hR B hBd N) (hR B hBd N)) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (pR_sub_vR B hBd hB1 N i))) ?_
  have hrep : Req (ofQ (invC B N i) (invC_den B hBd hB1 N i))
      (ofQ (mul (invH B N) (mul (invX B N i) (invV B N i)))
        (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos (invX_den B hBd hB1 N i) (invV_den B hBd hB1 N i)))) :=
    ofQ_congr _ _ (invC_eq B hBd hB1 N i)
  refine Rle_trans (Rle_of_Req (Rabs_congr hrep)) ?_
  refine Rle_trans (Rle_of_Req (Rabs_ofQ_nonneg _ (invC_rep_nonneg B hBd hB1 N i))) ?_
  refine Rle_trans (Rle_ofQ_ofQ _ (Qmul_den_pos (invH_den B hBd N) (invH_den B hBd N))
    (invC_rep_le B hBd hB1 N i)) ?_
  exact Rle_of_Req (Req_symm (Rmul_ofQ_ofQ _ _))

/-- **T2**: `|h·ψ(y_i) − v_i·φ(x_{i+1})| ≤ h·(L_φ·h) + M_φ·(h·h)`. -/
theorem cell_T2 (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (Rabs (Rsub (Rmul (hR B hBd N) ((invPullTest φ).f (yR B hBd N i)))
                    (Rmul (vR B hBd hB1 N i) (φ.f (xR B hBd hB1 N (i + 1))))))
        (Radd (Rmul (hR B hBd N) (Rmul (ofQ φ.L φ.hLd) (hR B hBd N)))
              (Rmul (ofQ φ.M φ.hMd) (Rmul (hR B hBd N) (hR B hBd N)))) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (hpsi_eq φ B hBd hB1 N i) (Req_refl _)))) ?_
  refine Rle_trans (Rabs_sub_tri _ (Rmul (pR B hBd hB1 N i) (φ.f (xR B hBd hB1 N (i + 1)))) _) ?_
  refine Radd_le_add ?_ ?_
  · -- P·F − P·F' = P·(F − F'); |·| ≤ P·(L·|x − x'|) ≤ h·(L·h)
    refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib _ _ _)))) ?_
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rle_of_Req (Rmul_congr (Rabs_of_nonneg (pR_nonneg B hBd hB1 N i)) (Req_refl _))) ?_
    refine Rmul_le_Rmul_both (pR_nonneg B hBd hB1 N i)
      (Rnonneg_Rmul (Rnonneg_ofQ φ.hLd φ.hLn) (hR_nonneg B hBd hB1 N)) (pR_le_hR B hBd hB1 N i) ?_
    refine Rle_trans (φ.hlip _ _) ?_
    refine Rmul_le_Rmul_left (Rnonneg_ofQ φ.hLd φ.hLn) ?_
    refine Rle_trans (Rle_of_Req (Rabs_congr (xR_sub B hBd hB1 N i))) ?_
    refine Rle_trans (Rle_of_Req (Rabs_ofQ_nonneg _ (invV_nonneg B hBd hB1 N i))) ?_
    exact vR_le_hR B hBd hB1 N i
  · -- P·F' − v·F' = (P − v)·F'; |·| ≤ |P − v|·M ≤ (h·h)·M
    refine Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rmul_sub_distrib_right _ _ _)))) ?_
    refine Rle_trans (Rle_of_Req (Rabs_Rmul _ _)) ?_
    refine Rle_trans (Rmul_le_Rmul_both (Rnonneg_Rabs _) (Rnonneg_ofQ φ.hMd φ.hMn)
      (pR_sub_vR_abs_le B hBd hB1 N i) (φ.hbd _)) ?_
    exact Rle_of_Req (Rmul_comm _ _)


-- ===========================================================================
-- (5) The per-cell total `|ψ-cell − φ-cell| ≤ h·h·E`.
-- ===========================================================================

/-- The cell constant `E = L_ψ + L_φ + M_φ + L_φ`. -/
def invE (φ : L2Test) : Q :=
  add (invPullTest φ).L (add φ.L (add φ.M φ.L))

theorem invE_den (φ : L2Test) : 0 < (invE φ).den :=
  add_den_pos (invPullTest φ).hLd (add_den_pos φ.hLd (add_den_pos φ.hMd φ.hLd))

theorem invE_num (φ : L2Test) : 0 ≤ (invE φ).num :=
  Qadd_num_nonneg_loc (invPullTest φ).hLn
    (Qadd_num_nonneg_loc φ.hLn (Qadd_num_nonneg_loc φ.hMn φ.hLn))

/-- The literal sum of the three cell bounds, as a rational. -/
def cellBoundQ (φ : L2Test) (B : Q) (N : Nat) : Q :=
  add (mul (invH B N) (mul (invPullTest φ).L (invH B N)))
    (add (add (mul (invH B N) (mul φ.L (invH B N))) (mul φ.M (mul (invH B N) (invH B N))))
         (mul (invH B N) (mul φ.L (invH B N))))

/-- `cellBoundQ = h·h·E` (ring identity). -/
theorem cellBoundQ_eq (φ : L2Test) (B : Q) (N : Nat) :
    Qeq (cellBoundQ φ B N) (mul (invH B N) (mul (invH B N) (invE φ))) := by
  simp only [cellBoundQ, invE, Qeq, add, mul]
  push_cast
  generalize (invH B N).num = hn
  generalize (((invH B N).den : Nat) : Int) = hd
  generalize (invPullTest φ).L.num = an
  generalize (((invPullTest φ).L.den : Nat) : Int) = ad
  generalize φ.L.num = ln
  generalize ((φ.L.den : Nat) : Int) = ld
  generalize φ.M.num = mn
  generalize ((φ.M.den : Nat) : Int) = md
  ring_uor

/-- The real bound sum equals `ofQ cellBoundQ`. -/
theorem cellBound_real (φ : L2Test) (B : Q) (hBd : 0 < B.den) (N : Nat) :
    Req (Radd (Rmul (hR B hBd N) (Rmul (ofQ (invPullTest φ).L (invPullTest φ).hLd) (hR B hBd N)))
          (Radd (Radd (Rmul (hR B hBd N) (Rmul (ofQ φ.L φ.hLd) (hR B hBd N)))
                      (Rmul (ofQ φ.M φ.hMd) (Rmul (hR B hBd N) (hR B hBd N))))
                (Rmul (hR B hBd N) (Rmul (ofQ φ.L φ.hLd) (hR B hBd N)))))
        (ofQ (cellBoundQ φ B N) (add_den_pos (Qmul_den_pos (invH_den B hBd N)
          (Qmul_den_pos (invPullTest φ).hLd (invH_den B hBd N)))
          (add_den_pos (add_den_pos (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos φ.hLd (invH_den B hBd N)))
            (Qmul_den_pos φ.hMd (Qmul_den_pos (invH_den B hBd N) (invH_den B hBd N))))
            (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos φ.hLd (invH_den B hBd N)))))) := by
  have t1 : Req (Rmul (hR B hBd N) (Rmul (ofQ (invPullTest φ).L (invPullTest φ).hLd) (hR B hBd N)))
      (ofQ (mul (invH B N) (mul (invPullTest φ).L (invH B N))) _) :=
    Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _)
  have t2 : Req (Rmul (hR B hBd N) (Rmul (ofQ φ.L φ.hLd) (hR B hBd N)))
      (ofQ (mul (invH B N) (mul φ.L (invH B N))) _) :=
    Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _)
  have t3 : Req (Rmul (ofQ φ.M φ.hMd) (Rmul (hR B hBd N) (hR B hBd N)))
      (ofQ (mul φ.M (mul (invH B N) (invH B N))) _) :=
    Req_trans (Rmul_congr (Req_refl _) (Rmul_ofQ_ofQ _ _)) (Rmul_ofQ_ofQ _ _)
  refine Req_trans (Radd_congr t1 (Radd_congr (Radd_congr t2 t3) t2)) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_congr (Radd_ofQ_ofQ _ _) (Req_refl _))) ?_
  refine Req_trans (Radd_congr (Req_refl _) (Radd_ofQ_ofQ _ _)) ?_
  exact Radd_ofQ_ofQ _ _

/-- **THE PER-CELL TOTAL** `|ψ-cell − φ-cell| ≤ h·h·E`. -/
theorem cell_total (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N i : Nat) :
    Rle (Rabs (Rsub (psiCell φ B hBd hB1 N i) (phiCell φ B hBd hB1 N i)))
        (ofQ (mul (invH B N) (mul (invH B N) (invE φ)))
          (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos (invH_den B hBd N) (invE_den φ)))) := by
  refine Rle_trans (Rabs_sub_tri _ (Rmul (hR B hBd N) ((invPullTest φ).f (yR B hBd N i))) _) ?_
  refine Rle_trans (Radd_le_add (cell_T1 φ B hBd hB1 N i)
    (Rabs_sub_tri _ (Rmul (vR B hBd hB1 N i) (φ.f (xR B hBd hB1 N (i + 1)))) _)) ?_
  refine Rle_trans (Radd_le_add (Rle_refl _)
    (Radd_le_add (cell_T2 φ B hBd hB1 N i) (cell_T3 φ B hBd hB1 N i))) ?_
  refine Rle_trans (Rle_of_Req (cellBound_real φ B hBd N)) ?_
  exact Rle_of_Req (ofQ_congr _ _ (cellBoundQ_eq φ B N))


-- ===========================================================================
-- (6) Sums over the cells and the window splits.
-- ===========================================================================

def psiSum (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) : Real :=
  genSum (fun i => psiCell φ B hBd hB1 N i) (N + 1)

def phiSum (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) : Real :=
  genSum (fun i => phiCell φ B hBd hB1 N i) (N + 1)

/-- `∫_{[y_0, y_{N+1}]} ψ = Σ ψ-cells`. -/
theorem psi_window_split (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Req (riemannIntegralI (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
          (invY B N 0) (Qsub (invY B N (N + 1)) (invY B N 0)) (invY_den B hBd N 0)
          (Qsub_den_pos (invY_den B hBd N (N + 1)) (invY_den B hBd N 0))
          (Qsub_num_nonneg (Qle_of_Qlt_loc (invY_zero_lt B hBd hB1 N N))))
        (psiSum φ B hBd hB1 N) :=
  partition_split (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
    (invY B N) (invY_den B hBd N) (invY_zero_lt B hBd hB1 N)
    (fun i => Qle_of_Qlt_loc (invY_step_lt B hBd hB1 N i)) N

/-- `∫_{[x_{N+1}, x_0]} φ = Σ φ-cells`. -/
theorem phi_window_split (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Req (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc
          (invX B N (N + 1)) (Qsub (invX B N 0) (invX B N (N + 1))) (invX_den B hBd hB1 N (N + 1))
          (Qsub_den_pos (invX_den B hBd hB1 N 0) (invX_den B hBd hB1 N (N + 1)))
          (Qsub_num_nonneg (Qle_of_Qlt_loc (invX_zero_lt B hBd hB1 N N))))
        (phiSum φ B hBd hB1 N) :=
  partition_split_dec φ.hLd φ.hLn φ.hlip φ.hfc (invX B N) (invX_den B hBd hB1 N)
    (invX_zero_lt B hBd hB1 N) (invX_step_lt B hBd hB1 N) N

/-- `|Σψ − Σφ| ≤ (N+1)·(h·h·E)`. -/
theorem sum_diff_le (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Rle (Rabs (Rsub (psiSum φ B hBd hB1 N) (phiSum φ B hBd hB1 N)))
        (ofQ (mul (⟨((N + 1 : Nat) : Int), 1⟩ : Q) (mul (invH B N) (mul (invH B N) (invE φ))))
          (Qmul_den_pos Nat.one_pos
            (Qmul_den_pos (invH_den B hBd N) (Qmul_den_pos (invH_den B hBd N) (invE_den φ))))) := by
  refine Rle_trans (Rle_of_Req (Rabs_congr (genSum_Rsub_cells _ _ (N + 1)))) ?_
  refine Rle_trans (genSum_Rabs_le _ (N + 1)) ?_
  refine Rle_trans (genSum_le_const (fun i => cell_total φ B hBd hB1 N i) (N + 1)) ?_
  exact Rle_of_Req (Rmul_ofQ_ofQ _ _)

-- ===========================================================================
-- (7) The rational tail `(N+1)·h·h·E = (B−1)²E/(N+1) ≤ C/(N+1)`.
-- ===========================================================================

/-- The `N`-independent numerator `G = (B−1)·((B−1)·E)`. -/
def invG (φ : L2Test) (B : Q) : Q :=
  mul (Qsub B (⟨1, 1⟩ : Q)) (mul (Qsub B (⟨1, 1⟩ : Q)) (invE φ))

theorem invG_den (φ : L2Test) (B : Q) (hBd : 0 < B.den) : 0 < (invG φ B).den :=
  Qmul_den_pos (Qsub_den_pos hBd Nat.one_pos) (Qmul_den_pos (Qsub_den_pos hBd Nat.one_pos) (invE_den φ))

theorem invG_num (φ : L2Test) (B : Q) (hB1 : Qlt (⟨1, 1⟩ : Q) B) : 0 ≤ (invG φ B).num :=
  Int.mul_nonneg (Int.le_of_lt (Qsub_num_pos_of_lt hB1))
    (Int.mul_nonneg (Int.le_of_lt (Qsub_num_pos_of_lt hB1)) (invE_num φ))

/-- The limit constant `C = ⌊G⌋ + 1`. -/
def invCst (φ : L2Test) (B : Q) : Nat := (invG φ B).num.toNat + 1

/-- `(N+1)·(h·h·E) = G·(1/(N+1))` (ring identity, `h = (B−1)/(N+1)`). -/
theorem tail_eq (φ : L2Test) (B : Q) (N : Nat) :
    Qeq (mul (⟨((N + 1 : Nat) : Int), 1⟩ : Q) (mul (invH B N) (mul (invH B N) (invE φ))))
        (mul (invG φ B) (⟨1, N + 1⟩ : Q)) := by
  simp only [invG, invH, Qeq, mul, Qsub, add, neg]
  push_cast
  generalize B.num = bn
  generalize ((B.den : Nat) : Int) = bd
  generalize (invE φ).num = en
  generalize (((invE φ).den : Nat) : Int) = ed
  generalize ((N : Nat) : Int) = K
  ring_uor

/-- **THE TAIL BOUND** `(N+1)·(h·h·E) ≤ C/(N+1)`. -/
theorem tail_le (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Qle (mul (⟨((N + 1 : Nat) : Int), 1⟩ : Q) (mul (invH B N) (mul (invH B N) (invE φ))))
        (⟨((invCst φ B : Nat) : Int), N + 1⟩ : Q) := by
  refine Qle_trans (Qmul_den_pos (invG_den φ B hBd) (Nat.succ_pos N)) (Qeq_le (tail_eq φ B N)) ?_
  refine Qle_trans (Qmul_den_pos Nat.one_pos (Nat.succ_pos N))
    (Qmul_le_mul_right (show (0 : Int) ≤ 1 by decide)
      (Qle_num_cap (invG φ B) (invG_den φ B hBd) (invG_num φ B hB1))) ?_
  refine Qeq_le ?_
  show Qeq (mul (⟨(((invG φ B).num.toNat + 1 : Nat) : Int), 1⟩ : Q) (⟨1, N + 1⟩ : Q))
    (⟨(((invG φ B).num.toNat + 1 : Nat) : Int), N + 1⟩ : Q)
  simp only [Qeq, mul]
  push_cast
  ring_uor

-- ===========================================================================
-- (8) The window congruences and THE INVERSION THEOREM.
-- ===========================================================================

theorem B_num_pos (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) : 0 < B.num :=
  qnum_pos_of_one_le hBd (Qle_of_Qlt_loc hB1)

/-- `[y_0, y_{N+1}] = [1, B]`. -/
theorem psi_window_congr (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Req (riemannIntegralI (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
          (invY B N 0) (Qsub (invY B N (N + 1)) (invY B N 0)) (invY_den B hBd N 0)
          (Qsub_den_pos (invY_den B hBd N (N + 1)) (invY_den B hBd N 0))
          (Qsub_num_nonneg (Qle_of_Qlt_loc (invY_zero_lt B hBd hB1 N N))))
        (riemannIntegralI (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
          (⟨1, 1⟩ : Q) (Qsub B (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos hBd Nat.one_pos)
          (Int.le_of_lt (Qsub_num_pos_of_lt hB1))) :=
  riemannIntegralI_congr_Q _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Qeq_refl _) (Qsub_congr (invY_top B hBd N) (Qeq_refl _))

/-- `[x_{N+1}, x_0] = [1/B, 1]`. -/
theorem phi_window_congr (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (N : Nat) :
    Req (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc
          (invX B N (N + 1)) (Qsub (invX B N 0) (invX B N (N + 1))) (invX_den B hBd hB1 N (N + 1))
          (Qsub_den_pos (invX_den B hBd hB1 N 0) (invX_den B hBd hB1 N (N + 1)))
          (Qsub_num_nonneg (Qle_of_Qlt_loc (invX_zero_lt B hBd hB1 N N))))
        (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc
          (Qinv B) (Qsub (⟨1, 1⟩ : Q) (Qinv B)) (Qinv_den_pos (B_num_pos B hBd hB1))
          (Qsub_den_pos Nat.one_pos (Qinv_den_pos (B_num_pos B hBd hB1)))
          (Qsub_num_nonneg (qinv_le_one hBd (Qle_of_Qlt_loc hB1)))) :=
  riemannIntegralI_congr_Q _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (Qinv_congr (invY_num B hBd hB1 N (N + 1)) (B_num_pos B hBd hB1) (invY_top B hBd N))
    (Qsub_congr (invX_zero_eq B N)
      (Qinv_congr (invY_num B hBd hB1 N (N + 1)) (B_num_pos B hBd hB1) (invY_top B hBd N)))

/-- **★★ INVERSION UNDER THE CERTIFIED INTEGRAL**
    `∫_{1/B}^{1} φ(x) dx = ∫_{1}^{B} φ(1/y)·(1/y)² dy` for every `L2Test` φ and rational `B > 1`. -/
theorem riemannIntegralI_inversion (φ : L2Test) (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) :
    Req (riemannIntegralI φ.hLd φ.hLn φ.hlip φ.hfc
          (Qinv B) (Qsub (⟨1, 1⟩ : Q) (Qinv B)) (Qinv_den_pos (B_num_pos B hBd hB1))
          (Qsub_den_pos Nat.one_pos (Qinv_den_pos (B_num_pos B hBd hB1)))
          (Qsub_num_nonneg (qinv_le_one hBd (Qle_of_Qlt_loc hB1))))
        (riemannIntegralI (invPullTest φ).hLd (invPullTest φ).hLn (invPullTest φ).hlip (invPullTest φ).hfc
          (⟨1, 1⟩ : Q) (Qsub B (⟨1, 1⟩ : Q)) Nat.one_pos (Qsub_den_pos hBd Nat.one_pos)
          (Int.le_of_lt (Qsub_num_pos_of_lt hB1))) := by
  refine Req_of_Rabs_le_lin (invCst φ B) (fun N => ?_)
  have hphi := Req_trans (Req_symm (phi_window_congr φ B hBd hB1 N)) (phi_window_split φ B hBd hB1 N)
  have hpsi := Req_trans (Req_symm (psi_window_congr φ B hBd hB1 N)) (psi_window_split φ B hBd hB1 N)
  refine Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr hphi hpsi))) ?_
  refine Rle_trans (Rle_of_Req (Rabs_Rsub_symm _ _)) ?_
  refine Rle_trans (sum_diff_le φ B hBd hB1 N) ?_
  exact Rle_ofQ_ofQ _ _ (tail_le φ B hBd hB1 N)


end UOR.Bridge.F1Square.Square
