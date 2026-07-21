/-
F1 square — **the `∫ log/x` layer, part 1: the `log²` step bracket** (`LogSqStep.lean`).
The `t4` slot's `poleB` component is `∫ f(x)/x dx = 4(log 2)²`, whose antiderivative is
`log²x/2` — the mirror of `Gn(n) = n·log n − n` for the `∫log` layer. This file opens
the campaign with the antiderivative object and its unit-step bracket:

    `Hn(n) := (log n)²`,
    `(log i + log(i+1))/(i+1)  ≤  Hn(i+1) − Hn(i)  ≤  (log i + log(i+1))/i`

— pure algebra over the certified per-step log bracket (`ExpBounds`): the difference of
squares collapses (`Hn(i+1) − Hn(i) = (log(i+1) − log i)·(log(i+1) + log i)`,
`Rmul_sub_add_self`), the first factor is bracketed by `[1/(i+1), 1/i]`
(`logN_step_lower/upper`), and the second factor is nonneg (`Rnonneg_logN`). General in
`i` — the telescope over `i = c·2^m + j` (unbounded) consumes exactly this shape.

HONEST SCOPE. An antiderivative object and a step inequality; no integral is evaluated
and no positivity is claimed. The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.LogStep
import F1Square.Analysis.HarmonicLog32

namespace UOR.Bridge.F1Square.Analysis

/-- **The `∫ log/x` antiderivative at integer arguments**: `Hn(n) = (log n)²`
    (the exact value of `2·∫₁ⁿ log x/x dx`). -/
def Hn (n : Nat) (hn : 1 ≤ n) : Real := Rmul (logN n hn) (logN n hn)

/-- `Hn(1) ≈ 0` (`log 1 = 0`). -/
theorem Hn_one : Req (Hn 1 (by omega)) zero :=
  Req_trans (Rmul_congr logN_one (Req_refl _)) (Req_trans (Rmul_comm _ _) (Rmul_zero _))

/-- The difference of squares collapse:
    `Hn(i+1) − Hn(i) ≈ (log(i+1) − log i)·(log(i+1) + log i)`. -/
private theorem Hn_diff (i : Nat) (hi : 1 ≤ i) :
    Req (Rsub (Hn (i + 1) (by omega)) (Hn i hi))
      (Rmul (Rsub (logN (i + 1) (by omega)) (logN i hi))
        (Radd (logN (i + 1) (by omega)) (logN i hi))) :=
  Req_symm (Rmul_sub_add_self (logN (i + 1) (by omega)) (logN i hi))

/-- The step difference is bracketed below: `1/(i+1) ≤ log(i+1) − log i`. -/
private theorem logStep_diff_lower (i : Nat) (hi : 1 ≤ i) :
    Rle (ofQ (⟨1, i + 1⟩ : Q) (Nat.succ_pos i))
      (Rsub (logN (i + 1) (by omega)) (logN i hi)) :=
  Rle_Rsub_of_Radd_le (logN_step_lower i hi)

/-- The step difference is bracketed above: `log(i+1) − log i ≤ 1/i`. -/
private theorem logStep_diff_upper (i : Nat) (hi : 1 ≤ i) :
    Rle (Rsub (logN (i + 1) (by omega)) (logN i hi)) (ofQ (⟨1, i⟩ : Q) hi) :=
  Rsub_le_of_le_Radd
    (Rle_trans (logN_step_upper i hi) (Rle_of_Req (Radd_comm _ _)))

/-- The log sum factor is nonneg. -/
private theorem logsum_nonneg (i : Nat) (hi : 1 ≤ i) :
    Rnonneg (Radd (logN (i + 1) (by omega)) (logN i hi)) :=
  Rnonneg_Radd (Rnonneg_logN (i + 1) (by omega)) (Rnonneg_logN i hi)

/-- **The step bracket, lower side**:
    `(1/(i+1))·(log(i+1) + log i) ≤ Hn(i+1) − Hn(i)` — general in `i`. -/
theorem Hn_step_lower (i : Nat) (hi : 1 ≤ i) :
    Rle (Rmul (ofQ (⟨1, i + 1⟩ : Q) (Nat.succ_pos i))
        (Radd (logN (i + 1) (by omega)) (logN i hi)))
      (Rsub (Hn (i + 1) (by omega)) (Hn i hi)) :=
  Rle_trans (Rmul_le_Rmul_right (logsum_nonneg i hi) (logStep_diff_lower i hi))
    (Rle_of_Req (Req_symm (Hn_diff i hi)))

/-- **The step bracket, upper side**:
    `Hn(i+1) − Hn(i) ≤ (1/i)·(log(i+1) + log i)` — general in `i`. -/
theorem Hn_step_upper (i : Nat) (hi : 1 ≤ i) :
    Rle (Rsub (Hn (i + 1) (by omega)) (Hn i hi))
      (Rmul (ofQ (⟨1, i⟩ : Q) hi)
        (Radd (logN (i + 1) (by omega)) (logN i hi))) :=
  Rle_trans (Rle_of_Req (Hn_diff i hi))
    (Rmul_le_Rmul_right (logsum_nonneg i hi) (logStep_diff_upper i hi))


-- ===========================================================================
-- Part 2: the step-folds and the telescopes.
-- ===========================================================================

/-- `x − y ≤ c ⟹ x ≤ y + c` (private copy). -/
private theorem hs_le_Radd {x y c : Real} (h : Rle (Rsub x y) c) : Rle x (Radd y c) := by
  have h1 : Rle (Radd (Rsub x y) y) (Radd c y) := Radd_le_add h (Rle_refl y)
  have h2 : Req (Radd (Rsub x y) y) x :=
    Req_trans (Radd_assoc x (Rneg y) y)
      (Req_trans (Radd_congr (Req_refl x)
        (Req_trans (Radd_comm (Rneg y) y) (Radd_neg y))) (Radd_zero x))
  exact Rle_trans (Rle_of_Req (Req_symm h2)) (Rle_trans h1 (Rle_of_Req (Radd_comm c y)))

/-- The lower step-fold `Σ_{j<c} (log(A+j) + log(A+j+1))/(A+j+1)` — the summed lower
    sides of the `Hn` step bracket. -/
def hsFoldLo (A : Nat) (hA : 1 ≤ A) : Nat → Real
  | 0 => zero
  | (c + 1) => Radd (hsFoldLo A hA c)
      (Rmul (ofQ (⟨1, A + c + 1⟩ : Q) (Nat.succ_pos (A + c)))
        (Radd (logN (A + c + 1) (by omega)) (logN (A + c) (by omega))))

/-- The upper step-fold `Σ_{j<c} (log(A+j) + log(A+j+1))/(A+j)`. -/
def hsFoldHi (A : Nat) (hA : 1 ≤ A) : Nat → Real
  | 0 => zero
  | (c + 1) => Radd (hsFoldHi A hA c)
      (Rmul (ofQ (⟨1, A + c⟩ : Q) (show 0 < A + c by omega))
        (Radd (logN (A + c + 1) (by omega)) (logN (A + c) (by omega))))

/-- **The telescope, lower side**: `Hn(A) + Σ_{j<c} stepLo(A+j) ≤ Hn(A+c)` — general in
    the base and the count. -/
theorem Hn_tele_lower (A : Nat) (hA : 1 ≤ A) : ∀ c : Nat,
    Rle (Radd (Hn A hA) (hsFoldLo A hA c)) (Hn (A + c) (by omega)) := by
  intro c
  induction c with
  | zero => exact Rle_of_Req (Radd_zero (Hn A hA))
  | succ k ih =>
    show Rle (Radd (Hn A hA) (Radd (hsFoldLo A hA k)
        (Rmul (ofQ (⟨1, A + k + 1⟩ : Q) (Nat.succ_pos (A + k)))
          (Radd (logN (A + k + 1) (by omega)) (logN (A + k) (by omega))))))
      (Hn (A + k + 1) (by omega))
    refine Rle_trans (Rle_of_Req (Req_symm (Radd_assoc (Hn A hA) (hsFoldLo A hA k) _))) ?_
    refine Rle_trans (Radd_le_add ih (Rle_refl _)) ?_
    refine Rle_trans (Radd_le_add (Rle_refl (Hn (A + k) (by omega)))
      (Hn_step_lower (A + k) (by omega))) ?_
    exact Rle_of_Req (Radd_Rsub_cancel (Hn (A + k + 1) (by omega)) (Hn (A + k) (by omega)))

/-- **The telescope, upper side**: `Hn(A+c) ≤ Hn(A) + Σ_{j<c} stepHi(A+j)`. -/
theorem Hn_tele_upper (A : Nat) (hA : 1 ≤ A) : ∀ c : Nat,
    Rle (Hn (A + c) (by omega)) (Radd (Hn A hA) (hsFoldHi A hA c)) := by
  intro c
  induction c with
  | zero => exact Rle_of_Req (Req_symm (Radd_zero (Hn A hA)))
  | succ k ih =>
    show Rle (Hn (A + k + 1) (by omega))
      (Radd (Hn A hA) (Radd (hsFoldHi A hA k)
        (Rmul (ofQ (⟨1, A + k⟩ : Q) (show 0 < A + k by omega))
          (Radd (logN (A + k + 1) (by omega)) (logN (A + k) (by omega))))))
    refine Rle_trans (Rle_trans (hs_le_Radd (Hn_step_upper (A + k) (by omega)))
      (Radd_le_add ih (Rle_refl _))) ?_
    exact Rle_of_Req (Radd_assoc (Hn A hA) (hsFoldHi A hA k) _)


-- ===========================================================================
-- Part 3: the fold gap — crude `log ≤ n` suffices, the harmonic telescope pays.
-- ===========================================================================

/-- The rational gap fold `Σ_{j<c} 2(K+1)/((A+j)(A+j+1))`. -/
def gapQ (A K : Nat) : Nat → Q
  | 0 => ⟨0, 1⟩
  | (c + 1) => add (gapQ A K c)
      ⟨((2 * (K + 1) : Nat) : Int), (A + c) * (A + c + 1)⟩

theorem gapQ_den_pos (A K : Nat) (hA : 1 ≤ A) : ∀ c, 0 < (gapQ A K c).den
  | 0 => Nat.one_pos
  | (c + 1) => add_den_pos (gapQ_den_pos A K hA c)
      (Nat.mul_pos (show 0 < A + c by omega) (Nat.succ_pos (A + c)))

/-- The per-cell gap: `stepHi ≤ stepLo + 2(K+1)/((A+c)(A+c+1))` — the weight
    difference is the harmonic cell `1/((A+c)(A+c+1))`, and the log sum is crudely
    bounded by `2(K+1)` (`logN_le_self`). -/
private theorem hs_cell_gap (A c K : Nat) (hA : 1 ≤ A) (hcK : A + c ≤ K) :
    Rle (Rmul (ofQ (⟨1, A + c⟩ : Q) (show 0 < A + c by omega))
        (Radd (logN (A + c + 1) (by omega)) (logN (A + c) (by omega))))
      (Radd (Rmul (ofQ (⟨1, A + c + 1⟩ : Q) (Nat.succ_pos (A + c)))
          (Radd (logN (A + c + 1) (by omega)) (logN (A + c) (by omega))))
        (ofQ (⟨((2 * (K + 1) : Nat) : Int), (A + c) * (A + c + 1)⟩ : Q)
          (Nat.mul_pos (show 0 < A + c by omega) (Nat.succ_pos (A + c))))) := by
  have hD : 0 < ((⟨1, (A + c) * (A + c + 1)⟩ : Q)).den :=
    Nat.mul_pos (show 0 < A + c by omega) (Nat.succ_pos (A + c))
  have hqeq : Qeq (add (⟨1, A + c⟩ : Q) (neg (⟨1, A + c + 1⟩ : Q)))
      (⟨1, (A + c) * (A + c + 1)⟩ : Q) := by
    simp only [Qeq, add, neg]; push_cast; ring_uor
  have hq1 : Qle (⟨((A + c + 1 : Nat) : Int), 1⟩ : Q) (⟨((K + 1 : Nat) : Int), 1⟩ : Q) := by
    show ((A + c + 1 : Nat) : Int) * 1 ≤ ((K + 1 : Nat) : Int) * 1
    push_cast; omega
  have hq2 : Qle (⟨((A + c : Nat) : Int), 1⟩ : Q) (⟨((K + 1 : Nat) : Int), 1⟩ : Q) := by
    show ((A + c : Nat) : Int) * 1 ≤ ((K + 1 : Nat) : Int) * 1
    push_cast; omega
  have hsum : Qeq (add (⟨((K + 1 : Nat) : Int), 1⟩ : Q) (⟨((K + 1 : Nat) : Int), 1⟩ : Q))
      (⟨((2 * (K + 1) : Nat) : Int), 1⟩ : Q) := by
    simp only [Qeq, add]; push_cast; ring_uor
  have hS : Rle (Radd (logN (A + c + 1) (by omega)) (logN (A + c) (by omega)))
      (ofQ (⟨((2 * (K + 1) : Nat) : Int), 1⟩ : Q) Nat.one_pos) :=
    Rle_trans (Radd_le_add
        (Rle_trans (logN_le_self (A + c + 1) (by omega))
          (Rle_ofQ_ofQ Nat.one_pos Nat.one_pos hq1))
        (Rle_trans (logN_le_self (A + c) (by omega))
          (Rle_ofQ_ofQ Nat.one_pos Nat.one_pos hq2)))
      (Rle_of_Req (Req_trans (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos)
        (ofQ_congr (add_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos hsum)))
  have hqeq2 : Qeq (mul (⟨1, (A + c) * (A + c + 1)⟩ : Q) (⟨((2 * (K + 1) : Nat) : Int), 1⟩ : Q))
      (⟨((2 * (K + 1) : Nat) : Int), (A + c) * (A + c + 1)⟩ : Q) := by
    simp only [Qeq, mul]; push_cast; ring_uor
  refine hs_le_Radd ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_sub_distrib_right
    (ofQ (⟨1, A + c⟩ : Q) (show 0 < A + c by omega))
    (ofQ (⟨1, A + c + 1⟩ : Q) (Nat.succ_pos (A + c))) _))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr
    (Req_trans (Rsub_ofQ_ofQ (show 0 < A + c by omega) (Nat.succ_pos (A + c)))
      (ofQ_congr (b := (⟨1, (A + c) * (A + c + 1)⟩ : Q))
        (add_den_pos (show 0 < A + c by omega) (Nat.succ_pos (A + c))) hD hqeq))
    (Req_refl _))) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ hD (show (0 : Int) ≤ (⟨1, (A + c) * (A + c + 1)⟩ : Q).num from (by decide : (0 : Int) ≤ 1))) hS) ?_
  refine Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ hD Nat.one_pos)) ?_
  exact Rle_of_Req (ofQ_congr (Qmul_den_pos hD Nat.one_pos)
    (Nat.mul_pos (show 0 < A + c by omega) (Nat.succ_pos (A + c))) hqeq2)

/-- **The fold gap**: `hsFoldHi ≤ hsFoldLo + Σ_{j<c} 2(K+1)/((A+j)(A+j+1))` for any
    cap `A + c ≤ K` — the crude `log ≤ n` bound suffices because the harmonic cells
    telescope to `≤ c/A²`, killing a factor of `A ~ cM` (scaled defect `~ 1/M`). -/
theorem hsFold_gap (A K : Nat) (hA : 1 ≤ A) : ∀ c, A + c ≤ K →
    Rle (hsFoldHi A hA c)
      (Radd (hsFoldLo A hA c) (ofQ (gapQ A K c) (gapQ_den_pos A K hA c))) := by
  intro c
  induction c with
  | zero => exact fun _ => Rle_of_Req (Req_symm (Radd_zero zero))
  | succ k ih =>
    intro hK
    show Rle (Radd (hsFoldHi A hA k) _) _
    refine Rle_trans (Radd_le_add (ih (by omega)) (hs_cell_gap A k K hA (by omega))) ?_
    refine Rle_trans (Rle_of_Req (Radd_swap (hsFoldLo A hA k)
      (ofQ (gapQ A K k) (gapQ_den_pos A K hA k)) _ _)) ?_
    exact Rle_of_Req (Radd_congr (Req_refl _)
      (Radd_ofQ_ofQ (gapQ_den_pos A K hA k)
        (Nat.mul_pos (show 0 < A + k by omega) (Nat.succ_pos (A + k)))))

end UOR.Bridge.F1Square.Analysis
