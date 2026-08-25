/-
F1 square — **the rational geometry of inversion** (`IntegralInversionGeom.lean`): the uniform
partition `y_i = 1 + i·h`, `h = (B−1)/(N+1)`, of `[1, B]` and its inverse image `x_i = 1/y_i`
(a NON-uniform strictly decreasing partition of `[1/B, 1]`; the cell count `N+1` is general — no dyadic restriction), with the exact rational identities
that drive the change of variables `x = 1/y`:

    `x_i − x_{i+1} = h·x_i·x_{i+1}`   (`invX_sub_eq`),   `0 ≤ x_i − x_{i+1} ≤ h`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.IntegralCell

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) Rational order helpers.
-- ===========================================================================

theorem Qlt_of_Qsub_num_pos {a b : Q} (h : 0 < (Qsub b a).num) : Qlt a b := by
  simp only [Qsub, add, neg, Int.neg_mul] at h
  show a.num * (b.den : Int) < b.num * (a.den : Int)
  omega

/-- `a < a + h` for `h > 0`. -/
theorem Qlt_self_add_pos (a : Q) (had : 0 < a.den) {h : Q} (hhd : 0 < h.den) (hhn : 0 < h.num) :
    Qlt a (add a h) := by
  show a.num * ((a.den * h.den : Nat) : Int) < (a.num * (h.den : Int) + h.num * (a.den : Int)) * (a.den : Int)
  have hp : 0 < h.num * ((a.den : Int) * (a.den : Int)) :=
    Int.mul_pos hhn (Int.mul_pos (Int.ofNat_pos.mpr had) (Int.ofNat_pos.mpr had))
  have e : (a.num * (h.den : Int) + h.num * (a.den : Int)) * (a.den : Int)
      - a.num * ((a.den * h.den : Nat) : Int) = h.num * ((a.den : Int) * (a.den : Int)) := by
    push_cast; ring_uor
  omega

/-- `(a + h) − a = h`. -/
theorem Qsub_add_self_eq (a h : Q) : Qeq (Qsub (add a h) a) h := by
  simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor

-- ===========================================================================
-- (2) The dyadic mesh and the two partitions.
-- ===========================================================================

/-- The mesh `h = (B−1)/(N+1)`. -/
def invH (B : Q) (k : Nat) : Q := mul (Qsub B (⟨1, 1⟩ : Q)) (⟨1, k + 1⟩ : Q)

theorem invH_den (B : Q) (hBd : 0 < B.den) (k : Nat) : 0 < (invH B k).den :=
  Qmul_den_pos (Qsub_den_pos hBd Nat.one_pos) (Nat.succ_pos k)

theorem invH_num (B : Q) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k : Nat) : 0 < (invH B k).num :=
  Int.mul_pos (Qsub_num_pos_of_lt hB1) (show (0 : Int) < 1 by decide)

/-- The uniform partition `y_0 = 1`, `y_{i+1} = y_i + h` of `[1, B]`. -/
def invY (B : Q) (k : Nat) : Nat → Q
  | 0 => ⟨1, 1⟩
  | (i + 1) => add (invY B k i) (invH B k)

theorem invY_den (B : Q) (hBd : 0 < B.den) (k : Nat) : ∀ i, 0 < (invY B k i).den
  | 0 => Nat.one_pos
  | (i + 1) => add_den_pos (invY_den B hBd k i) (invH_den B hBd k)

/-- `1 ≤ y_i`. -/
theorem invY_ge_one (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k : Nat) :
    ∀ i, Qle (⟨1, 1⟩ : Q) (invY B k i)
  | 0 => Qle_refl _
  | (i + 1) => Qle_trans (invY_den B hBd k i) (invY_ge_one B hBd hB1 k i)
      (Qle_self_add (Int.le_of_lt (invH_num B hB1 k)))

theorem invY_num (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    0 < (invY B k i).num :=
  qnum_pos_of_one_le (invY_den B hBd k i) (invY_ge_one B hBd hB1 k i)

/-- `y_i < y_{i+1}`. -/
theorem invY_step_lt (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qlt (invY B k i) (invY B k (i + 1)) :=
  Qlt_self_add_pos _ (invY_den B hBd k i) (invH_den B hBd k) (invH_num B hB1 k)

/-- `y_{i+1} − y_i = h`. -/
theorem invY_step_sub (B k i : _) : Qeq (Qsub (invY B k (i + 1)) (invY B k i)) (invH B k) :=
  Qsub_add_self_eq _ _

/-- The step `y_0 < y_{i+1} ⟹ y_0 < y_{i+2}` (`y_{i+2} − y_0 = (y_{i+2} − y_{i+1}) + (y_{i+1} − y_0)`,
    both positive) — standalone, so the reflection term stays out of the recursion. -/
theorem invY_zero_lt_step (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat)
    (h : Qlt (invY B k 0) (invY B k (i + 1))) : Qlt (invY B k 0) (invY B k (i + 2)) := by
  refine Qlt_of_Qsub_num_pos ?_
  have h1 := Qsub_num_pos_of_lt h
  have h2 := invH_num B hB1 k
  have hd := invY_den B hBd k 0
  have hd1 := invY_den B hBd k (i + 1)
  have hhd := invH_den B hBd k
  show 0 < (Qsub (add (invY B k (i + 1)) (invH B k)) (invY B k 0)).num
  simp only [Qsub, add, neg, Int.neg_mul] at h1 ⊢
  push_cast at h1 ⊢
  have e : ((invY B k (i + 1)).num * ((invH B k).den : Int) + (invH B k).num * ((invY B k (i + 1)).den : Int))
        * ((invY B k 0).den : Int) - (invY B k 0).num * (((invY B k (i + 1)).den : Int) * ((invH B k).den : Int))
      = ((invY B k (i + 1)).num * ((invY B k 0).den : Int) - (invY B k 0).num * ((invY B k (i + 1)).den : Int))
          * ((invH B k).den : Int)
        + (invH B k).num * (((invY B k (i + 1)).den : Int) * ((invY B k 0).den : Int)) := by
    generalize (invY B k (i + 1)).num = N
    generalize ((invY B k (i + 1)).den : Int) = D
    generalize (invY B k 0).num = N0
    generalize ((invY B k 0).den : Int) = D0
    generalize (invH B k).num = n
    generalize ((invH B k).den : Int) = d
    ring_uor
  have hp1 : 0 < ((invY B k (i + 1)).num * ((invY B k 0).den : Int) - (invY B k 0).num * ((invY B k (i + 1)).den : Int))
          * ((invH B k).den : Int) := Int.mul_pos h1 (Int.ofNat_pos.mpr hhd)
  have hp2 : 0 < (invH B k).num * (((invY B k (i + 1)).den : Int) * ((invY B k 0).den : Int)) :=
    Int.mul_pos h2 (Int.mul_pos (Int.ofNat_pos.mpr hd1) (Int.ofNat_pos.mpr hd))
  omega

/-- `y_0 < y_{i+1}`. -/
theorem invY_zero_lt (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k : Nat) :
    ∀ i, Qlt (invY B k 0) (invY B k (i + 1))
  | 0 => invY_step_lt B hBd hB1 k 0
  | (i + 1) => invY_zero_lt_step B hBd hB1 k i (invY_zero_lt B hBd hB1 k i)

/-- Closed-form identities (standalone reflection terms). -/
theorem invY_eq_zero_id (h : Q) :
    Qeq (⟨1, 1⟩ : Q) (add (⟨1, 1⟩ : Q) (mul (⟨((0 : Nat) : Int), 1⟩ : Q) h)) := by
  simp only [Qeq, add, mul]; push_cast
  generalize h.num = n
  generalize ((h.den : Nat) : Int) = d
  ring_uor

theorem invY_eq_step_id (h : Q) (i : Nat) :
    Qeq (add (add (⟨1, 1⟩ : Q) (mul (⟨(i : Int), 1⟩ : Q) h)) h)
        (add (⟨1, 1⟩ : Q) (mul (⟨((i + 1 : Nat) : Int), 1⟩ : Q) h)) := by
  simp only [Qeq, add, mul]; push_cast
  generalize h.num = n
  generalize ((h.den : Nat) : Int) = d
  generalize ((i : Nat) : Int) = I
  ring_uor

/-- The closed form `y_i = 1 + i·h`. -/
theorem invY_eq (B : Q) (hBd : 0 < B.den) (k : Nat) :
    ∀ i, Qeq (invY B k i) (add (⟨1, 1⟩ : Q) (mul (⟨(i : Int), 1⟩ : Q) (invH B k)))
  | 0 => invY_eq_zero_id (invH B k)
  | (i + 1) =>
      Qeq_trans (add_den_pos (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (invH_den B hBd k)))
          (invH_den B hBd k))
        (Qadd_congr (invY_eq B hBd k i) (Qeq_refl _)) (invY_eq_step_id (invH B k) i)

/-- **The top point** `y_{N+1} = B`. -/
theorem invY_top (B : Q) (hBd : 0 < B.den) (k : Nat) : Qeq (invY B k (k + 1)) B := by
  refine Qeq_trans (add_den_pos Nat.one_pos (Qmul_den_pos Nat.one_pos (invH_den B hBd k)))
    (invY_eq B hBd k (k + 1)) ?_
  simp only [Qeq, add, mul, invH, Qsub, neg]
  push_cast
  generalize B.num = bn
  generalize ((B.den : Nat) : Int) = bd
  generalize ((k : Nat) : Int) = K
  ring_uor

-- ===========================================================================
-- (3) The inverse partition `x_i = 1/y_i` of `[1/B, 1]`.
-- ===========================================================================

/-- `x_i = 1/y_i`. -/
def invX (B : Q) (k i : Nat) : Q := Qinv (invY B k i)

theorem invX_den (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    0 < (invX B k i).den := Qinv_den_pos (invY_num B hBd hB1 k i)

theorem invX_num (B : Q) (hBd : 0 < B.den) (k i : Nat) : 0 < (invX B k i).num :=
  Qinv_num_pos (invY_den B hBd k i)

theorem invX_nonneg (B : Q) (k i : Nat) : Qle (⟨0, 1⟩ : Q) (invX B k i) := qinv_num_nonneg _

theorem invX_le_one (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qle (invX B k i) (⟨1, 1⟩ : Q) :=
  qinv_le_one (invY_den B hBd k i) (invY_ge_one B hBd hB1 k i)

theorem invX_zero_eq (B : Q) (k : Nat) : Qeq (invX B k 0) (⟨1, 1⟩ : Q) := by
  show Qeq (Qinv (⟨1, 1⟩ : Q)) (⟨1, 1⟩ : Q); decide

/-- `x_{i+1} < x_i`. -/
theorem invX_step_lt (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qlt (invX B k (i + 1)) (invX B k i) :=
  Qinv_lt_of_lt (invY_num B hBd hB1 k i) (invY_num B hBd hB1 k (i + 1)) (invY_step_lt B hBd hB1 k i)

/-- `x_{i+1} < x_0`. -/
theorem invX_zero_lt (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qlt (invX B k (i + 1)) (invX B k 0) :=
  Qinv_lt_of_lt (invY_num B hBd hB1 k 0) (invY_num B hBd hB1 k (i + 1)) (invY_zero_lt B hBd hB1 k i)

/-- **THE KEY INVERSION IDENTITY** `x_i − x_{i+1} = h·x_i·x_{i+1}` (from `y_{i+1} = y_i + h`:
    `1/y − 1/(y+h) = h/(y(y+h))`). -/
theorem invX_sub_eq (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qeq (Qsub (invX B k i) (invX B k (i + 1)))
        (mul (invH B k) (mul (invX B k i) (invX B k (i + 1)))) := by
  have hN : 0 < (invY B k i).num := invY_num B hBd hB1 k i
  have hN' : 0 < (invY B k (i + 1)).num := invY_num B hBd hB1 k (i + 1)
  have hn1 : (((invY B k i).num.toNat : Nat) : Int) = (invY B k i).num :=
    Int.toNat_of_nonneg (Int.le_of_lt hN)
  have hn2 : (((invY B k (i + 1)).num.toNat : Nat) : Int) = (invY B k (i + 1)).num :=
    Int.toNat_of_nonneg (Int.le_of_lt hN')
  have hnum' : (invY B k (i + 1)).num
      = (invY B k i).num * ((invH B k).den : Int) + (invH B k).num * ((invY B k i).den : Int) := rfl
  have hden' : ((invY B k (i + 1)).den : Int) = ((invY B k i).den : Int) * ((invH B k).den : Int) := by
    show (((invY B k i).den * (invH B k).den : Nat) : Int) = _; push_cast; rfl
  show (Qsub (Qinv (invY B k i)) (Qinv (invY B k (i + 1)))).num
        * ((mul (invH B k) (mul (Qinv (invY B k i)) (Qinv (invY B k (i + 1))))).den : Int)
      = (mul (invH B k) (mul (Qinv (invY B k i)) (Qinv (invY B k (i + 1))))).num
        * ((Qsub (Qinv (invY B k i)) (Qinv (invY B k (i + 1)))).den : Int)
  simp only [Qsub, add, neg, mul, Qinv]
  push_cast
  rw [hn1, hn2, hnum', hden']
  generalize (invY B k i).num = N
  generalize ((invY B k i).den : Int) = D
  generalize (invH B k).num = n
  generalize ((invH B k).den : Int) = d
  ring_uor

/-- `0 ≤ x_i − x_{i+1}`. -/
theorem invX_sub_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    0 ≤ (Qsub (invX B k i) (invX B k (i + 1))).num :=
  Qsub_num_nonneg (Qle_of_Qlt_loc (invX_step_lt B hBd hB1 k i))

/-- `x_i·x_{i+1} ≤ 1`. -/
theorem invX_prod_le_one (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qle (mul (invX B k i) (invX B k (i + 1))) (⟨1, 1⟩ : Q) := by
  have h1 : Qle (mul (invX B k i) (invX B k (i + 1))) (mul (⟨1, 1⟩ : Q) (invX B k (i + 1))) :=
    Qmul_le_mul_right (Int.le_of_lt (invX_num B hBd k (i + 1))) (invX_le_one B hBd hB1 k i)
  refine Qle_trans (Qmul_den_pos Nat.one_pos (invX_den B hBd hB1 k (i + 1))) h1 ?_
  refine Qle_trans (invX_den B hBd hB1 k (i + 1)) (Qeq_le (Qone_mul _)) ?_
  exact invX_le_one B hBd hB1 k (i + 1)

/-- **`x_i − x_{i+1} ≤ h`** (the inverse partition is no coarser than the mesh). -/
theorem invX_sub_le_h (B : Q) (hBd : 0 < B.den) (hB1 : Qlt (⟨1, 1⟩ : Q) B) (k i : Nat) :
    Qle (Qsub (invX B k i) (invX B k (i + 1))) (invH B k) := by
  have hxd := invX_den B hBd hB1 k i
  have hxd' := invX_den B hBd hB1 k (i + 1)
  have hhd := invH_den B hBd k
  refine Qle_trans (Qmul_den_pos hhd (Qmul_den_pos hxd hxd')) (Qeq_le (invX_sub_eq B hBd hB1 k i)) ?_
  refine Qle_trans (Qmul_den_pos hhd Nat.one_pos)
    (Qmul_le_mul_left (Int.le_of_lt (invH_num B hB1 k)) (invX_prod_le_one B hBd hB1 k i)) ?_
  exact Qeq_le (Qeq_trans (Qmul_den_pos Nat.one_pos hhd) (Qmul_comm _ _) (Qone_mul _))

end UOR.Bridge.F1Square.Square
