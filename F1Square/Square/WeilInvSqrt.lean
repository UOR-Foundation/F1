/-
F1 square — **the certified `x^{-1/2}` weight test** (`WeilInvSqrt.lean`): the band-clamped inverse
square root `invSqrtF x = 1/√(max(min(x,B),1))` bundled as a genuine `L2Test` (`invSqrtTest`), the
weight factor of the continuous normalized cross-correlation `F_{f,g}(x) = x^{-1/2}·H_{f,g}(x)`.

CONSTRUCTION (all existing machinery, no new axioms):
  `isqRad x = clampedInv 1 (qBandQ 1 B x)` — the radicand `1/max(band(x),1) ∈ [1/B, 1]`
  `invSqrtF x = RsqrtRealPos (isqRad x) N hN _` — its square root `(invSqrtF x)² = isqRad x`
with `B ≥ 1` the (rational) band cap and `N ≥ B` a natural scale witness.  On the band `[1, B]` the
clamps are inert, so there `invSqrtF x` IS `x^{-1/2}`; every integral of the closed Weil form runs
inside `[1, B]` (`B` at least the support bound), so the clamping never touches a nonzero value.

CERTIFICATES: bound `M = 1` (`invSqrtF ≤ 1` since the radicand is `≤ 1`), Lipschitz modulus
`L = N/2` (the difference-of-squares route of `Rsqrt_lipschitz`: `|Δs|·(s+s') = |Δrad| ≤ |Δx|` and
`s, s' ≥ 1/N`), congruence via the unique-nonnegative-root property (`RsqrtRealPos_unique`).

RATIONAL READBACK: at a rational `1 ≤ q ≤ B`, `invSqrtF (ofQ q) ≈ normWeight q = q^{-1/2}` — the
weight of the finite-prime form `BForm`, so the continuous weight restricts to the arithmetic one.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilPrimeShiftCrux

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- The unique-nonnegative-root property of `RsqrtRealPos` (mirror of `RsqrtReal_unique`).
-- ===========================================================================

/-- **`RsqrtRealPos` is the unique non-negative square root**: any `y ≥ 0` with `y² = a` equals it. -/
theorem RsqrtRealPos_unique (a : Real) (N : Nat) (hN : 0 < N)
    (hscale : Rle one (Rmul (ofQ (⟨(N : Int) * (N : Int), 1⟩ : Q) Nat.one_pos) a))
    {y : Real} (hy : Rnonneg y) (hsq : Req (Rmul y y) a) :
    Req y (RsqrtRealPos a N hN hscale) := by
  have h : Req (Rmul y y) (Rmul (RsqrtRealPos a N hN hscale) (RsqrtRealPos a N hN hscale)) :=
    Req_trans hsq (Req_symm (RsqrtRealPos_sq a N hN hscale))
  exact Rle_antisymm
    (Rle_of_Rsq_le hy (RsqrtRealPos_nonneg a N hN hscale) (Rle_of_Req h))
    (Rle_of_Rsq_le (RsqrtRealPos_nonneg a N hN hscale) hy (Rle_of_Req (Req_symm h)))

-- ===========================================================================
-- The radicand `isqRad x = 1/max(band(x),1) ∈ [1/B, 1]`.
-- ===========================================================================

/-- The band clamp of the weight's argument: `isqBand B x ∈ [1, B]` per index. -/
def isqBand (B : Q) (hBd : 0 < B.den) (x : Real) : Real :=
  qBandQ (⟨1, 1⟩ : Q) B (by decide) hBd x

/-- **The weight radicand** `isqRad x = 1/max(isqBand x, 1)` — the clamped reciprocal of the banded
    argument, in `[1/B, 1]`. -/
def isqRad (B : Q) (hBd : 0 < B.den) (x : Real) : Real :=
  clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) (isqBand B hBd x)

/-- The radicand respects `≈`. -/
theorem isqRad_congr (B : Q) (hBd : 0 < B.den) {x y : Real} (h : Req x y) :
    Req (isqRad B hBd x) (isqRad B hBd y) :=
  clampedInv_congr (⟨1, 1⟩ : Q) (by decide) (by decide)
    (qBandQ_congr (⟨1, 1⟩ : Q) B (by decide) hBd h)

/-- `1 ≤ B` gives `0 < B.num`. -/
theorem qnum_pos_of_one_le {B : Q} (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B) : 0 < B.num := by
  have h := hB1
  simp only [Qle] at h
  push_cast at h
  omega

/-- The clamp under the reciprocal is `≤ B` per index (`Qmax(band_n, 1) ≤ B`). -/
theorem isqU_seq_le (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B) (x : Real) (n : Nat) :
    Qle ((qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x)).seq n) B := by
  show Qle (Qmax ((isqBand B hBd x).seq n) (⟨1, 1⟩ : Q)) B
  unfold Qmax
  split
  · exact hB1
  · exact qBandQ_le (⟨1, 1⟩ : Q) B (by decide) hBd x n

/-- The clamp under the reciprocal is `≤ B` at the `Real` level. -/
theorem isqU_le_B (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B) (x : Real) :
    Rle (qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x)) (ofQ B hBd) := fun n =>
  Qle_trans hBd (isqU_seq_le B hBd hB1 x n) (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **The radicand's upper bound**: `isqRad x ≤ 1` (the clamp is `≥ 1`, so its reciprocal is `≤ 1`). -/
theorem isqRad_le_one (B : Q) (hBd : 0 < B.den) (x : Real) :
    Rle (isqRad B hBd x) one :=
  Rinv_le_ofQ_inv (a := (⟨1, 1⟩ : Q)) (by decide) (by decide)
    (qClampQ_witness (⟨1, 1⟩ : Q) (by decide) (by decide) (isqBand B hBd x))
    (Rle_ofQ_qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x))

/-- **The radicand's lower bound**: `1/B ≤ isqRad x` (multiply `u·(1/u) = 1` through by `1/B` using
    `u ≤ B`). -/
theorem isqRad_ge_invB (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B) (x : Real) :
    Rle (ofQ (Qinv B) (Qinv_den_pos (qnum_pos_of_one_le hBd hB1))) (isqRad B hBd x) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  -- u·r ≈ 1 (the clamped reciprocal against its clamp)
  have hur : Req (Rmul (qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x)) (isqRad B hBd x))
      one :=
    Rmul_Rinv_self (qClampQ_witness (⟨1, 1⟩ : Q) (by decide) (by decide) (isqBand B hBd x))
  -- (1/B)·(u·r) ≤ (1/B)·(B·r) — via u ≤ B and r ≥ 0
  have hnnr : Rnonneg (isqRad B hBd x) :=
    Rnonneg_clampedInv (⟨1, 1⟩ : Q) (by decide) (by decide) (isqBand B hBd x)
  have hnnQ : Rnonneg (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
    Rnonneg_ofQ (Qinv_den_pos hBn) (Int.le_of_lt (Qinv_num_pos hBd))
  have hstep : Rle (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn))
        (Rmul (qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x)) (isqRad B hBd x)))
      (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (isqRad B hBd x))) :=
    Rmul_le_Rmul_left hnnQ
      (Rmul_le_Rmul_right hnnr (isqU_le_B B hBd hB1 x))
  -- LHS ≈ 1/B ; RHS ≈ ((1/B)·B)·r ≈ 1·r ≈ r
  have hL : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn))
        (Rmul (qClampQ (⟨1, 1⟩ : Q) (by decide) (isqBand B hBd x)) (isqRad B hBd x)))
      (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
    Req_trans (Rmul_congr (Req_refl _) hur) (Rmul_one _)
  have hQeq : Qeq (mul (Qinv B) B) (⟨1, 1⟩ : Q) :=
    Qeq_trans (Qmul_den_pos hBd (Qinv_den_pos hBn)) (Qmul_comm (Qinv B) B) (Qmul_Qinv hBn)
  have hR : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (isqRad B hBd x)))
      (isqRad B hBd x) := by
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (Qinv B) (Qinv_den_pos hBn)) (ofQ B hBd)
      (isqRad B hBd x))) ?_
    refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hBn) hBd)
      (ofQ_congr (Qmul_den_pos (Qinv_den_pos hBn) hBd) (by decide) hQeq)) (Req_refl _)) ?_
    exact Rone_mul _
  exact Rle_trans (Rle_of_Req (Req_symm hL)) (Rle_trans hstep (Rle_of_Req hR))

-- ===========================================================================
-- The scale witness `1 ≤ N²·isqRad x` (for `B ≤ N`).
-- ===========================================================================

/-- `1 ≤ N·(1/B)` as rationals (from `B ≤ N`). -/
theorem one_le_N_invB {B : Q} (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) :
    Qle (⟨1, 1⟩ : Q) (mul (⟨(N : Int), 1⟩ : Q) (Qinv B)) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  have hb := hBN
  simp only [Qle, mul, Qinv] at hb ⊢
  push_cast [Int.toNat_of_nonneg (Int.le_of_lt hBn)] at hb ⊢
  have hcomm : (N : Int) * (B.den : Int) = (B.den : Int) * (N : Int) := Int.mul_comm _ _
  omega

/-- **The scale witness**: `1 ≤ N·isqRad x` (via `isqRad ≥ 1/B` and `1 ≤ N·(1/B)`). -/
theorem one_le_N_isqRad (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle one (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (isqRad B hBd x)) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  have h1 : Rle one (ofQ (mul (⟨(N : Int), 1⟩ : Q) (Qinv B))
      (Qmul_den_pos Nat.one_pos (Qinv_den_pos hBn))) :=
    Rle_ofQ_ofQ (by decide) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hBn))
      (one_le_N_invB hBd hB1 N hBN)
  refine Rle_trans h1 ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (Qinv_den_pos hBn)))) ?_
  exact Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg N))
    (isqRad_ge_invB B hBd hB1 x)

/-- **The `N²` scale witness of `RsqrtRealPos`**: `1 ≤ N²·isqRad x`. -/
theorem isqRad_scale (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle one (Rmul (ofQ (⟨(N : Int) * (N : Int), 1⟩ : Q) Nat.one_pos) (isqRad B hBd x)) := by
  -- N²·r ≈ N·(N·r) ≥ N·1 = N ≥ 1
  have hstep : Rle (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) one)
      (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)
        (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (isqRad B hBd x))) :=
    Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg N))
      (one_le_N_isqRad B hBd hB1 N hN hBN x)
  have hN1 : Rle one (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) :=
    Rle_ofQ_ofQ (by decide) Nat.one_pos (by simp only [Qle]; push_cast; omega)
  have hcollapse : Req (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)
        (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (isqRad B hBd x)))
      (Rmul (ofQ (⟨(N : Int) * (N : Int), 1⟩ : Q) Nat.one_pos) (isqRad B hBd x)) := by
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    exact Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos)
      (ofQ_congr (Qmul_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos
        (by simp only [Qeq, mul]; try push_cast; try ring_uor))) (Req_refl _)
  refine Rle_trans hN1 ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_one (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)))) ?_
  exact Rle_trans hstep (Rle_of_Req hcollapse)

-- ===========================================================================
-- The weight `invSqrtF` and its certificates.
-- ===========================================================================

/-- **THE `x^{-1/2}` WEIGHT** (band-clamped): `invSqrtF x = √(1/max(band(x),1)) = 1/√(max(band(x),1))`. -/
def invSqrtF (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) : Real :=
  RsqrtRealPos (isqRad B hBd x) N hN (isqRad_scale B hBd hB1 N hN hBN x)

/-- The defining square: `(invSqrtF x)² = isqRad x`. -/
theorem invSqrtF_sq (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Req (Rmul (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN x))
      (isqRad B hBd x) :=
  RsqrtRealPos_sq (isqRad B hBd x) N hN (isqRad_scale B hBd hB1 N hN hBN x)

theorem invSqrtF_nonneg (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rnonneg (invSqrtF B hBd hB1 N hN hBN x) :=
  RsqrtRealPos_nonneg (isqRad B hBd x) N hN (isqRad_scale B hBd hB1 N hN hBN x)

/-- `invSqrtF ≤ 1` (its square is the radicand `≤ 1`). -/
theorem invSqrtF_le_one (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle (invSqrtF B hBd hB1 N hN hBN x) one := by
  refine Rle_of_Rsq_le (invSqrtF_nonneg B hBd hB1 N hN hBN x)
    (Rnonneg_ofQ (by decide) (by decide)) ?_
  refine Rle_trans (Rle_of_Req (invSqrtF_sq B hBd hB1 N hN hBN x)) ?_
  exact Rle_trans (isqRad_le_one B hBd x) (Rle_of_Req (Req_symm (Rmul_one one)))

/-- `1/N ≤ invSqrtF` (its square is the radicand `≥ 1/B ≥ 1/N ≥ 1/N²`). -/
theorem invSqrtF_ge_invN (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle (ofQ (⟨1, N⟩ : Q) hN) (invSqrtF B hBd hB1 N hN hBN x) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  refine Rle_of_Rsq_le (Rnonneg_ofQ hN (by show (0 : Int) ≤ 1; decide))
    (invSqrtF_nonneg B hBd hB1 N hN hBN x) ?_
  -- (1/N)² = 1/N² ≤ 1/N ≤ 1/B ≤ rad = s²
  have h1 : Req (Rmul (ofQ (⟨1, N⟩ : Q) hN) (ofQ (⟨1, N⟩ : Q) hN))
      (ofQ (⟨1, N * N⟩ : Q) (Nat.mul_pos hN hN)) :=
    Req_trans (Rmul_ofQ_ofQ hN hN)
      (ofQ_congr (Qmul_den_pos hN hN) (Nat.mul_pos hN hN) (Qeq_refl _))
  have h2 : Qle (⟨1, N * N⟩ : Q) (⟨1, N⟩ : Q) := by
    show (1 : Int) * (N : Int) ≤ 1 * ((N * N : Nat) : Int)
    push_cast
    have := Nat.le_mul_of_pos_left N hN
    omega
  have h3 : Qle (⟨1, N⟩ : Q) (Qinv B) := by
    show (1 : Int) * (B.num.toNat : Int) ≤ (B.den : Int) * (N : Int)
    have hb := hBN
    simp only [Qle] at hb
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hBn)] at hb ⊢
    have hcomm : (N : Int) * (B.den : Int) = (B.den : Int) * (N : Int) := Int.mul_comm _ _
    omega
  refine Rle_trans (Rle_of_Req h1) ?_
  refine Rle_trans (Rle_ofQ_ofQ (Nat.mul_pos hN hN) hN h2) ?_
  refine Rle_trans (Rle_ofQ_ofQ hN (Qinv_den_pos hBn) h3) ?_
  exact Rle_trans (isqRad_ge_invB B hBd hB1 x)
    (Rle_of_Req (Req_symm (invSqrtF_sq B hBd hB1 N hN hBN x)))

/-- The weight respects `≈` (unique non-negative root over the congruent radicand). -/
theorem invSqrtF_congr (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) {x y : Real} (h : Req x y) :
    Req (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y) :=
  RsqrtRealPos_unique (isqRad B hBd y) N hN (isqRad_scale B hBd hB1 N hN hBN y)
    (invSqrtF_nonneg B hBd hB1 N hN hBN x)
    (Req_trans (invSqrtF_sq B hBd hB1 N hN hBN x) (isqRad_congr B hBd h))

/-- **The weight is `N/2`-Lipschitz** — the `Rsqrt_lipschitz` route: `|Δs|·(s+s') = |Δrad| ≤ |Δx|`
    with `s, s' ≥ 1/N`, so `(2/N)·|Δs| ≤ |Δx|`. -/
theorem invSqrtF_lipschitz (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x y : Real) :
    Rle (Rabs (Rsub (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y)))
        (Rmul (ofQ (⟨(N : Int), 2⟩ : Q) (Nat.succ_pos 1)) (Rabs (Rsub x y))) := by
  -- 2/N ≤ s + t ≤ |s + t|
  have h2N : Req (ofQ (⟨2, N⟩ : Q) hN)
      (Radd (ofQ (⟨1, N⟩ : Q) hN) (ofQ (⟨1, N⟩ : Q) hN)) := by
    refine Req_trans (ofQ_congr hN (add_den_pos hN hN) ?_) (Req_symm (Radd_ofQ_ofQ hN hN))
    simp only [Qeq, add]; push_cast; ring_uor
  have h2st : Rle (ofQ (⟨2, N⟩ : Q) hN)
      (Rabs (Radd (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))) :=
    Rle_trans (Rle_trans (Rle_of_Req h2N)
        (Radd_le_add (invSqrtF_ge_invN B hBd hB1 N hN hBN x)
          (invSqrtF_ge_invN B hBd hB1 N hN hBN y)))
      (Rle_Rabs_self (Radd (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y)))
  -- (s − t)(s + t) ≈ rad x − rad y
  have hprod : Req (Rmul (Rsub (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))
        (Radd (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y)))
      (Rsub (isqRad B hBd x) (isqRad B hBd y)) :=
    Req_trans (Rmul_sub_add_self (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))
      (Rsub_congr (invSqrtF_sq B hBd hB1 N hN hBN x) (invSqrtF_sq B hBd hB1 N hN hBN y))
  have habs : Req (Rmul
        (Rabs (Rsub (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y)))
        (Rabs (Radd (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))))
      (Rabs (Rsub (isqRad B hBd x) (isqRad B hBd y))) :=
    Req_trans (Req_symm (Rabs_Rmul _ _)) (Rabs_congr hprod)
  -- |Δrad| ≤ |Δx|  (clampedInv 1-Lipschitz ∘ band 1-Lipschitz)
  have hradlip : Rle (Rabs (Rsub (isqRad B hBd x) (isqRad B hBd y))) (Rabs (Rsub x y)) := by
    refine Rle_trans (clampedInv_lipschitz (⟨1, 1⟩ : Q) (by decide) (by decide)
      (isqBand B hBd x) (isqBand B hBd y)) ?_
    have hone : Req (ofQ (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q)))
          (Qmul_den_pos (Qinv_den_pos (by decide)) (Qinv_den_pos (by decide)))) one :=
      Req_of_seq_Qeq (fun _ => by
        show Qeq (mul (Qinv (⟨1, 1⟩ : Q)) (Qinv (⟨1, 1⟩ : Q))) (⟨1, 1⟩ : Q); decide)
    refine Rle_trans (Rle_of_Req (Req_trans (Rmul_congr hone (Req_refl _)) (Rone_mul _))) ?_
    exact qBandQ_lipschitz (⟨1, 1⟩ : Q) B (by decide) hBd x y
  -- (2/N)·|Δs| ≤ |Δs|·|s+t| ≈ |Δrad| ≤ |Δx|
  have hchain : Rle (Rmul (ofQ (⟨2, N⟩ : Q) hN)
        (Rabs (Rsub (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))))
      (Rabs (Rsub x y)) := by
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs _) h2st) ?_
    refine Rle_trans (Rle_of_Req (Rmul_comm _ _)) ?_
    exact Rle_trans (Rle_of_Req habs) hradlip
  -- |Δs| ≈ (N/2)·((2/N)·|Δs|) ≤ (N/2)·|Δx|
  have hcollapse : Req (Rmul (ofQ (⟨(N : Int), 2⟩ : Q) (Nat.succ_pos 1)) (ofQ (⟨2, N⟩ : Q) hN)) one := by
    refine Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos 1) hN)
      (ofQ_congr (Qmul_den_pos (Nat.succ_pos 1) hN) (by decide) ?_)
    show (N : Int) * 2 * ((1 : Nat) : Int) = 1 * ((2 * N : Nat) : Int)
    push_cast; ring_uor
  refine Rle_trans (Rle_of_Req (Req_symm (Rone_mul (Rabs (Rsub (invSqrtF B hBd hB1 N hN hBN x)
    (invSqrtF B hBd hB1 N hN hBN y)))))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_symm hcollapse) (Req_refl _))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_assoc (ofQ (⟨(N : Int), 2⟩ : Q) (Nat.succ_pos 1))
    (ofQ (⟨2, N⟩ : Q) hN)
    (Rabs (Rsub (invSqrtF B hBd hB1 N hN hBN x) (invSqrtF B hBd hB1 N hN hBN y))))) ?_
  exact Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (Int.ofNat_nonneg N)) hchain

-- ===========================================================================
-- The bundled `L2Test`.
-- ===========================================================================

/-- **THE `x^{-1/2}` WEIGHT TEST** — `invSqrtF` bundled with its certificates (Lipschitz `N/2`,
    bound `1`), the weight factor of the continuous normalized cross-correlation. -/
def invSqrtTest (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) : L2Test where
  f := invSqrtF B hBd hB1 N hN hBN
  L := ⟨(N : Int), 2⟩
  M := ⟨1, 1⟩
  hLd := Nat.succ_pos 1
  hLn := Int.ofNat_nonneg N
  hMd := by decide
  hMn := by decide
  hlip := invSqrtF_lipschitz B hBd hB1 N hN hBN
  hfc := fun _ _ h => invSqrtF_congr B hBd hB1 N hN hBN h
  hbd := fun x =>
    Rle_trans
      (Rle_of_Req (Rabs_of_nonneg (invSqrtF_nonneg B hBd hB1 N hN hBN x)))
      (invSqrtF_le_one B hBd hB1 N hN hBN x)

-- ===========================================================================
-- Rational readback: on the band, `invSqrtF (ofQ q) = normWeight q = q^{-1/2}`.
-- ===========================================================================

/-- **RATIONAL IN-BAND READBACK**: at a rational `1 ≤ q ≤ B`, the continuous weight IS the
    finite-prime weight — `invSqrtF (ofQ q) ≈ normWeight q = q^{-1/2}`. -/
theorem invSqrtF_ofQ (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (q : Q) (hqd : 0 < q.den) (hq1 : Qle (⟨1, 1⟩ : Q) q) (hqB : Qle q B) :
    Req (invSqrtF B hBd hB1 N hN hBN (ofQ q hqd)) (normWeight q) := by
  have hqn : 0 < q.num := qnum_pos_of_one_le hqd hq1
  -- the radicand at ofQ q is 1/q
  have hband : Req (isqBand B hBd (ofQ q hqd)) (ofQ q hqd) :=
    qBandQ_eq_of_band (Rle_ofQ_ofQ (by decide) hqd hq1) (Rle_ofQ_ofQ hqd hBd hqB)
  have hrad : Req (isqRad B hBd (ofQ q hqd)) (ofQ (Qinv q) (Qinv_den_pos hqn)) :=
    Req_trans (clampedInv_congr (⟨1, 1⟩ : Q) (by decide) (by decide) hband)
      (clampedInv_ofQ (by decide) (by decide) hqd hqn hq1)
  -- normWeight q = Rsqrt (Qinv q) is a nonneg root of the same radicand
  have hroot : Req (Rmul (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q))
        (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)))
      (isqRad B hBd (ofQ q hqd)) :=
    Req_trans (Rsqrt_sq (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)) (Req_symm hrad)
  refine Req_symm (Req_trans (normWeight_pos_eq hqn) ?_)
  exact RsqrtRealPos_unique (isqRad B hBd (ofQ q hqd)) N hN
    (isqRad_scale B hBd hB1 N hN hBN (ofQ q hqd))
    (Rsqrt_nonneg (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)) hroot

/-- The weight at `1` is `1` (`normWeight ⟨1,1⟩ = √1 = 1`). -/
theorem invSqrtF_one (B : Q) (hBd : 0 < B.den) (hB1 : Qle (⟨1, 1⟩ : Q) B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) :
    Req (invSqrtF B hBd hB1 N hN hBN one) one := by
  refine Req_trans (invSqrtF_ofQ B hBd hB1 N hN hBN (⟨1, 1⟩ : Q) (by decide)
    (Qle_refl _) hB1) ?_
  -- normWeight ⟨1,1⟩ ≈ Rsqrt (Qinv ⟨1,1⟩) = Rsqrt ⟨1,1⟩ ≈ 1
  refine Req_trans (normWeight_pos_eq (by decide)) ?_
  exact Rsqrt_one

end UOR.Bridge.F1Square.Square
