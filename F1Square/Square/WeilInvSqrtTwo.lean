/-
F1 square — **the two-sided certified `x^{-1/2}` weight** (`WeilInvSqrtTwo.lean`): the band-clamped
inverse square root with a POSITIVE floor `c` (not `1`),

    `invSqrtTwoF x = √(1/max(min(x,B), c)) = x^{-1/2}`  on the whole band `[c, B]`,

so that — unlike the high-side `invSqrtF` (floor `1`, which equals `1` below `1`) — it carries the
genuine `x^{-1/2}` weight on BOTH sides of `1`.  On `[c, B]` with `c = 1/B` this is the two-sided
positive-band weight of the two-sided normalized correlation.

Same construction as `WeilInvSqrt`: radicand `1/max(band(x), c) ∈ [1/B, 1/c]`, square root
`RsqrtRealPos` with scale witness `N ≥ B`; certificates bound `M = 1/c`, Lipschitz `(N/2)·(1/c)²`,
congruence via the unique root; rational readback to `normWeight q = q^{-1/2}` at every `c ≤ q ≤ B`
(integer AND reciprocal scales).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilInvSqrt

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (0) The radicand `1/max(band_{[c,B]}(x), c) ∈ [1/B, 1/c]`.
-- ===========================================================================

/-- The band clamp of the argument to `[c, B]`. -/
def twoBand (c B : Q) (hcd : 0 < c.den) (hBd : 0 < B.den) (x : Real) : Real :=
  qBandQ c B hcd hBd x

/-- **The two-sided radicand** `1/max(band(x), c)`. -/
def twoRad (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den) (x : Real) : Real :=
  clampedInv c hcn hcd (twoBand c B hcd hBd x)

theorem twoRad_congr (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    {x y : Real} (h : Req x y) :
    Req (twoRad c B hcn hcd hBd x) (twoRad c B hcn hcd hBd y) :=
  clampedInv_congr c hcn hcd (qBandQ_congr c B hcd hBd h)

/-- The clamp under the reciprocal is `≤ B` per index (`Qmax(band_n, c) ≤ B`, needs `c ≤ B`). -/
theorem twoU_seq_le (c B : Q) (hcd : 0 < c.den) (hBd : 0 < B.den) (hcB : Qle c B)
    (x : Real) (n : Nat) :
    Qle ((qClampQ c hcd (twoBand c B hcd hBd x)).seq n) B := by
  show Qle (Qmax ((twoBand c B hcd hBd x).seq n) c) B
  unfold Qmax
  split
  · exact hcB
  · exact qBandQ_le c B hcd hBd x n

theorem twoU_le_B (c B : Q) (hcd : 0 < c.den) (hBd : 0 < B.den) (hcB : Qle c B) (x : Real) :
    Rle (qClampQ c hcd (twoBand c B hcd hBd x)) (ofQ B hBd) := fun n =>
  Qle_trans hBd (twoU_seq_le c B hcd hBd hcB x n) (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- **Upper bound** `twoRad ≤ 1/c`. -/
theorem twoRad_le_invc (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den) (x : Real) :
    Rle (twoRad c B hcn hcd hBd x) (ofQ (Qinv c) (Qinv_den_pos hcn)) :=
  Rinv_le_ofQ_inv hcn hcd (qClampQ_witness c hcn hcd (twoBand c B hcd hBd x))
    (Rle_ofQ_qClampQ c hcd (twoBand c B hcd hBd x))

/-- **Lower bound** `1/B ≤ twoRad` (multiply `u·(1/u) = 1` through by `1/B` using `u ≤ B`). -/
theorem twoRad_ge_invB (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (x : Real) :
    Rle (ofQ (Qinv B) (Qinv_den_pos (qnum_pos_of_one_le hBd hB1))) (twoRad c B hcn hcd hBd x) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  have hur : Req (Rmul (qClampQ c hcd (twoBand c B hcd hBd x)) (twoRad c B hcn hcd hBd x)) one :=
    Rmul_Rinv_self (qClampQ_witness c hcn hcd (twoBand c B hcd hBd x))
  have hnnr : Rnonneg (twoRad c B hcn hcd hBd x) :=
    Rnonneg_clampedInv c hcn hcd (twoBand c B hcd hBd x)
  have hnnQ : Rnonneg (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
    Rnonneg_ofQ (Qinv_den_pos hBn) (Int.le_of_lt (Qinv_num_pos hBd))
  have hstep : Rle (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn))
        (Rmul (qClampQ c hcd (twoBand c B hcd hBd x)) (twoRad c B hcn hcd hBd x)))
      (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (twoRad c B hcn hcd hBd x))) :=
    Rmul_le_Rmul_left hnnQ (Rmul_le_Rmul_right hnnr (twoU_le_B c B hcd hBd hcB x))
  have hL : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn))
        (Rmul (qClampQ c hcd (twoBand c B hcd hBd x)) (twoRad c B hcn hcd hBd x)))
      (ofQ (Qinv B) (Qinv_den_pos hBn)) :=
    Req_trans (Rmul_congr (Req_refl _) hur) (Rmul_one _)
  have hQeq : Qeq (mul (Qinv B) B) (⟨1, 1⟩ : Q) :=
    Qeq_trans (Qmul_den_pos hBd (Qinv_den_pos hBn)) (Qmul_comm (Qinv B) B) (Qmul_Qinv hBn)
  have hR : Req (Rmul (ofQ (Qinv B) (Qinv_den_pos hBn)) (Rmul (ofQ B hBd) (twoRad c B hcn hcd hBd x)))
      (twoRad c B hcn hcd hBd x) := by
    refine Req_trans (Req_symm (Rmul_assoc (ofQ (Qinv B) (Qinv_den_pos hBn)) (ofQ B hBd)
      (twoRad c B hcn hcd hBd x))) ?_
    refine Req_trans (Rmul_congr (Req_trans (Rmul_ofQ_ofQ (Qinv_den_pos hBn) hBd)
      (ofQ_congr (Qmul_den_pos (Qinv_den_pos hBn) hBd) (by decide) hQeq)) (Req_refl _)) ?_
    exact Rone_mul _
  exact Rle_trans (Rle_of_Req (Req_symm hL)) (Rle_trans hstep (Rle_of_Req hR))

/-- The scale witness `1 ≤ N·twoRad` (from `twoRad ≥ 1/B` and `1 ≤ N·(1/B)`). -/
theorem one_le_N_twoRad (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle one (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (twoRad c B hcn hcd hBd x)) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  have h1 : Rle one (ofQ (mul (⟨(N : Int), 1⟩ : Q) (Qinv B))
      (Qmul_den_pos Nat.one_pos (Qinv_den_pos hBn))) :=
    Rle_ofQ_ofQ (by decide) (Qmul_den_pos Nat.one_pos (Qinv_den_pos hBn))
      (one_le_N_invB hBd hB1 N hBN)
  refine Rle_trans h1 ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ Nat.one_pos (Qinv_den_pos hBn)))) ?_
  exact Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg N))
    (twoRad_ge_invB c B hcn hcd hBd hB1 hcB x)

/-- The `N²` scale witness of `RsqrtRealPos`: `1 ≤ N²·twoRad`. -/
theorem twoRad_scale (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle one (Rmul (ofQ (⟨(N : Int) * (N : Int), 1⟩ : Q) Nat.one_pos)
      (twoRad c B hcn hcd hBd x)) := by
  have hstep : Rle (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) one)
      (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)
        (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (twoRad c B hcn hcd hBd x))) :=
    Rmul_le_Rmul_left (Rnonneg_ofQ Nat.one_pos (Int.ofNat_nonneg N))
      (one_le_N_twoRad c B hcn hcd hBd hB1 hcB N hBN x)
  have hN1 : Rle one (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) :=
    Rle_ofQ_ofQ (by decide) Nat.one_pos (by simp only [Qle]; push_cast; omega)
  have hcollapse : Req (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)
        (Rmul (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos) (twoRad c B hcn hcd hBd x)))
      (Rmul (ofQ (⟨(N : Int) * (N : Int), 1⟩ : Q) Nat.one_pos) (twoRad c B hcn hcd hBd x)) := by
    refine Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_
    exact Rmul_congr (Req_trans (Rmul_ofQ_ofQ Nat.one_pos Nat.one_pos)
      (ofQ_congr (Qmul_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos
        (by simp only [Qeq, mul]; try push_cast; try ring_uor))) (Req_refl _)
  refine Rle_trans hN1 ?_
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_one (ofQ (⟨(N : Int), 1⟩ : Q) Nat.one_pos)))) ?_
  exact Rle_trans hstep (Rle_of_Req hcollapse)

-- ===========================================================================
-- (1) The two-sided weight and its certificates.
-- ===========================================================================

/-- **THE TWO-SIDED `x^{-1/2}` WEIGHT**: `invSqrtTwoF x = √(1/max(band_{[c,B]}(x), c))`. -/
def invSqrtTwoF (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) : Real :=
  RsqrtRealPos (twoRad c B hcn hcd hBd x) N hN (twoRad_scale c B hcn hcd hBd hB1 hcB N hN hBN x)

theorem invSqrtTwoF_sq (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Req (Rmul (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
              (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x))
        (twoRad c B hcn hcd hBd x) :=
  RsqrtRealPos_sq _ N hN _

theorem invSqrtTwoF_nonneg (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rnonneg (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) :=
  RsqrtRealPos_nonneg _ N hN _

/-- `invSqrtTwoF ≤ 1/c` (its square is `≤ 1/c ≤ (1/c)²`, since `c ≤ 1`). -/
theorem invSqrtTwoF_le (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) (ofQ (Qinv c) (Qinv_den_pos hcn)) := by
  have hinv1 : Qle (⟨1, 1⟩ : Q) (Qinv c) := by
    have h := hc1
    show (1 : Int) * ((c.num.toNat : Nat) : Int) ≤ (c.den : Int) * ((1 : Nat) : Int)
    simp only [Qle] at h
    push_cast [Int.toNat_of_nonneg (Int.le_of_lt hcn)] at h ⊢
    omega
  have hnn : Rnonneg (ofQ (Qinv c) (Qinv_den_pos hcn)) :=
    Rnonneg_ofQ (Qinv_den_pos hcn) (Int.le_of_lt (Qinv_num_pos hcd))
  refine Rle_of_Rsq_le (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x) hnn ?_
  refine Rle_trans (Rle_of_Req (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x)) ?_
  refine Rle_trans (twoRad_le_invc c B hcn hcd hBd x) ?_
  -- 1/c ≤ (1/c)·(1/c) since 1 ≤ 1/c
  refine Rle_trans (Rle_of_Req (Req_symm (Rmul_one _))) ?_
  exact Rmul_le_Rmul_left hnn (Rle_ofQ_ofQ (by decide) (Qinv_den_pos hcn) hinv1)

/-- `1/N ≤ invSqrtTwoF` (its square is `≥ 1/B ≥ 1/N ≥ 1/N²`). -/
theorem invSqrtTwoF_ge_invN (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x : Real) :
    Rle (ofQ (⟨1, N⟩ : Q) hN) (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x) := by
  have hBn : 0 < B.num := qnum_pos_of_one_le hBd hB1
  refine Rle_of_Rsq_le (Rnonneg_ofQ hN (by show (0 : Int) ≤ 1; decide))
    (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x) ?_
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
  exact Rle_trans (twoRad_ge_invB c B hcn hcd hBd hB1 hcB x)
    (Rle_of_Req (Req_symm (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x)))

theorem invSqrtTwoF_congr (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) {x y : Real} (h : Req x y) :
    Req (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
        (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y) :=
  RsqrtRealPos_unique (twoRad c B hcn hcd hBd y) N hN
    (twoRad_scale c B hcn hcd hBd hB1 hcB N hN hBN y)
    (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x)
    (Req_trans (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x) (twoRad_congr c B hcn hcd hBd h))

/-- **The two-sided weight is `(N/2)·(1/c)²`-Lipschitz** (`|Δs|·(s+s') = |Δrad| ≤ (1/c)²|Δx|`,
    `s, s' ≥ 1/N`). -/
theorem invSqrtTwoF_lipschitz (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) (x y : Real) :
    Rle (Rabs (Rsub (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                    (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y)))
        (Rmul (ofQ (mul (⟨(N : Int), 2⟩ : Q) (mul (Qinv c) (Qinv c)))
          (Qmul_den_pos (Nat.succ_pos 1) (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn))))
          (Rabs (Rsub x y))) := by
  have h2N : Req (ofQ (⟨2, N⟩ : Q) hN)
      (Radd (ofQ (⟨1, N⟩ : Q) hN) (ofQ (⟨1, N⟩ : Q) hN)) := by
    refine Req_trans (ofQ_congr hN (add_den_pos hN hN) ?_) (Req_symm (Radd_ofQ_ofQ hN hN))
    simp only [Qeq, add]; push_cast; ring_uor
  have h2st : Rle (ofQ (⟨2, N⟩ : Q) hN)
      (Rabs (Radd (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                  (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y))) :=
    Rle_trans (Rle_trans (Rle_of_Req h2N)
        (Radd_le_add (invSqrtTwoF_ge_invN c B hcn hcd hBd hB1 hcB N hN hBN x)
          (invSqrtTwoF_ge_invN c B hcn hcd hBd hB1 hcB N hN hBN y)))
      (Rle_Rabs_self _)
  have hprod : Req (Rmul (Rsub (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                              (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y))
        (Radd (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
              (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y)))
      (Rsub (twoRad c B hcn hcd hBd x) (twoRad c B hcn hcd hBd y)) :=
    Req_trans (Rmul_sub_add_self _ _)
      (Rsub_congr (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN x)
        (invSqrtTwoF_sq c B hcn hcd hBd hB1 hcB N hN hBN y))
  have habs : Req (Rmul
        (Rabs (Rsub (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                    (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y)))
        (Rabs (Radd (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                    (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y))))
      (Rabs (Rsub (twoRad c B hcn hcd hBd x) (twoRad c B hcn hcd hBd y))) :=
    Req_trans (Req_symm (Rabs_Rmul _ _)) (Rabs_congr hprod)
  -- |Δrad| ≤ (1/c)²·|Δband| ≤ (1/c)²·|Δx|
  have hradlip : Rle (Rabs (Rsub (twoRad c B hcn hcd hBd x) (twoRad c B hcn hcd hBd y)))
      (Rmul (ofQ (mul (Qinv c) (Qinv c)) (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn)))
        (Rabs (Rsub x y))) :=
    Rle_trans (clampedInv_lipschitz c hcn hcd (twoBand c B hcd hBd x) (twoBand c B hcd hBd y))
      (Rmul_le_Rmul_left (Rnonneg_ofQ _ (Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos hcd))
        (Int.le_of_lt (Qinv_num_pos hcd)))) (qBandQ_lipschitz c B hcd hBd x y))
  have hchain : Rle (Rmul (ofQ (⟨2, N⟩ : Q) hN)
        (Rabs (Rsub (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN x)
                    (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN y))))
      (Rmul (ofQ (mul (Qinv c) (Qinv c)) (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn)))
        (Rabs (Rsub x y))) := by
    refine Rle_trans (Rmul_le_Rmul_right (Rnonneg_Rabs _) h2st) ?_
    refine Rle_trans (Rle_of_Req (Rmul_comm _ _)) ?_
    exact Rle_trans (Rle_of_Req habs) hradlip
  -- |Δs| ≈ (N/2)·((2/N)·|Δs|) ≤ (N/2)·((1/c)²·|Δx|) ≈ ((N/2)·(1/c)²)·|Δx|
  have hcollapse : Req (Rmul (ofQ (⟨(N : Int), 2⟩ : Q) (Nat.succ_pos 1)) (ofQ (⟨2, N⟩ : Q) hN)) one := by
    refine Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos 1) hN)
      (ofQ_congr (Qmul_den_pos (Nat.succ_pos 1) hN) (by decide) ?_)
    show (N : Int) * 2 * ((1 : Nat) : Int) = 1 * ((2 * N : Nat) : Int)
    push_cast; ring_uor
  refine Rle_trans (Rle_of_Req (Req_symm (Rone_mul _))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_congr (Req_symm hcollapse) (Req_refl _))) ?_
  refine Rle_trans (Rle_of_Req (Rmul_assoc (ofQ (⟨(N : Int), 2⟩ : Q) (Nat.succ_pos 1))
    (ofQ (⟨2, N⟩ : Q) hN) _)) ?_
  refine Rle_trans (Rmul_le_Rmul_left (Rnonneg_ofQ (Nat.succ_pos 1) (Int.ofNat_nonneg N)) hchain) ?_
  refine Rle_of_Req (Req_trans (Req_symm (Rmul_assoc _ _ _)) ?_)
  exact Rmul_congr (Rmul_ofQ_ofQ (Nat.succ_pos 1)
    (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn))) (Req_refl _)

/-- **THE TWO-SIDED WEIGHT TEST** (`x^{-1/2}` on all of `[c, B]`). -/
def invSqrtTwoTest (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B) (hc1 : Qle c (⟨1, 1⟩ : Q))
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q)) : L2Test where
  f := invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN
  L := mul (⟨(N : Int), 2⟩ : Q) (mul (Qinv c) (Qinv c))
  M := Qinv c
  hLd := Qmul_den_pos (Nat.succ_pos 1) (Qmul_den_pos (Qinv_den_pos hcn) (Qinv_den_pos hcn))
  hLn := Int.mul_nonneg (Int.ofNat_nonneg N)
    (Int.mul_nonneg (Int.le_of_lt (Qinv_num_pos hcd)) (Int.le_of_lt (Qinv_num_pos hcd)))
  hMd := Qinv_den_pos hcn
  hMn := Int.le_of_lt (Qinv_num_pos hcd)
  hlip := invSqrtTwoF_lipschitz c B hcn hcd hBd hB1 hcB N hN hBN
  hfc := fun _ _ h => invSqrtTwoF_congr c B hcn hcd hBd hB1 hcB N hN hBN h
  hbd := fun x =>
    Rle_trans (Rle_of_Req (Rabs_of_nonneg (invSqrtTwoF_nonneg c B hcn hcd hBd hB1 hcB N hN hBN x)))
      (invSqrtTwoF_le c B hcn hcd hBd hB1 hcB hc1 N hN hBN x)

-- ===========================================================================
-- (2) Rational readback on the WHOLE band: `invSqrtTwoF (ofQ q) = normWeight q` for `c ≤ q ≤ B`.
-- ===========================================================================

/-- **TWO-SIDED RATIONAL READBACK**: at every rational `c ≤ q ≤ B` — integer scales AND reciprocal
    scales `1/n` (when `1/n ≥ c`) — the two-sided weight IS `normWeight q = q^{-1/2}`. -/
theorem invSqrtTwoF_ofQ (c B : Q) (hcn : 0 < c.num) (hcd : 0 < c.den) (hBd : 0 < B.den)
    (hB1 : Qle (⟨1, 1⟩ : Q) B) (hcB : Qle c B)
    (N : Nat) (hN : 0 < N) (hBN : Qle B (⟨(N : Int), 1⟩ : Q))
    (q : Q) (hqd : 0 < q.den) (hcq : Qle c q) (hqB : Qle q B) :
    Req (invSqrtTwoF c B hcn hcd hBd hB1 hcB N hN hBN (ofQ q hqd)) (normWeight q) := by
  have hqn : 0 < q.num := qnum_pos_of_le hcn hqd hcq
  have hband : Req (twoBand c B hcd hBd (ofQ q hqd)) (ofQ q hqd) :=
    qBandQ_eq_of_band (Rle_ofQ_ofQ hcd hqd hcq) (Rle_ofQ_ofQ hqd hBd hqB)
  have hrad : Req (twoRad c B hcn hcd hBd (ofQ q hqd)) (ofQ (Qinv q) (Qinv_den_pos hqn)) :=
    Req_trans (clampedInv_congr c hcn hcd hband) (clampedInv_ofQ hcn hcd hqd hqn hcq)
  have hroot : Req (Rmul (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q))
        (Rsqrt (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)))
      (twoRad c B hcn hcd hBd (ofQ q hqd)) :=
    Req_trans (Rsqrt_sq (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)) (Req_symm hrad)
  refine Req_symm (Req_trans (normWeight_pos_eq hqn) ?_)
  exact RsqrtRealPos_unique (twoRad c B hcn hcd hBd (ofQ q hqd)) N hN
    (twoRad_scale c B hcn hcd hBd hB1 hcB N hN hBN (ofQ q hqd))
    (Rsqrt_nonneg (Qinv q) (Qinv_den_pos hqn) (qinv_num_nonneg q)) hroot

end UOR.Bridge.F1Square.Square
