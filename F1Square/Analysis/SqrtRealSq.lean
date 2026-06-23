/-
F1 square — constructive square root, the defining identity components: the squeeze scaffolding for
`(Rsqrt q)² = q`.

`Rsqrt q` is bracketed by the bisection endpoints `lo_n ↑ √q ↓ hi_n` with `lo² ≤ q ≤ hi²` and width
`→ 0`. The defining identity follows by squeezing `(Rsqrt q)²` and `q` between `lo_n²` and `hi_n²`.
This file builds the order components: `Qle_of_sq_le` (√ monotone on `Q`), the cross-bracket
`lo_a ≤ hi_b`, the telescoping `genSum (sqrtTerm) M ≈ ofQ (lo_M)`, `Rsqrt ≥ 0`, and the upper bracket
`Rsqrt ≤ ofQ (hi_n)`. (The lower bracket — a monotone-limit fact — and the final squeeze are the
remaining step.)

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.SqrtReal
import F1Square.Analysis.ThetaFunction

namespace UOR.Bridge.F1Square.Analysis

/-- **`√` is monotone on `Q`₊**: `0 ≤ x, 0 ≤ y, x² ≤ y² ⟹ x ≤ y`. Constructive (factor
    `y² − x² = (y−x)(y+x)`, split on the sign of `y+x`). -/
theorem Qle_of_sq_le {x y : Q} (hx : 0 ≤ x.num) (hy : 0 ≤ y.num)
    (h : Qle (mul x x) (mul y y)) : Qle x y := by
  simp only [Qle, mul] at h ⊢
  push_cast at h
  have hxd : (0 : Int) ≤ (x.den : Int) := Int.ofNat_nonneg _
  have hyd : (0 : Int) ≤ (y.den : Int) := Int.ofNat_nonneg _
  have hna : 0 ≤ x.num * (y.den : Int) := Int.mul_nonneg hx hyd
  have hnb : 0 ≤ y.num * (x.den : Int) := Int.mul_nonneg hy hxd
  have hsq : (x.num * (y.den : Int)) * (x.num * (y.den : Int))
      ≤ (y.num * (x.den : Int)) * (y.num * (x.den : Int)) := by
    have e1 : (x.num * (y.den : Int)) * (x.num * (y.den : Int))
        = x.num * x.num * ((y.den : Int) * (y.den : Int)) := by ring_uor
    have e2 : (y.num * (x.den : Int)) * (y.num * (x.den : Int))
        = y.num * y.num * ((x.den : Int) * (x.den : Int)) := by ring_uor
    rw [e1, e2]; exact h
  have hprod : (0 : Int) ≤ ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
      * ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) := by
    have e : ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
          * ((y.num * (x.den : Int)) + (x.num * (y.den : Int)))
        = (y.num * (x.den : Int)) * (y.num * (x.den : Int))
          - (x.num * (y.den : Int)) * (x.num * (y.den : Int)) := by ring_uor
    rw [e]; omega
  rcases Int.lt_trichotomy 0 ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) with hlt | heq | hgt
  · have hh : (0 : Int) * ((y.num * (x.den : Int)) + (x.num * (y.den : Int)))
        ≤ ((y.num * (x.den : Int)) - (x.num * (y.den : Int)))
          * ((y.num * (x.den : Int)) + (x.num * (y.den : Int))) := by simpa using hprod
    have hcancel := Int.le_of_mul_le_mul_right hh hlt
    omega
  · omega
  · omega

/-- `0 ≤ x.num` from `0/1 ≤ x`. -/
private theorem qnum_nonneg_of_le {x : Q} (h : Qle (⟨0, 1⟩ : Q) x) : 0 ≤ x.num := by
  simp only [Qle] at h; omega

/-- **Cross-bracket**: every lower endpoint is below every upper endpoint, `lo_a ≤ hi_b` (both
    bracket `√q`, via `Qle_of_sq_le` on `lo_a² ≤ q ≤ hi_b²`). -/
theorem sqLo_le_sqHi_cross (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) (a b : Nat) :
    Qle (sqLo q a) (sqHi q b) := by
  obtain ⟨hloa, _, _, hposa⟩ := sqrtBisect_inv q hqd hq a
  obtain ⟨_, hhib, hleb, hposb⟩ := sqrtBisect_inv q hqd hq b
  have hlonn : 0 ≤ (sqLo q a).num := qnum_nonneg_of_le hposa
  have hhinn : 0 ≤ (sqHi q b).num :=
    qnum_nonneg_of_le (Qle_trans (sqrtBisect_den_pos q hqd b).1 hposb hleb)
  exact Qle_of_sq_le hlonn hhinn (Qle_trans hqd hloa hhib)

/-- **Telescoping**: `Σ_{k<M} Δ_k ≈ lo_M` (the increments sum to the lower endpoint, `lo_0 = 0`). -/
theorem genSum_sqrtTerm_eq (q : Q) (hqd : 0 < q.den) : ∀ M,
    Req (genSum (sqrtTerm q hqd) M) (ofQ (sqLo q M) (sqrtBisect_den_pos q hqd M).1)
  | 0 => Req_symm (Req_of_seq_Qeq (fun _ => Qeq_refl _))
  | (M + 1) => by
    refine Req_trans (Radd_congr (genSum_sqrtTerm_eq q hqd M) (Req_refl _)) ?_
    refine Req_trans (Radd_ofQ_ofQ (sqrtBisect_den_pos q hqd M).1
      (Qsub_den_pos (sqrtBisect_den_pos q hqd (M + 1)).1 (sqrtBisect_den_pos q hqd M).1)) ?_
    exact ofQ_congr _ (sqrtBisect_den_pos q hqd (M + 1)).1
      (by simp only [Qeq, add, Qsub, neg]; push_cast; ring_uor)

/-- Each increment is non-negative. -/
private theorem sqrtTerm_nonneg (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) (k : Nat) :
    Rnonneg (sqrtTerm q hqd k) :=
  Rnonneg_ofQ _ (by have h := Qsub_nonneg_of_le (sqLo_mono q hqd hq k); simp only [Qle] at h; omega)

/-- **`Rsqrt q ≥ 0`** (limit of non-negative partial sums). -/
theorem Rsqrt_nonneg (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) :
    Rnonneg (Rsqrt q hqd hq) :=
  Rnonneg_Rlim_seq _ (fun j => genSum_nonneg (fun k => sqrtTerm_nonneg q hqd hq k)
    (digammaMidx (sqrtK q) j))

/-- **Upper bracket**: `Rsqrt q ≤ hi_n` for every `n` (the limit of the `lo`'s, each `≤ hi_n` by the
    cross-bracket). -/
theorem Rsqrt_le_sqHi (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) (n : Nat) :
    Rle (Rsqrt q hqd hq) (ofQ (sqHi q n) (sqrtBisect_den_pos q hqd n).2) :=
  Rlim_le_ofQ _ (sqrtBisect_den_pos q hqd n).2 (fun j =>
    Rle_trans (Rle_of_Req (genSum_sqrtTerm_eq q hqd (digammaMidx (sqrtK q) j)))
      (Rle_ofQ_ofQ (sqrtBisect_den_pos q hqd (digammaMidx (sqrtK q) j)).1
        (sqrtBisect_den_pos q hqd n).2
        (sqLo_le_sqHi_cross q hqd hq (digammaMidx (sqrtK q) j) n)))

-- ===========================================================================
-- The lower bracket (monotone-limit) and squaring-monotonicity.
-- ===========================================================================

/-- One-sided ε-collapse (real order): `a − b ≤ C/(k+1)` for all `k` ⟹ `a ≤ b`. -/
theorem Rle_of_Rsub_le_eps {a b : Real} {C : Nat}
    (h : ∀ k, Rle (Rsub a b) (ofQ (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k))) : Rle a b := by
  intro n
  have hsub : Qle (Qsub (a.seq n) (b.seq n)) (⟨2, n + 1⟩ : Q) := by
    apply Qarch_gen (C := C) (Qsub_den_pos (a.den_pos n) (b.den_pos n)) (Nat.succ_pos n)
    intro k
    exact Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
      (seq_diff_le a b (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k) (h k) n)
      (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  have h2 : Qeq (a.seq n) (add (b.seq n) (Qsub (a.seq n) (b.seq n))) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  exact Qle_congr_left (add_den_pos (b.den_pos n) (Qsub_den_pos (a.den_pos n) (b.den_pos n)))
    (Qeq_symm h2) (Qadd_le_add (Qle_refl _) hsub)

/-- From convergence, the difference `X m − L` is `≤ 2/(m+1)` (the upper rate; `Rsub` reindexes both
    terms together so no regularity slack is incurred). -/
theorem RTendsTo_Rsub_le {X : Nat → Real} {L : Real} (h : RTendsTo X L) (m : Nat) :
    Rle (Rsub (X m) L) (ofQ (⟨2, m + 1⟩ : Q) (Nat.succ_pos m)) := by
  intro n
  show Qle (add ((X m).seq (2 * n + 1)) (neg (L.seq (2 * n + 1))))
        (add (⟨2, m + 1⟩ : Q) (⟨2, n + 1⟩ : Q))
  refine Qle_trans (Qabs_den_pos (Qsub_den_pos ((X m).den_pos _) (L.den_pos _)))
    (Qle_self_Qabs (Qsub ((X m).seq (2 * n + 1)) (L.seq (2 * n + 1)))) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (h m (2 * n + 1)) ?_
  exact Qadd_le_add (Qle_refl _)
    (by show Qle (⟨2, (2 * n + 1) + 1⟩ : Q) (⟨2, n + 1⟩ : Q); simp only [Qle]; push_cast; omega)

/-- **A monotone sequence sits below its limit**: `X j ≤ lim X` (the lower-bracket engine). -/
theorem term_le_Rlim {X : Nat → Real} (hX : RReg X)
    (hmono : ∀ i j, i ≤ j → Rle (X i) (X j)) (J : Nat) : Rle (X J) (Rlim X hX) := by
  refine Rle_of_Rsub_le_eps (C := 2) (fun k => ?_)
  refine Rle_trans (Radd_le_add (hmono J (J + k) (Nat.le_add_right J k))
    (Rle_refl (Rneg (Rlim X hX)))) ?_
  refine Rle_trans (RTendsTo_Rsub_le (Rlim_tendsTo X hX) (J + k)) ?_
  exact Rle_ofQ_ofQ (Nat.succ_pos _) (Nat.succ_pos k) (by simp only [Qle]; push_cast; omega)

/-- Partial sums of non-negative terms are monotone in the upper limit. -/
theorem genSum_mono {T : Nat → Real} (hT : ∀ n, Rnonneg (T n)) (M : Nat) :
    ∀ d, Rle (genSum T M) (genSum T (M + d))
  | 0 => Rle_refl _
  | (d + 1) => by
    refine Rle_trans (genSum_mono hT M d) ?_
    refine Rle_trans (Rle_of_Req (Req_symm (Radd_zero (genSum T (M + d))))) ?_
    exact Radd_le_add (Rle_refl _) (Rle_zero_of_Rnonneg (hT (M + d)))

/-- The lower endpoints are monotone: `a ≤ b ⟹ lo_a ≤ lo_b`. -/
theorem sqLo_mono_le (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) (a : Nat) :
    ∀ d, Qle (sqLo q a) (sqLo q (a + d))
  | 0 => Qle_refl _
  | (d + 1) => Qle_trans (sqrtBisect_den_pos q hqd (a + d)).1
      (sqLo_mono_le q hqd hq a d) (sqLo_mono q hqd hq (a + d))

/-- **Lower bracket**: `lo_m ≤ Rsqrt q` for every `m` (monotone-limit). -/
theorem Rsqrt_ge_sqLo (q : Q) (hqd : 0 < q.den) (hq : Qle (⟨0, 1⟩ : Q) q) (m : Nat) :
    Rle (ofQ (sqLo q m) (sqrtBisect_den_pos q hqd m).1) (Rsqrt q hqd hq) := by
  have hmidx : m ≤ digammaMidx (sqrtK q) m := by
    have : m + 1 ≤ digammaMidx (sqrtK q) m := by
      have h1 : 1 ≤ (sqrtK q).num.toNat + 1 := Nat.le_add_left 1 _
      calc m + 1 = 1 * (m + 1) := by omega
        _ ≤ ((sqrtK q).num.toNat + 1) * (m + 1) := Nat.mul_le_mul_right _ h1
    omega
  have hmono : ∀ i j, i ≤ j → Rle (genSum (sqrtTerm q hqd) (digammaMidx (sqrtK q) i))
      (genSum (sqrtTerm q hqd) (digammaMidx (sqrtK q) j)) := by
    intro i j hij
    obtain ⟨d, hd⟩ : ∃ d, digammaMidx (sqrtK q) j = digammaMidx (sqrtK q) i + d :=
      ⟨_, (Nat.add_sub_cancel' (digammaMidx_mono (sqrtK q) hij)).symm⟩
    rw [hd]
    exact genSum_mono (fun k => sqrtTerm_nonneg q hqd hq k) (digammaMidx (sqrtK q) i) d
  refine Rle_trans (Rle_ofQ_ofQ (sqrtBisect_den_pos q hqd m).1
    (sqrtBisect_den_pos q hqd (digammaMidx (sqrtK q) m)).1
    (by have := sqLo_mono_le q hqd hq m (digammaMidx (sqrtK q) m - m)
        rwa [Nat.add_sub_cancel' hmidx] at this)) ?_
  exact Rle_trans (Rle_of_Req (Req_symm (genSum_sqrtTerm_eq q hqd (digammaMidx (sqrtK q) m))))
    (term_le_Rlim _ hmono m)

/-- **Squaring is monotone on non-negatives**: `0 ≤ a ≤ b ⟹ a² ≤ b²`. -/
theorem Rsq_mono {a b : Real} (ha : Rnonneg a) (hb : Rnonneg b) (h : Rle a b) :
    Rle (Rmul a a) (Rmul b b) :=
  Rle_trans (Rmul_le_Rmul_left ha h) (Rmul_le_Rmul_right hb h)

end UOR.Bridge.F1Square.Analysis
