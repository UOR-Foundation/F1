/-
F1 square — **the clean, reusable ζ-free real multiplication/order core** (`RealOrderCore.lean`).

This module extracts the generic Bishop-real multiplication-and-order lemmas that the ℓ² completion layer
needs — `ofQ` monotonicity, `Rmul`/`Radd` monotonicity, `Rnonneg` transfer across `Rsub`/`Req`, and the
`Rmul`-nonnegativity core — into ONE shared, candidate-independent module, so the completion (and the
completed-inner-product work downstream) consume them from here instead of re-copying ~190 lines privately.

WHY A SEPARATE COPY (the `_loc` suffix): the identical lemmas already exist in `Analysis.RealPow`, but that
module transitively reaches `Analysis.Zeta` (the ζ / crux side), so the completion's import-only-`FinDirectLimit`
fence forbids importing it. These are re-proved on a Zeta-free cone (only `RealSquareDefinite`, i.e.
`Real` + `ROrder` + `QOrder`). The `_loc` suffix keeps every leaf name globally UNIQUE — distinct from
`RealPow`'s `Rnonneg_Rmul` / `Rmul_le_Rmul_left` / … — which the mechanized-honesty coverage gate requires
(it matches audited theorems by short name). The proofs are ported verbatim from `RealPow`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; Zeta-free cone. Crux `none`.
-/

import F1Square.Analysis.RealSquareDefinite

namespace UOR.Bridge.F1Square.Analysis

/-- `ofQ` of a nonnegative rational is `Rnonneg`. -/
theorem Rnonneg_ofQ_loc {q : Q} (hq : 0 < q.den) (hn : 0 ≤ q.num) : Rnonneg (ofQ q hq) := by
  intro n
  show (neg (Qbound n)).num * (q.den : Int) ≤ q.num * ((neg (Qbound n)).den : Int)
  have hd : (0 : Int) ≤ q.num * ((neg (Qbound n)).den : Int) :=
    Int.mul_nonneg hn (by show (0 : Int) ≤ ((neg (Qbound n)).den : Int); simp only [neg, Qbound]; omega)
  have hl : (neg (Qbound n)).num * (q.den : Int) ≤ 0 := by simp only [neg, Qbound]; push_cast; omega
  omega

/-- `ofQ` is monotone: `a ≤ b` (rationals) gives `ofQ a ≤ ofQ b`. -/
theorem Rle_ofQ_of_Qle_loc {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) (h : Qle a b) :
    Rle (ofQ a ha) (ofQ b hb) :=
  fun n => Qle_trans (b := b) hb h (Qle_self_add (by show (0 : Int) ≤ 2; decide))

/-- `⊕`-sum of two ℝ constants is the ℝ of their ℚ-sum. -/
theorem Radd_ofQ_loc {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Radd (ofQ a ha) (ofQ b hb)) (ofQ (add a b) (add_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl (add a b))

/-- `ofQ a · ofQ b ≈ ofQ (a·b)` (both sides are the constant sequence `a·b`). -/
theorem Rmul_ofQ_ofQ_loc {a b : Q} (ha : 0 < a.den) (hb : 0 < b.den) :
    Req (Rmul (ofQ a ha) (ofQ b hb)) (ofQ (mul a b) (Qmul_den_pos ha hb)) :=
  Req_of_seq_Qeq (fun _ => Qeq_refl _)

/-- ℝ addition is monotone. Both sides reindex to `2n+1`, so the sum bound lands pointwise. -/
theorem Radd_le_add_loc {a a' b b' : Real} (ha : Rle a a') (hb : Rle b b') :
    Rle (Radd a b) (Radd a' b') := by
  intro n
  show Qle (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1)))
    (add (add (a'.seq (2 * n + 1)) (b'.seq (2 * n + 1))) ⟨2, n + 1⟩)
  have hsum := Qadd_le_add (ha (2 * n + 1)) (hb (2 * n + 1))
  refine Qle_congr_right ?_ ?_ hsum
  · exact add_den_pos (add_den_pos (a'.den_pos (2 * n + 1)) (Nat.succ_pos _))
      (add_den_pos (b'.den_pos (2 * n + 1)) (Nat.succ_pos _))
  · simp only [Qeq, add]; push_cast; ring_uor

/-- `a ≤ b ⟹ −b ≤ −a` at the ℚ level (`Qneg_le_neg` lives in the out-of-cone `Pi`). -/
theorem Qneg_le_neg_loc {a b : Q} (h : Qle a b) : Qle (neg b) (neg a) := by
  simp only [Qle, neg] at h ⊢
  have e1 : (-b.num) * (a.den : Int) = -(b.num * (a.den : Int)) := by ring_uor
  have e2 : (-a.num) * (b.den : Int) = -(a.num * (b.den : Int)) := by ring_uor
  rw [e1, e2]; omega

/-- **The integer multiplication-lower-bound core**: from four one-sided integer bounds on `A, B` and their
    denominators, `−(dA·dB) ≤ A·B·m`. The shared "one factor non-negative" argument used to derive
    `Rnonneg (Rmul x y)` from the componentwise nonnegativity of `x, y`. -/
theorem mul_lo_core_loc {A B dA dB K m : Int}
    (hdA : 0 < dA) (hdB : 0 < dB) (hK : 0 < K) (_hm : 0 < m)
    (h1 : -dA ≤ A * (2 * K * m)) (h2 : -dB ≤ B * (2 * K * m))
    (h3 : A ≤ K * dA) (h4 : B ≤ K * dB) : -(dA * dB) ≤ A * B * m := by
  have posarg : ∀ F G dF dG : Int, 0 ≤ G → 0 ≤ dF → 0 < dG →
      -dF ≤ F * (2 * K * m) → G ≤ K * dG → -(dF * dG) ≤ F * G * m := by
    intro F G dF dG hG hdF hdG hbnd hGle
    have s1 := Int.mul_le_mul_of_nonneg_right hbnd hG
    have s2 := Int.mul_le_mul_of_nonneg_left hGle hdF
    have e1 : F * (2 * K * m) * G = 2 * K * (F * G * m) := by ring_uor
    have e2 : (-dF) * G = -(dF * G) := by ring_uor
    have e3 : dF * (K * dG) = K * (dF * dG) := by ring_uor
    rw [e1, e2] at s1
    rw [e3] at s2
    have s3 : -(K * (dF * dG)) ≤ -(dF * G) := by omega
    have s4 := Int.le_trans s3 s1
    have e4 : -(K * (dF * dG)) = K * (-(dF * dG)) := by ring_uor
    have e5 : 2 * K * (F * G * m) = K * (2 * (F * G * m)) := by ring_uor
    rw [e4, e5] at s4
    have hfin : -(dF * dG) ≤ 2 * (F * G * m) := Int.le_of_mul_le_mul_left s4 hK
    have hY : 0 ≤ dF * dG := Int.mul_nonneg hdF (Int.le_of_lt hdG)
    omega
  by_cases hB : 0 ≤ B
  · exact posarg A B dA dB hB (Int.le_of_lt hdA) hdB h1 h4
  · by_cases hA : 0 ≤ A
    · have hsymm := posarg B A dB dA hA (Int.le_of_lt hdB) hdA h2 h3
      have e : B * A * m = A * B * m := by ring_uor
      have e' : dB * dA = dA * dB := by ring_uor
      rw [e, e'] at hsymm; exact hsymm
    · -- both negative ⇒ `A·B ≥ 0`
      have hAB : 0 ≤ A * B := by
        have h := Int.mul_nonneg (by omega : 0 ≤ -A) (by omega : 0 ≤ -B)
        have e : (-A) * (-B) = A * B := by ring_uor
        rw [e] at h; exact h
      have hABm : 0 ≤ A * B * m := Int.mul_nonneg hAB (Int.le_of_lt _hm)
      have hY : 0 ≤ dA * dB := Int.mul_nonneg (Int.le_of_lt hdA) (Int.le_of_lt hdB)
      omega

/-- **`Rmul` preserves nonnegativity**: `0 ≤ x`, `0 ≤ y` ⟹ `0 ≤ x·y` (via `mul_lo_core_loc` at the
    product reindex `Ridx`). -/
theorem Rnonneg_Rmul_loc {x y : Real} (hx : Rnonneg x) (hy : Rnonneg y) : Rnonneg (Rmul x y) := by
  intro n
  show Qle (neg (Qbound n)) (mul (x.seq (Ridx x y n)) (y.seq (Ridx x y n)))
  have hIeq : (Ridx x y n + 1 : Nat) = 2 * RmulK x y * (n + 1) := Ridx_succ x y n
  have h1 : -((x.seq (Ridx x y n)).den : Int)
      ≤ (x.seq (Ridx x y n)).num * (2 * (RmulK x y : Int) * ((n + 1 : Nat) : Int)) := by
    have hh := hx (Ridx x y n)
    simp only [Qle, neg, Qbound] at hh
    rw [hIeq] at hh
    push_cast at hh ⊢
    omega
  have h2 : -((y.seq (Ridx x y n)).den : Int)
      ≤ (y.seq (Ridx x y n)).num * (2 * (RmulK x y : Int) * ((n + 1 : Nat) : Int)) := by
    have hh := hy (Ridx x y n)
    simp only [Qle, neg, Qbound] at hh
    rw [hIeq] at hh
    push_cast at hh ⊢
    omega
  have h3 : (x.seq (Ridx x y n)).num ≤ (RmulK x y : Int) * (x.seq (Ridx x y n)).den := by
    have hh : Qle (x.seq (Ridx x y n)) ⟨(RmulK x y : Int), 1⟩ :=
      Qle_trans (Qabs_den_pos (x.den_pos _)) (Qle_self_Qabs _)
        (canon_bound_le (Nat.le_max_left _ _) _)
    simp only [Qle] at hh
    push_cast at hh ⊢
    omega
  have h4 : (y.seq (Ridx x y n)).num ≤ (RmulK x y : Int) * (y.seq (Ridx x y n)).den := by
    have hh : Qle (y.seq (Ridx x y n)) ⟨(RmulK x y : Int), 1⟩ :=
      Qle_trans (Qabs_den_pos (y.den_pos _)) (Qle_self_Qabs _)
        (canon_bound_le (Nat.le_max_right _ _) _)
    simp only [Qle] at hh
    push_cast at hh ⊢
    omega
  have hcore := mul_lo_core_loc (A := (x.seq (Ridx x y n)).num) (B := (y.seq (Ridx x y n)).num)
    (dA := ((x.seq (Ridx x y n)).den : Int)) (dB := ((y.seq (Ridx x y n)).den : Int))
    (K := (RmulK x y : Int)) (m := ((n + 1 : Nat) : Int))
    (by exact_mod_cast x.den_pos _) (by exact_mod_cast y.den_pos _)
    (by exact_mod_cast RmulK_pos x y) (by exact_mod_cast Nat.succ_pos n) h1 h2 h3 h4
  simp only [Qle, neg, Qbound, mul]
  push_cast at hcore ⊢
  omega

/-- `0 ≤ x` (as `Rle zero x`) ⟹ `Rnonneg x` — the order-to-nonneg bridge (Archimedean, `C := 3`). -/
theorem Rnonneg_of_Rle_zero_loc {x : Real} (h : Rle zero x) : Rnonneg x := by
  intro n
  refine Qarch_gen (C := 3) (neg_den_pos (Qbound_den_pos n)) (x.den_pos n) (fun m => ?_)
  have hs2 : Qle (⟨0, 1⟩ : Q) (add (x.seq m) ⟨2, m + 1⟩) := h m
  have hs1 : Qle (x.seq m) (add (x.seq n) (add (Qbound m) (Qbound n))) :=
    Qle_add_of_Qabs_sub (x.den_pos m) (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)) (x.reg m n)
  have hcomb : Qle (⟨0, 1⟩ : Q)
      (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩) :=
    Qle_trans (add_den_pos (x.den_pos m) (Nat.succ_pos _)) hs2 (Qadd_le_add hs1 (Qle_refl _))
  have hfinal := Qadd_le_add hcomb (Qle_refl (neg (Qbound n)))
  have hLHSeq : Qeq (neg (Qbound n)) (add (⟨0, 1⟩ : Q) (neg (Qbound n))) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  have hRHSeq : Qeq (add (add (add (x.seq n) (add (Qbound m) (Qbound n))) ⟨2, m + 1⟩)
      (neg (Qbound n))) (add (x.seq n) ⟨3, m + 1⟩) := by
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  refine Qle_trans (add_den_pos (by decide) (neg_den_pos (Qbound_den_pos n))) (Qeq_le hLHSeq) ?_
  refine Qle_trans (add_den_pos (add_den_pos (add_den_pos (x.den_pos n)
      (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n))) (Nat.succ_pos _))
      (neg_den_pos (Qbound_den_pos n))) hfinal (Qeq_le hRHSeq)

/-- **`Rnonneg` respects `≈`** — via the order bridge (`Rle` transfers across `≈` cleanly). -/
theorem Rnonneg_congr_loc {x y : Real} (h : Req x y) (hx : Rnonneg x) : Rnonneg y :=
  Rnonneg_of_Rle_zero_loc (Rle_trans (Rle_zero_of_Rnonneg hx) (Rle_of_Req h))

/-- `a ≤ b ⟹ 0 ≤ b − a`. -/
theorem Rnonneg_Rsub_of_Rle_loc {a b : Real} (h : Rle a b) : Rnonneg (Rsub b a) := by
  intro n
  show Qle (neg (Qbound n)) (add (b.seq (2 * n + 1)) (neg (a.seq (2 * n + 1))))
  have hab : Qle (a.seq (2 * n + 1)) (add (b.seq (2 * n + 1)) ⟨2, (2 * n + 1) + 1⟩) := h (2 * n + 1)
  have hsub : Qle (Qsub (a.seq (2 * n + 1)) (b.seq (2 * n + 1))) (⟨2, (2 * n + 1) + 1⟩ : Q) :=
    Qsub_le_of_le_add (b.den_pos _) (Nat.succ_pos _) hab
  have heq1 : Qeq (neg (Qbound n)) (neg (⟨2, (2 * n + 1) + 1⟩ : Q)) := by
    simp only [Qeq, neg, Qbound]; push_cast; ring_uor
  have heq2 : Qeq (neg (Qsub (a.seq (2 * n + 1)) (b.seq (2 * n + 1))))
      (add (b.seq (2 * n + 1)) (neg (a.seq (2 * n + 1)))) := by
    simp only [Qeq, neg, Qsub, add]; push_cast; ring_uor
  exact Qle_trans (neg_den_pos (Nat.succ_pos _)) (Qeq_le heq1)
    (Qle_trans (neg_den_pos (Qsub_den_pos (a.den_pos _) (b.den_pos _))) (Qneg_le_neg_loc hsub)
      (Qeq_le heq2))

/-- `0 ≤ b − a ⟹ a ≤ b` — the inverse of `Rnonneg_Rsub_of_Rle_loc` (Archimedean, `C := 2`). -/
theorem Rle_of_Rnonneg_Rsub_loc {a b : Real} (h : Rnonneg (Rsub b a)) : Rle a b := by
  intro n
  refine Qarch_gen (C := 2) (a.den_pos n) (add_den_pos (b.den_pos n) (Nat.succ_pos _)) (fun m => ?_)
  have hh : Qle (neg (Qbound m)) (add (b.seq (2 * m + 1)) (neg (a.seq (2 * m + 1)))) := h m
  have hba : Qle (a.seq (2 * m + 1)) (add (b.seq (2 * m + 1)) (Qbound m)) := by
    have h1 := Qadd_le_add (Qle_refl (a.seq (2 * m + 1))) hh
    have heL : Qeq (add (a.seq (2 * m + 1)) (neg (Qbound m)))
        (add (a.seq (2 * m + 1)) (neg (Qbound m))) := Qeq_refl _
    have heR : Qeq (add (a.seq (2 * m + 1)) (add (b.seq (2 * m + 1)) (neg (a.seq (2 * m + 1)))))
        (b.seq (2 * m + 1)) := by simp only [Qeq, add, neg]; push_cast; ring_uor
    have h2 : Qle (add (a.seq (2 * m + 1)) (neg (Qbound m))) (b.seq (2 * m + 1)) :=
      Qle_congr_right (add_den_pos (a.den_pos _)
        (add_den_pos (b.den_pos _) (neg_den_pos (a.den_pos _)))) heR h1
    have h3 := Qadd_le_add h2 (Qle_refl (Qbound m))
    refine Qle_trans (add_den_pos (add_den_pos (a.den_pos _) (neg_den_pos (Qbound_den_pos m)))
      (Qbound_den_pos m)) (Qeq_le ?_) h3
    simp only [Qeq, add, neg, Qbound]; push_cast; ring_uor
  have hregA : Qle (a.seq n) (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos _)
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)) (a.reg n (2 * m + 1))
  have hregB : Qle (b.seq (2 * m + 1)) (add (b.seq n) (add (Qbound (2 * m + 1)) (Qbound n))) :=
    Qle_add_of_Qabs_sub (b.den_pos _) (b.den_pos n)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos n)) (b.reg (2 * m + 1) n)
  have c1 : Qle (a.seq n) (add (add (b.seq (2 * m + 1)) (Qbound m)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_trans (add_den_pos (a.den_pos _) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)))
      hregA (Qadd_le_add hba (Qle_refl _))
  have c2 : Qle (a.seq n)
      (add (add (add (b.seq n) (add (Qbound (2 * m + 1)) (Qbound n))) (Qbound m))
        (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_trans (add_den_pos (add_den_pos (b.den_pos _) (Qbound_den_pos m))
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _)))
      c1 (Qadd_le_add (Qadd_le_add hregB (Qle_refl _)) (Qle_refl _))
  refine Qle_trans (add_den_pos (add_den_pos (add_den_pos (b.den_pos n)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos n))) (Qbound_den_pos m))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos _))) c2 (Qeq_le ?_)
  simp only [Qeq, add, Qbound]; push_cast; ring_uor

/-- **`Rmul` monotone in the RIGHT factor** by a nonnegative left scalar: `0 ≤ c`, `a ≤ b` ⟹ `c·a ≤ c·b`. -/
theorem Rmul_le_Rmul_left_loc {c a b : Real} (hc : Rnonneg c) (h : Rle a b) :
    Rle (Rmul c a) (Rmul c b) :=
  Rle_of_Rnonneg_Rsub_loc (Rnonneg_congr_loc (Rmul_sub_distrib c b a)
    (Rnonneg_Rmul_loc hc (Rnonneg_Rsub_of_Rle_loc h)))

/-- **`Rmul` monotone in the LEFT factor** by a nonnegative right scalar: `0 ≤ c`, `a ≤ b` ⟹ `a·c ≤ b·c`. -/
theorem Rmul_le_Rmul_right_loc {c a b : Real} (hc : Rnonneg c) (h : Rle a b) :
    Rle (Rmul a c) (Rmul b c) :=
  Rle_trans (Rle_of_Req (Rmul_comm a c))
    (Rle_trans (Rmul_le_Rmul_left_loc hc h) (Rle_of_Req (Rmul_comm c b)))

end UOR.Bridge.F1Square.Analysis
