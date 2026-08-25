/-
F1 square — **rational density for Lipschitz identities** (`WeilDensity.lean`): two rational-Lipschitz
real functions that agree at every rational of a band agree at every real of the band.

  • `Rabs_sub_ofQ_seq_le` — a real is within `1/(n+1)` of its own `n`-th rational approximant:
    `|x − ofQ (x.seq n)| ≤ 1/(n+1)` (Bishop regularity, index-doubled through `Rsub`).
  • `Req_of_Rabs_le_lin` — `|u − v| ≤ C/(n+1)` for all `n` forces `u ≈ v` (`Req_of_lin_bound`).
  • `Req_of_lipschitz_dense` — the DENSITY PRINCIPLE: `F, G` rational-Lipschitz, `F (ofQ q) ≈ G (ofQ q)`
    for every rational `lo ≤ q ≤ hi`, then `F x ≈ G x` for every real `lo ≤ x ≤ hi` (approximate
    `x` by the band-clamped approximants `(qBandQ lo hi x).seq n`, which are rationals of the band).

This is the tool that lifts the RATIONAL-scale reciprocity `H_q(f,g) = H_{1/q}(g,f)` to REAL scales.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Square.WeilCrossFTwo

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- (1) A real is `1/(n+1)`-close to its `n`-th approximant.
-- ===========================================================================

/-- **`|x − ofQ (x.seq n)| ≤ 1/(n+1)`** — per index `k`, the entry is `|x_{2k+1} − x_n| ≤
    1/(2k+2) + 1/(n+1) ≤ 1/(n+1) + 2/(k+1)` (regularity). -/
theorem Rabs_sub_ofQ_seq_le (x : Real) (n : Nat) :
    Rle (Rabs (Rsub x (ofQ (x.seq n) (x.den_pos n)))) (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) := by
  intro k
  show Qle (Qabs (add (x.seq (2 * k + 1)) (neg (x.seq n)))) (add (⟨1, n + 1⟩ : Q) (⟨2, k + 1⟩ : Q))
  have hreg := x.reg (2 * k + 1) n
  -- hreg : |x_{2k+1} − x_n| ≤ 1/(2k+2) + 1/(n+1)
  -- 1/(2k+2) + 1/(n+1) ≈ 1/(n+1) + 1/(2k+2) ≤ 1/(n+1) + 2/(k+1)
  have h1 : Qle (Qbound n) (⟨1, n + 1⟩ : Q) := Qle_refl _
  have h2 : Qle (Qbound (2 * k + 1)) (⟨2, k + 1⟩ : Q) := by
    show (1 : Int) * ((k + 1 : Nat) : Int) ≤ 2 * ((2 * k + 1 + 1 : Nat) : Int)
    push_cast; omega
  refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) hreg ?_
  refine Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
    (Qeq_le (Qadd_comm (Qbound (2 * k + 1)) (Qbound n))) ?_
  exact Qadd_le_add h1 h2

-- ===========================================================================
-- (2) `|u − v| ≤ C/(n+1)` for all `n` forces `u ≈ v`.
-- ===========================================================================

/-- `neg (a − b) ≈ b − a` at the rational level. -/
theorem Qneg_Qsub_eq (a b : Q) : Qeq (neg (Qsub a b)) (Qsub b a) := by
  simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor

/-- **Real-level linear bound gives equality**: `|u − v| ≤ C/(n+1)` for every `n` ⟹ `u ≈ v`. -/
theorem Req_of_Rabs_le_lin {u v : Real} (C : Nat)
    (h : ∀ n, Rle (Rabs (Rsub u v)) (ofQ (⟨(C : Int), n + 1⟩ : Q) (Nat.succ_pos n))) : Req u v := by
  refine Req_of_lin_bound (C := C + 2) (fun k => ?_)
  have h1 : Rle (Rsub u v) (ofQ (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k)) := Rle_of_Rabs_le (h k)
  have hflip : Req (Rabs (Rsub v u)) (Rabs (Rsub u v)) :=
    Req_trans (Req_symm (Rabs_Rneg _)) (Rabs_congr (Rneg_Rsub _ _))
  have h2 : Rle (Rsub v u) (ofQ (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k)) :=
    Rle_of_Rabs_le (Rle_trans (Rle_of_Req hflip) (h k))
  have s1 := seq_diff_le u v (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k) h1 k
  have s2 := seq_diff_le v u (⟨(C : Int), k + 1⟩ : Q) (Nat.succ_pos k) h2 k
  have hsum : Qeq (add (⟨(C : Int), k + 1⟩ : Q) (⟨2, k + 1⟩ : Q)) (⟨((C + 2 : Nat) : Int), k + 1⟩ : Q) := by
    simp only [Qeq, add]; push_cast; ring_uor
  have hden : 0 < (add (⟨(C : Int), k + 1⟩ : Q) (⟨2, k + 1⟩ : Q)).den :=
    add_den_pos (Nat.succ_pos k) (Nat.succ_pos k)
  refine Qle_trans hden ?_ (Qeq_le hsum)
  refine Qabs_le_of_both s1 ?_
  exact Qle_trans (Qsub_den_pos (v.den_pos k) (u.den_pos k))
    (Qeq_le (Qneg_Qsub_eq (u.seq k) (v.seq k))) s2

-- ===========================================================================
-- (3) The density principle.
-- ===========================================================================

/-- Real triangle for differences (local copy): `|A−C| ≤ |A−B| + |B−C|`. -/
theorem Rabs_sub_tri (A B C : Real) :
    Rle (Rabs (Rsub A C)) (Radd (Rabs (Rsub A B)) (Rabs (Rsub B C))) :=
  Rle_trans (Rle_of_Req (Rabs_congr (Req_symm (Rsub_telescope A B C)))) (Rabs_Radd _ _)

/-- An integer cap of a non-negative rational: `L ≤ ⌊L⌋+1`. -/
theorem Qle_num_cap (L : Q) (hLd : 0 < L.den) (hLn : 0 ≤ L.num) :
    Qle L (⟨((L.num.toNat + 1 : Nat) : Int), 1⟩ : Q) := by
  show L.num * ((1 : Nat) : Int) ≤ ((L.num.toNat + 1 : Nat) : Int) * (L.den : Int)
  push_cast [Int.toNat_of_nonneg hLn]
  have h1 : L.num * 1 ≤ (L.num + 1) * 1 := by omega
  have h2 : (L.num + 1) * 1 ≤ (L.num + 1) * (L.den : Int) :=
    Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

/-- **THE DENSITY PRINCIPLE**: two rational-Lipschitz real functions agreeing at every rational of
    the band `[lo, hi]` agree at every real of the band.  Approximate `x` by the band-clamped
    approximants `(qBandQ lo hi x).seq n` (rationals of the band within `1/(n+1)`), triangle through
    the common rational value, and close by `Req_of_Rabs_le_lin`. -/
theorem Req_of_lipschitz_dense (F G : Real → Real) (LF LG : Q)
    (hLFd : 0 < LF.den) (hLFn : 0 ≤ LF.num) (hLGd : 0 < LG.den) (hLGn : 0 ≤ LG.num)
    (hlipF : ∀ x y, Rle (Rabs (Rsub (F x) (F y))) (Rmul (ofQ LF hLFd) (Rabs (Rsub x y))))
    (hlipG : ∀ x y, Rle (Rabs (Rsub (G x) (G y))) (Rmul (ofQ LG hLGd) (Rabs (Rsub x y))))
    (lo hi : Q) (hlod : 0 < lo.den) (hhid : 0 < hi.den) (hlohi : Qle lo hi)
    (hrat : ∀ (q : Q) (hqd : 0 < q.den), Qle lo q → Qle q hi → Req (F (ofQ q hqd)) (G (ofQ q hqd)))
    (x : Real) (hxlo : Rle (ofQ lo hlod) x) (hxhi : Rle x (ofQ hi hhid)) :
    Req (F x) (G x) := by
  have hLd : 0 < (add LF LG).den := add_den_pos hLFd hLGd
  have hLn : 0 ≤ (add LF LG).num := Qadd_num_nonneg_loc hLFn hLGn
  refine Req_of_Rabs_le_lin ((add LF LG).num.toNat + 1) (fun n => ?_)
  -- the band approximant
  have hband : Req (qBandQ lo hi hlod hhid x) x := qBandQ_eq_of_band hxlo hxhi
  have hqd := (qBandQ lo hi hlod hhid x).den_pos n
  have hloq : Qle lo ((qBandQ lo hi hlod hhid x).seq n) := qBandQ_ge lo hi hlod hhid hlohi x n
  have hqhi : Qle ((qBandQ lo hi hlod hhid x).seq n) hi := qBandQ_le lo hi hlod hhid x n
  have hclose : Rle (Rabs (Rsub x (ofQ ((qBandQ lo hi hlod hhid x).seq n) hqd)))
      (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) :=
    Rle_trans (Rle_of_Req (Rabs_congr (Rsub_congr (Req_symm hband) (Req_refl _))))
      (Rabs_sub_ofQ_seq_le (qBandQ lo hi hlod hhid x) n)
  have hclose' : Rle (Rabs (Rsub (ofQ ((qBandQ lo hi hlod hhid x).seq n) hqd) x))
      (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)) :=
    Rle_trans (Rle_of_Req (Req_trans (Req_symm (Rabs_Rneg _)) (Rabs_congr (Rneg_Rsub _ _)))) hclose
  have hmid := hrat _ hqd hloq hqhi
  -- |F x − G x| ≤ |F x − F q| + |F q − G x| ≤ |F x − F q| + (|F q − G q| + |G q − G x|)
  refine Rle_trans (Rabs_sub_tri (F x) (F (ofQ _ hqd)) (G x)) ?_
  refine Rle_trans (Radd_le_add (Rle_refl _)
    (Rabs_sub_tri (F (ofQ _ hqd)) (G (ofQ _ hqd)) (G x))) ?_
  have hA : Rle (Rabs (Rsub (F x) (F (ofQ _ hqd))))
      (Rmul (ofQ LF hLFd) (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))) :=
    Rle_trans (hlipF _ _) (Rmul_le_Rmul_left (Rnonneg_ofQ hLFd hLFn) hclose)
  have hB : Rle (Rabs (Rsub (F (ofQ _ hqd)) (G (ofQ _ hqd)))) zero :=
    Rle_of_Req (Req_trans (Rabs_congr (Req_trans (Rsub_congr hmid (Req_refl _)) (Radd_neg _)))
      Rabs_zero)
  have hC : Rle (Rabs (Rsub (G (ofQ _ hqd)) (G x)))
      (Rmul (ofQ LG hLGd) (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n))) :=
    Rle_trans (hlipG _ _) (Rmul_le_Rmul_left (Rnonneg_ofQ hLGd hLGn) hclose')
  refine Rle_trans (Radd_le_add hA (Radd_le_add hB hC)) ?_
  -- LF·(1/(n+1)) + (0 + LG·(1/(n+1))) ≈ (LF+LG)/(n+1) ≤ cap/(n+1)
  have hcollapse : Req (Radd (Rmul (ofQ LF hLFd) (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)))
        (Radd zero (Rmul (ofQ LG hLGd) (ofQ (⟨1, n + 1⟩ : Q) (Nat.succ_pos n)))))
      (ofQ (mul (add LF LG) (⟨1, n + 1⟩ : Q)) (Qmul_den_pos hLd (Nat.succ_pos n))) := by
    refine Req_trans (Radd_congr (Rmul_ofQ_ofQ hLFd (Nat.succ_pos n))
      (Req_trans (Radd_comm zero _) (Req_trans (Radd_zero _) (Rmul_ofQ_ofQ hLGd (Nat.succ_pos n))))) ?_
    refine Req_trans (Radd_ofQ_ofQ (Qmul_den_pos hLFd (Nat.succ_pos n))
      (Qmul_den_pos hLGd (Nat.succ_pos n))) ?_
    refine ofQ_congr (add_den_pos (Qmul_den_pos hLFd (Nat.succ_pos n))
      (Qmul_den_pos hLGd (Nat.succ_pos n))) (Qmul_den_pos hLd (Nat.succ_pos n)) ?_
    simp only [Qeq, add, mul]; push_cast; ring_uor
  refine Rle_trans (Rle_of_Req hcollapse) ?_
  refine Rle_ofQ_ofQ (Qmul_den_pos hLd (Nat.succ_pos n)) (Nat.succ_pos n) ?_
  -- (LF+LG)·(1/(n+1)) ≤ cap/(n+1)
  have hcap := Qle_num_cap (add LF LG) hLd hLn
  show (mul (add LF LG) (⟨1, n + 1⟩ : Q)).num * ((n + 1 : Nat) : Int)
    ≤ (((add LF LG).num.toNat + 1 : Nat) : Int) * ((mul (add LF LG) (⟨1, n + 1⟩ : Q)).den : Int)
  show ((add LF LG).num * 1) * ((n + 1 : Nat) : Int)
    ≤ (((add LF LG).num.toNat + 1 : Nat) : Int) * (((add LF LG).den * (n + 1) : Nat) : Int)
  have hc := hcap
  simp only [Qle] at hc
  push_cast [Int.toNat_of_nonneg hLn] at hc ⊢
  -- hc : num·1 ≤ (num+1)·den ; goal : num·1·(n+1) ≤ (num+1)·(den·(n+1))
  have hn1 : (0 : Int) ≤ ((n : Int) + 1) := by omega
  calc (add LF LG).num * 1 * ((n : Int) + 1)
      = ((add LF LG).num * 1) * ((n : Int) + 1) := by ring_uor
    _ ≤ (((add LF LG).num + 1) * ((add LF LG).den : Int)) * ((n : Int) + 1) :=
        Int.mul_le_mul_of_nonneg_right hc hn1
    _ = ((add LF LG).num + 1) * (((add LF LG).den : Int) * ((n : Int) + 1)) := by ring_uor

end UOR.Bridge.F1Square.Square
