/-
F1 square — **the clean, reusable ζ-free coordinatewise COMPLEX-LIMIT core** (`ComplexLimitCore.lean`).

The ℓ² completion's completed inner product `⟨X, Y⟩ := lim ⟨X_n, Y_n⟩` needs a genuine limit of a Cauchy
sequence of complex numbers. This module lifts the Zeta-free real completeness engine `Analysis.Complete`
(`RReg` / `Rlim` / `Rlim_tendsTo` / `RTendsTo_unique`) to ℂ COORDINATEWISE: a complex sequence is regular
iff both its real and imaginary coordinate-sequences are regular, and its limit is the pair of the two real
limits. Everything is a one-line reduction to the real side, so the constructive-analysis content is reused,
not re-proved.

WHY A SEPARATE `…Core` FAMILY: the existing `Analysis.ComplexLimit` already defines `CReg`/`Clim`/… with the
SAME meaning, but it imports `RlimProps`, whose cone transitively reaches `Analysis.Zeta` (the ζ / crux side);
the completion's import-only-`FinDirectLimit` fence forbids it. This core re-proves ONLY the basic
coordinatewise-limit facts (which need `Complete` alone, not the Zeta-tainted `RlimProps` arithmetic), under
the `…Core` names so every leaf name stays globally UNIQUE — distinct from `ComplexLimit`'s `Clim` / `CReg` /
… — which the mechanized-honesty coverage gate requires (leaf-name match + dups guard).

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; Zeta-free cone. Crux `none`.
-/

import F1Square.Analysis.Complete
import F1Square.Analysis.Complex
import F1Square.Analysis.ROrder

namespace UOR.Bridge.F1Square.Analysis

/-- **Regularity of a complex sequence**: both coordinate real-sequences are regular (Cauchy with the
    canonical modulus). The ζ-free-core mirror of `RReg`. -/
def CRegCore (Z : Nat → Complex) : Prop :=
  RReg (fun n => (Z n).re) ∧ RReg (fun n => (Z n).im)

/-- **The coordinatewise complex limit** `lim Z := ⟨lim Re Z, lim Im Z⟩`. The ζ-free-core mirror of `Rlim`. -/
def ClimCore (Z : Nat → Complex) (h : CRegCore Z) : Complex :=
  ⟨Rlim (fun n => (Z n).re) h.1, Rlim (fun n => (Z n).im) h.2⟩

/-- The real part of the complex limit is the real limit of the real parts (definitional). -/
theorem ClimCore_re (Z : Nat → Complex) (h : CRegCore Z) :
    (ClimCore Z h).re = Rlim (fun n => (Z n).re) h.1 := rfl

/-- The imaginary part of the complex limit is the real limit of the imaginary parts (definitional). -/
theorem ClimCore_im (Z : Nat → Complex) (h : CRegCore Z) :
    (ClimCore Z h).im = Rlim (fun n => (Z n).im) h.2 := rfl

/-- **Complex convergence** `Z k → L`: both coordinate sequences converge (as reals). ζ-free-core mirror of
    `RTendsTo`. -/
def CTendsToCore (Z : Nat → Complex) (L : Complex) : Prop :=
  RTendsTo (fun n => (Z n).re) L.re ∧ RTendsTo (fun n => (Z n).im) L.im

/-- **Completeness of ℂ** (coordinatewise): every regular complex sequence converges to its complex limit. -/
theorem ClimCore_tendsTo (Z : Nat → Complex) (h : CRegCore Z) : CTendsToCore Z (ClimCore Z h) :=
  ⟨Rlim_tendsTo (fun n => (Z n).re) h.1, Rlim_tendsTo (fun n => (Z n).im) h.2⟩

/-- **Complex limits are unique up to `≈`**: if `Z → L` and `Z → L'` then `L ≈ L'` (`Ceq`), coordinatewise
    from `RTendsTo_unique`. -/
theorem CTendsToCore_unique {Z : Nat → Complex} {L L' : Complex}
    (hL : CTendsToCore Z L) (hL' : CTendsToCore Z L') : Ceq L L' :=
  ⟨RTendsTo_unique hL.1 hL'.1, RTendsTo_unique hL.2 hL'.2⟩

/-- **From a real upper bound to a same-index rational bound** (the completeness bridge, ζ-free port of
    `ComplexZeta.seq_diff_le`, renamed `_core` for leaf-uniqueness): if `a − b ≤ c` as reals (`c` a
    rational), then `aₙ − bₙ ≤ c + 2/(n+1)` at every index `n`. Regularity moves the comparison index
    `2m+1` back to `n`; the generalized Archimedean lemma kills the `3/(m+1)` tail. -/
theorem seq_diff_le_core (a b : Real) (c : Q) (hcd : 0 < c.den)
    (h : Rle (Rsub a b) (ofQ c hcd)) (n : Nat) :
    Qle (Qsub (a.seq n) (b.seq n)) (add c ⟨2, n + 1⟩) := by
  apply Qarch_gen (C := 3) (Qsub_den_pos (a.den_pos n) (b.den_pos n))
    (add_den_pos hcd (Nat.succ_pos _))
  intro m
  have hmid : Qle (Qsub (a.seq (2 * m + 1)) (b.seq (2 * m + 1))) (add c ⟨2, m + 1⟩) := h m
  have s1 : Qle (a.seq n) (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos _)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (a.reg n (2 * m + 1))
  have s2 : Qle (neg (b.seq n)) (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1)))) :=
    Qle_add_of_Qabs_sub (neg_den_pos (b.den_pos n)) (neg_den_pos (b.den_pos _))
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
      (by rw [Qabs_Qsub_neg]; exact b.reg n (2 * m + 1))
  have hp1 : Qle (Qsub (a.seq n) (b.seq n))
      (add (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1))))
           (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1))))) :=
    Qadd_le_add s1 s2
  have hreg : Qeq
      (add (add (a.seq (2 * m + 1)) (add (Qbound n) (Qbound (2 * m + 1))))
           (add (neg (b.seq (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1)))))
      (add (Qsub (a.seq (2 * m + 1)) (b.seq (2 * m + 1)))
           (add (add (Qbound n) (Qbound (2 * m + 1))) (add (Qbound n) (Qbound (2 * m + 1))))) := by
    simp only [Qeq, Qsub, add, neg, Qbound]; push_cast; ring_uor
  refine Qle_trans
    (add_den_pos (add_den_pos (a.den_pos _) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)))
      (add_den_pos (neg_den_pos (b.den_pos _)) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    hp1 ?_
  refine Qle_trans
    (add_den_pos (Qsub_den_pos (a.den_pos _) (b.den_pos _))
      (add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    (Qeq_le hreg) ?_
  exact Qle_trans
    (add_den_pos (add_den_pos hcd (Nat.succ_pos _))
      (add_den_pos (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))
        (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _))))
    (Qadd_le_add hmid (Qle_refl _))
    (Qeq_le (by simp only [Qeq, add, Qbound]; push_cast; ring_uor))

/-- **The completeness bridge to `RReg`** (ζ-free port of `ComplexZeta.RReg_of_real_bound`, renamed
    `_core`): a family `X : ℕ → ℝ` whose pairwise real differences are bounded by rationals
    `c j k ≤ 1/(j+1) + 1/(k+1)` is a regular sequence of reals — the exact input `CRegCore` needs on each
    coordinate of an inner-product sequence. -/
theorem RReg_of_real_bound_core (X : Nat → Real) (c : Nat → Nat → Q) (hcd : ∀ j k, 0 < (c j k).den)
    (hcb : ∀ j k, Qle (c j k) (add ⟨1, j + 1⟩ ⟨1, k + 1⟩))
    (hX : ∀ j k, Rle (Rsub (X j) (X k)) (ofQ (c j k) (hcd j k))) : RReg X := by
  intro j k n
  have hjk : Qle (Qsub ((X j).seq n) ((X k).seq n)) (add (c j k) ⟨2, n + 1⟩) :=
    seq_diff_le_core (X j) (X k) (c j k) (hcd j k) (hX j k) n
  have hkj : Qle (Qsub ((X k).seq n) ((X j).seq n)) (add (c k j) ⟨2, n + 1⟩) :=
    seq_diff_le_core (X k) (X j) (c k j) (hcd k j) (hX k j) n
  have hcb' : Qle (c k j) (add ⟨1, j + 1⟩ ⟨1, k + 1⟩) :=
    Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (hcb k j)
      (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  refine Qabs_le_of_both ?_ ?_
  · exact Qle_trans (add_den_pos (hcd j k) (Nat.succ_pos _)) hjk
      (Qadd_le_add (hcb j k) (Qle_refl _))
  · have hcomm : Qeq (Qsub ((X k).seq n) ((X j).seq n))
        (neg (Qsub ((X j).seq n) ((X k).seq n))) := by
      simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
    refine Qle_congr_left (Qsub_den_pos ((X k).den_pos n) ((X j).den_pos n)) hcomm ?_
    exact Qle_trans (add_den_pos (hcd k j) (Nat.succ_pos _)) hkj
      (Qadd_le_add hcb' (Qle_refl _))

-- ===========================================================================
-- NULL-DIFFERENCE LIMIT THEOREM (the completedInner_congr foundation): two regular sequences that are
-- eventually within 1/(k+1) of each other have EQUAL Bishop limits. The reusable engine for
-- representative independence of the completed inner product and the pre-Hilbert limit laws. Built by
-- the Qarch_gen constant-tolerating technique (same as RTendsTo_unique / seq_diff_le_core).
-- ===========================================================================

/-- **Real-≤ to same-index-ℚ-≤ bridge across `Radd`+`ofQ`** (the ζ-free companion of `seq_diff_le_core`):
    if `a ≤ b + c` as reals (`c` a rational), then at every index `i` the ℚ-gap satisfies
    `aᵢ ≤ bᵢ + c + 2/(i+1)`. The hypothesis reads `b` at the reindex `2m+1`; regularity of `a` and `b`
    moves the comparison back to `i`, and the generalized Archimedean lemma kills the `4/(m+1)` tail. -/
private theorem seq_le_of_Rle_Radd_ofQ (a b : Real) (c : Q) (hcd : 0 < c.den)
    (h : Rle a (Radd b (ofQ c hcd))) (i : Nat) :
    Qle (a.seq i) (add (b.seq i) (add c ⟨2, i + 1⟩)) := by
  apply Qarch_gen (C := 4) (a.den_pos i)
    (add_den_pos (b.den_pos i) (add_den_pos hcd (Nat.succ_pos _)))
  intro m
  -- hypothesis at index m: aₘ ≤ (b_{2m+1} + c) + 2/(m+1)
  have hm : Qle (a.seq m) (add (add (b.seq (2 * m + 1)) c) ⟨2, m + 1⟩) := h m
  -- regularity of a: aᵢ ≤ aₘ + (1/(i+1) + 1/(m+1))
  have s1 : Qle (a.seq i) (add (a.seq m) (add (Qbound i) (Qbound m))) :=
    Qle_add_of_Qabs_sub (a.den_pos i) (a.den_pos m)
      (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)) (a.reg i m)
  -- regularity of b (weakened 2m+1 → m): b_{2m+1} ≤ bᵢ + (1/(m+1) + 1/(i+1))
  have hbnd : Qle (Qbound (2 * m + 1)) (Qbound m) := by simp only [Qle, Qbound]; push_cast; omega
  have s3 : Qle (b.seq (2 * m + 1)) (add (b.seq i) (add (Qbound (2 * m + 1)) (Qbound i))) :=
    Qle_add_of_Qabs_sub (b.den_pos (2 * m + 1)) (b.den_pos i)
      (add_den_pos (Qbound_den_pos _) (Qbound_den_pos i)) (b.reg (2 * m + 1) i)
  have s3' : Qle (b.seq (2 * m + 1)) (add (b.seq i) (add (Qbound m) (Qbound i))) :=
    Qle_trans (add_den_pos (b.den_pos i) (add_den_pos (Qbound_den_pos _) (Qbound_den_pos i)))
      s3 (Qadd_le_add (Qle_refl (b.seq i)) (Qadd_le_add hbnd (Qle_refl (Qbound i))))
  -- chain
  have c1 : Qle (a.seq i)
      (add (add (add (b.seq (2 * m + 1)) c) ⟨2, m + 1⟩) (add (Qbound i) (Qbound m))) :=
    Qle_trans (add_den_pos (a.den_pos m) (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)))
      s1 (Qadd_le_add hm (Qle_refl _))
  have c2 : Qle (a.seq i)
      (add (add (add (add (b.seq i) (add (Qbound m) (Qbound i))) c) ⟨2, m + 1⟩)
        (add (Qbound i) (Qbound m))) :=
    Qle_trans
      (add_den_pos (add_den_pos (add_den_pos (b.den_pos _) hcd) (Nat.succ_pos _))
        (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m)))
      c1
      (Qadd_le_add (Qadd_le_add (Qadd_le_add s3' (Qle_refl c)) (Qle_refl _)) (Qle_refl _))
  refine Qle_trans ?_ c2 (Qeq_le ?_)
  · exact add_den_pos (add_den_pos (add_den_pos
      (add_den_pos (b.den_pos i) (add_den_pos (Qbound_den_pos m) (Qbound_den_pos i))) hcd)
      (Nat.succ_pos _)) (add_den_pos (Qbound_den_pos i) (Qbound_den_pos m))
  · simp only [Qeq, add, Qbound]; push_cast; ring_uor

set_option maxHeartbeats 4000000 in
/-- **The per-`m` Archimedean slice** of the one-sided limit comparison, with the comparison index `j`
    (any `j ≥ m` for which the closeness `A j ≤ B j + 1/(m+1)` holds) passed explicitly. Route: regularity
    moves `lim A`/`lim B` from `n` to `j` (two `1/(n+1)`, summing to the `2/(n+1)` slack), `Rlim_tendsTo`
    swaps in `A j`/`B j` at `j`, the closeness gives `A j ≤ B j + 1/(m+1)`; all `1/(j+1)` pieces are `≤
    ·/(m+1)` since `j ≥ m`, so the residual tail is exactly `13/(m+1)`. -/
private theorem Rle_lim_step (A B : Nat → Real) (hA : RReg A) (hB : RReg B) (n m j : Nat)
    (hjm : m ≤ j)
    (hclose : Rle (A j) (Radd (B j) (ofQ (⟨1, m + 1⟩ : Q) (Nat.succ_pos m)))) :
    Qle ((Rlim A hA).seq n)
        (add (add ((Rlim B hB).seq n) (⟨2, n + 1⟩ : Q)) (⟨13, m + 1⟩ : Q)) := by
  have hAt := Rlim_tendsTo A hA
  have hBt := Rlim_tendsTo B hB
  have hbj : Qle (Qbound j) (Qbound m) := by simp only [Qle, Qbound]; push_cast; omega
  have h2j : Qle (⟨2, j + 1⟩ : Q) (⟨2, m + 1⟩ : Q) := by simp only [Qle]; push_cast; omega
  -- s1' : (Rlim A hA)ₙ ≤ LA_j + (1/(n+1) + 1/(m+1))
  have s1 : Qle ((Rlim A hA).seq n) (add ((Rlim A hA).seq j) (add (Qbound n) (Qbound j))) :=
    Qle_add_of_Qabs_sub ((Rlim A hA).den_pos n) ((Rlim A hA).den_pos j)
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos j)) ((Rlim A hA).reg n j)
  have s1' : Qle ((Rlim A hA).seq n) (add ((Rlim A hA).seq j) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos ((Rlim A hA).den_pos j) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos j)))
      s1 (Qadd_le_add (Qle_refl ((Rlim A hA).seq j)) (Qadd_le_add (Qle_refl (Qbound n)) hbj))
  -- s2' : LA_j ≤ A_j,j + (2/(m+1) + 2/(m+1))
  have s2raw : Qle ((Rlim A hA).seq j) (add ((A j).seq j) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) := by
    have hcomm : Qle (Qabs (Qsub ((Rlim A hA).seq j) ((A j).seq j))) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q)) := by
      rw [Qabs_Qsub_comm]; exact hAt j j
    exact Qle_add_of_Qabs_sub ((Rlim A hA).den_pos j) ((A j).den_pos j)
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) hcomm
  have s2' : Qle ((Rlim A hA).seq j) (add ((A j).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((A j).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s2raw (Qadd_le_add (Qle_refl ((A j).seq j)) (Qadd_le_add h2j h2j))
  -- s3' : A_j,j ≤ B_j,j + (1/(m+1) + 2/(m+1))
  have s3raw : Qle ((A j).seq j) (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) :=
    seq_le_of_Rle_Radd_ofQ (A j) (B j) (⟨1, m + 1⟩ : Q) (Nat.succ_pos m) hclose j
  have s3' : Qle ((A j).seq j) (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((B j).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s3raw (Qadd_le_add (Qle_refl ((B j).seq j)) (Qadd_le_add (Qle_refl (⟨1, m + 1⟩ : Q)) h2j))
  -- s4' : B_j,j ≤ LB_j + (2/(m+1) + 2/(m+1))
  have s4raw : Qle ((B j).seq j) (add ((Rlim B hB).seq j) (add (⟨2, j + 1⟩ : Q) (⟨2, j + 1⟩ : Q))) :=
    Qle_add_of_Qabs_sub ((B j).den_pos j) ((Rlim B hB).den_pos j)
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (hBt j j)
  have s4' : Qle ((B j).seq j) (add ((Rlim B hB).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) :=
    Qle_trans (add_den_pos ((Rlim B hB).den_pos j) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      s4raw (Qadd_le_add (Qle_refl ((Rlim B hB).seq j)) (Qadd_le_add h2j h2j))
  -- s5' : LB_j ≤ (Rlim B hB)ₙ + (1/(m+1) + 1/(n+1))
  have s5 : Qle ((Rlim B hB).seq j) (add ((Rlim B hB).seq n) (add (Qbound j) (Qbound n))) :=
    Qle_add_of_Qabs_sub ((Rlim B hB).den_pos j) ((Rlim B hB).den_pos n)
      (add_den_pos (Qbound_den_pos j) (Qbound_den_pos n)) ((Rlim B hB).reg j n)
  have s5' : Qle ((Rlim B hB).seq j) (add ((Rlim B hB).seq n) (add (Qbound m) (Qbound n))) :=
    Qle_trans (add_den_pos ((Rlim B hB).den_pos n) (add_den_pos (Qbound_den_pos j) (Qbound_den_pos n)))
      s5 (Qadd_le_add (Qle_refl ((Rlim B hB).seq n)) (Qadd_le_add hbj (Qle_refl (Qbound n))))
  -- chain: substitute one carrier at a time
  have c1 : Qle ((Rlim A hA).seq n)
      (add (add ((A j).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos ((Rlim A hA).den_pos j) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      s1' (Qadd_le_add s2' (Qle_refl _))
  have c2 : Qle ((Rlim A hA).seq n)
      (add (add (add ((B j).seq j) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos ((A j).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c1 (Qadd_le_add (Qadd_le_add s3' (Qle_refl _)) (Qle_refl _))
  have c3 : Qle ((Rlim A hA).seq n)
      (add (add (add (add ((Rlim B hB).seq j) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (add_den_pos ((B j).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c2 (Qadd_le_add (Qadd_le_add (Qadd_le_add s4' (Qle_refl _)) (Qle_refl _)) (Qle_refl _))
  have c4 : Qle ((Rlim A hA).seq n)
      (add (add (add (add (add ((Rlim B hB).seq n) (add (Qbound m) (Qbound n)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (⟨1, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q)))
        (add (⟨2, m + 1⟩ : Q) (⟨2, m + 1⟩ : Q))) (add (Qbound n) (Qbound m))) :=
    Qle_trans (add_den_pos (add_den_pos (add_den_pos (add_den_pos ((Rlim B hB).den_pos j)
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
        (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)))
      c3 (Qadd_le_add (Qadd_le_add (Qadd_le_add (Qadd_le_add s5' (Qle_refl _)) (Qle_refl _)) (Qle_refl _))
        (Qle_refl _))
  refine Qle_trans ?_ c4 (Qeq_le ?_)
  · exact add_den_pos (add_den_pos (add_den_pos (add_den_pos
      (add_den_pos ((Rlim B hB).den_pos n) (add_den_pos (Qbound_den_pos m) (Qbound_den_pos n)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m))
  · simp only [Qeq, add, Qbound]; push_cast; ring_uor

/-- **One-sided limit comparison**: if `A n ≤ B n + 1/(k+1)` eventually (for every `k`), then the Bishop
    limits satisfy `lim A ≤ lim B`. Unfold `Rle`, apply the Archimedean lemma at each index `n`, and feed
    the per-`m` slice `Rle_lim_step` with `j := N + m` (so `j ≥ m` and the closeness `A j ≤ B j + 1/(m+1)`
    holds by `hN`). -/
private theorem Rle_lim_of_close_one_side {A B : Nat → Real} (hA : RReg A) (hB : RReg B)
    (hAB : ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            Rle (A n) (Radd (B n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))) :
    Rle (Rlim A hA) (Rlim B hB) := by
  intro n
  apply Qarch_gen (C := 13) ((Rlim A hA).den_pos n)
    (add_den_pos ((Rlim B hB).den_pos n) (Nat.succ_pos _))
  intro m
  obtain ⟨N, hN⟩ := hAB m
  exact Rle_lim_step A B hA hB n m (N + m) (Nat.le_add_left m N) (hN (N + m) (Nat.le_add_right N m))

/-- **Null-difference limit theorem** (reals): if two regular real sequences are eventually within
    `1/(k+1)` of each other (two-sided, for every `k`), their Bishop limits are equal. -/
theorem Rlim_eq_of_close {A B : Nat → Real} (hA : RReg A) (hB : RReg B)
    (hAB : ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            Rle (A n) (Radd (B n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))))
    (hBA : ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            Rle (B n) (Radd (A n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))) :
    Req (Rlim A hA) (Rlim B hB) :=
  Rle_antisymm (Rle_lim_of_close_one_side hA hB hAB) (Rle_lim_of_close_one_side hB hA hBA)

/-- **Complex lift**: two regular complex sequences eventually close in each coordinate have equal
    `ClimCore` limits. Coordinatewise reduction to `Rlim_eq_of_close` on the real and imaginary parts. -/
theorem ClimCore_eq_of_close {Z W : Nat → Complex} (hZ : CRegCore Z) (hW : CRegCore W)
    (hre : ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            Rle (Z n).re (Radd (W n).re (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))))
    (hre' : ∀ k, ∃ N, ∀ n, N ≤ n → Rle (W n).re (Radd (Z n).re (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))))
    (him : ∀ k, ∃ N, ∀ n, N ≤ n → Rle (Z n).im (Radd (W n).im (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))))
    (him' : ∀ k, ∃ N, ∀ n, N ≤ n → Rle (W n).im (Radd (Z n).im (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))) :
    Ceq (ClimCore Z hZ) (ClimCore W hW) :=
  ⟨Rlim_eq_of_close hZ.1 hW.1 hre hre', Rlim_eq_of_close hZ.2 hW.2 him him'⟩

-- ===========================================================================
-- CLEAN LIMIT LAWS (consumed by the completed-inner-product pre-Hilbert laws): Rlim respects pointwise
-- equality (Rlim_congr_core), the constant limit (Rlim_const_core), the zero limit (Rlim_zero_core), monotone/nonneg
-- (Rlim_nonneg_core), and negation (RReg_neg_core, RTendsTo_neg_core, Rlim_neg_core). Several reduce to the null-difference
-- theorem Rlim_eq_of_close; Rlim_nonneg_core reads the nonnegativity at the diagonal index 4n+3.
-- ===========================================================================

-- ============================================================================
-- Private helpers (all facts re-proved inside the ζ-free import cone of
-- `ComplexLimitCore` = Complete + Complex + ROrder + Real; the out-of-cone
-- `Rnonneg_ofQ` / `Rle_self_Radd_right` are replicated here).
-- ============================================================================

/-- The constant sequence of reals is `RReg` (its pairwise gap is `|c−c| = 0`). -/
private theorem RReg_const (c : Real) : RReg (fun _ => c) := by
  intro j k n
  show Qle (Qabs (Qsub (c.seq n) (c.seq n))) (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩)
  unfold Qle Qabs
  rw [Qsub_self_num]
  simp only [Int.natAbs_zero, Int.ofNat_zero, Int.zero_mul]
  have hden : (0 : Int) ≤ ((Qsub (c.seq n) (c.seq n)).den : Int) := Int.ofNat_nonneg _
  have hnum : (0 : Int) ≤ (add (add (⟨1, j + 1⟩ : Q) ⟨1, k + 1⟩) ⟨2, n + 1⟩).num := by
    simp only [add]
    exact Int.add_nonneg (Int.mul_nonneg (by omega) (by omega))
      (Int.mul_nonneg (by omega) (by omega))
  exact Int.mul_nonneg hnum hden

/-- `ofQ` of a non-negative rational is `Rnonneg` (local copy of the out-of-cone `Rnonneg_ofQ`). -/
private theorem Rnonneg_ofQ_h {q : Q} (hq : 0 < q.den) (hn : 0 ≤ q.num) : Rnonneg (ofQ q hq) := by
  intro n
  show (neg (Qbound n)).num * (q.den : Int) ≤ q.num * ((neg (Qbound n)).den : Int)
  have hd : (0 : Int) ≤ q.num * ((neg (Qbound n)).den : Int) :=
    Int.mul_nonneg hn (by show (0 : Int) ≤ ((neg (Qbound n)).den : Int); simp only [neg, Qbound]; omega)
  have hl : (neg (Qbound n)).num * (q.den : Int) ≤ 0 := by simp only [neg, Qbound]; push_cast; omega
  omega

/-- `a ≤ a + b` when `b ≥ 0` (local copy of the out-of-cone `Rle_self_Radd_right`). -/
private theorem Rle_self_Radd_right_h {a b : Real} (hb : Rnonneg b) : Rle a (Radd a b) := by
  intro n
  show Qle (a.seq n) (add (add (a.seq (2 * n + 1)) (b.seq (2 * n + 1))) ⟨2, n + 1⟩)
  have s1 : Qle (a.seq n) (add (a.seq (2 * n + 1)) (add (Qbound n) (Qbound (2 * n + 1)))) :=
    Qle_add_of_Qabs_sub (a.den_pos n) (a.den_pos (2 * n + 1))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos (2 * n + 1))) (a.reg n (2 * n + 1))
  refine Qle_trans (add_den_pos (a.den_pos (2 * n + 1))
      (add_den_pos (Qbound_den_pos n) (Qbound_den_pos (2 * n + 1)))) s1 ?_
  refine Qle_trans (b := add (a.seq (2 * n + 1)) (add (b.seq (2 * n + 1)) ⟨2, n + 1⟩))
    (add_den_pos (a.den_pos (2 * n + 1)) (add_den_pos (b.den_pos (2 * n + 1)) (Nat.succ_pos _)))
    ?_ (Qeq_le (by simp only [Qeq, add]; push_cast; ring_uor))
  refine Qadd_le_add (Qle_refl _) ?_
  exact Qle_trans (b := add (neg (Qbound (2 * n + 1))) ⟨2, n + 1⟩)
    (add_den_pos (neg_den_pos (Qbound_den_pos _)) (Nat.succ_pos _))
    (Qeq_le (by simp only [Qeq, add, Qbound, neg]; push_cast; ring_uor))
    (Qadd_le_add (hb (2 * n + 1)) (Qle_refl _))

/-- `y ≤ y + 1/(k+1)` (the eventual-closeness witness feeding `Rlim_eq_of_close`). -/
private theorem Rle_self_add_ofQ (y : Real) (k : Nat) :
    Rle y (Radd y (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) :=
  Rle_self_Radd_right_h (Rnonneg_ofQ_h (Nat.succ_pos k) (by show (0 : Int) ≤ 1; decide))

-- ============================================================================
-- The three target theorems.
-- ============================================================================

/-- **Limit respects `≈`**: pointwise-equal regular sequences have equal diagonal limits. -/
theorem Rlim_congr_core {X X' : Nat → Real} (hX : RReg X) (hX' : RReg X')
    (h : ∀ n, Req (X n) (X' n)) : Req (Rlim X hX) (Rlim X' hX') :=
  Rlim_eq_of_close hX hX'
    (fun k => ⟨0, fun n _ => Rle_trans (Rle_of_Req (h n)) (Rle_self_add_ofQ (X' n) k)⟩)
    (fun k => ⟨0, fun n _ => Rle_trans (Rle_of_Req (Req_symm (h n))) (Rle_self_add_ofQ (X n) k)⟩)

/-- **Limit of a constant** sequence is that constant. -/
theorem Rlim_const_core (c : Real) (hc : RReg (fun _ => c)) : Req (Rlim (fun _ => c) hc) c := by
  intro n
  simp only [Rlim_seq]
  -- goal: Qle (Qabs (Qsub (c.seq (4*n+3)) (c.seq n))) ⟨2, n+1⟩
  have h1 : Qle (Qbound (4 * n + 3)) (Qbound n) := by
    show (1 : Int) * ((n + 1 : Nat) : Int) ≤ 1 * ((4 * n + 3 + 1 : Nat) : Int)
    push_cast; omega
  have hbnd : Qle (add (Qbound (4 * n + 3)) (Qbound n)) (⟨2, n + 1⟩ : Q) := by
    refine Qle_trans (add_den_pos (Qbound_den_pos n) (Qbound_den_pos n))
      (Qadd_le_add h1 (Qle_refl (Qbound n))) ?_
    apply Qeq_le
    simp only [Qeq, add, Qbound]; push_cast; ring_uor
  exact Qle_trans (add_den_pos (Qbound_den_pos _) (Qbound_den_pos _)) (c.reg (4 * n + 3) n) hbnd

/-- **Limit of a sequence that is pointwise `0`** is `0`. -/
theorem Rlim_zero_core {X : Nat → Real} (hX : RReg X) (h : ∀ n, Req (X n) zero) :
    Req (Rlim X hX) zero :=
  Req_trans (Rlim_congr_core hX (RReg_const zero) h) (Rlim_const_core zero (RReg_const zero))

theorem RReg_neg_core {X : Nat → Real} (hX : RReg X) : RReg (fun n => Rneg (X n)) := by
  intro j k n
  show Qle (Qabs (Qsub (neg ((X j).seq n)) (neg ((X k).seq n))))
    (add (add ⟨1, j + 1⟩ ⟨1, k + 1⟩) ⟨2, n + 1⟩)
  rw [Qabs_Qsub_neg]
  exact hX j k n

theorem RTendsTo_neg_core {X : Nat → Real} {L : Real} (hT : RTendsTo X L) :
    RTendsTo (fun n => Rneg (X n)) (Rneg L) := by
  intro k n
  show Qle (Qabs (Qsub (neg ((X k).seq n)) (neg (L.seq n))))
    (add ⟨2, k + 1⟩ ⟨2, n + 1⟩)
  rw [Qabs_Qsub_neg]
  exact hT k n

theorem Rlim_nonneg_core {X : Nat → Real} (hX : RReg X) (h : ∀ n, Rnonneg (X n)) :
    Rnonneg (Rlim X hX) := by
  intro n
  rw [show (Rlim X hX).seq n = (X (4 * n + 3)).seq (4 * n + 3) from rfl]
  have hbase : Qle (neg (Qbound (4 * n + 3))) ((X (4 * n + 3)).seq (4 * n + 3)) :=
    h (4 * n + 3) (4 * n + 3)
  have hstep : Qle (neg (Qbound n)) (neg (Qbound (4 * n + 3))) := by
    show ((-1 : Int)) * ((4 * n + 3 + 1 : Nat) : Int) ≤ (-1 : Int) * ((n + 1 : Nat) : Int)
    push_cast; omega
  exact Qle_trans (neg_den_pos (Qbound_den_pos _)) hstep hbase

theorem Rlim_neg_core {X : Nat → Real} (hX : RReg X) :
    Req (Rlim (fun n => Rneg (X n)) (RReg_neg_core hX)) (Rneg (Rlim X hX)) :=
  RTendsTo_unique
    (Rlim_tendsTo (fun n => Rneg (X n)) (RReg_neg_core hX))
    (RTendsTo_neg_core (Rlim_tendsTo X hX))


-- LIMIT LINEARITY (add / rational-scalar), of-approx workhorses — consumed by the
-- completed-inner-product sesquilinearity laws (add_right / smul_right).  RReg of a
-- pointwise SUM/SCALE is FALSE at the canonical modulus (RlimProps' documented wall),
-- so the combined-sequence regularity is an explicit hypothesis, exactly as consumed.
set_option maxHeartbeats 1000000 in
/-- **Limit additivity, up to an approximation** `lim W ≈ lim X + lim Y` when `W ≈ X + Y` pointwise.
    Does NOT require the (non-derivable) regularity of `X + Y`: the GIVEN regular sequence `W` carries
    the convergence, and `W ≈ X + Y` pointwise (`happ`). Both diagonals land at the same sequence
    position `8n+7`; the bound is the `happ` error `2/(4n+4)` plus the meta-regularity gap `10/(8n+8)`,
    total `14/(8n+8) ≤ 2/(n+1)`. ζ-free port of `RlimProps.Rlim_add_of_approx_core`. -/
theorem Rlim_add_of_approx_core (W X Y : Nat → Real) (hX : RReg X) (hY : RReg Y) (hW : RReg W)
    (happ : ∀ j, Req (W j) (Radd (X j) (Y j))) :
    Req (Rlim W hW) (Radd (Rlim X hX) (Rlim Y hY)) := by
  refine Req_of_lin_bound (C := 2) (fun n => ?_)
  have hpe : 4 * (2 * n + 1) + 3 = 2 * (4 * n + 3) + 1 := by omega
  show Qle (Qabs (Qsub
      ((W (4 * n + 3)).seq (4 * n + 3))
      (add ((X (4 * (2 * n + 1) + 3)).seq (4 * (2 * n + 1) + 3))
           ((Y (4 * (2 * n + 1) + 3)).seq (4 * (2 * n + 1) + 3)))))
    (⟨2, n + 1⟩ : Q)
  rw [hpe]
  have hw0 : (0 : Nat) < ((W (4 * n + 3)).seq (4 * n + 3)).den := (W (4 * n + 3)).den_pos _
  have ha : (0 : Nat) < ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1)).den := (X (4 * n + 3)).den_pos _
  have hb : (0 : Nat) < ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)).den := (Y (4 * n + 3)).den_pos _
  have hc : (0 : Nat) < ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)).den :=
    (X (2 * (4 * n + 3) + 1)).den_pos _
  have hd : (0 : Nat) < ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)).den :=
    (Y (2 * (4 * n + 3) + 1)).den_pos _
  have hregroup : Qeq
      (Qsub (add ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)))
            (add ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1))
                 ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1))))
      (add (Qsub ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)))
           (Qsub ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
                 ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)))) := by
    simp only [Qeq, Qsub, add, neg]; push_cast; ring_uor
  have hXbd := hX (4 * n + 3) (2 * (4 * n + 3) + 1) (2 * (4 * n + 3) + 1)
  have hYbd := hY (4 * n + 3) (2 * (4 * n + 3) + 1) (2 * (4 * n + 3) + 1)
  have heq : Qeq (add (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                          ⟨2, (2 * (4 * n + 3) + 1) + 1⟩)
                     (add (add (⟨1, (4 * n + 3) + 1⟩ : Q) ⟨1, (2 * (4 * n + 3) + 1) + 1⟩)
                          ⟨2, (2 * (4 * n + 3) + 1) + 1⟩))
      (⟨10, 8 * n + 8⟩ : Q) := by
    simp only [Qeq, add]; push_cast; ring_uor
  have hinner : Qle (Qabs (Qsub
        (add ((X (4 * n + 3)).seq (2 * (4 * n + 3) + 1))
             ((Y (4 * n + 3)).seq (2 * (4 * n + 3) + 1)))
        (add ((X (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1))
             ((Y (2 * (4 * n + 3) + 1)).seq (2 * (4 * n + 3) + 1)))))
      (⟨10, 8 * n + 8⟩ : Q) := by
    refine Qle_trans (Qabs_den_pos (add_den_pos (Qsub_den_pos ha hc) (Qsub_den_pos hb hd)))
      (Qeq_le (Qabs_Qeq hregroup)) ?_
    refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos ha hc))
        (Qabs_den_pos (Qsub_den_pos hb hd)))
      (Qabs_add_le _ _) ?_
    exact Qle_trans
      (add_den_pos
        (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _))
        (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
      (Qadd_le_add hXbd hYbd) (Qeq_le heq)
  have happn := happ (4 * n + 3) (4 * n + 3)
  have hfinal : Qle (add (⟨2, (4 * n + 3) + 1⟩ : Q) ⟨10, 8 * n + 8⟩) (⟨2, n + 1⟩ : Q) := by
    have heqf : Qeq (add (⟨2, (4 * n + 3) + 1⟩ : Q) ⟨10, 8 * n + 8⟩) (⟨14, 8 * n + 8⟩ : Q) := by
      simp only [Qeq, add]; push_cast; ring_uor
    refine Qle_trans (Nat.succ_pos _) (Qeq_le heqf) ?_
    show (14 : Int) * ((n + 1 : Nat) : Int) ≤ (2 : Int) * ((8 * n + 8 : Nat) : Int)
    push_cast; omega
  refine Qle_trans
    (add_den_pos (Qabs_den_pos (Qsub_den_pos hw0 (add_den_pos ha hb)))
      (Qabs_den_pos (Qsub_den_pos (add_den_pos ha hb) (add_den_pos hc hd))))
    (Qabs_sub_triangle hw0 (add_den_pos ha hb) (add_den_pos hc hd)) ?_
  exact Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
    (Qadd_le_add happn hinner) hfinal

/-- **Limit additivity** (the task's `Rlim_add_core`, honest form): `lim (A + B) ≈ lim A + lim B`, with the
    regularity of the pointwise sum supplied as a hypothesis `hAB` (it is NOT derivable from `hA`, `hB`
    at the canonical modulus — see the header). The `W = A + B` case of `Rlim_add_of_approx_core`. -/
theorem Rlim_add_core {A B : Nat → Real} (hA : RReg A) (hB : RReg B)
    (hAB : RReg (fun n => Radd (A n) (B n))) :
    Req (Rlim (fun n => Radd (A n) (B n)) hAB) (Radd (Rlim A hA) (Rlim B hB)) :=
  Rlim_add_of_approx_core (fun n => Radd (A n) (B n)) A B hA hB hAB (fun _ => Req_refl _)

set_option maxHeartbeats 1000000 in
/-- **Scalar-multiple limit, up to an approximation** `lim W ≈ c·lim X` when `W ≈ c·X` pointwise, for
    a rational constant `c`. `W`'s regularity is GIVEN, sidestepping the non-derivable `RReg(c·X)` when
    `|c| > 1`. The core bound on `|c·X_diag − c·lim X|` is `|c.num|/(n+1)`; one `happ`-triangle (error
    `2/(4n+4)`) adds on top, `C = |c.num| + 2`. ζ-free port of `RlimProps.Rlim_ofQ_mul_of_approx`. -/
theorem Rlim_smul_ofQ_of_approx (c : Q) (hc : 0 < c.den) (W X : Nat → Real) (hX : RReg X)
    (hW : RReg W) (happ : ∀ j, Req (W j) (Rmul (ofQ c hc) (X j))) :
    Req (Rlim W hW) (Rmul (ofQ c hc) (Rlim X hX)) := by
  refine Req_of_lin_bound (C := c.num.natAbs + 2) (fun n => ?_)
  have hcore : Qle (Qabs (Qsub
      (mul c ((X (4 * n + 3)).seq (Ridx (ofQ c hc) (X (4 * n + 3)) (4 * n + 3))))
      (mul c ((X (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)).seq
              (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)))))
      (⟨(c.num.natAbs : Int), n + 1⟩ : Q) := by
    generalize hj1def : Ridx (ofQ c hc) (X (4 * n + 3)) (4 * n + 3) = j1
    generalize hj2def : Ridx (ofQ c hc) (Rlim X hX) n = j2
    have ha : (0 : Nat) < ((X (4 * n + 3)).seq j1).den := (X (4 * n + 3)).den_pos _
    have hmid : (0 : Nat) < ((X (4 * n + 3)).seq (4 * j2 + 3)).den := (X (4 * n + 3)).den_pos _
    have hb : (0 : Nat) < ((X (4 * j2 + 3)).seq (4 * j2 + 3)).den := (X (4 * j2 + 3)).den_pos _
    have hj1ge : 8 * (n + 1) ≤ j1 + 1 := by
      rw [← hj1def, Ridx_succ]
      have hk1 : 1 ≤ RmulK (ofQ c hc) (X (4 * n + 3)) := RmulK_pos _ _
      have hge : 2 * 1 * (4 * n + 3 + 1) ≤ 2 * RmulK (ofQ c hc) (X (4 * n + 3)) * (4 * n + 3 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 2) hk1) (Nat.le_refl _)
      omega
    have hj2ge : 8 * (n + 1) ≤ 4 * j2 + 4 := by
      have hs : j2 + 1 = 2 * RmulK (ofQ c hc) (Rlim X hX) * (n + 1) := by
        rw [← hj2def]; exact Ridx_succ _ _ _
      have hk2 : 1 ≤ RmulK (ofQ c hc) (Rlim X hX) := RmulK_pos _ _
      have hge : 2 * 1 * (n + 1) ≤ 2 * RmulK (ofQ c hc) (Rlim X hX) * (n + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 2) hk2) (Nat.le_refl _)
      omega
    have hQj1 : Qle (⟨1, j1 + 1⟩ : Q) (⟨1, 8 * n + 8⟩ : Q) := by
      show (1 : Int) * ((8 * n + 8 : Nat) : Int) ≤ (1 : Int) * ((j1 + 1 : Nat) : Int)
      push_cast; omega
    have hQ4j2 : Qle (⟨1, 4 * j2 + 3 + 1⟩ : Q) (⟨1, 8 * n + 8⟩ : Q) := by
      show (1 : Int) * ((8 * n + 8 : Nat) : Int) ≤ (1 : Int) * ((4 * j2 + 3 + 1 : Nat) : Int)
      push_cast; omega
    have hQ4j2' : Qle (⟨2, 4 * j2 + 3 + 1⟩ : Q) (⟨2, 8 * n + 8⟩ : Q) := by
      show (2 : Int) * ((8 * n + 8 : Nat) : Int) ≤ (2 : Int) * ((4 * j2 + 3 + 1 : Nat) : Int)
      push_cast; omega
    have hQ4n : Qle (⟨1, 4 * n + 3 + 1⟩ : Q) (⟨2, 8 * n + 8⟩ : Q) := by
      show (1 : Int) * ((8 * n + 8 : Nat) : Int) ≤ (2 : Int) * ((4 * n + 3 + 1 : Nat) : Int)
      push_cast; omega
    have hXdiff : Qle (Qabs (Qsub ((X (4 * n + 3)).seq j1) ((X (4 * j2 + 3)).seq (4 * j2 + 3))))
        (⟨7, 8 * n + 8⟩ : Q) := by
      refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos ha hmid))
          (Qabs_den_pos (Qsub_den_pos hmid hb)))
        (Qabs_sub_triangle ha hmid hb) ?_
      refine Qle_trans (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
          (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
        (Qadd_le_add ((X (4 * n + 3)).reg j1 (4 * j2 + 3))
          (hX (4 * n + 3) (4 * j2 + 3) (4 * j2 + 3))) ?_
      refine Qle_trans (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
          (add_den_pos (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
        (Qadd_le_add (Qadd_le_add hQj1 hQ4j2) (Qadd_le_add (Qadd_le_add hQ4n hQ4j2) hQ4j2')) ?_
      apply Qeq_le; simp only [Qeq, add]; push_cast; ring_uor
    have hdist : Qeq (Qsub (mul c ((X (4 * n + 3)).seq j1)) (mul c ((X (4 * j2 + 3)).seq (4 * j2 + 3))))
        (mul c (Qsub ((X (4 * n + 3)).seq j1) ((X (4 * j2 + 3)).seq (4 * j2 + 3)))) := by
      simp only [Qeq, Qsub, mul, add, neg]; push_cast; ring_uor
    have hfeq : Qeq (Qabs (Qsub (mul c ((X (4 * n + 3)).seq j1))
          (mul c ((X (4 * j2 + 3)).seq (4 * j2 + 3)))))
        (mul (Qabs c) (Qabs (Qsub ((X (4 * n + 3)).seq j1) ((X (4 * j2 + 3)).seq (4 * j2 + 3))))) := by
      rw [← Qabs_mul]; exact Qabs_Qeq hdist
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos hc) (Qabs_den_pos (Qsub_den_pos ha hb)))
      (Qeq_le hfeq) ?_
    have h78 : Qle (⟨7, 8 * n + 8⟩ : Q) (⟨1, n + 1⟩ : Q) := by
      show (7 : Int) * ((n + 1 : Nat) : Int) ≤ (1 : Int) * ((8 * n + 8 : Nat) : Int)
      push_cast; omega
    refine Qle_trans (Qmul_den_pos (Qabs_den_pos hc) (Nat.succ_pos n))
      (Qle_trans (Qmul_den_pos (Qabs_den_pos hc) (Nat.succ_pos _))
        (Qmul_le_mul_left (Qabs_num_nonneg c) hXdiff)
        (Qmul_le_mul_left (Qabs_num_nonneg c) h78)) ?_
    show ((Qabs c).num * 1) * ((n + 1 : Nat) : Int)
        ≤ (c.num.natAbs : Int) * ((Qabs c).den * (n + 1 : Nat) : Int)
    have hqn : (Qabs c).num = (c.num.natAbs : Int) := rfl
    have hqd : (Qabs c).den = c.den := rfl
    rw [hqn, hqd]
    have hA : (0 : Int) ≤ (c.num.natAbs : Int) := Int.ofNat_nonneg _
    have hD : (1 : Int) ≤ (c.den : Int) := by exact_mod_cast hc
    have hN : (0 : Int) ≤ ((n + 1 : Nat) : Int) := Int.ofNat_nonneg _
    calc ((c.num.natAbs : Int) * 1) * ((n + 1 : Nat) : Int)
        = (c.num.natAbs : Int) * (1 * ((n + 1 : Nat) : Int)) := by rw [Int.mul_assoc]
      _ ≤ (c.num.natAbs : Int) * ((c.den : Int) * ((n + 1 : Nat) : Int)) :=
          Int.mul_le_mul_of_nonneg_left
            (Int.mul_le_mul_of_nonneg_right hD hN) hA
      _ = (c.num.natAbs : Int) * (((c.den : Int)) * ((n + 1 : Nat) : Int)) := rfl
  have happn := happ (4 * n + 3) (4 * n + 3)
  show Qle (Qabs (Qsub ((W (4 * n + 3)).seq (4 * n + 3))
      (mul c ((X (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)).seq
              (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)))))
    (⟨(c.num.natAbs : Int) + 2, n + 1⟩ : Q)
  have hwd : (0 : Nat) < ((W (4 * n + 3)).seq (4 * n + 3)).den := (W (4 * n + 3)).den_pos _
  have hqa : (0 : Nat) <
      (mul c ((X (4 * n + 3)).seq (Ridx (ofQ c hc) (X (4 * n + 3)) (4 * n + 3)))).den :=
    Qmul_den_pos hc ((X (4 * n + 3)).den_pos _)
  have hqc : (0 : Nat) < (mul c ((X (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)).seq
        (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3))).den :=
    Qmul_den_pos hc ((X (4 * Ridx (ofQ c hc) (Rlim X hX) n + 3)).den_pos _)
  refine Qle_trans (add_den_pos (Qabs_den_pos (Qsub_den_pos hwd hqa))
      (Qabs_den_pos (Qsub_den_pos hqa hqc)))
    (Qabs_sub_triangle hwd hqa hqc) ?_
  refine Qle_trans (add_den_pos (Nat.succ_pos _) (Nat.succ_pos _))
    (Qadd_le_add happn hcore) ?_
  have hfin : Qeq (add (⟨2, n + 1⟩ : Q) ⟨(c.num.natAbs : Int), n + 1⟩)
      (⟨(c.num.natAbs : Int) + 2, n + 1⟩ : Q) := by
    simp only [Qeq, add]; push_cast; ring_uor
  refine Qle_trans (Nat.succ_pos _)
    (Qadd_le_add (show Qle (⟨2, (4 * n + 3) + 1⟩ : Q) (⟨2, n + 1⟩ : Q) by
        show (2 : Int) * ((n + 1 : Nat) : Int) ≤ (2 : Int) * (((4 * n + 3) + 1 : Nat) : Int)
        push_cast; omega) (Qle_refl _)) (Qeq_le hfin)

/-- **Rational-scalar limit** (the task's `Rlim_smul_ofQ`, honest form): `lim (c·A) ≈ c·lim A`, with
    the regularity of `c·A` supplied as a hypothesis `hcA` (NOT derivable from `hA` when `|c| > 1` —
    see the header). The `W = c·A` case of `Rlim_smul_ofQ_of_approx`. -/
theorem Rlim_smul_ofQ (c : Q) (hc : 0 < c.den) {A : Nat → Real} (hA : RReg A)
    (hcA : RReg (fun n => Rmul (ofQ c hc) (A n))) :
    Req (Rlim (fun n => Rmul (ofQ c hc) (A n)) hcA) (Rmul (ofQ c hc) (Rlim A hA)) :=
  Rlim_smul_ofQ_of_approx c hc (fun n => Rmul (ofQ c hc) (A n)) A hA hcA (fun _ => Req_refl _)

end UOR.Bridge.F1Square.Analysis
