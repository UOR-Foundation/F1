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

end UOR.Bridge.F1Square.Analysis
