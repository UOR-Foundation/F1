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

end UOR.Bridge.F1Square.Analysis
