/-
F1 square — **the completed inner product on the ℓ² completion** (`DlimCompletedInner.lean`).

This is the CONSUMER layer the operator contract needs: it takes the completion carrier
`DLimCompletionRaw` (from `DlimHilbertCompletion`) and the ζ-free coordinatewise complex-limit engine
`ClimCore` (from `ComplexLimitCore`) and builds the genuine completed inner product
`⟨X,Y⟩ := lim ⟨X_{σn}, Y_{σn}⟩` as a constructive limit — closing the reviewer's "orphan substrate"
concern by consuming BOTH modules.

WHAT IS BUILT (reviewer gate, steps 1–3 + the step-5 definition):
- The **constructive complex Cauchy–Schwarz** for `dlimInner`, in its sqrt-free AM-GM/polarization form
  (`dlimInner_re_amgm`, in `DlimHilbertCompletion`) and packaged as the reusable single-term bound
  `dlimInner_re_termBound` (`Re⟨u,v⟩ ≤ e·(1+B)/2` given `‖u‖²≤e²`, `‖v‖²≤B`). NO `√`, NO discriminant.
- The **uniform squared-norm bound** `normBound`/`normBound_spec` for completion representatives.
- The **regularity** of the rescheduled inner-product sequence `innerSeq_CRegCore` — both coordinate
  real-sequences of `n ↦ ⟨X_{σn}, Y_{σn}⟩` are `RReg`, via the difference split + the single-term bound on
  each of the four sub-terms (the imaginary coordinate handled by the `(−i)`-twist `dlimInner_im_eq_re`),
  with the reschedule factor `F = 2 + normBound X + normBound Y` shrinking the constant onto RReg's exact
  modulus `1/(j+1)+1/(k+1)` (`modulus_bound`, which reduces to `2+BX+BY ≤ 2F`).
- **THE COMPLETED INNER PRODUCT** `completedInner X Y := ClimCore (n ↦ ⟨X_{σn},Y_{σn}⟩)`.

STILL OPEN (flagged honestly — the next gate): representative independence, the complex limit congruence /
add / scalar / conjugation limit laws, and the Hermitian / sesquilinear / positivity / definiteness
pre-Hilbert laws that package `completedInner` into a completed pre-Hilbert object. This module DEFINES the
completed inner product and proves its regularity; it does NOT yet claim the pre-Hilbert axioms, a completed
Hilbert space, an operator, or self-adjointness.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; Zeta-free cone. Crux `none`.
-/

import F1Square.Square.DlimHilbertCompletion
import F1Square.Analysis.ComplexLimitCore

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

/-- The half-bound rational `e·(1+B)/2` — the single-term Cauchy–Schwarz bound's value (matches
    `dlimInner_re_termBound`'s RHS). -/
def halfBound (e : Q) (B : Nat) : Q := ⟨e.num * (1 + (B : Int)), e.den * 2⟩

/-- **The modulus inequality**: with reschedule factor `F` satisfying `2+BX+BY ≤ 2F`, the sum of the two
    half-bounds at the rescheduled modulus `e = 1/(Fp)+1/(Fq)` is `≤ 1/p + 1/q` (RReg's target modulus).
    After clearing the common positive factor `2F³p²q²(p+q)`, the whole inequality reduces to
    `2+BX+BY ≤ 2F` — which the choice `F = 2+BX+BY` satisfies with room to spare. -/
theorem modulus_bound (F p q BX BY : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) (_hFpos : 1 ≤ F)
    (hF : 2 + BX + BY ≤ 2 * F) :
    Qle (add (halfBound (add (⟨1, F * p⟩ : Q) (⟨1, F * q⟩ : Q)) BY)
             (halfBound (add (⟨1, F * p⟩ : Q) (⟨1, F * q⟩ : Q)) BX))
        (add (⟨1, p⟩ : Q) (⟨1, q⟩ : Q)) := by
  simp only [Qle, halfBound, add, mul]
  push_cast
  refine Int.le_of_sub_nonneg ?_
  have hid :
      (1 * (q : Int) + 1 * (p : Int))
          * ((F : Int) * p * ((F : Int) * q) * 2 * ((F : Int) * p * ((F : Int) * q) * 2))
      - ((1 * ((F : Int) * q) + 1 * ((F : Int) * p)) * (1 + (BY : Int))
            * ((F : Int) * p * ((F : Int) * q) * 2)
          + (1 * ((F : Int) * q) + 1 * ((F : Int) * p)) * (1 + (BX : Int))
            * ((F : Int) * p * ((F : Int) * q) * 2)) * ((p : Int) * q)
      = 2 * ((F : Int) * F * F) * ((p : Int) * p) * ((q : Int) * q) * ((p : Int) + q)
          * (2 * (F : Int) - (2 + (BX : Int) + (BY : Int))) := by ring_uor
  rw [hid]
  have h2F : (0 : Int) ≤ 2 * (F : Int) - (2 + (BX : Int) + (BY : Int)) := by
    have : (2 : Int) + (BX : Int) + (BY : Int) ≤ 2 * (F : Int) := by exact_mod_cast hF
    omega
  have hFn : (0 : Int) ≤ (F : Int) := by exact_mod_cast Nat.zero_le F
  have hpn : (0 : Int) ≤ (p : Int) := by exact_mod_cast Nat.zero_le p
  have hqn : (0 : Int) ≤ (q : Int) := by exact_mod_cast Nat.zero_le q
  apply Int.mul_nonneg
  apply Int.mul_nonneg
  apply Int.mul_nonneg
  apply Int.mul_nonneg
  · exact Int.mul_nonneg (by decide) (Int.mul_nonneg (Int.mul_nonneg hFn hFn) hFn)
  · exact Int.mul_nonneg hpn hpn
  · exact Int.mul_nonneg hqn hqn
  · omega
  · exact h2F

/-- `0 + x ≈ x`. -/
private theorem zero_Radd_loc' (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- `(A − C) + (C − D) ≈ A − D` (the middle terms telescope). -/
private theorem radd_cancel_mid (A C D : Real) :
    Req (Radd (Radd A (Rneg C)) (Radd C (Rneg D))) (Rsub A D) :=
  Req_trans (Radd_assoc A (Rneg C) (Radd C (Rneg D)))
    (Radd_congr (Req_refl A)
      (Req_trans (Req_symm (Radd_assoc (Rneg C) C (Rneg D)))
        (Req_trans (Radd_congr (Req_trans (Radd_comm (Rneg C) C) (Radd_neg C)) (Req_refl (Rneg D)))
          (zero_Radd_loc' (Rneg D)))))

/-- **The Re difference split**: `Re⟨a_j,b_j⟩ − Re⟨a_k,b_k⟩ = Re⟨a_j−a_k,b_j⟩ + Re⟨a_k,b_j−b_k⟩`. -/
theorem innerSeq_re_split (aj ak bj bk : DLimRaw) :
    Req (Rsub (dlimInner aj bj).re (dlimInner ak bk).re)
        (Radd (dlimInner (dlimSub aj ak) bj).re (dlimInner ak (dlimSub bj bk)).re) := by
  have h1 : Req (dlimInner (dlimSub aj ak) bj).re
      (Radd (dlimInner aj bj).re (Rneg (dlimInner ak bj).re)) := (dlimInner_sub_left aj ak bj).1
  have h2 : Req (dlimInner ak (dlimSub bj bk)).re
      (Radd (dlimInner ak bj).re (Rneg (dlimInner ak bk).re)) := (dlimInner_sub_right ak bj bk).1
  exact Req_symm (Req_trans (Radd_congr h1 h2)
    (radd_cancel_mid (dlimInner aj bj).re (dlimInner ak bj).re (dlimInner ak bk).re))

/-- **The Im difference split**: same shape as Re (Im is additive over `Cadd`, negates over `Cneg`). -/
theorem innerSeq_im_split (aj ak bj bk : DLimRaw) :
    Req (Rsub (dlimInner aj bj).im (dlimInner ak bk).im)
        (Radd (dlimInner (dlimSub aj ak) bj).im (dlimInner ak (dlimSub bj bk)).im) := by
  have h1 : Req (dlimInner (dlimSub aj ak) bj).im
      (Radd (dlimInner aj bj).im (Rneg (dlimInner ak bj).im)) := (dlimInner_sub_left aj ak bj).2
  have h2 : Req (dlimInner ak (dlimSub bj bk)).im
      (Radd (dlimInner ak bj).im (Rneg (dlimInner ak bk).im)) := (dlimInner_sub_right ak bj bk).2
  exact Req_symm (Req_trans (Radd_congr h1 h2)
    (radd_cancel_mid (dlimInner aj bj).im (dlimInner ak bj).im (dlimInner ak bk).im))

/-- **The choice-free reschedule factor** absorbing the uniform-norm constant into RReg's modulus:
    `F = 2 + normBound X + normBound Y`. -/
def Fsched (X Y : DLimCompletionRaw) : Nat := 2 + normBound X + normBound Y

theorem one_le_Fsched (X Y : DLimCompletionRaw) : 1 ≤ Fsched X Y := by unfold Fsched; omega

/-- `σ_F(n) + 1 = F·(n+1)`: the rescheduled index's successor collapses the affine `−1`. -/
private theorem sched_succ (F n : Nat) (hF : 1 ≤ F) : F * (n + 1) - 1 + 1 = F * (n + 1) := by
  have : 0 < F * (n + 1) := Nat.mul_pos hF (Nat.succ_pos n); omega

/-- **The Re-coordinate difference bound**: the real part of the rescheduled inner-product sequence has
    pairwise difference `≤ 1/(j+1) + 1/(k+1)` (RReg's modulus, exactly). Difference split + the single-term
    Cauchy–Schwarz bound on each half + the reschedule modulus inequality. -/
theorem innerSeq_re_bound (X Y : DLimCompletionRaw) (j k : Nat) :
    Rle (Rsub (dlimInner (X.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (j + 1) - 1))).re
              (dlimInner (X.seq (Fsched X Y * (k + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1))).re)
        (ofQ (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
             (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))) := by
  have hF1 : 1 ≤ Fsched X Y := one_le_Fsched X Y
  have hed : 0 < (add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q)
                      (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q)).den :=
    add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hen : 0 < (add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q)
                      (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q)).num := by
    show 0 < (1 : Int) * (((Fsched X Y * (k + 1) - 1) + 1 : Nat) : Int)
           + (1 : Int) * (((Fsched X Y * (j + 1) - 1) + 1 : Nat) : Int)
    push_cast; omega
  have ht1 := dlimInner_re_termBound
    (e := add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q) (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q))
    hed hen (normBound Y) (dlimSub (X.seq (Fsched X Y * (j + 1) - 1)) (X.seq (Fsched X Y * (k + 1) - 1)))
    (Y.seq (Fsched X Y * (j + 1) - 1))
    (X.reg (Fsched X Y * (j + 1) - 1) (Fsched X Y * (k + 1) - 1))
    (normBound_spec Y (Fsched X Y * (j + 1) - 1))
  have hconj : Req (dlimInner (X.seq (Fsched X Y * (k + 1) - 1))
        (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))).re
      (dlimInner (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))
        (X.seq (Fsched X Y * (k + 1) - 1))).re :=
    (dlimInner_conj (X.seq (Fsched X Y * (k + 1) - 1))
      (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))).1
  have ht2 := dlimInner_re_termBound
    (e := add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q) (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q))
    hed hen (normBound X) (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))
    (X.seq (Fsched X Y * (k + 1) - 1))
    (Y.reg (Fsched X Y * (j + 1) - 1) (Fsched X Y * (k + 1) - 1))
    (normBound_spec X (Fsched X Y * (k + 1) - 1))
  refine Rle_trans (Rle_of_Req (innerSeq_re_split (X.seq (Fsched X Y * (j + 1) - 1))
    (X.seq (Fsched X Y * (k + 1) - 1)) (Y.seq (Fsched X Y * (j + 1) - 1))
    (Y.seq (Fsched X Y * (k + 1) - 1)))) ?_
  refine Rle_trans (Radd_le_add_loc ht1 (Rle_trans (Rle_of_Req hconj) ht2)) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_loc
    (Nat.mul_pos hed (by decide)) (Nat.mul_pos hed (by decide)))) ?_
  refine Rle_ofQ_of_Qle_loc _ _ ?_
  have esj : Fsched X Y * (j + 1) - 1 + 1 = Fsched X Y * (j + 1) := sched_succ _ _ hF1
  have esk : Fsched X Y * (k + 1) - 1 + 1 = Fsched X Y * (k + 1) := sched_succ _ _ hF1
  rw [esj, esk]
  exact modulus_bound (Fsched X Y) (j + 1) (k + 1) (normBound X) (normBound Y)
    (Nat.succ_pos j) (Nat.succ_pos k) hF1 (by unfold Fsched; omega)

/-- **The Im-coordinate difference bound** — the imaginary part reduced to the real case by the `(−i)`
    twist (`dlimInner_im_eq_re`, `dlimNormSq_smul_negI`), then the same single-term bound + modulus
    inequality. -/
theorem innerSeq_im_bound (X Y : DLimCompletionRaw) (j k : Nat) :
    Rle (Rsub (dlimInner (X.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (j + 1) - 1))).im
              (dlimInner (X.seq (Fsched X Y * (k + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1))).im)
        (ofQ (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
             (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))) := by
  have hF1 : 1 ≤ Fsched X Y := one_le_Fsched X Y
  have hed : 0 < (add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q)
                      (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q)).den :=
    add_den_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hen : 0 < (add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q)
                      (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q)).num := by
    show 0 < (1 : Int) * (((Fsched X Y * (k + 1) - 1) + 1 : Nat) : Int)
           + (1 : Int) * (((Fsched X Y * (j + 1) - 1) + 1 : Nat) : Int)
    push_cast; omega
  have ht1 := dlimInner_re_termBound
    (e := add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q) (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q))
    hed hen (normBound Y) (dlimSub (X.seq (Fsched X Y * (j + 1) - 1)) (X.seq (Fsched X Y * (k + 1) - 1)))
    (dlimSmul NEGI (Y.seq (Fsched X Y * (j + 1) - 1)))
    (X.reg (Fsched X Y * (j + 1) - 1) (Fsched X Y * (k + 1) - 1))
    (Rle_trans (Rle_of_Req (dlimNormSq_smul_negI (Y.seq (Fsched X Y * (j + 1) - 1))))
      (normBound_spec Y (Fsched X Y * (j + 1) - 1)))
  have him1 : Req (dlimInner (dlimSub (X.seq (Fsched X Y * (j + 1) - 1))
        (X.seq (Fsched X Y * (k + 1) - 1))) (Y.seq (Fsched X Y * (j + 1) - 1))).im
      (dlimInner (dlimSub (X.seq (Fsched X Y * (j + 1) - 1)) (X.seq (Fsched X Y * (k + 1) - 1)))
        (dlimSmul NEGI (Y.seq (Fsched X Y * (j + 1) - 1)))).re :=
    dlimInner_im_eq_re _ _
  have ht2 := dlimInner_re_termBound
    (e := add (⟨1, (Fsched X Y * (j + 1) - 1) + 1⟩ : Q) (⟨1, (Fsched X Y * (k + 1) - 1) + 1⟩ : Q))
    hed hen (normBound X)
    (dlimSmul NEGI (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1))))
    (X.seq (Fsched X Y * (k + 1) - 1))
    (Rle_trans (Rle_of_Req (dlimNormSq_smul_negI
        (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))))
      (Y.reg (Fsched X Y * (j + 1) - 1) (Fsched X Y * (k + 1) - 1)))
    (normBound_spec X (Fsched X Y * (k + 1) - 1))
  have him2 : Req (dlimInner (X.seq (Fsched X Y * (k + 1) - 1))
        (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1)))).im
      (dlimInner (dlimSmul NEGI (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1))
          (Y.seq (Fsched X Y * (k + 1) - 1)))) (X.seq (Fsched X Y * (k + 1) - 1))).re :=
    Req_trans (dlimInner_im_eq_re (X.seq (Fsched X Y * (k + 1) - 1))
        (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1)) (Y.seq (Fsched X Y * (k + 1) - 1))))
      (dlimInner_conj (X.seq (Fsched X Y * (k + 1) - 1))
        (dlimSmul NEGI (dlimSub (Y.seq (Fsched X Y * (j + 1) - 1))
          (Y.seq (Fsched X Y * (k + 1) - 1))))).1
  refine Rle_trans (Rle_of_Req (innerSeq_im_split (X.seq (Fsched X Y * (j + 1) - 1))
    (X.seq (Fsched X Y * (k + 1) - 1)) (Y.seq (Fsched X Y * (j + 1) - 1))
    (Y.seq (Fsched X Y * (k + 1) - 1)))) ?_
  refine Rle_trans (Radd_le_add_loc (Rle_trans (Rle_of_Req him1) ht1)
    (Rle_trans (Rle_of_Req him2) ht2)) ?_
  refine Rle_trans (Rle_of_Req (Radd_ofQ_loc
    (Nat.mul_pos hed (by decide)) (Nat.mul_pos hed (by decide)))) ?_
  refine Rle_ofQ_of_Qle_loc _ _ ?_
  have esj : Fsched X Y * (j + 1) - 1 + 1 = Fsched X Y * (j + 1) := sched_succ _ _ hF1
  have esk : Fsched X Y * (k + 1) - 1 + 1 = Fsched X Y * (k + 1) := sched_succ _ _ hF1
  rw [esj, esk]
  exact modulus_bound (Fsched X Y) (j + 1) (k + 1) (normBound X) (normBound Y)
    (Nat.succ_pos j) (Nat.succ_pos k) hF1 (by unfold Fsched; omega)

/-- **REGULARITY of the rescheduled inner-product sequence** (reviewer gate step 3): both coordinate
    real-sequences of `n ↦ ⟨X_{σn}, Y_{σn}⟩` are regular, so the sequence has a coordinatewise complex
    limit. Consumes `ComplexLimitCore` (`CRegCore`, `RReg_of_real_bound_core`). -/
theorem innerSeq_CRegCore (X Y : DLimCompletionRaw) :
    CRegCore (fun n => dlimInner (X.seq (Fsched X Y * (n + 1) - 1))
      (Y.seq (Fsched X Y * (n + 1) - 1))) :=
  ⟨RReg_of_real_bound_core _ (fun j k => add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
      (fun j k => add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
      (fun _ _ => Qle_refl _) (fun j k => innerSeq_re_bound X Y j k),
   RReg_of_real_bound_core _ (fun j k => add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
      (fun j k => add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
      (fun _ _ => Qle_refl _) (fun j k => innerSeq_im_bound X Y j k)⟩

/-- **THE COMPLETED INNER PRODUCT** (reviewer gate step 5, the definition): `⟨X,Y⟩ := lim ⟨X_{σn}, Y_{σn}⟩`,
    the coordinatewise complex limit of the rescheduled stagewise inner products. A genuine constructive
    limit — consumes both `DlimHilbertCompletion` (`dlimInner`) and `ComplexLimitCore` (`ClimCore`). -/
def completedInner (X Y : DLimCompletionRaw) : Complex :=
  ClimCore (fun n => dlimInner (X.seq (Fsched X Y * (n + 1) - 1))
    (Y.seq (Fsched X Y * (n + 1) - 1))) (innerSeq_CRegCore X Y)

end UOR.Bridge.F1Square.Square
