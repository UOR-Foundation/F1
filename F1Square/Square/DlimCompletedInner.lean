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
- **REPRESENTATIVE INDEPENDENCE** `completedInner_congr` (`X ≈ X' ∧ Y ≈ Y' ⟹ ⟨X,Y⟩ ≈ ⟨X',Y'⟩`): the two
  representative-dependent schedules are aligned by a triangle through the mid-point `⟨X'_i,Y'_i⟩`; both the
  `≈`-part (Term A, `X≈X'`/`Y≈Y'` read at level `m²`) and the schedule-difference part (Term B, `X'`/`Y'`
  Cauchy for indices `≥ 2m`) use a UNIFIED tolerance `e = 1/m` so the four half-bounds sum to `1/(k+1)`, fed
  into the null-difference limit theorem `ClimCore_eq_of_close`. So the completed inner product DESCENDS to
  the completion setoid — it is a genuine function of the completion classes.

STILL OPEN (flagged honestly — the next gate): the complex limit congruence / add / scalar / conjugation
limit laws, and the Hermitian / sesquilinear / positivity / definiteness pre-Hilbert laws that package
`completedInner` into a completed pre-Hilbert object. This module proves the completed inner product is a
well-defined, representative-independent function; it does NOT yet claim the pre-Hilbert axioms, a completed
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

-- ===========================================================================
-- TOWARD REPRESENTATIVE INDEPENDENCE (reviewer gate `completedInner_congr`). The general single-difference
-- bounds `Re⟨a,b⟩ − Re⟨a',b'⟩ ≤ eₐ(1+Bb)/2 + e_b(1+Ba)/2` (and the Im analogue), the reusable pieces that
-- bound both the ≈-part (Term A) and the schedule-difference part (Term B) of the congruence estimate.
-- ===========================================================================

/-- **General single-difference Re bound**: `Re⟨a,b⟩ − Re⟨a',b'⟩ ≤ eₐ(1+Bb)/2 + e_b(1+Ba)/2` given
    `‖a−a'‖²≤eₐ²`, `‖b‖²≤Bb`, `‖a'‖²≤Ba`, `‖b−b'‖²≤e_b²` (split `⟨a,b⟩−⟨a',b'⟩ = ⟨a−a',b⟩+⟨a',b−b'⟩`, then
    the single-term Cauchy–Schwarz bound on each half). -/
theorem dlimInner_re_diff_le {ea eb : Q} (hea : 0 < ea.den) (heaN : 0 < ea.num)
    (heb : 0 < eb.den) (hebN : 0 < eb.num) (Ba Bb : Nat) (a a' b b' : DLimRaw)
    (hAA : Rle (dlimNormSq (dlimSub a a')) (ofQ (mul ea ea) (Qmul_den_pos hea hea)))
    (hBb : Rle (dlimNormSq b) (ofQ (⟨(Bb : Int), 1⟩ : Q) Nat.one_pos))
    (hA' : Rle (dlimNormSq a') (ofQ (⟨(Ba : Int), 1⟩ : Q) Nat.one_pos))
    (hBB : Rle (dlimNormSq (dlimSub b b')) (ofQ (mul eb eb) (Qmul_den_pos heb heb))) :
    Rle (Rsub (dlimInner a b).re (dlimInner a' b').re)
        (Radd (ofQ (halfBound ea Bb) (Nat.mul_pos hea (by decide)))
              (ofQ (halfBound eb Ba) (Nat.mul_pos heb (by decide)))) := by
  refine Rle_trans (Rle_of_Req (innerSeq_re_split a a' b b')) ?_
  refine Radd_le_add_loc ?_ ?_
  · exact dlimInner_re_termBound hea heaN Bb (dlimSub a a') b hAA hBb
  · refine Rle_trans (Rle_of_Req (dlimInner_conj a' (dlimSub b b')).1) ?_
    exact dlimInner_re_termBound heb hebN Ba (dlimSub b b') a' hBB hA'

/-- **General single-difference Im bound** — the imaginary analogue via the `(−i)` twist. -/
theorem dlimInner_im_diff_le {ea eb : Q} (hea : 0 < ea.den) (heaN : 0 < ea.num)
    (heb : 0 < eb.den) (hebN : 0 < eb.num) (Ba Bb : Nat) (a a' b b' : DLimRaw)
    (hAA : Rle (dlimNormSq (dlimSub a a')) (ofQ (mul ea ea) (Qmul_den_pos hea hea)))
    (hBb : Rle (dlimNormSq b) (ofQ (⟨(Bb : Int), 1⟩ : Q) Nat.one_pos))
    (hA' : Rle (dlimNormSq a') (ofQ (⟨(Ba : Int), 1⟩ : Q) Nat.one_pos))
    (hBB : Rle (dlimNormSq (dlimSub b b')) (ofQ (mul eb eb) (Qmul_den_pos heb heb))) :
    Rle (Rsub (dlimInner a b).im (dlimInner a' b').im)
        (Radd (ofQ (halfBound ea Bb) (Nat.mul_pos hea (by decide)))
              (ofQ (halfBound eb Ba) (Nat.mul_pos heb (by decide)))) := by
  refine Rle_trans (Rle_of_Req (innerSeq_im_split a a' b b')) ?_
  refine Radd_le_add_loc ?_ ?_
  · refine Rle_trans (Rle_of_Req (dlimInner_im_eq_re (dlimSub a a') b)) ?_
    exact dlimInner_re_termBound hea heaN Bb (dlimSub a a') (dlimSmul NEGI b) hAA
      (Rle_trans (Rle_of_Req (dlimNormSq_smul_negI b)) hBb)
  · refine Rle_trans (Rle_of_Req (dlimInner_im_eq_re a' (dlimSub b b'))) ?_
    refine Rle_trans (Rle_of_Req (dlimInner_conj a' (dlimSmul NEGI (dlimSub b b'))).1) ?_
    exact dlimInner_re_termBound heb hebN Ba (dlimSmul NEGI (dlimSub b b')) a'
      (Rle_trans (Rle_of_Req (dlimNormSq_smul_negI (dlimSub b b'))) hBB) hA'

-- ===========================================================================
-- REPRESENTATIVE INDEPENDENCE (reviewer's non-negotiable gate `completedInner_congr`): X≈X' ∧ Y≈Y'
-- ⟹ ⟨X,Y⟩ ≈ ⟨X',Y'⟩, so the completed inner product DESCENDS to the completion setoid. The two
-- representative-dependent schedules are aligned by a triangle through the mid-point ⟨X'_i,Y'_i⟩;
-- BOTH the ≈-part (Term A, via X≈X'/Y≈Y' read at level m²) and the schedule-difference part (Term B,
-- via X'/Y' Cauchy for indices ≥ 2m) use a UNIFIED tolerance e = 1/m, so the four half-bounds sum to
-- 1/(k+1); fed into ClimCore_eq_of_close. The one-sided ε-chase (coord_close) is written once and
-- instantiated 4× (re/im × forward/reverse, the reverses via DLimCompletionEq_symm).
-- ===========================================================================

-- ===========================================================================
-- Small real-algebra bridges.
-- ===========================================================================

/-- `A − D ≈ (A − M) + (M − D)` (telescoping through a middle point). -/
private theorem Rsub_telescope (p mid q : Real) :
    Req (Rsub p q) (Radd (Rsub p mid) (Rsub mid q)) :=
  Req_symm
    (Req_trans (Radd_assoc p (Rneg mid) (Radd mid (Rneg q)))
      (Radd_congr (Req_refl p)
        (Req_trans (Req_symm (Radd_assoc (Rneg mid) mid (Rneg q)))
          (Req_trans
            (Radd_congr (Req_trans (Radd_comm (Rneg mid) mid) (Radd_neg mid)) (Req_refl (Rneg q)))
            (Req_trans (Radd_comm zero (Rneg q)) (Radd_zero (Rneg q)))))))

/-- From `p − q ≤ c` derive `p ≤ q + c`. -/
private theorem Rle_of_Rsub_le {p q c : Real} (h : Rle (Rsub p q) c) : Rle p (Radd q c) := by
  have e1 : Req (Radd (Rsub p q) q) p :=
    Req_trans (Radd_assoc p (Rneg q) q)
      (Req_trans (Radd_congr (Req_refl p) (Req_trans (Radd_comm (Rneg q) q) (Radd_neg q)))
        (Radd_zero p))
  have h1 : Rle (Radd (Rsub p q) q) (Radd c q) := Radd_le_add_loc h (Rle_refl q)
  exact Rle_trans (Rle_of_Req (Req_symm e1)) (Rle_trans h1 (Rle_of_Req (Radd_comm c q)))

-- ===========================================================================
-- The unified schedule/tolerance constant `m` and its ℚ estimates.
-- ===========================================================================

/-- The unified `m = 2(k+1)(1 + a + b + c)` — big enough that each of the four half-bounds
    `(1+x)/(2m)` (`x ≤ a+b+c`) is `≤ 1/(4(k+1))`, so the four sum to `1/(k+1)`. -/
def congrM (k a b c : Nat) : Nat := 2 * (k + 1) * (1 + a + b + c)

theorem congrM_pos (k a b c : Nat) : 0 < congrM k a b c := by
  unfold congrM
  exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos k)) (by omega)

/-- The Nat budget inequality `(1+x)·4(k+1) ≤ m·2` for `x ≤ a+b+c`, `m = congrM k a b c`. -/
theorem congrM_halfBound (k a b c x : Nat) (hx : x ≤ a + b + c) :
    (1 + x) * (4 * (k + 1)) ≤ congrM k a b c * 2 := by
  have h1 : (1 + x) * (4 * (k + 1)) ≤ (1 + a + b + c) * (4 * (k + 1)) :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have h2 : (1 + a + b + c) * (4 * (k + 1)) = congrM k a b c * 2 := by
    unfold congrM
    have : ((1 + a + b + c) * (4 * (k + 1)) : Int) = ((2 * (k + 1) * (1 + a + b + c)) * 2 : Int) := by
      push_cast; ring_uor
    exact_mod_cast this
  omega

/-- Each half-bound `(1+x)/(2m)` is `≤ 1/(4(k+1))`, given the Nat budget. -/
private theorem halfBound_le (nX m k : Nat)
    (hbound : (1 + nX) * (4 * (k + 1)) ≤ m * 2) :
    Qle (halfBound (⟨1, m⟩ : Q) nX) (⟨1, 4 * (k + 1)⟩ : Q) := by
  simp only [Qle, halfBound]
  push_cast
  refine Int.le_of_sub_nonneg ?_
  have hb : (0 : Int) ≤ (m : Int) * 2 - (1 + (nX : Int)) * (4 * ((k : Int) + 1)) := by
    have hI : ((1 + nX) * (4 * (k + 1)) : Int) ≤ ((m * 2 : Nat) : Int) := by exact_mod_cast hbound
    push_cast at hI
    omega
  have hid : (1 : Int) * ((m : Int) * 2) - (1 * (1 + (nX : Int))) * (4 * ((k : Int) + 1))
      = (m : Int) * 2 - (1 + (nX : Int)) * (4 * ((k : Int) + 1)) := by ring_uor
  rw [hid]; exact hb

/-- The Cauchy modulus `M(i,j)` is `≤ (1/m)²` once both indices exceed `2m`. -/
theorem dlimCauchyMod_le_inv_sq (i j m : Nat) (hmpos : 0 < m)
    (hi : 2 * m ≤ i + 1) (hj : 2 * m ≤ j + 1) :
    Rle (dlimCauchyModR i j) (ofQ (mul (⟨1, m⟩ : Q) (⟨1, m⟩ : Q)) (Qmul_den_pos hmpos hmpos)) := by
  unfold dlimCauchyModR
  refine Rle_ofQ_of_Qle_loc _ _ ?_
  have hSE : Qle (add (⟨1, i + 1⟩ : Q) (⟨1, j + 1⟩ : Q)) (⟨1, m⟩ : Q) := by
    simp only [Qle, add]
    push_cast
    refine Int.le_of_sub_nonneg ?_
    have hM : (0 : Int) ≤ (m : Int) := by omega
    have t1 : (0 : Int) ≤ (m : Int) * (((j : Int) + 1) - 2 * (m : Int)) :=
      Int.mul_nonneg hM (by omega)
    have t2 : (0 : Int) ≤ (((i : Int) + 1) - 2 * (m : Int)) * (m : Int) :=
      Int.mul_nonneg (by omega) hM
    have t3 : (0 : Int) ≤ (((i : Int) + 1) - 2 * (m : Int)) * (((j : Int) + 1) - 2 * (m : Int)) :=
      Int.mul_nonneg (by omega) (by omega)
    have hid : (1 : Int) * (((i : Int) + 1) * ((j : Int) + 1))
          - (1 * ((j : Int) + 1) + 1 * ((i : Int) + 1)) * (m : Int)
        = (m : Int) * (((j : Int) + 1) - 2 * (m : Int))
          + (((i : Int) + 1) - 2 * (m : Int)) * (m : Int)
          + (((i : Int) + 1) - 2 * (m : Int)) * (((j : Int) + 1) - 2 * (m : Int)) := by ring_uor
    rw [hid]; omega
  exact Qmul_le_mul (add_den_pos (Nat.succ_pos i) (Nat.succ_pos j)) hmpos
    (add_den_pos (Nat.succ_pos i) (Nat.succ_pos j))
    (by simp only [add]; push_cast; omega)
    (by simp only [add]; push_cast; omega)
    hSE hSE

/-- From `X ≈ X'`, eventually `‖X_n − X'_n‖² ≤ (1/m)²`. -/
private theorem eq_sq_bound {A A' : DLimCompletionRaw} (hAA' : DLimCompletionEq A A')
    (m : Nat) (hmpos : 0 < m) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Rle (dlimNormSq (dlimSub (A.seq n) (A'.seq n)))
          (ofQ (mul (⟨1, m⟩ : Q) (⟨1, m⟩ : Q)) (Qmul_den_pos hmpos hmpos)) := by
  obtain ⟨N, hN⟩ := hAA' (m * m)
  refine ⟨N, fun n hn => ?_⟩
  refine Rle_trans (hN n hn) (Rle_ofQ_of_Qle_loc _ _ ?_)
  simp only [Qle, mul]
  push_cast
  omega

-- ===========================================================================
-- The one-sided coordinate closeness (written once, instantiated 4×).
-- ===========================================================================

private theorem coord_close
    (proj : Complex → Real)
    (diffLe : ∀ (ea eb : Q) (hea : 0 < ea.den) (heaN : 0 < ea.num)
       (heb : 0 < eb.den) (hebN : 0 < eb.num) (Ba Bb : Nat) (a a' b b' : DLimRaw),
       Rle (dlimNormSq (dlimSub a a')) (ofQ (mul ea ea) (Qmul_den_pos hea hea)) →
       Rle (dlimNormSq b) (ofQ (⟨(Bb : Int), 1⟩ : Q) Nat.one_pos) →
       Rle (dlimNormSq a') (ofQ (⟨(Ba : Int), 1⟩ : Q) Nat.one_pos) →
       Rle (dlimNormSq (dlimSub b b')) (ofQ (mul eb eb) (Qmul_den_pos heb heb)) →
       Rle (Rsub (proj (dlimInner a b)) (proj (dlimInner a' b')))
           (Radd (ofQ (halfBound ea Bb) (Nat.mul_pos hea (by decide)))
                 (ofQ (halfBound eb Ba) (Nat.mul_pos heb (by decide)))))
    {A A' B B' : DLimCompletionRaw}
    (hAA' : DLimCompletionEq A A') (hBB' : DLimCompletionEq B B')
    (k : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Rle (proj (dlimInner (A.seq (Fsched A B * (n + 1) - 1)) (B.seq (Fsched A B * (n + 1) - 1))))
          (Radd (proj (dlimInner (A'.seq (Fsched A' B' * (n + 1) - 1))
                                 (B'.seq (Fsched A' B' * (n + 1) - 1))))
                (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) := by
  obtain ⟨NA, hNA⟩ := eq_sq_bound hAA' (congrM k (normBound B) (normBound A') (normBound B'))
    (congrM_pos k (normBound B) (normBound A') (normBound B'))
  obtain ⟨NB, hNB⟩ := eq_sq_bound hBB' (congrM k (normBound B) (normBound A') (normBound B'))
    (congrM_pos k (normBound B) (normBound A') (normBound B'))
  refine ⟨max (max NA NB) (2 * congrM k (normBound B) (normBound A') (normBound B')),
    fun n hn => ?_⟩
  have hnNA : NA ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left NA NB) (Nat.le_max_left _ _)) hn
  have hnNB : NB ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right NA NB) (Nat.le_max_left _ _)) hn
  have hn2m : 2 * congrM k (normBound B) (normBound A') (normBound B') ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hσ : 1 ≤ Fsched A B := one_le_Fsched A B
  have hσ' : 1 ≤ Fsched A' B' := one_le_Fsched A' B'
  have hile : n + 1 ≤ Fsched A B * (n + 1) := Nat.le_mul_of_pos_left (n + 1) hσ
  have hile' : n + 1 ≤ Fsched A' B' * (n + 1) := Nat.le_mul_of_pos_left (n + 1) hσ'
  have hisucc : Fsched A B * (n + 1) - 1 + 1 = Fsched A B * (n + 1) := by
    have : 0 < Fsched A B * (n + 1) := Nat.mul_pos hσ (Nat.succ_pos n); omega
  have hisucc' : Fsched A' B' * (n + 1) - 1 + 1 = Fsched A' B' * (n + 1) := by
    have : 0 < Fsched A' B' * (n + 1) := Nat.mul_pos hσ' (Nat.succ_pos n); omega
  have hi_ge_n : n ≤ Fsched A B * (n + 1) - 1 := by omega
  have hi_NA : NA ≤ Fsched A B * (n + 1) - 1 := Nat.le_trans hnNA hi_ge_n
  have hi_NB : NB ≤ Fsched A B * (n + 1) - 1 := Nat.le_trans hnNB hi_ge_n
  have h2m_i : 2 * congrM k (normBound B) (normBound A') (normBound B')
      ≤ Fsched A B * (n + 1) - 1 + 1 := by
    rw [hisucc]; exact Nat.le_trans (by omega) hile
  have h2m_i' : 2 * congrM k (normBound B) (normBound A') (normBound B')
      ≤ Fsched A' B' * (n + 1) - 1 + 1 := by
    rw [hisucc']; exact Nat.le_trans (by omega) hile'
  -- TERM A: the ≈-difference at index i.
  have termA := diffLe (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
    (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
    (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide : (0:Int) < 1)
    (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide : (0:Int) < 1)
    (normBound A') (normBound B)
    (A.seq (Fsched A B * (n + 1) - 1)) (A'.seq (Fsched A B * (n + 1) - 1))
    (B.seq (Fsched A B * (n + 1) - 1)) (B'.seq (Fsched A B * (n + 1) - 1))
    (hNA (Fsched A B * (n + 1) - 1) hi_NA)
    (normBound_spec B (Fsched A B * (n + 1) - 1))
    (normBound_spec A' (Fsched A B * (n + 1) - 1))
    (hNB (Fsched A B * (n + 1) - 1) hi_NB)
  -- TERM B: the schedule-difference on X' from i to i'.
  have termB := diffLe (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
    (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
    (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide : (0:Int) < 1)
    (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide : (0:Int) < 1)
    (normBound A') (normBound B')
    (A'.seq (Fsched A B * (n + 1) - 1)) (A'.seq (Fsched A' B' * (n + 1) - 1))
    (B'.seq (Fsched A B * (n + 1) - 1)) (B'.seq (Fsched A' B' * (n + 1) - 1))
    (Rle_trans (A'.reg (Fsched A B * (n + 1) - 1) (Fsched A' B' * (n + 1) - 1))
      (dlimCauchyMod_le_inv_sq (Fsched A B * (n + 1) - 1) (Fsched A' B' * (n + 1) - 1)
        (congrM k (normBound B) (normBound A') (normBound B'))
        (congrM_pos k (normBound B) (normBound A') (normBound B')) h2m_i h2m_i'))
    (normBound_spec B' (Fsched A B * (n + 1) - 1))
    (normBound_spec A' (Fsched A' B' * (n + 1) - 1))
    (Rle_trans (B'.reg (Fsched A B * (n + 1) - 1) (Fsched A' B' * (n + 1) - 1))
      (dlimCauchyMod_le_inv_sq (Fsched A B * (n + 1) - 1) (Fsched A' B' * (n + 1) - 1)
        (congrM k (normBound B) (normBound A') (normBound B'))
        (congrM_pos k (normBound B) (normBound A') (normBound B')) h2m_i h2m_i'))
  -- the target tolerance level 1/(4(k+1)).
  have htgt : 0 < 4 * (k + 1) := by omega
  have leB : Rle (ofQ (halfBound (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
        (normBound B)) (Nat.mul_pos (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide)))
      (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt) :=
    Rle_ofQ_of_Qle_loc _ _ (halfBound_le (normBound B)
      (congrM k (normBound B) (normBound A') (normBound B')) k
      (congrM_halfBound k (normBound B) (normBound A') (normBound B') (normBound B) (by omega)))
  have leA' : Rle (ofQ (halfBound (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
        (normBound A')) (Nat.mul_pos (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide)))
      (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt) :=
    Rle_ofQ_of_Qle_loc _ _ (halfBound_le (normBound A')
      (congrM k (normBound B) (normBound A') (normBound B')) k
      (congrM_halfBound k (normBound B) (normBound A') (normBound B') (normBound A') (by omega)))
  have leB' : Rle (ofQ (halfBound (⟨1, congrM k (normBound B) (normBound A') (normBound B')⟩ : Q)
        (normBound B')) (Nat.mul_pos (congrM_pos k (normBound B) (normBound A') (normBound B')) (by decide)))
      (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt) :=
    Rle_ofQ_of_Qle_loc _ _ (halfBound_le (normBound B')
      (congrM k (normBound B) (normBound A') (normBound B')) k
      (congrM_halfBound k (normBound B) (normBound A') (normBound B') (normBound B') (by omega)))
  have sum_eq : Req
      (Radd (Radd (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt) (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt))
            (Radd (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt) (ofQ (⟨1, 4 * (k + 1)⟩ : Q) htgt)))
      (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) :=
    Req_trans
      (Req_trans (Radd_congr (Radd_ofQ_loc htgt htgt) (Radd_ofQ_loc htgt htgt)) (Radd_ofQ_loc _ _))
      (ofQ_respects _ (Nat.succ_pos k) (by simp only [Qeq, add, mul]; push_cast; ring_uor))
  refine Rle_of_Rsub_le ?_
  refine Rle_trans (Rle_of_Req (Rsub_telescope
    (proj (dlimInner (A.seq (Fsched A B * (n + 1) - 1)) (B.seq (Fsched A B * (n + 1) - 1))))
    (proj (dlimInner (A'.seq (Fsched A B * (n + 1) - 1)) (B'.seq (Fsched A B * (n + 1) - 1))))
    (proj (dlimInner (A'.seq (Fsched A' B' * (n + 1) - 1)) (B'.seq (Fsched A' B' * (n + 1) - 1)))))) ?_
  refine Rle_trans (Radd_le_add_loc termA termB) ?_
  refine Rle_trans (Radd_le_add_loc (Radd_le_add_loc leB leA') (Radd_le_add_loc leB' leA')) ?_
  exact Rle_of_Req sum_eq

-- ===========================================================================
-- THE TARGET: representative independence of the completed inner product.
-- ===========================================================================

theorem completedInner_congr {X X' Y Y' : DLimCompletionRaw}
    (hX : DLimCompletionEq X X') (hY : DLimCompletionEq Y Y') :
    Ceq (completedInner X Y) (completedInner X' Y') := by
  refine ClimCore_eq_of_close (innerSeq_CRegCore X Y) (innerSeq_CRegCore X' Y') ?_ ?_ ?_ ?_
  · exact fun k => coord_close (fun z => z.re) (@dlimInner_re_diff_le) hX hY k
  · exact fun k => coord_close (fun z => z.re) (@dlimInner_re_diff_le)
      (DLimCompletionEq_symm hX) (DLimCompletionEq_symm hY) k
  · exact fun k => coord_close (fun z => z.im) (@dlimInner_im_diff_le) hX hY k
  · exact fun k => coord_close (fun z => z.im) (@dlimInner_im_diff_le)
      (DLimCompletionEq_symm hX) (DLimCompletionEq_symm hY) k

end UOR.Bridge.F1Square.Square
