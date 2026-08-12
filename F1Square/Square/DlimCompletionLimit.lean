/-
# Sharp (uncancelled) completion Cauchy–Schwarz + GENUINE full-complex fixed-vector limit continuity

Two ζ-free, sqrt-free, division-free upgrades living entirely in the completion cone.

* `completedInner_re_cs_sharp` — the SHARP real-part Cauchy–Schwarz `(Re⟨U,V⟩)² ≤ ‖U‖²·‖V‖²`, with the
  `‖V‖²` common factor CANCELLED (unlike `completedInner_re_cs_gen`, which keeps `‖V‖²·(…) ≤ ‖V‖²·(…)`).
  The cancellation is genuine: it is obtained constructively by refuting apart-positivity of the deficit,
  using an apartness/positive-scalar cancellation built here from the `Real`/`QOrder` primitives, together
  with the definiteness of the completed inner product (so the vacuous `‖V‖²≈0` case is handled honestly by
  `V ≈ 0`).

* `inner_fixed_tendsto_scs` — GENUINE fixed-vector limit continuity: for a fixed but arbitrary `V`, if
  `Xs n → X` in squared distance then `⟨V, Xs n⟩ → ⟨V, X⟩` in BOTH the real and imaginary coordinates,
  UNCONDITIONALLY (no `‖V‖²` factor to cancel; it works even at `‖V‖²≈0`). Each squared coordinate
  difference is bounded by `‖V‖²·d²(Xs n, X)` via the SHARP CS (real slot directly; imaginary slot through
  the `−i` twist), and the fixed constant `‖V‖²` is absorbed by a rational-index reschedule.

No `completedInner`/`completedNormSq`/`completedDist2` is ever unfolded by defeq; only the completion
black-box laws are used. Choice-free; axioms `[propext, Quot.sound]`.
-/
import F1Square.Square.DlimCompletionCS

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ micro-helpers (leaf names end in `_scs`).
-- ===========================================================================

private theorem Rneg_neg_scs (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (x.seq n))) (x.seq n)
    simp only [Qeq, neg]; ring_uor)

private theorem Rzero_add_scs (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

private theorem Rneg_zero_scs : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (zero.seq n)) (zero.seq n)
    rw [zero_seq]; decide)

private theorem Rone_mul_scs (x : Real) : Req (Rmul one x) x :=
  Req_trans (Rmul_comm one x) (Rmul_one x)

private theorem Rzero_mul_scs (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

private theorem Rneg_one_mul_scs (x : Real) : Req (Rmul (Rneg one) x) (Rneg x) :=
  Req_trans (Rmul_neg_left one x) (Rneg_congr (Rone_mul_scs x))

/-- `Re((−i)·z) ≈ Im z`. -/
private theorem Cmul_re_negI_scs (z : Complex) :
    Req (Cmul (⟨zero, Rneg one⟩ : Complex) z).re z.im := by
  show Req (Radd (Rmul zero z.re) (Rneg (Rmul (Rneg one) z.im))) z.im
  exact Req_trans
    (Radd_congr (Rzero_mul_scs z.re)
      (Req_trans (Rneg_congr (Rneg_one_mul_scs z.im)) (Rneg_neg_scs z.im)))
    (Rzero_add_scs z.im)

-- ===========================================================================
-- `Pos` order algebra rebuilt on the ζ-free cone (`Real`/`ROrder`/`QOrder`/`RealOrderCore`).
-- ===========================================================================

/-- `¬Pos z` gives `Rnonneg(−z)` (both say `∀n, zₙ ≤ 1/(n+1)`). -/
private theorem Rnonneg_neg_of_not_Pos_scs {z : Real} (h : ¬ Pos z) : Rnonneg (Rneg z) := by
  intro n
  show Qle (neg (Qbound n)) (neg (z.seq n))
  have hle : Qle (z.seq n) (Qbound n) := by
    have hnn : ¬ Qlt (Qbound n) (z.seq n) := fun hc => h ⟨n, hc⟩
    simp only [Qle, Qlt] at hnn ⊢; omega
  exact Qneg_le_neg_loc hle

/-- `Pos z` and `Rnonneg(−z)` are contradictory. -/
private theorem not_Pos_of_Rnonneg_neg_scs {z : Real} (h : Rnonneg (Rneg z)) : ¬ Pos z := by
  rintro ⟨n, hn⟩
  have hle : Qle (neg (Qbound n)) (neg (z.seq n)) := h n
  simp only [Qle, Qlt, neg, Int.neg_mul] at hle hn; omega

/-- `Pos ⟹ rational lower bound`: a positive real `x` exceeds the fixed positive rational `xₙ − 1/(n+1)`. -/
private theorem Pos_imp_ofQ_le_scs {x : Real} (h : Pos x) :
    ∃ (c : Q) (hcd : 0 < c.den), 0 < c.num ∧ Rle (ofQ c hcd) x := by
  obtain ⟨n, hn⟩ := h
  refine ⟨Qsub (x.seq n) (Qbound n), Qsub_den_pos (x.den_pos n) (Qbound_den_pos n), ?_, ?_⟩
  · simp only [Qlt, Qbound] at hn; simp only [Qsub, add, neg, Qbound]; push_cast at hn ⊢; omega
  · intro m
    show Qle (Qsub (x.seq n) (Qbound n)) (add (x.seq m) ⟨2, m + 1⟩)
    have hreg : Qle (x.seq n) (add (x.seq m) (add (Qbound n) (Qbound m))) :=
      Qle_add_of_Qabs_sub (x.den_pos n) (x.den_pos m)
        (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m)) (x.reg n m)
    have hassoc : Qle (x.seq n) (add (Qbound n) (add (x.seq m) (Qbound m))) :=
      Qle_trans (add_den_pos (x.den_pos m) (add_den_pos (Qbound_den_pos n) (Qbound_den_pos m))) hreg
        (Qeq_le (by simp only [Qeq, add, Qbound]; push_cast; ring_uor))
    have hsub : Qle (Qsub (x.seq n) (Qbound n)) (add (x.seq m) (Qbound m)) :=
      Qsub_le_of_le_add (Qbound_den_pos n) (add_den_pos (x.den_pos m) (Qbound_den_pos m)) hassoc
    exact Qle_trans (add_den_pos (x.den_pos m) (Qbound_den_pos m)) hsub
      (Qadd_le_add (Qle_refl _) (by simp only [Qle, Qbound]; push_cast; omega))

/-- `Pos ⟹ Rnonneg`. -/
private theorem Rnonneg_of_Pos_scs {x : Real} (h : Pos x) : Rnonneg x := by
  obtain ⟨c, hcd, hcn, hca⟩ := Pos_imp_ofQ_le_scs h
  have h0c : Rle zero (ofQ c hcd) := by
    intro n
    show Qle (⟨0, 1⟩ : Q) (add c ⟨2, n + 1⟩)
    have h1 : (0 : Int) ≤ c.num * ((n : Int) + 1) := Int.mul_nonneg (Int.le_of_lt hcn) (by omega)
    have h2 : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le c.den
    simp only [Qle, add]; push_cast; omega
  exact Rnonneg_congr_loc (Rsub_zero x) (Rnonneg_Rsub_of_Rle_loc (Rle_trans h0c hca))

/-- The integer core for `Pos_of_Rle_ofQ_scs`. -/
private theorem pos_core_scs (cn cd p q : Int) (hcn : 1 ≤ cn) (hcd : 1 ≤ cd) (hq : 1 ≤ q)
    (h : cn * (q * (3 * cd + 1)) ≤ (p * (3 * cd + 1) + 2 * q) * cd) : q < p * (3 * cd + 1) := by
  have hqNnn : 0 ≤ q * (3 * cd + 1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : q * (3 * cd + 1) ≤ cn * (q * (3 * cd + 1)) := by
    have hh := Int.mul_le_mul_of_nonneg_right hcn hqNnn
    rwa [Int.one_mul] at hh
  have h2 : q * (3 * cd + 1) ≤ (p * (3 * cd + 1) + 2 * q) * cd := Int.le_trans h1 h
  have e1 : q * (3 * cd + 1) = 3 * (q * cd) + q := by ring_uor
  have e2 : (p * (3 * cd + 1) + 2 * q) * cd = (p * (3 * cd + 1)) * cd + 2 * (q * cd) := by ring_uor
  rw [e1, e2] at h2
  have h3 : q * cd < (p * (3 * cd + 1)) * cd := by omega
  exact Int.lt_of_mul_lt_mul_right h3 (by omega)

/-- The witnessed strict-positivity index from a rational lower bound. -/
private theorem Rlt_Qbound_of_Rle_ofQ_scs {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) {x : Real}
    (h : Rle (ofQ c hcd) x) : Qlt (Qbound (3 * c.den)) (x.seq (3 * c.den)) := by
  have hRle := h (3 * c.den)
  have hcdI : (1 : Int) ≤ (c.den : Int) := by exact_mod_cast hcd
  have hqI : (1 : Int) ≤ ((x.seq (3 * c.den)).den : Int) := by exact_mod_cast x.den_pos _
  have hcond : c.num * (((x.seq (3 * c.den)).den : Int) * (3 * (c.den : Int) + 1))
      ≤ ((x.seq (3 * c.den)).num * (3 * (c.den : Int) + 1) + 2 * ((x.seq (3 * c.den)).den : Int))
        * (c.den : Int) := by
    have hu : Qle c (add (x.seq (3 * c.den)) ⟨2, 3 * c.den + 1⟩) := hRle
    simp only [Qle, add] at hu
    push_cast at hu
    have hgoal : c.num * (((x.seq (3 * c.den)).den : Int) * ((3 * c.den + 1 : Nat) : Int))
        ≤ ((x.seq (3 * c.den)).num * ((3 * c.den + 1 : Nat) : Int)
          + 2 * ((x.seq (3 * c.den)).den : Int)) * (c.den : Int) := by
      push_cast; push_cast at hu; omega
    push_cast at hgoal; omega
  have key := pos_core_scs c.num (c.den : Int) (x.seq (3 * c.den)).num ((x.seq (3 * c.den)).den : Int)
    (by omega) hcdI hqI hcond
  show Qlt (Qbound (3 * c.den)) (x.seq (3 * c.den))
  simp only [Qlt, Qbound]
  push_cast
  push_cast at key
  omega

/-- Strict positivity from a rational lower bound. -/
private theorem Pos_of_Rle_ofQ_scs {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den) {x : Real}
    (h : Rle (ofQ c hcd) x) : Pos x := ⟨3 * c.den, Rlt_Qbound_of_Rle_ofQ_scs hcn hcd h⟩

/-- Product of two positives is positive. -/
private theorem Pos_Rmul_scs {a b : Real} (ha : Pos a) (hb : Pos b) : Pos (Rmul a b) := by
  obtain ⟨c, hcd, hcn, hca⟩ := Pos_imp_ofQ_le_scs ha
  obtain ⟨d, hdd, hdn, hdb⟩ := Pos_imp_ofQ_le_scs hb
  refine Pos_of_Rle_ofQ_scs (c := mul c d) (by simp only [mul]; exact Int.mul_pos hcn hdn)
    (Qmul_den_pos hcd hdd) ?_
  exact Rle_trans (Rle_of_Req (Req_symm (Rmul_ofQ_ofQ_loc hcd hdd)))
    (Rle_trans (Rmul_le_Rmul_right_loc (Rnonneg_ofQ_loc hdd (Int.le_of_lt hdn)) hca)
      (Rmul_le_Rmul_left_loc (Rnonneg_of_Pos_scs ha) hdb))

/-- `x ≈ 0 ⟹ ¬Pos x`. -/
private theorem Req_zero_imp_not_Pos_scs {x : Real} (h : Req x zero) : ¬ Pos x := by
  refine not_Pos_of_Rnonneg_neg_scs ?_
  refine Rnonneg_congr_loc (y := Rneg x) ?_ Rnonneg_zero
  exact Req_trans (Req_symm Rneg_zero_scs) (Rneg_congr (Req_symm h))

-- ===========================================================================
-- Apartness / positive-scalar cancellation (division-free).
-- ===========================================================================

/-- **Positive-scalar cancellation**: `a ≥ 0`, `c` apart-positive, and `a·c ≈ 0` force `a ≈ 0`. Constructive
    (no reciprocal): if `a` were apart-positive then `a·c` would be apart-positive (product of positives),
    contradicting `a·c ≈ 0`; so `¬Pos a`, hence `a ≤ 0`, and with `a ≥ 0`, `a ≈ 0`. -/
private theorem apart_cancel_scs {a c : Real} (ha : Rnonneg a) (hc : Pos c)
    (h0 : Req (Rmul a c) zero) : Req a zero := by
  have hnpa : ¬ Pos a := fun hpa => (Req_zero_imp_not_Pos_scs h0) (Pos_Rmul_scs hpa hc)
  have hle_a0 : Rle a zero :=
    Rle_of_Rnonneg_Rsub_loc
      (Rnonneg_congr_loc (Req_symm (Rzero_add_scs (Rneg a)))
        (Rnonneg_neg_of_not_Pos_scs hnpa))
  exact Rle_antisymm hle_a0 (Rle_zero_of_Rnonneg ha)

/-- `x ≥ 0 ⟹ −x ≤ 0`. -/
private theorem Rle_Rneg_zero_of_Rnonneg_scs {x : Real} (h : Rnonneg x) : Rle (Rneg x) zero :=
  Rle_of_Rnonneg_Rsub_loc
    (Rnonneg_congr_loc
      (Req_symm (Req_trans (Rzero_add_scs (Rneg (Rneg x))) (Rneg_neg_scs x))) h)

/-- **Abstract sharp-CS deficit nonnegativity**: given `a ≥ 0`, `a·s ≥ 0`, and the definiteness input
    `a ≈ 0 ⟹ s ≈ 0`, conclude `s ≥ 0`. The refutation of apart-negativity of `s` uses `apart_cancel_scs`
    to force `a ≈ 0`, whence `s ≈ 0`, contradicting `s` apart-negative. This is the honest cancellation of
    the common `a` factor. -/
private theorem apart_nonneg_scs {a s : Real}
    (ha : Rnonneg a) (H1 : Rnonneg (Rmul a s)) (hdef : Req a zero → Req s zero) :
    Rnonneg s := by
  refine Rnonneg_congr_loc (Rneg_neg_scs s) (Rnonneg_neg_of_not_Pos_scs ?_)
  intro hps
  have hcnn : Rnonneg (Rneg s) := Rnonneg_of_Pos_scs hps
  have K2 : Rnonneg (Rmul a (Rneg s)) := Rnonneg_Rmul_loc ha hcnn
  have K1 : Rle (Rmul a (Rneg s)) zero :=
    Rle_trans (Rle_of_Req (Rmul_neg_right a s)) (Rle_Rneg_zero_of_Rnonneg_scs H1)
  have h0 : Req (Rmul a (Rneg s)) zero := Rle_antisymm K1 (Rle_zero_of_Rnonneg K2)
  have hA0 : Req a zero := apart_cancel_scs ha hps h0
  have hs0 : Req s zero := hdef hA0
  exact (Req_zero_imp_not_Pos_scs (Req_trans (Rneg_congr hs0) Rneg_zero_scs)) hps

-- ===========================================================================
-- TARGET A — the SHARP (uncancelled) real-part Cauchy–Schwarz.
--   `(Re⟨U,V⟩)² ≤ ‖U‖²·‖V‖²`.
-- ===========================================================================

/-- **SHARP real-part Cauchy–Schwarz** at the completion level: `(Re⟨U,V⟩)² ≤ ‖U‖²·‖V‖²`, with the `‖V‖²`
    factor cancelled. From the division-free `completedInner_re_cs_gen` (`‖V‖²·(Re⟨U,V⟩)² ≤ ‖V‖²·(‖U‖²·‖V‖²)`)
    we obtain `‖V‖²·s ≥ 0` for the deficit `s = ‖U‖²·‖V‖² − (Re⟨U,V⟩)²`; `apart_nonneg_scs` cancels the
    common `‖V‖²` honestly, its definiteness input coming from `completedInner_self_definite`
    (`‖V‖²≈0 ⟹ V ≈ 0 ⟹ ⟨U,V⟩ ≈ 0 ⟹ s ≈ 0`). -/
theorem completedInner_re_cs_sharp (U V : DLimCompletionRaw) :
    Rle (Rmul (completedInner U V).re (completedInner U V).re)
        (Rmul (completedNormSq U) (completedNormSq V)) := by
  refine Rle_of_Rnonneg_Rsub_loc ?_
  refine apart_nonneg_scs (completedNormSq_nonneg V) ?H1 ?hdef
  case H1 =>
    exact Rnonneg_congr_loc
      (Req_symm (Rmul_sub_distrib (completedNormSq V)
        (Rmul (completedNormSq U) (completedNormSq V))
        (Rmul (completedInner U V).re (completedInner U V).re)))
      (Rnonneg_Rsub_of_Rle_loc (completedInner_re_cs_gen U V))
  case hdef =>
    intro hA0
    have hCV : Ceq (completedInner V V) Czero := ⟨hA0, completedInner_self_im V⟩
    have hVz : DLimCompletionEq V dlimCompletionZero := completedInner_self_definite hCV
    have hr0 : Req (completedInner U V).re zero :=
      Req_trans (completedInner_congr (DLimCompletionEq_refl U) hVz).1
        (completedInner_zero_right_cpl U).1
    have hrr0 : Req (Rmul (completedInner U V).re (completedInner U V).re) zero :=
      Req_trans (Rmul_congr hr0 hr0) (Rmul_zero zero)
    have hba0 : Req (Rmul (completedNormSq U) (completedNormSq V)) zero :=
      Req_trans (Rmul_congr (Req_refl (completedNormSq U)) hA0) (Rmul_zero (completedNormSq U))
    exact Req_trans (Rsub_congr hba0 hrr0) (Rsub_zero zero)

-- ===========================================================================
-- Per-vector squared-coordinate bounds `(coord diff)² ≤ d²·‖V‖²` (real and imaginary).
-- ===========================================================================

/-- `(Re⟨V,A⟩ − Re⟨V,B⟩)² ≤ d²(A,B)·‖V‖²`, from the SHARP CS at `U := A⊖B` and Hermitian symmetry. -/
theorem inner_re_diff_sq_le_scs (V A B : DLimCompletionRaw) :
    Rle (Rmul (Rsub (completedInner V A).re (completedInner V B).re)
              (Rsub (completedInner V A).re (completedInner V B).re))
        (Rmul (completedDist2 A B) (completedNormSq V)) := by
  have hconj : Req (completedInner (dlimCompletionSub A B) V).re
      (completedInner V (dlimCompletionSub A B)).re :=
    (completedInner_conj (dlimCompletionSub A B) V).1
  have hCe : Ceq (completedInner V (dlimCompletionSub A B))
      (Cadd (completedInner V A) (Cneg (completedInner V B))) :=
    Ceq_trans (completedInner_add_right V A (dlimCompletionNeg B))
      (Cadd_congr (Ceq_refl (completedInner V A)) (completedInner_neg_right_cpl V B))
  have hUre : Req (completedInner (dlimCompletionSub A B) V).re
      (Rsub (completedInner V A).re (completedInner V B).re) :=
    Req_trans hconj hCe.1
  exact Rle_trans (Rle_of_Req (Rmul_congr (Req_symm hUre) (Req_symm hUre)))
    (completedInner_re_cs_sharp (dlimCompletionSub A B) V)

/-- `(Im⟨V,A⟩ − Im⟨V,B⟩)² ≤ d²(A,B)·‖V‖²`, from the SHARP CS at the `−i`-twisted vector `(−i)•(A⊖B)`
    (`Im⟨V,W⟩ = Re⟨V,(−i)•W⟩`, `‖(−i)•W‖² ≈ ‖W‖²`). -/
theorem inner_im_diff_sq_le_scs (V A B : DLimCompletionRaw) :
    Rle (Rmul (Rsub (completedInner V A).im (completedInner V B).im)
              (Rsub (completedInner V A).im (completedInner V B).im))
        (Rmul (completedDist2 A B) (completedNormSq V)) := by
  have hCe : Ceq (completedInner V (dlimCompletionSub A B))
      (Cadd (completedInner V A) (Cneg (completedInner V B))) :=
    Ceq_trans (completedInner_add_right V A (dlimCompletionNeg B))
      (Cadd_congr (Ceq_refl (completedInner V A)) (completedInner_neg_right_cpl V B))
  have hIdiff : Req (Rsub (completedInner V A).im (completedInner V B).im)
      (completedInner V (dlimCompletionSub A B)).im :=
    Req_symm hCe.2
  have hTwist : Req (completedInner V (dlimCompletionSmul (⟨zero, Rneg one⟩ : Complex)
        (dlimCompletionSub A B))).re
      (completedInner V (dlimCompletionSub A B)).im :=
    Req_trans (completedInner_smul_right (⟨zero, Rneg one⟩ : Complex) V (dlimCompletionSub A B)).1
      (Cmul_re_negI_scs (completedInner V (dlimCompletionSub A B)))
  have hFinal : Req (Rsub (completedInner V A).im (completedInner V B).im)
      (completedInner (dlimCompletionSmul (⟨zero, Rneg one⟩ : Complex) (dlimCompletionSub A B)) V).re :=
    Req_trans (Req_trans hIdiff (Req_symm hTwist))
      (Req_symm (completedInner_conj
        (dlimCompletionSmul (⟨zero, Rneg one⟩ : Complex) (dlimCompletionSub A B)) V).1)
  have hNorm : Req (completedNormSq (dlimCompletionSmul (⟨zero, Rneg one⟩ : Complex)
        (dlimCompletionSub A B))) (completedDist2 A B) :=
    completedNormSq_smul_negI (dlimCompletionSub A B)
  exact Rle_trans (Rle_of_Req (Rmul_congr hFinal hFinal))
    (Rle_trans (completedInner_re_cs_sharp
        (dlimCompletionSmul (⟨zero, Rneg one⟩ : Complex) (dlimCompletionSub A B)) V)
      (Rle_of_Req (Rmul_congr hNorm (Req_refl (completedNormSq V)))))

-- ===========================================================================
-- Squared-tolerance convergence predicates (sqrt-free).
-- ===========================================================================

/-- Convergence in the completion (squared distance below `1/(k+1)` eventually). -/
def CompletionTendsTo (Zs : Nat → DLimCompletionRaw) (Z : DLimCompletionRaw) : Prop :=
  ∀ k, ∃ N, ∀ n, N ≤ n → Rle (completedDist2 (Zs n) Z) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))

/-- Squared-tolerance complex convergence (real AND imaginary coordinates). -/
def ComplexTendsTo (zs : Nat → Complex) (z : Complex) : Prop :=
  (∀ k, ∃ N, ∀ n, N ≤ n →
    Rle (Rmul (Rsub (zs n).re z.re) (Rsub (zs n).re z.re)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) ∧
  (∀ k, ∃ N, ∀ n, N ≤ n →
    Rle (Rmul (Rsub (zs n).im z.im) (Rsub (zs n).im z.im)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)))

/-- **Constant-absorption reschedule**: if `Δ n ≤ d²(Xs n, X)·‖V‖²` for all `n` and `d²(Xs n, X) → 0`, then
    `Δ n → 0` in squared tolerance. The fixed constant `‖V‖²` is bounded by a natural `B+1`, and the
    completion tolerance is taken at index `(B+1)(k+1)` so that `d²·‖V‖² ≤ 1/(k+1)` eventually. -/
theorem tendsto_of_le_dist2_scs (V : DLimCompletionRaw) (Xs : Nat → DLimCompletionRaw)
    (X : DLimCompletionRaw) (hX : CompletionTendsTo Xs X) (Δ : Nat → Real)
    (hbound : ∀ n, Rle (Δ n) (Rmul (completedDist2 (Xs n) X) (completedNormSq V))) :
    ∀ k, ∃ N, ∀ n, N ≤ n → Rle (Δ n) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  intro k
  obtain ⟨B, hB⟩ := exists_nat_ge_loc (completedNormSq V)
  obtain ⟨N, hN⟩ := hX ((B + 1) * (k + 1))
  refine ⟨N, fun n hn => ?_⟩
  have hd : Rle (completedDist2 (Xs n) X)
      (ofQ (⟨1, (B + 1) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _)) := hN n hn
  have hVB : Rle (completedNormSq V) (ofQ (⟨(B : Int) + 1, 1⟩ : Q) Nat.one_pos) :=
    Rle_trans hB (Rle_ofQ_of_Qle_loc Nat.one_pos Nat.one_pos
      (by simp only [Qle]; push_cast; omega))
  have hVnn : Rnonneg (completedNormSq V) := completedNormSq_nonneg V
  have hmul : Rle (Rmul (completedDist2 (Xs n) X) (completedNormSq V))
      (Rmul (ofQ (⟨1, (B + 1) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _))
            (ofQ (⟨(B : Int) + 1, 1⟩ : Q) Nat.one_pos)) :=
    Rle_trans (Rmul_le_Rmul_right_loc hVnn hd)
      (Rmul_le_Rmul_left_loc
        (Rnonneg_ofQ_loc (Nat.succ_pos _) (show (0 : Int) ≤ 1 by decide)) hVB)
  have hQ : Qle (mul (⟨1, (B + 1) * (k + 1) + 1⟩ : Q) (⟨(B : Int) + 1, 1⟩ : Q)) (⟨1, k + 1⟩ : Q) := by
    show (1 * ((B : Int) + 1)) * (((k + 1 : Nat)) : Int)
          ≤ (1 : Int) * ((((B + 1) * (k + 1) + 1) * 1 : Nat) : Int)
    have key : (1 : Int) * ((((B + 1) * (k + 1) + 1) * 1 : Nat) : Int)
          = (1 * ((B : Int) + 1)) * (((k + 1 : Nat)) : Int) + 1 := by push_cast; ring_uor
    omega
  have hrat : Rle (Rmul (ofQ (⟨1, (B + 1) * (k + 1) + 1⟩ : Q) (Nat.succ_pos _))
                        (ofQ (⟨(B : Int) + 1, 1⟩ : Q) Nat.one_pos))
                  (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) :=
    Rle_trans (Rle_of_Req (Rmul_ofQ_ofQ_loc (Nat.succ_pos _) Nat.one_pos))
      (Rle_ofQ_of_Qle_loc (Qmul_den_pos (Nat.succ_pos _) Nat.one_pos) (Nat.succ_pos k) hQ)
  exact Rle_trans (hbound n) (Rle_trans hmul hrat)

-- ===========================================================================
-- TARGET B — GENUINE full-complex fixed-vector LIMIT continuity (unconditional).
-- ===========================================================================

/-- **GENUINE fixed-vector inner-product continuity**: for a fixed but arbitrary `V`, if `Xs n → X` in
    squared distance then `⟨V, Xs n⟩ → ⟨V, X⟩` in BOTH real and imaginary coordinates, UNCONDITIONALLY
    (works even at `‖V‖²≈0`, no cancellable factor). Each squared coordinate difference is bounded by
    `‖V‖²·d²(Xs n, X)` through the SHARP CS (`inner_re_diff_sq_le_scs` / `inner_im_diff_sq_le_scs`), and the
    fixed constant `‖V‖²` is absorbed by `tendsto_of_le_dist2_scs`. -/
theorem inner_fixed_tendsto_scs (V : DLimCompletionRaw) (Xs : Nat → DLimCompletionRaw)
    (X : DLimCompletionRaw) (hX : CompletionTendsTo Xs X) :
    ComplexTendsTo (fun n => completedInner V (Xs n)) (completedInner V X) := by
  refine ⟨?_, ?_⟩
  · exact tendsto_of_le_dist2_scs V Xs X hX
      (fun n => Rmul (Rsub (completedInner V (Xs n)).re (completedInner V X).re)
                     (Rsub (completedInner V (Xs n)).re (completedInner V X).re))
      (fun n => inner_re_diff_sq_le_scs V (Xs n) X)
  · exact tendsto_of_le_dist2_scs V Xs X hX
      (fun n => Rmul (Rsub (completedInner V (Xs n)).im (completedInner V X).im)
                     (Rsub (completedInner V (Xs n)).im (completedInner V X).im))
      (fun n => inner_im_diff_sq_le_scs V (Xs n) X)

end UOR.Bridge.F1Square.Square
