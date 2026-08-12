/-
# Completeness of the direct-limit completion

Every completion-Cauchy sequence of completion members converges to a completion member — the
fixed-modulus (SQUARED-distance) completeness that, with the isometric embedding (`ofHom`) and density
(`completion_dense`), makes `(DLimCompletionRaw / DLimCompletionEq, completedInner)` a constructive
Bishop completion of the finite-support direct limit (NOT a Hilbert space — no √-norm, factor-2 quasi-triangle).

* `CompletionCauchyU Z` — `Z : ℕ → DLimCompletionRaw` is Cauchy: `d²(Z j, Z k) ≤ M(j,k)`.
* `completionLim Z hZ` — the DIAGONAL limit member (`.seq m = (Z_{8m+7})_{2(9(m+1)²+1)}`; the reschedule
  `8m+7` beats the double-quasi-triangle factor-4 and the density rate `9(m+1)²` gives the rigid modulus).
* `completion_complete` — `Z m → completionLim Z hZ` in the completion metric, with explicit modulus.

WHNF NOTE: `completedDist2` / `completedInner` are NEVER unfolded by defeq here — the quasi-triangle,
symmetry, and embedding isometry are proved through the already-established `completedInner_*` pre-Hilbert
laws (`add_right`/`conj`/`congr`) and a completion-level polarization, used purely as black boxes. This
sidesteps both the schedule-alignment problem (`Fsched` differs per pair) and the completion whnf blow-up.

Not touched: operators, adjoints, self-adjointness, Atlas provenance, the Hilbert–Pólya crux.
-/
import F1Square.Square.DlimCompletionDense

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Complex / Real micro-helpers (leaf names end in `_cpl`).
-- ===========================================================================

/-- `a = b → a ≤ b` on ℤ (core has no bare `le_of_eq`). -/
theorem le_of_eq_cpl {a b : Int} (h : a = b) : a ≤ b := by omega

/-- `−(−x) ≈ x` on ℝ (local copy). -/
theorem Rneg_Rneg_cpl (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by simp only [Rneg, Qeq, neg]; push_cast; ring_uor)

/-- `z + 0 ≈ z` on ℂ. -/
theorem Cadd_zero_cpl (z : Complex) : Ceq (Cadd z Czero) z :=
  ⟨Radd_zero z.re, Radd_zero z.im⟩

/-- `−(−z) ≈ z` on ℂ. -/
theorem Cneg_Cneg_cpl (z : Complex) : Ceq (Cneg (Cneg z)) z :=
  ⟨Rneg_Rneg_cpl z.re, Rneg_Rneg_cpl z.im⟩

/-- `Cneg` respects `Ceq`. -/
theorem Cneg_congr_cpl {z w : Complex} (h : Ceq z w) : Ceq (Cneg z) (Cneg w) :=
  ⟨Rneg_congr h.1, Rneg_congr h.2⟩

/-- `conj(−z) ≈ −conj z` on ℂ (definitional). -/
theorem Cconj_Cneg_cpl (z : Complex) : Ceq (Cconj (Cneg z)) (Cneg (Cconj z)) :=
  Ceq_refl _

/-- If `z ≈ z + z` then `z ≈ 0`. -/
theorem Ceq_zero_of_eq_add_self_cpl {z : Complex} (h : Ceq z (Cadd z z)) : Ceq z Czero := by
  have e1 : Ceq (Cadd z (Cneg z)) (Cadd (Cadd z z) (Cneg z)) :=
    Cadd_congr h (Ceq_refl (Cneg z))
  have e2 : Ceq (Cadd (Cadd z z) (Cneg z)) z :=
    Ceq_trans (Cadd_assoc z z (Cneg z))
      (Ceq_trans (Cadd_congr (Ceq_refl z) (Cadd_neg z)) (Cadd_zero_cpl z))
  exact Ceq_trans (Ceq_symm e2) (Ceq_trans (Ceq_symm e1) (Cadd_neg z))

/-- If `a + b ≈ 0` then `b ≈ −a`. -/
theorem Ceq_neg_of_add_eq_zero_cpl {a b : Complex} (h : Ceq (Cadd a b) Czero) :
    Ceq b (Cneg a) := by
  have e1 : Ceq (Cadd (Cneg a) (Cadd a b)) (Cadd (Cneg a) Czero) :=
    Cadd_congr (Ceq_refl (Cneg a)) h
  have e2 : Ceq (Cadd (Cneg a) (Cadd a b)) b :=
    Ceq_trans (Ceq_symm (Cadd_assoc (Cneg a) a b))
      (Ceq_trans (Cadd_congr (Ceq_trans (Cadd_comm (Cneg a) a) (Cadd_neg a)) (Ceq_refl b))
        (Ceq_trans (Cadd_comm Czero b) (Cadd_zero_cpl b)))
  exact Ceq_trans (Ceq_symm e2) (Ceq_trans e1 (Cadd_zero_cpl (Cneg a)))

-- ===========================================================================
-- Completion inner-product algebra (setoid-respecting; schedule-agnostic).
-- ===========================================================================

/-- **Left-additivity** of the completed inner product (from right-additivity + Hermitian symmetry). -/
theorem completedInner_add_left_cpl (X Y Z : DLimCompletionRaw) :
    Ceq (completedInner (dlimCompletionAdd X Y) Z)
        (Cadd (completedInner X Z) (completedInner Y Z)) :=
  Ceq_trans (completedInner_conj (dlimCompletionAdd X Y) Z)
    (Ceq_trans (Cconj_congr (completedInner_add_right Z X Y))
      (Ceq_trans (Cconj_Cadd (completedInner Z X) (completedInner Z Y))
        (Cadd_congr (Ceq_symm (completedInner_conj X Z))
                    (Ceq_symm (completedInner_conj Y Z)))))

/-- `⟨X, 0⟩ ≈ 0`. -/
theorem completedInner_zero_right_cpl (X : DLimCompletionRaw) :
    Ceq (completedInner X dlimCompletionZero) Czero := by
  have hsplit : Ceq (completedInner X dlimCompletionZero)
      (Cadd (completedInner X dlimCompletionZero) (completedInner X dlimCompletionZero)) :=
    Ceq_trans
      (completedInner_congr (DLimCompletionEq_refl X)
        (DLimCompletionEq_symm (dlimCompletionAdd_zero dlimCompletionZero)))
      (completedInner_add_right X dlimCompletionZero dlimCompletionZero)
  exact Ceq_zero_of_eq_add_self_cpl hsplit

/-- `⟨X, −Y⟩ ≈ −⟨X, Y⟩`. -/
theorem completedInner_neg_right_cpl (X Y : DLimCompletionRaw) :
    Ceq (completedInner X (dlimCompletionNeg Y)) (Cneg (completedInner X Y)) := by
  have hzero : Ceq (Cadd (completedInner X Y) (completedInner X (dlimCompletionNeg Y))) Czero :=
    Ceq_trans (Ceq_symm (completedInner_add_right X Y (dlimCompletionNeg Y)))
      (Ceq_trans
        (completedInner_congr (DLimCompletionEq_refl X) (dlimCompletionAdd_neg Y))
        (completedInner_zero_right_cpl X))
  exact Ceq_neg_of_add_eq_zero_cpl hzero

/-- `⟨−X, Y⟩ ≈ −⟨X, Y⟩` (from `neg_right` and Hermitian symmetry). -/
theorem completedInner_neg_left_cpl (X Y : DLimCompletionRaw) :
    Ceq (completedInner (dlimCompletionNeg X) Y) (Cneg (completedInner X Y)) :=
  Ceq_trans (completedInner_conj (dlimCompletionNeg X) Y)
    (Ceq_trans (Cconj_congr (completedInner_neg_right_cpl Y X))
      (Ceq_trans (Cconj_Cneg_cpl (completedInner Y X))
        (Cneg_congr_cpl (Ceq_symm (completedInner_conj X Y)))))

/-- The completed squared norm respects the completion setoid. -/
theorem completedNormSq_congr_cpl {X X' : DLimCompletionRaw} (h : DLimCompletionEq X X') :
    Req (completedNormSq X) (completedNormSq X') :=
  (completedInner_congr h h).1

/-- `‖−X‖² ≈ ‖X‖²`. -/
theorem completedNormSq_neg_cpl (X : DLimCompletionRaw) :
    Req (completedNormSq (dlimCompletionNeg X)) (completedNormSq X) :=
  (Ceq_trans (completedInner_neg_left_cpl X (dlimCompletionNeg X))
    (Ceq_trans (Cneg_congr_cpl (completedInner_neg_right_cpl X X))
      (Cneg_Cneg_cpl (completedInner X X)))).1

/-- **Parallelogram expansion** at the completion level:
    `‖u+v‖² ≈ ‖u‖² + Re⟨u,v⟩ + Re⟨v,u⟩ + ‖v‖²`. -/
theorem completedNormSq_add_expand_cpl (u v : DLimCompletionRaw) :
    Req (completedNormSq (dlimCompletionAdd u v))
        (Radd (Radd (completedNormSq u) (completedInner u v).re)
              (Radd (completedInner v u).re (completedNormSq v))) :=
  (Ceq_trans (completedInner_add_left_cpl u v (dlimCompletionAdd u v))
    (Cadd_congr (completedInner_add_right u u v) (completedInner_add_right v u v))).1

-- ===========================================================================
-- Completion group algebra: the telescoping identity for the difference.
-- ===========================================================================

/-- `0 + W ≈ W`. -/
theorem zeroAdd_cpl (W : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd dlimCompletionZero W) W :=
  DLimCompletionEq_trans (dlimCompletionAdd_comm dlimCompletionZero W) (dlimCompletionAdd_zero W)

/-- `(−W) + W ≈ 0`. -/
theorem negAddSelf_cpl (W : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd (dlimCompletionNeg W) W) dlimCompletionZero :=
  DLimCompletionEq_trans (dlimCompletionAdd_comm (dlimCompletionNeg W) W) (dlimCompletionAdd_neg W)

/-- **Telescoping**: `X − Z ≈ (X − Y) + (Y − Z)` in the completion group. -/
theorem telescope_cpl (X Y Z : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionSub X Z)
      (dlimCompletionAdd (dlimCompletionSub X Y) (dlimCompletionSub Y Z)) := by
  have step : DLimCompletionEq
      (dlimCompletionAdd (dlimCompletionAdd X (dlimCompletionNeg Y))
                         (dlimCompletionAdd Y (dlimCompletionNeg Z)))
      (dlimCompletionAdd X (dlimCompletionNeg Z)) := by
    refine DLimCompletionEq_trans
      (dlimCompletionAdd_assoc X (dlimCompletionNeg Y)
        (dlimCompletionAdd Y (dlimCompletionNeg Z))) ?_
    refine DLimCompletionEq_trans
      (dlimCompletionAdd_congr (DLimCompletionEq_refl X)
        (DLimCompletionEq_symm
          (dlimCompletionAdd_assoc (dlimCompletionNeg Y) Y (dlimCompletionNeg Z)))) ?_
    refine DLimCompletionEq_trans
      (dlimCompletionAdd_congr (DLimCompletionEq_refl X)
        (dlimCompletionAdd_congr (negAddSelf_cpl Y)
          (DLimCompletionEq_refl (dlimCompletionNeg Z)))) ?_
    exact dlimCompletionAdd_congr (DLimCompletionEq_refl X) (zeroAdd_cpl (dlimCompletionNeg Z))
  exact DLimCompletionEq_symm step

-- ===========================================================================
-- THE THREE INFRA TARGETS: isometry, symmetry, quasi-triangle.
-- ===========================================================================

/-- **Isometry of the embedding** `of`: the completed squared distance between images equals the
    direct-limit squared distance. -/
theorem completedDist2_of_cpl (a b : DLimRaw) :
    Req (completedDist2 (DLimCompletionRaw.of a) (DLimCompletionRaw.of b)) (dlimDist2 a b) := by
  have hsub : DLimCompletionEq
      (dlimCompletionSub (DLimCompletionRaw.of a) (DLimCompletionRaw.of b))
      (DLimCompletionRaw.of (dlimSub a b)) :=
    DLimCompletionEq_trans
      (dlimCompletionAdd_congr (DLimCompletionEq_refl (DLimCompletionRaw.of a))
        (DLimCompletionEq_symm (DLimCompletionEq_of_neg b)))
      (DLimCompletionEq_symm (DLimCompletionEq_of_add a (dlimNeg b)))
  exact Req_trans (completedNormSq_congr_cpl hsub)
    ((completedInner_of (dlimSub a b) (dlimSub a b)).1)

/-- **Polarization** at the completion level:
    `d²(X,Y) ≈ ‖X‖² − Re⟨X,Y⟩ − Re⟨Y,X⟩ + ‖Y‖²`. -/
theorem dist2_polar_cpl (X Y : DLimCompletionRaw) :
    Req (completedDist2 X Y)
        (Radd (Radd (completedNormSq X) (Rneg (completedInner X Y).re))
              (Radd (Rneg (completedInner Y X).re) (completedNormSq Y))) := by
  refine Req_trans (completedNormSq_add_expand_cpl X (dlimCompletionNeg Y)) ?_
  exact Radd_congr
    (Radd_congr (Req_refl _) (completedInner_neg_right_cpl X Y).1)
    (Radd_congr (completedInner_neg_left_cpl Y X).1 (completedNormSq_neg_cpl Y))

/-- **Symmetry** of the completed squared distance. -/
theorem completedDist2_symm_cpl (X Y : DLimCompletionRaw) :
    Req (completedDist2 X Y) (completedDist2 Y X) := by
  refine Req_trans (dist2_polar_cpl X Y) (Req_trans ?_ (Req_symm (dist2_polar_cpl Y X)))
  apply Req_of_seq_Qeq
  intro n
  simp only [Radd, Rneg, Qeq, add, neg]
  push_cast
  ring_uor

/-- **Quasi-triangle** for the completed squared distance (factor-2 form). -/
theorem completedDist2_quasitriangle_cpl (X Y Z : DLimCompletionRaw) :
    Rle (completedDist2 X Z)
      (Radd (Radd (completedDist2 X Y) (completedDist2 X Y))
            (Radd (completedDist2 Y Z) (completedDist2 Y Z))) := by
  show Rle (completedDist2 X Z)
    (Radd (Radd (completedNormSq (dlimCompletionSub X Y)) (completedNormSq (dlimCompletionSub X Y)))
          (Radd (completedNormSq (dlimCompletionSub Y Z)) (completedNormSq (dlimCompletionSub Y Z))))
  have hcong : Req (completedDist2 X Z)
      (completedNormSq (dlimCompletionAdd (dlimCompletionSub X Y) (dlimCompletionSub Y Z))) :=
    completedNormSq_congr_cpl (telescope_cpl X Y Z)
  have hexp := completedNormSq_add_expand_cpl (dlimCompletionSub X Y) (dlimCompletionSub Y Z)
  have hnn : Rnonneg (completedDist2 (dlimCompletionSub X Y) (dlimCompletionSub Y Z)) :=
    completedDist2_nonneg _ _
  have hcross :
      Rle (Radd (completedInner (dlimCompletionSub X Y) (dlimCompletionSub Y Z)).re
                (completedInner (dlimCompletionSub Y Z) (dlimCompletionSub X Y)).re)
          (Radd (completedNormSq (dlimCompletionSub X Y))
                (completedNormSq (dlimCompletionSub Y Z))) := by
    apply Rle_of_Rnonneg_Rsub_loc
    refine Rnonneg_congr_loc ?_ hnn
    refine Req_trans (dist2_polar_cpl (dlimCompletionSub X Y) (dlimCompletionSub Y Z)) ?_
    apply Req_of_seq_Qeq
    intro n
    simp only [Rsub, Radd, Rneg, Qeq, add, neg]
    push_cast
    ring_uor
  refine Rle_trans (Rle_of_Req hcong) ?_
  refine Rle_trans (Rle_of_Req hexp) ?_
  have hE : Req
      (Radd (Radd (completedNormSq (dlimCompletionSub X Y))
                  (completedInner (dlimCompletionSub X Y) (dlimCompletionSub Y Z)).re)
            (Radd (completedInner (dlimCompletionSub Y Z) (dlimCompletionSub X Y)).re
                  (completedNormSq (dlimCompletionSub Y Z))))
      (Radd (Radd (completedNormSq (dlimCompletionSub X Y))
                  (completedNormSq (dlimCompletionSub Y Z)))
            (Radd (completedInner (dlimCompletionSub X Y) (dlimCompletionSub Y Z)).re
                  (completedInner (dlimCompletionSub Y Z) (dlimCompletionSub X Y)).re)) := by
    apply Req_of_seq_Qeq; intro n; simp only [Radd, Qeq, add]; push_cast; ring_uor
  refine Rle_trans (Rle_of_Req hE) ?_
  refine Rle_trans (Radd_le_add_loc (Rle_refl _) hcross) ?_
  apply Rle_of_Req
  apply Req_of_seq_Qeq; intro n; simp only [Radd, Qeq, add]; push_cast; ring_uor

-- ===========================================================================
-- Explicit-index density (a re-proof of `completion_dense` exposing the index).
-- ===========================================================================

/-- **Density at the explicit index** `2·(k+1)`: `d²(X, of (X_{2(k+1)})) ≤ 1/(k+1)`. -/
theorem completion_dense_at_cpl (X : DLimCompletionRaw) (k : Nat) :
    Rle (completedDist2 X (DLimCompletionRaw.of (X.seq (2 * (k + 1)))))
      (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  obtain ⟨σ, hg, hσ, heq⟩ := completedDist2_reduce_dns X (X.seq (2 * (k + 1)))
  rw [heq]
  refine Rle_Rlim_ofQ_eventual_dns _ hg (⟨1, k + 1⟩ : Q) (Nat.succ_pos k) (fun t => ?_)
  refine ⟨k, fun n hn => ?_⟩
  have hi : 2 * (k + 1) ≤ σ n + 1 := by have := hσ n; omega
  have hj : 2 * (k + 1) ≤ 2 * (k + 1) + 1 := by omega
  have hmpos : 0 < k + 1 := Nat.succ_pos k
  have hA : Qle (mul (⟨1, k + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (⟨1, k + 1⟩ : Q) := by
    have hkk : ((k + 1 : Nat) : Int) ≤ (((k + 1) * (k + 1) : Nat) : Int) := by
      exact_mod_cast Nat.le_mul_of_pos_left (k + 1) (Nat.succ_pos k)
    simp only [Qle, mul]; omega
  have hBle : Qle (⟨1, k + 1⟩ : Q) (add (⟨1, k + 1⟩ : Q) (⟨1, t + 1⟩ : Q)) :=
    Qle_self_add (by show (0 : Int) ≤ 1; omega)
  have hQ : Qle (mul (⟨1, k + 1⟩ : Q) (⟨1, k + 1⟩ : Q)) (add (⟨1, k + 1⟩ : Q) (⟨1, t + 1⟩ : Q)) :=
    Qle_trans (Nat.succ_pos k) hA hBle
  exact Rle_trans (X.reg (σ n) (2 * (k + 1)))
    (Rle_trans (dlimCauchyMod_le_inv_sq (σ n) (2 * (k + 1)) (k + 1) hmpos hi hj)
      (Rle_ofQ_of_Qle_loc _ _ hQ))

-- ===========================================================================
-- The load-bearing integer inequality for the rigid Cauchy modulus.
-- ===========================================================================

/-- `(128b²+36(a+b)²+256a²)·(ab)² ≤ (a+b)²·576a²b²` for `a,b ≥ 0`
    (the rigid-modulus integer inequality after clearing to denominator `576a²b²`). -/
theorem sumbound_key_cpl (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (128 * b * b + 36 * (a + b) * (a + b) + 256 * a * a) * (a * b * (a * b))
      ≤ ((b + a) * (b + a)) * (576 * (a * a) * (b * b)) := by
  have h3 : 0 ≤ a * b := Int.mul_nonneg ha hb
  have hW : 0 ≤ a * b * (a * b) := Int.mul_nonneg h3 h3
  have hq : 0 ≤ 284 * (a * a) + 1080 * (a * b) + 412 * (b * b) := by
    have t1 : 0 ≤ 284 * (a * a) := Int.mul_nonneg (by omega) (Int.mul_nonneg ha ha)
    have t2 : 0 ≤ 1080 * (a * b) := Int.mul_nonneg (by omega) h3
    have t3 : 0 ≤ 412 * (b * b) := Int.mul_nonneg (by omega) (Int.mul_nonneg hb hb)
    omega
  have hid : ((b + a) * (b + a)) * (576 * (a * a) * (b * b))
        - (128 * b * b + 36 * (a + b) * (a + b) + 256 * a * a) * (a * b * (a * b))
      = (a * b * (a * b)) * (284 * (a * a) + 1080 * (a * b) + 412 * (b * b)) := by ring_uor
  have hmn := Int.mul_nonneg hW hq
  omega

/-- **Generic tree collapse**: the diagonal's factor-`2/4/4` binary tree of same-denominator constants
    collapses to a single fraction. Proved once over abstract `p,q,r,D` so the reflected identity stays
    small. -/
theorem tree_collapse_cpl (p q r : Int) (D : Nat) (hD : 0 < D) :
    Req
      (Radd (Radd (ofQ ⟨p, D⟩ hD) (ofQ ⟨p, D⟩ hD))
        (Radd (Radd (Radd (ofQ ⟨q, D⟩ hD) (ofQ ⟨q, D⟩ hD)) (Radd (ofQ ⟨r, D⟩ hD) (ofQ ⟨r, D⟩ hD)))
              (Radd (Radd (ofQ ⟨q, D⟩ hD) (ofQ ⟨q, D⟩ hD)) (Radd (ofQ ⟨r, D⟩ hD) (ofQ ⟨r, D⟩ hD)))))
      (ofQ ⟨2 * p + 4 * q + 4 * r, D⟩ hD) := by
  apply Req_of_seq_Qeq
  intro n
  simp only [Radd, ofQ, Qeq, add]
  push_cast
  ring_uor

-- ===========================================================================
-- THE COMPLETION-CAUCHY PREDICATE and the DIAGONAL LIMIT.
-- ===========================================================================

/-- A sequence of completion members is completion-Cauchy at the rigid squared modulus. -/
def CompletionCauchyU (Z : Nat → DLimCompletionRaw) : Prop :=
  ∀ j k : Nat, Rle (completedDist2 (Z j) (Z k)) (dlimCauchyModR j k)

/-- Positivity of the density denominator `9(m+1)²`. -/
private theorem nine_sq_pos_cpl (m : Nat) : 0 < 9 * (m + 1) * (m + 1) :=
  Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos m)) (Nat.succ_pos m)

set_option maxHeartbeats 1200000 in
/-- **The diagonal is Cauchy at the rigid modulus** — the load-bearing regularity of the completion
    limit member. -/
theorem hcauchy_cpl (Z : Nat → DLimCompletionRaw) (hZ : CompletionCauchyU Z) :
    DLimCauchyU (fun m => (Z (8 * m + 7)).seq (2 * (9 * (m + 1) * (m + 1) + 1))) := by
  intro j k
  show Rle (dlimDist2 ((Z (8 * j + 7)).seq (2 * (9 * (j + 1) * (j + 1) + 1)))
                      ((Z (8 * k + 7)).seq (2 * (9 * (k + 1) * (k + 1) + 1))))
    (dlimCauchyModR j k)
  have hDj : 0 < 9 * (j + 1) * (j + 1) := nine_sq_pos_cpl j
  have hDk : 0 < 9 * (k + 1) * (k + 1) := nine_sq_pos_cpl k
  -- density bounds, weakened to 1/(9(·+1)²)
  have hPj : Rle (completedDist2 (Z (8 * j + 7))
        (DLimCompletionRaw.of ((Z (8 * j + 7)).seq (2 * (9 * (j + 1) * (j + 1) + 1)))))
      (ofQ (⟨1, 9 * (j + 1) * (j + 1)⟩ : Q) hDj) := by
    refine Rle_trans (completion_dense_at_cpl (Z (8 * j + 7)) (9 * (j + 1) * (j + 1)))
      (Rle_ofQ_of_Qle_loc _ _ ?_)
    simp only [Qle]; push_cast; omega
  have hPk : Rle (completedDist2 (Z (8 * k + 7))
        (DLimCompletionRaw.of ((Z (8 * k + 7)).seq (2 * (9 * (k + 1) * (k + 1) + 1)))))
      (ofQ (⟨1, 9 * (k + 1) * (k + 1)⟩ : Q) hDk) := by
    refine Rle_trans (completion_dense_at_cpl (Z (8 * k + 7)) (9 * (k + 1) * (k + 1)))
      (Rle_ofQ_of_Qle_loc _ _ ?_)
    simp only [Qle]; push_cast; omega
  -- common denominator CD = 576·(j+1)²·(k+1)²
  have hCD : 0 < (576 * (j + 1) * (j + 1) * (k + 1) * (k + 1) : Nat) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos j))
      (Nat.succ_pos j)) (Nat.succ_pos k)) (Nat.succ_pos k)
  -- rebound each leaf to the common denominator (with symmetry for the P-leaf)
  have hP : Rle (completedDist2
        (DLimCompletionRaw.of ((Z (8 * j + 7)).seq (2 * (9 * (j + 1) * (j + 1) + 1))))
        (Z (8 * j + 7)))
      (ofQ (⟨(64 * (k + 1) * (k + 1) : Nat),
            576 * (j + 1) * (j + 1) * (k + 1) * (k + 1)⟩ : Q) hCD) :=
    Rle_trans (Rle_of_Req (completedDist2_symm_cpl _ _))
      (Rle_trans hPj (Rle_of_Req (ofQ_respects hDj hCD (by simp only [Qeq]; push_cast; ring_uor))))
  have hR : Rle (completedDist2 (Z (8 * k + 7))
        (DLimCompletionRaw.of ((Z (8 * k + 7)).seq (2 * (9 * (k + 1) * (k + 1) + 1)))))
      (ofQ (⟨(64 * (j + 1) * (j + 1) : Nat),
            576 * (j + 1) * (j + 1) * (k + 1) * (k + 1)⟩ : Q) hCD) :=
    Rle_trans hPk (Rle_of_Req (ofQ_respects hDk hCD (by simp only [Qeq]; push_cast; ring_uor)))
  have hQ : Rle (completedDist2 (Z (8 * j + 7)) (Z (8 * k + 7)))
      (ofQ (⟨(9 * ((j + 1) + (k + 1)) * ((j + 1) + (k + 1)) : Nat),
            576 * (j + 1) * (j + 1) * (k + 1) * (k + 1)⟩ : Q) hCD) :=
    Rle_trans (hZ (8 * j + 7) (8 * k + 7))
      (Rle_of_Req (Req_of_seq_Qeq (fun n => by
        simp only [dlimCauchyModR, ofQ, Qeq, add, mul]; push_cast; ring_uor)))
  -- isometry + two quasi-triangles + leaf bounds → the common-denominator ofQ tree
  refine Rle_trans (Rle_of_Req (Req_symm (completedDist2_of_cpl _ _))) ?_
  refine Rle_trans (completedDist2_quasitriangle_cpl
    (DLimCompletionRaw.of ((Z (8 * j + 7)).seq (2 * (9 * (j + 1) * (j + 1) + 1))))
    (Z (8 * j + 7))
    (DLimCompletionRaw.of ((Z (8 * k + 7)).seq (2 * (9 * (k + 1) * (k + 1) + 1))))) ?_
  have hDB := Rle_trans (completedDist2_quasitriangle_cpl (Z (8 * j + 7)) (Z (8 * k + 7))
        (DLimCompletionRaw.of ((Z (8 * k + 7)).seq (2 * (9 * (k + 1) * (k + 1) + 1)))))
      (Radd_le_add_loc (Radd_le_add_loc hQ hQ) (Radd_le_add_loc hR hR))
  refine Rle_trans (Radd_le_add_loc (Radd_le_add_loc hP hP) (Radd_le_add_loc hDB hDB)) ?_
  -- collapse the common-denominator tree and finish with the rigid modulus inequality
  have hMden : 0 < (mul (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))
      (add (⟨1, j + 1⟩ : Q) (⟨1, k + 1⟩ : Q))).den :=
    Qmul_den_pos (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
      (add_den_pos (Nat.succ_pos j) (Nat.succ_pos k))
  refine Rle_trans (Rle_of_Req (tree_collapse_cpl _ _ _ _ hCD)) (Rle_ofQ_of_Qle_loc hCD hMden ?_)
  simp only [Qle, mul, add]
  push_cast
  have haJ : (0 : Int) ≤ (j : Int) + 1 := by omega
  have hbK : (0 : Int) ≤ (k : Int) + 1 := by omega
  revert haJ hbK
  generalize ((j : Int) + 1) = J
  generalize ((k : Int) + 1) = K
  intro haJ hbK
  calc (2 * (64 * K * K) + 4 * (9 * (J + K) * (J + K)) + 4 * (64 * J * J)) * (J * K * (J * K))
      = (128 * K * K + 36 * (J + K) * (J + K) + 256 * J * J) * (J * K * (J * K)) := by ring_uor
    _ ≤ ((K + J) * (K + J)) * (576 * (J * J) * (K * K)) := sumbound_key_cpl J K haJ hbK
    _ = (1 * K + 1 * J) * (1 * K + 1 * J) * (576 * J * J * K * K) := by ring_uor

/-- `n ≤ n·m` when `1 ≤ m` (for the loose-modulus denominator weakenings). -/
private theorem le_mul_self_cpl (n m : Nat) (hm : 1 ≤ m) : n ≤ n * m := by
  have h := Nat.mul_le_mul (Nat.le_refl n) hm
  simpa using h

/-- `16(k+1) ≤ (4(k+1))²`. -/
private theorem sixteen_le_cpl (k : Nat) : 16 * (k + 1) ≤ 4 * (k + 1) * (4 * (k + 1)) := by
  have heq : (4 * (k + 1) * (4 * (k + 1)) : Nat) = 16 * (k + 1) * (k + 1) := by
    have hI : (4 * (k + 1) * (4 * (k + 1)) : Int) = (16 * (k + 1) * (k + 1) : Int) := by
      push_cast; ring_uor
    exact_mod_cast hI
  rw [heq]
  exact le_mul_self_cpl (16 * (k + 1)) (k + 1) (by omega)

/-- **Generic collapse for the convergence tree** (factor `4/4/2`). -/
theorem tree_collapse2_cpl (a b e : Int) (D : Nat) (hD : 0 < D) :
    Req
      (Radd
        (Radd (Radd (Radd (ofQ ⟨a, D⟩ hD) (ofQ ⟨a, D⟩ hD)) (Radd (ofQ ⟨b, D⟩ hD) (ofQ ⟨b, D⟩ hD)))
              (Radd (Radd (ofQ ⟨a, D⟩ hD) (ofQ ⟨a, D⟩ hD)) (Radd (ofQ ⟨b, D⟩ hD) (ofQ ⟨b, D⟩ hD))))
        (Radd (ofQ ⟨e, D⟩ hD) (ofQ ⟨e, D⟩ hD)))
      (ofQ ⟨4 * a + 4 * b + 2 * e, D⟩ hD) := by
  apply Req_of_seq_Qeq
  intro n
  simp only [Radd, ofQ, Qeq, add]
  push_cast
  ring_uor

-- ===========================================================================
-- THE COMPLETION LIMIT MEMBER and COMPLETENESS (diagonal convergence).
-- ===========================================================================

/-- **The completion-limit member**: the diagonal `m ↦ (Z_{8m+7})_{2(9(m+1)²+1)}`, regular by
    `hcauchy_cpl`. -/
def completionLim (Z : Nat → DLimCompletionRaw) (hZ : CompletionCauchyU Z) : DLimCompletionRaw :=
  ⟨fun m => (Z (8 * m + 7)).seq (2 * (9 * (m + 1) * (m + 1) + 1)), hcauchy_cpl Z hZ⟩

set_option maxHeartbeats 1200000 in
/-- **COMPLETENESS**: every completion-Cauchy sequence converges to the completion-limit member. -/
theorem completion_complete (Z : Nat → DLimCompletionRaw) (hZ : CompletionCauchyU Z) :
    ∀ k : Nat, ∃ N : Nat, ∀ m : Nat, N ≤ m →
      Rle (completedDist2 (Z m) (completionLim Z hZ)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  intro k
  refine ⟨8 * (k + 1), fun m hm => ?_⟩
  have hD2 : 0 < (16 * (k + 1) : Nat) := by omega
  -- the W-approximant index and the corresponding stage member
  have hb : (completionLim Z hZ).seq (2 * (4 * (k + 1) + 1))
      = (Z (8 * (2 * (4 * (k + 1) + 1)) + 7)).seq
          (2 * (9 * (2 * (4 * (k + 1) + 1) + 1) * (2 * (4 * (k + 1) + 1) + 1) + 1)) := rfl
  -- leaf bound A : d²(Z m, Z_{8·Nap+7}) ≤ 1/(16(k+1))
  have hA : Rle (completedDist2 (Z m) (Z (8 * (2 * (4 * (k + 1) + 1)) + 7)))
      (ofQ (⟨1, 16 * (k + 1)⟩ : Q) hD2) := by
    refine Rle_trans (hZ m (8 * (2 * (4 * (k + 1) + 1)) + 7)) ?_
    refine Rle_trans (dlimCauchyMod_le_inv_sq m (8 * (2 * (4 * (k + 1) + 1)) + 7) (4 * (k + 1))
      (by omega) (by omega) (by omega)) ?_
    refine Rle_ofQ_of_Qle_loc _ _ ?_
    simp only [Qle, mul]
    push_cast
    have hI : (16 * ((k : Int) + 1)) ≤ 4 * ((k : Int) + 1) * (4 * ((k : Int) + 1)) := by
      exact_mod_cast sixteen_le_cpl k
    omega
  -- leaf bound B : d²(Z_{8·Nap+7}, of b) ≤ 1/(16(k+1))
  have hB : Rle (completedDist2 (Z (8 * (2 * (4 * (k + 1) + 1)) + 7))
        (DLimCompletionRaw.of ((completionLim Z hZ).seq (2 * (4 * (k + 1) + 1)))))
      (ofQ (⟨1, 16 * (k + 1)⟩ : Q) hD2) := by
    rw [hb]
    refine Rle_trans (completion_dense_at_cpl (Z (8 * (2 * (4 * (k + 1) + 1)) + 7))
      (9 * (2 * (4 * (k + 1) + 1) + 1) * (2 * (4 * (k + 1) + 1) + 1))) ?_
    refine Rle_ofQ_of_Qle_loc _ _ ?_
    simp only [Qle]
    have hp : 0 < 2 * (4 * (k + 1) + 1) + 1 := by omega
    have h2 : 9 * (2 * (4 * (k + 1) + 1) + 1)
        ≤ 9 * (2 * (4 * (k + 1) + 1) + 1) * (2 * (4 * (k + 1) + 1) + 1) :=
      le_mul_self_cpl _ _ hp
    have hNat : 16 * (k + 1)
        ≤ 9 * (2 * (4 * (k + 1) + 1) + 1) * (2 * (4 * (k + 1) + 1) + 1) + 1 := by omega
    push_cast
    have hI : (16 * ((k : Int) + 1))
        ≤ 9 * (2 * (4 * ((k : Int) + 1) + 1) + 1) * (2 * (4 * ((k : Int) + 1) + 1) + 1) + 1 := by
      exact_mod_cast hNat
    omega
  -- leaf bound E : d²(of b, W) ≤ 4/(16(k+1))
  have hE : Rle (completedDist2 (DLimCompletionRaw.of ((completionLim Z hZ).seq (2 * (4 * (k + 1) + 1))))
        (completionLim Z hZ))
      (ofQ (⟨4, 16 * (k + 1)⟩ : Q) hD2) := by
    refine Rle_trans (Rle_of_Req (completedDist2_symm_cpl _ _)) ?_
    refine Rle_trans (completion_dense_at_cpl (completionLim Z hZ) (4 * (k + 1))) ?_
    refine Rle_ofQ_of_Qle_loc _ _ ?_
    simp only [Qle]; push_cast; omega
  -- assemble the two quasi-triangles
  refine Rle_trans (completedDist2_quasitriangle_cpl (Z m)
    (DLimCompletionRaw.of ((completionLim Z hZ).seq (2 * (4 * (k + 1) + 1))))
    (completionLim Z hZ)) ?_
  have hD := Rle_trans (completedDist2_quasitriangle_cpl (Z m)
      (Z (8 * (2 * (4 * (k + 1) + 1)) + 7))
      (DLimCompletionRaw.of ((completionLim Z hZ).seq (2 * (4 * (k + 1) + 1)))))
    (Radd_le_add_loc (Radd_le_add_loc hA hA) (Radd_le_add_loc hB hB))
  refine Rle_trans (Radd_le_add_loc (Radd_le_add_loc hD hD) (Radd_le_add_loc hE hE)) ?_
  -- collapse and finish (loose tolerance)
  refine Rle_trans (Rle_of_Req (tree_collapse2_cpl _ _ _ _ hD2))
    (Rle_ofQ_of_Qle_loc hD2 (Nat.succ_pos k) ?_)
  simp only [Qle]
  push_cast
  omega

end UOR.Bridge.F1Square.Square
