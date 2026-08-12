/-
# Projection hardening: finProj congruence/linearity/idempotence, exported Pythagoras, coordinate separation

Fold-in hardening for the finite coordinate projection `finProj` (reviewer request):
* `finProj_pythagoras_hd` — the residual Pythagoras `‖X‖² ≈ ‖P_N X‖² + d²(X, P_N X)`, now EXPORTED.
* `finProj_congr_hd` / `finProj_add_hd` / `finProj_smul_hd` — setoid congruence, additivity, ℂ-homogeneity.
* `finProj_idem_hd` — idempotence `P_N (P_N X) ≈ P_N X`.
* `coord_separation_hd` — COMPLETION-COORDINATE SEPARATION: `(∀ i, coord i X ≈ coord i Y) ⟹ X ≈ Y` (vectors
  are determined by their coordinates), via `finProj_converges` + the Archimedean squeeze.
* `finProj_converges_pkg_hd` — the convergence, proved by consuming the PACKAGED `dlimIsCompletion.dense`.

ζ-free (single import `DlimCompletionProj`), whnf-safe.
-/
import F1Square.Square.DlimCompletionProj

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ/ℂ + Archimedean micro-helpers (leaf names end in `_hd`), rebuilt from in-cone primitives.
-- ===========================================================================

/-- `0 ⊕ x ≈ x` on ℝ (replica of the private `Rzero_add_pj`). -/
private theorem Rzero_add_hd (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- The residual `X ⊖ finProj N X` has vanishing coordinates `i < N` (replica of `residual_coords_pj`). -/
private theorem residual_coords_hd (N : Nat) (X : DLimCompletionRaw) :
    ∀ i, i < N → Ceq (coord i (dlimCompletionSub X (finProj N X))) Czero := fun i hi =>
  Ceq_trans (coord_add i X (dlimCompletionNeg (finProj N X)))
    (Ceq_trans (Cadd_congr (Ceq_refl (coord i X))
        (Ceq_trans (completedInner_neg_right_cpl (DLimCompletionRaw.of (dlimBasis i)) (finProj N X))
          (Cneg_congr_cpl (coord_finProj_lt_pj i N X hi))))
      (Cadd_neg (coord i X)))

/-- **Archimedean squeeze**: a nonnegative real that is `≤ 1/(k+1)` for every `k` is `≈ 0` (replica of
    the private `Req_zero_of_nonneg_of_small`). -/
private theorem Req_zero_of_nonneg_of_small_hd {x : Real} (hnn : Rnonneg x)
    (hall : ∀ k : Nat, Rle x (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k))) : Req x zero := by
  refine Rle_antisymm ?_ (Rle_zero_of_Rnonneg hnn)
  intro n
  refine Qarch_gen (C := 1) (x.den_pos n) (add_den_pos (zero.den_pos n) (Nat.succ_pos n)) (fun k => ?_)
  have hb : Qle (x.seq n) (add (⟨1, k + 1⟩ : Q) (⟨2, n + 1⟩ : Q)) := hall k n
  refine Qle_congr_right (add_den_pos (Nat.succ_pos k) (Nat.succ_pos n)) ?_ hb
  simp only [Qeq, add, zero_seq]; push_cast; ring_uor

/-- **Middle-four exchange** in the completion abelian group: `(A⊕B)⊕(C⊕D) ≈ (A⊕C)⊕(B⊕D)`, from
    associativity and commutativity only. -/
private theorem cadd_middle_exchange (A B C D : DLimCompletionRaw) :
    DLimCompletionEq (dlimCompletionAdd (dlimCompletionAdd A B) (dlimCompletionAdd C D))
      (dlimCompletionAdd (dlimCompletionAdd A C) (dlimCompletionAdd B D)) :=
  DLimCompletionEq_trans (dlimCompletionAdd_assoc A B (dlimCompletionAdd C D))
    (DLimCompletionEq_trans
      (dlimCompletionAdd_congr (DLimCompletionEq_refl A)
        (DLimCompletionEq_symm (dlimCompletionAdd_assoc B C D)))
      (DLimCompletionEq_trans
        (dlimCompletionAdd_congr (DLimCompletionEq_refl A)
          (dlimCompletionAdd_congr (dlimCompletionAdd_comm B C) (DLimCompletionEq_refl D)))
        (DLimCompletionEq_trans
          (dlimCompletionAdd_congr (DLimCompletionEq_refl A)
            (dlimCompletionAdd_assoc C B D))
          (DLimCompletionEq_symm (dlimCompletionAdd_assoc A C (dlimCompletionAdd B D))))))

/-- Coordinate-null projections vanish: if every coordinate of `W` is `0`, then `finProj N W ≈ 0`. -/
private theorem finProj_zero_of_coord_zero (N : Nat) (W : DLimCompletionRaw)
    (hW : ∀ i, Ceq (coord i W) Czero) :
    DLimCompletionEq (finProj N W) dlimCompletionZero := by
  induction N with
  | zero => exact DLimCompletionEq_refl _
  | succ N ih =>
      exact DLimCompletionEq_trans
        (dlimCompletionAdd_congr ih
          (DLimCompletionEq_trans (dlimCompletionSmul_congr_scalar (hW N))
            (dlimCompletionZero_smul (DLimCompletionRaw.of (dlimBasis N)))))
        (dlimCompletionAdd_zero dlimCompletionZero)

-- ===========================================================================
-- TARGET 1: residual PYTHAGORAS (exported from the local `hPyth` of `finProj_contraction_pj`).
-- ===========================================================================

/-- **Residual Pythagoras**: `‖X‖² ≈ ‖finProj N X‖² + d²(X, finProj N X)`. -/
theorem finProj_pythagoras_hd (N : Nat) (X : DLimCompletionRaw) :
    Req (completedNormSq X)
      (Radd (completedNormSq (finProj N X)) (completedDist2 X (finProj N X))) := by
  have hPR : Ceq (completedInner (finProj N X) (dlimCompletionSub X (finProj N X))) Czero :=
    finProj_ortho_residual N X (dlimCompletionSub X (finProj N X)) (residual_coords_hd N X)
  have hRP : Ceq (completedInner (dlimCompletionSub X (finProj N X)) (finProj N X)) Czero :=
    Ceq_trans (completedInner_conj (dlimCompletionSub X (finProj N X)) (finProj N X))
      (Ceq_trans (Cconj_congr hPR) Cconj_Czero)
  have hPX : DLimCompletionEq (dlimCompletionAdd (finProj N X) (dlimCompletionSub X (finProj N X))) X :=
    DLimCompletionEq_trans (dlimCompletionAdd_comm (finProj N X) (dlimCompletionSub X (finProj N X)))
      (DLimCompletionEq_trans (dlimCompletionAdd_assoc X (dlimCompletionNeg (finProj N X)) (finProj N X))
        (DLimCompletionEq_trans
          (dlimCompletionAdd_congr (DLimCompletionEq_refl X) (negAddSelf_cpl (finProj N X)))
          (dlimCompletionAdd_zero X)))
  exact Req_trans (completedNormSq_congr_cpl (DLimCompletionEq_symm hPX))
    (Req_trans (completedNormSq_add_expand_cpl (finProj N X) (dlimCompletionSub X (finProj N X)))
      (Req_trans
        (Radd_congr (Radd_congr (Req_refl (completedNormSq (finProj N X))) hPR.1)
          (Radd_congr hRP.1 (Req_refl (completedNormSq (dlimCompletionSub X (finProj N X))))))
        (Radd_congr (Radd_zero (completedNormSq (finProj N X)))
          (Rzero_add_hd (completedNormSq (dlimCompletionSub X (finProj N X)))))))

-- ===========================================================================
-- TARGET 7: convergence, consuming the PACKAGED density `dlimIsCompletion.dense`.
-- ===========================================================================

/-- **Convergence via the packaged completion bundle**: same statement as `finProj_converges_pj`, but the
    density is drawn from `(dlimIsCompletion : CompletionOf dlimPreHilbert).dense`, so the packaged
    relationship is actually consumed. -/
theorem finProj_converges_pkg_hd (X : DLimCompletionRaw) (k : Nat) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      Rle (completedDist2 X (finProj N X)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  obtain ⟨a, hM⟩ := dlimIsCompletion.dense X (4 * k + 3)
  refine ⟨a.stage, fun N hN => ?_⟩
  have hY : DLimCompletionEq (finProj N (DLimCompletionRaw.of a)) (DLimCompletionRaw.of a) :=
    finProj_of_eq_pj a N hN
  refine Rle_trans (finProj_best_approx_pj N X (DLimCompletionRaw.of a) hY) ?_
  refine Rle_trans hM (Rle_ofQ_of_Qle_loc (Nat.succ_pos (4 * k + 3)) (Nat.succ_pos k) ?_)
  simp only [Qle]
  push_cast
  omega

-- ===========================================================================
-- TARGET 2: setoid CONGRUENCE of the projection.
-- ===========================================================================

/-- **Congruence**: `X ≈ Y ⟹ finProj N X ≈ finProj N Y`. -/
theorem finProj_congr_hd (N : Nat) {X Y : DLimCompletionRaw} (h : DLimCompletionEq X Y) :
    DLimCompletionEq (finProj N X) (finProj N Y) := by
  induction N with
  | zero => exact DLimCompletionEq_refl _
  | succ N ih =>
      exact dlimCompletionAdd_congr ih
        (dlimCompletionSmul_congr (coord_congr N h) (DLimCompletionEq_refl _))

-- ===========================================================================
-- TARGET 3: ADDITIVITY of the projection.
-- ===========================================================================

/-- **Additivity**: `finProj N (X ⊕ Y) ≈ finProj N X ⊕ finProj N Y`. -/
theorem finProj_add_hd (N : Nat) (X Y : DLimCompletionRaw) :
    DLimCompletionEq (finProj N (dlimCompletionAdd X Y))
      (dlimCompletionAdd (finProj N X) (finProj N Y)) := by
  induction N with
  | zero => exact DLimCompletionEq_symm (dlimCompletionAdd_zero dlimCompletionZero)
  | succ N ih =>
      have hsmul : DLimCompletionEq
          (dlimCompletionSmul (coord N (dlimCompletionAdd X Y))
            (DLimCompletionRaw.of (dlimBasis N)))
          (dlimCompletionAdd
            (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))
            (dlimCompletionSmul (coord N Y) (DLimCompletionRaw.of (dlimBasis N)))) :=
        DLimCompletionEq_trans (dlimCompletionSmul_congr_scalar (coord_add N X Y))
          (dlimCompletionSmul_Cadd (coord N X) (coord N Y) (DLimCompletionRaw.of (dlimBasis N)))
      exact DLimCompletionEq_trans (dlimCompletionAdd_congr ih hsmul)
        (cadd_middle_exchange (finProj N X) (finProj N Y)
          (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))
          (dlimCompletionSmul (coord N Y) (DLimCompletionRaw.of (dlimBasis N))))

-- ===========================================================================
-- TARGET 4: ℂ-HOMOGENEITY of the projection.
-- ===========================================================================

/-- **Homogeneity**: `finProj N (c • X) ≈ c • finProj N X`. -/
theorem finProj_smul_hd (N : Nat) (c : Complex) (X : DLimCompletionRaw) :
    DLimCompletionEq (finProj N (dlimCompletionSmul c X))
      (dlimCompletionSmul c (finProj N X)) := by
  induction N with
  | zero => exact DLimCompletionEq_symm (dlimCompletionSmul_zero c)
  | succ N ih =>
      have hsmul : DLimCompletionEq
          (dlimCompletionSmul (coord N (dlimCompletionSmul c X))
            (DLimCompletionRaw.of (dlimBasis N)))
          (dlimCompletionSmul c
            (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))) :=
        DLimCompletionEq_trans (dlimCompletionSmul_congr_scalar (coord_smul N c X))
          (DLimCompletionEq_symm
            (dlimCompletionSmul_assoc c (coord N X) (DLimCompletionRaw.of (dlimBasis N))))
      exact DLimCompletionEq_trans (dlimCompletionAdd_congr ih hsmul)
        (DLimCompletionEq_symm
          (dlimCompletionSmul_add c (finProj N X)
            (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))))

-- ===========================================================================
-- TARGET 6: COMPLETION-COORDINATE SEPARATION (vectors determined by their coordinates).
-- ===========================================================================

/-- **Coordinate separation**: if `X` and `Y` agree on every coordinate, then `X ≈ Y`. Route: the
    difference `W = X ⊖ Y` has all coordinates `0`, so `finProj N W ≈ 0` for every `N`; density
    (`finProj_converges_pj`) then squeezes `d²(W, 0)` below every `1/(k+1)`, forcing `W ≈ 0`. -/
theorem coord_separation_hd {X Y : DLimCompletionRaw}
    (h : ∀ i : Nat, Ceq (coord i X) (coord i Y)) : DLimCompletionEq X Y := by
  have coordW : ∀ i, Ceq (coord i (dlimCompletionSub X Y)) Czero := fun i =>
    Ceq_trans (coord_add i X (dlimCompletionNeg Y))
      (Ceq_trans (Cadd_congr (Ceq_refl (coord i X))
          (completedInner_neg_right_cpl (DLimCompletionRaw.of (dlimBasis i)) Y))
        (Ceq_trans (Cadd_congr (h i) (Ceq_refl (Cneg (coord i Y))))
          (Cadd_neg (coord i Y))))
  have hnn : Rnonneg (completedDist2 (dlimCompletionSub X Y) dlimCompletionZero) :=
    completedDist2_nonneg _ _
  have hall : ∀ k : Nat, Rle (completedDist2 (dlimCompletionSub X Y) dlimCompletionZero)
      (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
    intro k
    obtain ⟨N0, hconv⟩ := finProj_converges_pj (dlimCompletionSub X Y) k
    have hcongr :
        Req (completedDist2 (dlimCompletionSub X Y) (finProj N0 (dlimCompletionSub X Y)))
            (completedDist2 (dlimCompletionSub X Y) dlimCompletionZero) :=
      completedDist2_congr (DLimCompletionEq_refl _)
        (finProj_zero_of_coord_zero N0 (dlimCompletionSub X Y) coordW)
    exact Rle_trans (Rle_of_Req (Req_symm hcongr)) (hconv N0 (Nat.le_refl N0))
  exact dlimCompletionEq_of_sub_zero
    (completedDist2_definite (Req_zero_of_nonneg_of_small_hd hnn hall))

-- ===========================================================================
-- TARGET 5: IDEMPOTENCE of the projection.
-- ===========================================================================

/-- **Idempotence**: `finProj N (finProj N X) ≈ finProj N X`. Coordinates agree at every index
    (`coord_finProj_lt_pj` below `N`, `coord_finProj_ge_pj` at/above `N`), so separation closes it. -/
theorem finProj_idem_hd (N : Nat) (X : DLimCompletionRaw) :
    DLimCompletionEq (finProj N (finProj N X)) (finProj N X) := by
  refine coord_separation_hd (fun i => ?_)
  by_cases hi : i < N
  · exact coord_finProj_lt_pj i N (finProj N X) hi
  · have hge : N ≤ i := Nat.le_of_not_lt hi
    exact Ceq_trans (coord_finProj_ge_pj N i (finProj N X) hge)
      (Ceq_symm (coord_finProj_ge_pj N i X hge))

end UOR.Bridge.F1Square.Square
