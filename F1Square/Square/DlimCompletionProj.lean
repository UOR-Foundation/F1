/-
# Finite coordinate projections onto the Bishop completion, residual Pythagoras, convergence

`finProj N X = Σ_{i<N} coord_i(X)·(of e_i)` — the projection of a completion member onto the span of the
first `N` coordinate-basis vectors `e_i = dlimBasis i`.

Main results (all whnf-safe: `completedInner`/`completedNormSq`/`completedDist2`/`coord` are NEVER
unfolded by defeq — only the `completedInner_*`/`coord_*`/completion-module laws are used, and `coord`
is delta-reduced only inside a folded `completedInner` argument, never forcing `completedInner` itself):

* `finProj_of_eq_pj`     — RECONSTRUCTION: for `N ≥ stage(a)`, `finProj N (of a) ≈ of a`.
* `finProj_contraction_pj` — Bessel CONTRACTION: `‖finProj N X‖² ≤ ‖X‖²` (via residual Pythagoras).
* `finProj_converges_pj` — CONVERGENCE: `d²(X, finProj N X) → 0`, consuming completion density.

The engine is the residual-orthogonality lemma `finProj_ortho_residual` (`⟨finProj N Z, R⟩ ≈ 0` when the
first-`N` coordinates of `R` vanish) plus the completion parallelogram expansion. Reconstruction routes
through a raw-level basis expansion `rawProj` and raw finite-vector extensionality (`dlim_ext_coords`).

ZETA-FREE: imports only the completion cone (transitive closure of `DlimCompletionCoord`); nothing from
the transcendental/analytic-number-theory modules. Basic ℝ/ℂ facts absent from the cone are rebuilt
locally from in-cone primitives.
-/
import F1Square.Square.DlimCompletionCoord

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Local ℝ/ℂ micro-helpers (leaf names end in `_pj`), rebuilt from in-cone primitives.
-- ===========================================================================

/-- `z · 0 ≈ 0` on ℂ (componentwise, from `Rmul_zero`). -/
private theorem Cmul_Czero_pj (z : Complex) : Ceq (Cmul z Czero) Czero :=
  ⟨Req_trans (Radd_congr (Rmul_zero z.re) (Rneg_congr (Rmul_zero z.im))) (Radd_neg zero),
   Req_trans (Radd_congr (Rmul_zero z.re) (Rmul_zero z.im)) (Radd_zero zero)⟩

/-- `0 ⊕ z ≈ z` on ℂ. -/
private theorem Czero_Cadd_pj (z : Complex) : Ceq (Cadd Czero z) z :=
  Ceq_trans (Cadd_comm Czero z) (Cadd_zero_cpl z)

/-- `0 ⊕ x ≈ x` on ℝ. -/
private theorem Rzero_add_pj (x : Real) : Req (Radd zero x) x :=
  Req_trans (Radd_comm zero x) (Radd_zero x)

/-- `(a ⊕ b) ⊖ a ≈ b` on ℝ (from the additive-group laws; no `ring_uor`). -/
private theorem Radd_sub_self_left (a b : Real) : Req (Rsub (Radd a b) a) b :=
  Req_trans (Radd_congr (Radd_comm a b) (Req_refl (Rneg a)))
    (Req_trans (Radd_assoc b a (Rneg a))
      (Req_trans (Radd_congr (Req_refl b) (Radd_neg a)) (Radd_zero b)))

-- ===========================================================================
-- THE FINITE COORDINATE PROJECTION.
-- ===========================================================================

/-- `finProj N X = Σ_{i<N} coord_i(X)·(of e_i)` — the finite coordinate projection of a completion
    member onto the span of the first `N` coordinate-basis vectors. -/
def finProj : Nat → DLimCompletionRaw → DLimCompletionRaw
  | 0, _ => dlimCompletionZero
  | (N + 1), X =>
      dlimCompletionAdd (finProj N X)
        (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))

-- ===========================================================================
-- `coord`/`completedInner` black-box helpers (each isolates a single `coord` delta at its use site).
-- ===========================================================================

/-- `coord i (−X) ≈ −coord i X`. -/
private theorem coord_neg_pj (i : Nat) (X : DLimCompletionRaw) :
    Ceq (coord i (dlimCompletionNeg X)) (Cneg (coord i X)) :=
  completedInner_neg_right_cpl (DLimCompletionRaw.of (dlimBasis i)) X

/-- `⟨0, R⟩ ≈ 0` (left-zero of the completed inner product), via Hermitian symmetry. -/
private theorem completedInner_zero_left_cpl (R : DLimCompletionRaw) :
    Ceq (completedInner dlimCompletionZero R) Czero :=
  Ceq_trans (completedInner_conj dlimCompletionZero R)
    (Ceq_trans (Cconj_congr (completedInner_zero_right_cpl R)) Cconj_Czero)

/-- `⟨c•U, V⟩ ≈ (conj c)·⟨U, V⟩` (left scalar), via Hermitian symmetry and `completedInner_smul_right`. -/
private theorem completedInner_smul_left_cpl (c : Complex) (U V : DLimCompletionRaw) :
    Ceq (completedInner (dlimCompletionSmul c U) V) (Cmul (Cconj c) (completedInner U V)) :=
  Ceq_trans (completedInner_conj (dlimCompletionSmul c U) V)
    (Ceq_trans (Cconj_congr (completedInner_smul_right c V U))
      (Ceq_trans (Cconj_Cmul c (completedInner V U))
        (Cmul_congr (Ceq_refl (Cconj c)) (Ceq_symm (completedInner_conj U V)))))

-- ===========================================================================
-- COORDINATE READS OF THE PROJECTION.
--   B0 `coord_finProj_ge_pj` : `coord i (finProj N X) ≈ 0`  for `i ≥ N` (support in first N coords).
--   B1 `coord_finProj_lt_pj` : `coord i (finProj N X) ≈ coord i X`  for `i < N` (reproduces coords).
-- ===========================================================================

/-- **B0 — support**: the projection onto the first `N` basis vectors has vanishing coordinates `i ≥ N`. -/
theorem coord_finProj_ge_pj : ∀ (N i : Nat) (X : DLimCompletionRaw), N ≤ i →
    Ceq (coord i (finProj N X)) Czero
  | 0, i, _, _ => completedInner_zero_right_cpl (DLimCompletionRaw.of (dlimBasis i))
  | (N + 1), i, X, h => by
      have hNi : N < i := h
      refine Ceq_trans (coord_add i (finProj N X)
        (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))) ?_
      refine Ceq_trans (Cadd_congr (coord_finProj_ge_pj N i X (Nat.le_of_lt hNi)) ?_)
        (Cadd_zero_cpl Czero)
      exact Ceq_trans (coord_smul i (coord N X) (DLimCompletionRaw.of (dlimBasis N)))
        (Ceq_trans (Cmul_congr (Ceq_refl (coord N X))
            (Ceq_trans (coord_of i (dlimBasis N)) (dlimBasis_ortho_bo i N (by omega))))
          (Cmul_Czero_pj (coord N X)))

/-- **B1 — reproduction**: the projection onto the first `N` basis vectors reproduces coordinates `i < N`. -/
theorem coord_finProj_lt_pj : ∀ (i N : Nat) (X : DLimCompletionRaw), i < N →
    Ceq (coord i (finProj N X)) (coord i X)
  | i, 0, _, h => absurd h (Nat.not_lt_zero i)
  | i, (N + 1), X, h => by
      by_cases hiN : i = N
      · rw [hiN]
        refine Ceq_trans (coord_add N (finProj N X)
          (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))) ?_
        refine Ceq_trans (Cadd_congr (coord_finProj_ge_pj N N X (Nat.le_refl N)) ?_)
          (Czero_Cadd_pj (coord N X))
        exact Ceq_trans (coord_smul N (coord N X) (DLimCompletionRaw.of (dlimBasis N)))
          (Ceq_trans (Cmul_congr (Ceq_refl (coord N X))
              (Ceq_trans (coord_of N (dlimBasis N)) (dlimBasis_normalized N)))
            (Cmul_one (coord N X)))
      · have hiN' : i < N := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hiN
        refine Ceq_trans (coord_add i (finProj N X)
          (dlimCompletionSmul (coord N X) (DLimCompletionRaw.of (dlimBasis N)))) ?_
        refine Ceq_trans (Cadd_congr (coord_finProj_lt_pj i N X hiN') ?_)
          (Cadd_zero_cpl (coord i X))
        exact Ceq_trans (coord_smul i (coord N X) (DLimCompletionRaw.of (dlimBasis N)))
          (Ceq_trans (Cmul_congr (Ceq_refl (coord N X))
              (Ceq_trans (coord_of i (dlimBasis N)) (dlimBasis_ortho_bo i N hiN)))
            (Cmul_Czero_pj (coord N X)))

-- ===========================================================================
-- RESIDUAL ORTHOGONALITY: any projection output is ⊥ to a vector with zero first-N coordinates.
-- ===========================================================================

/-- **Residual orthogonality**: if `R` has vanishing coordinates `i < N`, then `⟨finProj N Z, R⟩ ≈ 0`
    — the projection output lies in `span(e_0..e_{N−1})`, which is orthogonal to such `R`. -/
theorem finProj_ortho_residual : ∀ (N : Nat) (Z R : DLimCompletionRaw),
    (∀ i, i < N → Ceq (coord i R) Czero) → Ceq (completedInner (finProj N Z) R) Czero
  | 0, _, R, _ => completedInner_zero_left_cpl R
  | (N + 1), Z, R, hR => by
      refine Ceq_trans (completedInner_add_left_cpl (finProj N Z)
        (dlimCompletionSmul (coord N Z) (DLimCompletionRaw.of (dlimBasis N))) R) ?_
      refine Ceq_trans (Cadd_congr
        (finProj_ortho_residual N Z R (fun i hi => hR i (Nat.lt_succ_of_lt hi))) ?_)
        (Cadd_zero_cpl Czero)
      exact Ceq_trans (completedInner_smul_left_cpl (coord N Z)
          (DLimCompletionRaw.of (dlimBasis N)) R)
        (Ceq_trans (Cmul_congr (Ceq_refl (Cconj (coord N Z))) (hR N (Nat.lt_succ_self N)))
          (Cmul_Czero_pj (Cconj (coord N Z))))

/-- The residual `X ⊖ finProj N X` has vanishing coordinates `i < N` (from B1). -/
private theorem residual_coords_pj (N : Nat) (X : DLimCompletionRaw) :
    ∀ i, i < N → Ceq (coord i (dlimCompletionSub X (finProj N X))) Czero := fun i hi =>
  Ceq_trans (coord_add i X (dlimCompletionNeg (finProj N X)))
    (Ceq_trans (Cadd_congr (Ceq_refl (coord i X))
        (Ceq_trans (coord_neg_pj i (finProj N X))
          (Cneg_congr_cpl (coord_finProj_lt_pj i N X hi))))
      (Cadd_neg (coord i X)))

-- ===========================================================================
-- TARGET B: residual PYTHAGORAS `‖X‖² = ‖P_N X‖² + d²(X, P_N X)` → the Bessel CONTRACTION.
-- ===========================================================================

/-- **B — Bessel contraction**: the projection is non-expansive, `‖finProj N X‖² ≤ ‖X‖²`. Via residual
    Pythagoras `‖X‖² ≈ ‖finProj N X‖² + d²(X, finProj N X)` (parallelogram expansion of `X ≈ P ⊕ (X⊖P)`
    with both cross terms `Re⟨P, X⊖P⟩`, `Re⟨X⊖P, P⟩ ≈ 0`), dropping the nonnegative `d²`. -/
theorem finProj_contraction_pj (N : Nat) (X : DLimCompletionRaw) :
    Rle (completedNormSq (finProj N X)) (completedNormSq X) := by
  have hPR : Ceq (completedInner (finProj N X) (dlimCompletionSub X (finProj N X))) Czero :=
    finProj_ortho_residual N X (dlimCompletionSub X (finProj N X)) (residual_coords_pj N X)
  have hRP : Ceq (completedInner (dlimCompletionSub X (finProj N X)) (finProj N X)) Czero :=
    Ceq_trans (completedInner_conj (dlimCompletionSub X (finProj N X)) (finProj N X))
      (Ceq_trans (Cconj_congr hPR) Cconj_Czero)
  have hPX : DLimCompletionEq (dlimCompletionAdd (finProj N X) (dlimCompletionSub X (finProj N X))) X :=
    DLimCompletionEq_trans (dlimCompletionAdd_comm (finProj N X) (dlimCompletionSub X (finProj N X)))
      (DLimCompletionEq_trans (dlimCompletionAdd_assoc X (dlimCompletionNeg (finProj N X)) (finProj N X))
        (DLimCompletionEq_trans
          (dlimCompletionAdd_congr (DLimCompletionEq_refl X) (negAddSelf_cpl (finProj N X)))
          (dlimCompletionAdd_zero X)))
  have hPyth : Req (completedNormSq X)
      (Radd (completedNormSq (finProj N X)) (completedDist2 X (finProj N X))) :=
    Req_trans (completedNormSq_congr_cpl (DLimCompletionEq_symm hPX))
      (Req_trans (completedNormSq_add_expand_cpl (finProj N X) (dlimCompletionSub X (finProj N X)))
        (Req_trans
          (Radd_congr (Radd_congr (Req_refl (completedNormSq (finProj N X))) hPR.1)
            (Radd_congr hRP.1 (Req_refl (completedNormSq (dlimCompletionSub X (finProj N X))))))
          (Radd_congr (Radd_zero (completedNormSq (finProj N X)))
            (Rzero_add_pj (completedNormSq (dlimCompletionSub X (finProj N X)))))))
  exact Rle_of_Rnonneg_Rsub_loc
    (Rnonneg_congr_loc
      (Req_symm (Req_trans (Rsub_congr hPyth (Req_refl (completedNormSq (finProj N X))))
        (Radd_sub_self_left (completedNormSq (finProj N X)) (completedDist2 X (finProj N X)))))
      (completedDist2_nonneg X (finProj N X)))

-- ===========================================================================
-- BEST APPROXIMATION: d²(X, P_N X) ≤ d²(X, Y) for any Y fixed by the projection (Y ∈ span).
-- ===========================================================================

/-- **Best approximation**: `finProj N X` is the closest point of `span(e_0..e_{N−1})` to `X`. If `Y`
    is fixed by the projection (`finProj N Y ≈ Y`, i.e. `Y ∈ span`), then `d²(X, finProj N X) ≤ d²(X, Y)`.
    Via the Pythagorean decomposition `d²(X,Y) ≈ d²(X, finProj N X) + d²(finProj N X, Y)` (telescoping
    `X⊖Y ≈ (X⊖P) ⊕ (P⊖Y)` with both residual cross terms `≈ 0`), dropping the nonnegative `d²(P,Y)`. -/
theorem finProj_best_approx_pj (N : Nat) (X Y : DLimCompletionRaw)
    (hY : DLimCompletionEq (finProj N Y) Y) :
    Rle (completedDist2 X (finProj N X)) (completedDist2 X Y) := by
  have hPR : Ceq (completedInner (finProj N X) (dlimCompletionSub X (finProj N X))) Czero :=
    finProj_ortho_residual N X (dlimCompletionSub X (finProj N X)) (residual_coords_pj N X)
  have hQR : Ceq (completedInner (finProj N Y) (dlimCompletionSub X (finProj N X))) Czero :=
    finProj_ortho_residual N Y (dlimCompletionSub X (finProj N X)) (residual_coords_pj N X)
  have hRP : Ceq (completedInner (dlimCompletionSub X (finProj N X)) (finProj N X)) Czero :=
    Ceq_trans (completedInner_conj (dlimCompletionSub X (finProj N X)) (finProj N X))
      (Ceq_trans (Cconj_congr hPR) Cconj_Czero)
  have hRY : Ceq (completedInner (dlimCompletionSub X (finProj N X)) Y) Czero :=
    Ceq_trans (completedInner_congr (DLimCompletionEq_refl (dlimCompletionSub X (finProj N X)))
        (DLimCompletionEq_symm hY))
      (Ceq_trans (completedInner_conj (dlimCompletionSub X (finProj N X)) (finProj N Y))
        (Ceq_trans (Cconj_congr hQR) Cconj_Czero))
  have hRPmY : Ceq (completedInner (dlimCompletionSub X (finProj N X))
      (dlimCompletionSub (finProj N X) Y)) Czero :=
    Ceq_trans (completedInner_add_right (dlimCompletionSub X (finProj N X)) (finProj N X)
        (dlimCompletionNeg Y))
      (Ceq_trans (Cadd_congr hRP
          (Ceq_trans (completedInner_neg_right_cpl (dlimCompletionSub X (finProj N X)) Y)
            (Cneg_congr_cpl hRY)))
        (Cadd_neg Czero))
  have hPmYR : Ceq (completedInner (dlimCompletionSub (finProj N X) Y)
      (dlimCompletionSub X (finProj N X))) Czero :=
    Ceq_trans (completedInner_conj (dlimCompletionSub (finProj N X) Y)
        (dlimCompletionSub X (finProj N X)))
      (Ceq_trans (Cconj_congr hRPmY) Cconj_Czero)
  have hDecomp : Req (completedDist2 X Y)
      (Radd (completedDist2 X (finProj N X)) (completedDist2 (finProj N X) Y)) :=
    Req_trans (completedNormSq_congr_cpl (telescope_cpl X (finProj N X) Y))
      (Req_trans (completedNormSq_add_expand_cpl (dlimCompletionSub X (finProj N X))
          (dlimCompletionSub (finProj N X) Y))
        (Req_trans
          (Radd_congr
            (Radd_congr (Req_refl (completedNormSq (dlimCompletionSub X (finProj N X)))) hRPmY.1)
            (Radd_congr hPmYR.1 (Req_refl (completedNormSq (dlimCompletionSub (finProj N X) Y)))))
          (Radd_congr (Radd_zero (completedNormSq (dlimCompletionSub X (finProj N X))))
            (Rzero_add_pj (completedNormSq (dlimCompletionSub (finProj N X) Y))))))
  have hle : Rle (completedDist2 X (finProj N X))
      (Radd (completedDist2 X (finProj N X)) (completedDist2 (finProj N X) Y)) :=
    Rle_of_Rnonneg_Rsub_loc
      (Rnonneg_congr_loc
        (Req_symm (Radd_sub_self_left (completedDist2 X (finProj N X))
          (completedDist2 (finProj N X) Y)))
        (completedDist2_nonneg (finProj N X) Y))
  exact Rle_trans hle (Rle_of_Req (Req_symm hDecomp))

-- ===========================================================================
-- TARGET A: RECONSTRUCTION. Raw-level basis expansion + raw finite-vector extensionality.
-- ===========================================================================

/-- The RAW-level basis expansion `Σ_{i<N} ⟨e_i, a⟩·e_i` of a colimit vector. -/
def rawProj : Nat → DLimRaw → DLimRaw
  | 0, _ => dlimZero
  | (N + 1), a => dlimAdd (rawProj N a) (dlimSmul (dlimInner (dlimBasis N) a) (dlimBasis N))

/-- `rawProj N a` is supported at stage `≤ N`. -/
theorem rawProj_stage_le : ∀ (N : Nat) (a : DLimRaw), (rawProj N a).stage ≤ N
  | 0, _ => Nat.le_refl 0
  | (N + 1), a => by
      have ih := rawProj_stage_le N a
      show max (rawProj N a).stage (N + 1) ≤ N + 1
      omega

/-- **Embedding matches the raw expansion**: `finProj N (of a) ≈ of (rawProj N a)`. Induction on `N`,
    matching the recursive steps through `coord_of`, `of`-homomorphism (`_of_smul`, `_of_add`), and the
    completion module congruences. -/
theorem finProj_of_eq_rawProj : ∀ (N : Nat) (a : DLimRaw),
    DLimCompletionEq (finProj N (DLimCompletionRaw.of a)) (DLimCompletionRaw.of (rawProj N a))
  | 0, _ => DLimCompletionEq_refl _
  | (N + 1), a => by
      have hsmul : DLimCompletionEq
          (dlimCompletionSmul (coord N (DLimCompletionRaw.of a)) (DLimCompletionRaw.of (dlimBasis N)))
          (DLimCompletionRaw.of (dlimSmul (dlimInner (dlimBasis N) a) (dlimBasis N))) :=
        DLimCompletionEq_trans
          (dlimCompletionSmul_congr_scalar (coord_of N a))
          (DLimCompletionEq_of_smul (dlimInner (dlimBasis N) a) (dlimBasis N))
      exact DLimCompletionEq_trans
        (dlimCompletionAdd_congr (finProj_of_eq_rawProj N a) hsmul)
        (DLimCompletionEq_symm
          (DLimCompletionEq_of_add (rawProj N a)
            (dlimSmul (dlimInner (dlimBasis N) a) (dlimBasis N))))

/-- **Raw finite-vector extensionality**: two colimit vectors supported at stage `≤ N` that agree on all
    coordinates `⟨e_j, ·⟩` (`j < N`) are equal in the colimit. In finite dimension, the coordinates
    determine the vector (the two included `CVec N` representatives agree pointwise). -/
theorem dlim_ext_coords (u v : DLimRaw) (N : Nat) (hu : u.stage ≤ N) (hv : v.stage ≤ N)
    (hc : ∀ j, j < N → Ceq (dlimInner (dlimBasis j) u) (dlimInner (dlimBasis j) v)) :
    DLimEq u v := by
  have hUmk : DLimEq u (dlimMk (cvInc hu u.vec)) := DLimEq_symm (dlimMk_cvInc hu u.vec)
  have hVmk : DLimEq v (dlimMk (cvInc hv v.vec)) := DLimEq_symm (dlimMk_cvInc hv v.vec)
  refine ⟨N, hu, hv, fun i => ?_⟩
  have hu_chain : Ceq (dlimInner (dlimBasis i.val) u) ((cvInc hu u.vec) i) :=
    Ceq_trans (dlimInner_wd (DLimEq_refl (dlimBasis i.val)) hUmk)
      (dlimBasis_coord_bo i.val N i.isLt (cvInc hu u.vec))
  have hv_chain : Ceq (dlimInner (dlimBasis i.val) v) ((cvInc hv v.vec) i) :=
    Ceq_trans (dlimInner_wd (DLimEq_refl (dlimBasis i.val)) hVmk)
      (dlimBasis_coord_bo i.val N i.isLt (cvInc hv v.vec))
  exact Ceq_trans (Ceq_symm hu_chain) (Ceq_trans (hc i.val i.isLt) hv_chain)

/-- **Raw reconstruction**: `Σ_{i<N} ⟨e_i,a⟩·e_i ≈ a` for `a` supported at stage `≤ N`. Coordinates are
    transferred from B1 through the embedding match, then raw extensionality closes it. -/
theorem rawProj_eq (a : DLimRaw) (N : Nat) (h : a.stage ≤ N) : DLimEq (rawProj N a) a := by
  refine dlim_ext_coords (rawProj N a) a N (rawProj_stage_le N a) h (fun j hj => ?_)
  exact Ceq_trans (Ceq_symm (coord_of j (rawProj N a)))
    (Ceq_trans (coord_congr j (DLimCompletionEq_symm (finProj_of_eq_rawProj N a)))
      (Ceq_trans (coord_finProj_lt_pj j N (DLimCompletionRaw.of a) hj) (coord_of j a)))

/-- **A — RECONSTRUCTION**: for `N ≥ stage(a)`, the projection of an embedded finite vector recovers it,
    `finProj N (of a) ≈ of a`. -/
theorem finProj_of_eq_pj (a : DLimRaw) (N : Nat) (h : a.stage ≤ N) :
    DLimCompletionEq (finProj N (DLimCompletionRaw.of a)) (DLimCompletionRaw.of a) :=
  DLimCompletionEq_trans (finProj_of_eq_rawProj N a) (DLimCompletionEq_of (rawProj_eq a N h))

-- ===========================================================================
-- TARGET C: CONVERGENCE `d²(X, finProj N X) → 0`, consuming density + best approximation.
-- ===========================================================================

/-- **C — CONVERGENCE**: the finite coordinate projections converge to `X`. Given `k`, density supplies a
    finite vector `a := X_M` with `d²(X, of a) ≤ 1/(4(k+1))`; for `N ≥ stage(a)`, `of a` is fixed by the
    projection (reconstruction A), so best approximation gives `d²(X, finProj N X) ≤ d²(X, of a) ≤ 1/(k+1)`. -/
theorem finProj_converges_pj (X : DLimCompletionRaw) (k : Nat) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      Rle (completedDist2 X (finProj N X)) (ofQ (⟨1, k + 1⟩ : Q) (Nat.succ_pos k)) := by
  obtain ⟨M, hM⟩ := completion_dense X (4 * k + 3)
  refine ⟨(X.seq M).stage, fun N hN => ?_⟩
  have hY : DLimCompletionEq (finProj N (DLimCompletionRaw.of (X.seq M)))
      (DLimCompletionRaw.of (X.seq M)) := finProj_of_eq_pj (X.seq M) N hN
  refine Rle_trans (finProj_best_approx_pj N X (DLimCompletionRaw.of (X.seq M)) hY) ?_
  refine Rle_trans hM (Rle_ofQ_of_Qle_loc (Nat.succ_pos (4 * k + 3)) (Nat.succ_pos k) ?_)
  simp only [Qle]
  push_cast
  omega

end UOR.Bridge.F1Square.Square
