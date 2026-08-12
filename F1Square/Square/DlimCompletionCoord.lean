/-
# Completed coordinate reads and the coordinate continuity bound

`coord i X := ⟨of e_i, X⟩` reads the `i`-th coordinate of a completion member against the embedded,
normalized basis vector `e_i = dlimBasis i`. Congruence, additivity, ℂ-linearity, and recovery on the
embedding (`coord i (of a) ≈ ⟨e_i, a⟩`) are immediate from the `completedInner_*` laws.

`coord_re_continuity` — `(Re(coord i X) − Re(coord i Y))² ≤ d²(X,Y)` — is the quantitative continuity
bound (the real coordinate is 1-Lipschitz in the squared distance). It follows from a completion-level
sqrt-free AM-GM (`completedInner_re_amgm`) and the single-NORMALISED-vector Cauchy–Schwarz
`completedInner_re_cs_unit` ((Re⟨e,W⟩)² ≤ ‖W‖² when ‖e‖² ≈ 1), applied at `e = of e_i` (‖e_i‖² = 1).

HONESTY: the GENERAL Cauchy–Schwarz `(Re⟨U,V⟩)² ≤ ‖U‖²‖V‖²` is NOT proved here — its constructive
discriminant needs an ε-squeeze / real-reciprocal that currently lives only in ζ-tainted modules, so it
would break the ζ-free fence. The normalized-vector special case suffices for the coordinate continuity
bound (the AM-GM engine is in place should a ζ-free ε-squeeze be added later). All whnf-safe: no
`completedInner`/`completedNormSq`/`completedDist2` is ever unfolded by defeq.
-/
import F1Square.Square.DlimCompletionSpace
import F1Square.Square.DiagonalOperatorCore

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- The five GIVEN (already-verified) coordinate definitions/lemmas.
-- ===========================================================================

def coord (i : Nat) (X : DLimCompletionRaw) : Complex :=
  completedInner (DLimCompletionRaw.of (dlimBasis i)) X

theorem coord_congr (i : Nat) {X Z : DLimCompletionRaw} (h : DLimCompletionEq X Z) :
    Ceq (coord i X) (coord i Z) :=
  completedInner_congr (DLimCompletionEq_refl _) h

theorem coord_add (i : Nat) (X Y : DLimCompletionRaw) :
    Ceq (coord i (dlimCompletionAdd X Y)) (Cadd (coord i X) (coord i Y)) :=
  completedInner_add_right _ X Y

theorem coord_smul (i : Nat) (c : Complex) (X : DLimCompletionRaw) :
    Ceq (coord i (dlimCompletionSmul c X)) (Cmul c (coord i X)) :=
  completedInner_smul_right c _ X

theorem coord_of (i : Nat) (a : DLimRaw) :
    Ceq (coord i (DLimCompletionRaw.of a)) (dlimInner (dlimBasis i) a) :=
  completedInner_of (dlimBasis i) a

-- ===========================================================================
-- Real / Complex micro-helpers (leaf names end in `_wf`).
-- ===========================================================================

/-- `0·x ≈ 0` on ℝ. -/
private theorem Rzero_mul_wf (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

/-- Real-scalar complex multiplication reads off the real part:
    `Re((r + 0i)·z) ≈ r·Re z`. Definitional `(Cmul ⟨r,0⟩ z).re = r·z.re − 0·z.im`, then drop the
    zero term. -/
private theorem Cmul_re_ofReal_wf (r : Real) (z : Complex) :
    Req (Cmul (⟨r, zero⟩ : Complex) z).re (Rmul r z.re) :=
  Req_trans (Rsub_congr (Req_refl (Rmul r z.re)) (Rzero_mul_wf z.im)) (Rsub_zero (Rmul r z.re))

-- ===========================================================================
-- `‖r•V‖² ≈ r²·‖V‖²` at the completion level (real scalar `r`), via the sesquilinear laws.
-- ===========================================================================

/-- **Real-scalar norm scaling** at the completion level: `‖(r+0i)•V‖² ≈ r²·‖V‖²`. Proved through
    `completedInner_smul_right` (twice) and `completedInner_conj` — the completion inner laws used as
    black boxes; no `completedInner`/`completedNormSq` whnf unfold. -/
theorem completedNormSq_smul_real (r : Real) (V : DLimCompletionRaw) :
    Req (completedNormSq (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))
        (Rmul (Rmul r r) (completedNormSq V)) := by
  -- `⟨r•V, V⟩.re ≈ r·‖V‖²` (conj to move the scalar into the right slot, then smul_right)
  have hwre : Req (completedInner (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V).re
      (Rmul r (completedNormSq V)) := by
    have e1 : Req (completedInner (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V).re
        (completedInner V (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)).re :=
      (completedInner_conj (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V).1
    have e2 : Req (completedInner V (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)).re
        (Rmul r (completedInner V V).re) :=
      Req_trans (completedInner_smul_right (⟨r, zero⟩ : Complex) V V).1
        (Cmul_re_ofReal_wf r (completedInner V V))
    exact Req_trans e1 e2
  -- `‖r•V‖² = ⟨r•V, r•V⟩.re ≈ r·⟨r•V,V⟩.re ≈ r·(r·‖V‖²) ≈ r²·‖V‖²`
  have e3 : Req (completedNormSq (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))
      (Rmul r (completedInner (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V).re) :=
    Req_trans (completedInner_smul_right (⟨r, zero⟩ : Complex)
        (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V).1
      (Cmul_re_ofReal_wf r (completedInner (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) V))
  exact Req_trans e3
    (Req_trans (Rmul_congr (Req_refl r) hwre) (Req_symm (Rmul_assoc r r (completedNormSq V))))

-- ===========================================================================
-- THE COMPLETION AM-GM / polarization core (real scalar `r`).
--   `(r+r)·Re⟨U,V⟩ ≤ ‖U‖² + r²·‖V‖²`   for every real `r`.
-- Port of the stagewise `dlimInner_re_amgm` to the completion inner product: expand `‖U − r•V‖² ≥ 0`
-- through the completion sesquilinear/parallelogram laws (`completedNormSq_add_expand_cpl`,
-- `completedInner_smul_right`, `completedInner_conj`, `completedInner_neg_*_cpl`,
-- `completedNormSq_neg_cpl`, `completedNormSq_smul_real`).
-- ===========================================================================

/-- **The completion AM-GM / polarization core** — the constructive, sqrt-free real-part Cauchy–Schwarz
    seed: for every REAL `r`, `(r+r)·Re⟨U,V⟩ ≤ ‖U‖² + r²·‖V‖²`. Holds for every `r` (unsigned). -/
theorem completedInner_re_amgm (r : Real) (U V : DLimCompletionRaw) :
    Rle (Rmul (Radd r r) (completedInner U V).re)
        (Radd (completedNormSq U) (Rmul (Rmul r r) (completedNormSq V))) := by
  -- the (negated, scaled) second slot and the assembled vector
  -- `Re⟨U, r•V⟩ ≈ r·Re⟨U,V⟩`
  have hUX : Req (completedInner U (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)).re
      (Rmul r (completedInner U V).re) :=
    Req_trans (completedInner_smul_right (⟨r, zero⟩ : Complex) U V).1
      (Cmul_re_ofReal_wf r (completedInner U V))
  -- `Re⟨r•V, U⟩ ≈ r·Re⟨U,V⟩` (Hermitian symmetry)
  have hXU : Req (completedInner (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) U).re
      (Rmul r (completedInner U V).re) :=
    Req_trans (completedInner_conj (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) U).1 hUX
  -- `Re⟨-(r•V), U⟩ ≈ -(r·Re⟨U,V⟩)`
  have hA : Req (completedInner
        (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)) U).re
      (Rneg (Rmul r (completedInner U V).re)) :=
    Req_trans (completedInner_neg_left_cpl (dlimCompletionSmul (⟨r, zero⟩ : Complex) V) U).1
      (Rneg_congr hXU)
  -- `Re⟨U, -(r•V)⟩ ≈ -(r·Re⟨U,V⟩)`
  have hB : Req (completedInner U
        (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))).re
      (Rneg (Rmul r (completedInner U V).re)) :=
    Req_trans (completedInner_neg_right_cpl U (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)).1
      (Rneg_congr hUX)
  -- `‖-(r•V)‖² ≈ r²·‖V‖²`
  have hC : Req (completedNormSq (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)))
      (Rmul (Rmul r r) (completedNormSq V)) :=
    Req_trans (completedNormSq_neg_cpl (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))
      (completedNormSq_smul_real r V)
  -- parallelogram expansion of `‖U + (-(r•V))‖²`
  have expand := completedNormSq_add_expand_cpl U
    (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))
  -- substitute the four inner-product pieces
  have hbig :
      Req (completedNormSq (dlimCompletionAdd U
              (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V))))
          (Radd (Radd (completedNormSq U) (Rneg (Rmul r (completedInner U V).re)))
                (Radd (Rneg (Rmul r (completedInner U V).re))
                  (Rmul (Rmul r r) (completedNormSq V)))) :=
    Req_trans expand (Radd_congr (Radd_congr (Req_refl (completedNormSq U)) hB) (Radd_congr hA hC))
  -- rearrange the RHS into `(‖U‖² + r²‖V‖²) − (r+r)·Re⟨U,V⟩`
  have hdist : Req (Rmul (Radd r r) (completedInner U V).re)
      (Radd (Rmul r (completedInner U V).re) (Rmul r (completedInner U V).re)) :=
    Rmul_distrib_right r r (completedInner U V).re
  have hfinal :
      Req (Radd (Radd (completedNormSq U) (Rneg (Rmul r (completedInner U V).re)))
                (Radd (Rneg (Rmul r (completedInner U V).re))
                  (Rmul (Rmul r r) (completedNormSq V))))
          (Rsub (Radd (completedNormSq U) (Rmul (Rmul r r) (completedNormSq V)))
                (Rmul (Radd r r) (completedInner U V).re)) :=
    Req_trans
      (Radd_congr (Req_refl _)
        (Radd_comm (Rneg (Rmul r (completedInner U V).re))
          (Rmul (Rmul r r) (completedNormSq V))))
      (Req_trans
        (Req_symm (Rsub_Radd_Radd (completedNormSq U)
          (Rmul (Rmul r r) (completedNormSq V))
          (Rmul r (completedInner U V).re) (Rmul r (completedInner U V).re)))
        (Rsub_congr (Req_refl _) (Req_symm hdist)))
  have hnn : Rnonneg (completedNormSq (dlimCompletionAdd U
      (dlimCompletionNeg (dlimCompletionSmul (⟨r, zero⟩ : Complex) V)))) :=
    completedNormSq_nonneg _
  exact Rle_of_Rnonneg_Rsub_loc (Rnonneg_congr_loc (Req_trans hbig hfinal) hnn)

-- ===========================================================================
-- TARGET B: coordinate continuity (1-Lipschitz in squared distance).
-- Uses A specialised to the normalised basis vector `e_i` (‖e_i‖² = 1) with `r = Re⟨e_i, X⊖Y⟩`.
-- ===========================================================================

/-- **Single-normalised-vector Cauchy–Schwarz** at the completion level: if `‖e‖² ≈ 1` then
    `(Re⟨e, W⟩)² ≤ ‖W‖²`. The AM-GM at `r = Re⟨e,W⟩` gives `2r² ≤ ‖W‖² + r²`; cancel one `r²`. -/
theorem completedInner_re_cs_unit (e W : DLimCompletionRaw)
    (he : Req (completedNormSq e) one) :
    Rle (Rmul (completedInner e W).re (completedInner e W).re) (completedNormSq W) := by
  -- abbreviation: R := Re⟨e,W⟩
  -- `Re⟨W,e⟩ ≈ R`
  have hWe : Req (completedInner W e).re (completedInner e W).re :=
    (completedInner_conj W e).1
  -- AM-GM at `r = R`, `U = W`, `V = e`
  have amgm := completedInner_re_amgm (completedInner e W).re W e
  -- rewrite the AM-GM LHS `(R+R)·Re⟨W,e⟩` as `R² + R²`
  have hA' : Req
      (Radd (Rmul (completedInner e W).re (completedInner e W).re)
            (Rmul (completedInner e W).re (completedInner e W).re))
      (Rmul (Radd (completedInner e W).re (completedInner e W).re) (completedInner W e).re) :=
    Req_trans (Req_symm (Rmul_distrib_right (completedInner e W).re (completedInner e W).re
        (completedInner e W).re))
      (Rmul_congr (Req_refl _) (Req_symm hWe))
  -- rewrite the AM-GM RHS `‖W‖² + R²·‖e‖²` as `‖W‖² + R²`
  have hB' : Req
      (Radd (completedNormSq W)
        (Rmul (Rmul (completedInner e W).re (completedInner e W).re) (completedNormSq e)))
      (Radd (completedNormSq W)
        (Rmul (completedInner e W).re (completedInner e W).re)) :=
    Radd_congr (Req_refl _)
      (Req_trans (Rmul_congr (Req_refl _) he)
        (Rmul_one (Rmul (completedInner e W).re (completedInner e W).re)))
  -- the cancelled AM-GM: `R² + R² ≤ ‖W‖² + R²`
  have hcanc : Rle
      (Radd (Rmul (completedInner e W).re (completedInner e W).re)
            (Rmul (completedInner e W).re (completedInner e W).re))
      (Radd (completedNormSq W) (Rmul (completedInner e W).re (completedInner e W).re)) :=
    Rle_trans (Rle_of_Req hA') (Rle_trans amgm (Rle_of_Req hB'))
  -- subtract `R²` from both sides: `Rnonneg (‖W‖² − R²)`
  have hsub : Req
      (Rsub (Radd (completedNormSq W) (Rmul (completedInner e W).re (completedInner e W).re))
            (Radd (Rmul (completedInner e W).re (completedInner e W).re)
                  (Rmul (completedInner e W).re (completedInner e W).re)))
      (Rsub (completedNormSq W) (Rmul (completedInner e W).re (completedInner e W).re)) :=
    Req_trans
      (Rsub_Radd_Radd (completedNormSq W)
        (Rmul (completedInner e W).re (completedInner e W).re)
        (Rmul (completedInner e W).re (completedInner e W).re)
        (Rmul (completedInner e W).re (completedInner e W).re))
      (Req_trans
        (Radd_congr (Req_refl _)
          (Radd_neg (Rmul (completedInner e W).re (completedInner e W).re)))
        (Radd_zero (Rsub (completedNormSq W)
          (Rmul (completedInner e W).re (completedInner e W).re))))
  exact Rle_of_Rnonneg_Rsub_loc
    (Rnonneg_congr_loc hsub (Rnonneg_Rsub_of_Rle_loc hcanc))

/-- **COORDINATE CONTINUITY** (1-Lipschitz in the squared distance): the real part of each coordinate is
    non-expansive, `(Re(coord i X) − Re(coord i Y))² ≤ d²(X,Y)`. From the single-normalised-vector CS
    with `e = of(e_i)` (`‖e_i‖² = 1`) and `W = X ⊖ Y`, plus linearity of the coordinate. -/
theorem coord_re_continuity (i : Nat) (X Y : DLimCompletionRaw) :
    Rle (Rmul (Rsub (coord i X).re (coord i Y).re) (Rsub (coord i X).re (coord i Y).re))
        (completedDist2 X Y) := by
  -- `Re⟨e_i, X⊖Y⟩ ≈ Re(coord i X) − Re(coord i Y)`
  have hCe : Ceq (completedInner (DLimCompletionRaw.of (dlimBasis i)) (dlimCompletionSub X Y))
      (Cadd (coord i X) (Cneg (coord i Y))) :=
    Ceq_trans (completedInner_add_right (DLimCompletionRaw.of (dlimBasis i)) X (dlimCompletionNeg Y))
      (Cadd_congr (Ceq_refl (coord i X))
        (completedInner_neg_right_cpl (DLimCompletionRaw.of (dlimBasis i)) Y))
  have hRdiff : Req (Rsub (coord i X).re (coord i Y).re)
      (completedInner (DLimCompletionRaw.of (dlimBasis i)) (dlimCompletionSub X Y)).re :=
    Req_symm hCe.1
  -- `‖e_i‖² ≈ 1`
  have he : Req (completedNormSq (DLimCompletionRaw.of (dlimBasis i))) one :=
    Req_trans (completedInner_of (dlimBasis i) (dlimBasis i)).1 (dlimBasis_self_re i)
  -- specialised CS on `e_i`, `W = X ⊖ Y`
  have hCS := completedInner_re_cs_unit (DLimCompletionRaw.of (dlimBasis i))
    (dlimCompletionSub X Y) he
  -- transport through `hRdiff`
  exact Rle_trans (Rle_of_Req (Rmul_congr hRdiff hRdiff)) hCS

end UOR.Bridge.F1Square.Square
