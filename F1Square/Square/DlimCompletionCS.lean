/-
# Division-free general Cauchy–Schwarz for the completion inner product + fixed-vector continuity

Two ζ-free, sqrt-free, DIVISION-free results, living entirely in the `DlimCompletionCoord` cone:

* `completedInner_re_cs_gen` — the GENERAL real-part Cauchy–Schwarz in the un-normalised,
  DIVISION-FREE `a·r² ≤ a·(b·a)` shape:  `‖V‖²·(Re⟨U,V⟩)² ≤ ‖V‖²·(‖U‖²·‖V‖²)`.  No `‖V‖²=1`
  assumption, no cancellation of `‖V‖²` (hence no reciprocal / ε-squeeze that would touch the ζ-fence).
  Obtained by feeding the AM-GM core `completedInner_re_amgm` the vector `(‖V‖²)•U` at the real
  parameter `λ = Re⟨U,V⟩`:  `2·Re⟨U,V⟩·Re⟨(‖V‖²)•U, V⟩ ≤ ‖(‖V‖²)•U‖² + Re⟨U,V⟩²·‖V‖²`, i.e.
  `2·a·r² ≤ a²·b + a·r²`, then cancel one `a·r²`.

* `inner_fixed_continuity_cs` — fixed-vector inner-product continuity in the same division-free form:
  `‖V‖²·(Re⟨V,X⟩ − Re⟨V,Y⟩)² ≤ ‖V‖²·‖V‖²·d²(X,Y)`.  From the general CS at `U := X⊖Y` (using
  `Re⟨X⊖Y,V⟩ = Re⟨V,X⟩ − Re⟨V,Y⟩` by Hermitian symmetry + right-additivity and
  `‖X⊖Y‖² = d²(X,Y)` definitionally).

All whnf-safe: no `completedInner`/`completedNormSq`/`completedDist2` is ever unfolded by defeq; the
proofs go through the `completedInner_*`/`completedNormSq_*` black-box laws only.
-/
import F1Square.Square.DlimCompletionCoord

open UOR.Bridge.F1Square Square
open UOR.Bridge.F1Square.Analysis

namespace UOR.Bridge.F1Square.Square

-- ===========================================================================
-- Real / Complex micro-helpers (local copies of the `_wf` privates in
-- `DlimCompletionCoord`; leaf names end in `_csh`).
-- ===========================================================================

/-- `0·x ≈ 0` on ℝ. -/
private theorem Rzero_mul_csh (x : Real) : Req (Rmul zero x) zero :=
  Req_trans (Rmul_comm zero x) (Rmul_zero x)

/-- Real-scalar complex multiplication reads off the real part: `Re((r + 0i)·z) ≈ r·Re z`. -/
private theorem Cmul_re_ofReal_csh (r : Real) (z : Complex) :
    Req (Cmul (⟨r, zero⟩ : Complex) z).re (Rmul r z.re) :=
  Req_trans (Rsub_congr (Req_refl (Rmul r z.re)) (Rzero_mul_csh z.im)) (Rsub_zero (Rmul r z.re))

-- ===========================================================================
-- TARGET A — DIVISION-FREE general real-part Cauchy–Schwarz.
--   `‖V‖²·(Re⟨U,V⟩)² ≤ ‖V‖²·(‖U‖²·‖V‖²)`     (the `a·r² ≤ a·(b·a)` shape).
-- ===========================================================================

/-- **General (un-normalised) DIVISION-FREE real-part Cauchy–Schwarz** at the completion level:
    `‖V‖²·(Re⟨U,V⟩)² ≤ ‖V‖²·(‖U‖²·‖V‖²)`.  The `‖V‖²` factor is kept uncancelled on both sides — the
    honest ζ-free form (no reciprocal / discriminant division).  Feed `completedInner_re_amgm` the
    vector `(‖V‖²)•U` at parameter `λ = Re⟨U,V⟩` and cancel a common `‖V‖²·(Re⟨U,V⟩)²`. -/
theorem completedInner_re_cs_gen (U V : DLimCompletionRaw) :
    Rle (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
        (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V))) := by
  -- `Re⟨(‖V‖²)•U, V⟩ ≈ ‖V‖²·Re⟨U,V⟩`  (Hermitian symmetry + real-scalar peel)
  have hcross : Req
      (completedInner (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U) V).re
      (Rmul (completedNormSq V) (completedInner U V).re) := by
    have e1 : Req
        (completedInner (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U) V).re
        (completedInner V (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U)).re :=
      (completedInner_conj (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U) V).1
    have e2 : Req
        (completedInner V (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U)).re
        (Rmul (completedNormSq V) (completedInner V U).re) :=
      Req_trans (completedInner_smul_right (⟨completedNormSq V, zero⟩ : Complex) V U).1
        (Cmul_re_ofReal_csh (completedNormSq V) (completedInner V U))
    have e3 : Req (Rmul (completedNormSq V) (completedInner V U).re)
        (Rmul (completedNormSq V) (completedInner U V).re) :=
      Rmul_congr (Req_refl (completedNormSq V)) ((completedInner_conj V U).1)
    exact Req_trans e1 (Req_trans e2 e3)
  -- `‖(‖V‖²)•U‖² ≈ ‖V‖²·‖V‖²·‖U‖²`
  have hnorm : Req (completedNormSq (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U))
      (Rmul (Rmul (completedNormSq V) (completedNormSq V)) (completedNormSq U)) :=
    completedNormSq_smul_real (completedNormSq V) U
  -- the AM-GM core at `λ = Re⟨U,V⟩`, `U := (‖V‖²)•U`, `V := V`
  have amgm := completedInner_re_amgm (completedInner U V).re
    (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U) V
  -- `p·(a·p) ≈ a·(p·p)`  (real reassociation)
  have hpap : Req
      (Rmul (completedInner U V).re (Rmul (completedNormSq V) (completedInner U V).re))
      (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)) :=
    Req_trans
      (Req_symm (Rmul_assoc (completedInner U V).re (completedNormSq V) (completedInner U V).re))
      (Req_trans
        (Rmul_congr (Rmul_comm (completedInner U V).re (completedNormSq V))
          (Req_refl (completedInner U V).re))
        (Rmul_assoc (completedNormSq V) (completedInner U V).re (completedInner U V).re))
  -- rewrite the AM-GM LHS `(p+p)·Re⟨a•U,V⟩` as `a·p² + a·p²`
  have hLHS : Req
      (Rmul (Radd (completedInner U V).re (completedInner U V).re)
        (completedInner (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U) V).re)
      (Radd (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))) :=
    Req_trans (Rmul_congr (Req_refl (Radd (completedInner U V).re (completedInner U V).re)) hcross)
      (Req_trans
        (Rmul_distrib_right (completedInner U V).re (completedInner U V).re
          (Rmul (completedNormSq V) (completedInner U V).re))
        (Radd_congr hpap hpap))
  -- rewrite the AM-GM RHS `‖a•U‖² + p²·‖V‖²` as `a·(b·a) + a·p²`
  have hRHS1 : Req (completedNormSq (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U))
      (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V))) :=
    Req_trans hnorm
      (Req_trans (Rmul_assoc (completedNormSq V) (completedNormSq V) (completedNormSq U))
        (Rmul_congr (Req_refl (completedNormSq V)) (Rmul_comm (completedNormSq V) (completedNormSq U))))
  have hRHS2 : Req
      (Rmul (Rmul (completedInner U V).re (completedInner U V).re) (completedNormSq V))
      (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)) :=
    Rmul_comm (Rmul (completedInner U V).re (completedInner U V).re) (completedNormSq V)
  have hRHS : Req
      (Radd (completedNormSq (dlimCompletionSmul (⟨completedNormSq V, zero⟩ : Complex) U))
        (Rmul (Rmul (completedInner U V).re (completedInner U V).re) (completedNormSq V)))
      (Radd (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))) :=
    Radd_congr hRHS1 hRHS2
  -- the cancelled inequality `a·p² + a·p² ≤ a·(b·a) + a·p²`
  have hcanc : Rle
      (Radd (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)))
      (Radd (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))) :=
    Rle_trans (Rle_of_Req (Req_symm hLHS)) (Rle_trans amgm (Rle_of_Req hRHS))
  -- subtract `a·p²` from both sides
  have hsub : Req
      (Rsub
        (Radd (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
              (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)))
        (Radd (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
              (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))))
      (Rsub (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))) :=
    Req_trans
      (Rsub_Radd_Radd (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
        (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
        (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))
        (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)))
      (Req_trans
        (Radd_congr
          (Req_refl (Rsub (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
            (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))))
          (Radd_neg (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re))))
        (Radd_zero (Rsub (Rmul (completedNormSq V) (Rmul (completedNormSq U) (completedNormSq V)))
          (Rmul (completedNormSq V) (Rmul (completedInner U V).re (completedInner U V).re)))))
  exact Rle_of_Rnonneg_Rsub_loc (Rnonneg_congr_loc hsub (Rnonneg_Rsub_of_Rle_loc hcanc))

-- ===========================================================================
-- TARGET B — fixed-vector inner-product continuity (division-free).
--   `‖V‖²·(Re⟨V,X⟩ − Re⟨V,Y⟩)² ≤ ‖V‖²·‖V‖²·d²(X,Y)`.
-- ===========================================================================

/-- **Fixed-vector inner-product continuity** in the division-free form: the real functional
    `Re⟨V,·⟩` is Lipschitz up to the `‖V‖²` factor,
    `‖V‖²·(Re⟨V,X⟩ − Re⟨V,Y⟩)² ≤ ‖V‖²·‖V‖²·d²(X,Y)`.  Instantiate `completedInner_re_cs_gen` at
    `U := X⊖Y`, using `Re⟨X⊖Y,V⟩ = Re⟨V,X⟩ − Re⟨V,Y⟩` and `‖X⊖Y‖² = d²(X,Y)`.  `hV` is documentary
    (the nonnegativity of `‖V‖²`); the bound holds unconditionally. -/
theorem inner_fixed_continuity_cs (V : DLimCompletionRaw) (hV : Rnonneg (completedNormSq V))
    (X Y : DLimCompletionRaw) :
    Rle (Rmul (completedNormSq V)
          (Rmul (Rsub (completedInner V X).re (completedInner V Y).re)
                (Rsub (completedInner V X).re (completedInner V Y).re)))
        (Rmul (Rmul (completedNormSq V) (completedNormSq V)) (completedDist2 X Y)) := by
  -- `Re⟨X⊖Y, V⟩ ≈ Re⟨V,X⟩ − Re⟨V,Y⟩`  (Hermitian symmetry + right-additivity of the second slot)
  have hconj : Req (completedInner (dlimCompletionSub X Y) V).re
      (completedInner V (dlimCompletionSub X Y)).re :=
    (completedInner_conj (dlimCompletionSub X Y) V).1
  have hCe : Ceq (completedInner V (dlimCompletionSub X Y))
      (Cadd (completedInner V X) (Cneg (completedInner V Y))) :=
    Ceq_trans (completedInner_add_right V X (dlimCompletionNeg Y))
      (Cadd_congr (Ceq_refl (completedInner V X)) (completedInner_neg_right_cpl V Y))
  have hUre : Req (completedInner (dlimCompletionSub X Y) V).re
      (Rsub (completedInner V X).re (completedInner V Y).re) :=
    Req_trans hconj hCe.1
  -- transport the LHS of the general CS through `hUre`
  have hLeq : Req
      (Rmul (completedNormSq V)
        (Rmul (completedInner (dlimCompletionSub X Y) V).re
              (completedInner (dlimCompletionSub X Y) V).re))
      (Rmul (completedNormSq V)
        (Rmul (Rsub (completedInner V X).re (completedInner V Y).re)
              (Rsub (completedInner V X).re (completedInner V Y).re))) :=
    Rmul_congr (Req_refl (completedNormSq V)) (Rmul_congr hUre hUre)
  -- rearrange the RHS product `a·(d·a) ≈ (a·a)·d`  (`d = ‖X⊖Y‖² = d²(X,Y)` definitionally)
  have hReq : Req
      (Rmul (completedNormSq V)
        (Rmul (completedNormSq (dlimCompletionSub X Y)) (completedNormSq V)))
      (Rmul (Rmul (completedNormSq V) (completedNormSq V))
        (completedNormSq (dlimCompletionSub X Y))) :=
    Req_trans
      (Rmul_congr (Req_refl (completedNormSq V))
        (Rmul_comm (completedNormSq (dlimCompletionSub X Y)) (completedNormSq V)))
      (Req_symm (Rmul_assoc (completedNormSq V) (completedNormSq V)
        (completedNormSq (dlimCompletionSub X Y))))
  exact Rle_trans (Rle_of_Req (Req_symm hLeq))
    (Rle_trans (completedInner_re_cs_gen (dlimCompletionSub X Y) V) (Rle_of_Req hReq))

end UOR.Bridge.F1Square.Square
