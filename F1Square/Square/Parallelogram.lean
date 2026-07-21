/-
F1 square — **the pre-Hilbert layer, brick 12** (`Parallelogram.lean`): **THE PARALLELOGRAM LAW
and the squared-distance geometry** — the sqrt-free metric substrate of the completion axis.

- `innerN_add_right` / `innerN_sub_right` — bilinearity completed on the second slot.
- **`parallelogram`** — `⟨f+g, f+g⟩ + ⟨f−g, f−g⟩ ≈ (⟨f,f⟩ + ⟨f,f⟩) + (⟨g,g⟩ + ⟨g,g⟩)`: THE
  characterizing identity of inner-product geometry, proven by bilinear expansion and the
  `RsumL` additive normalizer (the cross terms cancel as ± pairs in the multiset).
- `dist2 f g N = ⟨f−g, f−g⟩_N` — the SQUARED distance: the substrate has no square root, so the
  constructive metric geometry runs on `dist2` throughout; `dist2_nonneg`, `dist2_self`,
  `dist2_symm`.
- **`dist2_doubling`** — `d²(f,h) ≤ (d²(f,g) + d²(f,g)) + (d²(g,h) + d²(g,h))`: the
  quasi-triangle inequality of the squared distance, an immediate corollary of the
  parallelogram law (drop the nonnegative `⟨a−b, a−b⟩` term). This is the inequality Cauchy
  sequences and completions are phrased with when no square root exists.

WHY (the Sonine route, step 3). The completion axis ("completeness past finite support") needs a
metric to be complete FOR. Without sqrt the metric is the squared distance, and its usable
triangle-type inequality is the doubling bound — delivered here from the parallelogram law,
which is itself the identity that certifies the pairing is genuinely an inner product (not just
a bilinear form). The Bishop-Cauchy completion over `dist2` is the banked next object.

HONEST SCOPE. Identities and inequalities at fixed truncation on the discrete substrate; no
completion is constructed, no L² mirror stated (needs an `L2Test.neg`/`sub` combinator, banked).
The crux fields stay `none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.Projection
import F1Square.Analysis.RAddNF
import F1Square.Analysis.MonotoneIntegral

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Bilinearity completed: the second slot.
-- ===========================================================================

/-- **Additivity in the second slot**: `⟨f, g + g'⟩_N ≈ ⟨f,g⟩_N + ⟨f,g'⟩_N`. -/
theorem innerN_add_right (f g g' : Nat → Real) (N : Nat) :
    Req (innerN f (fun i => Radd (g i) (g' i)) N) (Radd (innerN f g N) (innerN f g' N)) :=
  Req_trans (innerN_symm f (fun i => Radd (g i) (g' i)) N)
    (Req_trans (innerN_add_left g g' f N)
      (Radd_congr (innerN_symm g f N) (innerN_symm g' f N)))

/-- **Subtraction in the second slot**: `⟨f, g − g'⟩_N ≈ ⟨f,g⟩_N − ⟨f,g'⟩_N`. -/
theorem innerN_sub_right (f g g' : Nat → Real) (N : Nat) :
    Req (innerN f (fun i => Rsub (g i) (g' i)) N) (Rsub (innerN f g N) (innerN f g' N)) :=
  Req_trans (innerN_symm f (fun i => Rsub (g i) (g' i)) N)
    (Req_trans (innerN_sub_left g g' f N)
      (Rsub_congr (innerN_symm g f N) (innerN_symm g' f N)))

-- ===========================================================================
-- The parallelogram law.
-- ===========================================================================

/-- `(a+b)+(c+d) ≈ RsumL [a,b,c,d]` — quaternary flattening. -/
private theorem add4_eq_RsumL (a b c d : Real) :
    Req (Radd (Radd a b) (Radd c d)) (RsumL [a, b, c, d]) :=
  Req_trans (Radd_congr (Radd_eq_RsumL a b) (Radd_eq_RsumL c d))
    (Req_symm (RsumL_append [a, b] [c, d]))

/-- **THE PARALLELOGRAM LAW**: `⟨f+g, f+g⟩ + ⟨f−g, f−g⟩ ≈ (⟨f,f⟩ + ⟨f,f⟩) + (⟨g,g⟩ + ⟨g,g⟩)` —
    bilinear expansion; the cross terms `±⟨f,g⟩, ±⟨g,f⟩` cancel as multiset pairs (`RsumL`
    engine). The identity that certifies the pairing is inner-product geometry, and the source
    of the sqrt-free quasi-triangle inequality below. -/
theorem parallelogram (f g : Nat → Real) (N : Nat) :
    Req (Radd (innerN (fun i => Radd (f i) (g i)) (fun i => Radd (f i) (g i)) N)
              (innerN (fun i => Rsub (f i) (g i)) (fun i => Rsub (f i) (g i)) N))
        (Radd (Radd (innerN f f N) (innerN f f N))
              (Radd (innerN g g N) (innerN g g N))) := by
  -- expand ⟨f+g, f+g⟩ ≈ (⟨f,f⟩ + ⟨f,g⟩) + (⟨g,f⟩ + ⟨g,g⟩)
  have hPP : Req (innerN (fun i => Radd (f i) (g i)) (fun i => Radd (f i) (g i)) N)
      (Radd (Radd (innerN f f N) (innerN f g N)) (Radd (innerN g f N) (innerN g g N))) :=
    Req_trans (innerN_add_left f g (fun i => Radd (f i) (g i)) N)
      (Radd_congr (innerN_add_right f f g N) (innerN_add_right g f g N))
  -- expand ⟨f−g, f−g⟩ ≈ (⟨f,f⟩ − ⟨f,g⟩) − (⟨g,f⟩ − ⟨g,g⟩)
  have hMM : Req (innerN (fun i => Rsub (f i) (g i)) (fun i => Rsub (f i) (g i)) N)
      (Rsub (Rsub (innerN f f N) (innerN f g N)) (Rsub (innerN g f N) (innerN g g N))) :=
    Req_trans (innerN_sub_left f g (fun i => Rsub (f i) (g i)) N)
      (Rsub_congr (innerN_sub_right f f g N) (innerN_sub_right g f g N))
  refine Req_trans (Radd_congr hPP hMM) ?_
  -- abelian collapse: (A+B)+(C+D) + ((A−B)−(C−D)) ≈ (A+A)+(D+D)
  have hflat2 : Req (Rsub (Rsub (innerN f f N) (innerN f g N))
        (Rsub (innerN g f N) (innerN g g N)))
      (RsumL [innerN f f N, Rneg (innerN f g N), Rneg (innerN g f N), innerN g g N]) := by
    refine Req_trans (Radd_congr (Req_refl _)
      (Req_trans (Rneg_Radd (innerN g f N) (Rneg (innerN g g N)))
        (Radd_congr (Req_refl _) (Rneg_neg (innerN g g N))))) ?_
    exact add4_eq_RsumL (innerN f f N) (Rneg (innerN f g N))
      (Rneg (innerN g f N)) (innerN g g N)
  refine Req_trans (Radd_congr
    (add4_eq_RsumL (innerN f f N) (innerN f g N) (innerN g f N) (innerN g g N))
    hflat2) ?_
  refine Req_trans (Req_symm (RsumL_append
    [innerN f f N, innerN f g N, innerN g f N, innerN g g N]
    [innerN f f N, Rneg (innerN f g N), Rneg (innerN g f N), innerN g g N])) ?_
  -- cancel the ⟨f,g⟩ pair: [A,B,C,D,A,−B,−C,D] → [A,C,D,A,−C,D]
  refine Req_trans (RsumL_cancel_anywhere (innerN f g N)
    [innerN f f N] [innerN g f N, innerN g g N, innerN f f N]
    [Rneg (innerN g f N), innerN g g N]) ?_
  -- cancel the ⟨g,f⟩ pair: [A,C,D,A,−C,D] → [A,D,A,D]
  refine Req_trans (RsumL_cancel_anywhere (innerN g f N)
    [innerN f f N] [innerN g g N, innerN f f N] [innerN g g N]) ?_
  -- permute [A,D,A,D] → [A,A,D,D] and unflatten
  refine Req_trans (RsumL_perm (List.Perm.cons (innerN f f N)
    (List.Perm.swap (innerN f f N) (innerN g g N) [innerN g g N]))) ?_
  exact Req_symm (add4_eq_RsumL (innerN f f N) (innerN f f N)
    (innerN g g N) (innerN g g N))

-- ===========================================================================
-- The squared distance and its quasi-triangle inequality.
-- ===========================================================================

/-- The **squared distance** `d²(f,g) = ⟨f−g, f−g⟩_N` — the substrate has no square root, so
    the constructive metric geometry runs on the square. -/
def dist2 (f g : Nat → Real) (N : Nat) : Real :=
  innerN (fun i => Rsub (f i) (g i)) (fun i => Rsub (f i) (g i)) N

/-- `d²(f,g) ≥ 0`. -/
theorem dist2_nonneg (f g : Nat → Real) (N : Nat) : Rnonneg (dist2 f g N) :=
  innerN_self_nonneg (fun i => Rsub (f i) (g i)) N

/-- `d²(f,f) ≈ 0`. -/
theorem dist2_self (f : Nat → Real) (N : Nat) : Req (dist2 f f N) zero :=
  RsumN_zero N (fun i _ =>
    Req_trans (Rmul_congr (Radd_neg (f i)) (Req_refl _))
      (Req_trans (Rmul_comm zero _) (Rmul_zero _)))

/-- `d²(f,g) ≈ d²(g,f)` — the difference flips sign, the square does not. -/
theorem dist2_symm (f g : Nat → Real) (N : Nat) : Req (dist2 f g N) (dist2 g f N) :=
  RsumN_congr N (fun i _ =>
    Req_trans (Rmul_congr (Req_symm (Rneg_Rsub_flip (g i) (f i)))
                          (Req_symm (Rneg_Rsub_flip (g i) (f i))))
      (Req_trans (Rmul_neg_left _ _)
        (Req_trans (Rneg_congr (Rmul_neg_right _ _)) (Rneg_neg _))))

/-- **THE QUASI-TRIANGLE (doubling) INEQUALITY**:
    `d²(f,h) ≤ (d²(f,g) + d²(f,g)) + (d²(g,h) + d²(g,h))` — from the parallelogram law with
    `a = f−g`, `b = g−h` (`a+b ≈ f−h` termwise, and the `⟨a−b, a−b⟩ ≥ 0` term drops). The
    inequality Cauchy sequences and completions are phrased with when no square root exists. -/
theorem dist2_doubling (f g h : Nat → Real) (N : Nat) :
    Rle (dist2 f h N)
        (Radd (Radd (dist2 f g N) (dist2 f g N)) (Radd (dist2 g h N) (dist2 g h N))) := by
  have hsum : Req (dist2 f h N)
      (innerN (fun i => Radd (Rsub (f i) (g i)) (Rsub (g i) (h i)))
              (fun i => Radd (Rsub (f i) (g i)) (Rsub (g i) (h i))) N) :=
    innerN_congr N (fun i _ => Req_symm (Rsub_split (f i) (g i) (h i)))
      (fun i _ => Req_symm (Rsub_split (f i) (g i) (h i)))
  refine Rle_trans (Rle_of_Req hsum) ?_
  refine Rle_trans (Rle_self_Radd_right
    (innerN_self_nonneg (fun i => Rsub (Rsub (f i) (g i)) (Rsub (g i) (h i))) N)) ?_
  exact Rle_of_Req (parallelogram (fun i => Rsub (f i) (g i))
    (fun i => Rsub (g i) (h i)) N)

end UOR.Bridge.F1Square.Square
