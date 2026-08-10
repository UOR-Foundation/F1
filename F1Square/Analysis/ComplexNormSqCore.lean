/-
F1 square — **the CLEAN Complex-only squared modulus** `|z|² = re² + im²` (`ComplexNormSqCore.lean`).
This is the single, deliberately-minimal core the ℓ² completion's scalar multiplication consumes. The
existing `Analysis.ZeroGeometry.cnormSq` has the SAME definition but its module transitively reaches
`Analysis.Zeta` (via `RealPow`), and `Analysis.ComplexMod` is heavier still; this file re-extracts the
squared modulus with a Zeta-free cone (only `ComplexCore` + `RealSquareDefinite`), so the completion layer
that uses it stays candidate-independent and ζ/crux-free.

WHAT IS BUILT: `cNormSq z := re² + im²`; its NONNEGATIVITY (`cNormSq_nonneg`, sum of two squares); and the
two facts that make `z · conj z` the real scalar `|z|²` — `Cmul_Cconj_re` (`Re(z·z̄) = |z|²`) and
`Cmul_Cconj_im` (`Im(z·z̄) = 0`). These are exactly what the scalar-multiplication squared-norm scaling
`‖c·v‖² ≈ |c|²·‖v‖²` needs.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; Zeta-free cone. Crux `none`.
-/

import F1Square.Analysis.ComplexCore
import F1Square.Analysis.RealSquareDefinite

namespace UOR.Bridge.F1Square.Analysis

/-- The **complex squared modulus** `|z|² = re² + im²` — the clean core (NOT the ζ-tainted
    `ZeroGeometry.cnormSq`, NOT the heavy `ComplexMod`). -/
def cNormSq (z : Complex) : Real := Radd (Rmul z.re z.re) (Rmul z.im z.im)

/-- `|z|² ≥ 0` (a sum of two real squares). -/
theorem cNormSq_nonneg (z : Complex) : Rnonneg (cNormSq z) :=
  Rnonneg_Radd (Rnonneg_Rmul_self_loc z.re) (Rnonneg_Rmul_self_loc z.im)

/-- `|·|²` respects complex equality. -/
theorem cNormSq_congr {z w : Complex} (h : Ceq z w) : Req (cNormSq z) (cNormSq w) :=
  Radd_congr (Rmul_congr h.1 h.1) (Rmul_congr h.2 h.2)

/-- **Constructive Archimedean upper bound**: every real is `≤ B/1` for a computable `B : Nat`
    (`B := xBound x`, from `canon_bound`). Ported from the block-ladder Archimedean lemma, retargeted to
    the `ofQ ⟨B,1⟩` shape (defeq to `RofNat B`). -/
theorem exists_nat_ge_loc (x : Real) : ∃ B : Nat, Rle x (ofQ (⟨(B : Int), 1⟩ : Q) Nat.one_pos) := by
  refine ⟨xBound x, fun n => ?_⟩
  show Qle (x.seq n) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩)
  have h1 : Qle (x.seq n) (Qabs (x.seq n)) := by
    show (x.seq n).num * ((Qabs (x.seq n)).den : Int) ≤ (Qabs (x.seq n)).num * ((x.seq n).den : Int)
    simp only [Qabs]
    exact Int.mul_le_mul_of_nonneg_right Int.le_natAbs (by omega)
  have h2 : Qle (Qabs (x.seq n)) (⟨(xBound x : Int), 1⟩ : Q) := canon_bound x n
  have h3 : Qle (⟨(xBound x : Int), 1⟩ : Q) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_self_add (by show (0 : Int) ≤ 2; decide)
  have h23 : Qle (Qabs (x.seq n)) (add (⟨(xBound x : Int), 1⟩ : Q) ⟨2, n + 1⟩) :=
    Qle_trans (b := (⟨(xBound x : Int), 1⟩ : Q)) (by show (0 : Nat) < 1; decide) h2 h3
  exact Qle_trans (b := Qabs (x.seq n)) (x.den_pos n) h1 h23

/-- **A constructive natural upper bound for `|c|²`** (reviewer gate 2): `|c|² ≤ B` for a computable
    `B : Nat` — the scalar-magnitude bound scalar multiplication's reschedule needs. -/
theorem cNormSq_nat_bound (z : Complex) : ∃ B : Nat, Rle (cNormSq z) (ofQ (⟨(B : Int), 1⟩ : Q) Nat.one_pos) :=
  exists_nat_ge_loc (cNormSq z)

/-- `Rneg` is an involution (component form), used to collapse the `−(−im²)` from `z · z̄`. -/
private theorem Rneg_Rneg_core (r : Real) : Req (Rneg (Rneg r)) r :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (r.seq n))) (r.seq n)
    simp only [Qeq, neg]; push_cast; ring_uor)

/-- **`Re(z · conj z) = |z|²`**: `re·re − im·(−im) = re² + im²`. -/
theorem Cmul_Cconj_re (z : Complex) : Req (Cmul z (Cconj z)).re (cNormSq z) := by
  show Req (Rsub (Rmul z.re z.re) (Rmul z.im (Rneg z.im))) (Radd (Rmul z.re z.re) (Rmul z.im z.im))
  refine Req_trans (Rsub_congr (Req_refl _) (Rmul_neg_right z.im z.im)) ?_
  show Req (Radd (Rmul z.re z.re) (Rneg (Rneg (Rmul z.im z.im))))
    (Radd (Rmul z.re z.re) (Rmul z.im z.im))
  exact Radd_congr (Req_refl _) (Rneg_Rneg_core (Rmul z.im z.im))

/-- **`Im(z · conj z) = 0`** (so `z · conj z` is the real scalar `|z|²`): `re·(−im) + im·re = 0`. -/
theorem Cmul_Cconj_im (z : Complex) : Req (Cmul z (Cconj z)).im zero := by
  show Req (Radd (Rmul z.re (Rneg z.im)) (Rmul z.im z.re)) zero
  refine Req_trans (Radd_congr (Rmul_neg_right z.re z.im) (Rmul_comm z.im z.re)) ?_
  exact Req_trans (Radd_comm _ _) (Radd_neg (Rmul z.re z.im))

end UOR.Bridge.F1Square.Analysis
