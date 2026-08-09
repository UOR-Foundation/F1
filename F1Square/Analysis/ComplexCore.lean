/-
F1 square — **the zeta-free complex foundation**: complex conjugation and the elementary
`Cadd`/`Cmul`/`Cconj` congruence and ring laws, extracted into a module whose import cone is
`Complex` alone (transitively `Real`/`Rat`/`QOrder`/`RingNF`/`RingTac`) — provably free of ζ, η,
the zeros, and the Li stack.

WHY THIS EXISTS. These lemmas are componentwise lifts of real identities and use nothing analytic,
but historically they lived in files (`Reflection`, `ComplexConjAlgebra`, `ComplexArgLower`,
`EtaVariation`) whose cones reach `ComplexZeta` and the zero-bearing ζ. That made every downstream
consumer — including the genuine Hilbert–Pólya construction in `FinInnerProduct.lean` — architecturally
zeta-tainted even though no zero is ever used. This module is the canonical home for the elementary
laws; the four files above now import it and no longer define their own copies, so a consumer that
needs only conjugation/ring algebra can stay zeta-free by importing `ComplexCore` directly.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.Complex

namespace UOR.Bridge.F1Square.Analysis

-- ===========================================================================
-- Private real-negation helpers (kept private to avoid clashing with the public
-- copies in the ζ-tainted `RealPow`/`ComplexZeta`; proved from `Real` primitives).
-- ===========================================================================

/-- `−(−x) ≈ x`. -/
private theorem rneg_neg (x : Real) : Req (Rneg (Rneg x)) x :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (neg (x.seq n))) (x.seq n)
    simp only [Qeq, neg]; push_cast; ring_uor)

/-- `−(x + y) ≈ (−x) + (−y)`. -/
private theorem rneg_radd (x y : Real) : Req (Rneg (Radd x y)) (Radd (Rneg x) (Rneg y)) :=
  Req_of_seq_Qeq (fun n => by
    show Qeq (neg (add (x.seq (2 * n + 1)) (y.seq (2 * n + 1))))
      (add (neg (x.seq (2 * n + 1))) (neg (y.seq (2 * n + 1))))
    simp only [Qeq, neg, add]; push_cast; ring_uor)

/-- `−0 ≈ 0`. -/
private theorem rneg_zero : Req (Rneg zero) zero :=
  Req_of_seq_Qeq (fun _ => by show Qeq (neg (⟨0, 1⟩ : Q)) ⟨0, 1⟩; decide)

-- ===========================================================================
-- Complex conjugation and the elementary ring/congruence laws.
-- ===========================================================================

/-- Complex **conjugation** `z ↦ z̄` — same real part, negated imaginary part. -/
def Cconj (z : Complex) : Complex := ⟨z.re, Rneg z.im⟩

/-- `Cconj` respects `≈`. -/
theorem Cconj_congr {z w : Complex} (h : Ceq z w) : Ceq (Cconj z) (Cconj w) :=
  ⟨h.1, Rneg_congr h.2⟩

/-- **`Cconj` is an involution**: `conj(conj z) = z`. -/
theorem Cconj_Cconj (z : Complex) : Ceq (Cconj (Cconj z)) z :=
  ⟨Req_refl z.re, rneg_neg z.im⟩

/-- **`Cconj` distributes over `Cadd`**: `conj(z + w) = conj z + conj w`. -/
theorem Cconj_Cadd (z w : Complex) : Ceq (Cconj (Cadd z w)) (Cadd (Cconj z) (Cconj w)) :=
  ⟨Req_refl (Radd z.re w.re), rneg_radd z.im w.im⟩

/-- **`Cconj` fixes `0`**: `conj 0 = 0`. -/
theorem Cconj_Czero : Ceq (Cconj Czero) Czero :=
  ⟨Req_refl zero, rneg_zero⟩

/-- **Conjugate distributes over product** `z̄·w̄ = (zw)‾`. Componentwise: Re uses
    `(−Im z)(−Im w) = Im z·Im w`, Im uses `−(Re z·Im w + Im z·Re w) = Re z·(−Im w) + (−Im z)·Re w`. -/
theorem Cconj_Cmul (z w : Complex) : Ceq (Cconj (Cmul z w)) (Cmul (Cconj z) (Cconj w)) := by
  have hnn : Req (Rmul (Rneg z.im) (Rneg w.im)) (Rmul z.im w.im) :=
    Req_trans (Rmul_neg_left z.im (Rneg w.im))
      (Req_trans (Rneg_congr (Rmul_neg_right z.im w.im)) (rneg_neg (Rmul z.im w.im)))
  refine ⟨?_, ?_⟩
  · show Req (Rsub (Rmul z.re w.re) (Rmul z.im w.im))
      (Rsub (Rmul z.re w.re) (Rmul (Rneg z.im) (Rneg w.im)))
    exact Rsub_congr (Req_refl (Rmul z.re w.re)) (Req_symm hnn)
  · show Req (Rneg (Radd (Rmul z.re w.im) (Rmul z.im w.re)))
      (Radd (Rmul z.re (Rneg w.im)) (Rmul (Rneg z.im) w.re))
    refine Req_trans (rneg_radd (Rmul z.re w.im) (Rmul z.im w.re)) ?_
    exact Req_symm (Radd_congr (Rmul_neg_right z.re w.im) (Rmul_neg_left z.im w.re))

/-- ℂ addition respects `≈`. -/
theorem Cadd_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cadd z w) (Cadd z' w') := ⟨Radd_congr hz.1 hw.1, Radd_congr hz.2 hw.2⟩

/-- ℂ multiplication respects `≈`. -/
theorem Cmul_congr {z z' w w' : Complex} (hz : Ceq z z') (hw : Ceq w w') :
    Ceq (Cmul z w) (Cmul z' w') :=
  ⟨Rsub_congr (Rmul_congr hz.1 hw.1) (Rmul_congr hz.2 hw.2),
   Radd_congr (Rmul_congr hz.1 hw.2) (Rmul_congr hz.2 hw.1)⟩

end UOR.Bridge.F1Square.Analysis
