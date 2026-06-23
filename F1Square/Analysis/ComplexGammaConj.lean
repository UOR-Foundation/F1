/-
F1 square — Track 1: **conjugation of the Spouge Γ approximant** `Γ(s̄/2) = conj(Γ(s/2))` — the
Γ-side discharge of `Cxi_conj`'s `hg`.

`CSpougeGammaW w = (w+b)^{w−½} · e^{−(w+b)} · [c₀ + Σ_{k} cₖ/(w+(k−1))]`.  Conjugation distributes
(`Cconj_Cmul`) over the three factors, each of which conjugates with the toolbox:
  * the **bracket** `CspougeBracketW` is a `Cadd`-recursion of `cₖ·(w+(k−1))⁻¹` with real `cₖ`; it
    conjugates by induction (`Cconj_Cadd`/`Cconj_Cmul`/`Cconj_ofReal`/`Cinv_conj`), since
    `CdigammaArg (s̄) = conj(CdigammaArg s)` (cheaply defeq — `⟨Re+n, Im⟩`, no `Cexp`);
  * the **base power** `(w+b)^{w−½}` via `Cpow_conj` (note `CspougeBase (s̄) = conj(CspougeBase s)`,
    `(w̄−½) = conj(w−½)`), carrying its `hre` `RlogPos`-congruence seam;
  * the **exponential** `e^{−(w+b)}` via `Cexp_conj`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.ComplexLogConj
import F1Square.Analysis.ComplexConjAlgebra
import F1Square.Analysis.ComplexArgLower

namespace UOR.Bridge.F1Square.Analysis

/-- **Conjugation of the Spouge bracket auxiliary** `CspougeBracketWAux (w̄) = conj(CspougeBracketWAux w)`
    — by induction on the term count: the base `c₀` is real (`Cconj_ofReal`), each added term
    `cₖ·(w+(k−1))⁻¹` conjugates via `Cconj_Cmul` + `Cconj_ofReal` + `Cinv_conj` (the `s̄`-side `Re w`
    bound `hcwc` supplies the inverse witness; `CdigammaArg (Cconj w) k = Cconj (CdigammaArg w k)`). -/
theorem CspougeBracketWAux_conj (w : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcw : Rle (ofQ c hcd) w.re) (hcwc : Rle (ofQ c hcd) (Cconj w).re) (a : Q) (hadp : 0 < a.den) :
    ∀ (m : Nat) (ha : ∀ (k : Nat), 1 ≤ k → k ≤ m → Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)),
      Ceq (CspougeBracketWAux (Cconj w) hcn hcd hcwc a hadp m ha)
          (Cconj (CspougeBracketWAux w hcn hcd hcw a hadp m ha))
  | 0, _ => Ceq_symm (Cconj_ofReal spougeSqrt2pi)
  | (k + 1), ha => by
      refine Ceq_trans (Cadd_congr
        (CspougeBracketWAux_conj w hcn hcd hcw hcwc a hadp k
          (fun j hj1 hjk => ha j hj1 (Nat.le_succ_of_le hjk))) ?term)
        (Ceq_symm (Cconj_Cadd (CspougeBracketWAux w hcn hcd hcw a hadp k
          (fun j hj1 hjk => ha j hj1 (Nat.le_succ_of_le hjk)))
          (Cmul (ofReal (spougeCoeff a hadp (k + 1) (ha (k + 1) (Nat.le_add_left 1 k) (Nat.le_refl _))))
            (Cinv (CdigammaArg w k) (CdigK c) (CdigammaArg_witness hcn hcd hcw k)))))
      refine Ceq_trans (Cmul_congr (Ceq_symm (Cconj_ofReal _)) ?inv)
        (Ceq_symm (Cconj_Cmul (ofReal (spougeCoeff a hadp (k + 1)
          (ha (k + 1) (Nat.le_add_left 1 k) (Nat.le_refl _))))
          (Cinv (CdigammaArg w k) (CdigK c) (CdigammaArg_witness hcn hcd hcw k))))
      exact Cinv_conj (CdigammaArg w k) (CdigK c) (CdigammaArg_witness hcn hcd hcw k) (CdigK c)
        (CdigammaArg_witness hcn hcd hcwc k)

/-- **Conjugation of the Spouge bracket** `CspougeBracketW (w̄) = conj(CspougeBracketW w)`. -/
theorem CspougeBracketW_conj (w : Complex) {c : Q} (hcn : 0 < c.num) (hcd : 0 < c.den)
    (hcw : Rle (ofQ c hcd) w.re) (hcwc : Rle (ofQ c hcd) (Cconj w).re) (a : Q) (hadp : 0 < a.den)
    (N : Nat) (ha : ∀ (k : Nat), 1 ≤ k → k ≤ N → Qlt (⟨1, 1⟩ : Q) (Qsub a ⟨(k : Int), 1⟩)) :
    Ceq (CspougeBracketW (Cconj w) hcn hcd hcwc a hadp N ha)
        (Cconj (CspougeBracketW w hcn hcd hcw a hadp N ha)) :=
  CspougeBracketWAux_conj w hcn hcd hcw hcwc a hadp N ha

end UOR.Bridge.F1Square.Analysis
