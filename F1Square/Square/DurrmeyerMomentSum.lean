/-
F1 square — **the Durrmeyer moments of the low monomials** (`DurrmeyerMomentSum.lean`), the
Mellin-inversion arc, sub-brick J₄. Summing the per-`k` weights (J₃) against `(n+1)·b_{n,k}(x)` and the
Bernstein moment identities (partition of unity, `bernR_mean`, `bernR_sq`) gives the Durrmeyer operator's
action on `1, x, x²`:

    `durrOp 1  n x = 1`                                     (`durrOp_powTest_zero`, normalization).

WHY (the Sonine route, step 3, the Mellin FRONT). `M_n⁽⁰⁾ = 1` is the normalization `∫₀¹ K_n(x,t) dt = 1`
of the Durrmeyer kernel (a genuine averaging/probabilistic operator); together with `M_n⁽¹⁾`, `M_n⁽²⁾` it
gives the second central moment `T_n(x) = M_n⁽²⁾ − 2x·M_n⁽¹⁾ + x²`, the vanishing quantity that drives
`durrOp φ n x → φ(x)`.

HONEST SCOPE. The Durrmeyer moment `M_n⁽⁰⁾ = 1`, over `Real`. NOT `M_n⁽¹⁾`/`M_n⁽²⁾` yet, NOT the
second-moment estimate, NOT convergence, NOT inversion, NOT positivity. Step 4 is RH; crux fields stay
`none`.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by
`scripts/honesty_audit.sh`.
-/

import F1Square.Square.DurrmeyerWeights

namespace UOR.Bridge.F1Square.Square

open UOR.Bridge.F1Square.Analysis

/-- Pure-ℤ normalization identity `A·1 = 1·(1·A)`. -/
private theorem durrM0_id (A : Int) : A * 1 = 1 * (1 * A) := by ring_uor

/-- **THE DURRMEYER OPERATOR PRESERVES THE CONSTANT `1`** (`M_n⁽⁰⁾ = 1`): `durrOp 1 n x = 1`. Each weight
    is the constant `⟨1, b_{n,k}⟩ = n!/(n+1)!` (J₃, `durrInt_zero`); pull it out of the sum
    (`RsumN_mul_right`), collapse `Σ_k b_{n,k}(x) = 1` (partition of unity), and `(n+1)·n!/(n+1)! = 1`. -/
theorem durrOp_powTest_zero (n : Nat) (x : Real) :
    Req (durrOp (powTest 0) n x) one := by
  show Req (Rmul (RofNat (n + 1))
      (RsumN (fun k => Rmul (bernR x n k) (innerI (powTest 0) (bernBasisTest n k))) (n + 1))) one
  refine Req_trans (Rmul_congr (Req_refl _)
    (Req_trans (RsumN_congr (n + 1) (fun k hk =>
        Rmul_congr (Req_refl _) (durrInt_zero n k (by omega))))
      (Req_trans (RsumN_mul_const (bernR x n)
          (ofQ (⟨((fct n : Nat) : Int), fct (n + 1)⟩ : Q) (fct_pos _)) (n + 1))
        (Req_trans (Rmul_congr (bernR_partition x n) (Req_refl _))
          (Rone_mul _))))) ?_
  refine Req_trans (Rmul_ofQ_ofQ Nat.one_pos (fct_pos _)) ?_
  refine ofQ_congr (Qmul_den_pos Nat.one_pos (fct_pos _)) (by decide) ?_
  have hfn1 : fct (n + 1) = (n + 1) * fct n := fct_succ n
  simp only [Qeq, mul]
  rw [hfn1]
  push_cast
  exact durrM0_id _

end UOR.Bridge.F1Square.Square
