/-
F1 square — Track 1/2 gateway: **certified integration**, the constructive Riemann integral over the
unit interval `[0,1]`, foundation layer.

The document names certified integration as the gateway for *both* tracks: the item-3 Mellin link
(`∫₁^∞ t^{s/2−1}ψ(t)dt`, connecting the Jacobi theta function `ThetaFunction.lean` to the completed
ζ) and Track-2's genuine `f, f̂` Weil-pairing objects. No `∫` exists beyond interface statements.

This file lays the foundation: the **left Riemann sum** `R_N(f) = (1/(N+1))·Σ_{i≤N} f(i/(N+1))` over
`[0,1]` with `N+1` equal subintervals (rational partition points, so no `Rdiv`-witness threading), its
congruence in `f`, and the first integral identity `∫₀¹ c = c` (`riemannSum_const`). Convergence for
Lipschitz integrands (via dyadic refinement → `RReg` → `Rlim`, the established UOR pattern) is the
next layer.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RSum
import F1Square.Analysis.ComplexPow
import F1Square.Analysis.RealPow

namespace UOR.Bridge.F1Square.Analysis

/-- **The left Riemann sum** of `f` over `[0,1]` with `N+1` equal subintervals:
    `R_N(f) = (1/(N+1))·Σ_{i=0}^{N} f(i/(N+1))`. The partition points `i/(N+1)` are rational
    embeddings (`ofQ`), so the sum is `Rdiv`-free. -/
def riemannSum (f : Real → Real) (N : Nat) : Real :=
  Rmul (ofQ (⟨1, N + 1⟩ : Q) (Nat.succ_pos N))
    (RsumN (fun i => f (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N))) (N + 1))

/-- The Riemann sum respects `≈` of the integrand at the partition points. -/
theorem riemannSum_congr {f g : Real → Real} (N : Nat)
    (h : ∀ i, i < N + 1 →
      Req (f (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))
          (g (ofQ (⟨(i : Int), N + 1⟩ : Q) (Nat.succ_pos N)))) :
    Req (riemannSum f N) (riemannSum g N) :=
  Rmul_congr (Req_refl _) (RsumN_congr (N + 1) h)

/-- **Sum of `M` copies of `c` is `M·c`.** -/
theorem RsumN_const (c : Real) : ∀ M, Req (RsumN (fun _ => c) M) (Rmul (RofNat M) c)
  | 0 => Req_symm (Req_trans (Rmul_comm (RofNat 0) c) (Rmul_zero c))
  | (M + 1) => by
      have hsucc : Req (RofNat (M + 1)) (Radd (RofNat M) one) :=
        Req_symm (Req_trans (Radd_ofQ_ofQ Nat.one_pos Nat.one_pos)
          (ofQ_congr (add_den_pos Nat.one_pos Nat.one_pos) Nat.one_pos
            (by simp only [Qeq, add]; push_cast; ring_uor)))
      refine Req_trans (Radd_congr (RsumN_const c M) (Req_refl c)) ?_
      refine Req_symm (Req_trans (Rmul_congr hsucc (Req_refl c)) ?_)
      exact Req_trans (Rmul_distrib_right (RofNat M) one c) (Radd_congr (Req_refl _) (Rone_mul c))

/-- **`∫₀¹ c = c`** — the Riemann sum of a constant integrand equals the constant (the integral over
    the unit interval). The first integral identity: `(1/(N+1))·((N+1)·c) = c`. -/
theorem riemannSum_const (c : Real) (N : Nat) : Req (riemannSum (fun _ => c) N) c := by
  have hone : Req (Rmul (ofQ (⟨1, N + 1⟩ : Q) (Nat.succ_pos N)) (RofNat (N + 1)))
      (ofQ (⟨1, 1⟩ : Q) Nat.one_pos) :=
    Req_trans (Rmul_ofQ_ofQ (Nat.succ_pos N) Nat.one_pos)
      (ofQ_congr (Qmul_den_pos (Nat.succ_pos N) Nat.one_pos) Nat.one_pos
        (by simp only [Qeq, mul]; push_cast; ring_uor))
  refine Req_trans (Rmul_congr (Req_refl _) (RsumN_const c (N + 1))) ?_
  refine Req_trans (Req_symm (Rmul_assoc _ (RofNat (N + 1)) c)) ?_
  exact Req_trans (Rmul_congr hone (Req_refl c)) (Rone_mul c)

end UOR.Bridge.F1Square.Analysis
