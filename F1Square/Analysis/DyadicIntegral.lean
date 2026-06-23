/-
F1 square — certified integration, **convergence layer**: the dyadic Riemann sums of a Lipschitz
integrand form a regular sequence, so the integral exists as a Bishop limit.

The dyadic sequence `D k = riemannSum f (2^k − 1)` uses `2^k` equal subintervals. The refinement
bound (`riemannSum_refine`) gives `|D_{k+1} − D_k| ≤ L/(4·2^k)` (doubling the partition: parameter
`2^k−1 → 2(2^k−1)+1 = 2^{k+1}−1`). The geometric increment `L/(4·2^k)` sits under the digamma
envelope `K/((k+1)k)` (with `K = L`, since `(k+1)k ≤ 4·2^k`), so the generic regularity engine
`genSum_RReg` applies verbatim: the `L`-reindexed partial sums of the increments are `RReg`, and
`Rlim` produces the integral.

Pure Lean 4 core, no Mathlib, no `sorry`/`native_decide`, choice-free; audited by `scripts/honesty_audit.sh`.
-/

import F1Square.Analysis.RiemannConv
import F1Square.Analysis.ComplexDigamma

namespace UOR.Bridge.F1Square.Analysis

/-- **The digamma envelope** `(m+1)·m ≤ 4·2^m` — the geometric increment `L/(4·2^m)` sits under the
    `K/((m+1)m)` term-bound shape `genSum_RReg` requires (with `K = L`). -/
theorem two_mul_env : ∀ m : Nat, (m + 1) * m ≤ 4 * 2 ^ m
  | 0 => by decide
  | (m + 1) => by
    have ih := two_mul_env m
    have hk : m + 1 ≤ 2 ^ (m + 1) := Nat.le_of_lt Nat.lt_two_pow_self
    have hp : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by
      simp only [Nat.succ_mul, Nat.mul_succ]; omega
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    omega

/-- **Denominator-antitone scaling**: for `L ≥ 0`, a larger denominator gives a smaller scaled
    fraction, `L/d₁ ≤ L/d₂` when `d₂ ≤ d₁`. Proved at the `Int` level (avoids the `mul`-`whnf`
    blowup). -/
theorem qmul_den_anti {L : Q} (hLn : 0 ≤ L.num) {d1 d2 : Nat}
    (h : d2 ≤ d1) : Qle (mul L (⟨1, d1⟩ : Q)) (mul L (⟨1, d2⟩ : Q)) := by
  show (L.num * 1) * ((L.den * d2 : Nat) : Int) ≤ (L.num * 1) * ((L.den * d1 : Nat) : Int)
  refine Int.mul_le_mul_of_nonneg_left ?_ (by simpa using hLn)
  exact_mod_cast Nat.mul_le_mul_left L.den h

/-- The dyadic Riemann sum with `2^k` equal subintervals on `[0,1]`. -/
def dyadicR (f : Real → Real) (k : Nat) : Real := riemannSum f (2 ^ k - 1)

/-- The refinement increment `D_{k+1} − D_k`. -/
def dyadicTerm (f : Real → Real) (k : Nat) : Real :=
  Rsub (dyadicR f (k + 1)) (dyadicR f k)

/-- **The dyadic increment two-sided bound** `|D_{m+1} − D_m| ≤ L/((m+1)m)` for `m ≥ 1` — the exact
    shape `genSum_RReg` consumes (with `K = L`). Built from `riemannSum_refine` (giving `L/(4·2^m)`)
    transported under the envelope `(m+1)m ≤ 4·2^m`. -/
theorem dyadicTerm_bound {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) (m : Nat) (hm : 1 ≤ m) :
    Rle (Rneg (ofQ (mul L (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hLd (digamma_succ_mul_pos hm))))
        (dyadicTerm f m)
    ∧ Rle (dyadicTerm f m)
          (ofQ (mul L (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hLd (digamma_succ_mul_pos hm))) := by
  have hpow1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  -- index identity: `D_{m+1} = riemannSum f (2·(2^m−1)+1)`.
  have hidx : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    omega
  have hEqTerm : Req (dyadicTerm f m)
      (Rsub (riemannSum f (2 * (2 ^ m - 1) + 1)) (riemannSum f (2 ^ m - 1))) := by
    show Req (Rsub (riemannSum f (2 ^ (m + 1) - 1)) (riemannSum f (2 ^ m - 1)))
             (Rsub (riemannSum f (2 * (2 ^ m - 1) + 1)) (riemannSum f (2 ^ m - 1)))
    rw [hidx]; exact Req_refl _
  obtain ⟨hlo, hhi⟩ := riemannSum_refine hLd hLn hlip hfc (2 ^ m - 1)
  -- the refinement denominator `4·((2^m−1)+1) = 4·2^m` dominates `(m+1)·m`.
  have hden : (m + 1) * m ≤ 4 * (2 ^ m - 1 + 1) := by
    have := two_mul_env m; omega
  have hQle : Qle (mul L (⟨1, 4 * (2 ^ m - 1 + 1)⟩ : Q)) (mul L (⟨1, (m + 1) * m⟩ : Q)) :=
    qmul_den_anti hLn hden
  have hbd : Rle (ofQ (mul L (⟨1, 4 * (2 ^ m - 1 + 1)⟩ : Q))
                  (Qmul_den_pos hLd (Nat.mul_pos (by decide) (Nat.succ_pos (2 ^ m - 1)))))
                (ofQ (mul L (⟨1, (m + 1) * m⟩ : Q)) (Qmul_den_pos hLd (digamma_succ_mul_pos hm))) :=
    Rle_ofQ_ofQ _ _ hQle
  constructor
  · refine Rle_trans ?_ (Rle_of_Req (Req_symm hEqTerm))
    refine Rle_trans (Rle_Rneg hbd) hlo
  · exact Rle_trans (Rle_of_Req hEqTerm) (Rle_trans hhi hbd)

/-- **The dyadic Riemann sums are a regular sequence** (`RReg`) — the input to Bishop's `Rlim`. The
    `L`-reindexed partial sums of the refinement increments converge (`genSum_RReg`), so the integral
    of a Lipschitz integrand exists constructively. -/
theorem dyadicSum_RReg {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) :
    RReg (fun j => genSum (dyadicTerm f) (digammaMidx L j)) :=
  genSum_RReg (dyadicTerm f) hLd hLn (fun m hm => dyadicTerm_bound hLd hLn hlip hfc m hm)

/-- **The certified Riemann integral** `∫₀¹ f` of a Lipschitz integrand — the Bishop limit of the
    dyadic Riemann sums, anchored at `D_0 = f(0)` plus the limit of the telescoping increments. -/
def riemannIntegral {f : Real → Real} {L : Q} (hLd : 0 < L.den) (hLn : 0 ≤ L.num)
    (hlip : ∀ x y, Rle (Rabs (Rsub (f x) (f y))) (Rmul (ofQ L hLd) (Rabs (Rsub x y))))
    (hfc : ∀ x y, Req x y → Req (f x) (f y)) : Real :=
  Radd (dyadicR f 0)
    (Rlim (fun j => genSum (dyadicTerm f) (digammaMidx L j)) (dyadicSum_RReg hLd hLn hlip hfc))

end UOR.Bridge.F1Square.Analysis
