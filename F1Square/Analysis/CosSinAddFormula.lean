/-
F1 square — the **cos/sin angle-addition formulas** `cos(a+b) = cos a cos b − sin a sin b` and
`sin(a+b) = sin a cos b + cos a sin b` (the v0.16.0 prerequisite for the complex exponential law
`Cexp(a+b) = Cexp a · Cexp b`, hence for the tight Lipschitz bounds `|cos a − cos b| ≤ |a−b|` that
control the η-series variation `Σ|n⁻ˢ − (n+1)⁻ˢ| < ∞` — the integration-free route to `ζ` on the
critical strip).

This module builds the **formal (finite, exact) heart**: the *antidiagonal binomial identity*

    (a+b)^{2m}/(2m)!  =  Σ_{2i ≤ 2m} a^{2i}·b^{2m−2i}/((2i)!·(2m−2i)!)        [the `cos·cos` diagonal]
                       + Σ_{2i+1 ≤ 2m} a^{2i+1}·b^{2m−2i−1}/((2i+1)!·(2m−2i−1)!)  [the `sin·sin` diagonal]

which is exactly `cos(a+b)`'s degree-`2m` term reorganized into the product diagonals. It is a pure
binomial fact: each coefficient `C(2m,p)/(2m)! = 1/(p!·(2m−p)!)` (`choose_mul_fct_mul_fct`), and the
even/odd split of `p` is `Fsum_parity_split`. The convergence/reconciliation (lifting to `RaltReal`)
builds on top, mirroring `CosSinAdd` / `ExpRealAdd`.

Pure Lean 4, no Mathlib, no `sorry`/`native_decide`, choice-free.
-/

import F1Square.Analysis.CosSinAdd

namespace UOR.Bridge.F1Square.Analysis

/-- **The two-variable pair term** `aᵖ·b^{2m−p}/(p!·(2m−p)!)` — the coefficient-`p` summand of the
    degree-`2m` antidiagonal (a `cos·cos` term when `p` even, a `sin·sin` term when `p` odd). -/
def pairTerm (a b : Q) (m p : Nat) : Q :=
  mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩

theorem pairTerm_den_pos {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m p : Nat) :
    0 < (pairTerm a b m p).den :=
  Qmul_den_pos (Qmul_den_pos (qpow_den_pos had p) (qpow_den_pos hbd _))
    (Nat.mul_pos (fct_pos _) (fct_pos _))

/-- **Per-term scaling**: the binomial term `C(2m,p)·aᵖ·b^{2m−p}` divided by `(2m)!` equals the pair
    term `aᵖ·b^{2m−p}/(p!·(2m−p)!)` (the binomial-coefficient identity `C(2m,p)/(2m)! = 1/(p!(2m−p)!)`). -/
theorem binTerm_scaled_eq {a b : Q} (m : Nat) {p : Nat} (hp : p ≤ 2 * m) :
    Qeq (mul (⟨1, fct (2 * m)⟩ : Q) (binTerm a b (2 * m) p)) (pairTerm a b m p) := by
  -- `binTerm a b (2m) p = ⟨C(2m,p),1⟩ · (aᵖ · b^{2m−p})`; scale by `1/(2m)!`. The whole thing reduces to
  -- the coefficient identity `⟨C(2m,p), (2m)!⟩ ≈ ⟨1, p!·(2m−p)!⟩` (`choose_mul_fct_mul_fct`).
  have hkeyZ : (choose (2 * m) p : Int) * (fct p : Int) * (fct (2 * m - p) : Int)
      = (fct (2 * m) : Int) := by exact_mod_cast choose_mul_fct_mul_fct hp
  show Qeq (mul (⟨1, fct (2 * m)⟩ : Q)
      (mul (⟨(choose (2 * m) p : Int), 1⟩ : Q) (mul (qpow a p) (qpow b (2 * m - p)))))
    (mul (mul (qpow a p) (qpow b (2 * m - p))) ⟨1, fct p * fct (2 * m - p)⟩)
  simp only [Qeq, mul]
  push_cast
  generalize (qpow a p).num = an
  generalize (qpow b (2 * m - p)).num = bn
  generalize ((qpow a p).den : Int) = ad
  generalize ((qpow b (2 * m - p)).den : Int) = bd
  generalize ((choose (2 * m) p : Nat) : Int) = cc at hkeyZ ⊢
  generalize ((fct p : Nat) : Int) = fp at hkeyZ ⊢
  generalize ((fct (2 * m - p) : Nat) : Int) = fq at hkeyZ ⊢
  generalize ((fct (2 * m) : Nat) : Int) = ff at hkeyZ ⊢
  rw [← hkeyZ]; ring_uor

/-- **The antidiagonal binomial identity** (the formal heart of the addition formula): for `m = m'+1`,

    `(a+b)^{2m}/(2m)!  =  Σ_{j=0}^{m'+1} a^{2j}·b^{2m−2j}/((2j)!·(2m−2j)!)`     [`cos·cos` diagonal]
                        ` + Σ_{j=0}^{m'} a^{2j+1}·b^{2m−2j−1}/((2j+1)!·(2m−2j−1)!)` [`sin·sin` diagonal].

    Pure binomial: expand `(a+b)^{2m}` (`binomial`), divide each term by `(2m)!`
    (`binTerm_scaled_eq`, the coefficient identity), then split the index by parity
    (`Fsum_parity_split`). The `sin·sin` diagonal has the even `p`-terms removed and `+1` shifted. -/
theorem addPow_div_antidiag {a b : Q} (had : 0 < a.den) (hbd : 0 < b.den) (m' : Nat) :
    Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
  have hbtd : ∀ i, 0 < (binTerm a b (2 * (m' + 1)) i).den := binTerm_den_pos had hbd _
  have hptd : ∀ i, 0 < (pairTerm a b (m' + 1) i).den := pairTerm_den_pos had hbd _
  have hc2m : 0 < (⟨1, fct (2 * (m' + 1))⟩ : Q).den := fct_pos _
  -- `(a+b)^{2m}·(1/(2m)!) ≈ (1/(2m)!)·Σ binTerm`.
  have h1 : Qeq (mul (qpow (add a b) (2 * (m' + 1))) ⟨1, fct (2 * (m' + 1))⟩)
      (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1)))) :=
    Qeq_trans (Qmul_den_pos (Fsum_den_pos hbtd _) hc2m)
      (Qmul_congr (binomial had hbd _) (Qeq_refl _)) (Qmul_swap _ _)
  -- distribute the scaling into the sum, then rewrite each term to `pairTerm`.
  have h2 : Qeq (mul (⟨1, fct (2 * (m' + 1))⟩ : Q) (Fsum (binTerm a b (2 * (m' + 1))) (2 * (m' + 1))))
      (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1))) :=
    Qeq_trans (Fsum_den_pos (fun i => Qmul_den_pos hc2m (hbtd i)) _)
      (Qeq_symm (Fsum_mul_left hc2m hbtd _))
      (Fsum_congr_le (fun i hi => binTerm_scaled_eq (m' + 1) (by omega : i ≤ 2 * (m' + 1))))
  -- parity-split the index `0 ≤ p ≤ 2m = 2m'+2`.
  have h3 : Qeq (Fsum (pairTerm a b (m' + 1)) (2 * (m' + 1)))
      (add (Fsum (fun j => pairTerm a b (m' + 1) (2 * j)) (m' + 1))
           (Fsum (fun j => pairTerm a b (m' + 1) (2 * j + 1)) m')) := by
    have hsplit := Fsum_parity_split (pairTerm a b (m' + 1)) hptd m'
    rwa [show 2 * m' + 2 = 2 * (m' + 1) from by omega] at hsplit
  exact Qeq_trans (Qmul_den_pos hc2m (Fsum_den_pos hbtd _)) h1
    (Qeq_trans (Fsum_den_pos hptd _) h2 h3)

end UOR.Bridge.F1Square.Analysis
